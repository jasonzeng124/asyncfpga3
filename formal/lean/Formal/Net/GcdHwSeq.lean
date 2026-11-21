import Formal.Net.GcdHwLive

/-!
# gcd_hw under a sequential environment: every pair, in order, for any number of pairs (S5, token level)

Core Lean only. Shard C, 2026-11-02.

**Problem.** `gcd_hw_graph_computes_gcd` (C-8i/8k) is about ONE invocation: one pair
(a, b) offered to an empty graph. THE goal's `NetCorrectSeq` needs any number of pairs
under `SeqEnv`: pair k+1 is offered as soon as the k-th result has been taken from
`out0`, while pair k's leftover tokens may still be in flight inside the graph (a
token-level simulation sees leftovers on up to 15 internal channels at that moment,
e.g. the `a = 0` fast path's pending `b = 0` test, and the sink of `control_merge12`).

**Model.** The graph bdc emits for gcd_hw (`Gcd.rules`, 158 firing rules, imported from
bdc's own code) is closed with a sequential environment written as six more rules
(`envRules`), so the whole system is again an imported-style graph:
* `take`  (fork 250 -> 259, 254): take the front of `out0` into the result log 259
  and return one credit to 254;
* `offer` (comp [254, 252] -> 255; fork 255 -> 256..258; comp [256] -> a;
  comp [257, 253] -> b; comp [258] -> start): spend the credit and offer the next
  pair from the two input lists 252 (a's) and 253 (b's).
Initially there is one credit, the pairs on 252/253, nothing else. So pair k+1 can
enter only after `out0`'s k-th token was taken: SeqEnv at token level. The schedule
of all 164 rules is arbitrary (any interleaving, any arbitration of the
control_merges); the env may take a result at any time after it appears.

**Results** (`gcd_hw_seq`), for every list of pairs with a, b < 2^31:
* some schedule completes;
* every complete run ends with the result log equal to `ps.map gcd` (all results,
  in order, nothing extra);
* at every point of every run the log is a prefix of `ps.map gcd` (safety: never a
  wrong or out-of-order result);
* every partial run can be completed (no deadlock), and one bound covers the length
  of every run (no livelock).

**Proof idea.** A token-count invariant (`PS`: the control spine without the
`control_merge12 -> sink15` branch, plus `control_merge12`'s index, `out0`, the credit
and the offer's start path) holds at most one token in every reachable state. That
is exactly what the diamond property of the generic Kahn layer needs (the
control_merges' inputs are never both full), so all complete runs end in the same
state (`KahnLTS.terminal_unique`); and the run that drains each pair before taking
its result is built from the single-invocation theorem by a frame lemma (leftover
end tokens, the remaining inputs and the result log are channels the graph does not
read). The generic closure lemma `closedQ` extends `closed_of_check` to rules that
move the counted token from a control_merge's index to a mux's output.

**Not covered.** Token level only: unbounded FIFO channels, H_SOURCE_ETERNAL for the
collapsed constants (as in C-8i). Nothing about circuits, delays or the bitstream:
this is the S5 obligation's token-level half; the circuit must still be shown to
refine this graph (S4) under SeqEnv. The end channel (3) collects one token per pair
and is never read.
-/

namespace Formal.Net.GcdHw.Seq

open Formal.Net.Kahn Formal.Net.GcdHw Formal.Net.GcdHw.Gcd

/-! ## 1. Generic lemmas: firing depends only on inputs; frames; lifting -/

section Generic
variable {L : Type}

theorem fire_congr (G : L → Node Nat Nat) (l : L) {s s' : Store Nat Nat}
    (h : ∀ c, (G l).ins c → s c = s' c) : (G l).fire s = (G l).fire s' := by
  cases h1 : (G l).fire s with
  | some r => exact ((G l).mono s s' r h1 (fun c hc => ⟨[], by rw [h c hc, List.append_nil]⟩)).symm
  | none =>
    cases h2 : (G l).fire s' with
    | none => rfl
    | some r =>
      have := (G l).mono s' s r h2 (fun c hc => ⟨[], by rw [h c hc, List.append_nil]⟩)
      rw [h1] at this; cases this

/-- `E` placed in front of `s`, channel by channel (older tokens first). -/
def Ext (E s : Store Nat Nat) : Store Nat Nat := fun c => E c ++ s c

theorem step_ext (G : L → Node Nat Nat) {E : Store Nat Nat}
    (hE : ∀ c l, E c ≠ [] → ¬ (G l).ins c) (s : Store Nat Nat) (l : L) :
    step G (Ext E s) l = (step G s l).map (Ext E) := by
  have hf : (G l).fire (Ext E s) = (G l).fire s := by
    apply fire_congr; intro c hc
    have : E c = [] := Classical.byContradiction fun h => hE c l h hc
    simp [Ext, this]
  unfold step; rw [hf]
  cases hr : (G l).fire s with
  | none => rfl
  | some r =>
    simp only [Option.map]
    congr 1
    funext c
    simp only [applyF, Ext]
    by_cases he : E c = []
    · simp [he]
    · have : r.1 c = 0 := (G l).pop_ins s r c hr (hE c l he)
      simp [this]

/-- Frame: tokens on channels no node reads do not change a run. -/
theorem run_ext (G : L → Node Nat Nat) {E : Store Nat Nat}
    (hE : ∀ c l, E c ≠ [] → ¬ (G l).ins c) :
    ∀ {s n t}, Run (step G) s n t → Run (step G) (Ext E s) n (Ext E t) := by
  intro s n t h
  induction h with
  | refl s => exact Run.refl _
  | cons l hl _ ih =>
    refine Run.cons l ?_ ih
    rw [step_ext G hE, hl]; rfl

theorem terminal_ext (G : L → Node Nat Nat) {E : Store Nat Nat}
    (hE : ∀ c l, E c ≠ [] → ¬ (G l).ins c) {t : Store Nat Nat}
    (ht : Terminal (step G) t) : Terminal (step G) (Ext E t) := by
  intro l; rw [step_ext G hE, ht l]; rfl

/-- A channel no node reads only grows along a run. -/
theorem run_grows (G : L → Node Nat Nat) {c : Nat} (hc : ∀ l, ¬ (G l).ins c) :
    ∀ {s n t}, Run (step G) s n t → ∃ x, t c = s c ++ x := by
  intro s n t h
  induction h with
  | refl s => exact ⟨[], by simp⟩
  | @cons s s' t n l hl _ ih =>
    obtain ⟨r, hr, rfl⟩ := step_some hl
    obtain ⟨x, hx⟩ := ih
    refine ⟨r.2 c ++ x, ?_⟩
    rw [hx]; simp [applyF, (G l).pop_ins s r c hr (hc l)]

end Generic

theorem step_append (rs rs2 : List Rule) {s s' : Store Nat Nat} {l : Nat}
    (h : step (graph rs) s l = some s') : step (graph (rs ++ rs2)) s l = some s' := by
  cases hr : rs[l]? with
  | none =>
    unfold step at h
    simp [graph, graphV, hr, inert] at h
  | some r =>
    have hl : l < rs.length := by
      by_cases hl : l < rs.length
      · exact hl
      · rw [List.getElem?_eq_none (by omega)] at hr; cases hr
    have hr2 : (rs ++ rs2)[l]? = some r := by rw [List.getElem?_append_left hl, hr]
    unfold step at h ⊢
    rw [graph_fire hr] at h; rw [graph_fire hr2]; exact h

theorem run_append (rs rs2 : List Rule) :
    ∀ {s n t}, Run (step (graph rs)) s n t → Run (step (graph (rs ++ rs2))) s n t := by
  intro s n t h
  induction h with
  | refl s => exact Run.refl _
  | cons l hl _ ih => exact Run.cons l (step_append rs rs2 hl) ih

theorem not_ins_of_check {rs : List Rule} {c : Nat} (h : rs.all (fun r => !(r.insL.contains c)) = true) :
    ∀ l, ¬ (graph rs l).ins c := by
  intro l hc
  obtain ⟨r, hr, hcr⟩ := graph_ins hc
  have := List.all_eq_true.mp h r (List.mem_of_getElem? hr)
  simp [hcr] at this

/-! ## 2. Generic: the counted-token invariant through control_merge index and mux -/

/-- Like `Rule.okP`, but a control_merge may put its token on its index instead of its
result, and a mux may pass a counted select token on to its output. -/
def _root_.Formal.Net.GcdHw.Rule.okQ (P : List Nat) : Rule → Bool
  | .mux s _ o _ => !(decide (o ∈ P)) || decide (s ∈ P)
  | .cm i res idx _ => decide (res ≠ idx) &&
      (if i ∈ P then !(decide (res ∈ P) && decide (idx ∈ P))
       else !(decide (res ∈ P)) && !(decide (idx ∈ P)))
  | r => r.okP P

theorem push_le_pop (P : List Nat) (rs : List Rule) (hP : P.Nodup)
    (h : rs.all (Rule.okQ P) = true) {s : Store Nat Nat} {l : Nat} {res : Fire Nat Nat}
    (hres : (graph rs l).fire s = some res) :
    (P.map fun c => (res.2 c).length).sum ≤ (P.map res.1).sum := by
  unfold graph graphV at hres
  split at hres
  · rename_i r hr
    have hok : r.okQ P = true := List.all_eq_true.mp h r (List.mem_of_getElem? hr)
    change Rule.fire natVI r s = some res at hres
    cases r with
    | mux s0 ds o iw =>
      change muxF natVI s0 ds o iw s = some res at hres
      obtain ⟨v, vs, j, d, x, xs, -, -, -, -, -, rfl⟩ := muxF_some hres
      simp only [Rule.okQ, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        decide_eq_true_eq] at hok
      have h1 := sum_one P hP o
      have a : (P.map fun c => ((fun y => if y = o then [x] else []) c).length).sum ≤
          (P.map fun c => if c = o then 1 else 0).sum :=
        sum_le (fun c => by simp only; split <;> simp)
      have b : (P.map fun c => if c = s0 then 1 else 0).sum ≤
          (P.map fun y => (if y = s0 then 1 else 0) + (if y = d then 1 else 0)).sum :=
        sum_le (fun c => by omega)
      have h2 := sum_one P hP s0
      simp only at a b ⊢
      rcases hok with ho | hs
      · rw [if_neg ho] at h1; omega
      · rw [if_pos hs] at h2; split at h1 <;> omega
    | comp ins o e =>
      have hok' : (Rule.comp ins o e).okP P = true := hok
      change strictF _ _ s = some res at hres
      obtain ⟨vs, out, hh, hg, rfl⟩ := strictF_some hres
      simp only [Rule.out, Option.some.injEq] at hg; subst hg
      dsimp only [Rule.insL]
      have h1 := sum_one P hP o
      have : (P.map fun c => ((fun c => if c = o then [natVI.comp e vs] else []) c).length).sum ≤
          (P.map fun c => if c = o then 1 else 0).sum :=
        sum_le (fun c => by simp only; split <;> simp)
      simp only at this ⊢
      by_cases ho : o ∈ P
      · simp only [Rule.okP, ho, decide_true, Bool.not_true, Bool.false_or, List.any_eq_true,
          decide_eq_true_eq] at hok'
        obtain ⟨c, hc, hcP⟩ := hok'
        have := popOf_sum hc hcP; simp [ho] at h1; omega
      · simp [ho] at h1; omega
    | fork i os =>
      have hok' : (Rule.fork i os).okP P = true := hok
      change strictF _ _ s = some res at hres
      obtain ⟨vs, out, hh, hg, rfl⟩ := strictF_some hres
      simp only [Rule.out, Option.some.injEq] at hg; subst hg
      show (P.map fun c => (if c ∈ os then vs.take 1 else []).length).sum ≤ (P.map (popOf [i])).sum
      simp only [Rule.okP, decide_eq_true_eq] at hok'
      have a : (P.map fun c => (if c ∈ os then vs.take 1 else []).length).sum ≤
          (P.map fun c => if c ∈ os then 1 else 0).sum :=
        sum_le (fun c => by split; exact take1_len vs; simp)
      rw [sum_ind_filter] at a
      by_cases hi : i ∈ P
      · have := popOf_sum (ins := [i]) (by simp) hi; rw [if_pos hi] at hok'; omega
      · rw [if_neg hi] at hok'; omega
    | branch c d t f =>
      have hok' : (Rule.branch c d t f).okP P = true := hok
      change strictF _ _ s = some res at hres
      obtain ⟨vs, out, hh, hg, rfl⟩ := strictF_some hres
      simp only [Rule.out] at hg
      split at hg
      · rename_i v x
        simp only [natVI, Option.map_some, Option.some.injEq] at hg; subst hg
        have htf : ∀ tgt, (tgt = t ∨ tgt = f) →
            (P.map fun y => (if y = tgt then [x] else []).length).sum ≤ (P.map (popOf [c, d])).sum := by
          intro tgt htg
          have h1 := sum_one P hP tgt
          have a : (P.map fun y => (if y = tgt then [x] else []).length).sum ≤
              (P.map fun y => if y = tgt then 1 else 0).sum :=
            sum_le (fun y => by split <;> simp)
          by_cases hp : tgt ∈ P
          · have htf : t ∈ P ∨ f ∈ P := by rcases htg with rfl | rfl <;> simp [hp]
            simp only [Rule.okP, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hok'
            have hcd : c ∈ P ∨ d ∈ P := by
              rcases hok' with (h0 | h0) | h0
              · simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at h0
                exact False.elim (htf.elim (fun h => h0.1 h) (fun h => h0.2 h))
              · exact Or.inl h0
              · exact Or.inr h0
            rcases hcd with hc | hd
            · have := popOf_sum (ins := [c, d]) (by simp) hc; rw [if_pos hp] at h1; omega
            · have := popOf_sum (ins := [c, d]) (by simp) hd; rw [if_pos hp] at h1; omega
          · rw [if_neg hp] at h1; omega
        exact htf _ (by split <;> simp)
      · cases hg
    | cm i r0 idx k =>
      change strictF _ _ s = some res at hres
      obtain ⟨vs, out, hh, hg, rfl⟩ := strictF_some hres
      simp only [Rule.out, Option.some.injEq] at hg; subst hg
      show (P.map fun c => ((if c = r0 then vs.take 1 else []) ++
            (if c = idx then [natVI.lit k] else [])).length).sum ≤ (P.map (popOf [i])).sum
      simp only [Rule.okQ, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨hne, hok⟩ := hok
      by_cases hi : i ∈ P
      · rw [if_pos hi] at hok
        have hpop := popOf_sum (ins := [i]) (by simp) hi
        by_cases hr0 : r0 ∈ P
        · have hidx : idx ∉ P := by
            intro h; simp [hr0, h] at hok
          have h1 := sum_one P hP r0
          have a : (P.map fun c => ((if c = r0 then vs.take 1 else []) ++
                (if c = idx then [natVI.lit k] else [])).length).sum ≤
              (P.map fun c => if c = r0 then 1 else 0).sum := by
            apply sum_le_mem; intro c hc
            have e2 : c ≠ idx := fun e => hidx (e ▸ hc)
            simp only [e2, ↓reduceIte, List.append_nil]; split; exact take1_len vs; simp
          rw [if_pos hr0] at h1; omega
        · have h1 := sum_one P hP idx
          have a : (P.map fun c => ((if c = r0 then vs.take 1 else []) ++
                (if c = idx then [natVI.lit k] else [])).length).sum ≤
              (P.map fun c => if c = idx then 1 else 0).sum := by
            apply sum_le_mem; intro c hc
            have e2 : c ≠ r0 := fun e => hr0 (e ▸ hc)
            simp only [e2, ↓reduceIte, List.nil_append]; split <;> simp
          split at h1 <;> omega
      · rw [if_neg hi] at hok
        simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hok
        have : (P.map fun c => ((if c = r0 then vs.take 1 else []) ++
              (if c = idx then [natVI.lit k] else [])).length).sum = 0 := by
          apply sum_zero; intro c hc
          have e1 : c ≠ r0 := fun e => hok.1 (e ▸ hc)
          have e2 : c ≠ idx := fun e => hok.2 (e ▸ hc)
          simp [e1, e2]
        omega
    | sink i =>
      change strictF _ _ s = some res at hres
      obtain ⟨vs, out, hh, hg, rfl⟩ := strictF_some hres
      simp only [Rule.out, Option.some.injEq] at hg; subst hg
      show (P.map fun _ => ([] : List Nat).length).sum ≤ _
      exact Nat.le_trans (Nat.le_of_eq (sum_zero (fun _ _ => rfl))) (Nat.zero_le _)
  · cases hres

/-- The counted tokens never increase. -/
theorem cnt_step_le (P : List Nat) (rs : List Rule) (hP : P.Nodup)
    (h : rs.all (Rule.okQ P) = true) {s s' : Store Nat Nat} {l : Nat}
    (hs : step (graph rs) s l = some s') : cnt P s' ≤ cnt P s := by
  obtain ⟨res, hres, rfl⟩ := step_some hs
  have hle := (graph rs l).pop_le s res
  have key := cnt_apply P s res (fun c => hle c hres)
  have := push_le_pop P rs hP h hres
  omega

theorem closedQ (P : List Nat) (rs : List Rule) (hP : P.Nodup)
    (h : rs.all (Rule.okQ P) = true) : Closed (step (graph rs)) (Inv P) :=
  fun _ _ _ hI hs => Nat.le_trans (cnt_step_le P rs hP h hs) hI


/-! ## 3. gcd_hw closed with a sequential environment -/

/-- The environment as six rules (channels 252..259; see the module doc). -/
def envRules : List Rule := [
  .fork 250 [259, 254],            -- take: out0 -> result log 259, credit 254
  .comp [254, 252] 255 (.var 1),   -- offer: spend the credit with the next a
  .fork 255 [256, 257, 258],
  .comp [256] 0 (.var 0),          -- a
  .comp [257, 253] 1 (.var 1),     -- b
  .comp [258] 2 (.lit 0)]          -- start

def rsS : List Rule := rules ++ envRules
abbrev GS := graph rsS

/-- The result log. -/
def chGot : Nat := 259

/-- Counted channels: the control spine without control_merge12's result branch (251, to
sink15), plus control_merge12's index (249), out0 (250), the credit (254) and the offer's
start path (255, 258). -/
def PS : List Nat := spine.filter (· ≠ 251) ++ [249, 250, 254, 255, 258]

theorem rules_len : rules.length = 158 := by decide +kernel
theorem PS_nodup : PS.Nodup := by decide +kernel
theorem insS_ok : checkIns rsS = true := by decide +kernel
theorem outsS_ok : checkOuts PS rsS = true := by decide +kernel
theorem okS : rsS.all (Rule.okQ PS) = true := by decide +kernel

theorem closedS : Closed (step GS) (Inv PS) := closedQ PS rsS PS_nodup okS
theorem diamondS : DiamondOn (step GS) (Inv PS) :=
  wfOn_diamond (wfOn_of_check PS rsS PS_nodup insS_ok outsS_ok)

/-- Environment state between pairs: `k` end tokens, results `got` logged, `rest` still
to offer, credit `cr` (one token, or none while a pair is inside). -/
def S (k : Nat) (got : List Nat) (rest : List (Nat × Nat)) (cr : List Nat) : Store Nat Nat :=
  fun c =>
    if c = 3 then List.replicate k 0 else
    if c = 252 then rest.map Prod.fst else
    if c = 253 then rest.map Prod.snd else
    if c = 254 then cr else
    if c = 259 then got else []

/-- Start state for the pair list `ps`. -/
def start (ps : List (Nat × Nat)) : Store Nat Nat := S 0 [] ps [0]


theorem stepS {l : Nat} {r : Rule} (hr : rsS[l]? = some r) (s : Store Nat Nat) :
    step GS s l = (r.fire natVI s).map (applyF s) := by
  unfold step; rw [graph_fire hr]

theorem r159 : rsS[159]? = some (.comp [254, 252] 255 (.var 1)) := by decide +kernel
theorem r160 : rsS[160]? = some (.fork 255 [256, 257, 258]) := by decide +kernel
theorem r161 : rsS[161]? = some (.comp [256] 0 (.var 0)) := by decide +kernel
theorem r162 : rsS[162]? = some (.comp [257, 253] 1 (.var 1)) := by decide +kernel
theorem r163 : rsS[163]? = some (.comp [258] 2 (.lit 0)) := by decide +kernel
theorem r158 : rsS[158]? = some (.fork 250 [259, 254]) := by decide +kernel

/-- Offering pair (a, b): five env firings turn the between-pairs state into the single-
invocation start store, framed by the env's own channels. -/
theorem offer_run (k : Nat) (got : List Nat) (a b : Nat) (rest : List (Nat × Nat)) (x : Nat) :
    Run (step GS) (S k got ((a, b) :: rest) [x]) 5 (Ext (S k got rest []) (init a b)) := by
  have e := exec_run (G := GS) (s := S k got ((a, b) :: rest) [x]) (ls := [159, 160, 161, 162, 163])
    (t := Ext (S k got rest []) (init a b)) (t' := Ext (S k got rest []) (init a b))
  apply e _ (fun _ => rfl)
  simp only [exec, stepS r159, stepS r160, stepS r161, stepS r162, stepS r163]
  simp [Rule.fire, strictF, heads, S, Rule.out, natVI, E.eval, Rule.insL, applyF, popOf]
  funext c
  obtain ⟨-, -, -, h3⟩ := init_store a b
  by_cases hc : c < 3
  · have : c = 0 ∨ c = 1 ∨ c = 2 := by omega
    rcases this with rfl | rfl | rfl <;> rfl
  · have hi : init a b c = [] := h3 c (by omega)
    simp only [applyF, popOf, Ext, S, hi, List.mem_cons, List.not_mem_nil, or_false, List.append_nil]
    have n0 : c ≠ 0 := by omega
    have n1 : c ≠ 1 := by omega
    have n2 : c ≠ 2 := by omega
    by_cases e3 : c = 3
    · subst e3; simp
    by_cases e252 : c = 252
    · subst e252; simp
    by_cases e253 : c = 253
    · subst e253; simp
    by_cases e254 : c = 254
    · subst e254; simp
    by_cases e259 : c = 259
    · subst e259; simp
    by_cases e255 : c = 255
    · subst e255; simp
    by_cases e256 : c = 256
    · subst e256; simp
    by_cases e257 : c = 257
    · subst e257; simp
    by_cases e258 : c = 258
    · subst e258; simp
    simp [n0, n1, n2, e3, e252, e253, e254, e255, e256, e257, e258, e259]


theorem final_zero (r c : Nat) (h3 : c ≠ 3) (h250 : c ≠ 250) : final r c = [] := by
  simp only [final, St, ofL_lmap, List.map_eq_nil_iff, T1, ofL_sp]
  have e3 : (c == 3) = false := by simp; omega
  have e250 : (c == 250) = false := by simp; omega
  split <;> simp [List.lookup, e3, e250]

/-- Taking the result: after a drained invocation, `take` logs it and returns the credit. -/
theorem take_step (k : Nat) (got : List Nat) (rest : List (Nat × Nat)) (g : Nat) :
    step GS (Ext (S k got rest []) (final g)) 158 = some (S (k + 1) (got ++ [g]) rest [g]) := by
  rw [stepS r158]
  have h250 : Ext (S k got rest []) (final g) 250 = [g] := rfl
  simp only [Rule.fire, strictF, Rule.insL, heads, h250, Rule.out, Option.bind, Option.map]
  congr 1
  funext c
  simp only [applyF, popOf, Ext, S, List.mem_cons, List.not_mem_nil, or_false]
  by_cases e3 : c = 3
  · subst e3; simp [List.replicate_succ']; rfl
  by_cases e250 : c = 250
  · subst e250; simp; rfl
  have hf := final_zero g c e3 e250
  by_cases e259 : c = 259
  · subst e259; simp [hf]
  by_cases e254 : c = 254
  · subst e254; simp [hf]
  simp [e3, e250, e254, e259, hf]

theorem frame_ok (k : Nat) (got : List Nat) (rest : List (Nat × Nat)) :
    ∀ c l, S k got rest [] c ≠ [] → ¬ (G l).ins c := by
  intro c l hc
  have hc' : c = 3 ∨ c = 252 ∨ c = 253 ∨ c = 259 := by
    simp only [S] at hc; split at hc; omega; split at hc; omega; split at hc; omega
    split at hc; simp at hc; split at hc; omega; simp at hc
  rcases hc' with rfl | rfl | rfl | rfl
  · exact not_ins_of_check (by decide +kernel) l
  · exact not_ins_of_check (by decide +kernel) l
  · exact not_ins_of_check (by decide +kernel) l
  · exact not_ins_of_check (by decide +kernel) l

def gcdP (p : Nat × Nat) : Nat := Nat.gcd p.1 p.2

/-- One pair, drained: offer, run the invocation to its final store, take the result. -/
theorem pair_run (k : Nat) (got : List Nat) (a b : Nat) (rest : List (Nat × Nat)) (x : Nat)
    (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    ∃ n, Run (step GS) (S k got ((a, b) :: rest) [x]) n
      (S (k + 1) (got ++ [Nat.gcd a b]) rest [Nat.gcd a b]) := by
  obtain ⟨⟨n, hn⟩, -⟩ := gcd_hw_graph_computes_gcd ha hb
  have h1 := run_append rules envRules (run_ext G (frame_ok k got rest) hn)
  have h2 := run_trans (offer_run k got a b rest x) h1
  exact ⟨_, run_trans h2 (Run.cons 158 (take_step k got rest _) (Run.refl _))⟩

/-- All pairs, each drained before its result is taken. -/
theorem seq_run : ∀ (ps : List (Nat × Nat)) (k : Nat) (got : List Nat) (x : Nat),
    (∀ p ∈ ps, p.1 < 2 ^ 31 ∧ p.2 < 2 ^ 31) →
    ∃ n y, Run (step GS) (S k got ps [x]) n (S (k + ps.length) (got ++ ps.map gcdP) [] [y])
  | [], k, got, x, _ => ⟨0, x, by simpa using Run.refl _⟩
  | (a, b) :: rest, k, got, x, h => by
    obtain ⟨ha, hb⟩ := h (a, b) (by simp)
    obtain ⟨n1, h1⟩ := pair_run k got a b rest x ha hb
    obtain ⟨n2, y, h2⟩ := seq_run rest (k + 1) (got ++ [Nat.gcd a b]) (Nat.gcd a b)
      (fun p hp => h p (by simp [hp]))
    refine ⟨n1 + n2, y, ?_⟩
    have := run_trans h1 h2
    simpa [gcdP, Nat.add_assoc, Nat.add_comm 1] using this

theorem dead_congr {st st' : Store Nat Nat} (r : Rule)
    (h : ∀ c ∈ r.insL, (st c).isEmpty = (st' c).isEmpty) : r.dead st = r.dead st' := by
  cases r with
  | mux s0 ds o iw => simp only [Rule.dead]; exact h s0 (by simp [Rule.insL])
  | comp ins o e =>
    simp only [Rule.dead, Rule.insL] at h ⊢
    induction ins with
    | nil => rfl
    | cons c cs ih =>
      simp only [List.any_cons]
      rw [h c (by simp), ih (fun d hd => h d (by simp [hd]))]
  | fork i os => simp only [Rule.dead]; exact h i (by simp [Rule.insL])
  | branch c d t f =>
    simp only [Rule.dead]; rw [h c (by simp [Rule.insL]), h d (by simp [Rule.insL])]
  | cm i r0 idx k => simp only [Rule.dead]; exact h i (by simp [Rule.insL])
  | sink i => simp only [Rule.dead]; exact h i (by simp [Rule.insL])

/-- The end state (every pair offered and its result taken) is quiescent. -/
theorem end_terminal (k : Nat) (got : List Nat) (y : Nat) : Terminal (step GS) (S k got [] [y]) := by
  apply terminal_of_dead
  have hall : rsS.all (Rule.dead (S 0 [] [] [0])) = true := by decide +kernel
  have hno : rsS.all (fun r => !(r.insL.contains 3) && !(r.insL.contains 259)) = true := by decide +kernel
  rw [List.all_eq_true] at hall hno ⊢
  intro r hr
  rw [dead_congr r (st' := S 0 [] [] [0]) (fun c hc => ?_)]
  · exact hall r hr
  · have := hno r hr
    have n3 : c ≠ 3 := by intro e; subst e; simp [hc] at this
    have n259 : c ≠ 259 := by intro e; subst e; simp [hc] at this
    by_cases e2 : c = 252 <;> by_cases e3 : c = 253 <;> by_cases e4 : c = 254 <;> simp [S, *]


theorem start_inv (ps : List (Nat × Nat)) : Inv PS (start ps) := by
  have e : ∀ c ∈ PS, (start ps c).length = (S 0 [] [] [0] c).length := by
    intro c hc
    have h2 : c ≠ 252 := by intro e; subst e; revert hc; decide +kernel
    have h3 : c ≠ 253 := by intro e; subst e; revert hc; decide +kernel
    simp [start, S, h2, h3]
  unfold Inv cnt; rw [List.map_congr_left e]; decide +kernel

theorem got_unread : ∀ l, ¬ (GS l).ins chGot := not_ins_of_check (by decide +kernel)

/-- **gcd_hw under a sequential environment, any number of pairs (token level).**
For every list of pairs with `a, b < 2^31`, in the gcd_hw graph closed with the
sequential environment (pair k+1 offered only after the k-th result was taken from
`out0`; leftovers of pair k may still be inside), on every schedule:
1. some run completes, with the result log `ps.map gcd`;
2. every complete run ends with the result log exactly `ps.map gcd`;
3. at every point of every run, the log is a prefix of `ps.map gcd`;
4. every partial run can be completed (no deadlock);
5. one bound covers the length of every run (no livelock). -/
theorem gcd_hw_seq (ps : List (Nat × Nat)) (hps : ∀ p ∈ ps, p.1 < 2 ^ 31 ∧ p.2 < 2 ^ 31) :
    (∃ n t, Run (step GS) (start ps) n t ∧ Terminal (step GS) t ∧ t chGot = ps.map gcdP) ∧
    (∀ m t, Run (step GS) (start ps) m t → Terminal (step GS) t → t chGot = ps.map gcdP) ∧
    (∀ m u, Run (step GS) (start ps) m u → ∃ x, u chGot ++ x = ps.map gcdP) ∧
    (∀ m u, Run (step GS) (start ps) m u → ∃ k t, Run (step GS) u k t ∧ Terminal (step GS) t) ∧
    (∃ N, ∀ m u, Run (step GS) (start ps) m u → m ≤ N) := by
  obtain ⟨n, y, hr⟩ := seq_run ps 0 [] 0 hps
  have hT := end_terminal (0 + ps.length) ([] ++ ps.map gcdP) y
  have hg : S (0 + ps.length) ([] ++ ps.map gcdP) [] [y] chGot = ps.map gcdP := by simp [S, chGot]
  have hI := start_inv ps
  refine ⟨⟨n, _, hr, hT, hg⟩, ?_, ?_, ?_, ⟨n, fun m u hu => no_divergence closedS diamondS hI hr hT hu⟩⟩
  · intro m t hm ht
    obtain ⟨e, -⟩ := terminal_unique closedS diamondS hI hr hT hm ht
    rw [e, hg]
  · intro m u hu
    obtain ⟨-, hk⟩ := prefix_run closedS diamondS hu hr hT hI
    obtain ⟨x, hx⟩ := run_grows GS got_unread hk
    exact ⟨x, by rw [← hx, hg]⟩
  · intro m u hu
    obtain ⟨-, hk⟩ := prefix_run closedS diamondS hu hr hT hI
    exact ⟨_, _, hk, hT⟩

end Formal.Net.GcdHw.Seq
