import Formal.Rewrite.Steps.ScriptRF
import Formal.Rewrite.ChanInv

/-!
# Formal.Rewrite.Steps.Width — rewrite scripts under the token-width assumption (shard A, 2026-11-20)

**Problem, plainly.** research's `BDC_RING_FUSE` packs several results of one cell into one word and slices them out
again. A part that passes an input through (`hi` in `sel(c, hi, mid - 1)`, `a` in `|a| = sel(a >s -1, a, 0 - a)`)
equals its 32-bit slice of the packed word only if the token is `< 2^32`. Tokens in the model are unbounded `Nat`s, so
without an assumption the two graphs really differ (an input `≥ 2^32` comes out reduced mod `2^32`). Can Lean check the
fused graph against the unfused one **under the assumption that every input token fits its declared width**?

**The hypothesis is the width assumption**: `InP NA Wi σ0`, i.e. every channel `≥ NA` starts empty and every token on
an input channel `c` fits its declared width, `v < 2 ^ Wi[c]` (`InW`; width `0` = no width, no constraint, used for
control tokens). Nothing else is assumed.

**Proved.**
* `bwpv_lt`: a width bound computed from the top operator, from the widths of the variables, and from packed pairs is
  a bound on the value, in any environment whose variables fit their widths (`EnvOK`). `unsliceNW_eval`: the slice
  rules of `ScriptRF` with these bounds keep the value in such an environment.
* `safeB_ok`: a Bool check that a rule, fired from a store whose tokens fit a width map `W`, pushes only tokens that
  fit `W` (comp: the expression's bound from its inputs' widths is at most the output's width; fork, branch, mux, cm:
  widths only grow along the data path). `soundP_of_inv`: if every rule of `rs` passes it and `rs'` fires like `rs`
  from every such store, then from every such initial store `rs` and `rs'` have the same complete runs.
* `applyUW_sound` (step `unpackw l W`): the comp at `l` gets its slices narrowed by `unsliceNW` with its inputs' widths
  from `W`; checked: every rule of the graph passes `safeB W`. `applyUD_sound` (step `undedupe`): `Dedupe` read
  backward (a comp reads one more copy of a forked channel), checked by deduping back to the old rules.
* `runScriptW_sound`: for ANY rules and script over `StepW` (every `StepRF` step, `unpackw`, `undedupe`), if
  `runScriptW NA Wi rs ss = some (rs', pre, chg)` then from every initial store satisfying `InP NA Wi` with `pre`
  empty, complete runs of `rs` and `rs'` correspond with the same store outside `chg` (`SoundP`). Each `unpackw`'s map
  must agree with `Wi` on the inputs (`agreeB`: no wider bound than declared is ever assumed).

**Not covered:** token level only; `Wi` is read off the MLIR function signature by the planner (dfimport, trusted
Python), and the hypothesis is stated in its terms. The unconditional theorems (`runScriptRF_sound`) are unchanged.
-/

namespace Formal.Rewrite.Steps

open Formal.Net.Kahn Formal.Net.GcdHw Formal.Rewrite.IncCmp Formal.Rewrite.ChanInv

/-! ## Widths and the width assumption -/

/-- The width a map gives channel (or variable) `c`; `0` = no width. -/
def wOf (W : List Nat) (c : Nat) : Nat := W.getD c 0

/-- **The width assumption on one token**: `v` on channel `c` fits the width `W` gives `c`, if it gives one. -/
def InW (W : List Nat) (c v : Nat) : Prop := wOf W c = 0 ∨ v < 2 ^ wOf W c

/-- Every variable of `env` fits the width `ws` gives it. -/
def EnvOK (ws env : List Nat) : Prop := ∀ k, wOf ws k ≠ 0 → env.getD k 0 < 2 ^ wOf ws k

/-! ## Width bounds with variable widths -/

def bwv (ws : List Nat) : E → Option Nat
  | .var k => if wOf ws k = 0 then none else some (wOf ws k)
  | .lit v => some (v.log2 + 1)
  | .sel _ a b =>
    match bwv ws a, bwv ws b with
    | some x, some y => some (max x y)
    | _, _ => none
  | .un o w a => bw (.un o w a)
  | .bin o w a b => bw (.bin o w a b)

theorem bwv_lt {ws env : List Nat} (henv : EnvOK ws env) : ∀ (e : E) (b : Nat), bwv ws e = some b →
    e.eval env < 2 ^ b
  | .var k, b, h => by
    simp only [bwv] at h
    split at h
    · cases h
    · rename_i hk; obtain rfl := (Option.some.inj h).symm; exact henv k hk
  | .lit v, b, h => by
    simp only [bwv, Option.some.injEq] at h; subst h; exact Nat.lt_log2_self
  | .sel s a c, b, h => by
    simp only [bwv] at h
    split at h
    next x y hx hy =>
      obtain rfl := Option.some.inj h
      have ha := bwv_lt henv a x hx; have hc := bwv_lt henv c y hy
      simp only [E.eval, Ops.select]
      split
      · exact Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _))
      · exact Nat.lt_of_lt_of_le hc (Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _))
    next => cases h
  | .un o w a, b, h => bw_lt _ b h env
  | .bin o w a c, b, h => bw_lt _ b h env

/-- `bwv`, plus packed pairs (as `bwp`). -/
def bwpv (ws : List Nat) : E → Option Nat
  | .bin .addi W A (.bin .shli W2 B (.lit w0)) =>
    match bwpv ws A, bwpv ws B with
    | some a, some b => if W2 = W ∧ a ≤ w0 ∧ w0 + b ≤ W then some (w0 + b) else some W
    | _, _ => some W
  | e => bwv ws e
termination_by structural e => e

theorem bwpv_lt_aux {ws env : List Nat} (henv : EnvOK ws env) : ∀ (n : Nat) (e : E) (b : Nat), sizeOf e < n →
    bwpv ws e = some b → e.eval env < 2 ^ b
  | 0, _, _, hs, _ => absurd hs (Nat.not_lt_zero _)
  | n + 1, e, b, hs, h => by
    unfold bwpv at h
    split at h
    next W A W2 B w0 =>
      have hW : (E.bin .addi W A (.bin .shli W2 B (.lit w0))).eval env < 2 ^ W :=
        Nat.mod_lt _ (Nat.two_pow_pos W)
      simp only [E.bin.sizeOf_spec, E.lit.sizeOf_spec] at hs
      split at h
      next a bb ha hb =>
        split at h
        next hk =>
          obtain ⟨rfl, h1, h2⟩ := hk
          obtain rfl := (Option.some.inj h).symm
          have hA : A.eval env < 2 ^ w0 :=
            Nat.lt_of_lt_of_le (bwpv_lt_aux henv n A a (by omega) ha) (Nat.pow_le_pow_right (by decide) h1)
          have hB : B.eval env < 2 ^ bb := bwpv_lt_aux henv n B bb (by omega) hb
          simp only [E.eval, BOp.ev]
          rw [pack_val hA hB h2]
          have h1' : A.eval env + B.eval env * 2 ^ w0 < (B.eval env + 1) * 2 ^ w0 := by
            rw [Nat.succ_mul]; omega
          have h2' : (B.eval env + 1) * 2 ^ w0 ≤ 2 ^ bb * 2 ^ w0 := Nat.mul_le_mul_right _ hB
          rw [Nat.pow_add, Nat.mul_comm (2 ^ w0)]; omega
        next => obtain rfl := (Option.some.inj h).symm; exact hW
      next => obtain rfl := (Option.some.inj h).symm; exact hW
    next => exact bwv_lt henv _ b h

theorem bwpv_lt {ws env : List Nat} (henv : EnvOK ws env) (e : E) (b : Nat) (h : bwpv ws e = some b) :
    e.eval env < 2 ^ b :=
  bwpv_lt_aux henv (sizeOf e + 1) e b (Nat.lt_succ_self _) h

/-! ## The slice rules with variable widths -/

def unsliceW (ws : List Nat) : E → Option E
  | .un .trunci w (.bin .shrui W (.bin .addi W1 A (.bin .shli W2 B (.lit w0))) (.lit lo)) =>
    match bwpv ws A, bwpv ws B with
    | some a, some b =>
      if W1 = W ∧ W2 = W ∧ a ≤ w0 ∧ w0 + b ≤ W then
        if lo + w ≤ w0 then some (.un .trunci w (.bin .shrui W A (.lit lo)))
        else if w0 ≤ lo then some (.un .trunci w (.bin .shrui W B (.lit (lo - w0))))
        else none
      else none
    | _, _ => none
  | .un .trunci w (.bin .shrui W B (.lit 0)) =>
    match bwpv ws B with
    | some b => if b ≤ w ∧ b ≤ W then some B else none
    | none => none
  | _ => none

theorem unsliceW_eval {ws env : List Nat} (henv : EnvOK ws env) {F F' : E} (h : unsliceW ws F = some F') :
    F'.eval env = F.eval env := by
  unfold unsliceW at h
  split at h
  next w W W1 A W2 B w0 lo =>
    split at h
    next a b ha hb =>
      split at h
      next hk =>
        obtain ⟨rfl, rfl, h0, h1⟩ := hk
        have hA : A.eval env < 2 ^ w0 :=
          Nat.lt_of_lt_of_le (bwpv_lt henv A a ha) (Nat.pow_le_pow_right (by decide) h0)
        have hB : B.eval env < 2 ^ b := bwpv_lt henv B b hb
        split at h
        next hl =>
          obtain rfl := (Option.some.inj h).symm
          simp only [E.eval, UOp.ev, BOp.ev]
          exact (slice_lo hA hB h1 hl).symm
        next =>
          split at h
          next hl =>
            obtain rfl := (Option.some.inj h).symm
            simp only [E.eval, UOp.ev, BOp.ev]
            exact (slice_hi hA hB h1 hl).symm
          next => cases h
      next => cases h
    next => cases h
  next w W B hne =>
    split at h
    next b hb =>
      split at h
      next hk =>
        obtain rfl := (Option.some.inj h).symm
        simp only [E.eval, UOp.ev, BOp.ev]
        exact (slice_id (bwpv_lt henv _ b hb) hk.1 hk.2).symm
      next => cases h
    next => cases h
  next => cases h

def unsliceDeepW (ws : List Nat) (e : E) : E :=
  match unsliceW ws e with
  | some e' => e'
  | none =>
    match e with
    | .un o w a => .un o w (unsliceDeepW ws a)
    | .bin o w a b => .bin o w (unsliceDeepW ws a) (unsliceDeepW ws b)
    | .sel s a b => .sel (unsliceDeepW ws s) (unsliceDeepW ws a) (unsliceDeepW ws b)
    | e => e
termination_by structural e

theorem unsliceDeepW_eval {ws env : List Nat} (henv : EnvOK ws env) : ∀ e : E,
    (unsliceDeepW ws e).eval env = e.eval env := by
  intro e
  induction e with
  | var k => unfold unsliceDeepW; split <;> rename_i h <;> first | exact unsliceW_eval henv h | rfl
  | lit v => unfold unsliceDeepW; split <;> rename_i h <;> first | exact unsliceW_eval henv h | rfl
  | un o w a ih =>
    unfold unsliceDeepW; split
    · rename_i h; exact unsliceW_eval henv h
    · simp only [E.eval, ih]
  | bin o w a b iha ihb =>
    unfold unsliceDeepW; split
    · rename_i h; exact unsliceW_eval henv h
    · simp only [E.eval, iha, ihb]
  | sel s a b ihs iha ihb =>
    unfold unsliceDeepW; split
    · rename_i h; exact unsliceW_eval henv h
    · simp only [E.eval, ihs, iha, ihb]

def unsliceNW (ws : List Nat) : Nat → E → E
  | 0, e => e
  | n + 1, e => unsliceNW ws n (unsliceDeepW ws e)

theorem unsliceNW_eval {ws env : List Nat} (henv : EnvOK ws env) : ∀ (n : Nat) (e : E),
    (unsliceNW ws n e).eval env = e.eval env
  | 0, _ => rfl
  | n + 1, e => by simp only [unsliceNW, unsliceNW_eval henv n, unsliceDeepW_eval henv]

/-! ## Rules that keep tokens within a width map -/

theorem envOK_of_pw {W : List Nat} : ∀ {ins vs : List Nat}, Pw (InW W) ins vs → EnvOK (ins.map (wOf W)) vs
  | [], [], _ => fun k hk => absurd (by simp [wOf]) hk
  | c :: cs, v :: vs, h => by
    intro k hk
    cases k with
    | zero =>
      have h1 : wOf W c = 0 ∨ v < 2 ^ wOf W c := h.1
      have e1 : wOf (List.map (wOf W) (c :: cs)) 0 = wOf W c := by simp [wOf]
      rw [e1] at hk ⊢
      rcases h1 with h1 | h1
      · exact absurd h1 hk
      · simpa using h1
    | succ k =>
      have e1 : wOf (List.map (wOf W) (c :: cs)) (k + 1) = wOf (List.map (wOf W) cs) k := by simp [wOf]
      rw [e1] at hk ⊢
      have := envOK_of_pw h.2 k hk
      simpa using this
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- Width of `a` fits within width of `b` (or `b` has none). -/
def wle (W : List Nat) (a b : Nat) : Bool := wOf W b == 0 || (wOf W a != 0 && decide (wOf W a ≤ wOf W b))

theorem wle_ok {W : List Nat} {a b : Nat} (h : wle W a b = true) {v : Nat} (hv : InW W a v) : InW W b v := by
  simp only [wle, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · rcases hv with hv | hv
    · exact absurd hv h1
    · exact Or.inr (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) h2))

/-- A rule fired from a store whose tokens fit `W` pushes only tokens that fit `W` (checked). -/
def safeB (W : List Nat) : Rule → Bool
  | .comp ins o e => wOf W o == 0 ||
      (match bwpv (ins.map (wOf W)) e with
       | some b => decide (b ≤ wOf W o)
       | none => false)
  | .fork i os => os.all (wle W i)
  | .branch _ d t f => wle W d t && wle W d f
  | .mux _ ds o _ => ds.all (fun d => wle W d o)
  | .cm i res idx k => wle W i res && (wOf W idx == 0 || decide (k < 2 ^ wOf W idx))
  | .sink _ => true

theorem safeB_ok {W : List Nat} {r : Rule} (h : safeB W r = true) : RuleSafe (InW W) r := by
  cases r with
  | comp ins o e =>
    apply comp_safe; intro vs hvs
    simp only [safeB, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · exact Or.inl h
    · right
      split at h
      next b hb =>
        exact Nat.lt_of_lt_of_le (bwpv_lt (envOK_of_pw hvs) e b hb)
          (Nat.pow_le_pow_right (by decide) (of_decide_eq_true h))
      next => cases h
  | fork i os => exact fork_safe fun o ho v hv => wle_ok (List.all_eq_true.mp h o ho) hv
  | branch c d t f =>
    simp only [safeB, Bool.and_eq_true] at h
    exact branch_safe fun v hv => ⟨wle_ok h.1 hv, wle_ok h.2 hv⟩
  | mux s ds o iw => exact mux_safe fun d hd v hv => wle_ok (List.all_eq_true.mp h d hd) hv
  | cm i res idx k =>
    simp only [safeB, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    exact cm_safe (fun v hv => wle_ok h.1 hv) (by rcases h.2 with h2 | h2; exact Or.inl h2; exact Or.inr h2)
  | sink i => exact sink_safe

/-! ## Runs under a store invariant -/

/-- Rewrites that preserve complete runs from the initial stores satisfying `P`. -/
structure SoundP (P : Store Nat Nat → Prop) (rs rs' : List Rule) (pre chg : List Nat) : Prop where
  fwd : ∀ {σ0 t : Store Nat Nat} {n : Nat}, P σ0 → (∀ c ∈ pre, σ0 c = []) → Run (step (graph rs)) σ0 n t →
    Terminal (step (graph rs)) t →
    ∃ t' m, Run (step (graph rs')) σ0 m t' ∧ Terminal (step (graph rs')) t' ∧ Agree chg t t'
  bwd : ∀ {σ0 t' : Store Nat Nat} {n : Nat}, P σ0 → (∀ c ∈ pre, σ0 c = []) → Run (step (graph rs')) σ0 n t' →
    Terminal (step (graph rs')) t' →
    ∃ t m, Run (step (graph rs)) σ0 m t ∧ Terminal (step (graph rs)) t ∧ Agree chg t' t

theorem Sound.toP {rs rs' : List Rule} {pre chg : List Nat} (h : Sound rs rs' pre chg) (P : Store Nat Nat → Prop) :
    SoundP P rs rs' pre chg :=
  ⟨fun _ => h.fwd, fun _ => h.bwd⟩

theorem SoundP.symm {P : Store Nat Nat → Prop} {rs rs' : List Rule} {p c : List Nat} (h : SoundP P rs rs' p c) :
    SoundP P rs' rs p c :=
  ⟨h.bwd, h.fwd⟩

theorem SoundP.mono {P Q : Store Nat Nat → Prop} {rs rs' : List Rule} {p c : List Nat} (hPQ : ∀ σ, P σ → Q σ)
    (h : SoundP Q rs rs' p c) : SoundP P rs rs' p c :=
  ⟨fun hP => h.fwd (hPQ _ hP), fun hP => h.bwd (hPQ _ hP)⟩

theorem SoundP.trans {P : Store Nat Nat → Prop} {rs1 rs2 rs3 : List Rule} {p1 c1 p2 c2 : List Nat}
    (h1 : SoundP P rs1 rs2 p1 c1) (h2 : SoundP P rs2 rs3 p2 c2) : SoundP P rs1 rs3 (p1 ++ p2) (c1 ++ c2) := by
  constructor
  · intro σ0 t n hP h0 hr ht
    obtain ⟨t2, m2, r2, ht2, a2⟩ := h1.fwd hP (fun c hc => h0 c (List.mem_append_left _ hc)) hr ht
    obtain ⟨t3, m3, r3, ht3, a3⟩ := h2.fwd hP (fun c hc => h0 c (List.mem_append_right _ hc)) r2 ht2
    exact ⟨t3, m3, r3, ht3, a2.trans a3⟩
  · intro σ0 t n hP h0 hr ht
    obtain ⟨t2, m2, r2, ht2, a2⟩ := h2.bwd hP (fun c hc => h0 c (List.mem_append_right _ hc)) hr ht
    obtain ⟨t1, m1, r1, ht1, a1⟩ := h1.bwd hP (fun c hc => h0 c (List.mem_append_left _ hc)) r2 ht2
    exact ⟨t1, m1, r1, ht1, (a2.trans a1).mono (fun c hc => by
      rcases List.mem_append.mp hc with h | h
      · exact List.mem_append_right _ h
      · exact List.mem_append_left _ h)⟩

section Inv
variable {Q : Nat → Nat → Prop} {rs rs' : List Rule}

theorem sinv_step_safe (hs : ∀ (l : Nat) (r : Rule), rs[l]? = some r → RuleSafe Q r) {σ σ1 : Store Nat Nat} {l : Nat}
    (h : step (graph rs) σ l = some σ1) (hI : SInv Q σ) : SInv Q σ1 := by
  obtain ⟨r, fr, hr, hf, rfl⟩ := step_some_rule h
  exact sinv_apply hI (hs l r hr σ fr hI hf)

theorem run_inv_fwd (hs : ∀ (l : Nat) (r : Rule), rs[l]? = some r → RuleSafe Q r)
    (h : ∀ (l : Nat) (σ : Store Nat Nat), SInv Q σ → step (graph rs') σ l = step (graph rs) σ l) :
    ∀ {σ t : Store Nat Nat} {n : Nat}, Run (step (graph rs)) σ n t → SInv Q σ →
      Run (step (graph rs')) σ n t ∧ SInv Q t := by
  intro σ t n hr
  induction hr with
  | refl s => exact fun hI => ⟨Run.refl s, hI⟩
  | cons l hl _ ih =>
    intro hI
    have k := ih (sinv_step_safe hs hl hI)
    exact ⟨Run.cons l (by rw [h l _ hI]; exact hl) k.1, k.2⟩

theorem run_inv_bwd (hs : ∀ (l : Nat) (r : Rule), rs[l]? = some r → RuleSafe Q r)
    (h : ∀ (l : Nat) (σ : Store Nat Nat), SInv Q σ → step (graph rs') σ l = step (graph rs) σ l) :
    ∀ {σ t : Store Nat Nat} {n : Nat}, Run (step (graph rs')) σ n t → SInv Q σ →
      Run (step (graph rs)) σ n t ∧ SInv Q t := by
  intro σ t n hr
  induction hr with
  | refl s => exact fun hI => ⟨Run.refl s, hI⟩
  | @cons s s' _ _ l hl _ ih =>
    intro hI
    have hl' : step (graph rs) s l = some s' := by rw [← h l s hI]; exact hl
    have k := ih (sinv_step_safe hs hl' hI)
    exact ⟨Run.cons l hl' k.1, k.2⟩

/-- Every rule of `rs` keeps `Q`, and `rs'` fires like `rs` from every `Q`-store: same complete runs from
`Q`-stores. -/
theorem soundP_of_inv (hs : ∀ (l : Nat) (r : Rule), rs[l]? = some r → RuleSafe Q r)
    (h : ∀ (l : Nat) (σ : Store Nat Nat), SInv Q σ → step (graph rs') σ l = step (graph rs) σ l) : SoundP (SInv Q) rs rs' [] [] := by
  constructor
  · intro σ0 t n hP _ hr ht
    obtain ⟨r', hI⟩ := run_inv_fwd hs h hr hP
    exact ⟨t, n, r', fun l => by rw [h l t hI]; exact ht l, fun _ _ => rfl⟩
  · intro σ0 t n hP _ hr ht
    obtain ⟨r', hI⟩ := run_inv_bwd hs h hr hP
    exact ⟨t, n, r', fun l => by rw [← h l t hI]; exact ht l, fun _ _ => rfl⟩

end Inv

/-! ## The width-checked unpack step -/

theorem pw_store {W : List Nat} {σ : Store Nat Nat} (hI : SInv (InW W) σ) :
    ∀ {ins : List Nat}, (∀ c ∈ ins, σ c ≠ []) → Pw (InW W) ins (ins.map (hd σ))
  | [], _ => trivial
  | c :: cs, hall => by
    refine ⟨?_, pw_store hI (fun d hd => hall d (List.mem_cons_of_mem _ hd))⟩
    have hc := hall c (by simp)
    cases hσ : σ c with
    | nil => exact absurd hσ hc
    | cons v vs => exact hI c v (by rw [hσ]; simp) |>.elim (fun h => Or.inl h) (fun h => by
        right; simp only [hd, hσ, List.headD_cons]; exact h)

theorem fire_eq_inv {W ins : List Nat} {o : Nat} {F F' : E}
    (hF : ∀ env, EnvOK (ins.map (wOf W)) env → F'.eval env = F.eval env) {σ : Store Nat Nat}
    (hI : SInv (InW W) σ) : (Rule.comp ins o F').fire natVI σ = (Rule.comp ins o F).fire natVI σ := by
  by_cases hall : ∀ c ∈ ins, σ c ≠ []
  · rw [fire_comp hall, fire_comp hall, hF _ (envOK_of_pw (pw_store hI hall))]
  · obtain ⟨c, hc, he⟩ := exists_empty hall
    rw [fire_comp_none hc he, fire_comp_none hc he]

def applyUW (rs : List Rule) (l : Nat) (W : List Nat) : Option Res :=
  match rs[l]? with
  | some (.comp ins o F) =>
    if allL rs (fun _ r => safeB W r) = true then
      some (rs.set l (.comp ins o (unsliceNW (ins.map (wOf W)) 8 F)), [], [])
    else none
  | _ => none

theorem applyUW_sound {rs : List Rule} {l : Nat} {W : List Nat} {res : Res} (h : applyUW rs l W = some res) :
    SoundP (SInv (InW W)) rs res.1 res.2.1 res.2.2 := by
  unfold applyUW at h
  split at h
  next ins o F hl =>
    split at h
    next hA =>
      obtain rfl := (Option.some.inj h).symm
      refine soundP_of_inv (fun k r hr => safeB_ok (of_allL hA k r hr)) ?_
      intro k σ hI
      by_cases e : k = l
      · subst e
        rw [step_graph hl, step_graph (set_self hl),
          fire_eq_inv (fun env henv => unsliceNW_eval henv 8 F) hI]
      · simp only [step, graph, graphV, set_ne (Ne.symm e)]
    next => cases h
  next => cases h

/-! ## Dedupe read backward -/

/-- The fork at `lf` gets outputs `os'` and the comp at `lc` reads `ins'` with expression `F'`; checked: deduping
`b` into `a` (`Dedupe`) gives the old rules exactly. -/
def applyUD (rs : List Rule) (lf lc a b : Nat) (os' ins' : List Nat) (F' : E) : Option Res :=
  match rs[lf]?, rs[lc]? with
  | some (.fork x _), some (.comp _ y _) =>
    match applyDD ((rs.set lf (.fork x os')).set lc (.comp ins' y F')) lf lc a b with
    | some (rs2, pre, chg) =>
      if rs2 = rs then some ((rs.set lf (.fork x os')).set lc (.comp ins' y F'), pre, chg) else none
    | none => none
  | _, _ => none

theorem applyUD_sound {rs : List Rule} {lf lc a b : Nat} {os' ins' : List Nat} {F' : E} {res : Res}
    (h : applyUD rs lf lc a b os' ins' F' = some res) : Sound rs res.1 res.2.1 res.2.2 := by
  unfold applyUD at h
  split at h
  next =>
    split at h
    next rs2 pre chg hr =>
      split at h
      next he =>
        subst he
        obtain rfl := (Option.some.inj h).symm
        exact (applyDD_sound hr).symm
      next => cases h
    next => cases h
  next => cases h

/-! ## Scripts under the width assumption -/

/-- **The width assumption on an initial store**: every channel from `NA` on is empty (only the `NA` inputs hold
tokens), and every token on input channel `c` fits its declared width `Wi[c]` (`0`: no width declared). -/
def InP (NA : Nat) (Wi : List Nat) (σ0 : Store Nat Nat) : Prop :=
  (∀ ch, NA ≤ ch → σ0 ch = []) ∧ SInv (InW Wi) σ0

theorem inP_mk {NA : Nat} {Wi : List Nat} {σ0 : Store Nat Nat} (h0 : ∀ ch, NA ≤ ch → σ0 ch = [])
    (hW : ∀ ch v, v ∈ σ0 ch → InW Wi ch v) : InP NA Wi σ0 :=
  And.intro h0 hW

/-- `W` assumes of an input channel no width narrower than declared. -/
def agreeB (NA : Nat) (Wi W : List Nat) : Bool :=
  (List.range NA).all (fun c => wOf W c == 0 || (wOf Wi c != 0 && decide (wOf Wi c ≤ wOf W c)))

theorem inP_inv {NA : Nat} {Wi W : List Nat} (h : agreeB NA Wi W = true) {σ0 : Store Nat Nat} (hP : InP NA Wi σ0) :
    SInv (InW W) σ0 := by
  intro ch v hv
  by_cases hc : ch < NA
  · have := List.all_eq_true.mp h ch (List.mem_range.mpr hc)
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at this
    rcases this with h1 | ⟨h1, h2⟩
    · exact Or.inl h1
    · rcases hP.2 ch v hv with h3 | h3
      · exact absurd h3 h1
      · exact Or.inr (Nat.lt_of_lt_of_le h3 (Nat.pow_le_pow_right (by decide) h2))
  · rw [hP.1 ch (by omega)] at hv; cases hv

inductive StepW
  | rf (s : StepRF)
  | unpackw (l : Nat) (W : List Nat)
  | undedupe (lf lc a b : Nat) (os ins : List Nat) (F : E)
  deriving Repr

def applyStepW (NA : Nat) (Wi : List Nat) (rs : List Rule) : StepW → Option Res
  | .rf s => applyStepRF rs s
  | .unpackw l W => if agreeB NA Wi W = true then applyUW rs l W else none
  | .undedupe lf lc a b os ins F => applyUD rs lf lc a b os ins F

def runScriptW (NA : Nat) (Wi : List Nat) : List Rule → List StepW → Option Res
  | rs, [] => some (rs, [], [])
  | rs, s :: ss =>
    match applyStepW NA Wi rs s with
    | some (rs1, p1, c1) =>
      match runScriptW NA Wi rs1 ss with
      | some (rs2, p2, c2) => some (rs2, p1 ++ p2, c1 ++ c2)
      | none => none
    | none => none

theorem applyStepW_sound {NA : Nat} {Wi : List Nat} {rs : List Rule} {s : StepW} {res : Res}
    (h : applyStepW NA Wi rs s = some res) : SoundP (InP NA Wi) rs res.1 res.2.1 res.2.2 := by
  cases s with
  | rf s => exact (applyStepRF_sound h).toP _
  | unpackw l W =>
    simp only [applyStepW] at h
    split at h
    next hag => exact (applyUW_sound h).mono (fun _ hP => inP_inv hag hP)
    next => cases h
  | undedupe lf lc a b os ins F => exact (applyUD_sound h).toP _

/-- **The pass theorem under the width assumption.** A script `runScriptW NA Wi` accepts preserves complete runs
from every initial store satisfying `InP NA Wi` (inputs only, each input token within its declared width). -/
theorem runScriptW_sound {NA : Nat} {Wi : List Nat} : ∀ {rs : List Rule} {ss : List StepW} {rs' : List Rule}
    {pre chg : List Nat}, runScriptW NA Wi rs ss = some (rs', pre, chg) → SoundP (InP NA Wi) rs rs' pre chg := by
  intro rs ss
  induction ss generalizing rs with
  | nil => intro rs' pre chg h; simp only [runScriptW, Option.some.injEq, Prod.mk.injEq] at h
           obtain ⟨rfl, rfl, rfl⟩ := h; exact (Sound.refl rs).toP _
  | cons s ss ih =>
    intro rs' pre chg h
    simp only [runScriptW] at h
    split at h
    next rs1 p1 c1 h1 =>
      split at h
      next rs2 p2 c2 h2 =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact (applyStepW_sound h1).trans (ih h2)
      next => cases h
    next => cases h

end Formal.Rewrite.Steps
