import Formal.Net.CapstoneRigAllWalk
import Formal.Net.CapstoneWalk

/-!
# Probe C-8s3: the periodic H_WALK for gcd_hw, from 8s's H_WALK and the token run

`WalkOKR` (the periodic walk's arbiter condition, `CapstoneRigAllWalk`) follows from 8s's
`WalkOK` once the stream solution is periodic along the walk: every invocation of the
periodic walk visits each spine channel exactly as often as the first, and the steer selects
and arbiter oracles it reads repeat with that period. Both facts are read off the complete
token run `y` of 8s (`good_run`):

* `Wf c = |history of grp c|`: at the end of the walk (8s's `walk_sim`, cursor `none`) the
  spine is empty and the walk's visit counts are the consumed counts of the run's spine
  groups; after that state no firing touches the spine (`push_le_pop`, the spine check
  `GcdHw.spine_ok`), so they are the final histories' lengths.
* periods: a control steer's select is its branch's condition history, of the same length as
  the branch's data history (`BrI`); an arbiter oracle is its control_merge's label history,
  of the same length as the result history (`RI.cml`, `RI.lab`).
-/

namespace Formal.Net.GcdHw
open Formal.Net.Kahn

/-- The spine check's per-firing content: a firing pushes no more tokens onto the spine than
it pops from it (the core of `closed_of_check`, restated). -/
theorem push_le_pop (P : List Nat) (rs : List Rule) (hP : P.Nodup)
    (h : rs.all (Rule.okP P) = true) (s : Store Nat Nat) (l : Nat) (res : Fire Nat Nat)
    (hres : (graph rs l).fire s = some res) :
    (P.map fun c => (res.2 c).length).sum ≤ (P.map res.1).sum := by
  unfold graph graphV at hres
  split at hres
  · rename_i r hr
    have hok : r.okP P = true := List.all_eq_true.mp h r (List.mem_of_getElem? hr)
    change Rule.fire natVI r s = some res at hres
    cases r with
    | mux s0 ds o iw =>
      change muxF natVI s0 ds o iw s = some res at hres
      obtain ⟨v, vs, j, d, x, xs, -, -, -, -, -, rfl⟩ := muxF_some hres
      simp only [Rule.okP, Bool.not_eq_true', decide_eq_false_iff_not] at hok
      have h1 := sum_one P hP o
      simp only [hok, ↓reduceIte] at h1
      have : (P.map fun c => ((fun y => if y = o then [x] else []) c).length).sum ≤
          (P.map fun c => if c = o then 1 else 0).sum :=
        sum_le (fun c => by simp only; split <;> simp)
      simp only at this ⊢; omega
    | comp ins o e =>
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
          decide_eq_true_eq] at hok
        obtain ⟨c, hc, hcP⟩ := hok
        have := popOf_sum hc hcP; simp [ho] at h1; omega
      · simp [ho] at h1; omega
    | fork i os =>
      change strictF _ _ s = some res at hres
      obtain ⟨vs, out, hh, hg, rfl⟩ := strictF_some hres
      simp only [Rule.out, Option.some.injEq] at hg; subst hg
      show (P.map fun c => (if c ∈ os then vs.take 1 else []).length).sum ≤ (P.map (popOf [i])).sum
      simp only [Rule.okP, decide_eq_true_eq] at hok
      have a : (P.map fun c => (if c ∈ os then vs.take 1 else []).length).sum ≤
          (P.map fun c => if c ∈ os then 1 else 0).sum :=
        sum_le (fun c => by split; exact take1_len vs; simp)
      rw [sum_ind_filter] at a
      by_cases hi : i ∈ P
      · have := popOf_sum (ins := [i]) (by simp) hi; rw [if_pos hi] at hok; omega
      · rw [if_neg hi] at hok; omega
    | branch c d t f =>
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
            simp only [Rule.okP, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hok
            have hcd : c ∈ P ∨ d ∈ P := by
              rcases hok with (h0 | h0) | h0
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
      simp only [Rule.okP, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
        decide_eq_false_iff_not, decide_eq_true_eq] at hok
      obtain ⟨⟨hidx, hres'⟩, hne⟩ := hok
      have h1 := sum_one P hP r0
      have a : (P.map fun c => ((if c = r0 then vs.take 1 else []) ++
            (if c = idx then [natVI.lit k] else [])).length).sum ≤
          (P.map fun c => if c = r0 then 1 else 0).sum := by
        apply sum_le_mem; intro c hc
        have e2 : c ≠ idx := fun e => hidx (e ▸ hc)
        simp only [e2, ↓reduceIte, List.append_nil]; split; exact take1_len vs; simp
      by_cases hp : r0 ∈ P
      · have := popOf_sum (ins := [i]) (by simp) (hres'.resolve_left (fun h => h hp)); rw [if_pos hp] at h1; omega
      · rw [if_neg hp] at h1; omega
    | sink i =>
      change strictF _ _ s = some res at hres
      obtain ⟨vs, out, hh, hg, rfl⟩ := strictF_some hres
      simp only [Rule.out, Option.some.injEq] at hg; subst hg
      show (P.map fun _ => ([] : List Nat).length).sum ≤ _
      exact Nat.le_trans (Nat.le_of_eq (sum_zero (fun _ _ => rfl))) (Nat.zero_le _)
  · cases hres

end Formal.Net.GcdHw

namespace Formal.Net.CapNet.Gcd
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.GcdHw
open Formal.Net.CapSafe Formal.Net.Kahn Formal.Net.GcdHw.Gcd

set_option maxRecDepth 100000

/-! ## After the spine token is gone, the spine is quiet -/

/-- With no spine token, a firing leaves every spine channel empty and its consumed history
unchanged. -/
theorem quiet0 {x x1 : TS} {l : Nat} (hemp : ∀ h ∈ spine, x.s h = [])
    (ht : tstep x l = some x1) : ∀ h ∈ spine, x1.s h = [] ∧ x1.cn h = x.cn h := by
  obtain ⟨f, hf, hs, hc, -⟩ := tstep_some ht
  have hpop : ∀ h ∈ spine, f.1 h = 0 := by
    intro h hh
    have := (G l).pop_le x.s f h hf
    rw [hemp h hh] at this; simpa using this
  have hpp := push_le_pop spine rules spine_nodup spine_ok x.s l f hf
  rw [sum_zero hpop] at hpp
  intro h hh
  have hz : (f.2 h).length = 0 := by
    have := le_sum_of_mem (f := fun c => (f.2 c).length) hh; omega
  refine ⟨?_, ?_⟩
  · rw [hs]; simp [applyF, hpop h hh, hemp h hh, List.length_eq_zero_iff.mp hz]
  · rw [hc, hpop h hh]; simp

theorem quiet0_run : ∀ (ls : List Nat) (x y : TS), (∀ h ∈ spine, x.s h = []) →
    texec x ls = some y → ∀ h ∈ spine, y.cn h = x.cn h := by
  intro ls
  induction ls with
  | nil => intro x y _ h; simp [texec] at h; subst h; intro _ _; rfl
  | cons l ls ih =>
    intro x y hemp h
    simp only [texec] at h
    cases ht : tstep x l with
    | none => rw [ht] at h; simp at h
    | some x1 =>
      rw [ht] at h
      have hq := quiet0 hemp ht
      have := ih x1 y (fun g hg => (hq g hg).1) h
      intro g hg; rw [this g hg, (hq g hg).2]

/-! ## Periods -/

theorem perL_period (L : List Nat) (d m k : Nat) : perL L d (m * L.length + k) = perL L d k := by
  unfold perL
  split
  · rfl
  · rw [show m * L.length + k = k + m * L.length by omega, Nat.add_mul_mod_self_right]

section per
variable {a b : Nat} {y : TS} {ls : List Nat} (hy : Good a b y) (hex : texec (x0 a b) ls = some y)

include hex in
theorem ri_y : RI a b y := texec_pres (ri_pres a b) ls (x0 a b) y hex (ri_x0 a b)

theorem A_one {c : Fin NC} {g : Nat} (h : al c = [g]) : A y c = (y.cn g).length := by
  simp [A, h]

theorem nxt_eEnd_none (σ : Fin NC → Nat → Nat) (k : Nat) : nxt σ eEnd k = none := by
  simp [nxt, cons_eEnd]

include hy hex in
/-- **Visit counts of one invocation**: at the walk's first arrival on `eEnd`, every other
spine channel has been visited as often as its token-run group was consumed. -/
theorem end_counts {P : Nat} (hP : (walk (σY a b y) P).cur = some eEnd) :
    ∀ c, sp c = true → c ≠ eEnd → (walk (σY a b y) P).W c = A y c := by
  intro c hc hce
  obtain ⟨x, ⟨_, ls', hx⟩, hR⟩ := walk_sim hy hex (P + 1)
  have hcur : (walk (σY a b y) (P + 1)).cur = none := by
    rw [cur_succ, hP]; simp [nxt_eEnd_none]
  have h1 := hR.cnt c hc
  rw [hcur, W_succ] at h1
  have hv : visB (σY a b y) c P = false := by
    unfold visB; rw [hP]; simp [Ne.symm hce]
  rw [hv] at h1
  rw [show ((none : Option (Fin NC)) == some c) = false from rfl] at h1
  simp only [bn, Bool.false_eq_true, ite_false, Nat.add_zero, Option.map_none, Bo] at h1
  rw [h1]
  have hq := quiet0_run ls' x y (hR.emp hcur) hx
  unfold A
  congr 1
  apply List.map_congr_left
  intro g hg
  rw [hq g ((glob hc).2.1 g hg)]

include hy hex in
/-- A control steer's select repeats with the period `A y c` of its input. -/
theorem sel_period {c j t f : Fin NC} (hs : sp c = true) (hk : opAt (consOf c) = .steerC j t f) :
    ∀ m k, σY a b y c (m * A y c + k) = σY a b y c k := by
  have hok := cOK_of hs
  unfold cOK at hok
  rw [hk] at hok
  simp only [Bool.and_eq_true] at hok
  have hst := hok.2
  unfold steerR at hst
  split at hst
  · rename_i gc gd gt gf hr
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, Bool.not_eq_true'] at hst
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ha, hgd⟩, -⟩, -⟩, -⟩, -⟩, h3⟩, h250⟩, hcond⟩, -⟩, -⟩, -⟩, -⟩ := hst
    obtain ⟨cc, dd, d0, hd, hh⟩ := condOK_spec hcond
    have hal := (glob hs).2.2 ha
    have hbr := (hy.br _ gc gd gt gf hr).1
    have hn : A y c = (Hh a b y gc).length := by
      rw [A_one hal, Hh_cn hy h3 h250, hbr, hgd]
    intro m k
    rw [hn]
    simp only [σY]
    rw [ref_bj tab _ rank_ok hd (by simp), ref_bj tab _ rank_ok hd (by simp)]
    simp only [List.map_cons, List.map_nil, E.eval, List.getD_cons_zero]
    rw [ref_hist tab _ hh nf_pos, ref_hist tab _ hh nf_pos, perL_period]
  · simp at hst

include hy hex in
/-- The walk's successor repeats with the period `A y c`. -/
theorem nxt_period {c : Fin NC} (hs : sp c = true) (m k : Nat) :
    nxt (σY a b y) c (m * A y c + k) = nxt (σY a b y) c k := by
  unfold nxt
  split
  · rfl
  · rfl
  · rfl
  · rename_i j t f hk
    rw [sel_period hy hex hs hk]
  · rfl
  · rfl

include hy hex in
/-- An arbiter oracle repeats with the period `A y z` of the stage's output. -/
theorem om_period {o : Fin NO} {x u z : Fin NC} {w : Nat} (ho : opAt o = .amerge x u z w) :
    ∀ m k, omOf a b y w (m * A y z + k) = omOf a b y w k := by
  have hs := spok o
  rw [ho] at hs
  simp only [SpOK, Bool.and_eq_true, bne_iff_ne, ne_eq] at hs
  have huo : consOf u = o := cons_in o u (by rw [ho]; simp [K.insC])
  have hok := cOK_of hs.1.1.2
  unfold cOK at hok
  rw [huo, ho] at hok
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hok
  have hR := ri_y hex
  have ham : amR u u z w = true := by
    rcases hok with h | h
    · exfalso
      have := h.2
      unfold accOK at this
      simp only [Bool.and_eq_true, beq_iff_eq] at this
      exact hs.2 this.1.1.1.1.2.symm
    · exact h.2
  unfold amR at ham
  simp only [Bool.and_eq_true] at ham
  have ham2 := ham.2
  split at ham2
  · rename_i i res idx kk hr
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, Bool.not_eq_true',
      decide_eq_true_eq] at ham2
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, hres⟩, -⟩, -⟩, hidx3⟩, hres3⟩, hidx250⟩, -⟩, hw⟩ := ham2
    have hcml := hR.cml _ i res idx kk hr
    unfold omOf
    intro m k
    split at hw
    · rename_i gi hgi
      simp only [Bool.and_eq_true, beq_iff_eq] at hw
      obtain ⟨⟨rfl, hal⟩, -⟩ := hw
      have hsp := (glob hs.1.2).2.1 res (by rw [hal]; simp)
      have hne := noend hsp
      have hn : A y z = (Hh a b y gi).length := by
        rw [A_one hal, Hh_pr hidx3, hcml, ← Hh_pr hres3, Hh_cn hy hne.1 hne.2]
      rw [hgi, hn]
      simp only [W.om]
      rw [perL_period]
    · rename_i gi hgi
      simp only [Bool.and_eq_true, beq_iff_eq] at hw
      obtain ⟨⟨⟨rfl, rfl⟩, hal⟩, -⟩ := hw
      have hn : A y z = ((Hh a b y 249).filter (fun v => v % 4 != 2)).length := by
        rw [Hh_pr (by decide), hR.lab]; simp [A, hal]
      rw [hgi, hn]
      simp only [W.om]
      rw [perL_period]
    · rename_i gi hgi
      simp only [Bool.and_eq_true, beq_iff_eq] at hw
      obtain ⟨⟨⟨rfl, hal⟩, -⟩, -⟩ := hw
      have hsp := (glob hs.1.2).2.1 res (by rw [hal]; simp)
      have hne := noend hsp
      have hn : A y z = (Hh a b y gi).length := by
        rw [A_one hal, Hh_pr hidx3, hcml, ← Hh_pr hres3, Hh_cn hy hne.1 hne.2]
      rw [hgi, hn]
      simp only [W.om]
      rw [perL_period]
  · simp at ham2

end per

/-! ## The periodic walk is the one-invocation walk, repeated -/

section ag
variable (σ : Fin NC → Nat → Nat)

theorem nxtR_congr {d : Fin NC} {k1 k2 : Nat} (h : nxt σ d k1 = nxt σ d k2) :
    nxtR σ d k1 = nxtR σ d k2 := by
  unfold nxtR; rw [h]

/-- After `m` full invocations of `P` steps and `q` more, the periodic walk is at the
one-invocation walk's `q`-th channel, with `m` periods `Wf` of visits added. -/
def Ag (P : Nat) (Wf : Fin NC → Nat) (m q : Nat) : Prop :=
  (walk σ q).cur = some (walkR σ (m * P + q)).cur ∧
    ∀ c, (walkR σ (m * P + q)).W c = m * Wf c + (walk σ q).W c

variable {σ}
variable {P : Nat} {Wf : Fin NC → Nat}
  (hper : ∀ c, sp c = true → ∀ m k, nxt σ c (m * Wf c + k) = nxt σ c k)

include hper in
theorem ag_cur {m q : Nat} (hA : Ag σ P Wf m q) :
    (walkR σ (m * P + q + 1)).cur = nxtR σ (walkR σ (m * P + q)).cur
      ((walk σ q).W (walkR σ (m * P + q)).cur) := by
  rw [cur_succR, hA.2]
  exact nxtR_congr σ (hper _ (by have := cur_sp σ q _ hA.1; exact this) m _)

theorem ag_W {m q : Nat} (hA : Ag σ P Wf m q) (c : Fin NC) :
    (walkR σ (m * P + q + 1)).W c = m * Wf c + (walk σ (q + 1)).W c := by
  rw [W_succR, hA.2, W_succ]
  unfold visB
  rw [hA.1]
  have : ((walkR σ (m * P + q)).cur == c) = (some (walkR σ (m * P + q)).cur == some c) := by
    simp
  rw [this]; omega

include hper in
theorem stepA {m q : Nat} (hA : Ag σ P Wf m q) (hd : (walk σ q).cur ≠ some eEnd)
    (hq1 : (walk σ (q + 1)).cur ≠ some eEnd) : Ag σ P Wf m (q + 1) := by
  have hdE : (walkR σ (m * P + q)).cur ≠ eEnd := by
    intro e; have h1 := hA.1; rw [e] at h1; exact hd h1
  have hsd := cur_sp σ q _ hA.1
  obtain ⟨e, he⟩ := nxt_some_of_live σ hsd hdE ((walk σ q).W (walkR σ (m * P + q)).cur)
  have hw1 : (walk σ (q + 1)).cur = some e := by rw [cur_succ, hA.1]; simpa using he
  have hee : e ≠ eEnd := by intro x; rw [x] at hw1; exact hq1 hw1
  refine ⟨?_, ?_⟩
  · rw [show m * P + (q + 1) = m * P + q + 1 by omega, ag_cur hper hA, nxtR_eq σ he hee, hw1]
  · intro c
    rw [show m * P + (q + 1) = m * P + q + 1 by omega]
    exact ag_W hA c

include hper in
theorem stepB {m q : Nat} (hA : Ag σ P Wf m q) (hd : (walk σ q).cur ≠ some eEnd)
    (hq1 : (walk σ (q + 1)).cur = some eEnd) (hP : q + 1 = P) (hWf : Wf = (walk σ P).W) :
    Ag σ P Wf (m + 1) 0 := by
  have hdE : (walkR σ (m * P + q)).cur ≠ eEnd := by
    intro e; have h1 := hA.1; rw [e] at h1; exact hd h1
  have hn : nxt σ (walkR σ (m * P + q)).cur ((walk σ q).W (walkR σ (m * P + q)).cur) =
      some eEnd := by
    have := hq1; rw [cur_succ, hA.1] at this; simpa using this
  have hidx : (m + 1) * P + 0 = m * P + q + 1 := by rw [← hP]; rw [Nat.succ_mul]; omega
  refine ⟨?_, ?_⟩
  · rw [hidx, ag_cur hper hA]
    unfold nxtR; rw [hn]; simp; rfl
  · intro c
    rw [hidx, ag_W hA c, hP, ← hWf]
    show m * Wf c + Wf c = (m + 1) * Wf c + 0
    rw [Nat.succ_mul]; rfl

end ag

section walkper
variable {a b : Nat} {y : TS} {ls : List Nat} (hy : Good a b y) (hex : texec (x0 a b) ls = some y)

theorem exists_min (f : Nat → Prop) (h : ∃ n, f n) : ∃ n, f n ∧ ∀ m, m < n → ¬ f m := by
  obtain ⟨n, hn⟩ := h
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases hm : ∃ m, m < n ∧ f m
    · obtain ⟨m, hmn, hfm⟩ := hm
      exact ih m hmn hfm
    · exact ⟨n, hn, fun m hmn hfm => hm ⟨m, hmn, hfm⟩⟩

include hy hex in
/-- **The periodic H_WALK for gcd_hw**, from 8s's H_WALK and the periodicity of the token
run's stream solution. -/
theorem walk_okR : WalkOKR (σY a b y) (omOf a b y) := by
  have hWO := walk_ok hy hex
  by_cases hend : ∃ P, (walk (σY a b y) P).cur = some eEnd
  · obtain ⟨P, hP, hmin⟩ := exists_min _ hend
    have hP0 : 0 < P := by
      rcases Nat.eq_zero_or_pos P with h | h
      · subst h; simp [walk] at hP; exact absurd hP (Ne.symm eEnd_ne_start)
      · exact h
    have hWf := end_counts hy hex hP
    -- periodicity of the successor with period Wf
    have hper : ∀ c, sp c = true → ∀ m k,
        nxt (σY a b y) c (m * (walk (σY a b y) P).W c + k) = nxt (σY a b y) c k := by
      intro c hc m k
      by_cases hce : c = eEnd
      · subst hce; rw [nxt_eEnd_none, nxt_eEnd_none]
      · rw [hWf c hc hce]; exact nxt_period hy hex hc m k
    have hall : ∀ m q, q < P → Ag (σY a b y) P (walk (σY a b y) P).W m q := by
      intro m
      induction m with
      | zero =>
        intro q
        induction q with
        | zero => intro _; exact ⟨by simp [walkR, walk], fun c => by simp [walkR, walk]⟩
        | succ q ih =>
          intro hq
          exact stepA hper (ih (by omega)) (hmin q (by omega)) (hmin (q + 1) hq)
      | succ m ihm =>
        intro q
        induction q with
        | zero =>
          intro _
          have hA := ihm (P - 1) (by omega)
          have e1 : P - 1 + 1 = P := by omega
          exact stepB hper hA (hmin (P - 1) (by omega)) (by rw [e1]; exact hP) e1 rfl
        | succ q ih =>
          intro hq
          exact stepA hper (ih (by omega)) (hmin q (by omega)) (hmin (q + 1) hq)
    intro n x u z w ho
    have hn : n = (n / P) * P + n % P := by rw [Nat.mul_comm]; exact (Nat.div_add_mod n P).symm
    have hA := hall (n / P) (n % P) (Nat.mod_lt _ hP0)
    obtain ⟨hc, hW⟩ := hA
    have hWz := hW z
    rw [← hn] at hc hWz
    have hze := (am_ne ho).2.2
    have hsz : sp z = true := by
      have := spok (consOf (walkR (σY a b y) n).cur); rw [ho] at this
      simp only [SpOK, Bool.and_eq_true] at this; exact this.1.2
    rw [hWz, hWf z hsz hze, om_period hy hex ho]
    exact hWO (n % P) _ x u z w hc ho
  · have hnot : ∀ q, (walk (σY a b y) q).cur ≠ some eEnd := fun q h => hend ⟨q, h⟩
    have hper : ∀ c, sp c = true → ∀ m k,
        nxt (σY a b y) c (m * (fun _ => 0) c + k) = nxt (σY a b y) c k := by
      intro c _ m k; simp
    have hall : ∀ q, Ag (σY a b y) 1 (fun _ => 0) 0 q := by
      intro q
      induction q with
      | zero => exact ⟨by simp [walkR, walk], fun c => by simp [walkR, walk]⟩
      | succ q ih => exact stepA hper ih (hnot q) (hnot (q + 1))
    intro n x u z w ho
    obtain ⟨hc, hW⟩ := hall n
    simp only [Nat.zero_mul, Nat.zero_add] at hc hW
    rw [hW z]
    exact hWO n _ x u z w hc ho

end walkper

/-- **Circuit safety for repeated invocations** (gcd_hw): for `a, b < 2^31`, under H_CELLS,
H_BUNDLE and H_START_GATE (`start`'s `(k+1)`-th offer only after `z251`'s `k`-th offer), every
value the circuit latches on `out0`, in every invocation, is `gcd a b`. -/
theorem gcd_hw_circuit_safe_all (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) (ch : Fin NC → Chan)
    (H_CELLS : ∀ o : Fin NO, Cell ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_GATE : H_START_GATE ch) :
    (∀ k e, TokAt (ch out0) k e → (ch out0).dat e = Nat.gcd a b) ∧
    (∀ t, closedVals (ch out0) t = List.replicate (cnt (fallB (ch out0).ack) t) (Nat.gcd a b)) := by
  obtain ⟨y, ls, hy, hex⟩ := good_run ha hb
  exact gcd_hw_circuit_safeR a b ch H_CELLS H_BUNDLE H_GATE ⟨y, hy, walk_okR hy hex⟩

end Formal.Net.CapNet.Gcd
