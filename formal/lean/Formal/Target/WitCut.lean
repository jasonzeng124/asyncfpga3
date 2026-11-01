import Formal.Target.Witness

/-!
# Formal.Target.WitCut — eventually periodic witnesses with a cut per node (faster checks)

Shard A, 2026-11-01. `Witness.ext` repeats every node from one global cut `b`. A node that is quiet early, or
that becomes periodic early (the free-running ring), then still has to be checked over the whole window
`[dmax, b)`, and the gate check is quadratic in the flips it sees. Here every node `n` has its own cut
`cut n`: its description holds below `cut n`, and from there it repeats its last period. A gate is checked on
`[dmax, B)` where `B` is the largest cut among its nodes. `gateOK_cut` is `Witness.gateOK_slow` for this
extension. Same proof shape; nothing in `Witness.lean` changes.
-/

namespace Formal.Target.Wit
open Formal.Target

/-- The behaviour of a description table, node `n` extended periodically from its own cut. -/
def extC (D : Nat → SD) (cut : Nat → Nat) (P : Nat) : Beh := fun n t => (D n).val (wrap (cut n) P t)

theorem extC_lt (D : Nat → SD) {cut : Nat → Nat} {P n s : Nat} (h : s < cut n) : extC D cut P n s = (D n).val s := by
  simp [extC, wrap_lt h]

theorem extC_per (D : Nat → SD) {cut : Nat → Nat} {P Dm n s : Nat} (hP : 0 < P) (hPb : P + Dm ≤ cut n)
    (hper : PerOn (D n) P (cut n - Dm) (cut n)) (hs : cut n - Dm ≤ s) :
    extC D cut P n s = extC D cut P n (s - P) := by
  unfold extC
  by_cases h : s < cut n
  · rw [wrap_lt h, wrap_lt (by omega)]; exact hper s hs h
  · rw [wrap_per hP (by omega) (by omega)]

/-- **The gate equation for the per-node extension**, from a segment check on `[lo, B)` with `B` at least every
cut of the gate's nodes, and each node periodic on the last `Dm` before its own cut. -/
theorem eq_extC (D : Nat → SD) (cut : Nat → Nat) (g : Gate) {B P Dm lo fuel : Nat} (hP : 0 < P)
    (hlo : lo + P ≤ B) (hd : ∀ i, i < g.k → dsl g i ≤ Dm)
    (hBo : cut g.out ≤ B) (hBi : ∀ i, i < g.k → cut (g.ins.getD i 0) ≤ B)
    (hPo : P + Dm ≤ cut g.out) (hPi : ∀ i, i < g.k → P + Dm ≤ cut (g.ins.getD i 0))
    (hchk : chkFrom D g (dsl g) B fuel lo = true)
    (hpi : ∀ i, i < g.k → PerOn (D (g.ins.getD i 0)) P (cut (g.ins.getD i 0) - Dm) (cut (g.ins.getD i 0)))
    (hlow : ∀ s, s < B → extC D cut P g.out s = (D g.out).val s)
    (hlowi : ∀ i, i < g.k → ∀ s, s < B → extC D cut P (g.ins.getD i 0) s = (D (g.ins.getD i 0)).val s) :
    ∀ t, lo ≤ t → extC D cut P g.out t = rhs (extC D cut P) g (dsl g) t := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro hlt
    by_cases htb : t < B
    · rw [hlow t htb, chkFrom_sound D g (dsl g) B fuel lo hchk t hlt htb]
      unfold rhs; congr 1; apply addr_congr; intro i hi
      simp only [beh]; rw [hlowi i hi _ (by omega)]
    · have e1 : extC D cut P g.out t = extC D cut P g.out (t - P) := by
        unfold extC; rw [wrap_per hP (by omega) (by omega)]
      have e2 : rhs (extC D cut P) g (dsl g) t = rhs (extC D cut P) g (dsl g) (t - P) := by
        unfold rhs; congr 1; apply addr_congr; intro i hi
        have := hd i hi
        have := hBi i hi
        rw [extC_per D hP (hPi i hi) (hpi i hi) (by omega), show t - dsl g i - P = t - P - dsl g i by omega]
      rw [e1, e2]; exact ih (t - P) (by omega) (by omega)

/-- Below `B`, the extension agrees with the description, IF the description already repeats there
(`PerOn` on `[cut n, B)` is what makes the gate check over the longer window sound). -/
theorem extC_eq_val_upto (D : Nat → SD) {cut : Nat → Nat} {P B n : Nat} (hP : 0 < P) (hPc : P ≤ cut n)
    (hper : PerOn (D n) P (cut n) B) : ∀ s, s < B → extC D cut P n s = (D n).val s := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro hsB
    by_cases h : s < cut n
    · exact extC_lt D h
    · have e : extC D cut P n s = extC D cut P n (s - P) := by
        unfold extC; rw [wrap_per hP hPc (by omega)]
      rw [e, ih (s - P) (by omega) (by omega), hper s (by omega) hsB]

/-- **`Spec.GateOK` at the slow corner for the per-node extension.** -/
theorem gateOK_cut (D : Nat → SD) (cut : Nat → Nat) (g : Gate) {B P Dm fuel : Nat} (hP : 0 < P)
    (hlo : g.dmax + P ≤ B) (hDm : g.dmax ≤ Dm) (hlen : g.arcs.length = g.k)
    (harc : ∀ e ∈ g.arcs, e.fmin ≤ e.smin ∧ e.smin ≤ e.smax)
    (hBo : cut g.out ≤ B) (hBi : ∀ i, i < g.k → cut (g.ins.getD i 0) ≤ B)
    (hPo : P + Dm ≤ cut g.out) (hPi : ∀ i, i < g.k → P + Dm ≤ cut (g.ins.getD i 0))
    (hchk : chkFrom D g (dsl g) B fuel g.dmax = true)
    (hpo2 : PerOn (D g.out) P (cut g.out) B)
    (hpi : ∀ i, i < g.k → PerOn (D (g.ins.getD i 0)) P (cut (g.ins.getD i 0) - Dm) (cut (g.ins.getD i 0)))
    (hpi2 : ∀ i, i < g.k → PerOn (D (g.ins.getD i 0)) P (cut (g.ins.getD i 0)) B) :
    GateOK pSlow 1 g (extC D cut P) := by
  have hdi : ∀ i, i < g.k → dsl g i ≤ g.dmax := fun i hi => le_dmax g i (by omega)
  refine ⟨fun i t => t - dsl g i, fun i _ a c hac => by simp only; omega, fun t ht => ?_⟩
  rw [start_slow] at ht
  refine ⟨fun i hi => ⟨Nat.sub_le _ _, ?_⟩, ?_⟩
  · rw [show t - (t - dsl g i) = dsl g i by have := hdi i hi; omega]
    obtain ⟨h1, h2⟩ := harc _ (getD_mem g.arcs default (by rw [hlen]; exact hi))
    exact adm_slow _ _ h1 h2 (Nat.le_refl _)
  · exact eq_extC D cut g hP hlo (fun i hi => Nat.le_trans (hdi i hi) hDm) hBo hBi hPo hPi hchk hpi
      (extC_eq_val_upto D hP (by omega) hpo2)
      (fun i hi => extC_eq_val_upto D hP (by have := hPi i hi; omega) (hpi2 i hi)) t ht

/-! ## Data: description, cut and horizon per node -/

/-- A node's witness data: its description, its cut (periodic from there) and its horizon (the description is
only used below it). -/
structure NodeW where
  d : SD
  cut : Nat
  hor : Nat
  deriving Inhabited

inductive BTW where
  | leaf (v : NodeW)
  | node (mid : Nat) (l r : BTW)
  deriving Inhabited

def BTW.find : BTW → Nat → NodeW
  | .leaf v, _ => v
  | .node m l r, n => if n < m then l.find n else r.find n

theorem perOn_mono {d : SD} {P lo hi lo' hi' : Nat} (h : PerOn d P lo hi) (h1 : lo ≤ lo') (h2 : hi' ≤ hi) :
    PerOn d P lo' hi' := fun s hs1 hs2 => h s (by omega) (by omega)

/-- A gate's window end: the largest cut among its nodes, and at least `dmax + P`. -/
def _root_.Formal.Target.Gate.winEnd (cut : Nat → Nat) (P : Nat) (g : Gate) : Nat :=
  ((List.range g.k).map fun i => cut (g.ins.getD i 0)).foldr max (max (cut g.out) (g.dmax + P))

theorem le_winEnd_out (cut : Nat → Nat) (P : Nat) (g : Gate) : cut g.out ≤ g.winEnd cut P ∧ g.dmax + P ≤ g.winEnd cut P := by
  unfold Gate.winEnd
  generalize (List.range g.k).map (fun i => cut (g.ins.getD i 0)) = l
  induction l with
  | nil => simp only [List.foldr_nil]; omega
  | cons x l ih => simp only [List.foldr_cons]; omega

theorem le_winEnd_in (cut : Nat → Nat) (P : Nat) (g : Gate) (i : Nat) (hi : i < g.k) :
    cut (g.ins.getD i 0) ≤ g.winEnd cut P := by
  unfold Gate.winEnd
  have hm : cut (g.ins.getD i 0) ∈ (List.range g.k).map (fun i => cut (g.ins.getD i 0)) :=
    List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩
  generalize (List.range g.k).map (fun i => cut (g.ins.getD i 0)) = l at hm
  induction l with
  | nil => cases hm
  | cons x l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 hm with h | h
    · omega
    · have := ih h; omega

/-- A node whose flips all end a period before its cut reads its description in the extension. -/
theorem extC_eq_val (D : Nat → SD) {cut : Nat → Nat} {P n : Nat} (hP : 0 < P) (hPc : P ≤ cut n)
    (hq : ∀ τ ∈ (D n).ts, τ + P < cut n) : extC D cut P n = (D n).val :=
  by
  funext t
  unfold extC
  by_cases h : t < cut n
  · rw [wrap_lt h]
  · have hw1 : cut n - P ≤ wrap (cut n) P t := by unfold wrap; rw [if_neg h]; omega
    have hw2 : wrap (cut n) P t ≤ t := by
      unfold wrap; rw [if_neg h]
      have := Nat.mod_lt (t - (cut n - P)) hP
      have := Nat.mod_le (t - (cut n - P)) P
      omega
    exact ((D n).val_const hw2 (fun x hx h1 => by have := hq x hx; omega)).symm

end Formal.Target.Wit
