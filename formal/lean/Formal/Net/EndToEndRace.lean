import Formal.Timing.Checker

/-!
# Probe C-8e, part 1: two-path races on 10a's verified checker

A **path** is a list of arc delay intervals `(lo, hi)` (ps), in routing order:
for example `[wire, SDELAY LUT, wire, C-element LUT pin]`. A fixed-delay run
gives every arc of the path one delay inside its interval (`inPath`).

`fan2 E L` is the 10a `Netlist` with a launch node `0` and two chains hanging
off it: the **early** path `E` (nodes `1 .. |E|`) and the **late** path `L`
(nodes `|E|+1 .. |E|+|L|`). `race2 E L s` runs 10a's `check` on it: the late
end must settle `s` ticks before the early end can first move.

`race2_sound`: if `race2 E L s` holds then for every per-arc delay choice
inside the intervals, `sum(late delays) + s ≤ sum(early delays)`.
The proof does not re-derive interval arithmetic: it builds the step-launch
`FixedRun` of `fan2 E L` with exactly those delays (node `v` steps at the sum
of the delays on its path) and applies 10a's `check_sound` to it. So every
timing obligation used in `EndToEnd.lean` is discharged by the verified
checker itself, and the checker sees a real netlist, not a number.

Constant terms (a setup/hold margin, a one-tick gate step) enter as dummy
arcs `(c, c)`.
-/

namespace Formal.Net.EndToEnd
open Formal.Net Formal.Timing

abbrev Path := List (Nat × Nat)

/-- The run's per-arc delays `ds` realize path `p`: same length, each delay in
its arc's interval (H_FIXED_DELAY: one delay per arc for the whole run). -/
def inPath : List Nat → Path → Prop
  | [], [] => True
  | d :: ds, (lo, hi) :: p => lo ≤ d ∧ d ≤ hi ∧ inPath ds p
  | _, _ => False

theorem inPath_length : ∀ {ds : List Nat} {p : Path}, inPath ds p → ds.length = p.length
  | [], [], _ => rfl
  | _ :: ds, (_, _) :: p, h => by simp only [List.length_cons]; rw [inPath_length h.2.2]
  | [], _ :: _, h => by simp [inPath] at h
  | _ :: _, [], h => by simp [inPath] at h

theorem inPath_get : ∀ {ds : List Nat} {p : Path}, inPath ds p → ∀ k, k < p.length →
    (p.getD k (0, 0)).1 ≤ ds.getD k 0 ∧ ds.getD k 0 ≤ (p.getD k (0, 0)).2
  | [], [], _, k, hk => by simp at hk
  | d :: ds, (lo, hi) :: p, h, k, hk => by
    cases k with
    | zero => simp; exact ⟨h.1, h.2.1⟩
    | succ k => simp at hk ⊢; exact inPath_get h.2.2 k (by omega)
  | [], _ :: _, h, _, _ => by simp [inPath] at h
  | _ :: _, [], h, _, _ => by simp [inPath] at h

theorem inPath_append : ∀ {ds ds' : List Nat} {p p' : Path},
    inPath ds p → inPath ds' p' → inPath (ds ++ ds') (p ++ p')
  | [], _, [], _, _, h' => h'
  | d :: ds, _, (lo, hi) :: p, _, h, h' => ⟨h.1, h.2.1, inPath_append h.2.2 h'⟩
  | [], _, _ :: _, _, h, _ => by simp [inPath] at h
  | _ :: _, _, [], _, h, _ => by simp [inPath] at h

theorem inPath_const (c : Nat) : inPath [c] [(c, c)] := ⟨Nat.le_refl _, Nat.le_refl _, trivial⟩

/-! ## The race netlist -/

def ivl (p : Path) (i : Nat) : Nat × Nat := p.getD i (0, 0)

def earlyArcs (E : Path) : List Arc :=
  (List.range E.length).map fun k => ⟨k, k + 1, (ivl E k).1, (ivl E k).2⟩

def lateArcs (E L : Path) : List Arc :=
  (List.range L.length).map fun i =>
    ⟨if i = 0 then 0 else E.length + i, E.length + i + 1, (ivl L i).1, (ivl L i).2⟩

def fan2 (E L : Path) : Netlist where
  arcs := earlyArcs E ++ lateArcs E L

/-- End node of the late chain (`0` = the launch itself when `L = []`). -/
def endL (E L : Path) : Nat := if L.length = 0 then 0 else E.length + L.length

/-- The race check: 10a's `check`, request = early end, data = late end. -/
def race2 (E L : Path) (s : Nat) : Bool := check (fan2 E L) E.length [endL E L] s

/-- The arc at index `k` of `fan2 E L`. -/
def arcAt (E L : Path) (k : Nat) : Option Arc :=
  if k < E.length then some ⟨k, k + 1, (ivl E k).1, (ivl E k).2⟩
  else if k < E.length + L.length then
    some ⟨if k - E.length = 0 then 0 else k, k + 1, (ivl L (k - E.length)).1, (ivl L (k - E.length)).2⟩
  else none

theorem fan2_arc (E L : Path) (k : Nat) : (fan2 E L).arcs[k]? = arcAt E L k := by
  simp only [fan2, arcAt]
  have hlE : (earlyArcs E).length = E.length := by simp [earlyArcs]
  by_cases h1 : k < E.length
  · rw [List.getElem?_append_left (by omega)]
    simp [earlyArcs, h1]
  · rw [List.getElem?_append_right (by omega), hlE]
    simp only [h1, if_false, lateArcs, List.getElem?_map]
    by_cases h2 : k < E.length + L.length
    · have h3 : k - E.length < L.length := by omega
      rw [List.getElem?_range h3, if_pos h2, Option.map_some]
      congr 1
      simp only [Arc.mk.injEq]
      refine ⟨?_, by omega, ?_⟩
      · split <;> omega
      · simp
    · have h3 : ¬ k - E.length < L.length := by omega
      rw [List.getElem?_eq_none (by simp; omega), if_neg h2]; rfl

/-! ## The step-launch fixed-delay run of `fan2` -/

def pre (ds : List Nat) (i : Nat) : Nat := (ds.take i).sum

theorem pre_zero (ds : List Nat) : pre ds 0 = 0 := by simp [pre]

theorem pre_succ : ∀ (ds : List Nat) (i : Nat), i < ds.length → pre ds (i + 1) = pre ds i + ds.getD i 0
  | [], i, h => by simp at h
  | d :: ds, 0, _ => by simp [pre]
  | d :: ds, i + 1, h => by
    have := pre_succ ds i (by simp at h; omega)
    simp only [pre, List.take_succ_cons, List.sum_cons, List.getD_cons_succ] at this ⊢
    omega

theorem pre_full (ds : List Nat) : pre ds ds.length = ds.sum := by simp [pre]

/-- Delays of the run: arc `k` of the early chain gets `dsE[k]`, of the late chain `dsL[k-|E|]`. -/
def fanD (E : Path) (dsE dsL : List Nat) (k : Nat) : Nat :=
  if k < E.length then dsE.getD k 0 else dsL.getD (k - E.length) 0

def fanSig (E L : Path) (dsE dsL : List Nat) (v : Nat) : Trace := fun t =>
  if v ≤ E.length then decide (pre dsE v < t)
  else if v ≤ E.length + L.length then decide (pre dsL (v - E.length) < t)
  else false

def fanG (E L : Path) (v : Nat) (x : Nat → Bool) : Bool :=
  if 1 ≤ v ∧ v ≤ E.length + L.length then x (v - 1) else false

theorem shift_eq (d : Nat) (s : Trace) (t : Nat) : shift d s t = s (t - d) := by
  simp only [shift]; split
  · rw [show t - d = 0 by omega]
  · rfl

theorem fan2_wf {E L : Path} {dsE dsL : List Nat} (hE : inPath dsE E) (hL : inPath dsL L) :
    (fan2 E L).WF := by
  intro a ha
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp ha
  rw [fan2_arc] at hk
  simp only [arcAt] at hk
  by_cases h1 : k < E.length
  · simp only [h1, if_true, Option.some.injEq] at hk; subst hk
    have := inPath_get hE k h1
    exact ⟨by simp, Nat.le_trans this.1 this.2⟩
  · by_cases h2 : k < E.length + L.length
    · simp only [h1, h2, if_true, if_false, Option.some.injEq] at hk; subst hk
      have := inPath_get hL (k - E.length) (by omega)
      refine ⟨?_, Nat.le_trans this.1 this.2⟩
      simp only; split <;> omega
    · simp [h1, h2] at hk

def fanRun (E L : Path) (dsE dsL : List Nat) (hE : inPath dsE E) (hL : inPath dsL L) :
    FixedRun (fan2 E L) (fanSig E L dsE dsL) where
  d := fanD E dsE dsL
  g := fanG E L
  launch := by
    intro t ht
    apply Classical.byContradiction; intro h0; apply ht
    simp only [fanSig, Nat.zero_le, if_true, pre_zero]
    rw [decide_eq_decide]; omega
  range := by
    intro k a hk
    rw [fan2_arc] at hk
    simp only [arcAt] at hk
    by_cases h1 : k < E.length
    · simp only [h1, if_true, Option.some.injEq] at hk; subst hk
      have := inPath_get hE k h1
      simp only [fanD, h1, if_true, ivl]; exact this
    · by_cases h2 : k < E.length + L.length
      · simp only [h1, h2, if_true, if_false, Option.some.injEq] at hk; subst hk
        have := inPath_get hL (k - E.length) (by omega)
        simp only [fanD, h1, if_false, ivl]; exact this
      · simp [h1, h2] at hk
  local_ := by
    intro v x y hxy
    simp only [fanG]
    split
    · rename_i hv
      by_cases h1 : v - 1 < E.length
      · exact hxy (v - 1) ⟨v - 1, v - 1 + 1, (ivl E (v - 1)).1, (ivl E (v - 1)).2⟩
          (by rw [fan2_arc]; simp [arcAt, h1]) (by show v - 1 + 1 = v; omega)
      · exact hxy (v - 1) ⟨if v - 1 - E.length = 0 then 0 else v - 1, v - 1 + 1,
            (ivl L (v - 1 - E.length)).1, (ivl L (v - 1 - E.length)).2⟩
          (by rw [fan2_arc]; simp only [arcAt, h1, if_false,
                show v - 1 < E.length + L.length by omega, if_true])
          (by show v - 1 + 1 = v; omega)
    · rfl
  node := by
    intro v hv t
    have lE := inPath_length hE
    have lL := inPath_length hL
    simp only [fanG, fixedPin]
    by_cases hr : 1 ≤ v ∧ v ≤ E.length + L.length
    · simp only [hr, and_self, if_true]
      rw [fan2_arc]; simp only [arcAt]
      by_cases h1 : v - 1 < E.length
      · simp only [h1, if_true, shift_eq]
        have hv1 : v ≤ E.length := by omega
        have hp := pre_succ dsE (v - 1) (by omega)
        rw [show v - 1 + 1 = v by omega] at hp
        simp only [fanSig, hv1, if_true, show v - 1 ≤ E.length by omega, fanD, h1]
        rw [decide_eq_decide, hp]; omega
      · have h2 : v - 1 < E.length + L.length := by omega
        simp only [h1, if_false, h2, if_true, shift_eq]
        have hp := pre_succ dsL (v - 1 - E.length) (by omega)
        rw [show v - 1 - E.length + 1 = v - E.length by omega] at hp
        have hv1 : ¬ v ≤ E.length := by omega
        simp only [fanSig, hv1, if_false, hr.2, if_true, fanD, h1]
        by_cases h0 : v - 1 - E.length = 0
        · simp only [h0, if_true, Nat.zero_le, pre_zero]
          rw [h0, pre_zero] at hp
          rw [decide_eq_decide, hp]; omega
        · simp only [h0, if_false, show ¬ v - 1 ≤ E.length by omega,
            show v - 1 ≤ E.length + L.length by omega, if_true]
          rw [decide_eq_decide, hp]; omega
    · simp only [hr, if_false]
      simp only [fanSig]
      have : ¬ v ≤ E.length := by omega
      have : ¬ v ≤ E.length + L.length := by omega
      simp [*]

theorem step_changes (P t : Nat) : changes (fun u => decide (P < u)) t ↔ t = P := by
  simp only [changes, ne_eq, decide_eq_decide]; omega

/-- **Race soundness.** If the verified checker accepts the race, then for
every fixed-delay realization of the two paths, the late path's total delay
plus the margin is at most the early path's total delay. -/
theorem race2_sound {E L : Path} {s : Nat} (hc : race2 E L s = true)
    {dsE dsL : List Nat} (hE : inPath dsE E) (hL : inPath dsL L) :
    dsL.sum + s ≤ dsE.sum := by
  have lE := inPath_length hE
  have lL := inPath_length hL
  have r := (fanRun E L dsE dsL hE hL).toRun
  have key := check_sound (fan2_wf hE hL) hc r (endL E L) (List.mem_singleton_self _)
    dsL.sum dsE.sum
  apply key
  · simp only [endL]
    by_cases h0 : L.length = 0
    · simp only [h0, if_true]
      have : dsL = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this
      have e0 : fanSig E L dsE [] 0 = fun u => decide (0 < u) := by
        funext u; simp [fanSig, pre_zero]
      rw [e0]; exact (step_changes 0 0).mpr rfl
    · simp only [h0, if_false]
      have e1 : fanSig E L dsE dsL (E.length + L.length) = fun u => decide (pre dsL L.length < u) := by
        funext u; simp only [fanSig, show ¬ E.length + L.length ≤ E.length by omega, if_false,
          Nat.le_refl, if_true, Nat.add_sub_cancel_left]
      rw [e1, ← lL, pre_full]; exact (step_changes _ _).mpr rfl
  · have e1 : fanSig E L dsE dsL E.length = fun u => decide (pre dsE E.length < u) := by
      funext u; simp [fanSig]
    rw [e1, ← lE, pre_full]; exact (step_changes _ _).mpr rfl

end Formal.Net.EndToEnd
