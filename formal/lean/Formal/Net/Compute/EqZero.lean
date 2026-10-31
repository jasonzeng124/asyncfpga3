import Formal.Net.Compute.Word
import Formal.Net.GcdHwLib

/-!
# H_COMPUTE_FN, part 4: `e0 == 0` as an AND of zero-detecting groups

`EqZOK cells outs o groups`: output `outs = [.net o]`; each group `(g, bits)` is a net `g`
checked exhaustively to be "all of `bits` of port 0 are 0"; `o` is checked, with the group
nets as cut points, to be the AND of the group nets; the groups cover bits `0..31` and only
those. `eqz_sound`: then the unit computes `Ops.cmpi .eq 32 a 0` for every `a`.
-/

namespace Formal.Net.Compute
open Formal.Net.GcdHw

def EqZOK (cells : List Cell) (outs : List W) (o : Nat) (groups : List (Nat × List Nat)) : Prop :=
  outs = [.net o] ∧ (cells.flatMap Cell.outs).Nodup ∧
  (LocalOK (groups.map Prod.fst) (filt cells [o]).1 (.net o) (groups.map fun g => .cut g.1)
      (fun l => l.all id) ∧ (groups.map fun g => Leaf.cut g.1).Nodup ∧
    (swOf (groups.map Prod.fst) (filt cells [o]).1 (.net o)).all
      (fun l => decide (l ∈ groups.map fun g => Leaf.cut g.1)) = true) ∧
  (∀ g ∈ groups, LocalOK [] (filt cells [g.1]).1 (.net g.1) (g.2.map (Leaf.inp 0))
      (fun l => l.all (fun b => !b)) ∧ (g.2.map (Leaf.inp 0)).Nodup ∧
    (swOf [] (filt cells [g.1]).1 (.net g.1)).all
      (fun l => decide (l ∈ g.2.map (Leaf.inp 0))) = true) ∧
  (∀ i, i < 32 → groups.any (fun g => g.2.contains i) = true) ∧
  (∀ g ∈ groups, ∀ i ∈ g.2, i < 32)

instance (cells : List Cell) (outs : List W) (o : Nat) (groups : List (Nat × List Nat)) :
    Decidable (EqZOK cells outs o groups) := by
  unfold EqZOK; exact inferInstance

theorem mod_eq_zero_iff_bits (a : Nat) :
    a % 2 ^ 32 = 0 ↔ ∀ i, i < 32 → a.testBit i = false := by
  constructor
  · intro h i hi
    have := congrArg (fun x => x.testBit i) h
    simp only [Nat.testBit_mod_two_pow, Nat.zero_testBit, hi, decide_true, Bool.true_and] at this
    exact this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
    by_cases hi : i < 32
    · simp [hi, h i hi]
    · simp [hi]

/-- **A certified zero detector computes `e0 == 0`** (32 bits) for every input. -/
theorem eqz_sound {cells : List Cell} {outs : List W} {o : Nat} {groups : List (Nat × List Nat)}
    (h : EqZOK cells outs o groups) (a : Nat) :
    unitVal cells outs [a] = Ops.cmpi .eq 32 a 0 := by
  obtain ⟨ho, hnd, ⟨hok, hS, hsup⟩, hg, hcov, hrng⟩ := h
  let env := inEnv [a]
  let R := run env [] cells (fun _ => false)
  have hgv : ∀ g ∈ groups, R g.1 = (g.2.map (fun i => a.testBit i)).all (fun b => !b) := by
    intro g hgm
    obtain ⟨h1, h2, h3⟩ := hg g hgm
    rw [show R g.1 = _ from cert_val hnd h1 h2 h3 env, List.map_map]
    rfl
  have hov : R o = (groups.map (fun g => R g.1)).all id := by
    rw [show R o = _ from cert_val hnd hok hS hsup env, List.map_map]
    rfl
  have key : R o = true ↔ ∀ i, i < 32 → a.testBit i = false := by
    rw [hov]
    simp only [List.all_eq_true, List.mem_map, id]
    constructor
    · intro hall i hi
      obtain ⟨g, hgm, hgi⟩ := List.any_eq_true.mp (hcov i hi)
      have := hall (R g.1) ⟨g, hgm, rfl⟩
      rw [hgv g hgm] at this
      simp only [List.all_eq_true, List.mem_map] at this
      have := this (a.testBit i) ⟨i, by simpa using hgi, rfl⟩
      simpa using this
    · rintro hall _ ⟨g, hgm, rfl⟩
      rw [hgv g hgm]
      simp only [List.all_eq_true, List.mem_map]
      rintro _ ⟨i, hi, rfl⟩
      simp [hall i (hrng g hgm i hi)]
  have hu : unitVal cells outs [a] = if R o then 1 else 0 := by
    subst ho
    cases hr : R o <;> simp [unitVal, word, eval, wv, hr, R, env, List.getD]
  rw [hu, Ops.cmpi]
  simp only [Ops.b2n, Nat.zero_mod]
  by_cases hz : a % 2 ^ 32 = 0
  · have : R o = true := key.mpr ((mod_eq_zero_iff_bits a).mp hz)
    simp [this, hz]
  · have : R o = false := by
      cases hr : R o
      · rfl
      · exact absurd ((mod_eq_zero_iff_bits a).mpr (key.mp hr)) hz
    simp [this, hz]

end Formal.Net.Compute
