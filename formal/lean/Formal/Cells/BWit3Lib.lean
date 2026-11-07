import Formal.Cells.BWit2Lib
import Formal.Cells.FiniteNetComb

/-!
# Probe Bwit3 (shard B): a checker for `FCombSpec` cells on event lists

`combB F pls Ln`: a LUT `F` (with the reset `rst2`) over pins with event lists `pls`, node
`cL Ln` = the excitation one tick later (unit LUT delay). `combB_spec`: a passing check gives
`FiniteNetComb.FCombSpec` with edges `Ln[j] - 1` for the excitation, so its `H_EXC_CLEAN` holds
because the excitation IS the node one tick early, a clean step signal (`gph_shift`). On a run
this is how the arbiter's race hypothesis is discharged: by checking the actual traces.
**Assumed:** nothing (definitions and lemmas). Core Lean only.
-/

namespace Formal.Cells.BWit3
open Formal.Cells
open Formal.Cells.FiniteNet
open Formal.Cells.FiniteNetComb (FCombSpec exc)
open Formal.Cells.WinFifo (Win)
open Formal.Cells.WinFifoCausal (NoRevertI nt)
open Formal.Cells.PipeTimed (Vph)
open Formal.Cells.LutFbBridge2Env (ε)
open Formal.Cells.FiniteRunsWit (sortedB bv_tail all_t cL rst2 NB bnd)
open Formal.Net.CapNet.Wit (bv)
open Formal.Cells.AssumeGuaranteeEnds (GPin gE)
open Formal.Cells.AssumeGuaranteeEndsNet (GD)
open Formal.Cells.FiniteNetWit2 (step_win nt11 eps_list getD_ge1)

/-- A clean step signal read one tick later, with every edge at least 1. -/
theorem gph_shift {y : Nat → Bool} {c : Nat → Nat} {L : Nat → Prop} (h : GPh y c L)
    (h1 : ∀ j, L j → 1 ≤ c j) : GPh (fun t => y (t + 1)) (fun j => c j - 1) L := by
  intro T
  have g := h (T + 1)
  refine ⟨fun s hs h0 => g.pre (s + 1) (by omega) ?_, fun j s hs hj a b => ?_⟩
  · rcases h0 with h0 | h0
    · exact Or.inl h0
    · by_cases hL : L 0
      · have := h1 0 hL; exact Or.inr (by omega)
      · exact Or.inl hL
  · have := h1 j hj
    exact g.ph j (s + 1) (by omega) hj (by omega) (fun hj1 => by have := b hj1; have := h1 _ hj1; omega)

/-- The excitation of `F` over event-list pins. -/
def excL (F : List Bool → Bool → Bool) (pls : List (List Nat)) (t : Nat) : Bool :=
  F (pls.map fun l => bv l t) (rst2 t)

/-- **The checker**: node `cL Ln` is the excitation one tick later; lists bounded and sorted. -/
def combB (F : List Bool → Bool → Bool) (pls : List (List Nat)) (Ln : List Nat) : Bool :=
  bnd Ln && sortedB Ln && pls.all bnd && !bv Ln 1 && decide (1 ≤ Ln.getD 0 1) &&
  (List.range (NB + 1)).all (fun t => bv Ln (t + 2) == excL F pls t)

theorem excL_tail {F : List Bool → Bool → Bool} {pls : List (List Nat)} (hb : pls.all bnd = true)
    (t : Nat) (ht : NB ≤ t) : excL F pls t = excL F pls NB := by
  unfold excL
  have hNB : NB = 768 := rfl
  have e : (pls.map fun l => bv l t) = (pls.map fun l => bv l NB) :=
    List.map_congr_left fun l hl => bv_tail (List.all_eq_true.1 hb l hl) t ht
  rw [e, show rst2 t = rst2 NB by unfold rst2; simp; omega]

theorem combB_spec {F : List Bool → Bool → Bool} {pls : List (List Nat)} {Ln : List Nat}
    (hchk : combB F pls Ln = true) {ι : Type} {D : GD ι} {L : ι → Nat → Prop} {c : ι}
    {ps : List (GPin ι)} (hO : D.O c = cL Ln) (hlo : D.lo c = 1) (hhi : D.hi c = 1)
    (hrst : D.rst = rst2) (hpins : D.pins c = ps) (hP : ps.map (·.P) = pls.map bv)
    (hτL : ∀ j, j < Ln.length → D.τ c j = Ln.getD j 1) (hLc : L c = fun j => j < Ln.length) :
    FCombSpec D L c F ps (fun j => Ln.getD j 1 - 1) (fun j => j < Ln.length) := by
  simp only [combB, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, Bool.not_eq_true',
    decide_eq_true_eq] at hchk
  obtain ⟨⟨⟨⟨⟨hbn, hsn⟩, hbp⟩, hpw⟩, h0⟩, hlut⟩ := hchk
  have hNB : NB = 768 := rfl
  have hex : ∀ t, exc F ps D.rst t = excL F pls t := by
    intro t
    unfold exc excL
    rw [hrst]
    congr 1
    have := congrArg (List.map fun f : Nat → Bool => f t) hP
    rw [List.map_map, List.map_map] at this
    exact this
  have lutA : ∀ t, (bv Ln (t + 2) == excL F pls t) = true := all_t NB
    (List.all_eq_true.2 fun t ht => by simpa using hlut t ht) (fun t ht => by
      rw [bv_tail hbn (t + 2) (by omega), excL_tail (List.all_eq_true.2 hbp) t ht,
        bv_tail hbn (NB + 2) (by omega)])
  have hstep : ∀ t, D.O c (t + 1) = exc F ps D.rst t := by
    intro t; have := lutA t; simp only [beq_iff_eq] at this
    rw [hO, hex]; exact this
  have sw := step_win hstep
  have hg1 : ∀ j, 1 ≤ Ln.getD j 1 := getD_ge1 hsn h0
  refine { H_PINS := hpins, H_LUT_WIN := ?_, H_NO_REVERT := ?_, H_PWR := ?_,
           H_EXC_CLEAN := fun T _ => ?_, H_TIMES := fun j hj => ?_, H_CNT := fun j => ?_,
           H_FLOOR := fun j _ => ?_ }
  · rw [hlo, hhi]; exact sw.1
  · rw [hlo, hhi]; exact sw.2
  · intro t ht; rw [hhi] at ht
    have : t = 0 := by omega
    subst this; rw [hO]; exact hpw
  · have g := gph_shift (FiniteNetWit.cL_gph hsn) (fun j _ => hg1 j) T
    have e : exc F ps D.rst = fun t => cL Ln (t + 1) := funext fun t => by
      rw [← hstep, hO]
    rw [e]; exact g
  · rw [hLc] at hj
    have hl := eps_list hsn j hj
    unfold ε at hl
    rw [nt11] at hl
    dsimp only at hl
    have hv : bv Ln (Ln.getD j 1 + 1) = Vph j := by
      by_cases h : bv Ln (Ln.getD j 1 + 1) = Vph j
      · exact h
      · rw [if_neg h] at hl; omega
    have := hg1 j
    rw [hτL j hj, hO, hlo, hhi, nt11]
    have e2 : Ln.getD j 1 - 1 + 1 = Ln.getD j 1 := by omega
    rw [e2]
    rw [if_pos (show cL Ln (Ln.getD j 1) = Vph j from hv)]
  · rw [hLc]
  · rw [hhi, hlo]; omega

end Formal.Cells.BWit3
