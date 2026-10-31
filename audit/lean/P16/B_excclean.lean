import Formal.Cells.FiniteNetComb
/-! Auditor P16: what H_EXC_CLEAN constrains.
(1) Any excitation that is a step signal for SOME edge list satisfies the H_EXC_CLEAN field
    form, whatever the pins do (the premise is not used).
(2) A 1-tick runt (pulse at t = 5) IS a "clean step signal" in the sense of GPhT, with two
    edges [5, 6]: "no runt" is not what GPhT/H_EXC_CLEAN excludes; a runt is two extra edges,
    which H_CNT then forces into the cell's edge set L c. -/
open Formal.Cells Formal.Cells.FiniteNet Formal.Cells.FiniteNetComb
open Formal.Cells.AssumeGuaranteeEnds (GPin gE)
open Formal.Cells.AssumeGuaranteeEndsNet (GD)
open Formal.Cells.PipeTimed (Vph)

theorem exc_clean_of_gph {ι : Type} {D : GD ι} {L : ι → Nat → Prop} {F : List Bool → Bool → Bool}
    {ps : List (GPin ι)} {e : Nat → Nat} {Le : Nat → Prop}
    (h : GPh (exc F ps D.rst) e Le) :
    ∀ T, (∀ p ∈ ps, GPhT p.P (gE D.τ p) (L p.drv) T) → GPhT (exc F ps D.rst) e Le T :=
  fun T _ => h T

def runt (t : Nat) : Bool := t == 5
def runtE (j : Nat) : Nat := if j = 0 then 5 else 6

theorem runt_gph : GPh runt runtE (fun j => j < 2) := by
  intro T
  refine ⟨fun s _ h => ?_, fun j s _ hj h1 h2 => ?_⟩
  · rcases h with h | h
    · exact absurd (by omega) h
    · simp [runt, runtE] at h ⊢; omega
  · have hV0 : Vph 0 = true := rfl
    have hV1 : Vph 1 = false := rfl
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · have := h2 (by omega); simp [runtE] at h1 this
      rw [hV0]; simp [runt]; omega
    · simp [runtE] at h1; rw [hV1]; simp [runt]; omega

#print axioms exc_clean_of_gph
#print axioms runt_gph
