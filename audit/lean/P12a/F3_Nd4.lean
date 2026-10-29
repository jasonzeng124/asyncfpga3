import Formal.Net.CapstoneLiveNd4Serial
import Formal.Net.CapstoneLiveNd4Mux
import Formal.Timing.ChainSettleChain

/-!
# Audit P12a / F3: 8z4 `serial` -- the "rank is necessary" example is a real necessity example

`arb_not_reach` shows 00 -> 11 is not interleaving-reachable for the contested arbiter. For this
to show that the RANK premise (and not `hex`) is what fails, the other premise `hex` must hold.
Here: with `Dis := (· ≠ ·)` (each grant disables the other) `hex` holds for the tick 00 -> 11,
and no rank exists.
-/

namespace P12a.Nd4
open Formal.Net.CapNet.Live.Nd4

def s0 : Fin 2 → Bool := fun _ => false
def s1 : Fin 2 → Bool := fun _ => true

theorem other_ne : ∀ i : Fin 2, (1 - i : Fin 2) ≠ i := by decide

theorem arb_hex : ∀ (L : List (Fin 2)) (i : Fin 2), s0 i ≠ s1 i → i ∈ L →
    (∀ j, j ∉ L → s0 j ≠ s1 j → ¬ (j ≠ i)) → arbEx i (s1 i) (mixL s0 s1 L) := by
  intro L i _ _ hcl
  have hj : (1 - i : Fin 2) ∈ L := by
    apply Classical.byContradiction
    intro h
    exact hcl (1 - i) h (by simp [s0, s1]) (other_ne i)
  left
  refine ⟨rfl, ?_⟩
  simp [mixL, hj, s0]

theorem arb_norank : ¬ ∃ r : Fin 2 → Nat, ∀ i j : Fin 2, s0 i ≠ s1 i → s0 j ≠ s1 j → j ≠ i →
    r i < r j := by
  rintro ⟨r, h⟩
  have a := h 0 1 (by simp [s0, s1]) (by simp [s0, s1]) (by decide)
  have b := h 1 0 (by simp [s0, s1]) (by simp [s0, s1]) (by decide)
  omega

/-- So `serial` with `hex` alone (no rank) would prove a false statement. -/
theorem serial_needs_rank : ¬ (∀ (Dis : Fin 2 → Fin 2 → Prop),
    (∀ (L : List (Fin 2)) (i : Fin 2), s0 i ≠ s1 i → i ∈ L →
      (∀ j, j ∉ L → s0 j ≠ s1 j → ¬ Dis j i) → arbEx i (s1 i) (mixL s0 s1 L)) →
    Reach arbEx s0 s1) := by
  intro h
  exact arb_not_reach (h (fun j i => j ≠ i) arb_hex)

end P12a.Nd4

#print axioms P12a.Nd4.serial_needs_rank
#print axioms Formal.Net.CapNet.Live.Nd4.serial
#print axioms Formal.Net.CapNet.Live.Nd4.trace_nodead
#print axioms Formal.Net.CapNet.Live.Nd4.arb_not_reach
#print axioms Formal.Net.CapNet.Live.Nd4.mux_out_not_mux
#print axioms Formal.Net.CapNet.Live.Nd4.mux_out_chk
#print axioms Formal.Timing.ChainSettle.settled_iff
#print axioms Formal.Timing.ChainSettle.runt_of_gap
#print axioms Formal.Timing.ChainSettle.low_iff
#print axioms Formal.Timing.ChainSettle.chain2_settled_iff
#print axioms Formal.Timing.ChainSettle.runt_example
#print axioms Formal.Timing.ChainSettle.or_runt_of_gap
