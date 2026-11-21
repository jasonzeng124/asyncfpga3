import Formal.Net.CViewPS.RIslBnd00
import Formal.Net.CViewPS.RIslBnd01
import Formal.Net.CViewPS.RIslBnd02
import Formal.Net.CViewPS.RIslBnd03
import Formal.Net.CViewPS.RIslBnd04
import Formal.Net.CViewPS.RIslBnd05
import Formal.Net.CViewPS.RIslBnd06
import Formal.Net.CViewPS.RIslBnd07
import Formal.Net.CViewPS.RIslBnd08
import Formal.Net.CViewPS.RIslBnd09
import Formal.Net.CViewPS.RIslBnd10
import Formal.Net.CViewPS.RIslBnd11
import Formal.Net.CViewPS.RIslBnd12
import Formal.Net.CViewPS.RIslBnd13
import Formal.Net.CViewPS.RIslBnd14
import Formal.Net.CViewPS.RIslBnd15
import Formal.Net.CViewPS.RIslBnd16
import Formal.Net.CViewPS.RIslBnd17
import Formal.Net.CViewPS.RIslBnd18
import Formal.Net.CViewPS.RIslBnd19
import Formal.Net.CViewPS.RIslBnd20
import Formal.Net.CViewPS.RIslBnd21
import Formal.Net.CViewPS.RIslBnd22
import Formal.Net.CViewPS.RIslBnd23
import Formal.Net.CViewPS.RIslBnd24
import Formal.Net.CViewPS.RIslBnd25
import Formal.Net.CViewPS.RIslBnd26
import Formal.Net.CViewPS.RIslBnd27
import Formal.Net.CViewPS.RIslBnd28
import Formal.Net.CViewPS.RIslBnd29
import Formal.Net.CViewPS.RIslBnd30
import Formal.Net.CViewPS.RIslBnd31
import Formal.Net.CViewPS.RIslBnd32
import Formal.Net.CViewPS.RIslBnd33
import Formal.Net.CViewPS.RIslBnd34
import Formal.Net.CViewPS.RIslBnd35
import Formal.Net.CViewPS.RIslBnd36
import Formal.Net.CViewPS.RIslBnd37
import Formal.Net.CViewPS.RIslBnd38
import Formal.Net.CViewPS.RIslBnd39
import Formal.Net.CViewPS.RIslBnd40
import Formal.Net.CViewPS.RIslBnd41
import Formal.Net.CViewPS.RIslBnd42
import Formal.Net.CViewPS.RIslBnd43
import Formal.Net.CViewPS.RIslBnd44
import Formal.Net.CViewPS.RIslBnd45
import Formal.Net.CViewPS.RIslBnd46
import Formal.Net.CViewPS.RIslBnd47
import Formal.Net.CViewPS.RIslBnd48
import Formal.Net.CViewPS.RIslBnd49
import Formal.Net.CViewPS.RIslBnd50
import Formal.Net.CViewPS.RIslBnd51
import Formal.Net.CViewPS.RIslBnd52
import Formal.Net.CViewPS.RIslBnd53
import Formal.Net.CViewPS.RIslBnd54
import Formal.Net.CViewPS.RIslBnd55
import Formal.Net.CViewPS.RIslBnd56
import Formal.Net.CViewPS.RIslBnd57
import Formal.Net.CViewPS.RIslBnd58
import Formal.Net.CViewPS.RIslBnd59
import Formal.Net.CViewPS.RIslBnd60
import Formal.Net.CViewPS.RIslBnd61
import Formal.Net.CViewPS.RIslPS
import Formal.Net.CViewPS.Idle0All

/-!
# THE target starts quiet, for every guard and scatter (shard C)

**Problem, plainly.** `reset_quiet_PS` leaves the delay bounds `A` (gate starts) and `M` (composite pin delays)
open. **Proved** (`reset_quiet_all`): for every sane `p` (any `g > 0`, `0 ≤ κ`), in every behaviour of THE
theorem's circuit with the reset node high on `[0, R)`, every one of the 3,224 reset-island members equals its listed
value at every `t` with `C·(A2 + 15·M2) ≤ t ≤ R - 1`, where `C = ⌈(1+κ)·g⌉`, `A2 = 19,832 ps`, `M2 = 4,636 ps`
(prjxray slow-max sums, checked per member in the kernel, RIslBnd*.lean). So at g = 1, κ = 0 the island is known
from 89,372 ps until the end of reset. **Not shown:** anything after `R - 1`; nodes outside the island.
-/

namespace Formal.Net.CViewPS
open Formal.Target Formal.Target.DecodedPS Formal.Timing.SpecSettle Formal.Timing.SpecChain
  Formal.Timing.SpecChainM Formal.Timing.ChunkCM Formal.Timing.Huffman Formal.Timing.SpecLoop
  Formal.Timing.Island

theorem rIsl_bnd : rIsl.all rBndOK = true := by
  simp only [rIsl, RTree.all,
    rbb0_ok, rbb1_ok, rbb2_ok, rbb3_ok, rbb4_ok, rbb5_ok, rbb6_ok, rbb7_ok, rbb8_ok, rbb9_ok, rbb10_ok, rbb11_ok, rbb12_ok, rbb13_ok, rbb14_ok, rbb15_ok, rbb16_ok, rbb17_ok, rbb18_ok, rbb19_ok, rbb20_ok, rbb21_ok, rbb22_ok, rbb23_ok, rbb24_ok, rbb25_ok, rbb26_ok, rbb27_ok, rbb28_ok, rbb29_ok, rbb30_ok, rbb31_ok, rbb32_ok, rbb33_ok, rbb34_ok, rbb35_ok, rbb36_ok, rbb37_ok, rbb38_ok, rbb39_ok, rbb40_ok, rbb41_ok, rbb42_ok, rbb43_ok, rbb44_ok, rbb45_ok, rbb46_ok, rbb47_ok, rbb48_ok, rbb49_ok, rbb50_ok, rbb51_ok, rbb52_ok, rbb53_ok, rbb54_ok, rbb55_ok, rbb56_ok, rbb57_ok, rbb58_ok, rbb59_ok, rbb60_ok, rbb61_ok, Bool.and_self]

theorem rbnd_facts {w : Nat} (h : memR w = true) :
    cStartN (gAt cs 2500 w) (pcsPS w) ≤ A2 ∧ ∀ i, i < (gAt cs 2500 w).k → sumMaxN (arcsPS w i) ≤ M2 := by
  unfold memR at h
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨rfl, hok⟩ := RTree.find_all rIsl w e he rIsl_bnd
  simp only [rBndOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hok
  exact ⟨hok.1, fun i hi => hok.2 i hi⟩

/-- **Quiet start of THE target, every `(g, κ)`.** -/
theorem reset_quiet_all {p : DelayPar} (hp : Sane p) {x : Beh} (hb : Behaves p (circuit net boundary) x)
    (R : Nat) (hR : ∀ t, t < R → x rstPS t = true) (hR0 : 0 < R) :
    ∀ w, memR w = true → ∀ t, Cp p * A2 + 15 * (Cp p * M2) ≤ t → t ≤ R - 1 → x w t = valR w := by
  obtain ⟨c, _, _, h⟩ := reset_quiet_PS15 hp hb
  exact h R (Cp p * M2) (Cp p * A2) hR hR0
    (fun w hw => le_trans (cStart_le hp _ _) (Nat.mul_le_mul_left _ (rbnd_facts hw).1))
    (fun w hw i hi => le_trans (sumMax_le hp _) (Nat.mul_le_mul_left _ ((rbnd_facts hw).2 i hi)))

end Formal.Net.CViewPS
