import Formal.Cells.ResetGcdWave
open Formal.Core.LutList
/-!
# Self-audit of shard B (probe Bsa), part 2: a joint witness for the gcd_hw reset/wave chain

`ResetGcd.gcd_reset_binary`, `ResetGcdWave.gcd_loop_late` and
`ResetGcdWave.gcd_wave_settled` quantify over every bounded GMW run of the
3322-node network, but no run satisfying all their hypotheses was exhibited.
Here: 7f's synchronous unit-delay simulation (`TernarySound.unitRun`, `D = W = 0`)
from ANY power-up state `c0`, with rst = 1 on `[1, F]` and 0 afterwards and
every data net 0. All hypotheses are discharged (H_STEER_HOLD from
`gcd_loop_late`, H_SETTLED from `gcd_reset_binary`), so the chain is not
vacuous, and the conclusion is concrete: at step `F + 34` every control node
equals `sigB` (the post-wave state), for every `c0`.

Observation (not a defect, but it sharpens the note): with `D = W = 0`,
`gcd_loop_late` keeps the steers at 0 exactly through `F + 34`, and the wave
settles exactly at `F + 34 · (D + W + 1) = F + 34`. So in the unit-delay run
the window on which `gcd_wave_settled` says something is a single step. With
`D + W > 0`, nothing proved keeps the steers at 0 until `F + 34(D+W+1)`; the
settled-state conclusion then holds only on runs where the loop entry is late
enough (H_STEER_HOLD), as B-reset-gcd-wave.md says.
-/
namespace Formal.Cells.SelfAuditB2
open Formal.Cells Formal.Cells.TernarySound Formal.Cells.ResetGcd Formal.Cells.ResetGcdWave

/-- rst = 1 on `[0, F]`, 0 afterwards; every other input 0. -/
def inpR (F : Nat) (k n : Nat) : Bool := (n == 0) && decide (k ≤ F)

theorem node0_input : gNet.node 0 = .input := rfl

theorem simB_input {F : Nat} {c0 : Nat → Bool} (k n : Nat) (h : gNet.node n = .input) :
    simB gNet (inpR F) c0 (k + 1) n = inpR F (k + 1) n := by
  show (match gNet.node n with
    | .input => inpR F (k + 1) n
    | .gate init pins => lutB init (pinsB (fun _ i => simB gNet (inpR F) c0 k i) pins 0)) = _
  rw [h]

theorem rst_at {F : Nat} {c0 : Nat → Bool} (k : Nat) (hk : 0 < k) :
    simB gNet (inpR F) c0 k 0 = decide (k ≤ F) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [simB_input j 0 node0_input]; simp [inpR]

theorem held {F : Nat} {c0 : Nat → Bool} :
    ∀ k, 0 < k → k ≤ F → TernaryPhases.InputsIn gNet (simB gNet (inpR F) c0) gA k := by
  intro k hk hkF n hn
  by_cases h0 : n = 0
  · subst h0; rw [rst_at k hk]; simp [gA, hkF, K3.admits]
  · simp [gA, h0, K3.admits]

/-- **Joint witness.** From any power-up state, the unit-delay run with rst
held on `[1, F]` (`F ≥ 23`) meets every hypothesis of `gcd_reset_binary`,
`gcd_loop_late` and `gcd_wave_settled`, and at step `F + 34` every control
node is at the post-wave state `sigB`. -/
theorem wave_witness (c0 : Nat → Bool) (F : Nat) (hF : 23 ≤ F) :
    ∀ n, gCtl n = true → simB gNet (inpR F) c0 (F + 34) n = sigB n := by
  let v := simB gNet (inpR F) c0
  have Rn := unitRun gNet (inpR F) c0
  have hB := unitDelay_run gNet (inpR F) c0
  have RB : ∀ n, gCtl n = true → ∀ k, 23 ≤ k → k ≤ F → v k n = gR n := fun n hc k h1 h2 =>
    gcd_reset_binary (unitRun gNet (inpR F) c0) hB F held n hc k (by simpa [maxRank] using h1) h2
  have hS : ∀ k n, k ≤ F → F ≤ k + 0 → gCtl n = true → n ≠ 0 → v k n = gR n :=
    fun k n a b hc _ => RB n hc k (by omega) a
  have LL := gcd_loop_late (unitRun gNet (inpR F) c0) hB.wire F F hS
    (fun j a b => by
      show simB gNet (inpR F) c0 j 0 = true
      rw [rst_at j (by omega)]; simp; omega)
  intro n hc
  exact gcd_wave_settled (unitRun gNet (inpR F) c0) hB F F (F + 34) (Nat.le_refl F) hS
    (fun k a b => by
      show simB gNet (inpR F) c0 k 0 = false
      rw [rst_at k (by omega)]; simp; omega)
    (fun k z hz a b => LL z hz k (by omega) b)
    (F + 34) n (by simp [maxB]) (Nat.le_refl _) hc

end Formal.Cells.SelfAuditB2
