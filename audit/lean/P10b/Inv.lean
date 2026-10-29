import Formal.Core.Delay.InvolutionTrace
import Formal.Core.Delay.InvolutionLoopSignal
import Formal.Core.Delay.InvolutionLoopRate
import Formal.Core.XSimChanReal
import Formal.Core.XSimChanTern
import Formal.Core.XAudit.SoundPhys
import Formal.Core.XAudit.SoundChain

/-! Auditor P10b: commits aa90885, 45b9acb, 44d7383 (involution), 9e1499e (XSound2). -/

namespace Audit.P10b.Inv
open Formal.Core.DelayInvolution Formal.Core.DelayInvolutionTransfer

#print axioms Formal.Core.DelayInvolution.InvolutionPair.channel_eq
#print axioms Formal.Core.DelayInvolution.InvolutionPair.cancel_no_chain
#print axioms Formal.Core.DelayInvolution.InvolutionPair.channel_sorted
#print axioms Formal.Core.DelayInvolution.InvolutionPair.rat_memory_channel
#print axioms Formal.Core.InvolutionLoop.crit_unique
#print axioms Formal.Core.InvolutionLoop.latch
#print axioms Formal.Core.InvolutionLoop.lost
#print axioms Formal.Core.InvolutionLoop.resolution_unbounded
#print axioms Formal.Core.InvolutionLoop.laps_unbounded_above
#print axioms Formal.Core.InvolutionLoop.stat_exists
#print axioms Formal.Core.InvolutionLoop.Signal.arb_trichotomy
#print axioms Formal.Core.InvolutionLoop.Signal.arb_threshold
#print axioms Formal.Core.XSimChanReal.boundedInertial_chanCells
#print axioms Formal.Core.XSimChanReal.inertial_wide_not_chanCells
#print axioms Formal.Core.XSimChanReal.sound_real
#print axioms Formal.Core.XSimChanReal.Cex.cex_real

/-! ## Own nontrivial instance of the trace channel, through the ALGORITHM:
`[0, 1/2, 5, 6]` on ratPair (δ(T) = 2 - 1/(T+2)): tent = 2, 1/2 (cancels with 2),
5 + δ(9/2) = 89/13, 6 + δ(6 - 89/13) = 6 + 2 - 13/15 = 107/15 (survives). -/
theorem my_channel4 : ratPair.channel [0, 1 / 2, 5, 6] = [89 / 13, 107 / 15] := by
  simp only [InvolutionPair.channel, List.foldl, InvolutionPair.step,
    InvolutionPair.rat_delayAt, ratDelay]
  norm_num

/-! ## Own instance of the loop threshold for ratPair (symmetric, δ∞ = 2):
the stationary train has h = l = w with 2 - 1/(2 - w) = 2w, i.e. 2w² - 6w + 3 = 0,
w = (3 - √3)/2 ≈ 0.634, so s* = 2 - w ≈ 1.366; prove 1.35 < s* < 1.4. -/
open Formal.Core.InvolutionLoop in
theorem rat_crit_bounds {h l : ℝ} (S : Stat ratPair h l) :
    1.35 < crit ratPair l ∧ crit ratPair l < 1.4 := by
  have Y : Sym ratPair := ⟨fun _ => rfl, rfl⟩
  have hl : h = l := Sym.duty ratPair Y S
  subst hl
  have e := S.up_eq
  have h0 := S.h_pos
  have h2 : h < 2 := S.h_lt
  show (1.35 : ℝ) < ratPair.infUp - h ∧ ratPair.infUp - h < 1.4
  change ratDelay (-h) = h + h at e
  unfold ratDelay at e
  have hq : (0 : ℝ) < -h + 2 := by linarith
  have key : 2 * h ^ 2 - 6 * h + 3 = 0 := by
    field_simp at e; nlinarith [e]
  show (1.35 : ℝ) < 2 - h ∧ 2 - h < 1.4
  constructor <;> nlinarith [key]

open Formal.Core.InvolutionLoop Formal.Core.InvolutionLoop.Signal in
/-- The trichotomy instantiated at a genuine involution channel (non-vacuous). -/
example : ∃ h l : ℝ, Stat ratPair h l ∧ crit ratPair l < ratPair.infUp ∧
    ∀ s, 0 < s → s < ratPair.infUp →
      ∀ r1 r2 x qp, Formal.Cells.ArbInvolution.ALoop ratPair s r1 r2 x qp →
        (Latched qp ↔ crit ratPair l < s) := by
  obtain ⟨h, l, S, _, h2, H⟩ := arb_threshold ratPair
  exact ⟨h, l, S, h2, fun s a b r1 r2 x qp L => ((H s a b).2 r1 r2 x qp L).1⟩

/-! ## XSound2: the side condition at a concrete point (q = 1, lo = 1, hi = 2):
ρ = 2 = (hi + 1 - lo) q is covered; ρ = 5/2 is not. -/
open Formal.Core.XSimChanReal in
example {x y : ℝ → Bool} (h : Formal.Core.DelayInertial.BoundedInertial 2 1 2 x y) :
    Formal.Core.XSimChan.ChanCells (fun t => ⌊t / 1⌋₊) 1 2 x y :=
  boundedInertial_chanCells (cellMap_floor (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) h

open Formal.Core.XSimChanReal in
example : ∃ x y : ℝ → Bool, Formal.Core.DelayInertial.BoundedInertial (5 / 2) ((1 : ℕ) * 1) ((2 : ℕ) * 1) x y ∧
    ¬ Formal.Core.XSimChan.ChanCells (fun t => ⌊t / 1⌋₊) 1 2 x y :=
  inertial_wide_not_chanCells (by norm_num) (by norm_num) (by norm_num)

end Audit.P10b.Inv
