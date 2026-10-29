import Formal.Net.CapstoneLiveWitCells
import Formal.Net.CapstoneLiveWitStepA
import Formal.Net.CapstoneLiveWitStepB
import Formal.Net.CapstoneLiveWitStepC
import Formal.Net.CapstoneLiveWitStepD
import Formal.Net.CapstoneLiveWitStepE
import Formal.Net.CapstoneLiveWitStepF
import Formal.Net.CapstoneLiveWitNd
import Formal.Net.CapstoneLiveNdWalk

/-!
# Probe C-8z2 (5): `gcd_hw_live_final` is not vacuous

`gcd_hw_live_joint_witness`: one explicit circuit run of the concrete 465-channel gcd_hw network
(a = 12, b = 18, `H = 1`) satisfies ALL SEVEN hypotheses of 8z's `gcd_hw_live_final` together:
H_CELLS (with explicit internal traces), H_BUNDLE, H_START_ONCE, H_BOUNDED_DELAY' 1 (every
gate except `start`'s LUT, including the free-running a/b sources), H_START_ENV 1,
H_ARB_UNCONTESTED_BOUNDED 1 and H_NO_DEADLOCK'; and in it out0's first token closes, carrying 6.

`gcd_hw_live_witness_consistent` applies `gcd_hw_live_final` to the run: the theorem's
conclusion (some out0 close within its bound, carrying gcd 12 18 = 6) is then a consequence,
and agrees with the run.

What this does NOT show: H_NO_DEADLOCK' for any other run (it is checked here for this one
run only, from its certificate); anything about other inputs, schedules or real delays. It
is a satisfiability (non-vacuity) result for the hypothesis set.
-/

namespace Formal.Net.CapNet.LiveWit
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapNet.Live Formal.Net.CapNet.Live.Nd Formal.Net.CapNet.Wit
open Formal.Net.CapSafe (Good)

set_option maxRecDepth 100000

theorem l_step : ∀ p : Fin NO, p ≠ prodOf start → opStep cdW p = true := by
  intro p hp
  have := p.isLt
  by_cases h1 : p.val < 60
  · exact stepR_get lstepA p (by omega) h1 hp
  by_cases h2 : p.val < 120
  · exact stepR_get lstepB p (by omega) h2 hp
  by_cases h3 : p.val < 180
  · exact stepR_get lstepC p (by omega) h3 hp
  by_cases h4 : p.val < 240
  · exact stepR_get lstepD p (by omega) h4 hp
  by_cases h5 : p.val < 300
  · exact stepR_get lstepE p (by omega) h5 hp
  · exact stepR_get lstepF p (by omega) (by simpa using this) hp

theorem start_op : opAt (prodOf start) = .src 2 2 0 := by decide +kernel

/-- H_BOUNDED_DELAY' 1 holds for the run. -/
theorem l_bnd : ∀ p, p ≠ prodOf start → ∀ g ∈ gatesK p (opAt p), BndG 1 (gsAt chL (itrW cdW)) g :=
  bnd_all l_step

/-- H_ARB_UNCONTESTED_BOUNDED 1 holds for the run. -/
theorem l_arb : ∀ p x u z w, opAt p = .amerge x u z w →
    ArbUnc 1 (chL x) (chL u) (chL z) (itrW cdW p 0) (itrW cdW p 1) :=
  arb_all l_step (fun x u z w h => by rw [start_op] at h; cases h)

/-- H_NO_DEADLOCK' holds for the run. -/
theorem l_nd : ∀ t, cnt (fallB (chL out0).ack) t = 0 →
    ¬ (Quiet2 (gsAt chL (itrW cdW) t) ∧
       (cnt (riseB (chL start).req) t = 0 → (chL start).ack t = false → (chL start).req t = true)) :=
  nd_of certL lnd closeL l_out0.1.1 lcert_len

/-- **Joint non-vacuity of `gcd_hw_live_final`.** One circuit run meets all seven hypotheses
(with `a = 12 < 2^31`, `b = 18 < 2^31`, `H = 1`), and out0's first token closes carrying 6. -/
theorem gcd_hw_live_joint_witness :
    ∃ (ch : Fin NC → Chan) (itr : Itr),
      (∀ p : Fin NO, CellI ch (srcV 12 18) itr p (opAt p)) ∧
      (∀ c, Held (ch c)) ∧
      (∀ t, cnt (riseB (ch start).req) t ≤ 1) ∧
      (∀ p, p ≠ prodOf start → ∀ g ∈ gatesK p (opAt p), BndG 1 (gsAt ch itr) g) ∧
      StartEnv 1 (ch start) ∧
      (∀ p x u z w, opAt p = .amerge x u z w → ArbUnc 1 (ch x) (ch u) (ch z) (itr p 0) (itr p 1)) ∧
      (∀ t, cnt (fallB (ch out0).ack) t = 0 →
        ¬ (Quiet2 (gsAt ch itr t) ∧
           (cnt (riseB (ch start).req) t = 0 → (ch start).ack t = false → (ch start).req t = true))) ∧
      (∃ e, TokAt (ch out0) 0 e ∧ (ch out0).dat e = 6) :=
  ⟨chL, itrW cdW, l_cells, l_held, l_start_once, l_bnd, l_start_env, l_arb, l_nd, ⟨closeL, l_out0⟩⟩

/-- Sanity check: `gcd_hw_live_final` applied to the witness run. Its conclusion holds, and the
first out0 token it promises is the one the run closes at `closeL`, carrying `gcd 12 18 = 6`. -/
theorem gcd_hw_live_witness_consistent :
    (∃ y, Good 12 18 y ∧ ∃ e, e < (1168 * (8 * Lrun y + 23) + 1) * (1 + 1) ∧ TokAt (chL out0) 0 e ∧
      (chL out0).dat e = Nat.gcd 12 18) ∧
    TokAt (chL out0) 0 closeL ∧ (chL out0).dat closeL = Nat.gcd 12 18 := by
  refine ⟨gcd_hw_live_final 12 18 1 (by decide) (by decide) chL (itrW cdW) l_cells l_held l_start_once
    l_bnd l_start_env l_arb l_nd, l_out0.1, ?_⟩
  rw [l_out0.2]; decide

end Formal.Net.CapNet.LiveWit
