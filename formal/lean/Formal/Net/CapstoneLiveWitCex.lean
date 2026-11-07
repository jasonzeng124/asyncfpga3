import Formal.Net.CapstoneLiveWitCexCells
import Formal.Net.CapstoneLiveWitCexStepA
import Formal.Net.CapstoneLiveWitCexStepB
import Formal.Net.CapstoneLiveNd2

/-!
# Probe C-8z2 (9): 8z's H_NO_DEADLOCK' is not a network obligation: a counterexample run

`nd_counterexample`: one explicit circuit run of the concrete gcd_hw network (a = 12, b = 18,
`H = 1`) meets the SIX other hypotheses of `gcd_hw_live_final` (H_CELLS, H_BUNDLE,
H_START_ONCE, H_BOUNDED_DELAY' 1, H_START_ENV 1, H_ARB_UNCONTESTED_BOUNDED 1), out0's
acknowledge never falls, and H_NO_DEADLOCK' is false on it. The run is the unit-delay run in
which `start`'s LUT, after its one offer, never releases its request (8z's hypotheses put no
delay bound on that LUT once it has offered). So H_NO_DEADLOCK' cannot be derived from the
other hypotheses: it hides the environment assumption "start's token is released".

H_NO_DEADLOCK' is refuted through `gcd_hw_live_final` itself (if it held, out0 would close).
The run also violates the repair's H_START_REL 1 (`x_not_rel`), as it must.
-/

namespace Formal.Net.CapNet.LiveWit
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapNet.Live Formal.Net.CapNet.Live.Nd Formal.Net.CapNet.Wit

set_option maxRecDepth 100000

theorem x_step : ∀ p : Fin NO, p ≠ prodOf start → opStep cdX p = true := by
  intro p hp
  have := p.isLt
  by_cases h1 : p.val < 180
  · exact stepR_get xstepA p (by omega) h1 hp
  · exact stepR_get xstepB p (by omega) p.isLt hp

theorem start_op' : opAt (prodOf start) = .src 2 2 0 := rfl

theorem x_bnd : ∀ p, p ≠ prodOf start → ∀ g ∈ gatesK p (opAt p), BndG 1 (gsAt chX (itrW cdX)) g :=
  bnd_all x_step

theorem x_arb : ∀ p x u z w, opAt p = .amerge x u z w →
    ArbUnc 1 (chX x) (chX u) (chX z) (itrW cdX p 0) (itrW cdX p 1) :=
  arb_all x_step (fun x u z w h => by rw [start_op'] at h; cases h)

/-- The repair's H_START_REL 1 fails on this run: the request is never released. -/
theorem x_not_rel : ¬ Live.Nd2.StartRel 1 (chX start) := by
  intro h
  have hr : ∀ u, 1 ≤ u → (chX start).req u = true := fun u hu => by
    show bv (cdX start).rq u = true; rw [xstart_rq]; exact bv_one (by omega)
  have ha : ∀ u, 99 ≤ u → (chX start).ack u = true := fun u hu => by
    show bv (cdX start).ak u = true; rw [xstart_ak]; exact bv_one (by omega)
  obtain ⟨u, h1, -, hu⟩ := h 99 (fun u h1 _ => ⟨hr u (by omega), ha u h1⟩)
  rw [hr u (by omega)] at hu; cases hu

/-- **H_NO_DEADLOCK' is not implied by the other hypotheses of `gcd_hw_live_final`.** -/
theorem nd_counterexample :
    ∃ (ch : Fin NC → Chan) (itr : Itr),
      (∀ p : Fin NO, CellI ch (srcV 12 18) itr p (opAt p)) ∧
      (∀ c, Held (ch c)) ∧
      (∀ t, cnt (riseB (ch start).req) t ≤ 1) ∧
      (∀ p, p ≠ prodOf start → ∀ g ∈ gatesK p (opAt p), BndG 1 (gsAt ch itr) g) ∧
      StartEnv 1 (ch start) ∧
      (∀ p x u z w, opAt p = .amerge x u z w → ArbUnc 1 (ch x) (ch u) (ch z) (itr p 0) (itr p 1)) ∧
      (∀ t, cnt (fallB (ch out0).ack) t = 0) ∧
      ¬ (∀ t, cnt (fallB (ch out0).ack) t = 0 →
        ¬ (Quiet2 (gsAt ch itr t) ∧
           (cnt (riseB (ch start).req) t = 0 → (ch start).ack t = false → (ch start).req t = true))) := by
  refine ⟨chX, itrW cdX, x_cells, x_held, x_start_once, x_bnd, x_start_env, x_arb, x_never, ?_⟩
  intro hnd
  obtain ⟨_, _, e, _, hT, _⟩ := gcd_hw_live_final 12 18 1 (by decide) (by decide) chX (itrW cdX) x_cells
    x_held x_start_once x_bnd x_start_env x_arb hnd
  have h1 := x_never (e + 1)
  simp [cnt, hT.1] at h1

end Formal.Net.CapNet.LiveWit
