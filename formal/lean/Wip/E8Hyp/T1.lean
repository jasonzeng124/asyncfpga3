import Formal.Core.XAudit.Events2PinDesign

namespace Formal.Core.XAudit.Events8Bridge

open Formal.Core
open Formal.Core.XAudit
open Formal.Core.TraceDiscrete (Sig Warp Mono)
open Formal.Core.XAudit.Events2Pin (SatPin PinRel PinTab shift_warp)

theorem warp_lo_le_hi {lo hi : Nat} {f : Nat → Nat} (w : Warp lo hi f) : lo ≤ hi := by
  have a := w.le_late (lo + hi); have b := w.early_le (lo + hi); omega

/-! ## Time origin -/

/-- **The time origin of `SatPin`.** At time 0 every gate output is its INIT at the
inputs' time-0 values: time 0 is a combinational fixpoint of the whole netlist. -/
theorem satPin_origin {d : Design} {pl : PinTab} {x : Fin d.n → Sig} (hs : SatPin d pl x) :
    ∀ g ∈ d.gates, x (d.wire g.out) 0 =
      g.init.testBit (addr (fun p : Fin g.k => x (d.wire (g.ins.getD p.val 0)) 0)) := by
  intro g hg
  obtain ⟨f, hw, he⟩ := hs g hg
  rw [he 0]
  congr 2
  funext p
  have h := (hw p.val p.isLt).le_late 0
  have : f p.val 0 = 0 := by omega
  rw [this]

/-- A physical per-pin relation valid from `t0` on (monotone reads, band `pl g i`). -/
def PhysPin (d : Design) (pl : PinTab) (g : GSpec) (y : Fin d.n → Sig) (t0 : Nat) : Prop :=
  ∃ f : Nat → Nat → Nat, (∀ i, i < g.k → Mono (f i) ∧
      ∀ t, t0 ≤ t → f i t + (pl g i).1 ≤ t ∧ t ≤ f i t + (pl g i).2) ∧
    ∀ t, t0 ≤ t → y (d.wire g.out) t =
      g.init.testBit (addr (fun p : Fin g.k => y (d.wire (g.ins.getD p.val 0)) (f p.val t)))

/-- **Shift bridge.** A physical trace that obeys the per-pin relation from `t0` on and
is QUIET (every wire constant) on `[t0 - H, t0]`, `H` at least every pin band's upper
end, is, shifted to start at `t0`, a `SatPin` behaviour. -/
theorem satPin_shift {d : Design} {pl : PinTab} {y : Fin d.n → Sig} {t0 H : Nat}
    (hp : ∀ g ∈ d.gates, PhysPin d pl g y t0)
    (hH : ∀ g ∈ d.gates, ∀ i, i < g.k → (pl g i).2 ≤ H)
    (hq : ∀ w u, t0 - H ≤ u → u ≤ t0 → y w u = y w t0) :
    SatPin d pl (fun w t => y w (t0 + t)) := by
  intro g hg
  obtain ⟨f, hw, he⟩ := hp g hg
  refine ⟨fun i t => f i (t0 + t) - t0, fun i hi => ⟨?_, ?_, ?_⟩, fun t => ?_⟩
  · intro a c hac; have := (hw i hi).1 (t0 + a) (t0 + c) (by omega); dsimp only; omega
  · intro t; have := ((hw i hi).2 (t0 + t) (by omega)).1; dsimp only; omega
  · intro t; have := ((hw i hi).2 (t0 + t) (by omega)).2; dsimp only; omega
  · show y (d.wire g.out) (t0 + t) = _
    rw [he (t0 + t) (by omega)]
    congr 2
    funext p
    have h1 := ((hw p.val p.isLt).2 (t0 + t) (by omega)).2
    have h2 := hH g hg p.val p.isLt
    by_cases hc : t0 ≤ f p.val (t0 + t)
    · show _ = y _ (t0 + (f p.val (t0 + t) - t0))
      congr 1; omega
    · show _ = y _ (t0 + (f p.val (t0 + t) - t0))
      have e : t0 + (f p.val (t0 + t) - t0) = t0 := by omega
      rw [e]; exact hq _ _ (by omega) (by omega)

end Formal.Core.XAudit.Events8Bridge
