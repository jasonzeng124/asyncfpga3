import Formal.Core.XSimChanReal
import Formal.Core.XAudit.SoundCells

/-!
# Formal.Core.XAudit.SoundPhys — xaudit's timed verdicts hold for ℝ-time transport/inertial gates

Probe XSound2 (shard A). See `formal/notes/A-xsound2.md`.

The verdicts `xaudit` prints (rows of `Fast.auditF`, read with `valF`, checked
with `noXF`, `SoundCells.allEqF`, `rowsFixedF`) are theorems about every
behaviour in CONTINUOUS time (`ℝ`, any unit; one step = one cell of width `q`,
for xaudit `q = unit_ps`) in which

* every parsed gate is its zero-delay INIT function of the pin values (the
  LUT samples all pins at one instant) followed by a `XSimChanReal.PhysChan q
  lo hi` channel: transport `DelayPure.Chan L H` or bounded inertial
  `DelayInertial.BoundedInertial ρ L H` with `lo q ≤ L`, `H ≤ hi q` and, for
  inertial, `ρ ≤ (hi + 1 - lo) q` (`SatPhys`);
* the inputs are covered cell by cell by the stimulus (`InputsCoveredT` with
  `c = ⌊·/q⌋₊`, or any `CellMap q c`);
* the power-up state is arbitrary (the executable starts from all `X`).

Results: `valF_sound_phys`, `noXF_sound_phys` (an X-free stretch of steps means
the printed binary value at every instant of those cells, so the same waveform
in every behaviour: no X, no glitch, any delays in the bands),
`noXF_deterministic_phys`, `constF_sound_phys`, `settledF_phys` (fixed point:
every binary value of row `T` holds at every instant from `T q` on).

Assumed (named): `SatPhys` (the gate/channel model and the bands — a band is a
measurement hypothesis), `InputsCoveredT`. `SoundSteps` says when the parser's
rounding meets the band side conditions (not when `L < unit`: those arcs are
listed as "raised" and are NOT covered). NOT covered: inertial channels whose
rejection window exceeds the abstract window (`XSimChanReal.inertial_wide_not_chanCells`,
`XSimChanReal.Cex.cex_real` is a concrete failure); involution channels; analog
effects (runts at intermediate voltage, metastability).
-/

namespace Formal.Core.XAudit.SoundPhys

open Formal.Core K3
open Formal.Core.XSim
open Formal.Core.XSimChan
open Formal.Core.XSimChanReal
open Formal.Core.XAudit
open Formal.Core.XAudit.Fast
open Formal.Core.XAudit.SoundCells

/-- **The physical gate hypothesis.** Every parsed gate: zero-delay INIT
function, then a transport or (bounded) inertial channel within its step band
at cell width `q`. -/
def SatPhys (d : Design) (q : ℝ) (x : Fin d.n → ℝ → Bool) : Prop :=
  ∀ g ∈ d.gates, PhysChan q g.lo g.hi (excT (g.toLGate d) x) (x (d.wire g.out))

theorem satCells_of_phys {d : Design} {q : ℝ} (hq : 0 < q) {c : ℝ → ℕ} (hc : CellMap q c)
    {x : Fin d.n → ℝ → Bool} (h : SatPhys d q x) : SatCells d c x :=
  fun g hg => physChan_chanCells hc hq (h g hg)

/-- Every printed value covers the concrete value at every instant of its cell. -/
theorem valF_sound_phys (d : Design) (hwf : d.WF) (u : Fin d.n → ℕ → K3) (T : ℕ)
    {q : ℝ} (hq : 0 < q) (c : ℝ → ℕ) (hc : CellMap q c) (x : Fin d.n → ℝ → Bool)
    (hsat : SatPhys d q x) (hin : InputsCoveredT d u c x) (t : ℝ) (ht : c t ≤ T) (w : Fin d.n) :
    valF (auditF d u T) (c t) w.val ⊑ ofBool (x w t) :=
  valF_sound_cells d hwf u T c x (satCells_of_phys hq hc hsat) hin t ht w

/-- **"No X at `w` on steps `[t1, t2]`", in continuous time.** -/
theorem noXF_sound_phys (d : Design) (hwf : d.WF) (u : Fin d.n → ℕ → K3) (T : ℕ)
    (w : Fin d.n) (t1 t2 : ℕ) (ht2 : t2 ≤ T) (h : noXF (auditF d u T) w.val t1 t2 = true)
    {q : ℝ} (hq : 0 < q) (c : ℝ → ℕ) (hc : CellMap q c) (x : Fin d.n → ℝ → Bool)
    (hsat : SatPhys d q x) (hin : InputsCoveredT d u c x) :
    ∀ t, t1 ≤ c t → c t ≤ t2 → x w t = pick (valF (auditF d u T) (c t) w.val) :=
  noXF_sound_cells d hwf u T w t1 t2 ht2 h c x (satCells_of_phys hq hc hsat) hin

theorem noXF_deterministic_phys (d : Design) (hwf : d.WF) (u : Fin d.n → ℕ → K3) (T : ℕ)
    (w : Fin d.n) (t1 t2 : ℕ) (ht2 : t2 ≤ T) (h : noXF (auditF d u T) w.val t1 t2 = true)
    {q : ℝ} (hq : 0 < q) (c : ℝ → ℕ) (hc : CellMap q c) (x y : Fin d.n → ℝ → Bool)
    (hx : SatPhys d q x) (hy : SatPhys d q y)
    (hix : InputsCoveredT d u c x) (hiy : InputsCoveredT d u c y) :
    ∀ t, t1 ≤ c t → c t ≤ t2 → x w t = y w t :=
  noXF_deterministic_cells d hwf u T w t1 t2 ht2 h c x y (satCells_of_phys hq hc hx)
    (satCells_of_phys hq hc hy) hix hiy

/-- **Binary and constant** at every instant of the cells `t1..t2`. -/
theorem constF_sound_phys (d : Design) (hwf : d.WF) (u : Fin d.n → ℕ → K3) (T : ℕ)
    (w : Fin d.n) (t1 t2 : ℕ) (ht2 : t2 ≤ T) (v : Bool)
    (h : allEqF (auditF d u T) w.val t1 t2 v = true)
    {q : ℝ} (hq : 0 < q) (c : ℝ → ℕ) (hc : CellMap q c) (x : Fin d.n → ℝ → Bool)
    (hsat : SatPhys d q x) (hin : InputsCoveredT d u c x) :
    ∀ t, t1 ≤ c t → c t ≤ t2 → x w t = v :=
  constF_sound_cells d hwf u T w t1 t2 ht2 v h c x (satCells_of_phys hq hc hsat) hin

/-- **Fixed point**, continuous time: with `c = ⌊·/q⌋₊`, every binary value of
row `T` holds at every instant `t ≥ T q`. -/
theorem settledF_phys (d : Design) (hwf : d.WF) (u : Fin d.n → ℕ → K3) (T : ℕ) (hT : 1 ≤ T)
    (hu : ∀ w, Undriven (build d) w → ∀ t, T ≤ t → u w t = u w T)
    (hfix : rowsFixedF (auditF d u T) T d.maxHi = true)
    {q : ℝ} (hq : 0 < q) (x : Fin d.n → ℝ → Bool) (hsat : SatPhys d q x)
    (hin : InputsCoveredT d u (fun t => ⌊t / q⌋₊) x) (w : Fin d.n) (v : Bool)
    (hv : valF (auditF d u T) T w.val = ofBool v) : ∀ t : ℝ, (T : ℝ) * q ≤ t → x w t = v := by
  intro t ht
  refine settledF_cells d hwf u T hT hu hfix _ x
    (satCells_of_phys hq (cellMap_floor hq) hsat) hin w v hv t ?_
  have : (T : ℝ) ≤ t / q := by rw [le_div_iff₀ hq]; exact ht
  exact Nat.le_floor this

end Formal.Core.XAudit.SoundPhys
