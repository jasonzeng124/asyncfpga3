-- Bsa4 mutant M07 of Formal/Cells/Necessity5Mem.lean: one change, '↔ m0.tSU ≤ m0.dsLo := by' -> '↔ m0.tSU ≤ m0.dsLo + 1 := by'. Expected: FAIL.
import Formal.Cells.ConstraintsMore

/-!
# Necessity5Mem: the `bd_mem` port rows in the event model, exactly

Probe Bnx5 (shard B). Rows `bd_mem.setup`, `.hold`, `.rdata_before_ack`,
`.clk_high_width` were "sufficient", backed by `LibEndMemMlink.MemPort`'s
`setup_ok`, `hold_ok`, `rdata_before_ack` and `ConstraintsMore.MemPort.clk_high_ok`
(and `clk_low_ok`).

Model (unchanged): `MemPort` = the event times of one access (request,
RAM clock, ack, payload changes, next request/clock) constrained by
H_SETUP_LINE (the `usetup -> ubuf -> CLKARDCLK` line within `[dsLo, dsHi]`
rise, `[dsLoF, dsHiF]` fall), H_CO_LINE (`ram_clk -> uco -> ack` at least
`dcLo` / `dcLoF`) and H_FOUR_PHASE_ENV; the RAMB18E1 datasheet numbers
`tSU`, `tHD`, `tCO`, `tPWH`, `tPWL` are constants. The BRAM is NOT a gate
model: "the datasheet requirement holds" is the conclusion.

`Same m m0`: `m` has `m0`'s line bounds and datasheet numbers (its events are
free). For every port `m0` (so its line bounds are consistent:
`dsLo ≤ dsHi`, `dsLoF ≤ dsHiF`, from its own H_SETUP_LINE), `fast m0` is a
port with the same numbers where every line takes its minimum and the
environment answers at once (`fast_port`, `fast_same`). On it every
shipped bound is attained.

* **Proved (iffs, event model):**
  - `setup_exact`: (every such port meets `tPay + tSU ≤ tClkR`) ↔ `tSU ≤ dsLo`.
  - `hold_exact`: (… `tClkR + tHD ≤ tPayNext`) ↔ `tHD ≤ dcLo + dsLoF + dcLoF`.
  - `rdata_exact`: (… `tClkR + tCO ≤ tAckR`) ↔ `tCO ≤ dcLo`.
  - `clk_high_exact`: (… `tClkR + tPWH ≤ tClkF`) ↔ `tPWH ≤ dcLo + dsLoF`.
    The shipped condition `tPWH + dsHi ≤ dsLo + dcLo + dsLoF`
    (`clk_high_ok`, the JSON inequality) is therefore NOT necessary whenever
    the setup line has spread (`clk_high_not_necessary`: dsLo = 1, dsHi = 3,
    dcLo = dsLoF = 1, tPWH = 2: shipped fails, every port meets tPWH). The
    clock high phase is measured from the clock's own rise, so the setup
    line's rise spread does not enter (`clk_high_tight`: width ≥ dcLo + dsLoF).
  - `clk_low_exact`: (… `tClkF + tPWL ≤ tClkR2`) ↔ `tPWL ≤ dcLoF + dsLo`.
* **NOT covered:** the consumer's `rdata` vs `ack` route skew
  (H_RDATA_ROUTE: the JSON's rdata row adds it, the Lean has `tCO ≤ dcLo`
  only); payload route skew at the RAM pins (requester's bundling, tPay is
  an environment time); the BRAM's behaviour when a datasheet number is
  violated (no gate model); multi-access interaction beyond one next access.

Core Lean only.
-/

namespace Formal.Cells.Necessity5Mem
open Formal.Cells Formal.Cells.LibEndMemMlink

/-- Same line bounds and datasheet numbers (events free). -/
def Same (m m0 : MemPort) : Prop :=
  m.dsLo = m0.dsLo ∧ m.dsHi = m0.dsHi ∧ m.dsLoF = m0.dsLoF ∧ m.dsHiF = m0.dsHiF ∧
  m.dcLo = m0.dcLo ∧ m.dcLoF = m0.dcLoF ∧ m.tSU = m0.tSU ∧ m.tHD = m0.tHD ∧ m.tCO = m0.tCO

theorem same_refl (m : MemPort) : Same m m := by
  unfold Same; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The fastest access with `m0`'s numbers: request at 0, every line at its minimum,
the environment answers at once. -/
def fast (m0 : MemPort) : MemPort where
  tReqR := 0
  tReqF := m0.dsLo + m0.dcLo
  tClkR := m0.dsLo
  tClkF := m0.dsLo + m0.dcLo + m0.dsLoF
  tAckR := m0.dsLo + m0.dcLo
  tAckF := m0.dsLo + m0.dcLo + m0.dsLoF + m0.dcLoF
  tPay := 0
  tPayNext := m0.dsLo + m0.dcLo + m0.dsLoF + m0.dcLoF
  tReqR2 := m0.dsLo + m0.dcLo + m0.dsLoF + m0.dcLoF
  tClkR2 := m0.dsLo + m0.dcLo + m0.dsLoF + m0.dcLoF + m0.dsLo
  dsLo := m0.dsLo
  dsHi := m0.dsHi
  dsLoF := m0.dsLoF
  dsHiF := m0.dsHiF
  dcLo := m0.dcLo
  dcLoF := m0.dcLoF
  tSU := m0.tSU
  tHD := m0.tHD
  tCO := m0.tCO
  H_SETUP_LINE := by
    have := m0.H_SETUP_LINE
    refine ⟨by omega, by omega, by omega, by omega, by omega⟩
  H_CO_LINE := ⟨by omega, by omega⟩
  H_FOUR_PHASE_ENV := ⟨by omega, by omega, by omega, by omega⟩

theorem fast_same (m0 : MemPort) : Same (fast m0) m0 := by
  unfold Same; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem setup_exact (m0 : MemPort) :
    (∀ m, Same m m0 → m.tPay + m.tSU ≤ m.tClkR) ↔ m0.tSU ≤ m0.dsLo + 1 := by
  constructor
  · intro h; have := h (fast m0) (fast_same m0); simp only [fast] at this; omega
  · intro h m hs
    obtain ⟨e1, -, -, -, -, -, e7, -, -⟩ := hs
    exact m.setup_ok (by omega)

theorem hold_exact (m0 : MemPort) :
    (∀ m, Same m m0 → m.tClkR + m.tHD ≤ m.tPayNext) ↔ m0.tHD ≤ m0.dcLo + m0.dsLoF + m0.dcLoF := by
  constructor
  · intro h; have := h (fast m0) (fast_same m0); simp only [fast] at this; omega
  · intro h m hs
    obtain ⟨-, -, e3, -, e5, e6, -, e8, -⟩ := hs
    exact m.hold_ok (by omega)

theorem rdata_exact (m0 : MemPort) :
    (∀ m, Same m m0 → m.tClkR + m.tCO ≤ m.tAckR) ↔ m0.tCO ≤ m0.dcLo := by
  constructor
  · intro h; have := h (fast m0) (fast_same m0); simp only [fast] at this; omega
  · intro h m hs
    obtain ⟨-, -, -, -, e5, -, -, -, e9⟩ := hs
    exact m.rdata_before_ack (by omega)

/-- The clock high width is at least `dcLo + dsLoF` on every port (measured
from the clock's own rise). -/
theorem clk_high_tight (m : MemPort) : m.tClkR + m.dcLo + m.dsLoF ≤ m.tClkF := by
  have := m.H_SETUP_LINE; have := m.H_CO_LINE; have := m.H_FOUR_PHASE_ENV; omega

theorem clk_high_exact (m0 : MemPort) (tPWH : Nat) :
    (∀ m, Same m m0 → m.tClkR + tPWH ≤ m.tClkF) ↔ tPWH ≤ m0.dcLo + m0.dsLoF := by
  constructor
  · intro h; have := h (fast m0) (fast_same m0); simp only [fast] at this; omega
  · intro h m hs
    obtain ⟨-, -, e3, -, e5, -, -, -, -⟩ := hs
    have := clk_high_tight m; omega

theorem clk_low_exact (m0 : MemPort) (tPWL : Nat) :
    (∀ m, Same m m0 → m.tClkF + tPWL ≤ m.tClkR2) ↔ tPWL ≤ m0.dcLoF + m0.dsLo := by
  constructor
  · intro h; have := h (fast m0) (fast_same m0); simp only [fast] at this; omega
  · intro h m hs
    obtain ⟨e1, -, -, -, -, e6, -, -, -⟩ := hs
    exact ConstraintsMore.MemPort.clk_low_ok m tPWL (by omega)

/-- A concrete port: dsLo 1, dsHi 3, dsLoF 1, dsHiF 1, dcLo 1, dcLoF 1. -/
def p0 : MemPort := fast
  { tReqR := 0, tReqF := 2, tClkR := 1, tClkF := 3, tAckR := 2, tAckF := 4, tPay := 0,
    tPayNext := 4, tReqR2 := 4, tClkR2 := 5, dsLo := 1, dsHi := 3, dsLoF := 1, dsHiF := 1,
    dcLo := 1, dcLoF := 1, tSU := 1, tHD := 1, tCO := 1,
    H_SETUP_LINE := by decide, H_CO_LINE := by decide, H_FOUR_PHASE_ENV := by decide }

/-- **The shipped clock-high condition is not necessary**: with setup-line
spread 2 and `tPWH = 2`, `clk_high_ok`'s hypothesis `2 + 3 ≤ 1 + 1 + 1`
fails while every port with these numbers meets `tPWH`. -/
theorem clk_high_not_necessary :
    ¬ (2 + p0.dsHi ≤ p0.dsLo + p0.dcLo + p0.dsLoF) ∧ (∀ m, Same m p0 → m.tClkR + 2 ≤ m.tClkF) :=
  ⟨by decide, (clk_high_exact p0 2).2 (by decide)⟩

/-- Non-vacuity: `p0` meets every shipped condition at `tSU = tHD = tCO = 1`
(setup, hold, rdata hold on it). -/
theorem nonvacuous : p0.tPay + p0.tSU ≤ p0.tClkR ∧ p0.tClkR + p0.tHD ≤ p0.tPayNext ∧
    p0.tClkR + p0.tCO ≤ p0.tAckR := by decide

end Formal.Cells.Necessity5Mem
