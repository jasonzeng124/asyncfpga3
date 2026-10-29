import Formal.Core.Prims.Ram
import Formal.Core.Prims.SeqXray

/-!
# Formal.Core.Prims.RamXray — prjxray-db numbers for RAMB18E1 port A (bd_mem's configuration)

Shard A, probe PrimsRam. Core Lean only. Notes: `formal/notes/A-prims-ram.md` §2.

## Source (transcribed by hand, integer ps; checked by `Wip/PrimsRam/bram_xray.py --check`)

`$TC/openxc7/share/nextpnr/prjxray-db/zynq7/timings/BRAM_L.sdf` (`TIMESCALE 1ns`, sha256
`71fdc426...5302f`; `BRAM_R.sdf` is identical up to the tile name). All of it is one cell
type `RAMBFIFO36E1` with configuration-suffixed CELLTYPEs:

* CLK->DO, `RAM_MODE_U_RAMB18TDP_U_DOA_REG_U_0`: `IOPATH CLKARDCLKU DOADOU
  (0.585::1.098)(1.353::2.454)`. (`DOA_REG_U_1`: `(0.204::0.327)(0.468::0.882)`, not used.)
* ADDR, cell `RAMBFIFO36E1`: `SETUP ADDRAU (-0.360::0.566)`, `HOLD ADDRAU (-0.566::0.360)`.
* WE, cell `RAMBFIFO36E1`: `SETUP WEAU (-0.197::0.532)`, `HOLD WEAU (-0.532::0.197)`.
* DI, `RAM_MODE_RAMB18TDP_U_WRITE_MODE_U_{WF,NC}`: `SETUP DIADIU (-0.667::0.737)`,
  `HOLD DIADIU (-0.737::0.667)`; `..._U_RF`: `SETUP (-0.405::0.241)`, `HOLD (-0.241::0.405)`.

## Corners and which number is used

IOPATH triples are `(FAST_MIN::FAST_MAX)(SLOW_MIN::SLOW_MAX)` (fast/slow process corners,
NOT rise/fall; no rise/fall split anywhere). TIMINGCHECKs carry ONE pair,
`(SLOW_MIN::SLOW_MAX)` (`prjxray/utils/makesdf.py`), so there is no fast-corner window:
**H_WINDOW_SLOW_ONLY** (as for the slice flops). The BRAM pairs have a peculiar shape:
`SETUP = (-h, s)` and `HOLD = (-s, h)` for the same `s, h`. Either way the widest window is
`lo = -SETUP_MAX = HOLD_MIN`, `hi = HOLD_MAX = -SETUP_MIN`, used here (a wider window only
adds X). So ADDR `[e-566, e+360]`, WE `[e-532, e+197]`, DI(WRITE_FIRST) `[e-737, e+667]`.

## Coverage gaps (facts about the file, `bram_xray.py` prints them)

* Only the UPPER RAMB18 of a RAMB36 tile (`..U`, `RAMB18_Y1`) has TDP numbers: there is no
  `ADDRAL`/`WEAL`/`DIADIL` check and no `CLKARDCLKL -> DOADOL` arc for TDP mode (the `L`
  CLK->DO arc exists only for FIFO18 mode, with the same values). A bd_mem placed in
  `RAMB18_Y0` is given the U numbers: **H_BRAM_LU_SAME**, untested.
* No minimum clock period / pulse width, no clock-to-clock collision window for the BRAM:
  **H_BRAM_PERIOD** (the model trusts every edge).
* ENARDEN (`(-0.227::0.443)`/`(-0.443::0.227)`) and RSTRAMA exist but bd_mem ties them to
  constants, so they never have a window to violate.
-/

namespace Formal.Core.Prims.Ram

open Formal.Core.Prims.Seq

/-! ## Raw numbers (integer ps), named as `bram_xray.py` prints them -/

def coFastLo : Nat := 585
def coFastHi : Nat := 1098
def coSlowLo : Nat := 1353
def coSlowHi : Nat := 2454
/-- `DOA_REG = 1` (registered output): NOT bd_mem's configuration, recorded for completeness. -/
def coRegFastLo : Nat := 204
def coRegFastHi : Nat := 327
def coRegSlowLo : Nat := 468
def coRegSlowHi : Nat := 882
def addrSetupMin : Int := -360
def addrSetupMax : Int := 566
def addrHoldMin : Int := -566
def addrHoldMax : Int := 360
def weSetupMin : Int := -197
def weSetupMax : Int := 532
def weHoldMin : Int := -532
def weHoldMax : Int := 197
def diWFSetupMin : Int := -667
def diWFSetupMax : Int := 737
def diWFHoldMin : Int := -737
def diWFHoldMax : Int := 667
def diRFSetupMin : Int := -405
def diRFSetupMax : Int := 241
def diRFHoldMin : Int := -241
def diRFHoldMax : Int := 405
def diNCSetupMin : Int := -667
def diNCSetupMax : Int := 737
def diNCHoldMin : Int := -737
def diNCHoldMax : Int := 667

/-- The DI window ends for a write mode. -/
def diLo : WMode → Int
  | .writeFirst => -diWFSetupMax
  | .readFirst => -diRFSetupMax
  | .noChange => -diNCSetupMax
def diHi : WMode → Int
  | .writeFirst => diWFHoldMax
  | .readFirst => diRFHoldMax
  | .noChange => diNCHoldMax

/-- Port A of a TDP x18 RAMB18E1 with `DOA_REG = 0`, at corner `c`, write mode `md`. -/
def bram (c : XCorner) (md : WMode) : RamTiming :=
  { cqLo := cs c coFastLo coSlowLo
    cqHi := cs c coFastHi coSlowHi
    aLo := -addrSetupMax, aHi := addrHoldMax
    weLo := -weSetupMax, weHi := weHoldMax
    dLo := diLo md, dHi := diHi md }

theorem bram_ok (c : XCorner) (md : WMode) : (bram c md).Ok := by
  cases c <;> cases md <;> decide

/-- The widest-window reading agrees from both ends: `-SETUP_MAX = HOLD_MIN` and
`HOLD_MAX = -SETUP_MIN`, for every pin used. -/
theorem windows_symmetric :
    -addrSetupMax = addrHoldMin ∧ addrHoldMax = -addrSetupMin ∧
    -weSetupMax = weHoldMin ∧ weHoldMax = -weSetupMin ∧
    -diWFSetupMax = diWFHoldMin ∧ diWFHoldMax = -diWFSetupMin := by decide

/-- bd_mem's configuration: WRITE_FIRST. Slow corner: CLK->DO `[1353, 2454]`, ADDR
`[-566, 360]`, WE `[-532, 197]`, DI `[-737, 667]`. -/
theorem bram_slow_wf : bram .slow .writeFirst =
    { cqLo := 1353, cqHi := 2454, aLo := -566, aHi := 360, weLo := -532, weHi := 197,
      dLo := -737, dHi := 667 } := by decide

theorem bram_fast_wf : bram .fast .writeFirst =
    { cqLo := 585, cqHi := 1098, aLo := -566, aHi := 360, weLo := -532, weHi := 197,
      dLo := -737, dHi := 667 } := by decide

/-- The widest aperture in bd_mem's configuration is DI's, 737 + 667 = 1404 ps: any change
of the payload in `[e - 737, e + 667]` around the CLKARDCLK edge can corrupt the access. -/
theorem wf_aperture : (bram .slow .writeFirst).dHi - (bram .slow .writeFirst).dLo = 1404 := by
  decide

end Formal.Core.Prims.Ram
