import Formal.Target.CexRuntD60.X000
import Formal.Target.CexRuntD60.X001
import Formal.Target.CexRuntD60.X002
import Formal.Target.CexRuntD60.X003
import Formal.Target.CexRuntD60.X004
import Formal.Target.CexRuntD60.X005
import Formal.Target.CexRuntD60.X006
import Formal.Target.CexRuntD60.X007
import Formal.Target.CexRuntD60.X008
import Formal.Target.CexRuntD60.X009
import Formal.Target.CexRuntD60.X010
import Formal.Target.CexRuntD60.X011
import Formal.Target.CexRuntD60.X012
import Formal.Target.CexRuntD60.X013
import Formal.Target.CexRuntD60.X014
import Formal.Target.CexRuntD60.X015
import Formal.Target.CexRuntD60.X016
import Formal.Target.CexRuntD60.X017
import Formal.Target.CexRuntD60.X018
import Formal.Target.CexRuntD60.X019
import Formal.Target.CexRuntD60.X020
import Formal.Target.CexRuntD60.X021
import Formal.Target.CexRuntD60.X022
import Formal.Target.CexRuntD60.X023
import Formal.Target.CexRuntD60.X024
import Formal.Target.CexRuntD60.X025
import Formal.Target.CexRuntD60.X026
import Formal.Target.CexRuntD60.X027
import Formal.Target.CexRuntD60.X028
import Formal.Target.CexRuntD60.X029
import Formal.Target.CexRuntD60.X030
import Formal.Target.CexRuntD60.X031
import Formal.Target.CexRuntD60.X032
import Formal.Target.CexRuntD60.X033
import Formal.Target.CexRuntD60.X034
import Formal.Target.CexRuntD60.X035
import Formal.Target.CexRuntD60.X036
import Formal.Target.CexRuntD60.X037
import Formal.Target.CexRuntD60.X038
import Formal.Target.CexRuntD60.X039
import Formal.Target.CexRuntD60.X040
import Formal.Target.CexRuntD60.X041
import Formal.Target.CexRuntD60.X042
import Formal.Target.CexRuntD60.X043
import Formal.Target.CexRuntD60.X044
import Formal.Target.CexRuntD60.X045
import Formal.Target.CexRuntD60.X046
import Formal.Target.CexRuntD60.X047
import Formal.Target.CexRuntD60.X048
import Formal.Target.CexRuntD60.X049
import Formal.Target.CexRuntD60.X050
import Formal.Target.CexRuntD60.X051
import Formal.Target.CexRuntD60.X052
import Formal.Target.CexRuntD60.X053
import Formal.Target.CexRuntD60.X054
import Formal.Target.CexRuntD60.X055
import Formal.Target.CexRuntD60.X056
import Formal.Target.CexRuntD60.X057
import Formal.Target.CexRuntD60.X058
import Formal.Target.CexRuntD60.X059
import Formal.Target.CexRuntD60.X060
import Formal.Target.CexRuntD60.X061
import Formal.Target.CexRuntD60.X062
import Formal.Target.CexRuntD60.X063
import Formal.Target.CexRuntD60.X064
import Formal.Target.CexRuntD60.X065
import Formal.Target.CexRuntD60.X066
import Formal.Target.CexRuntD60.X067
import Formal.Target.CexRuntD60.X068
import Formal.Target.CexRuntD60.X069
import Formal.Target.CexRuntD60.X070
import Formal.Target.CexRuntD60.X071
import Formal.Target.CexRuntD60.X072
import Formal.Target.CexRuntD60.X073
import Formal.Target.CexRuntD60.X074

/-!
# A behaviour of THE target under H_RUNT(20 ps) that deadlocks, under a WIDER filter: w = 40 ps, g = 1, κ = 15/25 (shard A, 2026-11-07)

**Problem, plainly.** Shard C found (JOURNAL-C 2026-11-07 07:31-07:40, FOR-RESEARCH C3) that slowing only the
feedback route of one C-element (ulink_n_falseResult_85 stage 0, SLICE_X32Y45.A6: its pin-0 arc and the 6 pips/hops
of its self-loop route) to the top of its window, every other arc at the bottom, makes THE target deadlock on the
pair (1071, 462) at κ = 0.44 under H_RUNT(20) (`CexRunt44`). Does a WIDER runt filter save it? At w = 40 that run is
correct, and not even admissible (its slowed pin is at the top of its window, so it cannot skip anything). Giving the
adversary 40 ps of slack on those 7 arcs (`simrunt.py --classes --sslack 40`) it is correct at κ = 0.44, 0.48, 0.52 and
deadlocks at κ = 0.60. Is that run a behaviour under `SpecRunt.BehavesRunt 40`?

**Proved (if this file checks).** `xR` (shard A's dump tools-A/target/out/k60w40_dump.json.xz, data by
formal/tools-A/target/gen_runtp.py) is a behaviour of `circuit DecodedPS.net DecodedPS.boundary` under
`BehavesRunt 40` at `pP 15 = ⟨1, 15/25⟩`, corner 0 (`behavesRunt_r`): the 7 listed arcs read at the
explicit delays in `slR` (top of their κ = 15/25 window minus 40 ps, floored at the fast end), every other at
⌈10·FAST_MIN/25⌉ (LUT pins at least 40 ps), every LUT pin skipping every pulse narrower than 40 ps inside its window; every gate kernel-checked at every breakpoint.

**Assumptions used.** Only Spec's and SpecRunt's definitions; standard axioms.
-/

namespace Formal.Target.CexRuntD60
open Formal.Target Formal.Target.DecodedPS Formal.Net.CViewPS Formal.Net.CexPS72 Formal.Target.CexRuntD

def gR : List (List Gate) := [g000, g001, g002, g003, g004, g005, g006, g007, g008, g009, g010, g011, g012, g013, g014, g015, g016, g017, g018, g019, g020, g021, g022, g023, g024, g025, g026, g027, g028, g029, g030, g031, g032, g033, g034, g035, g036, g037, g038, g039, g040, g041, g042, g043, g044, g045, g046, g047, g048, g049, g050, g051, g052, g053, g054, g055, g056, g057, g058, g059, g060, g061, g062, g063, g064, g065, g066, g067, g068, g069, g070, g071, g072, g073, g074]

theorem gates_eq : gates = gR.flatten := by simp [gates, gR]

set_option maxRecDepth 100000 in
theorem x_all : ∀ c, c < gR.length → (gR.getD c []).all (fun g => !keepPS g || gateWR 15 40 encR chR slR g) = true := by
  intro c hc
  have h75 : gR.length = 75 := rfl
  rw [h75] at hc
  match c, hc with
  | 0, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x000_ok
  | 1, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x001_ok
  | 2, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x002_ok
  | 3, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x003_ok
  | 4, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x004_ok
  | 5, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x005_ok
  | 6, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x006_ok
  | 7, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x007_ok
  | 8, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x008_ok
  | 9, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x009_ok
  | 10, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x010_ok
  | 11, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x011_ok
  | 12, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x012_ok
  | 13, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x013_ok
  | 14, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x014_ok
  | 15, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x015_ok
  | 16, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x016_ok
  | 17, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x017_ok
  | 18, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x018_ok
  | 19, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x019_ok
  | 20, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x020_ok
  | 21, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x021_ok
  | 22, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x022_ok
  | 23, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x023_ok
  | 24, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x024_ok
  | 25, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x025_ok
  | 26, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x026_ok
  | 27, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x027_ok
  | 28, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x028_ok
  | 29, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x029_ok
  | 30, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x030_ok
  | 31, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x031_ok
  | 32, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x032_ok
  | 33, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x033_ok
  | 34, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x034_ok
  | 35, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x035_ok
  | 36, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x036_ok
  | 37, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x037_ok
  | 38, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x038_ok
  | 39, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x039_ok
  | 40, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x040_ok
  | 41, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x041_ok
  | 42, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x042_ok
  | 43, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x043_ok
  | 44, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x044_ok
  | 45, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x045_ok
  | 46, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x046_ok
  | 47, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x047_ok
  | 48, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x048_ok
  | 49, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x049_ok
  | 50, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x050_ok
  | 51, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x051_ok
  | 52, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x052_ok
  | 53, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x053_ok
  | 54, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x054_ok
  | 55, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x055_ok
  | 56, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x056_ok
  | 57, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x057_ok
  | 58, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x058_ok
  | 59, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x059_ok
  | 60, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x060_ok
  | 61, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x061_ok
  | 62, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x062_ok
  | 63, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x063_ok
  | 64, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x064_ok
  | 65, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x065_ok
  | 66, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x066_ok
  | 67, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x067_ok
  | 68, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x068_ok
  | 69, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x069_ok
  | 70, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x070_ok
  | 71, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x071_ok
  | 72, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x072_ok
  | 73, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x073_ok
  | 74, _ => simp only [gR, List.getD_cons_succ, List.getD_cons_zero]; exact x074_ok
  | n + 75, h => exact absurd h (by omega)

/-- The counterexample behaviour. -/
def xR : Beh := fun n => sigL (encR n)

theorem behavesRunt_r : BehavesRunt 40 (pP 15) (circuit net boundary) xR := by
  refine ⟨0, le_refl _, zero_le_one, fun g hg => ?_⟩
  have hmem := hg
  rw [circuit_gates, gates_eq, List.mem_filter, List.mem_flatten] at hmem
  obtain ⟨⟨gc, hgc, hgg⟩, hk⟩ := hmem
  obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem hgc
  have hall := x_all c hc
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc, Option.getD_some] at hall
  have := List.all_eq_true.mp hall g hgg
  simp only [hk, Bool.not_true, Bool.false_or] at this
  exact gateOKRunt_of_gateWR 15 (by norm_num) 40 (by norm_num) _ _ _ g this

end Formal.Target.CexRuntD60
