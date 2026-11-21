import Formal.Target.CexQ36.X000
import Formal.Target.CexQ36.X001
import Formal.Target.CexQ36.X002
import Formal.Target.CexQ36.X003
import Formal.Target.CexQ36.X004
import Formal.Target.CexQ36.X005
import Formal.Target.CexQ36.X006
import Formal.Target.CexQ36.X007
import Formal.Target.CexQ36.X008
import Formal.Target.CexQ36.X009
import Formal.Target.CexQ36.X010
import Formal.Target.CexQ36.X011
import Formal.Target.CexQ36.X012
import Formal.Target.CexQ36.X013
import Formal.Target.CexQ36.X014
import Formal.Target.CexQ36.X015
import Formal.Target.CexQ36.X016
import Formal.Target.CexQ36.X017
import Formal.Target.CexQ36.X018
import Formal.Target.CexQ36.X019
import Formal.Target.CexQ36.X020
import Formal.Target.CexQ36.X021
import Formal.Target.CexQ36.X022
import Formal.Target.CexQ36.X023
import Formal.Target.CexQ36.X024
import Formal.Target.CexQ36.X025
import Formal.Target.CexQ36.X026
import Formal.Target.CexQ36.X027
import Formal.Target.CexQ36.X028
import Formal.Target.CexQ36.X029
import Formal.Target.CexQ36.X030
import Formal.Target.CexQ36.X031
import Formal.Target.CexQ36.X032
import Formal.Target.CexQ36.X033
import Formal.Target.CexQ36.X034
import Formal.Target.CexQ36.X035
import Formal.Target.CexQ36.X036
import Formal.Target.CexQ36.X037
import Formal.Target.CexQ36.X038
import Formal.Target.CexQ36.X039
import Formal.Target.CexQ36.X040
import Formal.Target.CexQ36.X041
import Formal.Target.CexQ36.X042
import Formal.Target.CexQ36.X043
import Formal.Target.CexQ36.X044
import Formal.Target.CexQ36.X045
import Formal.Target.CexQ36.X046
import Formal.Target.CexQ36.X047
import Formal.Target.CexQ36.X048
import Formal.Target.CexQ36.X049
import Formal.Target.CexQ36.X050
import Formal.Target.CexQ36.X051
import Formal.Target.CexQ36.X052
import Formal.Target.CexQ36.X053
import Formal.Target.CexQ36.X054
import Formal.Target.CexQ36.X055
import Formal.Target.CexQ36.X056
import Formal.Target.CexQ36.X057
import Formal.Target.CexQ36.X058
import Formal.Target.CexQ36.X059
import Formal.Target.CexQ36.X060
import Formal.Target.CexQ36.X061
import Formal.Target.CexQ36.X062
import Formal.Target.CexQ36.X063
import Formal.Target.CexQ36.X064
import Formal.Target.CexQ36.X065
import Formal.Target.CexQ36.X066
import Formal.Target.CexQ36.X067
import Formal.Target.CexQ36.X068
import Formal.Target.CexQ36.X069
import Formal.Target.CexQ36.X070
import Formal.Target.CexQ36.X071
import Formal.Target.CexQ36.X072
import Formal.Target.CexQ36.X073
import Formal.Target.CexQ36.X074

/-!
# A behaviour of THE target under H_RUNT(20 ps) that LIVELOCKS, at g = 1, κ = 9/25 (shard A, 2026-11-09)

**Problem, plainly.** Under H_RUNT(20) and within-die scatter κ = 0.36 at the fast corner, can THE target fail to
answer the full-width pair (0x49e9c618, 0x35bf992e) without ever going quiet?

**Proved (if this file checks).** `xR` is a behaviour of `circuit DecodedPS.net DecodedPS.boundary` under
`SpecRunt.BehavesRunt 20` at `pP 9 = ⟨1, 9/25⟩`, corner 0 (`behavesRunt_r`). `xR` is eventually periodic: every node
follows its prefix code (transitions before 491,000 ps) and then repeats one period of 79 ps for ever (140 nodes
oscillate; `CexRuntQ.xQ`). Delays: pin 0 of the C-element SLICE_X16Y21.A6 and the 5 pips/hops of its route from
SLICE_X17Y23.B6 at ⌊34·FAST_MAX/25⌋ (6 arcs, `slR`), every other arc at ⌈16·FAST_MIN/25⌉, LUT pins raised to at
least 20 ps; LUT pins skip narrow-pulse chains (A's jump reads). Run: shard B's simadv.py --classes --w 20 dump
(`formal/tools-B/target/out/k36w20_x16y21_dump_1200ns.json.xz`), periodic from 490,314 ps to 1.2 µs; data by
`formal/tools-A/target/gen_runtq.py` (Q 79, t0 491000, m 21, V 492501).

**Assumptions used.** Only Spec's and SpecRunt's definitions; standard axioms. The finite check is
`CexRuntQ.gateQ` (window [start, 492,580) of the run unrolled to 492,659 ps, plus seam/floor conditions), sound by
`CexRuntQ.gateOKRunt_of_gateQ` and `SpecPeriodic.gateOKRunt_of_window`.
-/

namespace Formal.Target.CexQ36
open Formal.Target Formal.Target.DecodedPS Formal.Net.CViewPS Formal.Net.CexPS72 Formal.Target.CexRuntP Formal.Target.CexRuntQ

def gR : List (List Gate) := [g000, g001, g002, g003, g004, g005, g006, g007, g008, g009, g010, g011, g012, g013, g014, g015, g016, g017, g018, g019, g020, g021, g022, g023, g024, g025, g026, g027, g028, g029, g030, g031, g032, g033, g034, g035, g036, g037, g038, g039, g040, g041, g042, g043, g044, g045, g046, g047, g048, g049, g050, g051, g052, g053, g054, g055, g056, g057, g058, g059, g060, g061, g062, g063, g064, g065, g066, g067, g068, g069, g070, g071, g072, g073, g074]

theorem gates_eq : gates = gR.flatten := by simp [gates, gR]

set_option maxRecDepth 100000 in
theorem x_all : ∀ c, c < gR.length → (gR.getD c []).all (fun g => !keepPS g || gateQ 9 20 79 491000 21 492501 encR perR chR slR g) = true := by
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

/-- The counterexample behaviour: the prefix codes, then one period repeated for ever. -/
def xR : Beh := xQ 79 encR perR

theorem behavesRunt_r : BehavesRunt 20 (pP 9) (circuit net boundary) xR := by
  refine ⟨0, le_refl _, zero_le_one, fun g hg => ?_⟩
  have hmem := hg
  rw [circuit_gates, gates_eq, List.mem_filter, List.mem_flatten] at hmem
  obtain ⟨⟨gc, hgc, hgg⟩, hk⟩ := hmem
  obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem hgc
  have hall := x_all c hc
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc, Option.getD_some] at hall
  have := List.all_eq_true.mp hall g hgg
  simp only [hk, Bool.not_true, Bool.false_or] at this
  exact gateOKRunt_of_gateQ 9 (by norm_num) 20 (by norm_num) 79 491000 21 492501 (by norm_num) _ _ _ _ g this

end Formal.Target.CexQ36
