import Formal.Core.Prims.SeqXray

/-!
P14 audit (A): SeqXray SLICEM windows (commits 5f245cc4 / 1fa61617), against my own reading of
`/root/audit-tc/openxc7/share/nextpnr/prjxray-db/zynq7/timings/slicem.sdf`
(md5 5cdfd60b4f988d57cdc1a7c4b8b7fd72, identical to /root/dev2/lib/xray/prjxray-db).
Convention (theirs, checked on the SLICEL defs): lo = -SETUP_MAX, hi = HOLD_MAX,
srLo = -RECOVERY_MAX, srHi = REMOVAL_MAX, IOPATH (fmin::fmax)(smin::smax) -> cs c fmin smin / fmax smax.

Every number below is typed from the SDF by me (not copied from their file).
-/

open Formal.Core.Prims.Seq

-- REG_INIT_FF (SLICEM): CLK Q (0.118::0.147)(0.292::0.362); SETUP DIN (-0.074::-0.06);
-- HOLD DIN (0.211::0.262); SETUP CE (0.088::0.109); HOLD CE (-0.007::-0.005)
-- REG_INIT_FF_QH: SR Q (0.197::0.245)(0.489::0.606); RECOVERY (0.314::0.389); REMOVAL (-0.292::-0.238)
-- REG_INIT_FF_QL: SR Q (0.247::0.308)(0.689::0.855); RECOVERY (0.279::0.347); REMOVAL (-0.285::-0.232)
example : ∀ rv r, (regFFM .fast rv r).cqLo = 118 ∧ (regFFM .slow rv r).cqLo = 292 ∧
    (regFFM .fast rv r).cqHi = 147 ∧ (regFFM .slow rv r).cqHi = 362 ∧
    (regFFM .slow rv r).dLo = 60 ∧ (regFFM .slow rv r).dHi = 262 ∧
    (regFFM .slow rv r).ceLo = -109 ∧ (regFFM .slow rv r).ceHi = -5 := by
  intro rv r; cases rv <;> decide
example : ∀ r, (regFFM .slow true r).srLo = -389 ∧ (regFFM .slow true r).srHi = -238 ∧
    (regFFM .fast true r).sqLo = 197 ∧ (regFFM .slow true r).sqLo = 489 ∧
    (regFFM .fast true r).sqHi = 245 ∧ (regFFM .slow true r).sqHi = 606 := by intro r; decide
example : ∀ r, (regFFM .slow false r).srLo = -347 ∧ (regFFM .slow false r).srHi = -232 ∧
    (regFFM .fast false r).sqLo = 247 ∧ (regFFM .slow false r).sqLo = 689 ∧
    (regFFM .fast false r).sqHi = 308 ∧ (regFFM .slow false r).sqHi = 855 := by intro r; decide

-- FF_INIT (SLICEM): CLK Q (0.102::0.127)(0.259::0.322); SETUP DIN (-0.074::-0.06); HOLD DIN (0.194::0.241)
-- CE as REG_INIT_FF. FF_INIT_QH: SR Q (0.184::0.229)(0.455::0.565); RECOVERY (0.279::0.347); REMOVAL (-0.292::-0.238)
-- FF_INIT_QL: SR Q (0.233::0.29)(0.648::0.804); RECOVERY (0.314::0.389); REMOVAL (-0.285::-0.232)
example : ∀ rv r, (ff5M .fast rv r).cqLo = 102 ∧ (ff5M .slow rv r).cqLo = 259 ∧
    (ff5M .fast rv r).cqHi = 127 ∧ (ff5M .slow rv r).cqHi = 322 ∧
    (ff5M .slow rv r).dLo = 60 ∧ (ff5M .slow rv r).dHi = 241 ∧
    (ff5M .slow rv r).ceLo = -109 ∧ (ff5M .slow rv r).ceHi = -5 := by
  intro rv r; cases rv <;> decide
example : ∀ r, (ff5M .slow true r).srLo = -347 ∧ (ff5M .slow true r).srHi = -238 ∧
    (ff5M .fast true r).sqLo = 184 ∧ (ff5M .slow true r).sqLo = 455 ∧
    (ff5M .fast true r).sqHi = 229 ∧ (ff5M .slow true r).sqHi = 565 := by intro r; decide
example : ∀ r, (ff5M .slow false r).srLo = -389 ∧ (ff5M .slow false r).srHi = -232 ∧
    (ff5M .fast false r).sqLo = 233 ∧ (ff5M .slow false r).sqLo = 648 ∧
    (ff5M .fast false r).sqHi = 290 ∧ (ff5M .slow false r).sqHi = 804 := by intro r; decide

-- REG_INIT_LAT (SLICEM): CE Q (0.129::0.161)(0.415::0.514); CLK Q (0.132::0.164)(0.378::0.469);
-- D Q (0.075::0.094)(0.214::0.265); HOLD DIN (0.211::0.262); SETUP DIN (-0.078::-0.064)
-- gate band = hull(CE Q, CLK Q): fast [129,164], slow [378,514]
-- _QH SR Q (0.161::0.201)(0.493::0.611); _QL SR Q (0.198::0.246)(0.645::0.8)
example : ∀ rv r, (latM .fast rv r).gqLo = min 129 132 ∧ (latM .slow rv r).gqLo = min 415 378 ∧
    (latM .fast rv r).gqHi = max 161 164 ∧ (latM .slow rv r).gqHi = max 514 469 ∧
    (latM .fast rv r).dqLo = 75 ∧ (latM .slow rv r).dqLo = 214 ∧
    (latM .fast rv r).dqHi = 94 ∧ (latM .slow rv r).dqHi = 265 ∧
    (latM .slow rv r).hHi = 262 ∧ (latM .slow rv r).hLo = -265 ∧
    (latM .slow rv r).hLo ≤ 64 := by
  intro rv r; cases rv <;> decide
example : ∀ r, (latM .fast true r).sqLo = 161 ∧ (latM .slow true r).sqLo = 493 ∧
    (latM .fast true r).sqHi = 201 ∧ (latM .slow true r).sqHi = 611 ∧
    (latM .fast false r).sqLo = 198 ∧ (latM .slow false r).sqLo = 645 ∧
    (latM .fast false r).sqHi = 246 ∧ (latM .slow false r).sqHi = 800 := by intro r; decide

-- site selection dispatches as claimed
example : regFFAt .slicem = regFFM ∧ regFFAt .slicel = regFF ∧ latAt .slicem = latM ∧ ff5At .slicem = ff5M :=
  ⟨rfl, rfl, rfl, rfl⟩

-- Mutation sanity: a wrong SLICEM hold (the SLICEL 241) is detected.
example : (regFFM .slow false 0).dHi ≠ 241 := by decide

#print axioms Formal.Core.Prims.Seq.slicem_hold_longer
#print axioms Formal.Core.Prims.Seq.regFFAt_ok
