import Formal.Timing.RtFbCore
import Formal.Timing.RtFbGcdSd
import Formal.Timing.RtFbGcdS2
import Formal.Timing.RtFbGcdS3
import Formal.Timing.RtFbGcdS4

/-!
# RT_FB on every C-element of the routed, shipped gcd_hw kernel (probes C-10f, C-10f2)

gcd_hw = the board-measured design: bdc-compiled gcd (cloud/fixtures/frontend/gcd) + cells/hw/gcd_rig.v,
built by the project flow (cells/hw/build_hw.sh gcd_hw, BDC_SELECT_PADS = cells/hw/gcd_hw_pads.json,
BD_RLOC=v4, no --freq (BOARD-QUEUE #1's command; the same
recipe with --freq 100 gives a byte-identical FASM on all 4 seeds, C-10f2), nextpnr 9c732bc6303458df, toolchain.sh ok, fasm_audit PASS; routes by
formal/tools/rtfb/route_gcd.sh = C-10e's recipe), read back from the bitstream by
formal/tools/rtfb/rtfb_design.py.

C-10f2 (2026-10-29): routes that leave a slice through AMUX..DMUX now carry the driver-side OUTMUX
hop (prjxray slicel/slicem.sdf, e.g. a6lut -> amux (0.071::0.088)(0.168::0.209) ns), on the
feedback and on every response net.  C-10f's data had no such hop (audit P4).

Data `RtFbGcdS<seed>`: one entry per C-element (bd_c2/c2n/_set/c3/c4) that has a response path
whose H_INDEP lower bound is below its feedback's H_INDEP upper bound: the tree of its feedback
route and every such simple response path through any number of LUTs.  The other C-elements
(H_CONE, Python-checked by Dijkstra, not in Lean) have no response that can arrive before the
latest feedback in ANY bound variant.

| seed | C-elements | in Lean | failing indep | fast | slow | fastE | slowE | worst slowE (ps) |
|---|---|---|---|---|---|---|---|---|
| d | 363 | 12 | 12 | 0 | 0 | 0 | 0 | 530 |
| 2 | 363 | 10 | 10 | 0 | 0 | 0 | 0 | 162 |
| 3 | 363 | 6 | 6 | 0 | 0 | 0 | 0 | 895 |
| 4 | 363 | 10 | 10 | 1 | 0 | 0 | 0 | 161 |
-/

namespace Formal.Timing.RtFb
open Formal.Timing Formal.Net Formal.Timing.Routed

theorem gcdd_len : RtFbGcdSd.slowE.length = 12 := by decide +kernel
theorem gcdd_pass :
    nPass RtFbGcdSd.indep = 0 ∧
    nPass RtFbGcdSd.fast = 12 ∧
    nPass RtFbGcdSd.slow = 12 ∧
    nPass RtFbGcdSd.fastE = 12 ∧
    nPass RtFbGcdSd.slowE = 12 ∧
    nPass RtFbGcdSd.sdf = 12 := by decide +kernel
theorem gcdd_worst :
    worstSlack RtFbGcdSd.indep = some (-503) ∧
    worstSlack RtFbGcdSd.fast = some (70) ∧
    worstSlack RtFbGcdSd.slow = some (348) ∧
    worstSlack RtFbGcdSd.fastE = some (252) ∧
    worstSlack RtFbGcdSd.slowE = some (530) ∧
    worstSlack RtFbGcdSd.sdf = some (421) := by decide +kernel
theorem gcdd_wf : RtFbGcdSd.indep.all wfOne = true ∧ RtFbGcdSd.fastE.all wfOne = true ∧ RtFbGcdSd.slowE.all wfOne = true := by
  decide +kernel
theorem gcdd_sep : RtFbGcdSd.indep.all sepOne = true := by decide +kernel
theorem gcdd_wf1 : RtFbGcdSd.fast.all wfOne = true ∧ RtFbGcdSd.slow.all wfOne = true := by
  decide +kernel
theorem gcdd_sep1 : RtFbGcdSd.fast.all sepOne = true ∧ RtFbGcdSd.slow.all sepOne = true ∧ RtFbGcdSd.fastE.all sepOne = true ∧ RtFbGcdSd.slowE.all sepOne = true := by
  decide +kernel
/-- gcd_hw seed d, one-corner variant `fast`: the 12 passing entries hold RT_FB in every run, the 0
failing entries each have a real violating fixed-delay run. -/
theorem gcdd_fast_exact :
    (∀ e ∈ RtFbGcdSd.fast, rtOne e = true → ∀ {sig : Nat → Trace}, Run (ofBuckets e.1) sig →
      ∀ r ∈ e.2.1, ∀ s t, changes (sig e.2.2.1) s → changes (sig r) t → s ≤ t) ∧
    (∀ e ∈ RtFbGcdSd.fast, rtOne e = false → ∃ r ∈ e.2.1, ∃ sig, Nonempty (FixedRun (ofBuckets e.1) sig) ∧
      ∃ s t, changes (sig e.2.2.1) s ∧ changes (sig r) t ∧ t < s) :=
  ⟨rt_sound_of _ gcdd_wf1.1, rt_violated_of _ gcdd_wf1.1 gcdd_sep1.1⟩

/-- gcd_hw seed d, one-corner variant `slow`: the 12 passing entries hold RT_FB in every run, the 0
failing entries each have a real violating fixed-delay run. -/
theorem gcdd_slow_exact :
    (∀ e ∈ RtFbGcdSd.slow, rtOne e = true → ∀ {sig : Nat → Trace}, Run (ofBuckets e.1) sig →
      ∀ r ∈ e.2.1, ∀ s t, changes (sig e.2.2.1) s → changes (sig r) t → s ≤ t) ∧
    (∀ e ∈ RtFbGcdSd.slow, rtOne e = false → ∃ r ∈ e.2.1, ∃ sig, Nonempty (FixedRun (ofBuckets e.1) sig) ∧
      ∃ s t, changes (sig e.2.2.1) s ∧ changes (sig r) t ∧ t < s) :=
  ⟨rt_sound_of _ gcdd_wf1.2, rt_violated_of _ gcdd_wf1.2 gcdd_sep1.2.1⟩

/-- gcd_hw seed d, one-corner variant `fastE`: the 12 passing entries hold RT_FB in every run, the 0
failing entries each have a real violating fixed-delay run. -/
theorem gcdd_fastE_exact :
    (∀ e ∈ RtFbGcdSd.fastE, rtOne e = true → ∀ {sig : Nat → Trace}, Run (ofBuckets e.1) sig →
      ∀ r ∈ e.2.1, ∀ s t, changes (sig e.2.2.1) s → changes (sig r) t → s ≤ t) ∧
    (∀ e ∈ RtFbGcdSd.fastE, rtOne e = false → ∃ r ∈ e.2.1, ∃ sig, Nonempty (FixedRun (ofBuckets e.1) sig) ∧
      ∃ s t, changes (sig e.2.2.1) s ∧ changes (sig r) t ∧ t < s) :=
  ⟨rt_sound_of _ gcdd_wf.2.1, rt_violated_of _ gcdd_wf.2.1 gcdd_sep1.2.2.1⟩

/-- gcd_hw seed d, one-corner variant `slowE`: the 12 passing entries hold RT_FB in every run, the 0
failing entries each have a real violating fixed-delay run. -/
theorem gcdd_slowE_exact :
    (∀ e ∈ RtFbGcdSd.slowE, rtOne e = true → ∀ {sig : Nat → Trace}, Run (ofBuckets e.1) sig →
      ∀ r ∈ e.2.1, ∀ s t, changes (sig e.2.2.1) s → changes (sig r) t → s ≤ t) ∧
    (∀ e ∈ RtFbGcdSd.slowE, rtOne e = false → ∃ r ∈ e.2.1, ∃ sig, Nonempty (FixedRun (ofBuckets e.1) sig) ∧
      ∃ s t, changes (sig e.2.2.1) s ∧ changes (sig r) t ∧ t < s) :=
  ⟨rt_sound_of _ gcdd_wf.2.2, rt_violated_of _ gcdd_wf.2.2 gcdd_sep1.2.2.2⟩

/-- gcd_hw seed d, H_ONE_CORNER + H_RC_EXACT (slowE): every C-element in the data satisfies RT_FB
in every run. -/
theorem gcdd_slowE_safe : ∀ e ∈ RtFbGcdSd.slowE, ∀ {sig : Nat → Trace}, Run (ofBuckets e.1) sig →
    ∀ r ∈ e.2.1, ∀ s t, changes (sig e.2.2.1) s → changes (sig r) t → s ≤ t := by
  have hall : RtFbGcdSd.slowE.all rtOne = true := by decide +kernel
  intro e he
  exact rt_sound_of _ gcdd_wf.2.2 e he (List.all_eq_true.1 hall e he)

/-- gcd_hw seed d, H_ONE_CORNER + H_RC_EXACT (fastE): every C-element in the data satisfies RT_FB
in every run. -/
theorem gcdd_fastE_safe : ∀ e ∈ RtFbGcdSd.fastE, ∀ {sig : Nat → Trace}, Run (ofBuckets e.1) sig →
    ∀ r ∈ e.2.1, ∀ s t, changes (sig e.2.2.1) s → changes (sig r) t → s ≤ t := by
  have hall : RtFbGcdSd.fastE.all rtOne = true := by decide +kernel
  intro e he
  exact rt_sound_of _ gcdd_wf.2.1 e he (List.all_eq_true.1 hall e he)

/-- gcd_hw seed d, H_INDEP: the 12 failing C-elements each have a real violating fixed-delay run. -/
theorem gcdd_indep_violated : ∀ e ∈ RtFbGcdSd.indep, rtOne e = false → ∃ r ∈ e.2.1, ∃ sig,
    Nonempty (FixedRun (ofBuckets e.1) sig) ∧ ∃ s t, changes (sig e.2.2.1) s ∧ changes (sig r) t ∧ t < s :=
  rt_violated_of _ gcdd_wf.1 gcdd_sep

theorem gcd2_len : RtFbGcdS2.slowE.length = 10 := by decide +kernel
theorem gcd2_pass :
    nPass RtFbGcdS2.indep = 0 ∧
    nPass RtFbGcdS2.fast = 10 ∧
    nPass RtFbGcdS2.slow = 10 ∧
    nPass RtFbGcdS2.fastE = 10 ∧
    nPass RtFbGcdS2.slowE = 10 ∧
    nPass RtFbGcdS2.sdf = 10 := by decide +kernel
theorem gcd2_worst :
    worstSlack RtFbGcdS2.indep = some (-498) ∧
    worstSlack RtFbGcdS2.fast = some (14) ∧
    worstSlack RtFbGcdS2.slow = some (132) ∧
    worstSlack RtFbGcdS2.fastE = some (44) ∧
    worstSlack RtFbGcdS2.slowE = some (162) ∧
    worstSlack RtFbGcdS2.sdf = some (419) := by decide +kernel
theorem gcd2_wf : RtFbGcdS2.indep.all wfOne = true ∧ RtFbGcdS2.fastE.all wfOne = true ∧ RtFbGcdS2.slowE.all wfOne = true := by
  decide +kernel
theorem gcd2_sep : RtFbGcdS2.indep.all sepOne = true := by decide +kernel
theorem gcd2_wf1 : RtFbGcdS2.fast.all wfOne = true ∧ RtFbGcdS2.slow.all wfOne = true := by
  decide +kernel
theorem gcd2_sep1 : RtFbGcdS2.fast.all sepOne = true ∧ RtFbGcdS2.slow.all sepOne = true ∧ RtFbGcdS2.fastE.all sepOne = true ∧ RtFbGcdS2.slowE.all sepOne = true := by
  decide +kernel
/-- gcd_hw seed 2, one-corner variant `fast`: the 10 passing entries hold RT_FB in every run, the 0
failing entries each have a real violating fixed-delay run. -/
theorem gcd2_fast_exact :
    (∀ e ∈ RtFbGcdS2.fast, rtOne e = true → ∀ {sig : Nat → Trace}, Run (ofBuckets e.1) sig →
      ∀ r ∈ e.2.1, ∀ s t, changes (sig e.2.2.1) s → changes (sig r) t → s ≤ t) ∧
    (∀ e ∈ RtFbGcdS2.fast, rtOne e = false → ∃ r ∈ e.2.1, ∃ sig, Nonempty (FixedRun (ofBuckets e.1) sig) ∧
      ∃ s t, changes (sig e.2.2.1) s ∧ changes (sig r) t ∧ t < s) :=
  ⟨rt_sound_of _ gcd2_wf1.1, rt_violated_of _ gcd2_wf1.1 gcd2_sep1.1⟩

/-- gcd_hw seed 2, one-corner variant `slow`: the 10 passing entries hold RT_FB in every run, the 0
failing entries each have a real violating fixed-delay run. -/
theorem gcd2_slow_exact :
    (∀ e ∈ RtFbGcdS2.slow, rtOne e = true → ∀ {sig : Nat → Trace}, Run (ofBuckets e.1) sig →
      ∀ r ∈ e.2.1, ∀ s t, changes (sig e.2.2.1) s → changes (sig r) t → s ≤ t) ∧
    (∀ e ∈ RtFbGcdS2.slow, rtOne e = false → ∃ r ∈ e.2.1, ∃ sig, Nonempty (FixedRun (ofBuckets e.1) sig) ∧
      ∃ s t, changes (sig e.2.2.1) s ∧ changes (sig r) t ∧ t < s) :=
  ⟨rt_sound_of _ gcd2_wf1.2, rt_violated_of _ gcd2_wf1.2 gcd2_sep1.2.1⟩

/-- gcd_hw seed 2, one-corner variant `fastE`: the 10 passing entries hold RT_FB in every run, the 0
failing entries each have a real violating fixed-delay run. -/
theorem gcd2_fastE_exact :
    (∀ e ∈ RtFbGcdS2.fastE, rtOne e = true → ∀ {sig : Nat → Trace}, Run (ofBuckets e.1) sig →
      ∀ r ∈ e.2.1, ∀ s t, changes (sig e.2.2.1) s → changes (sig r) t → s ≤ t) ∧
    (∀ e ∈ RtFbGcdS2.fastE, rtOne e = false → ∃ r ∈ e.2.1, ∃ sig, Nonempty (FixedRun (ofBuckets e.1) sig) ∧
      ∃ s t, changes (sig e.2.2.1) s ∧ changes (sig r) t ∧ t < s) :=
  ⟨rt_sound_of _ gcd2_wf.2.1, rt_violated_of _ gcd2_wf.2.1 gcd2_sep1.2.2.1⟩

/-- gcd_hw seed 2, one-corner variant `slowE`: the 10 passing entries hold RT_FB in every run, the 0
failing entries each have a real violating fixed-delay run. -/
theorem gcd2_slowE_exact :
    (∀ e ∈ RtFbGcdS2.slowE, rtOne e = true → ∀ {sig : Nat → Trace}, Run (ofBuckets e.1) sig →
      ∀ r ∈ e.2.1, ∀ s t, changes (sig e.2.2.1) s → changes (sig r) t → s ≤ t) ∧
    (∀ e ∈ RtFbGcdS2.slowE, rtOne e = false → ∃ r ∈ e.2.1, ∃ sig, Nonempty (FixedRun (ofBuckets e.1) sig) ∧
      ∃ s t, changes (sig e.2.2.1) s ∧ changes (sig r) t ∧ t < s) :=
  ⟨rt_sound_of _ gcd2_wf.2.2, rt_violated_of _ gcd2_wf.2.2 gcd2_sep1.2.2.2⟩

/-- gcd_hw seed 2, H_ONE_CORNER + H_RC_EXACT (slowE): every C-element in the data satisfies RT_FB
in every run. -/
theorem gcd2_slowE_safe : ∀ e ∈ RtFbGcdS2.slowE, ∀ {sig : Nat → Trace}, Run (ofBuckets e.1) sig →
    ∀ r ∈ e.2.1, ∀ s t, changes (sig e.2.2.1) s → changes (sig r) t → s ≤ t := by
  have hall : RtFbGcdS2.slowE.all rtOne = true := by decide +kernel
  intro e he
  exact rt_sound_of _ gcd2_wf.2.2 e he (List.all_eq_true.1 hall e he)

/-- gcd_hw seed 2, H_ONE_CORNER + H_RC_EXACT (fastE): every C-element in the data satisfies RT_FB
in every run. -/
theorem gcd2_fastE_safe : ∀ e ∈ RtFbGcdS2.fastE, ∀ {sig : Nat → Trace}, Run (ofBuckets e.1) sig →
    ∀ r ∈ e.2.1, ∀ s t, changes (sig e.2.2.1) s → changes (sig r) t → s ≤ t := by
  have hall : RtFbGcdS2.fastE.all rtOne = true := by decide +kernel
  intro e he
  exact rt_sound_of _ gcd2_wf.2.1 e he (List.all_eq_true.1 hall e he)

/-- gcd_hw seed 2, H_INDEP: the 10 failing C-elements each have a real violating fixed-delay run. -/
theorem gcd2_indep_violated : ∀ e ∈ RtFbGcdS2.indep, rtOne e = false → ∃ r ∈ e.2.1, ∃ sig,
    Nonempty (FixedRun (ofBuckets e.1) sig) ∧ ∃ s t, changes (sig e.2.2.1) s ∧ changes (sig r) t ∧ t < s :=
  rt_violated_of _ gcd2_wf.1 gcd2_sep

theorem gcd3_len : RtFbGcdS3.slowE.length = 6 := by decide +kernel
theorem gcd3_pass :
    nPass RtFbGcdS3.indep = 0 ∧
    nPass RtFbGcdS3.fast = 6 ∧
    nPass RtFbGcdS3.slow = 6 ∧
    nPass RtFbGcdS3.fastE = 6 ∧
    nPass RtFbGcdS3.slowE = 6 ∧
    nPass RtFbGcdS3.sdf = 6 := by decide +kernel
theorem gcd3_worst :
    worstSlack RtFbGcdS3.indep = some (-282) ∧
    worstSlack RtFbGcdS3.fast = some (248) ∧
    worstSlack RtFbGcdS3.slow = some (659) ∧
    worstSlack RtFbGcdS3.fastE = some (484) ∧
    worstSlack RtFbGcdS3.slowE = some (895) ∧
    worstSlack RtFbGcdS3.sdf = some (889) := by decide +kernel
theorem gcd3_wf : RtFbGcdS3.indep.all wfOne = true ∧ RtFbGcdS3.fastE.all wfOne = true ∧ RtFbGcdS3.slowE.all wfOne = true := by
  decide +kernel
theorem gcd3_sep : RtFbGcdS3.indep.all sepOne = true := by decide +kernel
theorem gcd3_wf1 : RtFbGcdS3.fast.all wfOne = true ∧ RtFbGcdS3.slow.all wfOne = true := by
  decide +kernel
theorem gcd3_sep1 : RtFbGcdS3.fast.all sepOne = true ∧ RtFbGcdS3.slow.all sepOne = true ∧ RtFbGcdS3.fastE.all sepOne = true ∧ RtFbGcdS3.slowE.all sepOne = true := by
  decide +kernel
/-- gcd_hw seed 3, one-corner variant `fast`: the 6 passing entries hold RT_FB in every run, the 0
failing entries each have a real violating fixed-delay run. -/
theorem gcd3_fast_exact :
    (∀ e ∈ RtFbGcdS3.fast, rtOne e = true → ∀ {sig : Nat → Trace}, Run (ofBuckets e.1) sig →
      ∀ r ∈ e.2.1, ∀ s t, changes (sig e.2.2.1) s → changes (sig r) t → s ≤ t) ∧
    (∀ e ∈ RtFbGcdS3.fast, rtOne e = false → ∃ r ∈ e.2.1, ∃ sig, Nonempty (FixedRun (ofBuckets e.1) sig) ∧
      ∃ s t, changes (sig e.2.2.1) s ∧ changes (sig r) t ∧ t < s) :=
  ⟨rt_sound_of _ gcd3_wf1.1, rt_violated_of _ gcd3_wf1.1 gcd3_sep1.1⟩

/-- gcd_hw seed 3, one-corner variant `slow`: the 6 passing entries hold RT_FB in every run, the 0
failing entries each have a real violating fixed-delay run. -/
theorem gcd3_slow_exact :
    (∀ e ∈ RtFbGcdS3.slow, rtOne e = true → ∀ {sig : Nat → Trace}, Run (ofBuckets e.1) sig →
      ∀ r ∈ e.2.1, ∀ s t, changes (sig e.2.2.1) s → changes (sig r) t → s ≤ t) ∧
    (∀ e ∈ RtFbGcdS3.slow, rtOne e = false → ∃ r ∈ e.2.1, ∃ sig, Nonempty (FixedRun (ofBuckets e.1) sig) ∧
      ∃ s t, changes (sig e.2.2.1) s ∧ changes (sig r) t ∧ t < s) :=
  ⟨rt_sound_of _ gcd3_wf1.2, rt_violated_of _ gcd3_wf1.2 gcd3_sep1.2.1⟩

/-- gcd_hw seed 3, one-corner variant `fastE`: the 6 passing entries hold RT_FB in every run, the 0
failing entries each have a real violating fixed-delay run. -/
theorem gcd3_fastE_exact :
    (∀ e ∈ RtFbGcdS3.fastE, rtOne e = true → ∀ {sig : Nat → Trace}, Run (ofBuckets e.1) sig →
      ∀ r ∈ e.2.1, ∀ s t, changes (sig e.2.2.1) s → changes (sig r) t → s ≤ t) ∧
    (∀ e ∈ RtFbGcdS3.fastE, rtOne e = false → ∃ r ∈ e.2.1, ∃ sig, Nonempty (FixedRun (ofBuckets e.1) sig) ∧
      ∃ s t, changes (sig e.2.2.1) s ∧ changes (sig r) t ∧ t < s) :=
  ⟨rt_sound_of _ gcd3_wf.2.1, rt_violated_of _ gcd3_wf.2.1 gcd3_sep1.2.2.1⟩

/-- gcd_hw seed 3, one-corner variant `slowE`: the 6 passing entries hold RT_FB in every run, the 0
failing entries each have a real violating fixed-delay run. -/
theorem gcd3_slowE_exact :
    (∀ e ∈ RtFbGcdS3.slowE, rtOne e = true → ∀ {sig : Nat → Trace}, Run (ofBuckets e.1) sig →
      ∀ r ∈ e.2.1, ∀ s t, changes (sig e.2.2.1) s → changes (sig r) t → s ≤ t) ∧
    (∀ e ∈ RtFbGcdS3.slowE, rtOne e = false → ∃ r ∈ e.2.1, ∃ sig, Nonempty (FixedRun (ofBuckets e.1) sig) ∧
      ∃ s t, changes (sig e.2.2.1) s ∧ changes (sig r) t ∧ t < s) :=
  ⟨rt_sound_of _ gcd3_wf.2.2, rt_violated_of _ gcd3_wf.2.2 gcd3_sep1.2.2.2⟩

/-- gcd_hw seed 3, H_ONE_CORNER + H_RC_EXACT (slowE): every C-element in the data satisfies RT_FB
in every run. -/
theorem gcd3_slowE_safe : ∀ e ∈ RtFbGcdS3.slowE, ∀ {sig : Nat → Trace}, Run (ofBuckets e.1) sig →
    ∀ r ∈ e.2.1, ∀ s t, changes (sig e.2.2.1) s → changes (sig r) t → s ≤ t := by
  have hall : RtFbGcdS3.slowE.all rtOne = true := by decide +kernel
  intro e he
  exact rt_sound_of _ gcd3_wf.2.2 e he (List.all_eq_true.1 hall e he)

/-- gcd_hw seed 3, H_ONE_CORNER + H_RC_EXACT (fastE): every C-element in the data satisfies RT_FB
in every run. -/
theorem gcd3_fastE_safe : ∀ e ∈ RtFbGcdS3.fastE, ∀ {sig : Nat → Trace}, Run (ofBuckets e.1) sig →
    ∀ r ∈ e.2.1, ∀ s t, changes (sig e.2.2.1) s → changes (sig r) t → s ≤ t := by
  have hall : RtFbGcdS3.fastE.all rtOne = true := by decide +kernel
  intro e he
  exact rt_sound_of _ gcd3_wf.2.1 e he (List.all_eq_true.1 hall e he)

/-- gcd_hw seed 3, H_INDEP: the 6 failing C-elements each have a real violating fixed-delay run. -/
theorem gcd3_indep_violated : ∀ e ∈ RtFbGcdS3.indep, rtOne e = false → ∃ r ∈ e.2.1, ∃ sig,
    Nonempty (FixedRun (ofBuckets e.1) sig) ∧ ∃ s t, changes (sig e.2.2.1) s ∧ changes (sig r) t ∧ t < s :=
  rt_violated_of _ gcd3_wf.1 gcd3_sep

theorem gcd4_len : RtFbGcdS4.slowE.length = 10 := by decide +kernel
theorem gcd4_pass :
    nPass RtFbGcdS4.indep = 0 ∧
    nPass RtFbGcdS4.fast = 9 ∧
    nPass RtFbGcdS4.slow = 10 ∧
    nPass RtFbGcdS4.fastE = 10 ∧
    nPass RtFbGcdS4.slowE = 10 ∧
    nPass RtFbGcdS4.sdf = 10 := by decide +kernel
theorem gcd4_worst :
    worstSlack RtFbGcdS4.indep = some (-559) ∧
    worstSlack RtFbGcdS4.fast = some (-16) ∧
    worstSlack RtFbGcdS4.slow = some (51) ∧
    worstSlack RtFbGcdS4.fastE = some (94) ∧
    worstSlack RtFbGcdS4.slowE = some (161) ∧
    worstSlack RtFbGcdS4.sdf = some (419) := by decide +kernel
theorem gcd4_wf : RtFbGcdS4.indep.all wfOne = true ∧ RtFbGcdS4.fastE.all wfOne = true ∧ RtFbGcdS4.slowE.all wfOne = true := by
  decide +kernel
theorem gcd4_sep : RtFbGcdS4.indep.all sepOne = true := by decide +kernel
theorem gcd4_wf1 : RtFbGcdS4.fast.all wfOne = true ∧ RtFbGcdS4.slow.all wfOne = true := by
  decide +kernel
theorem gcd4_sep1 : RtFbGcdS4.fast.all sepOne = true ∧ RtFbGcdS4.slow.all sepOne = true ∧ RtFbGcdS4.fastE.all sepOne = true ∧ RtFbGcdS4.slowE.all sepOne = true := by
  decide +kernel
/-- gcd_hw seed 4, one-corner variant `fast`: the 9 passing entries hold RT_FB in every run, the 1
failing entries each have a real violating fixed-delay run. -/
theorem gcd4_fast_exact :
    (∀ e ∈ RtFbGcdS4.fast, rtOne e = true → ∀ {sig : Nat → Trace}, Run (ofBuckets e.1) sig →
      ∀ r ∈ e.2.1, ∀ s t, changes (sig e.2.2.1) s → changes (sig r) t → s ≤ t) ∧
    (∀ e ∈ RtFbGcdS4.fast, rtOne e = false → ∃ r ∈ e.2.1, ∃ sig, Nonempty (FixedRun (ofBuckets e.1) sig) ∧
      ∃ s t, changes (sig e.2.2.1) s ∧ changes (sig r) t ∧ t < s) :=
  ⟨rt_sound_of _ gcd4_wf1.1, rt_violated_of _ gcd4_wf1.1 gcd4_sep1.1⟩

/-- gcd_hw seed 4, one-corner variant `slow`: the 10 passing entries hold RT_FB in every run, the 0
failing entries each have a real violating fixed-delay run. -/
theorem gcd4_slow_exact :
    (∀ e ∈ RtFbGcdS4.slow, rtOne e = true → ∀ {sig : Nat → Trace}, Run (ofBuckets e.1) sig →
      ∀ r ∈ e.2.1, ∀ s t, changes (sig e.2.2.1) s → changes (sig r) t → s ≤ t) ∧
    (∀ e ∈ RtFbGcdS4.slow, rtOne e = false → ∃ r ∈ e.2.1, ∃ sig, Nonempty (FixedRun (ofBuckets e.1) sig) ∧
      ∃ s t, changes (sig e.2.2.1) s ∧ changes (sig r) t ∧ t < s) :=
  ⟨rt_sound_of _ gcd4_wf1.2, rt_violated_of _ gcd4_wf1.2 gcd4_sep1.2.1⟩

/-- gcd_hw seed 4, one-corner variant `fastE`: the 10 passing entries hold RT_FB in every run, the 0
failing entries each have a real violating fixed-delay run. -/
theorem gcd4_fastE_exact :
    (∀ e ∈ RtFbGcdS4.fastE, rtOne e = true → ∀ {sig : Nat → Trace}, Run (ofBuckets e.1) sig →
      ∀ r ∈ e.2.1, ∀ s t, changes (sig e.2.2.1) s → changes (sig r) t → s ≤ t) ∧
    (∀ e ∈ RtFbGcdS4.fastE, rtOne e = false → ∃ r ∈ e.2.1, ∃ sig, Nonempty (FixedRun (ofBuckets e.1) sig) ∧
      ∃ s t, changes (sig e.2.2.1) s ∧ changes (sig r) t ∧ t < s) :=
  ⟨rt_sound_of _ gcd4_wf.2.1, rt_violated_of _ gcd4_wf.2.1 gcd4_sep1.2.2.1⟩

/-- gcd_hw seed 4, one-corner variant `slowE`: the 10 passing entries hold RT_FB in every run, the 0
failing entries each have a real violating fixed-delay run. -/
theorem gcd4_slowE_exact :
    (∀ e ∈ RtFbGcdS4.slowE, rtOne e = true → ∀ {sig : Nat → Trace}, Run (ofBuckets e.1) sig →
      ∀ r ∈ e.2.1, ∀ s t, changes (sig e.2.2.1) s → changes (sig r) t → s ≤ t) ∧
    (∀ e ∈ RtFbGcdS4.slowE, rtOne e = false → ∃ r ∈ e.2.1, ∃ sig, Nonempty (FixedRun (ofBuckets e.1) sig) ∧
      ∃ s t, changes (sig e.2.2.1) s ∧ changes (sig r) t ∧ t < s) :=
  ⟨rt_sound_of _ gcd4_wf.2.2, rt_violated_of _ gcd4_wf.2.2 gcd4_sep1.2.2.2⟩

/-- gcd_hw seed 4, H_ONE_CORNER + H_RC_EXACT (slowE): every C-element in the data satisfies RT_FB
in every run. -/
theorem gcd4_slowE_safe : ∀ e ∈ RtFbGcdS4.slowE, ∀ {sig : Nat → Trace}, Run (ofBuckets e.1) sig →
    ∀ r ∈ e.2.1, ∀ s t, changes (sig e.2.2.1) s → changes (sig r) t → s ≤ t := by
  have hall : RtFbGcdS4.slowE.all rtOne = true := by decide +kernel
  intro e he
  exact rt_sound_of _ gcd4_wf.2.2 e he (List.all_eq_true.1 hall e he)

/-- gcd_hw seed 4, H_ONE_CORNER + H_RC_EXACT (fastE): every C-element in the data satisfies RT_FB
in every run. -/
theorem gcd4_fastE_safe : ∀ e ∈ RtFbGcdS4.fastE, ∀ {sig : Nat → Trace}, Run (ofBuckets e.1) sig →
    ∀ r ∈ e.2.1, ∀ s t, changes (sig e.2.2.1) s → changes (sig r) t → s ≤ t := by
  have hall : RtFbGcdS4.fastE.all rtOne = true := by decide +kernel
  intro e he
  exact rt_sound_of _ gcd4_wf.2.1 e he (List.all_eq_true.1 hall e he)

/-- gcd_hw seed 4, H_INDEP: the 10 failing C-elements each have a real violating fixed-delay run. -/
theorem gcd4_indep_violated : ∀ e ∈ RtFbGcdS4.indep, rtOne e = false → ∃ r ∈ e.2.1, ∃ sig,
    Nonempty (FixedRun (ofBuckets e.1) sig) ∧ ∃ s t, changes (sig e.2.2.1) s ∧ changes (sig r) t ∧ t < s :=
  rt_violated_of _ gcd4_wf.1 gcd4_sep

end Formal.Timing.RtFb
