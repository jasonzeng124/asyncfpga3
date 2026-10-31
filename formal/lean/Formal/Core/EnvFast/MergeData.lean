import Formal.Core.EnvFast.MuxCompiled
import Formal.Core.EnvFast.Data
import Formal.Core.EnvFast.MergeDataCert

/-!
# Formal.Core.EnvFast.MergeData — bd_merge with its data mux, by the kernel checker

`Merge.lean` checked bd_merge's control path only. Here the select LUT `usel`
drives the cell's real data mux (`bd_datamux`, W = 1: the odd-bit LUT3,
`z = sel ? x : y`), the senders carry data, and the obligation is
`Data.SoundD` (`MuxModels.mergeDModel`, `mergeDSpec`, `mergeDQ`): every
CONTROL element (request OR, both acknowledge C-elements) is hazard-free and
persistent on every reachable transition exactly as in `Env.Sound`; the DATA
elements (`sel`, `z_data`) are held to the same checks whenever the output
window `z_req↑ … z_ack↓` is open, and inside the window `z_data` is not
excited and equals the live input's bit. Shard A; notes
`formal/notes/A-envfast-2.md`.

* `mergeD_sound` (2630 states): under `excl` and `bundle` (the matched delay)
  only. **`selFast`, which `Merge.merge_needs_selFast` shows necessary when
  `sel` is checked as a control signal, is NOT needed**: its two violations
  (a runt on `sel`, a static-1 MIC on `usel`) both happen with the window
  closed, where `sel` only steers data nobody samples.
* `mergeD_needs_bundle`: without the matched delay, `z_req` rises while `sel`
  has not yet followed `x_req`, and the window opens on y's data.
* `mergeD_needs_excl`: without exclusivity, y's token is acknowledged for x
  (the header's obligation), now with data.
-/

namespace Formal.Core.EnvFast

open Formal.Core.LutCells Formal.Core.Env Formal.Core.EnvFast.Tables Formal.Core.EnvFast.Certs

set_option Elab.async false
-- `kmkTree` over a few thousand states nests that many `kinsert` thunks in the kernel.
set_option maxRecDepth 100000

theorem mD1N_init : kinit (mergeDModel 1 ⟨true, false, true⟩) (kmkTree mergeD1_N.flatten) = true := by
  decide +kernel
theorem mD1N_c0 : kchunkD (CM1 ⟨true, false, true⟩) mergeDSpecK (kmergeDQ 1 (CM1 ⟨true, false, true⟩)) (kmkTree mergeD1_N.flatten) mergeD1_N_0 = true := by decide +kernel
theorem mD1N_c1 : kchunkD (CM1 ⟨true, false, true⟩) mergeDSpecK (kmergeDQ 1 (CM1 ⟨true, false, true⟩)) (kmkTree mergeD1_N.flatten) mergeD1_N_1 = true := by decide +kernel
theorem mD1N_c2 : kchunkD (CM1 ⟨true, false, true⟩) mergeDSpecK (kmergeDQ 1 (CM1 ⟨true, false, true⟩)) (kmkTree mergeD1_N.flatten) mergeD1_N_2 = true := by decide +kernel
theorem mD1N_c3 : kchunkD (CM1 ⟨true, false, true⟩) mergeDSpecK (kmergeDQ 1 (CM1 ⟨true, false, true⟩)) (kmkTree mergeD1_N.flatten) mergeD1_N_3 = true := by decide +kernel
theorem mD1N_c4 : kchunkD (CM1 ⟨true, false, true⟩) mergeDSpecK (kmergeDQ 1 (CM1 ⟨true, false, true⟩)) (kmkTree mergeD1_N.flatten) mergeD1_N_4 = true := by decide +kernel
theorem mD1N_c5 : kchunkD (CM1 ⟨true, false, true⟩) mergeDSpecK (kmergeDQ 1 (CM1 ⟨true, false, true⟩)) (kmkTree mergeD1_N.flatten) mergeD1_N_5 = true := by decide +kernel
theorem mD1N_c6 : kchunkD (CM1 ⟨true, false, true⟩) mergeDSpecK (kmergeDQ 1 (CM1 ⟨true, false, true⟩)) (kmkTree mergeD1_N.flatten) mergeD1_N_6 = true := by decide +kernel
theorem mD1N_c7 : kchunkD (CM1 ⟨true, false, true⟩) mergeDSpecK (kmergeDQ 1 (CM1 ⟨true, false, true⟩)) (kmkTree mergeD1_N.flatten) mergeD1_N_7 = true := by decide +kernel
theorem mD1N_c8 : kchunkD (CM1 ⟨true, false, true⟩) mergeDSpecK (kmergeDQ 1 (CM1 ⟨true, false, true⟩)) (kmkTree mergeD1_N.flatten) mergeD1_N_8 = true := by decide +kernel
theorem mD1N_c9 : kchunkD (CM1 ⟨true, false, true⟩) mergeDSpecK (kmergeDQ 1 (CM1 ⟨true, false, true⟩)) (kmkTree mergeD1_N.flatten) mergeD1_N_9 = true := by decide +kernel
theorem mD1N_c10 : kchunkD (CM1 ⟨true, false, true⟩) mergeDSpecK (kmergeDQ 1 (CM1 ⟨true, false, true⟩)) (kmkTree mergeD1_N.flatten) mergeD1_N_10 = true := by decide +kernel
theorem mD1N_c11 : kchunkD (CM1 ⟨true, false, true⟩) mergeDSpecK (kmergeDQ 1 (CM1 ⟨true, false, true⟩)) (kmkTree mergeD1_N.flatten) mergeD1_N_11 = true := by decide +kernel
theorem mD1N_c12 : kchunkD (CM1 ⟨true, false, true⟩) mergeDSpecK (kmergeDQ 1 (CM1 ⟨true, false, true⟩)) (kmkTree mergeD1_N.flatten) mergeD1_N_12 = true := by decide +kernel
theorem mD1N_c13 : kchunkD (CM1 ⟨true, false, true⟩) mergeDSpecK (kmergeDQ 1 (CM1 ⟨true, false, true⟩)) (kmkTree mergeD1_N.flatten) mergeD1_N_13 = true := by decide +kernel
theorem mD1N_c14 : kchunkD (CM1 ⟨true, false, true⟩) mergeDSpecK (kmergeDQ 1 (CM1 ⟨true, false, true⟩)) (kmkTree mergeD1_N.flatten) mergeD1_N_14 = true := by decide +kernel
theorem mD1N_c15 : kchunkD (CM1 ⟨true, false, true⟩) mergeDSpecK (kmergeDQ 1 (CM1 ⟨true, false, true⟩)) (kmkTree mergeD1_N.flatten) mergeD1_N_15 = true := by decide +kernel
theorem mD1N_c16 : kchunkD (CM1 ⟨true, false, true⟩) mergeDSpecK (kmergeDQ 1 (CM1 ⟨true, false, true⟩)) (kmkTree mergeD1_N.flatten) mergeD1_N_16 = true := by decide +kernel
theorem mD1N_c17 : kchunkD (CM1 ⟨true, false, true⟩) mergeDSpecK (kmergeDQ 1 (CM1 ⟨true, false, true⟩)) (kmkTree mergeD1_N.flatten) mergeD1_N_17 = true := by decide +kernel
theorem mD1N_c18 : kchunkD (CM1 ⟨true, false, true⟩) mergeDSpecK (kmergeDQ 1 (CM1 ⟨true, false, true⟩)) (kmkTree mergeD1_N.flatten) mergeD1_N_18 = true := by decide +kernel
theorem mD1N_c19 : kchunkD (CM1 ⟨true, false, true⟩) mergeDSpecK (kmergeDQ 1 (CM1 ⟨true, false, true⟩)) (kmkTree mergeD1_N.flatten) mergeD1_N_19 = true := by decide +kernel
theorem mD1N_c20 : kchunkD (CM1 ⟨true, false, true⟩) mergeDSpecK (kmergeDQ 1 (CM1 ⟨true, false, true⟩)) (kmkTree mergeD1_N.flatten) mergeD1_N_20 = true := by decide +kernel

/-- **bd_merge with its data mux (W = 1)**, under the cell's exclusivity
obligation and the matched delay only: control path hazard-free, persistent and
live; never acknowledges a token it did not carry; and throughout the output
window `z_data` is stable (not excited, no hazardous MIC) and equals the live
input's bit. 2630 states. -/
theorem mergeD_sound : SoundD (mergeDModel 1 ⟨true, false, true⟩) mergeDSpec
    (mergeDQ 1 (mergeDModel 1 ⟨true, false, true⟩)) :=
  kcheckD_SoundD (mergeD1_kc _) mergeDSpec_agree (kmergeDQ_eq (mergeD1_kc _) 1) mD1N_init (by
    intro c hc
    simp only [mergeD1_N, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact mD1N_c0
    · exact mD1N_c1
    · exact mD1N_c2
    · exact mD1N_c3
    · exact mD1N_c4
    · exact mD1N_c5
    · exact mD1N_c6
    · exact mD1N_c7
    · exact mD1N_c8
    · exact mD1N_c9
    · exact mD1N_c10
    · exact mD1N_c11
    · exact mD1N_c12
    · exact mD1N_c13
    · exact mD1N_c14
    · exact mD1N_c15
    · exact mD1N_c16
    · exact mD1N_c17
    · exact mD1N_c18
    · exact mD1N_c19
    · exact mD1N_c20)

/-- **The matched delay is necessary**: x requests, the request OR and the
delay line fire before `sel` has followed `x_req`, so the window opens with
the mux on y; y then loads new data and `z_data` moves inside the window. -/
theorem mergeD_needs_bundle :
    ¬ SoundD (mergeDModel 1 ⟨true, false, false⟩) mergeDSpec (mergeDQ 1 (mergeDModel 1 ⟨true, false, false⟩)) :=
  not_soundD_of_witnessQ (s0 := 0) (ts := [9, 0, 2, 3, 12]) (t := 7) (by decide) (by decide +kernel)

/-- **Exclusivity is necessary** (the header's obligation, with data): y's
transaction is in the window when x requests; `z_ack` rises and `x_ack` is
excited for a token the merge carried for y (and `sel` swings the data mux to
x inside the window). -/
theorem mergeD_needs_excl :
    ¬ SoundD (mergeDModel 1 ⟨false, false, true⟩) mergeDSpec (mergeDQ 1 (mergeDModel 1 ⟨false, false, true⟩)) :=
  not_soundD_of_witnessQ (s0 := 0) (ts := [9, 10, 1, 2, 3, 0, 4]) (t := 5) (by decide) (by decide +kernel)

end Formal.Core.EnvFast
