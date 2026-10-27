import Formal.Core.EnvFast.MuxCompiled
import Formal.Core.EnvFast.Data
import Formal.Core.EnvFast.MuxDataCert

/-!
# Formal.Core.EnvFast.MuxData — bd_mux with its data mux, by the kernel checker

`MuxModels.muxDModel`: the control path of `muxModel` (every fork isochronic)
plus `bd_datamux`'s odd-bit LUT3 (`z = s ? y : x`), a data sender on x, and
`Data.SoundD` with the output window `z_req↑ … z_ack↓` (`muxDSpec`, `muxDQ`).
y's bit is held at 1 (`yMoves = false`; x's starts at 0, so a wrong selection
is visible). With both senders free the model has 27680 states; its
certificate is generated (`Gen2.lean`, `GEN_MUXD_FULL`) and passed the
explorer, but a kernel check costs about 26 s per 128-state chunk on this
machine, too much for the shared build (see notes). By the cell's x/y, s/¬s
symmetry the held-y model covers every single-sender behaviour of y.

* `muxD_sound` (4788 states): under `rtz` and `bundle` (the matched delay).
  The header's "converts a timing obligation into a data one" holds: no
  select-timing assumption is needed beyond the control channel's own
  contract (`s` held from `ctl_req↑` to `ctl_ack↓`), which is part of the
  environment.
* `muxD_needs_bundle`: without the matched delay the window opens while the
  data mux is still switching to x.
-/

namespace Formal.Core.EnvFast

open Formal.Core.LutCells Formal.Core.Env Formal.Core.EnvFast.Tables Formal.Core.EnvFast.Certs

set_option Elab.async false
-- `kmkTree` over a few thousand states nests that many `kinsert` thunks in the kernel.
set_option maxRecDepth 100000

abbrev CD := muxDC ⟨true, true, false⟩

theorem muxD_init : kinit (muxDModel ⟨true, true, false⟩) (kmkTree mux_D.flatten) = true := by
  decide +kernel
theorem muxD_c0 : kchunkD CD muxDSpecK (kmuxDQ CD) (kmkTree mux_D.flatten) mux_D_0 = true := by decide +kernel
theorem muxD_c1 : kchunkD CD muxDSpecK (kmuxDQ CD) (kmkTree mux_D.flatten) mux_D_1 = true := by decide +kernel
theorem muxD_c2 : kchunkD CD muxDSpecK (kmuxDQ CD) (kmkTree mux_D.flatten) mux_D_2 = true := by decide +kernel
theorem muxD_c3 : kchunkD CD muxDSpecK (kmuxDQ CD) (kmkTree mux_D.flatten) mux_D_3 = true := by decide +kernel
theorem muxD_c4 : kchunkD CD muxDSpecK (kmuxDQ CD) (kmkTree mux_D.flatten) mux_D_4 = true := by decide +kernel
theorem muxD_c5 : kchunkD CD muxDSpecK (kmuxDQ CD) (kmkTree mux_D.flatten) mux_D_5 = true := by decide +kernel
theorem muxD_c6 : kchunkD CD muxDSpecK (kmuxDQ CD) (kmkTree mux_D.flatten) mux_D_6 = true := by decide +kernel
theorem muxD_c7 : kchunkD CD muxDSpecK (kmuxDQ CD) (kmkTree mux_D.flatten) mux_D_7 = true := by decide +kernel
theorem muxD_c8 : kchunkD CD muxDSpecK (kmuxDQ CD) (kmkTree mux_D.flatten) mux_D_8 = true := by decide +kernel
theorem muxD_c9 : kchunkD CD muxDSpecK (kmuxDQ CD) (kmkTree mux_D.flatten) mux_D_9 = true := by decide +kernel
theorem muxD_c10 : kchunkD CD muxDSpecK (kmuxDQ CD) (kmkTree mux_D.flatten) mux_D_10 = true := by decide +kernel
theorem muxD_c11 : kchunkD CD muxDSpecK (kmuxDQ CD) (kmkTree mux_D.flatten) mux_D_11 = true := by decide +kernel
theorem muxD_c12 : kchunkD CD muxDSpecK (kmuxDQ CD) (kmkTree mux_D.flatten) mux_D_12 = true := by decide +kernel
theorem muxD_c13 : kchunkD CD muxDSpecK (kmuxDQ CD) (kmkTree mux_D.flatten) mux_D_13 = true := by decide +kernel
theorem muxD_c14 : kchunkD CD muxDSpecK (kmuxDQ CD) (kmkTree mux_D.flatten) mux_D_14 = true := by decide +kernel
theorem muxD_c15 : kchunkD CD muxDSpecK (kmuxDQ CD) (kmkTree mux_D.flatten) mux_D_15 = true := by decide +kernel
theorem muxD_c16 : kchunkD CD muxDSpecK (kmuxDQ CD) (kmkTree mux_D.flatten) mux_D_16 = true := by decide +kernel
theorem muxD_c17 : kchunkD CD muxDSpecK (kmuxDQ CD) (kmkTree mux_D.flatten) mux_D_17 = true := by decide +kernel
theorem muxD_c18 : kchunkD CD muxDSpecK (kmuxDQ CD) (kmkTree mux_D.flatten) mux_D_18 = true := by decide +kernel
theorem muxD_c19 : kchunkD CD muxDSpecK (kmuxDQ CD) (kmkTree mux_D.flatten) mux_D_19 = true := by decide +kernel
theorem muxD_c20 : kchunkD CD muxDSpecK (kmuxDQ CD) (kmkTree mux_D.flatten) mux_D_20 = true := by decide +kernel
theorem muxD_c21 : kchunkD CD muxDSpecK (kmuxDQ CD) (kmkTree mux_D.flatten) mux_D_21 = true := by decide +kernel
theorem muxD_c22 : kchunkD CD muxDSpecK (kmuxDQ CD) (kmkTree mux_D.flatten) mux_D_22 = true := by decide +kernel
theorem muxD_c23 : kchunkD CD muxDSpecK (kmuxDQ CD) (kmkTree mux_D.flatten) mux_D_23 = true := by decide +kernel
theorem muxD_c24 : kchunkD CD muxDSpecK (kmuxDQ CD) (kmkTree mux_D.flatten) mux_D_24 = true := by decide +kernel
theorem muxD_c25 : kchunkD CD muxDSpecK (kmuxDQ CD) (kmkTree mux_D.flatten) mux_D_25 = true := by decide +kernel
theorem muxD_c26 : kchunkD CD muxDSpecK (kmuxDQ CD) (kmkTree mux_D.flatten) mux_D_26 = true := by decide +kernel
theorem muxD_c27 : kchunkD CD muxDSpecK (kmuxDQ CD) (kmkTree mux_D.flatten) mux_D_27 = true := by decide +kernel
theorem muxD_c28 : kchunkD CD muxDSpecK (kmuxDQ CD) (kmkTree mux_D.flatten) mux_D_28 = true := by decide +kernel
theorem muxD_c29 : kchunkD CD muxDSpecK (kmuxDQ CD) (kmkTree mux_D.flatten) mux_D_29 = true := by decide +kernel
theorem muxD_c30 : kchunkD CD muxDSpecK (kmuxDQ CD) (kmkTree mux_D.flatten) mux_D_30 = true := by decide +kernel
theorem muxD_c31 : kchunkD CD muxDSpecK (kmuxDQ CD) (kmkTree mux_D.flatten) mux_D_31 = true := by decide +kernel
theorem muxD_c32 : kchunkD CD muxDSpecK (kmuxDQ CD) (kmkTree mux_D.flatten) mux_D_32 = true := by decide +kernel
theorem muxD_c33 : kchunkD CD muxDSpecK (kmuxDQ CD) (kmkTree mux_D.flatten) mux_D_33 = true := by decide +kernel
theorem muxD_c34 : kchunkD CD muxDSpecK (kmuxDQ CD) (kmkTree mux_D.flatten) mux_D_34 = true := by decide +kernel
theorem muxD_c35 : kchunkD CD muxDSpecK (kmuxDQ CD) (kmkTree mux_D.flatten) mux_D_35 = true := by decide +kernel
theorem muxD_c36 : kchunkD CD muxDSpecK (kmuxDQ CD) (kmkTree mux_D.flatten) mux_D_36 = true := by decide +kernel
theorem muxD_c37 : kchunkD CD muxDSpecK (kmuxDQ CD) (kmkTree mux_D.flatten) mux_D_37 = true := by decide +kernel

/-- **bd_mux with its data mux (W = 1)** under `rtz` and the matched delay:
the control path is hazard-free, persistent and live with only the selected
input acknowledged (`muxQ`), and throughout the output window `z_data` is
stable (not excited, no hazardous MIC at the data mux) and equals the selected
input's bit. 4788 states. -/
theorem muxD_sound : SoundD (muxDModel ⟨true, true, false⟩) muxDSpec
    (muxDQ (muxDModel ⟨true, true, false⟩)) :=
  kcheckD_SoundD (muxD_kc _) muxDSpec_agree (kmuxDQ_eq (muxD_kc _)) muxD_init (by
    intro c hc
    simp only [mux_D, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact muxD_c0
    · exact muxD_c1
    · exact muxD_c2
    · exact muxD_c3
    · exact muxD_c4
    · exact muxD_c5
    · exact muxD_c6
    · exact muxD_c7
    · exact muxD_c8
    · exact muxD_c9
    · exact muxD_c10
    · exact muxD_c11
    · exact muxD_c12
    · exact muxD_c13
    · exact muxD_c14
    · exact muxD_c15
    · exact muxD_c16
    · exact muxD_c17
    · exact muxD_c18
    · exact muxD_c19
    · exact muxD_c20
    · exact muxD_c21
    · exact muxD_c22
    · exact muxD_c23
    · exact muxD_c24
    · exact muxD_c25
    · exact muxD_c26
    · exact muxD_c27
    · exact muxD_c28
    · exact muxD_c29
    · exact muxD_c30
    · exact muxD_c31
    · exact muxD_c32
    · exact muxD_c33
    · exact muxD_c34
    · exact muxD_c35
    · exact muxD_c36
    · exact muxD_c37)

/-- **The matched delay is necessary**: the control selects x, x requests, and
`j0`, the request OR and the delay line fire while the data mux output is still
excited (it held y's 1, x's bit is 0): the window opens on the wrong value. -/
theorem muxD_needs_bundle :
    ¬ SoundD (muxDModel ⟨true, false, false⟩) muxDSpec (muxDQ (muxDModel ⟨true, false, false⟩)) :=
  not_soundD_of_witnessQ (s0 := 2 ^ 14 + 2 ^ 15) (ts := [12, 2, 16, 0, 4, 6, 7]) (t := 15)
    (by decide) (by decide +kernel)

/-- **`rtz` is still necessary with data** (`Mux.mux_needs_rtz`, here on the
data model): `x_ack`'s return to zero is overtaken by the next token's `z_ack↑`. -/
theorem muxD_needs_rtz :
    ¬ SoundD (muxDModel ⟨false, true, false⟩) muxDSpec (muxDQ (muxDModel ⟨false, true, false⟩)) :=
  not_soundD_of_witness (s0 := 2 ^ 14 + 2 ^ 15)
    (ts := [1, 12, 2, 12, 13, 16, 0, 4, 6, 7, 8, 2, 9, 0, 4, 6, 7, 8, 3, 12, 2, 5, 6, 7]) (t := 8)
    (by decide) (by decide +kernel)

end Formal.Core.EnvFast
