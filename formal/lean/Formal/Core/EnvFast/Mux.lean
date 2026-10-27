import Formal.Core.EnvFast.MuxCompiled
import Formal.Core.EnvFast.MuxCert

/-!
# Formal.Core.EnvFast.Mux — bd_mux (control path) by the kernel checker

Models: `MuxModels.lean` (`muxModel`, `muxZaModel`, `muxCrModel`). Shard A.
Notes: `formal/notes/A-envfast-2.md`. Results (all `Env.Sound`, i.e. every LUT
sees a hazard-free MIC on every reachable transition, every excited element
stays excited, plus `muxQ`: only the selected input is acknowledged, the
receiver acknowledges only a token the control selected, no deadlock):

* `mux_sound` (436 states): every fork isochronic, under `rtz`.
* `muxZa_sound` (3832 states): the three branches of `z_ack` as separate
  delayed wires, under `rtz`, `zaSettle`, `zaIso`.
* `muxCr_sound` (911 states): the `ctl_req` branch at `uj1` as a delayed wire,
  under `rtz`, `crSettle`, `sHold`.
* Each assumption is necessary: `mux_needs_rtz`, `muxZa_needs_settle`,
  `muxZa_needs_iso`, `muxCr_needs_settle`, `muxCr_needs_hold` (explicit
  reachable witness traces, replayed by the kernel).
-/

namespace Formal.Core.EnvFast

open Formal.Core.LutCells Formal.Core.Env Formal.Core.EnvFast.Tables Formal.Core.EnvFast.Certs

set_option Elab.async false
-- `kmkTree` over a few thousand states nests that many `kinsert` thunks in the kernel.
set_option maxRecDepth 100000

/-! ## Every fork isochronic -/

abbrev CR := muxC ⟨true⟩

theorem muxR_init : kinit (muxModel ⟨true⟩) (kmkTree mux_R.flatten) = true := by decide +kernel
theorem muxR_c0 : kchunk CR (kmuxQ CR) (kmkTree mux_R.flatten) mux_R_0 = true := by decide +kernel
theorem muxR_c1 : kchunk CR (kmuxQ CR) (kmkTree mux_R.flatten) mux_R_1 = true := by decide +kernel
theorem muxR_c2 : kchunk CR (kmuxQ CR) (kmkTree mux_R.flatten) mux_R_2 = true := by decide +kernel
theorem muxR_c3 : kchunk CR (kmuxQ CR) (kmkTree mux_R.flatten) mux_R_3 = true := by decide +kernel

/-- **bd_mux, control path, every fork isochronic, under `rtz`**: hazard-free
(both joins, the request OR, both acknowledge C-elements, on every reachable
MIC), persistent, live; only the selected input is acknowledged and the
receiver acknowledges only the control's choice. 436 states. -/
theorem mux_sound : Sound (muxModel ⟨true⟩) (muxQ (muxModel ⟨true⟩)) :=
  kcheck_Sound (mux_kc _) (kmuxQ_eq (mux_kc _)) muxR_init (by
    intro c hc
    simp only [mux_R, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact muxR_c0
    · exact muxR_c1
    · exact muxR_c2
    · exact muxR_c3)

/-- **`rtz` is necessary (not in the RTL header).** x and y both request; the
control selects x; x's transaction runs until `z_ack` falls, so `x_ack` is
excited to fall; a new control token selecting y lets `j1` fire on y's waiting
request, and the receiver raises `z_ack` again before `x_ack` has fallen: the
MIC `(j0 = 0, z_ack↑)` at `uxa` is a hazard and `x_ack`'s excitation is
withdrawn (a runt on `x_ack`, or an acknowledge that never returns to zero). -/
theorem mux_needs_rtz : ¬ Sound (muxModel ⟨false⟩) (muxQ (muxModel ⟨false⟩)) :=
  not_sound_of_witness (s0 := 0) (ts := [0, 1, 12, 2, 4, 6, 7, 8, 9, 0, 12, 2, 4, 6, 7, 8, 3, 12, 2, 5, 6, 7])
    (t := 8) (by decide) (by decide +kernel)

/-! ## The `z_ack` fork -/

abbrev CZA := muxZaC ⟨true, true, true⟩

theorem muxZA_init : kinit (muxZaModel ⟨true, true, true⟩) (kmkTree mux_ZA.flatten) = true := by
  decide +kernel
theorem muxZA_c0 : kchunk CZA (kmuxQ CZA) (kmkTree mux_ZA.flatten) mux_ZA_0 = true := by decide +kernel
theorem muxZA_c1 : kchunk CZA (kmuxQ CZA) (kmkTree mux_ZA.flatten) mux_ZA_1 = true := by decide +kernel
theorem muxZA_c2 : kchunk CZA (kmuxQ CZA) (kmkTree mux_ZA.flatten) mux_ZA_2 = true := by decide +kernel
theorem muxZA_c3 : kchunk CZA (kmuxQ CZA) (kmkTree mux_ZA.flatten) mux_ZA_3 = true := by decide +kernel
theorem muxZA_c4 : kchunk CZA (kmuxQ CZA) (kmkTree mux_ZA.flatten) mux_ZA_4 = true := by decide +kernel
theorem muxZA_c5 : kchunk CZA (kmuxQ CZA) (kmkTree mux_ZA.flatten) mux_ZA_5 = true := by decide +kernel
theorem muxZA_c6 : kchunk CZA (kmuxQ CZA) (kmkTree mux_ZA.flatten) mux_ZA_6 = true := by decide +kernel
theorem muxZA_c7 : kchunk CZA (kmuxQ CZA) (kmkTree mux_ZA.flatten) mux_ZA_7 = true := by decide +kernel
theorem muxZA_c8 : kchunk CZA (kmuxQ CZA) (kmkTree mux_ZA.flatten) mux_ZA_8 = true := by decide +kernel
theorem muxZA_c9 : kchunk CZA (kmuxQ CZA) (kmkTree mux_ZA.flatten) mux_ZA_9 = true := by decide +kernel
theorem muxZA_c10 : kchunk CZA (kmuxQ CZA) (kmkTree mux_ZA.flatten) mux_ZA_10 = true := by decide +kernel
theorem muxZA_c11 : kchunk CZA (kmuxQ CZA) (kmkTree mux_ZA.flatten) mux_ZA_11 = true := by decide +kernel
theorem muxZA_c12 : kchunk CZA (kmuxQ CZA) (kmkTree mux_ZA.flatten) mux_ZA_12 = true := by decide +kernel
theorem muxZA_c13 : kchunk CZA (kmuxQ CZA) (kmkTree mux_ZA.flatten) mux_ZA_13 = true := by decide +kernel
theorem muxZA_c14 : kchunk CZA (kmuxQ CZA) (kmkTree mux_ZA.flatten) mux_ZA_14 = true := by decide +kernel
theorem muxZA_c15 : kchunk CZA (kmuxQ CZA) (kmkTree mux_ZA.flatten) mux_ZA_15 = true := by decide +kernel
theorem muxZA_c16 : kchunk CZA (kmuxQ CZA) (kmkTree mux_ZA.flatten) mux_ZA_16 = true := by decide +kernel
theorem muxZA_c17 : kchunk CZA (kmuxQ CZA) (kmkTree mux_ZA.flatten) mux_ZA_17 = true := by decide +kernel
theorem muxZA_c18 : kchunk CZA (kmuxQ CZA) (kmkTree mux_ZA.flatten) mux_ZA_18 = true := by decide +kernel
theorem muxZA_c19 : kchunk CZA (kmuxQ CZA) (kmkTree mux_ZA.flatten) mux_ZA_19 = true := by decide +kernel
theorem muxZA_c20 : kchunk CZA (kmuxQ CZA) (kmkTree mux_ZA.flatten) mux_ZA_20 = true := by decide +kernel
theorem muxZA_c21 : kchunk CZA (kmuxQ CZA) (kmkTree mux_ZA.flatten) mux_ZA_21 = true := by decide +kernel
theorem muxZA_c22 : kchunk CZA (kmuxQ CZA) (kmkTree mux_ZA.flatten) mux_ZA_22 = true := by decide +kernel
theorem muxZA_c23 : kchunk CZA (kmuxQ CZA) (kmkTree mux_ZA.flatten) mux_ZA_23 = true := by decide +kernel
theorem muxZA_c24 : kchunk CZA (kmuxQ CZA) (kmkTree mux_ZA.flatten) mux_ZA_24 = true := by decide +kernel
theorem muxZA_c25 : kchunk CZA (kmuxQ CZA) (kmkTree mux_ZA.flatten) mux_ZA_25 = true := by decide +kernel
theorem muxZA_c26 : kchunk CZA (kmuxQ CZA) (kmkTree mux_ZA.flatten) mux_ZA_26 = true := by decide +kernel
theorem muxZA_c27 : kchunk CZA (kmuxQ CZA) (kmkTree mux_ZA.flatten) mux_ZA_27 = true := by decide +kernel
theorem muxZA_c28 : kchunk CZA (kmuxQ CZA) (kmkTree mux_ZA.flatten) mux_ZA_28 = true := by decide +kernel
theorem muxZA_c29 : kchunk CZA (kmuxQ CZA) (kmkTree mux_ZA.flatten) mux_ZA_29 = true := by decide +kernel

/-- **bd_mux with the `z_ack` fork as three delayed branches** (at `uxa`, at
`uya`, and `ctl_ack` to the control sender): sound under `rtz`, `zaSettle`,
`zaIso`. 3832 states. -/
theorem muxZa_sound : Sound (muxZaModel ⟨true, true, true⟩) (muxQ (muxZaModel ⟨true, true, true⟩)) :=
  kcheck_Sound (muxZa_kc _) (kmuxQ_eq (muxZa_kc _)) muxZA_init (by
    intro c hc
    simp only [mux_ZA, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact muxZA_c0
    · exact muxZA_c1
    · exact muxZA_c2
    · exact muxZA_c3
    · exact muxZA_c4
    · exact muxZA_c5
    · exact muxZA_c6
    · exact muxZA_c7
    · exact muxZA_c8
    · exact muxZA_c9
    · exact muxZA_c10
    · exact muxZA_c11
    · exact muxZA_c12
    · exact muxZA_c13
    · exact muxZA_c14
    · exact muxZA_c15
    · exact muxZA_c16
    · exact muxZA_c17
    · exact muxZA_c18
    · exact muxZA_c19
    · exact muxZA_c20
    · exact muxZA_c21
    · exact muxZA_c22
    · exact muxZA_c23
    · exact muxZA_c24
    · exact muxZA_c25
    · exact muxZA_c26
    · exact muxZA_c27
    · exact muxZA_c28
    · exact muxZA_c29)

/-- **`zaSettle` is necessary**: `z_ack` rises and falls again before its branch
at `uya` has followed the rise; that branch's excitation is withdrawn (a runt
on the net into `uya`). -/
theorem muxZa_needs_settle :
    ¬ Sound (muxZaModel ⟨true, false, true⟩) (muxQ (muxZaModel ⟨true, false, true⟩)) :=
  not_sound_of_witness (s0 := 0) (ts := [0, 12, 2, 4, 6, 7, 8, 13, 9, 0, 15, 2, 4, 6, 7]) (t := 8)
    (by decide) (by decide +kernel)

/-- **`zaIso` is necessary**: the branch of `z_ack` at `uya` still holds the
fall of an x transaction when y's join fires for the next token: the MIC
`(z_ack@uya↓ ∥ j1↑)` at `uya` (a C-element with q = 0) is a static hazard, and
`y_ack`'s excitation is withdrawn — a spurious `y_ack` pulse. -/
theorem muxZa_needs_iso :
    ∃ s, Reach (muxZaModel ⟨true, true, false⟩) s ∧
      (14, post (muxZaModel ⟨true, true, false⟩) s 14) ∈ succs (muxZaModel ⟨true, true, false⟩) s ∧
      (!lutOK (muxZaModel ⟨true, true, false⟩) s 14 (.lut 10 bd_c2_u .O [11, 10, 14, 5]) 5 &&
        !persistOK (muxZaModel ⟨true, true, false⟩) s 14) = true :=
  witness_sound (M := muxZaModel ⟨true, true, false⟩) (s0 := 0)
    (ts := [0, 1, 12, 2, 4, 6, 7, 8, 12, 13, 9, 0, 14, 15, 2, 4, 6, 7, 8, 15, 3, 12, 2, 5]) (t := 14)
    (bad := fun s t => !lutOK (muxZaModel ⟨true, true, false⟩) s t (.lut 10 bd_c2_u .O [11, 10, 14, 5]) 5 &&
      !persistOK (muxZaModel ⟨true, true, false⟩) s t)
    (by decide) (by decide +kernel)

/-! ## The `ctl_req` branch at `uj1` -/

abbrev CCR := muxCrC ⟨true, true, true⟩

theorem muxCR_init : kinit (muxCrModel ⟨true, true, true⟩) (kmkTree mux_CR.flatten) = true := by
  decide +kernel
theorem muxCR_c0 : kchunk CCR (kmuxQ CCR) (kmkTree mux_CR.flatten) mux_CR_0 = true := by decide +kernel
theorem muxCR_c1 : kchunk CCR (kmuxQ CCR) (kmkTree mux_CR.flatten) mux_CR_1 = true := by decide +kernel
theorem muxCR_c2 : kchunk CCR (kmuxQ CCR) (kmkTree mux_CR.flatten) mux_CR_2 = true := by decide +kernel
theorem muxCR_c3 : kchunk CCR (kmuxQ CCR) (kmkTree mux_CR.flatten) mux_CR_3 = true := by decide +kernel
theorem muxCR_c4 : kchunk CCR (kmuxQ CCR) (kmkTree mux_CR.flatten) mux_CR_4 = true := by decide +kernel
theorem muxCR_c5 : kchunk CCR (kmuxQ CCR) (kmkTree mux_CR.flatten) mux_CR_5 = true := by decide +kernel
theorem muxCR_c6 : kchunk CCR (kmuxQ CCR) (kmkTree mux_CR.flatten) mux_CR_6 = true := by decide +kernel
theorem muxCR_c7 : kchunk CCR (kmuxQ CCR) (kmkTree mux_CR.flatten) mux_CR_7 = true := by decide +kernel

/-- **bd_mux with the `ctl_req` branch at `uj1` as a delayed wire**: sound
under `rtz`, `crSettle`, `sHold`. 911 states. -/
theorem muxCr_sound : Sound (muxCrModel ⟨true, true, true⟩) (muxQ (muxCrModel ⟨true, true, true⟩)) :=
  kcheck_Sound (muxCr_kc _) (kmuxQ_eq (muxCr_kc _)) muxCR_init (by
    intro c hc
    simp only [mux_CR, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact muxCR_c0
    · exact muxCR_c1
    · exact muxCR_c2
    · exact muxCR_c3
    · exact muxCR_c4
    · exact muxCR_c5
    · exact muxCR_c6
    · exact muxCR_c7)

/-- **`crSettle` is necessary**: the control sender sees `ctl_ack` and drops
`ctl_req` before its rise reached the deselected join: the branch's excitation
is withdrawn (a runt into `uj1`). -/
theorem muxCr_needs_settle :
    ¬ Sound (muxCrModel ⟨true, false, true⟩) (muxQ (muxCrModel ⟨true, false, true⟩)) :=
  not_sound_of_witness (s0 := 0) (ts := [0, 12, 2, 4, 6, 7, 8]) (t := 2) (by decide) (by decide +kernel)

/-- **`sHold` is necessary (hold of the select at the join pin)**: `ctl_req`'s
fall is still in flight inside `uj1` (y requesting) when the control sender,
having seen `ctl_ack` fall, moves `s` for the next token: the MIC
`(ctl_req@uj1↓ ∥ s↑)` at `uj1` crosses the vertex `ctl_req·s = 1`, a static-0
hazard on `j1` = a spurious join for y. -/
theorem muxCr_needs_hold :
    ∃ s, Reach (muxCrModel ⟨true, true, false⟩) s ∧
      (3, post (muxCrModel ⟨true, true, false⟩) s 3) ∈ succs (muxCrModel ⟨true, true, false⟩) s ∧
      (!lutOK (muxCrModel ⟨true, true, false⟩) s 3 (.lut 5 bd_mux_uj1 .O [11, 5, 3, 13, 1]) 1) = true :=
  witness_sound (M := muxCrModel ⟨true, true, false⟩) (s0 := 0)
    (ts := [0, 1, 12, 2, 4, 6, 7, 8, 9, 0, 12, 13, 2, 4, 6, 7, 8, 13]) (t := 3)
    (bad := fun s t => !lutOK (muxCrModel ⟨true, true, false⟩) s t (.lut 5 bd_mux_uj1 .O [11, 5, 3, 13, 1]) 1)
    (by decide) (by decide +kernel)

end Formal.Core.EnvFast
