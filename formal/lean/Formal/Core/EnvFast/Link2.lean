import Formal.Core.EnvFast.Kernel
import Formal.Core.EnvFast.Tables
import Formal.Core.EnvFast.Models
import Formal.Core.EnvFast.Link2Cert

/-!
# Formal.Core.EnvFast.Link2 — bd_link with a W = 2 latch pair, by the kernel checker

`link2_sound` is the conjecture `Formal.Core.Env.Wip.link2_sound`
(`formal/lean/Wip/Env.lean`), now proved, for the copy `EnvFast.link2Model` of
that model (identical definition; `Wip/Env.lean` is not built so cannot be
imported). `link1_sound` re-proves `Env.link_sound` with the new checker, as a
cross-check of the two checkers on the same model.
-/

namespace Formal.Core.EnvFast

open Formal.Core.LutCells Formal.Core.Env Formal.Core.EnvFast.Tables Formal.Core.EnvFast.Certs

set_option Elab.async false

/-! ### Compiled models -/

def link1CG : List CGate :=
  [.lut 1 bd_c2n_u .O [7, 1, 2, 0] tt_bd_c2n_u_O hz_bd_c2n_u_O, .wire 3 1,
   .lut 5 bd_latch_u_L44 .O [5, 3, 4] tt_bd_latch_u_L44_O hz_bd_latch_u_L44_O]

theorem link1_compiled (A : LinkAsm) : Compiled (linkModel A) link1CG where
  gates := rfl
  valid := by
    simp only [link1CG, List.all_cons, List.all_nil, CGate.valid, List.length_cons,
      List.length_nil, Nat.reduceAdd, tt_bd_c2n_u_O_ok, hz_bd_c2n_u_O_ok,
      tt_bd_latch_u_L44_O_ok, hz_bd_latch_u_L44_O_ok, Bool.and_self]

/-- `Env.linkModel`'s environment with `kb` for `bit`. -/
def link1C (A : LinkAsm) : CModel where
  n := 8
  settle := true
  gates := link1CG
  env := [(4, fun s => !kb s 6 && !kb s 0 && !kb s 1),
          (6, fun s => (!kb s 6 && !kb s 0 && !kb s 1) || (kb s 6 && kb s 0)),
          (0, fun s => (!kb s 0 && kb s 6 && !kb s 1) || (kb s 0 && kb s 1)),
          (2, fun s => kne (kb s 2) (kb s 1))]
  prio := (linkModel A).prio

theorem link1_kc (A : LinkAsm) : KCompiled (linkModel A) (link1C A) where
  n := rfl
  settle := rfl
  comp := link1_compiled A
  prio := rfl
  env := .cons rfl (fun s => by simp [kb_eq]) <| .cons rfl (fun s => by simp [kb_eq]) <|
    .cons rfl (fun s => by simp [kb_eq]) <| .cons rfl (fun s => by simp [kb_eq, kne_eq]) .nil

def link2CG : List CGate :=
  [.lut 1 bd_c2n_u .O [9, 1, 2, 0] tt_bd_c2n_u_O hz_bd_c2n_u_O, .wire 3 1,
   .lut 6 bd_latch_u_L38 .O5 [7, 5, 6, 3, 4] tt_bd_latch_u_L38_O5 hz_bd_latch_u_L38_O5,
   .lut 7 bd_latch_u_L38 .O6 [7, 5, 6, 3, 4] tt_bd_latch_u_L38_O6 hz_bd_latch_u_L38_O6]

theorem link2_compiled (A : LinkAsm) : Compiled (link2Model A) link2CG where
  gates := rfl
  valid := by
    simp only [link2CG, List.all_cons, List.all_nil, CGate.valid, List.length_cons,
      List.length_nil, Nat.reduceAdd, tt_bd_c2n_u_O_ok, hz_bd_c2n_u_O_ok,
      tt_bd_latch_u_L38_O5_ok, hz_bd_latch_u_L38_O5_ok, tt_bd_latch_u_L38_O6_ok,
      hz_bd_latch_u_L38_O6_ok, Bool.and_self]

def link2C (A : LinkAsm) : CModel where
  n := 10
  settle := true
  gates := link2CG
  env := [(4, fun s => !kb s 8 && !kb s 0 && !kb s 1),
          (5, fun s => !kb s 8 && !kb s 0 && !kb s 1),
          (8, fun s => (!kb s 8 && !kb s 0 && !kb s 1) || (kb s 8 && kb s 0)),
          (0, fun s => (!kb s 0 && kb s 8 && !kb s 1) || (kb s 0 && kb s 1)),
          (2, fun s => kne (kb s 2) (kb s 1))]
  prio := (link2Model A).prio

theorem link2_kc (A : LinkAsm) : KCompiled (link2Model A) (link2C A) where
  n := rfl
  settle := rfl
  comp := link2_compiled A
  prio := rfl
  env := .cons rfl (fun s => by simp [kb_eq]) <| .cons rfl (fun s => by simp [kb_eq]) <|
    .cons rfl (fun s => by simp [kb_eq]) <| .cons rfl (fun s => by simp [kb_eq]) <|
    .cons rfl (fun s => by simp [kb_eq, kne_eq]) .nil

/-! ### W = 1 (cross-check of `Env.link_sound`) -/

abbrev C1 := link1C ⟨true, true, true, false⟩

theorem link1_init : kinit (linkModel ⟨true, true, true, false⟩) (kmkTree link1_HLI.flatten) = true := by
  decide +kernel
theorem link1_c0 : kchunk C1 (klive C1) (kmkTree link1_HLI.flatten) link1_HLI_0 = true := by decide +kernel
theorem link1_c1 : kchunk C1 (klive C1) (kmkTree link1_HLI.flatten) link1_HLI_1 = true := by decide +kernel

theorem link1_sound : Sound (linkModel ⟨true, true, true, false⟩) (live (linkModel ⟨true, true, true, false⟩)) :=
  kcheck_Sound (link1_kc _) (klive_eq (link1_kc _)) link1_init (by
    intro c hc
    simp only [link1_HLI, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact link1_c0
    · exact link1_c1)

/-! ### W = 2 -/

abbrev C2 := link2C ⟨true, true, true, false⟩

theorem link2_init : kinit (link2Model ⟨true, true, true, false⟩) (kmkTree link2_HLI.flatten) = true := by
  decide +kernel
theorem link2_c0 : kchunk C2 (klive C2) (kmkTree link2_HLI.flatten) link2_HLI_0 = true := by decide +kernel
theorem link2_c1 : kchunk C2 (klive C2) (kmkTree link2_HLI.flatten) link2_HLI_1 = true := by decide +kernel
theorem link2_c2 : kchunk C2 (klive C2) (kmkTree link2_HLI.flatten) link2_HLI_2 = true := by decide +kernel
theorem link2_c3 : kchunk C2 (klive C2) (kmkTree link2_HLI.flatten) link2_HLI_3 = true := by decide +kernel
theorem link2_c4 : kchunk C2 (klive C2) (kmkTree link2_HLI.flatten) link2_HLI_4 = true := by decide +kernel
theorem link2_c5 : kchunk C2 (klive C2) (kmkTree link2_HLI.flatten) link2_HLI_5 = true := by decide +kernel
theorem link2_c6 : kchunk C2 (klive C2) (kmkTree link2_HLI.flatten) link2_HLI_6 = true := by decide +kernel
theorem link2_c7 : kchunk C2 (klive C2) (kmkTree link2_HLI.flatten) link2_HLI_7 = true := by decide +kernel
theorem link2_c8 : kchunk C2 (klive C2) (kmkTree link2_HLI.flatten) link2_HLI_8 = true := by decide +kernel

/-- **bd_link with a W = 2 latch pair (LUT6_2, en fanning out to both outputs)
is hazard-free and persistent under rules H, L and the isochronic enable
branch**, against an arbitrary four-phase receiver; no deadlock. 1048 reachable
states. (The conjecture `Env.Wip.link2_sound`.) -/
theorem link2_sound : Sound (link2Model ⟨true, true, true, false⟩)
    (live (link2Model ⟨true, true, true, false⟩)) :=
  kcheck_Sound (link2_kc _) (klive_eq (link2_kc _)) link2_init (by
    intro c hc
    simp only [link2_HLI, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact link2_c0
    · exact link2_c1
    · exact link2_c2
    · exact link2_c3
    · exact link2_c4
    · exact link2_c5
    · exact link2_c6
    · exact link2_c7
    · exact link2_c8)

/-- The reachable set is exactly 1048 states in the certificate; every reachable
state is one of them. -/
theorem link2_reach_in_cert : ∀ s, Reach (link2Model ⟨true, true, true, false⟩) s → s ∈ link2_HLI.flatten :=
  fun s hs => (kcheck_sound (link2_kc _) (klive_eq (link2_kc _)) link2_init (by
    intro c hc
    simp only [link2_HLI, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact link2_c0
    · exact link2_c1
    · exact link2_c2
    · exact link2_c3
    · exact link2_c4
    · exact link2_c5
    · exact link2_c6
    · exact link2_c7
    · exact link2_c8) s hs).1

/-! ### W = 2 with receiver bundling: data validity -/

/-- Kernel form of `link2Q`. -/
noncomputable def klink2Q (C : CModel) (s : Nat) : Bool :=
  let x := kexc C s
  klive C s &&
    (!(kb (kenOf C x) 2 && !kb s 2) ||
      (keq (kb s 6) (kb s 4) && keq (kb s 7) (kb s 5) && !kb x 6 && !kb x 7))

theorem klink2Q_eq (A : LinkAsm) (s : Nat) : klink2Q (link2C A) s = link2Q (link2Model A) s := by
  simp only [klink2Q, link2Q, link2Data, klive_eq (link2_kc A), kexc_eq (link2_kc A),
    kenOf_eq (link2_kc A), kb_eq, keq_eq, enMask_eq_enOf]

abbrev C2R := link2C ⟨true, true, true, true⟩

theorem link2R_init : kinit (link2Model ⟨true, true, true, true⟩) (kmkTree link2_HLIR.flatten) = true := by
  decide +kernel
theorem link2R_c0 : kchunk C2R (klink2Q C2R) (kmkTree link2_HLIR.flatten) link2_HLIR_0 = true := by decide +kernel
theorem link2R_c1 : kchunk C2R (klink2Q C2R) (kmkTree link2_HLIR.flatten) link2_HLIR_1 = true := by decide +kernel
theorem link2R_c2 : kchunk C2R (klink2Q C2R) (kmkTree link2_HLIR.flatten) link2_HLIR_2 = true := by decide +kernel
theorem link2R_c3 : kchunk C2R (klink2Q C2R) (kmkTree link2_HLIR.flatten) link2_HLIR_3 = true := by decide +kernel
theorem link2R_c4 : kchunk C2R (klink2Q C2R) (kmkTree link2_HLIR.flatten) link2_HLIR_4 = true := by decide +kernel
theorem link2R_c5 : kchunk C2R (klink2Q C2R) (kmkTree link2_HLIR.flatten) link2_HLIR_5 = true := by decide +kernel

/-- **bd_link W = 2 with receiver bundling (`rxBundle`: both latch outputs settle
before the receiver acknowledges): the receiver always acknowledges the sender's
two bits** (data validity), on top of hazard freedom, persistence and liveness.
752 states. (W = 2 analogue of `Env.link_data_sound`.) -/
theorem link2_data_sound : Sound (link2Model ⟨true, true, true, true⟩)
    (link2Q (link2Model ⟨true, true, true, true⟩)) :=
  kcheck_Sound (link2_kc _) (klink2Q_eq _) link2R_init (by
    intro c hc
    simp only [link2_HLIR, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    · exact link2R_c0
    · exact link2R_c1
    · exact link2R_c2
    · exact link2R_c3
    · exact link2R_c4
    · exact link2R_c5)

/-- Negative control of the checker: the certificate with one reachable state
removed (index 479 of the flattened list, a successor of the first state of
chunk 0) is rejected. -/
def link2_cut : List (List Nat) :=
  [link2_HLI_0, link2_HLI_1, link2_HLI_2, link2_HLI_3.eraseIdx 95, link2_HLI_4, link2_HLI_5,
   link2_HLI_6, link2_HLI_7, link2_HLI_8]

theorem link2_cut_rejected :
    (kinit (link2Model ⟨true, true, true, false⟩) (kmkTree link2_cut.flatten) &&
      kall (kchunk C2 (klive C2) (kmkTree link2_cut.flatten)) link2_cut) = false := by
  decide +kernel

end Formal.Core.EnvFast
