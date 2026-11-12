import Formal.Core.EnvFast.Kernel
import Formal.Core.EnvFast.Tables
import Formal.Core.EnvFast.Models
import Formal.Core.EnvFast.MergeCert

/-!
# Formal.Core.EnvFast.Merge — bd_merge (control path) by the kernel checker

Model: `EnvFast.mergeModel` (see `Models.lean`). Results:
* `merge_sound`: with the cell's documented exclusivity obligation (`excl`) and
  the select-settling assumption (`selFast`, found by the checker), the control
  path is hazard-free and persistent, live, and never acknowledges an input
  whose token it did not carry (`mergeQ`). 33 states.
* `merge_needs_excl_token`, `merge_needs_excl_hazard`: without `excl` the
  checker finds (i) `y_ack` rising for x's token, and (ii) a static-1 MIC on
  the request OR (`x_req↑ ∥ y_req↓`, a glitch on `z_req`) — the header's
  "exclusivity is not enough" warning, derived.
* `merge_needs_selFast`: without `selFast`, `sel`'s excitation is withdrawn.
* `merge_free_rejected`: negative control of the fast checker itself: on the
  reachable set of the model without `excl` it returns `false`.
-/

namespace Formal.Core.EnvFast

open Formal.Core.LutCells Formal.Core.Env Formal.Core.EnvFast.Tables Formal.Core.EnvFast.Certs

set_option Elab.async false

def mergeCG : List CGate :=
  [.lut 2 bd_merge_uor .O [1, 0] tt_bd_merge_uor_O hz_bd_merge_uor_O, .wire 3 2,
   .lut 5 bd_c2_u .O [8, 5, 4, 0] tt_bd_c2_u_O hz_bd_c2_u_O,
   .lut 6 bd_c2_u .O [8, 6, 4, 1] tt_bd_c2_u_O hz_bd_c2_u_O,
   .lut 7 bd_merge_usel .O [5, 0] tt_bd_merge_usel_O hz_bd_merge_usel_O]

theorem merge_compiled (A : MergeAsm) : Compiled (mergeModel A) mergeCG where
  gates := rfl
  valid := by
    simp only [mergeCG, List.all_cons, List.all_nil, CGate.valid, List.length_cons,
      List.length_nil, Nat.reduceAdd, tt_bd_merge_uor_O_ok, hz_bd_merge_uor_O_ok,
      tt_bd_c2_u_O_ok, hz_bd_c2_u_O_ok, tt_bd_merge_usel_O_ok, hz_bd_merge_usel_O_ok,
      Bool.and_self]

def mergeC (A : MergeAsm) : CModel where
  n := 9
  settle := true
  gates := mergeCG
  env := [(0, fun s => keq (kb s 0) (kb s 5) && (kb s 0 || !A.excl || (!kb s 1 && !kb s 6))),
          (1, fun s => keq (kb s 1) (kb s 6) && (kb s 1 || !A.excl || (!kb s 0 && !kb s 5))),
          (4, fun s => kne (kb s 4) (kb s 3))]
  prio := (mergeModel A).prio

theorem merge_kc (A : MergeAsm) : KCompiled (mergeModel A) (mergeC A) where
  n := rfl
  settle := rfl
  comp := merge_compiled A
  prio := rfl
  env := .cons rfl (fun s => by simp [kb_eq, keq_eq]) <|
    .cons rfl (fun s => by simp [kb_eq, keq_eq]) <|
    .cons rfl (fun s => by simp [kb_eq, kne_eq]) .nil

/-- Kernel form of `mergeQ`. -/
noncomputable def kmergeQ (C : CModel) (s : Nat) : Bool :=
  let x := kexc C s
  klive C s && !(kb x 6 && !kb s 6 && (kb s 0 || kb s 5)) && !(kb x 5 && !kb s 5 && (kb s 1 || kb s 6))

theorem kmergeQ_eq (A : MergeAsm) (s : Nat) :
    kmergeQ (mergeC A) s = mergeQ (mergeModel A) s := by
  simp only [kmergeQ, mergeQ, klive_eq (merge_kc A), kexc_eq (merge_kc A), kb_eq]

abbrev CM := mergeC ⟨true, true⟩

theorem merge_init : kinit (mergeModel ⟨true, true⟩) (kmkTree merge_excl.flatten) = true := by
  decide +kernel
theorem merge_c0 : kchunk CM (kmergeQ CM) (kmkTree merge_excl.flatten) merge_excl_0 = true := by
  decide +kernel

/-- **bd_merge's control path** (request OR, delay line as one unbounded wire,
two acknowledge C-elements, select OR), under the exclusivity obligation and
`selFast`: hazard-free, persistent, live, and no acknowledge for a token the
merge did not carry. -/
theorem merge_sound : Sound (mergeModel ⟨true, true⟩) (mergeQ (mergeModel ⟨true, true⟩)) :=
  kcheck_Sound (merge_kc _) (kmergeQ_eq _) merge_init (by
    intro c hc
    simp only [merge_excl, List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc; exact merge_c0)

/-- **Exclusivity is necessary (token)**: after `x_req↑, y_req↑, either↑,
z_req↑, z_ack↑`, `y_ack` is excited although z carried x's token. -/
theorem merge_needs_excl_token :
    ¬ Sound (mergeModel ⟨false, true⟩) (mergeQ (mergeModel ⟨false, true⟩)) := by
  intro hS
  obtain ⟨s, hs, _, hb⟩ := witness_sound (M := mergeModel ⟨false, true⟩) (s0 := 0)
    (ts := [0, 1, 2, 3, 4]) (t := 7) (bad := fun s _ => !mergeQ (mergeModel ⟨false, true⟩) s)
    (by decide) (by decide +kernel)
  have := (hS s hs).1
  simp [this] at hb

/-- **Exclusivity is necessary (hazard)**: after `y_req↑, either↑, z_req↑,
z_ack↑, y_ack↑, x_req↑`, y withdraws its request while x's rise is still in
flight at the request OR: a static-1 MIC `(x_req↑ ∥ y_req↓)` on `either`, i.e.
a possible glitch on `z_req`. -/
theorem merge_needs_excl_hazard :
    ∃ s, Reach (mergeModel ⟨false, true⟩) s ∧
      (1, post (mergeModel ⟨false, true⟩) s 1) ∈ succs (mergeModel ⟨false, true⟩) s ∧
      (!lutOK (mergeModel ⟨false, true⟩) s 1 (.lut 2 bd_merge_uor .O [1, 0]) 0) = true :=
  witness_sound (M := mergeModel ⟨false, true⟩) (s0 := 0) (ts := [1, 2, 3, 4, 6, 0]) (t := 1)
    (bad := fun s t => !lutOK (mergeModel ⟨false, true⟩) s t (.lut 2 bd_merge_uor .O [1, 0]) 0)
    (by decide) (by decide +kernel)

/-- **selFast is necessary**: a whole x transaction (`x_req↑ either↑ z_req↑
z_ack↑ x_ack↑ x_req↓ either↓ z_req↓ z_ack↓`) completes before `sel` follows
`x_ack↑`; then `x_ack↓` withdraws `sel`'s excitation (a runt on the mux
select, while the data were being steered by it). -/
theorem merge_needs_selFast : ¬ Sound (mergeModel ⟨true, false⟩) (live (mergeModel ⟨true, false⟩)) :=
  not_sound_of_witness (s0 := 0) (ts := [0, 2, 3, 4, 5, 0, 2, 3, 4]) (t := 5) (by decide) (by decide +kernel)

/-- Negative control of the fast checker: it rejects the reachable set of the
model without `excl`. -/
theorem merge_free_rejected :
    (kinit (mergeModel ⟨false, true⟩) (kmkTree merge_free.flatten) &&
      kall (kchunk (mergeC ⟨false, true⟩) (kmergeQ (mergeC ⟨false, true⟩)) (kmkTree merge_free.flatten))
        merge_free) = false := by
  decide +kernel

end Formal.Core.EnvFast
