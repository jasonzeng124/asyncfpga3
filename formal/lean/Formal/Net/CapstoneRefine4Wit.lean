import Formal.Net.CapstoneRefine4Fn
import Formal.Net.CapstoneRefine3FnWit

/-!
# Probe C-8x4: the SAMPLED branch of `CellP`, end to end, on a toy

`gcd_hw_phys5_witness` (C-8t's run) takes every output as a ghost: C-8t's run is zero-delay and
has no tcheck rows. Here the other branch (`Row`) is exercised on a two-channel network with one
fork stage `forkG 0 [1]`: channel 0 = C-8x3's input `wI`, channel 1 = C-8x3's slowed output `wQ`
(C-8x's netlist runs `wrun` as its tcheck obligation, DAG row `wcheck`).

* `toy_hs`: the fork's handshake half holds (`wQ.req` follows `wI.req`, `wI.ack` follows `wQ.ack`);
* `toy_row`: `Row` for channel 1 (tcheck row + H_TXWIN, H_FN, H_LAUNCH) holds;
* `toy_cellP`: so `CellP` holds with channel 1 SAMPLED;
* `toy_field` / `toy_cellB`: the fork's relaxed data field is DERIVED (`fieldOf_row`);
* `toy_old_fails`: while the OLD all-time fork field fails on the same run;
* `toy_rowG`: the bit-level form `RowG` (H_ZD_BITS + H_WIDTH instead of H_FN) also holds, and
  `fnOK kT` passes (a fork branch is a wire), so `row_of_rowG` re-derives the row.
-/

namespace Formal.Net.CapstoneRefine.Wit
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Timing Formal.Net.CapstoneRefine
open Formal.Net.CapNet Formal.Net.OpsBusy Formal.Net.OpsBusy3

/-- The toy network's channels. -/
def chT (c : Fin 2) : Chan := if c.val = 0 then wI else wQ

/-- The toy operator: a one-branch fork from channel 0 to channel 1. -/
def kT : K 2 := .forkG 0 [1]

def wT : Nat → Trace := fun _ _ => false

theorem chT0 : chT 0 = wI := rfl
theorem chT1 : chT 1 = wQ := rfl

theorem kT_disj : Disj kT := by decide

theorem toy_proto : ∀ c, Protocol (chT c) := by
  intro c
  match c with
  | ⟨0, _⟩ => exact wI_proto
  | ⟨1, _⟩ => exact wQ_proto

theorem toy_held : ∀ c, Held (chT c) := by
  intro c
  match c with
  | ⟨0, _⟩ => exact wI_held
  | ⟨1, _⟩ => exact held_of_bcert wQ_bcert wQ_proto.1 (fun t => (wQ_proto.2 t).2)

/-- **The fork's handshake half** on (`wI`, `wQ`). -/
theorem toy_hs (sv : Nat → Nat) : HS chT sv kT wT := by
  have J := wjoin_H
  have h1 : (1 : Fin 2) ∈ kT.outsC := by decide
  have h0 : (0 : Fin 2) ∉ kT.outsC := by decide
  refine ⟨by simp, ?_, ?_, ?_, ?_, ?_⟩
  · intro o ho t hne
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at ho
    subst ho
    exact (J.cel t hne wI (List.mem_singleton_self _)).symm
  · intro t hne o ho
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at ho
    subst ho
    exact (J.wire wI (List.mem_singleton_self _) t hne).symm
  · intro o ho t _
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at ho
    subst ho
    rw [modC_in h1, modC_out h0]; rfl
  · exact wI_proto.1.2
  · intro o ho
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at ho
    subst ho
    exact wQ_proto.1.1

/-- **The row of the sampled channel 1.** -/
theorem toy_row (sv : Nat → Nat) : Row chT sv kT wT 1 :=
  Row.mk wnet wnet_wf wsig [1] (fun k v => changes (wsig k 2) v) wrun wXQ
    (sep_dag wnet_wf wcheck wrun) (fun k _ => if bk k then 1 else 0) (fun _ => false)
    (fun k => by rw [w_fn]; rfl)
    (fun k r ho => by
      refine ⟨fun i hi => ?_, rfl⟩
      have hi0 : i = 0 := by simpa [kT, K.insC] using hi
      subst hi0
      have := w_launch k r ho
      simp only [wvin, List.map_cons, List.map_nil, List.cons.injEq, and_true] at this
      exact this)

/-- `CellP` with channel 1 SAMPLED. -/
theorem toy_cellP (sv : Nat → Nat) : CellP chT sv kT :=
  ⟨wT, toy_hs sv, fun c hc => by
    have : c = 1 := by simpa [kT, K.outsC] using hc
    subst this; exact Or.inr (toy_row sv)⟩

/-- **The fork's data field on the sampled channel, derived** from the row. -/
theorem toy_field (sv : Nat → Nat) : FieldOf chT sv kT wT 1 :=
  fieldOf_row kT_disj (toy_hs sv) toy_proto toy_held (by decide) (toy_row sv)

theorem toy_cellB (sv : Nat → Nat) : CellB chT sv kT :=
  cellB_of_cellP kT_disj (toy_cellP sv) toy_proto toy_held

/-- The OLD (all-time) fork field fails on this run: the relaxation is used. -/
theorem toy_old_fails : ¬ ∀ t, (chT 1).dat t = (chT 0).dat t := by
  intro h
  apply wjoin_old_fails
  intro t
  exact h t

/-- The bit-level row (`RowG`: H_ZD_BITS + H_WIDTH) of channel 1; `fnOK` passes for the fork. -/
theorem toy_rowG (sv : Nat → Nat) : RowG chT sv kT wT 1 :=
  RowG.mk wnet wnet_wf wsig [1] (fun k v => changes (wsig k 2) v) wrun wXQ
    (sep_dag wnet_wf wcheck wrun) (fun k _ => if bk k then 1 else 0) (fun _ => false)
    (fun m j hj => by
      have hj0 : j = 0 := by simp at hj; omega
      subst hj0
      have hz := w_zdBus m
      simp only [zdBus, bv, List.length_cons, List.length_nil, List.getD_cons_zero] at hz
      show some (zdEval wnet (wrun m).g (wsig m 0 1) 1) = some (bitN (if bk m then 1 else 0) 0)
      cases hb : bk m <;> cases hzz : zdEval wnet (wrun m).g (wsig m 0 1) 1 <;>
        simp_all [bitN])
    (fun m => by show (if bk m then 1 else 0) < 2 ^ 1; split <;> decide)
    (fun k r ho => by
      refine ⟨fun i hi => ?_, rfl⟩
      have hi0 : i = 0 := by simpa [kT, K.insC] using hi
      subst hi0
      have := w_launch k r ho
      simp only [wvin, List.map_cons, List.map_nil, List.cons.injEq, and_true] at this
      exact this)

theorem toy_fnOK : fnOK kT = true := rfl

theorem toy_row' (sv : Nat → Nat) : Row chT sv kT wT 1 := row_of_rowG toy_fnOK (toy_rowG sv)

end Formal.Net.CapstoneRefine.Wit
