import Formal.Net.CapstoneRefine2
import Formal.Net.OpsBusy2Held
import Formal.Net.CapstoneRefine3Cert
import Formal.Net.CapstoneRefine2Strict

/-!
# Probe C-8x3: the physical gcd_hw capstone without H_SEND and H_RECV

C-8x2's `gcd_hw_circuit_safe_phys3` assumed the sender and receiver rules on every channel
(H_SEND, H_RECV) because the structural bundling closure (`held_struct`) needs the protocol and
the capstone derives the protocol from `Held` (`net_protocol`). Here both are derived together,
by one induction over time (`OpsBusy2.net_joint`):

* protocol at step `t` from `Held` on the steps `< t` (`OpsBusy2.cell_protoT_B`: the steer, mux and
  muxn read their select only before `t`);
* `Held` at step `t` from the protocol on the steps `≤ t`, by induction on a rank: structural
  producers (`OpsBusy2.cellB_heldT`, now including 5 arbiter stages, piece (b)) from their inputs
  at steps `≤ t`; roots from their tcheck certificate (`heldStep_of_bcert`, receiver rule `≤ t`).

* `rootIds3` (26 channels: 21 mux, the 3-input mux, 4 arbiter stages on cycles without a mux),
  `rankL3`, `struct3_chk` (kernel `decide`);
* **`gcd_hw_joint`**: H_CELLS_B + certificates on the 26 roots ⇒ protocol and `Held` everywhere;
* **`gcd_hw_circuit_safe_phys4`**: H_CELLS_B, H_START_ONCE, `BCert` on the 26 roots ⇒ every out0
  latch is `Nat.gcd a b`;
* `gcd_hw_phys4_witness`: C-8t's run meets all three hypotheses.
-/

namespace Formal.Net.CapNet.Gcd
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.OpsBusy
open Formal.Net.CapstoneRefine Formal.Net.OpsBusy2

set_option maxRecDepth 100000

/-- The 26 channels whose bundling is NOT structural once arbiter stages count as structural:
the 21 two-input muxes, the 3-input mux (out0), and the 4 arbiter stages (456, 458, 459, 461)
that lie on a cycle of structural producers. Produced by `Wip/C8x3/probe_amerge.py`. -/
def rootIds3 : List Nat := [84, 91, 99, 136, 142, 148, 158, 173, 181, 214, 229, 237, 321, 328, 336, 351, 365, 372, 379, 399, 405, 416, 456, 458, 459, 461]

def rankL3 : List Nat := [
  0, 0, 0, 1, 1, 1, 1, 2, 3, 4, 4, 4, 6, 7, 8, 6, 6, 6, 6, 6, 7, 7, 8, 9, 7, 7, 10, 11, 11, 11, 13, 14, 15, 13, 13, 13, 13, 13, 14, 14,
  15, 16, 14, 14, 15, 16, 14, 14, 15, 15, 15, 17, 18, 19, 20, 21, 21, 21, 21, 23, 24, 25, 23, 24, 25, 23, 24, 25, 23, 24, 25, 23, 24, 25, 23, 24, 25, 23, 23, 2,
  3, 10, 11, 12, 0, 1, 2, 3, 10, 11, 12, 0, 1, 2, 3, 4, 10, 11, 12, 0, 1, 1, 1, 10, 11, 12, 13, 2, 3, 3, 4, 2, 3, 3, 4, 2, 5, 6, 7, 8,
  8, 8, 8, 10, 11, 12, 10, 11, 12, 10, 11, 12, 10, 26, 27, 28, 0, 1, 2, 26, 27, 28, 0, 1, 2, 26, 27, 28, 0, 1, 2, 25, 25, 2, 3, 6, 7, 8, 0, 1,
  2, 1, 1, 2, 1, 2, 2, 3, 4, 6, 7, 8, 9, 0, 2, 3, 4, 6, 7, 8, 9, 0, 1, 1, 6, 7, 8, 9, 3, 4, 4, 4, 4, 4, 3, 6, 7, 8, 6, 6,
  7, 8, 6, 7, 8, 6, 6, 7, 7, 2, 3, 6, 7, 8, 0, 1, 2, 1, 1, 2, 1, 2, 2, 3, 4, 6, 7, 8, 9, 0, 2, 3, 4, 6, 7, 8, 9, 0, 1, 1,
  6, 7, 8, 9, 3, 4, 4, 4, 4, 4, 3, 6, 6, 6, 6, 6, 6, 7, 7, 8, 9, 7, 7, 10, 11, 11, 11, 11, 13, 14, 15, 13, 14, 15, 13, 14, 15, 13, 14, 15,
  13, 13, 13, 13, 14, 15, 6, 7, 7, 8, 6, 7, 7, 6, 7, 6, 7, 8, 9, 10, 10, 10, 10, 12, 13, 14, 12, 13, 6, 12, 13, 14, 12, 13, 12, 12, 12, 12, 13, 16,
  17, 0, 1, 2, 1, 2, 16, 17, 0, 1, 2, 1, 2, 16, 17, 18, 0, 1, 2, 15, 16, 17, 18, 15, 3, 4, 2, 3, 6, 7, 8, 0, 1, 2, 1, 1, 2, 1, 2, 2,
  3, 6, 7, 8, 9, 0, 2, 3, 6, 7, 8, 9, 0, 2, 3, 6, 7, 8, 9, 0, 1, 1, 6, 7, 8, 9, 3, 4, 4, 4, 4, 4, 4, 3, 6, 6, 16, 17, 18, 0,
  1, 2, 16, 17, 18, 0, 1, 2, 15, 15, 3, 4, 5, 17, 18, 19, 0, 17, 5, 5, 5, 12, 12, 12, 22, 22, 22, 22, 9, 9, 9, 9, 5, 5, 5, 5, 5, 5, 5, 5,
  5, 5, 12, 12, 12, 12, 11, 11, 11, 11, 5, 5, 5, 5, 5, 5, 0, 24, 0, 0, 14, 0, 14, 14, 16]

def isRoot3 (c : Fin NC) : Bool := rootIds3.contains c.val
def hrk3 (c : Fin NC) : Nat := rankL3.getD c.val 0

theorem struct3_all : (List.range NC).all (fun c => rootIds3.contains c ||
    (StructK2 (ops.getD (prodT.getD c 0).val (K.sink 0)) &&
      (ops.getD (prodT.getD c 0).val (K.sink 0)).insC.all
        (fun i => decide (rankL3.getD i.val 0 < rankL3.getD c 0)))) = true := by
  decide +kernel

theorem struct3_chk (c : Fin NC) (hr : isRoot3 c = false) :
    StructK2 (opAt (prodOf c)) = true ∧ ∀ i ∈ (opAt (prodOf c)).insC, hrk3 i < hrk3 c := by
  have h := List.all_eq_true.mp struct3_all c.val (List.mem_range.mpr c.isLt)
  simp only [isRoot3] at hr
  simp only [hr, Bool.false_or, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, fun i hi => h.2 i hi⟩

/-- **Protocol and bundling, jointly, from the relaxed cells and the 26 root certificates.** -/
theorem gcd_hw_joint (a b : Nat) (ch : Fin NC → Chan)
    (H_CELLS_B : ∀ o : Fin NO, CellB ch (srcV a b) (opAt o))
    (H_TCHECK_ROOT : ∀ c, isRoot3 c = true → BCert (ch c)) :
    (∀ c, Protocol (ch c)) ∧ (∀ c, Held (ch c)) := by
  refine net_joint net ch (fun o => cell_protoT_B ch (srcV a b) (opAt o) (H_CELLS_B o) (disj_ok o)) ?_
  intro t hinit hp hprev
  have key : ∀ m, ∀ c : Fin NC, hrk3 c = m → HeldStep (ch c) t := by
    intro m
    induction m using Nat.strongRecOn with
    | _ m ih =>
      intro c hm
      cases hr : isRoot3 c
      · obtain ⟨hs, hlt⟩ := struct3_chk c hr
        exact cellB_heldT ch (srcV a b) (opAt (prodOf c)) (H_CELLS_B _) hs t hinit hp
          (fun i hi s hs => by
            rcases Nat.lt_or_eq_of_le hs with h | h
            · exact hprev i s h
            · rw [h]; exact ih (hrk3 i) (by rw [← hm]; exact hlt i hi) i rfl)
          c (prod_mem c)
      · exact heldStep_of_bcert (H_TCHECK_ROOT c hr) (hinit c) (fun s hs => (hp c s hs).2)
  exact fun c => key _ c rfl

/-- **Physical gcd_hw safety: no protocol hypothesis.** The observed run `ch` (handshake wires
and observed buses) meets the relaxed gate models, `start` is offered at most once, and each of
the 26 root channels has a tcheck certificate (or an explicit `exempt`). Then every value out0
latches is `Nat.gcd a b`. -/
theorem gcd_hw_circuit_safe_phys4 (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31)
    (ch : Fin NC → Chan)
    (H_CELLS_B : ∀ o : Fin NO, CellB ch (srcV a b) (opAt o))
    (H_START_ONCE : ∀ t, Handshake.cnt (riseB (ch start).req) t ≤ 1)
    (H_TCHECK_ROOT : ∀ c, isRoot3 c = true → BCert (ch c)) :
    (∀ k e, TokAt (ch out0) k e → (ch out0).dat e = Nat.gcd a b) ∧
    (∀ t, closedVals (ch out0) t =
      List.replicate (Handshake.cnt (fallB (ch out0).ack) t) (Nat.gcd a b)) :=
  gcd_hw_circuit_safe3B a b ha hb ch H_CELLS_B (gcd_hw_joint a b ch H_CELLS_B H_TCHECK_ROOT).2
    H_START_ONCE

/-- The protocol is a CONCLUSION now: the sender and receiver rules of C-8x2's phys3 follow. -/
theorem gcd_hw_send_recv (a b : Nat) (ch : Fin NC → Chan)
    (H_CELLS_B : ∀ o : Fin NO, CellB ch (srcV a b) (opAt o))
    (H_TCHECK_ROOT : ∀ c, isRoot3 c = true → BCert (ch c)) :
    (∀ c t, SendStep (ch c) t) ∧ (∀ c t, RecvStep (ch c) t) :=
  have h := (gcd_hw_joint a b ch H_CELLS_B H_TCHECK_ROOT).1
  ⟨fun c t => ((h c).2 t).1, fun c t => ((h c).2 t).2⟩

theorem roots3_sub_all : (List.range NC).all (fun c => !rootIds3.contains c || rootIds.contains c) =
    true := by decide +kernel

/-- Every phys4 root is a phys3 root, so phys4's certificate hypothesis is implied by phys3's. -/
theorem roots3_sub (c : Fin NC) (h : isRoot3 c = true) : isRoot c = true := by
  have e := List.all_eq_true.mp roots3_sub_all c.val (List.mem_range.mpr c.isLt)
  simp only [isRoot3] at h
  simp only [isRoot, h, Bool.not_true, Bool.false_or] at e ⊢
  exact e

/-- **phys4 is stronger than phys3**: its hypotheses follow from phys3's (it drops H_SEND, H_RECV
and 5 root certificates). -/
theorem phys4_hyps_of_phys3 (ch : Fin NC → Chan)
    (H_TCHECK_ROOT : ∀ c, isRoot c = true → BCert (ch c)) :
    ∀ c, isRoot3 c = true → BCert (ch c) := fun c h => H_TCHECK_ROOT c (roots3_sub c h)

end Formal.Net.CapNet.Gcd

namespace Formal.Net.CapNet.Wit
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapstoneRefine Formal.Net.OpsBusy

/-- Joint consistency of the three hypotheses of `gcd_hw_circuit_safe_phys4` (C-8t's run, root
certificates `exempt`). -/
theorem gcd_hw_phys4_witness :
    (∀ o : Fin NO, CellB chW (srcV 12 18) (opAt o)) ∧
    (∀ t, Handshake.cnt (riseB (chW start).req) t ≤ 1) ∧
    (∀ c, isRoot3 c = true → BCert (chW c)) :=
  ⟨fun o => cell_relax chW _ _ (w_cells o), w_start_once, fun c _ => BCert.exempt (w_held c)⟩

/-- C-8x2's strictness run `chS` (a sink branch's idle bus garbled, so the OLD gate models fail on
it: `strict_old_fails`) also meets every hypothesis of `gcd_hw_circuit_safe_phys4`. -/
theorem strict_phys4_hyps :
    (∀ o : Fin NO, CellB chS (srcV 12 18) (opAt o)) ∧
    (∀ t, Handshake.cnt (riseB (chS start).req) t ≤ 1) ∧
    (∀ c, isRoot3 c = true → BCert (chS c)) :=
  ⟨cells_S, strict_phys2_hyps.2.1, fun c _ => BCert.exempt (held_S c)⟩

end Formal.Net.CapNet.Wit
