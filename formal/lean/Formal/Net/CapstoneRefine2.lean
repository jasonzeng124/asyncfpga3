import Formal.Net.CapstoneRefine2Cut
import Formal.Net.CapstoneRefineNet
import Formal.Net.CapstoneWitness3

/-!
# Probe C-8x2: the physical gcd_hw capstone without H_ZD_AGREE, and H_DERIVED made structural

The Ops trace of the capstone is now the PHYSICAL OBSERVATION itself: each channel's
handshake wires plus its observed bus (capture-pin bus for a channel whose consumer samples it,
see the note), with the busy-gated gate models `CellB` (OpsBusy). There is no second,
zero-delay trace, hence no H_ZD_AGREE.

* **`gcd_hw_circuit_safe_phys2`**: H_CELLS_B (relaxed gate models on the observed trace),
  H_START_ONCE, H_RECV and a per-channel bundling certificate `BCert` (C-8x: tcheck DAG row,
  tcheck cert row, or `exempt` = H_DERIVED) ⇒ out0 latches only `Nat.gcd a b`.
* **H_DERIVED, structural part** (`held_struct`): on the relaxed model, `Held` of every output
  of a fork, join/compute, steer, link or source follows from `Held` of the operator's inputs
  (`OpsBusy.cellB_held`). The dependency graph of these 434 channels is ranked (kernel
  `decide`, `struct_chk`) with the 31 outputs of the muxes, the 3-input mux and the arbiter
  stages as roots (`rootIds`). So `Held` on the roots and the four-phase protocol give `Held`
  on all 465 channels.
* **`gcd_hw_circuit_safe_phys3`**: certificates only on the 31 roots; the price is H_SEND
  (every producer obeys the sender rule), because the structural step needs the protocol
  and the capstone derives the protocol from `Held` (`net_protocol`); a time-bounded
  `net_protocol` would remove H_SEND and H_RECV together (open).
* `gcd_hw_phys2_witness`, `gcd_hw_phys3_witness`: C-8t's run meets every hypothesis (joint
  consistency, roots `exempt`).
-/

namespace Formal.Net.CapNet.Gcd
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.OpsBusy
open Formal.Net.CapstoneRefine

set_option maxRecDepth 100000

/-- **Physical gcd_hw safety without H_ZD_AGREE.** `ch` is the observed run: the Ops handshake
wires and, per channel, the observed bus. -/
theorem gcd_hw_circuit_safe_phys2 (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31)
    (ch : Fin NC → Chan)
    (H_CELLS_B : ∀ o : Fin NO, CellB ch (srcV a b) (opAt o))
    (H_START_ONCE : ∀ t, Handshake.cnt (riseB (ch start).req) t ≤ 1)
    (H_RECV : ∀ c t, RecvStep (ch c) t)
    (H_TCHECK : ∀ c, BCert (ch c)) :
    (∀ k e, TokAt (ch out0) k e → (ch out0).dat e = Nat.gcd a b) ∧
    (∀ t, closedVals (ch out0) t =
      List.replicate (Handshake.cnt (fallB (ch out0).ack) t) (Nat.gcd a b)) :=
  gcd_hw_circuit_safe3B a b ha hb ch H_CELLS_B
    (fun c => held_of_bcert (H_TCHECK c) (gcd_hw_init_B a b ch H_CELLS_B c) (fun t => H_RECV c t))
    H_START_ONCE

/-! ## H_DERIVED: the structural closure -/

/-- The 31 channels whose bundling is NOT structural: the outputs of the 21 two-input muxes,
the 3-input mux (out0) and the 9 arbiter stages. -/
def rootIds : List Nat := [84, 91, 99, 136, 142, 148, 158, 173, 181, 214, 229, 237, 321, 328, 336, 351, 365, 372, 379, 399, 405, 416, 456, 457, 458, 459, 460, 461, 462, 463, 464]

/-- A rank of the bundling dependency (produced by `Wip/C8x2/classify.py`, checked below). -/
def rankL : List Nat := [
  0, 0, 0, 1, 1, 1, 1, 2, 3, 4, 4, 4, 6, 7, 8, 6, 6, 6, 6, 6, 7, 7, 8, 9, 7, 7, 10, 11, 11, 11, 13, 14, 15, 13, 13, 13, 13, 13, 14, 14,
  15, 16, 14, 14, 15, 16, 14, 14, 15, 15, 15, 17, 18, 19, 20, 21, 21, 21, 21, 23, 24, 25, 23, 24, 25, 23, 24, 25, 23, 24, 25, 23, 24, 25, 23, 24, 25, 23, 23, 2,
  3, 10, 11, 12, 0, 1, 2, 3, 10, 11, 12, 0, 1, 2, 3, 4, 10, 11, 12, 0, 1, 1, 1, 10, 11, 12, 13, 2, 3, 3, 4, 2, 3, 3, 4, 2, 5, 6, 7, 8,
  8, 8, 8, 10, 11, 12, 10, 11, 12, 10, 11, 12, 10, 2, 3, 4, 0, 1, 2, 2, 3, 4, 0, 1, 2, 2, 3, 4, 0, 1, 2, 1, 1, 2, 3, 6, 7, 8, 0, 1,
  2, 1, 1, 2, 1, 2, 2, 3, 4, 6, 7, 8, 9, 0, 2, 3, 4, 6, 7, 8, 9, 0, 1, 1, 6, 7, 8, 9, 3, 4, 4, 4, 4, 4, 3, 6, 7, 8, 6, 6,
  7, 8, 6, 7, 8, 6, 6, 7, 7, 2, 3, 6, 7, 8, 0, 1, 2, 1, 1, 2, 1, 2, 2, 3, 4, 6, 7, 8, 9, 0, 2, 3, 4, 6, 7, 8, 9, 0, 1, 1,
  6, 7, 8, 9, 3, 4, 4, 4, 4, 4, 3, 6, 6, 6, 6, 6, 6, 7, 7, 8, 9, 7, 7, 10, 11, 11, 11, 11, 13, 14, 15, 13, 14, 15, 13, 14, 15, 13, 14, 15,
  13, 13, 13, 13, 14, 15, 6, 7, 7, 8, 6, 7, 7, 6, 7, 6, 7, 8, 9, 10, 10, 10, 10, 12, 13, 14, 12, 13, 6, 12, 13, 14, 12, 13, 12, 12, 12, 12, 13, 2,
  3, 0, 1, 2, 1, 2, 2, 3, 0, 1, 2, 1, 2, 2, 3, 4, 0, 1, 2, 1, 2, 3, 4, 1, 3, 4, 2, 3, 6, 7, 8, 0, 1, 2, 1, 1, 2, 1, 2, 2,
  3, 6, 7, 8, 9, 0, 2, 3, 6, 7, 8, 9, 0, 2, 3, 6, 7, 8, 9, 0, 1, 1, 6, 7, 8, 9, 3, 4, 4, 4, 4, 4, 4, 3, 6, 6, 2, 3, 4, 0,
  1, 2, 2, 3, 4, 0, 1, 2, 1, 1, 3, 4, 5, 1, 2, 3, 0, 1, 5, 5, 5, 12, 12, 12, 22, 22, 22, 22, 9, 9, 9, 9, 5, 5, 5, 5, 5, 5, 5, 5,
  5, 5, 12, 12, 12, 12, 11, 11, 11, 11, 5, 5, 5, 5, 5, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def isRoot (c : Fin NC) : Bool := rootIds.contains c.val
def hrk (c : Fin NC) : Nat := rankL.getD c.val 0

theorem struct_all : (List.range NC).all (fun c => rootIds.contains c ||
    (StructK (ops.getD (prodT.getD c 0).val (K.sink 0)) &&
      (ops.getD (prodT.getD c 0).val (K.sink 0)).insC.all
        (fun i => decide (rankL.getD i.val 0 < rankL.getD c 0)))) = true := by
  decide +kernel

theorem struct_chk (c : Fin NC) (hr : isRoot c = false) :
    StructK (opAt (prodOf c)) = true ∧ ∀ i ∈ (opAt (prodOf c)).insC, hrk i < hrk c := by
  have h := List.all_eq_true.mp struct_all c.val (List.mem_range.mpr c.isLt)
  simp only [isRoot] at hr
  simp only [hr, Bool.false_or, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, fun i hi => h.2 i hi⟩

/-- **Structural bundling closure**: on the relaxed model, with the protocol on every channel,
`Held` on the 31 roots gives `Held` on all 465 channels. -/
theorem held_struct (a b : Nat) (ch : Fin NC → Chan)
    (H_CELLS_B : ∀ o : Fin NO, CellB ch (srcV a b) (opAt o))
    (hp : ∀ c, Protocol (ch c)) (hroot : ∀ c, isRoot c = true → Held (ch c)) :
    ∀ c, Held (ch c) := by
  have key : ∀ m, ∀ c : Fin NC, hrk c = m → Held (ch c) := by
    intro m
    induction m using Nat.strongRecOn with
    | _ m ih =>
      intro c hm
      cases hr : isRoot c
      · obtain ⟨hs, hlt⟩ := struct_chk c hr
        exact cellB_held ch (srcV a b) (opAt (prodOf c)) (H_CELLS_B _) hs hp
          (fun i hi => ih (hrk i) (by rw [← hm]; exact hlt i hi) i rfl) c (prod_mem c)
      · exact hroot c hr
  exact fun c => key _ c rfl

/-- **Physical gcd_hw safety, certificates only on the 31 roots.** H_DERIVED is gone; H_SEND
(the sender rule on every channel) is the price (see the module doc). -/
theorem gcd_hw_circuit_safe_phys3 (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31)
    (ch : Fin NC → Chan)
    (H_CELLS_B : ∀ o : Fin NO, CellB ch (srcV a b) (opAt o))
    (H_START_ONCE : ∀ t, Handshake.cnt (riseB (ch start).req) t ≤ 1)
    (H_RECV : ∀ c t, RecvStep (ch c) t)
    (H_SEND : ∀ c t, SendStep (ch c) t)
    (H_TCHECK_ROOT : ∀ c, isRoot c = true → BCert (ch c)) :
    (∀ k e, TokAt (ch out0) k e → (ch out0).dat e = Nat.gcd a b) ∧
    (∀ t, closedVals (ch out0) t =
      List.replicate (Handshake.cnt (fallB (ch out0).ack) t) (Nat.gcd a b)) := by
  have hinit := gcd_hw_init_B a b ch H_CELLS_B
  have hp : ∀ c, Protocol (ch c) := fun c => ⟨hinit c, fun t => ⟨H_SEND c t, H_RECV c t⟩⟩
  exact gcd_hw_circuit_safe3B a b ha hb ch H_CELLS_B
    (held_struct a b ch H_CELLS_B hp (fun c hr =>
      held_of_bcert (H_TCHECK_ROOT c hr) (hinit c) (fun t => H_RECV c t)))
    H_START_ONCE

end Formal.Net.CapNet.Gcd

namespace Formal.Net.CapNet.Wit
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapstoneRefine Formal.Net.OpsBusy

/-- Joint consistency of the hypotheses of `gcd_hw_circuit_safe_phys2` (C-8t's run, every
certificate `exempt`). -/
theorem gcd_hw_phys2_witness :
    (∀ o : Fin NO, CellB chW (srcV 12 18) (opAt o)) ∧
    (∀ t, Handshake.cnt (riseB (chW start).req) t ≤ 1) ∧
    (∀ c t, RecvStep (chW c) t) ∧
    (∀ c, BCert (chW c)) :=
  ⟨fun o => cell_relax chW _ _ (w_cells o), w_start_once,
   fun c t => ((gcd_hw_protocol 12 18 chW w_cells w_held c).2 t).2,
   fun c => BCert.exempt (w_held c)⟩

/-- Joint consistency of the hypotheses of `gcd_hw_circuit_safe_phys3`. -/
theorem gcd_hw_phys3_witness :
    (∀ o : Fin NO, CellB chW (srcV 12 18) (opAt o)) ∧
    (∀ t, Handshake.cnt (riseB (chW start).req) t ≤ 1) ∧
    (∀ c t, RecvStep (chW c) t) ∧ (∀ c t, SendStep (chW c) t) ∧
    (∀ c, isRoot c = true → BCert (chW c)) :=
  ⟨fun o => cell_relax chW _ _ (w_cells o), w_start_once,
   fun c t => ((gcd_hw_protocol 12 18 chW w_cells w_held c).2 t).2,
   fun c t => ((gcd_hw_protocol 12 18 chW w_cells w_held c).2 t).1,
   fun c _ => BCert.exempt (w_held c)⟩

end Formal.Net.CapNet.Wit
