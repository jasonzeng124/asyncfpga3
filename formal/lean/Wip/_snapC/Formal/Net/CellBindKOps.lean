import Formal.Net.CellBindWit
import Formal.Net.CellBindKNets

/-!
# Probe C-O4b (1/2): the generated-cell hypothesis for every kernel's operator widths

O4's `GenCell` (`CellBindOps`) covers the widths gcd_hw uses. The four kernels of the generic
capstone (`KCap.kernel_circuit_safe`) use, by a kernel-checked census (`Wip/CO4b/Shape.lean`):

| kernel   | forks (branches)        | compute joins (inputs) | other kinds                               |
|----------|-------------------------|------------------------|-------------------------------------------|
| gcd_hw   | 2, 3, 4, 5, 6           | 1, 2                   | bjoin 2, steer, mux, muxn, amerge, link, src, sink |
| ipow     | 2, 3, 4                 | 1, 2, **3**            | bjoin 2, steer, mux, amerge, link, src, sink |
| collatz  | 2, 3, 4                 | 1, 2, **3**            | bjoin 2, steer, mux, amerge, link, src, sink |
| xorshift | 2, 3, 4                 | 1, 2                   | bjoin 2, steer, mux, amerge, link, src, sink |

The only operator kind not covered by O4 is the **3-input compute unit** (ipow and collatz:
`select`, and fused regions). bdc emits it as `bd_join #(.N(3))` (`bdc/compute.py`), whose
request tree `bd_ctree N = 3` is one generated LUT6 (`CellBindKNets.bd_join_N3`, from
`Wip/CO4b/gen_extra.sh`, gen.sh's yosys flow). Without it O4's `GenCell` is `False` on these
operators (`JoinNode _ [_, _, _] = False`), so a theorem with H_GEN over ipow/collatz would be
vacuous.

ipow's `muli` is DSP48E1-backed: that is the compute unit's DATA path, which the Ops model
(and O4) keep as the copied hypothesis H_DATA_COMB; its request side is the same bd_join +
`uor` + matched delay as every compute unit, so no new control cell is involved.

* `j3F`, `j3_gate`: bd_join N = 3's LUT is the 3-input C-element.
* `JoinNodeK`, `GenJoinK`, `join_of_genK`: the compute unit for N = 1, 2, 3.
* `GenCellK` (= O4's `GenCell` except for `.join`, which uses `GenJoinK`), `cell_of_genK`.
* `shapeK`, `gen_frozenK`: freezing any `Cell` run at tick 0 satisfies `GenCellK` when every
  operator has a covered width (forks 2..6, compute joins 1..3, branch joins 2).
-/

namespace Formal.Net.CellBind.KOps
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CellBind Formal.Net.CellBind.Ops
open Formal.Gen Formal.Gen.Cells Formal.Net.Ops.Gen Formal.Net.CapNet Formal.Net.CellBind.Wit

/-- bd_join N = 3's request tree (one generated LUT6, feedback on I3, `rst` on I4). -/
def j3F (p : Bool × Bool × Bool) (q : Bool) : Bool :=
  genF KNets.bd_join_N3 "u.genblk1.genblk1.g3.u.u" .O
    ["req_in[0]", "req_in[1]", "req_in[2]", "req", "rst"] [p.1, p.2.1, p.2.2, q, false]

theorem j3_gate : ∀ (p : Bool × Bool × Bool) q, j3F p q = cel3 p.1 p.2.1 p.2.2 q := by
  intro ⟨a, b, c⟩ q; revert a b c q; decide +kernel

/-- The joined request of a compute unit's bd_join, N = 1, 2, 3. -/
def JoinNodeK (m : Trace) : List Chan → Prop
  | [i0] => m = i0.req
  | [i0, i1] => CNode j2F (fun t => (i0.req t, i1.req t)) m
  | [i0, i1, i2] => CNode j3F (fun t => (i0.req t, i1.req t, i2.req t)) m
  | _ => False

/-- The C-element property of the joined request (N = 2, 3). -/
theorem joinnode_cel {m : Trace} : ∀ {ins : List Chan}, JoinNodeK m ins → 2 ≤ ins.length →
    ∀ t, m (t + 1) ≠ m t → ∀ l ∈ ins.map Chan.req, l t = m (t + 1)
  | [i0, i1], hJ, _, t, ht, l, hl => by
    have e := cnode_move j2_gate hJ t ht
    have mv := cel2_move _ _ _ (by rw [← e]; exact ht); rw [← e] at mv
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · exact mv.1
    · exact mv.2
  | [i0, i1, i2], hJ, _, t, ht, l, hl => by
    have e := cnode_move j3_gate hJ t ht
    have mv := cel3_move _ _ _ _ (by rw [← e]; exact ht); rw [← e] at mv
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl
    · exact mv.1
    · exact mv.2.1
    · exact mv.2.2
  | [], hJ, _, _, _, _, _ => hJ.elim
  | [_], _, h2, _, _, _, _ => by simp at h2
  | _ :: _ :: _ :: _ :: _, hJ, _, _, _, _, _ => hJ.elim

/-- A compute unit (`K.join`), N = 1, 2, 3: bd_join → `uor` → request delay (H_CHAIN_SETTLED),
plus H_LEAF_PERSIST of the input requests (used for N ≥ 2). -/
structure GenJoinK (g : List Nat → Nat) (ins : List Chan) (o : Chan) : Prop where
  node : ∃ m, JoinNodeK m ins ∧ GenChain m o.req ∧ m 0 = o.req 0
  H_LEAF_PERSIST : LeafPersist (ins.map Chan.req) o.req
  H_WIRE_DI : ∀ i ∈ ins, ∀ t, i.ack (t + 1) ≠ i.ack t → i.ack (t + 1) = o.ack t
  H_DATA_COMB : ∀ t, o.dat t = g (ins.map (fun i => i.dat t))
  initO : o.req 0 = false
  initI : ∀ i ∈ ins, i.ack 0 = false

theorem joinnode_ne {m : Trace} : ∀ {ins : List Chan}, JoinNodeK m ins → ins ≠ []
  | [], h => h.elim
  | _ :: _, _ => List.cons_ne_nil _ _

theorem join_of_genK {g : List Nat → Nat} {ins : List Chan} {o : Chan} (h : GenJoinK g ins o) :
    Join.Join g ins o := by
  obtain ⟨m, hJ, hch, h0⟩ := h.node
  have hR := chain_lumped hch
  refine ⟨joinnode_ne hJ, ?_, h.H_WIRE_DI, h.H_DATA_COMB, h.initO, h.initI⟩
  intro t ht i hi
  match ins, hJ, hi with
  | [i0], hJ, hi =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rw [hi, hR t ht, hJ]
  | i0 :: i1 :: rest, hJ, hi =>
    exact cel_lumped (joinnode_cel hJ (by simp)) hR h.H_LEAF_PERSIST h0 t ht i.req
      (List.mem_map_of_mem hi)

variable {n : Nat}

/-- **The generated-netlist hypothesis of an operator, every kernel's widths.** -/
def GenCellK (ch : Fin n → Chan) (sv : Nat → Nat) : K n → Prop
  | .join ins o e js _ => GenJoinK (jg e js) (ins.map ch) (ch o)
  | k => GenCell ch sv k

theorem cell_of_genK (ch : Fin n → Chan) (sv : Nat → Nat) (k : K n) (h : GenCellK ch sv k) :
    Cell ch sv k := by
  cases k with
  | join ins o e js jw => exact join_of_genK h
  | _ => unfold GenCellK at h; exact cell_of_gen ch sv _ h

/-- The widths the generated netlists cover (now with compute joins of 3 inputs). -/
def shapeK : K n → Bool
  | .join ins _ _ _ _ => decide (ins.length = 1 ∨ ins.length = 2 ∨ ins.length = 3)
  | k => shapeB k

/-- Freezing a `Cell` run at tick 0 gives a `GenCellK` run (covered widths). -/
theorem gen_frozenK (ch : Fin n → Chan) (sv : Nat → Nat) (k : K n) (hc : Cell ch sv k)
    (hs : shapeK k = true) : GenCellK (fun c => Wit.frz (ch c)) sv k := by
  cases k with
  | join ins o e js jw =>
    have J : Join.Join (jg e js) (ins.map ch) (ch o) := hc
    simp only [shapeK, decide_eq_true_eq] at hs
    have hn : JoinNodeK q (ins.map (fun c => Wit.frz (ch c))) := by
      match ins, hs with
      | [_], _ => rfl
      | [_, _], _ => exact cnodeQ
      | [_, _, _], _ => exact cnodeQ
      | [], hs => simp at hs
      | _ :: _ :: _ :: _ :: _, hs => simp at hs
    exact ⟨⟨q, hn, chainQ, rfl⟩, leafQ (mapq' ins),
      fun i hi t h => by simp only [List.mem_map] at hi; obtain ⟨_, _, rfl⟩ := hi; exact absurd rfl h,
      fun t => by have := J.dat 0; simpa [List.map_map, Function.comp_def, Wit.frz] using this,
      rfl, fun i hi => by simp only [List.mem_map] at hi; obtain ⟨_, _, rfl⟩ := hi; rfl⟩
  | _ => unfold GenCellK; exact gen_frozen ch sv _ hc hs

end Formal.Net.CellBind.KOps
