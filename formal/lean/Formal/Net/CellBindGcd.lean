import Formal.Net.CellBindOps
import Formal.Net.CapstoneWalk
import Formal.Net.CapstoneRigAll

/-!
# Probe C-O4 (4/4): the gcd_hw capstones with H_CELLS replaced by the generated netlists

* `cells_of_gen`: `∀ o, GenCell ch sv (opAt o)` gives `∀ o, Cell ch sv (opAt o)` (H_CELLS).
* **`gcd_hw_circuit_safe_gen`**: `gcd_hw_circuit_safe3` with H_GEN (every operator instance
  of gcd_hw's 367 is its generated netlist under the per-gate SI model, with the named
  hypotheses of `CellBindOps`) in place of H_CELLS.
* **`gcd_rig_all_gen`**: the same for the rig theorem `gcd_rig_all` (sources without the
  reset clause, `GenCellR`).
* `tree_needs_persist`: the generated two-level C-tree of bd_fork N = 5, with every LUT
  obeying H_LUT_SI and H_FB_FIRST, violates the lumped `Fork.cel` field when a leaf withdraws
  early: H_LEAF_PERSIST is needed, not a convenience.
* `mut_breaks`: a bd_fork N = 2 whose C-element INIT has ONE bit flipped (bit 1: `a0 = 1,
  a1 = 0, q = 0`) admits a run that obeys the mutated LUT and H_FB_FIRST and violates
  `Fork.cel`; and its gate lemma is false (`mut_gate_false`). `Wip/CO4/Mutant.lean` shows
  the binding proof itself failing to check on the mutant.
-/

namespace Formal.Net.CellBind.Gcd
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.GcdHw Formal.Net.CapSafe Formal.Net.CellBind Formal.Net.CellBind.Ops
open Formal.Gen Formal.Gen.Cells Formal.Net.Ops.Gen

theorem cells_of_gen {ch : Fin NC → Chan} {sv : Nat → Nat}
    (H_GEN : ∀ o : Fin NO, GenCell ch sv (opAt o)) : ∀ o : Fin NO, Cell ch sv (opAt o) :=
  fun o => cell_of_gen ch sv (opAt o) (H_GEN o)

/-- **gcd_hw, from the generated netlists.** For `a, b < 2^31` and every run `ch` of bdc's
gcd_hw network in which every operator instance obeys its generated netlist (H_GEN: per-LUT
H_LUT_SI with the yosys INITs, H_FB_FIRST, H_CHAIN_SETTLED / H_REQ_PERSIST per delay chain,
H_LEAF_PERSIST, H_WIRE_DI per pure-fan-out wire, and the copied data / select / arbiter /
reset fields), every channel is bundled (H_BUNDLE) and `start` rises at most once: every
token closed on `out0` carries `gcd a b`. -/
theorem gcd_hw_circuit_safe_gen (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) (ch : Fin NC → Chan)
    (H_GEN : ∀ o : Fin NO, GenCell ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, Handshake.cnt (riseB (ch start).req) t ≤ 1) :
    (∀ k e, TokAt (ch out0) k e → (ch out0).dat e = Nat.gcd a b) ∧
    (∀ t, closedVals (ch out0) t = List.replicate (Handshake.cnt (fallB (ch out0).ack) t) (Nat.gcd a b)) :=
  gcd_hw_circuit_safe3 a b ha hb ch (cells_of_gen H_GEN) H_BUNDLE H_START_ONCE

/-- The rig's form: the sources hold their requests through reset, so the source's reset
clause is dropped (`CellR`). -/
def GenCellR {n : Nat} (ch : Fin n → Chan) (sv : Nat → Nat) : K n → Prop
  | .src z which _ => LutSI (fun a => genF bd_src_W2 "u" .O ["ack"] [a]) (ch z).ack (ch z).req ∧
      ∀ t, (ch z).dat t = sv which
  | k => GenCell ch sv k

theorem cellR_of_gen {n : Nat} (ch : Fin n → Chan) (sv : Nat → Nat) (k : K n) (h : GenCellR ch sv k) :
    CellR ch sv k := by
  cases k with
  | src z which d => exact ⟨src_bound h.1, h.2⟩
  | _ => unfold GenCellR at h; unfold CellR; exact cell_of_gen ch sv _ h

/-- **The rig theorem, from the generated netlists.** -/
theorem gcd_rig_all_gen (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) (ch : Fin NC → Chan)
    (H_GEN_R : ∀ o : Fin NO, GenCellR ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_ENV : RigEnv (ch start).req (ch out0).ack) :
    (∀ k r, OffAt (ch out0) k r → (ch out0).dat (r + 1) = Nat.gcd a b) ∧
    (∀ k e, TokAt (ch out0) k e → (ch out0).dat e = Nat.gcd a b) :=
  gcd_rig_all a b ha hb ch (fun o => cellR_of_gen ch (srcV a b) (opAt o) (H_GEN_R o)) H_BUNDLE H_ENV

/-! ## H_LEAF_PERSIST is needed: the bd_fork N = 5 tree -/

def tr (l : List Bool) (d : Bool) : Trace := fun t => l.getD t d

theorem tr_tail (l : List Bool) (d : Bool) (t : Nat) (h : l.length ≤ t) : tr l d t = d := by
  simp [tr, List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

/-- Leaves `a0` (withdraws at t = 1→2), `a1..a4` high; chunk node `m` rises at 0→1, root
`r` (the fork's `ack`) rises at 2→3 reading `m = a4 = 1` while `a0 = 0`. -/
def lA0 : Trace := tr [true, true, false, false] false
def lHi : Trace := fun _ => true
def nM : Trace := tr [false, true, true, true] true
def nR : Trace := tr [false, false, false, true] true

theorem tree_needs_persist :
    CNode f5cF (fun t => (lA0 t, lHi t, lHi t, lHi t)) nM ∧
    CNode f5tF (fun t => (nM t, lHi t)) nR ∧ nM 0 = nR 0 ∧
    ¬ (∀ t, nR (t + 1) ≠ nR t → ∀ l ∈ [lA0, lHi, lHi, lHi, lHi], l t = nR (t + 1)) := by
  refine ⟨⟨nM, fun t ht => ?_, fun t _ => rfl⟩, ⟨nR, fun t ht => ?_, fun t _ => rfl⟩, rfl, fun H => ?_⟩
  · by_cases h : t < 4
    · have key : ∀ t, t < 4 → nM (t + 1) ≠ nM t →
          nM (t + 1) = f5cF (lA0 t, lHi t, lHi t, lHi t) (nM t) := by decide +kernel
      exact key t h ht
    · exfalso; apply ht; simp only [nM]; rw [tr_tail _ _ _ (by simp; omega), tr_tail _ _ _ (by simp; omega)]
  · by_cases h : t < 4
    · have key : ∀ t, t < 4 → nR (t + 1) ≠ nR t → nR (t + 1) = f5tF (nM t, lHi t) (nR t) := by
        decide +kernel
      exact key t h ht
    · exfalso; apply ht; simp only [nR]; rw [tr_tail _ _ _ (by simp; omega), tr_tail _ _ _ (by simp; omega)]
  · have := H 2 (by decide) lA0 (by simp)
    exact absurd this (by decide)

/-! ## A flipped INIT bit breaks the binding -/

/-- bd_fork N = 2 with INIT bit 1 flipped (the entry `a0 = 1, a1 = 0, q = 0, rst = 0`). -/
def mutFork : Netlist :=
  { bd_fork_N2 with cells := bd_fork_N2.cells.map (fun c => { c with init := c.init ^^^ 2 }) }

def mF (p : Bool × Bool) (q : Bool) : Bool :=
  genF mutFork forkCell .O ["ack_in[0]", "ack_in[1]", "ack", "rst"] [p.1, p.2, q, false]

theorem mut_gate_false : ¬ ∀ (p : Bool × Bool) q, mF p q = cel2 p.1 p.2 q := by
  intro h; have := h (true, false) false; revert this; decide +kernel

/-- A run that obeys the mutated LUT with H_FB_FIRST and violates `Fork.cel`: branch acks
`1, 0`, the fork's `ack` rises at 0→1. -/
theorem mut_breaks :
    CNode mF (fun t => (lHi t, (fun _ => false : Trace) t)) (tr [false] true) ∧
    ¬ (∀ t, (tr [false] true) (t + 1) ≠ (tr [false] true) t →
        ∀ l ∈ [lHi, (fun _ => false : Trace)], l t = (tr [false] true) (t + 1)) := by
  refine ⟨⟨tr [false] true, fun t ht => ?_, fun t _ => rfl⟩, fun H => ?_⟩
  · cases t with
    | zero => show true = mF (true, false) false; decide +kernel
    | succ t => exfalso; apply ht; rw [tr_tail _ _ _ (by simp), tr_tail _ _ _ (by simp)]
  · have := H 0 (by decide) (fun _ => false) (by simp)
    exact absurd this (by decide)

end Formal.Net.CellBind.Gcd
