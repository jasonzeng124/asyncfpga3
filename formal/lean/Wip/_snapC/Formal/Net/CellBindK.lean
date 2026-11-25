import Formal.Net.CellBindKOps
import Formal.Net.KernelCapGcd
import Formal.Net.KernelCapIpow
import Formal.Net.KernelCapCollatz
import Formal.Net.XorshiftWit
import Formal.Net.CollatzWit

/-!
# Probe C-O4b (2/2): `kernel_circuit_safe_gen`, H_GEN in place of H_CELLS for any kernel

* **`kernel_circuit_safe_gen`**: for any kernel `[KD] [KP]`, C-8y2's `kernel_circuit_safe`
  with H_GEN (every operator obeys its yosys-generated netlist: `GenCellK`, O4's per-gate
  model plus bd_join N = 3) in place of H_CELLS.
* Instances: `gcd_hw_circuit_safe_genK`, `ipow_circuit_safe_gen`, `collatz_circuit_safe_gen`,
  `xorshift_circuit_safe_gen`, with the statements of the four H_CELLS instance theorems.
* **Coverage** (`*_shape`, kernel `decide`): every operator of all four networks has a width
  the generated netlists cover (`shapeK`), so H_GEN is not `False` on any operator.
* **Non-vacuity**, quiet runs only (`*_gen_witness`): freezing at tick 0 the C-8t (gcd_hw),
  C-wit (collatz n = 7, xorshift seed 2463534242 / rounds 4) runs gives runs that satisfy
  H_GEN, H_BUNDLE and H_START_ONCE jointly. ipow: no `Cell` run in `Formal` to freeze (the
  audit's `IpowWit` lives on the audit branch), so no ipow witness here (open).

The named hypotheses inside H_GEN are O4's (see `CellBindOps`): H_LUT_SI, H_FB_FIRST, H_PIN_EQ,
H_CHAIN_SETTLED, H_REQ_PERSIST, H_LEAF_PERSIST, H_WIRE_DI, the copied data / select / arbiter
fields, H_R0_ISO, H_PORT_ORDER. `CellBindPersist*` removes H_LEAF_PERSIST and H_REQ_PERSIST.
-/

namespace Formal.Net.CellBind.K
open Formal.Net Formal.Net.Kahn Formal.Net.GcdHw Formal.Net.Handshake Formal.Net.Ops
open Formal.Net.CapNet hiding R Hh Hh_pr Hh_cn NoEnd JOK FoldOK OpChk
open Formal.Net.KCap KD KP
open Formal.Net.CellBind.KOps

/-- **The capstone for any kernel, from the generated netlists.** -/
theorem kernel_circuit_safe_gen [KD] [KP] (a b : Nat) (hd : dom a b) (ch : Fin NC → Chan)
    (H_GEN : ∀ o : Fin NO, GenCellK ch (srcVal a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, Handshake.cnt (riseB (ch start).req) t ≤ 1) :
    (∀ k e, TokAt (ch out0) k e → (ch out0).dat e = spec a b) ∧
    (∀ t, closedVals (ch out0) t =
      List.replicate (Handshake.cnt (fallB (ch out0).ack) t) (spec a b)) :=
  kernel_circuit_safe a b hd ch (fun o => cell_of_genK ch (srcVal a b) (opAt o) (H_GEN o))
    H_BUNDLE H_START_ONCE

/-- Every operator of a network whose list passes `shapeK` has a covered width. -/
theorem shape_at {n : Nat} {ops : List (K n)} (h : ops.all shapeK = true) (i : Nat) (d : K n)
    (hd : shapeK d = true) : shapeK (ops.getD i d) = true := by
  rw [List.getD_eq_getElem?_getD]
  cases hg : ops[i]? with
  | none => exact hd
  | some k => exact List.all_eq_true.mp h k (List.mem_of_getElem? hg)

theorem frz_held (c : Chan) : Held (Wit.frz c) := fun _ _ _ => rfl

theorem frz_once (c : Chan) : ∀ t, Handshake.cnt (riseB (Wit.frz c).req) t ≤ 1 := by
  have : ∀ t, Handshake.cnt (riseB (Wit.frz c).req) t = 0 := by
    intro t; induction t with
    | zero => rfl
    | succ t ih => simp only [Handshake.cnt]; rw [ih]; rfl
  intro t; rw [this]; exact Nat.zero_le 1

/-! ## gcd_hw -/

section gcd
open Formal.Net.KCap.GcdInst
attribute [local instance] gcdKD gcdKP

theorem gcd_shape : CapNet.Gcd.ops.all shapeK = true := by decide +kernel

theorem gcd_hw_circuit_safe_genK (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31)
    (ch : Fin CapNet.Gcd.NC → Chan)
    (H_GEN : ∀ o : Fin CapNet.Gcd.NO, GenCellK ch (CapNet.srcV a b) (CapNet.Gcd.opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, Handshake.cnt (riseB (ch CapNet.Gcd.start).req) t ≤ 1) :
    (∀ k e, TokAt (ch CapNet.Gcd.out0) k e → (ch CapNet.Gcd.out0).dat e = Nat.gcd a b) ∧
    (∀ t, closedVals (ch CapNet.Gcd.out0) t =
      List.replicate (Handshake.cnt (fallB (ch CapNet.Gcd.out0).ack) t) (Nat.gcd a b)) :=
  kernel_circuit_safe_gen a b (⟨ha, hb⟩ : a < 2 ^ 31 ∧ b < 2 ^ 31) ch H_GEN H_BUNDLE H_START_ONCE

theorem gcd_gen_witness :
    ∃ ch : Fin CapNet.Gcd.NC → Chan,
      (∀ o : Fin CapNet.Gcd.NO, GenCellK ch (CapNet.srcV 12 18) (CapNet.Gcd.opAt o)) ∧
      (∀ c, Held (ch c)) ∧ (∀ t, Handshake.cnt (riseB (ch CapNet.Gcd.start).req) t ≤ 1) := by
  obtain ⟨ch, hC, _, _, _⟩ := Formal.Net.CapNet.Wit.gcd_hw_joint_witness3
  exact ⟨fun c => Wit.frz (ch c),
    fun o => gen_frozenK ch _ (CapNet.Gcd.opAt o) (hC o) (shape_at gcd_shape o.val _ rfl),
    fun _ => frz_held _, frz_once _⟩

end gcd

/-! ## ipow -/

section ipow
open Formal.Net.KCap.IpowInst
attribute [local instance] ipowKD ipowKP

theorem ipow_shape : IpowCap.ops.all shapeK = true := by decide +kernel

theorem ipow_circuit_safe_gen (b e : Nat) (he : e < 2 ^ 32) (ch : Fin IpowCap.NC → Chan)
    (H_GEN : ∀ o : Fin IpowCap.NO, GenCellK ch (CapNet.srcV b e) (IpowCap.opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, Handshake.cnt (riseB (ch IpowCap.start).req) t ≤ 1) :
    (∀ k v, TokAt (ch IpowCap.out0) k v → (ch IpowCap.out0).dat v = IpowHw.ipowSpec b e) ∧
    (∀ t, closedVals (ch IpowCap.out0) t =
      List.replicate (Handshake.cnt (fallB (ch IpowCap.out0).ack) t) (IpowHw.ipowSpec b e)) :=
  kernel_circuit_safe_gen b e he ch H_GEN H_BUNDLE H_START_ONCE

end ipow

/-! ## collatz -/

section collatz
open Formal.Net.KCap.CollatzInst
attribute [local instance] collatzKD collatzKP

theorem collatz_shape : CollatzCap.ops.all shapeK = true := by decide +kernel

theorem collatz_circuit_safe_gen (n fuel r : Nat) (hr : CollatzHw.collatzC fuel n = some r)
    (ch : Fin CollatzCap.NC → Chan)
    (H_GEN : ∀ o : Fin CollatzCap.NO, GenCellK ch (srcC n fuel) (KCap.opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, Handshake.cnt (riseB (ch CollatzCap.start).req) t ≤ 1) :
    (∀ k v, TokAt (ch CollatzCap.out0) k v → (ch CollatzCap.out0).dat v = r) ∧
    (∀ t, closedVals (ch CollatzCap.out0) t =
      List.replicate (Handshake.cnt (fallB (ch CollatzCap.out0).ack) t) r) :=
  collatz_circuit_safe n fuel r hr ch (fun o => cell_of_genK ch _ _ (H_GEN o)) H_BUNDLE H_START_ONCE

theorem collatz_gen_witness :
    ∃ ch : Fin CollatzCap.NC → Chan,
      (∀ o : Fin CollatzCap.NO, GenCellK ch (srcC 7 200) (KCap.opAt o)) ∧
      (∀ c, Held (ch c)) ∧ (∀ t, Handshake.cnt (riseB (ch CollatzCap.start).req) t ≤ 1) :=
  ⟨fun c => Wit.frz (Formal.Net.KCap.CollatzWit.chC c),
    fun o => gen_frozenK _ _ (KCap.opAt o) (Formal.Net.KCap.CollatzWit.c_cells o)
      (shape_at collatz_shape o.val _ rfl),
    fun _ => frz_held _, frz_once _⟩

end collatz

/-! ## xorshift -/

section xorshift
open Formal.Net.KCap.XorshiftInst
attribute [local instance] xorKD xorKP

theorem xorshift_shape : XorshiftCap.ops.all shapeK = true := by decide +kernel

theorem xorshift_circuit_safe_gen (seed rounds : Nat) (hr : rounds < 2 ^ 32)
    (ch : Fin XorshiftCap.NC → Chan)
    (H_GEN : ∀ o : Fin XorshiftCap.NO, GenCellK ch (CapNet.srcV seed rounds) (KCap.opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, Handshake.cnt (riseB (ch XorshiftCap.start).req) t ≤ 1) :
    (∀ k v, TokAt (ch XorshiftCap.out0) k v →
      (ch XorshiftCap.out0).dat v = XorshiftHw.xsSpec seed rounds) ∧
    (∀ t, closedVals (ch XorshiftCap.out0) t =
      List.replicate (Handshake.cnt (fallB (ch XorshiftCap.out0).ack) t)
        (XorshiftHw.xsSpec seed rounds)) :=
  kernel_circuit_safe_gen seed rounds hr ch H_GEN H_BUNDLE H_START_ONCE

theorem xorshift_gen_witness :
    ∃ ch : Fin XorshiftCap.NC → Chan,
      (∀ o : Fin XorshiftCap.NO, GenCellK ch (CapNet.srcV 2463534242 4) (KCap.opAt o)) ∧
      (∀ c, Held (ch c)) ∧ (∀ t, Handshake.cnt (riseB (ch XorshiftCap.start).req) t ≤ 1) :=
  ⟨fun c => Wit.frz (Formal.Net.KCap.XorshiftWit.chX c),
    fun o => gen_frozenK _ _ (KCap.opAt o) (Formal.Net.KCap.XorshiftWit.x_cells o)
      (shape_at xorshift_shape o.val _ rfl),
    fun _ => frz_held _, frz_once _⟩

end xorshift

end Formal.Net.CellBind.K
