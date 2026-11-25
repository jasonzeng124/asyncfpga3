import Formal.Target.Spec
import Formal.Core.Prims.Carry
import Formal.Core.Lut

/-!
# Formal.Cells.PrimTables — MUXF7/F8, CARRY4 and LUT6_2 as Spec gates (H_PRIM tables)

Shard B, THE goal. `formal/target/STATUS.md` item 3: "MUXF7/F8, CARRY4 as gates of this
kind not yet decoded". Spec v1 (`Formal.Target.Spec`, frozen) has ONE primitive kind: a
`Gate` with `k` pins, an INIT table read at `addr k` (pin 0 = bit 0) and one arc per pin.
This file gives the INIT tables the decoder must emit for the slice primitives that are
not LUTs, and proves each equal to shard A's Core model of that primitive.

## Problem, plainly
Is "a CARRY4 output / a MUXF7 / a MUXF8 / each half of a LUT6_2 is a Spec gate with table
X" the same Boolean function as Core's model (`Carry.bout`, `Muxf.bmux`, `Lut62`)? If so,
the decoder can turn every such primitive into Spec gates with these tables, and H_PRIM for
them is exactly Core's H_C4_PERPIN / H_MUXF_PASS (per-pin reads), nothing new.

## Results
* `table_sound`: generic. If `init.testBit a = F (bits of a)` for every `a < 2^k`
  (checked by `decide`), then the Spec gate reads `F` on EVERY pin vector:
  `init.testBit (addr k v) = F v`, for any `F` that reads only pins `< k`.
* `muxf_gate`: MUXF7/MUXF8 (pins I0, I1, S): table `0xCA` = `S ? I1 : I0` = Core `bmux`.
* `carry_gate o`: the eight CARRY4 outputs (pins `c0, DI0..DI3, S0..S3`, `c0` the
  PRECYINIT output, i.e. the node the configuration selects: constant, AX or CIN) with
  the 512-bit tables `c4Table o` equal Core's `bout · o`.
* `aCarry_gate co i` (shard A's decoder layout, `tools-A/target/build_net.py`): pins
  `[CIN, CYINIT, S0..Si, DI0..]`, carry-in `CIN || CYINIT`, table built by A's loop
  (`aCarryF`, transcribed; `aCarryInit`): the Spec gate reads Core's `bout` on the
  corresponding Core pin vector (`aToCore`), all 8 outputs, every input. Negative control:
  swapping the mux arms in the transcribed loop breaks `aCarry_core`.
* `lut6_gate`, `lut5_gate`: a LUT6_2's O6 is the 6-pin gate with the full INIT; O5 the
  5-pin gate with `INIT % 2^32` (Core `Lut62.o5` = `INIT[31:0]`); both against Core's
  `Lut.eval`.

## Fidelity note (why per-pin reads are exact for CARRY4 and MUXF)
Spec reads each pin ONCE per output instant. For a function in which some pin reaches the
output along two paths, a real gate could see that pin at two different times; per-pin
reads would then miss a glitch. Every CARRY4 output and the MUXF are read-once formulas of
their pins (Core `Carry.kout_sic`), so one read per pin loses nothing there. A LUT is a mux
tree in which each pin drives one rank; Spec's single read per pin assumes the rank sees
the pin at one instant (H_KLEENE_LUT's timing half, already named in Core).

## Not covered
The decoder itself (part II, shard A); the PRECYINIT/CYINIT selection as a node choice;
CARRY4 arcs (Core `XrayData.carry4Arc`, per variant).
-/

namespace Formal.Cells.PrimTables

open Formal.Target Formal.Core.Prims
open Formal.Core (Lut Lut62 vtail K3)

/-! ## Spec's address of a pin vector is its bit pattern -/

theorem addr_lt : ∀ (k : Nat) (v : Nat → Bool), addr k v < 2 ^ k
  | 0, _ => by simp [Formal.Target.addr]
  | k + 1, v => by
    have := addr_lt k v
    simp only [Formal.Target.addr, Nat.pow_succ]
    split <;> omega

theorem addr_testBit : ∀ (k : Nat) (v : Nat → Bool) (i : Nat), i < k → (addr k v).testBit i = v i
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, v, i, h => by
    have hlt := addr_lt k v
    simp only [Formal.Target.addr]
    by_cases hv : v k
    · simp only [hv, ite_true]
      rw [Nat.add_comm]
      by_cases hik : i = k
      · subst hik
        rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]; simp [hv]
      · rw [Nat.testBit_two_pow_add_gt (by omega)]
        exact addr_testBit k v i (by omega)
    · simp only [hv, Bool.false_eq_true, ite_false, Nat.add_zero]
      by_cases hik : i = k
      · subst hik; rw [Nat.testBit_lt_two_pow hlt]; simp [hv]
      · exact addr_testBit k v i (by omega)

/-- `F` reads only pins below `k`. -/
def ReadsBelow (k : Nat) (F : (Nat → Bool) → Bool) : Prop :=
  ∀ u v, (∀ i, i < k → u i = v i) → F u = F v

/-- **Generic table soundness.** -/
theorem table_sound {k init : Nat} {F : (Nat → Bool) → Bool} (hF : ReadsBelow k F)
    (h : ∀ a, a < 2 ^ k → init.testBit a = F (fun i => a.testBit i)) (v : Nat → Bool) :
    init.testBit (addr k v) = F v := by
  rw [h _ (addr_lt k v)]
  exact hF _ _ (fun i hi => addr_testBit k v i hi)

/-! ## MUXF7 / MUXF8 -/

/-- Pins `0 = I0`, `1 = I1`, `2 = S`. -/
def muxfInit : Nat := 0xCA

theorem muxf_gate (v : Nat → Bool) : muxfInit.testBit (addr 3 v) = bmux (v 2) (v 0) (v 1) :=
  table_sound (F := fun v => bmux (v 2) (v 0) (v 1))
    (fun u w h => by
      show bmux (u 2) (u 0) (u 1) = bmux (w 2) (w 0) (w 1)
      rw [h 0 (by omega), h 1 (by omega), h 2 (by omega)]) (by decide) v

/-! ## CARRY4 -/

/-- The 512-bit table of CARRY4 output `o`, pins `0 = c0`, `1..4 = DI0..DI3`, `5..8 = S0..S3`
(Core `Carry`'s pin order). Generated by `#eval` from `bout`, then checked below. -/
def c4Table : COut → Nat
  | .o0 => 0x55555555aaaaaaaa55555555aaaaaaaa55555555aaaaaaaa55555555aaaaaaaa55555555aaaaaaaa55555555aaaaaaaa55555555aaaaaaaa55555555aaaaaaaa
  | .o1 => 0x5555555533333333aaaaaaaacccccccc5555555533333333aaaaaaaacccccccc5555555533333333aaaaaaaacccccccc5555555533333333aaaaaaaacccccccc
  | .o2 => 0x55555555333333330f0f0f0f0f0f0f0faaaaaaaaccccccccf0f0f0f0f0f0f0f055555555333333330f0f0f0f0f0f0f0faaaaaaaaccccccccf0f0f0f0f0f0f0f0
  | .o3 => 0x55555555333333330f0f0f0f0f0f0f0f00ff00ff00ff00ff00ff00ff00ff00ffaaaaaaaaccccccccf0f0f0f0f0f0f0f0ff00ff00ff00ff00ff00ff00ff00ff00
  | .co0 => 0xaaaaaaaaccccccccaaaaaaaaccccccccaaaaaaaaccccccccaaaaaaaaccccccccaaaaaaaaccccccccaaaaaaaaccccccccaaaaaaaaccccccccaaaaaaaacccccccc
  | .co1 => 0xaaaaaaaaccccccccf0f0f0f0f0f0f0f0aaaaaaaaccccccccf0f0f0f0f0f0f0f0aaaaaaaaccccccccf0f0f0f0f0f0f0f0aaaaaaaaccccccccf0f0f0f0f0f0f0f0
  | .co2 => 0xaaaaaaaaccccccccf0f0f0f0f0f0f0f0ff00ff00ff00ff00ff00ff00ff00ff00aaaaaaaaccccccccf0f0f0f0f0f0f0f0ff00ff00ff00ff00ff00ff00ff00ff00
  | .co3 => 0xaaaaaaaaccccccccf0f0f0f0f0f0f0f0ff00ff00ff00ff00ff00ff00ff00ff00ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000

/-- Core's CARRY4 output read off a Nat-indexed pin vector. -/
def c4F (o : COut) (v : Nat → Bool) : Bool := bout (fun i : Fin 9 => v i.val) o

theorem c4F_reads (o : COut) : ReadsBelow 9 (c4F o) := by
  intro u w h
  unfold c4F
  congr 1
  funext i
  exact h i.val i.isLt

theorem c4_tables : ∀ o : COut, ∀ a, a < 2 ^ 9 → (c4Table o).testBit a = c4F o (fun i => a.testBit i) := by
  intro o; cases o <;> decide +kernel

/-- **CARRY4 output `o` is the Spec gate with table `c4Table o`**, on every pin vector. -/
theorem carry_gate (o : COut) (v : Nat → Bool) :
    (c4Table o).testBit (addr 9 v) = bout (fun i : Fin 9 => v i.val) o :=
  table_sound (c4F_reads o) (c4_tables o) v

/-! ## Shard A's decoder layout (tools-A/target/build_net.py), mirrored and checked

`build_net.py` emits CARRY4 output `CO i` / `O i` as one gate whose pins are
`[CIN, CYINIT, S0..Si, DI0..DI(nd-1)]` (`nd = i+1` for CO, `i` for O; pins that cannot
matter are dropped) and whose table is computed by the loop below, with carry-in
`CIN || CYINIT` (yosys cells_sim; the silicon's PRECYINIT is a static mux, which agrees
when the unused source is tied 0). `aCarryF` is that loop, transcribed; `aCarry_core`
proves it equals Core's chain `bout` on the corresponding Core pin vector, for every input
and every one of the 8 outputs. `aCarryInit` is the table the loop produces; `aCarry_gate`
says the Spec gate with that table and that pin order reads Core's CARRY4. -/

/-- Number of pins of A's gate for output `(co, i)`. -/
def aK (co : Bool) (i : Nat) : Nat := 2 + (i + 1) + (if co then i + 1 else i)

/-- A's loop: `cc = CIN | CYINIT`, then `cc = S_j ? cc : DI_j` for `j < i`, then the output. -/
def aCarryF (co : Bool) (i : Nat) (v : Nat → Bool) : Bool :=
  let s := fun j => v (2 + j)
  let di := fun j => v (3 + i + j)
  let cc := (List.range i).foldl (fun c j => if s j then c else di j) (v 0 || v 1)
  if co then (if s i then cc else di i) else (s i ^^ cc)

/-- The Core pin vector A's gate stands for: `c0 = CIN || CYINIT`, `S_j`, `DI_j`
(pins of A's gate beyond the ones it keeps are irrelevant to that output). -/
def aToCore (co : Bool) (i : Nat) (v : Nat → Bool) : Fin 9 → Bool := fun p =>
  if p.val = 0 then (v 0 || v 1)
  else if p.val ≤ 4 then
    (if p.val - 1 < (if co then i + 1 else i) then v (3 + i + (p.val - 1)) else false)
  else (if p.val - 5 ≤ i then v (2 + (p.val - 5)) else false)

def coutOf (co : Bool) : Fin 4 → COut
  | 0 => if co then .co0 else .o0
  | 1 => if co then .co1 else .o1
  | 2 => if co then .co2 else .o2
  | 3 => if co then .co3 else .o3

/-- A's table for output `(co, i)`, built by the loop over all addresses. -/
def aCarryInit (co : Bool) (i : Nat) : Nat :=
  (List.range (2 ^ aK co i)).foldl
    (fun acc a => if aCarryF co i (fun q => a.testBit q) then acc + 2 ^ a else acc) 0

/-- **A's loop is Core's CARRY4**, on every bit pattern of its pins. -/
theorem aCarry_core : ∀ co : Bool, ∀ i : Fin 4, ∀ a, a < 2 ^ aK co i.val →
    aCarryF co i.val (fun q => a.testBit q) = bout (aToCore co i.val (fun q => a.testBit q)) (coutOf co i) := by
  decide +kernel

/-- A's table bit `a` is the loop's value on `a`'s bit pattern. -/
theorem aToCore_reads (co : Bool) (i : Fin 4) :
    ReadsBelow (aK co i.val) (fun v => bout (aToCore co i.val v) (coutOf co i)) := by
  intro u w h
  show bout _ _ = bout _ _
  congr 1
  funext p
  have hk : ∀ q, q < aK co i.val → u q = w q := h
  have i4 := i.isLt
  unfold aToCore
  by_cases a0 : p.val = 0
  · simp only [a0, ite_true]
    rw [hk 0 (by unfold aK; split <;> omega), hk 1 (by unfold aK; split <;> omega)]
  · simp only [a0, ite_false]
    by_cases a1 : p.val ≤ 4
    · simp only [a1, ite_true]
      by_cases a2 : p.val - 1 < (if co then i.val + 1 else i.val)
      · simp only [a2, ite_true]; apply hk; unfold aK; revert a2; split <;> intro a2 <;> omega
      · simp only [a2, ite_false]
    · simp only [a1, ite_false]
      by_cases a3 : p.val - 5 ≤ i.val
      · simp only [a3, ite_true]; apply hk; unfold aK; have := p.isLt; split <;> omega
      · simp only [a3, ite_false]

theorem aCarry_table : ∀ co : Bool, ∀ i : Fin 4, ∀ a, a < 2 ^ aK co i.val →
    (aCarryInit co i.val).testBit a = aCarryF co i.val (fun q => a.testBit q) := by
  decide +kernel

/-- **The Spec gate A's decoder emits for CARRY4 output `(co, i)` reads Core's CARRY4.** -/
theorem aCarry_gate (co : Bool) (i : Fin 4) (v : Nat → Bool) :
    (aCarryInit co i.val).testBit (addr (aK co i.val) v) = bout (aToCore co i.val v) (coutOf co i) :=
  table_sound (aToCore_reads co i)
    (fun a ha => (aCarry_table co i a ha).trans (aCarry_core co i a ha)) v

/-! ## LUT6_2 -/

/-- Core's LUT reading of a Nat-indexed pin vector. -/
def lutF {k : Nat} (L : Lut k) (v : Nat → Bool) : Bool := L.eval (fun i : Fin k => v i.val)

theorem lutF_reads {k : Nat} (L : Lut k) : ReadsBelow k (lutF L) := by
  intro u w h; unfold lutF; congr 1; funext i; exact h i.val i.isLt

/-- Core's address of the bit pattern of `a` is `a mod 2^k`. -/
theorem core_addr_bits : ∀ (k a : Nat), Formal.Core.addr (fun i : Fin k => a.testBit i.val) = a % 2 ^ k
  | 0, a => by simp [Formal.Core.addr, Nat.mod_one]
  | k + 1, a => by
    show (a.testBit 0).toNat + 2 * Formal.Core.addr (vtail fun i : Fin (k + 1) => a.testBit i.val)
      = a % 2 ^ (k + 1)
    have ht : (vtail fun i : Fin (k + 1) => a.testBit i.val) = fun i : Fin k => (a / 2).testBit i.val := by
      funext i; simp [vtail, Nat.testBit_succ]
    rw [ht, core_addr_bits k (a / 2), Nat.pow_succ', Nat.mod_mul]
    have h0 : (a.testBit 0).toNat = a % 2 := by
      rw [Nat.testBit_zero]; rcases Nat.mod_two_eq_zero_or_one a with h | h <;> simp [h]
    rw [h0]

/-- **A Core LUT is the Spec gate with its INIT (as a Nat)**, on every pin vector. -/
theorem lut_gate {k : Nat} (L : Lut k) (v : Nat → Bool) :
    L.init.toNat.testBit (addr k v) = lutF L v := by
  apply table_sound (lutF_reads L)
  intro a ha
  unfold lutF Lut.eval Lut.entry
  rw [core_addr_bits, Nat.mod_eq_of_lt ha]
  rfl

/-- LUT6_2 O6: the 6-pin gate with the whole INIT. -/
theorem lut6_gate (L : Lut62) (v : Nat → Bool) : L.init.toNat.testBit (addr 6 v) = lutF L.o6 v :=
  lut_gate L.o6 v

/-- LUT6_2 O5: the 5-pin gate with `INIT mod 2^32` (Core `o5` = `INIT[31:0]`). -/
theorem lut5_gate (L : Lut62) (v : Nat → Bool) :
    (L.init.toNat % 2 ^ 32).testBit (addr 5 v) = lutF L.o5 v := by
  rw [← lut_gate L.o5 v]
  simp [Lut62.o5, BitVec.toNat_setWidth]

end Formal.Cells.PrimTables
