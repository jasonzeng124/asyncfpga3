import Formal.Gen.Netlist
import Formal.Core.Prims.Carry
import Formal.Core.Prims.Lut62

/-!
# Formal.Core.Prims.GenCheck — Core primitive semantics = shard C's generated models

Shard A, probe PrimsComb. Core Lean only (no Mathlib). Imports shard C's
`Formal.Gen.Netlist` (the ONE interpreter behind every generated netlist and
`Formal.Gen.ProofsPrims`) read-only, and proves that its Kleene reading
(`kleeneSem`) of each combinational primitive is the semantics of
`Formal.Core.Prims`:

* `muxf_eq` : a MUXF7/MUXF8 cell's `O` is `mux2 S I0 I1` (`Muxf.mux2`); and
  `mux2_eq_kmux` : `mux2` is C's `kmux`.
* `lut62_o6_eq`, `lut62_o5_eq` : a LUT6_2 cell's `O6` is the A6-rooted physical
  tree `L62.o6Tree`, its `O5` is the shared lower sub-tree `L62.o5Tree`.
* `carry4_eq` : a CARRY4 cell's eight outputs are `Carry.kout` of the pins,
  with `c[0] = CI or CYINIT` (C's H_CARRY4_SIM).
* `carry4_c0` : **the one modelling difference.** The silicon's `c[0]` is the
  PRECYINIT configuration mux (`Carry.precy`), C's is `CI or CYINIT`. They agree
  for every configuration under the tie-off C's decoder uses (`genTie`: the
  unused one of CI/CYINIT is 0; C-11f-design-import.md "CARRY4"), and differ
  when both are non-zero (`carry4_c0_differs`), which a decoded bitstream
  cannot produce.

Hypotheses: none beyond the cell being of that kind with no inverted pins
(`inv = []`; C's importer sets `inv` only on flip-flops and latches).
Not covered: timing (C's interpreter has none); the binary reading follows from
`kout_ofBool`/`Lut.keval_ofBoolVec` and is not restated.
-/

namespace Formal.Core.Prims.GenCheck

open Formal.Core Formal.Core.K3 Formal.Net.CoreLut Formal.Gen Formal.Core.Prims

theorem mux2_eq_kmux : ∀ s a b : K3, mux2 s a b = kmux s a b := by
  intro s a b; cases s <;> rfl

theorem kevalL_mux (a b s : K3) : kevalL MUX_INIT [a, b, s] = mux2 s a b := by
  rw [mux_kleene, mux2_eq_kmux]

theorem kevalL_or2 : ∀ a b : K3, kevalL OR2_INIT [a, b] = K3.or a b := by decide +kernel

theorem kevalL_xor2 : ∀ a b : K3, kevalL XOR2_INIT [a, b] = kxor a b := by decide +kernel

/-! ## MUXF7 / MUXF8 -/

theorem muxf_eq (c : Cell) (hk : c.kind = .muxf7 ∨ c.kind = .muxf8) (hinv : c.inv = [])
    (a b s : K3) : c.out kleeneSem .O [a, b, s] = some (mux2 s a b) := by
  rcases hk with hk | hk <;>
    simp only [Cell.out, hk, hinv, List.isEmpty_nil, ite_true, kleeneSem, kevalL_mux]

/-! ## LUT6_2 -/

theorem lut62Of_o6 (init : Nat) : (lut62Of init).o6 = lutOf init 6 := rfl

theorem lut62Of_o5 (init : Nat) : (lut62Of init).o5 = lutOf (init % 2 ^ 32) 5 := by
  show (⟨(BitVec.ofNat 64 init).setWidth 32⟩ : Lut 5) = ⟨BitVec.ofNat 32 (init % 2 ^ 32)⟩
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_mod_of_dvd _ (by decide : 2 ^ 32 ∣ 2 ^ 64), Nat.mod_mod]

theorem lut62_o6_eq (c : Cell) (hk : c.kind = .lut6_2) (hinv : c.inv = [])
    (a0 a1 a2 a3 a4 a5 : K3) :
    c.out kleeneSem .O6 [a0, a1, a2, a3, a4, a5] =
      some (L62.o6Tree (lut62Of c.init) (kvec [a0, a1, a2, a3, a4, a5] 6)) := by
  rw [L62.o6Tree_eq_keval, lut62Of_o6]
  simp only [Cell.out, hk, hinv, List.isEmpty_nil, ite_true, kleeneSem]
  rfl

theorem lut62_o5_eq (c : Cell) (hk : c.kind = .lut6_2) (hinv : c.inv = [])
    (a0 a1 a2 a3 a4 a5 : K3) :
    c.out kleeneSem .O5 [a0, a1, a2, a3, a4, a5] =
      some (L62.o5Tree (lut62Of c.init) (kvec [a0, a1, a2, a3, a4, a5] 6)) := by
  rw [L62.o5Tree_eq_keval, lut62Of_o5]
  simp only [Cell.out, hk, hinv, List.isEmpty_nil, ite_true, kleeneSem]
  rfl

/-! ## CARRY4 -/

/-- The Core pin vector from C's pin list `[CI, CYINIT, DI0..3, S0..3]`, with
C's `c[0] = CI or CYINIT`. -/
def c4vec (ci cy d0 d1 d2 d3 s0 s1 s2 s3 : K3) : Fin 9 → K3 :=
  kvec [K3.or ci cy, d0, d1, d2, d3, s0, s1, s2, s3] 9

/-- C's output pin for a Core output. -/
def outPin : COut → Pin
  | .o0 => .O0 | .o1 => .O1 | .o2 => .O2 | .o3 => .O3
  | .co0 => .CO0 | .co1 => .CO1 | .co2 => .CO2 | .co3 => .CO3

theorem carry4_eq (c : Cell) (hk : c.kind = .carry4) (hinv : c.inv = [])
    (ci cy d0 d1 d2 d3 s0 s1 s2 s3 : K3) (o : COut) :
    c.out kleeneSem (outPin o) [ci, cy, d0, d1, d2, d3, s0, s1, s2, s3] =
      some (kout (c4vec ci cy d0 d1 d2 d3 s0 s1 s2 s3) o) := by
  cases o <;>
    simp [Cell.out, hk, hinv, carries, kleeneSem, outPin, kevalL_mux, kevalL_or2,
      kevalL_xor2, kout, kc1, kc2, kc3, kc4, c4vec, Formal.Core.ofList] <;> rfl

/-- C-11f's decode of the PRECYINIT bits into C's `(CI, CYINIT)` pins. -/
def genTie : PreCy → K3 → K3 → K3 × K3
  | .cin, ci, _ => (ci, .zero)
  | .ax, _, ax => (.zero, ax)
  | .zero, _, _ => (.zero, .zero)
  | .one, _, _ => (.zero, .one)

/-- Under that decode C's `CI or CYINIT` is the PRECYINIT mux, for every
configuration and every (Kleene) value. -/
theorem carry4_c0 : ∀ (cfg : PreCy) (ci ax : K3),
    K3.or (genTie cfg ci ax).1 (genTie cfg ci ax).2 = precy cfg ci ax := by
  intro cfg ci ax; cases cfg <;> cases ci <;> cases ax <;> rfl

/-- Outside that decode the two differ: with `CI = 1` and `CYINIT = 0` driven
together, the OR gives 1, a PRECYINIT mux set to `AX` (= CYINIT) gives 0. -/
theorem carry4_c0_differs : K3.or .one .zero ≠ precy .ax .one .zero := by decide

end Formal.Core.Prims.GenCheck
