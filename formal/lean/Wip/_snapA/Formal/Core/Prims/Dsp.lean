import Formal.Core.Kleene

/-!
# Formal.Core.Prims.Dsp — DSP48E1 in the one configuration ipow uses

Shard A, probe PrimsDSP (north star 1: "DSP48E1 ... if a design uses them"). Core Lean only
(no Mathlib, no `bv_decide`: it rests on `Lean.ofReduceBool`). Notes:
`formal/notes/A-prims-dsp.md`. Timing is in `Formal.Core.Prims.DspTimed`.

## What ipow's routed design contains (census, read from a routed build's netlists)

Six DSP48E1, two 32x32 multiplies (`ipow_kernel.v:220` `e0_data * e1_data` and `:277`
`e3_data * e4_data`), each a three-DSP cascade built by yosys `mul2dsp`/`xc7_dsp_map` with
17-bit unsigned slices (`DSP_A_MAXWIDTH_PARTIAL = 18`):

| cell | A port | B port | OPMODE (Z,Y,X) | PCIN | used outputs |
|---|---|---|---|---|---|
| head `sliceA[0].sliceB[0]` | a[16:0], A[29:17] = 0 | b[16:0], B[17] = 0 | 000 01 01: P = M | 0 | P[16:0] = y[16:0]; PCOUT; ACOUT |
| mid `sliceA[0].mul_sliceB_last` | A = 0, A_INPUT = CASCADE (ACIN = head ACOUT) | b[31:17], B[17:15] = 0 | 101 01 01: P = (PCIN >>> 17) + M | head PCOUT | PCOUT |
| tail `sliceA.last.sliceB[0]` | a[31:17], A[29:15] = 0 | b[16:0], B[17] = 0 | 001 01 01: P = PCIN + M | mid PCOUT | P[14:0] = y[31:17] |

Every cell: every pipeline register 0 (AREG ACASCREG BREG BCASCREG CREG MREG PREG ADREG DREG
INMODEREG OPMODEREG ALUMODEREG CARRYINREG CARRYINSELREG), INMODE = 00000, ALUMODE = 0000,
CARRYINSEL = 000, CARRYIN = 0, C = 0, D = 0, USE_MULT = MULTIPLY, USE_DPORT = FALSE,
USE_SIMD = ONE48, B_INPUT = DIRECT. So ipow's DSPs are **purely combinational**: no
registered stage is used (the research branch's registered model is not needed here).

The values are those of the yosys netlist; the routed netlist was checked to have every
`*REG = 0` on all six cells. That the bitstream realises exactly this configuration is
hypothesis **H_FASM_DSP** (`cells/flow.sh` runs `verify/fasm_audit.py`, which reads every
DSP48E1 register/const-pin bit back from the FASM; not re-run here).

## Function (UG479, this mode)

`M = signed(A[24:0]) * signed(B[17:0])` (`mulM`), `P = (Z + M) mod 2^48` (`pOut`), with
`Z = 0 | PCIN | PCIN >>> 17` (arithmetic shift) by OPMODE[6:4]; `PCOUT = P`;
`ACOUT = A` (A_INPUT DIRECT) or `ACIN` (CASCADE), ACASCREG = AREG = 0. This is the
expression of the research GLS's `DSP48E1_DSP48E1` g_mult branch (`P = z + {{5{m[42]}}, m}`).

## Results

* `ipow_cells_supported`: the three transcribed cells are in the modelled set
  (`Cfg.supported`); `ug479_default_registered`: the UG479 attribute defaults (registers 1) are
  NOT (so reading a missing register attribute as 0, as the audit found research's gen.py does,
  changes the cell's class).
* `ipowMul_eq`: **the three-DSP cascade computes C's 32-bit multiply**,
  `ipowMul a b = (a * b) % 2^32` for ALL naturals `a b` (by algebra: `omega` with the four
  partial products as atoms, `grind` for the ring expansion). `(a * b) % 2^32` is textually
  shard C's `Formal.Net.GcdHw.Ops.muli 32` (`GcdHwLib.lean:37`), i.e. the wrap-around `i32`
  multiply of the kernel's `int r = r * b` / `b = b * b` (C leaves signed overflow undefined;
  MLIR `arith.muli` on i32, which is what bdc reads, wraps; the low 32 bits of a product do not
  depend on signedness).
* X propagation (bit level, §4):
  - `coarse f`: any X input bit makes every output bit X. `coarse_ext`: it is a monotone
    Kleene extension of `f`; `coarse_le_ext`: it is below EVERY monotone extension (= the
    ternary semantics of every gate network computing `f`), so it is sound whatever the DSP's
    internal structure; `coarse_sound`: sound against every Boolean resolution;
    `poison`: for every gate network `g` and input bit `i`, adding `x_i xor x_i` gives another
    network for `f` whose output is X whenever `x_i` is, so no model that is more defined than
    `coarse` is sound for ALL realisations (`coarse_greatest`).
  - `lowBits_sound`: the sharper model "bit j of `(a*b) mod 2^32` is defined when bits 0..j of
    both operands are" is sound against every Boolean resolution (the function's exact
    Kleene extension), for every `j`.
  - `booth_breaks_lowBits`: but a radix-4 Booth partial-product cell (the structure of the
    DSP48E1 multiplier, UG479 "two partial products") realises bit 0 = a0 b0 as
    `((b0 a0) xor b1) xor b1`, which is X when `b1` is X although bit 0 never depends on `b1`.
    So `lowBits` is sound for the silicon only under the named hypothesis **H_DSP_LOWBITS**
    (the silicon is at least as defined as the function's low-bit cone); `coarse` needs no
    hypothesis.

## NOT covered
Signed operands (ipow ties A[24:17]/B[17] to 0, so `sext` is the identity there; the general
`mulM` is defined but only used on that range), other OPMODE/ALUMODE/INMODE values, CARRYOUT,
pattern detect, the registered pipeline (unused), the analogue behaviour of an X input.
-/

namespace Formal.Core.Prims.Dsp
open Formal.Core

/-! ## 1. Configuration -/

/-- The Z multiplexer selections ipow uses (OPMODE[6:4] = 000, 001, 101). -/
inductive ZSel where
  | zero
  | pcin
  | pcinShr17
  deriving DecidableEq, Repr

/-- The DSP48E1 attributes and constant control pins that decide its function, as the
yosys netlist gives them. Control buses as naturals, bit `i` = pin `i`. -/
structure Cfg where
  areg : Nat
  acascreg : Nat
  breg : Nat
  bcascreg : Nat
  creg : Nat
  mreg : Nat
  preg : Nat
  adreg : Nat
  dreg : Nat
  inmodereg : Nat
  opmodereg : Nat
  alumodereg : Nat
  carryinreg : Nat
  carryinselreg : Nat
  /-- `A_INPUT = CASCADE` (multiplier and ACOUT read ACIN). -/
  aCascade : Bool
  /-- `B_INPUT = CASCADE`. -/
  bCascade : Bool
  useDport : Bool
  useMultMultiply : Bool
  simdOne48 : Bool
  opmode : Nat
  alumode : Nat
  inmode : Nat
  carryinsel : Nat
  carryin : Nat
  deriving DecidableEq, Repr

/-- OPMODE[6:4] decoded, for the three values modelled here. -/
def Cfg.zsel (c : Cfg) : Option ZSel :=
  if c.opmode / 16 = 0 then some .zero
  else if c.opmode / 16 = 1 then some .pcin
  else if c.opmode / 16 = 5 then some .pcinShr17
  else none

/-- Every pipeline register bypassed. -/
def Cfg.combinational (c : Cfg) : Bool :=
  c.areg == 0 && c.acascreg == 0 && c.breg == 0 && c.bcascreg == 0 && c.creg == 0 &&
  c.mreg == 0 && c.preg == 0 && c.adreg == 0 && c.dreg == 0 && c.inmodereg == 0 &&
  c.opmodereg == 0 && c.alumodereg == 0 && c.carryinreg == 0 && c.carryinselreg == 0

/-- The modelled set: combinational, B direct, no pre-adder, MULTIPLY, ONE48, OPMODE X = Y = M
(OPMODE[3:0] = 0101) and Z in {0, PCIN, PCIN>>>17}, INMODE = ALUMODE = CARRYINSEL = CARRYIN = 0. -/
def Cfg.supported (c : Cfg) : Bool :=
  c.combinational && !c.bCascade && !c.useDport && c.useMultMultiply && c.simdOne48 &&
  decide (c.opmode < 128) && c.opmode % 16 == 5 && c.zsel.isSome &&
  c.alumode == 0 && c.inmode == 0 && c.carryinsel == 0 && c.carryin == 0

/-- The values shared by the three ipow cells (yosys netlist of the ipow_hw build, see notes). -/
def base : Cfg :=
  { areg := 0, acascreg := 0, breg := 0, bcascreg := 0, creg := 0, mreg := 0, preg := 0,
    adreg := 0, dreg := 0, inmodereg := 0, opmodereg := 0, alumodereg := 0, carryinreg := 0,
    carryinselreg := 0, aCascade := false, bCascade := false, useDport := false,
    useMultMultiply := true, simdOne48 := true, opmode := 0, alumode := 0, inmode := 0,
    carryinsel := 0, carryin := 0 }

/-- Head: OPMODE = 0000101. -/
def head : Cfg := { base with opmode := 5 }
/-- Middle: OPMODE = 1010101, A_INPUT = CASCADE. -/
def mid : Cfg := { base with opmode := 85, aCascade := true }
/-- Tail: OPMODE = 0010101. -/
def tail : Cfg := { base with opmode := 21 }

theorem ipow_cells_supported : head.supported ∧ mid.supported ∧ tail.supported := by decide

theorem ipow_cells_zsel :
    head.zsel = some .zero ∧ mid.zsel = some .pcinShr17 ∧ tail.zsel = some .pcin := by decide

/-- The UG479 attribute defaults: AREG = ACASCREG = BREG = BCASCREG = CREG = MREG = PREG =
INMODEREG = OPMODEREG = ALUMODEREG = CARRYINREG = CARRYINSELREG = ADREG = DREG = 1. -/
def ug479Default : Cfg :=
  { base with areg := 1, acascreg := 1, breg := 1, bcascreg := 1, creg := 1, mreg := 1,
    preg := 1, adreg := 1, dreg := 1, inmodereg := 1, opmodereg := 1, alumodereg := 1,
    carryinreg := 1, carryinselreg := 1 }

/-- A cell left on the UG479 defaults is registered, so a reader that maps a missing register
attribute to 0 puts it in the wrong class (audit row on research d4896fe, item b). -/
theorem ug479_default_registered :
    ug479Default.combinational = false ∧ ug479Default.supported = false := by decide

/-! ## 2. The function of this mode -/

/-- Two's-complement value of the low 25 bits (A[24:0]). -/
def sext25 (x : Nat) : Int :=
  if x % 2 ^ 25 < 2 ^ 24 then ((x % 2 ^ 25 : Nat) : Int) else ((x % 2 ^ 25 : Nat) : Int) - 2 ^ 25

/-- Two's-complement value of the low 18 bits (B[17:0]). -/
def sext18 (x : Nat) : Int :=
  if x % 2 ^ 18 < 2 ^ 17 then ((x % 2 ^ 18 : Nat) : Int) else ((x % 2 ^ 18 : Nat) : Int) - 2 ^ 18

/-- Two's-complement value of the low 48 bits (PCIN[47:0]). -/
def sext48 (x : Nat) : Int :=
  if x % 2 ^ 48 < 2 ^ 47 then ((x % 2 ^ 48 : Nat) : Int) else ((x % 2 ^ 48 : Nat) : Int) - 2 ^ 48

/-- The multiplier: `signed(A[24:0]) * signed(B[17:0])` (43-bit signed result). -/
def mulM (a b : Nat) : Int := sext25 a * sext18 b

/-- The Z operand. `PCIN >>> 17` is the arithmetic shift (`Int./` by a positive power of two
is floor division). -/
def zval : ZSel → Nat → Int
  | .zero, _ => 0
  | .pcin, p => ((p % 2 ^ 48 : Nat) : Int)
  | .pcinShr17, p => sext48 p / 2 ^ 17

/-- A 48-bit result as an unsigned word. -/
def u48 (i : Int) : Nat := (i % 2 ^ 48).toNat

/-- `P = PCOUT = (Z + M) mod 2^48` (ALUMODE = 0000: Z + X + Y + CIN with X + Y = M, CIN = 0). -/
def pOut (z : ZSel) (a b pcin : Nat) : Nat := u48 (zval z pcin + mulM a b)

/-- `ACOUT` with ACASCREG = AREG = 0: the A operand actually used. -/
def acoutF (cascade : Bool) (a acin : Nat) : Nat := if cascade then acin % 2 ^ 30 else a % 2 ^ 30

theorem pOut_lt (z : ZSel) (a b p : Nat) : pOut z a b p < 2 ^ 48 := by
  unfold pOut u48; omega

theorem u48_nat (n : Nat) (h : n < 2 ^ 48) : u48 (n : Int) = n := by
  unfold u48; omega

theorem sext25_small (a : Nat) (h : a < 2 ^ 24) : sext25 a = a := by
  unfold sext25; split <;> omega

theorem sext18_small (b : Nat) (h : b < 2 ^ 17) : sext18 b = b := by
  unfold sext18; split <;> omega

theorem zval_shr (p : Nat) (h : p < 2 ^ 47) : zval .pcinShr17 p = ((p / 2 ^ 17 : Nat) : Int) := by
  unfold zval sext48; split <;> omega

theorem zval_pcin (p : Nat) (h : p < 2 ^ 48) : zval .pcin p = (p : Int) := by
  unfold zval; omega

/-- On non-negative operands that fit (A < 2^24, B < 2^17) and a non-negative Z with no
48-bit overflow, the DSP is the natural-number `Z + A * B`. -/
theorem pOut_nat (z : ZSel) (a b p zn : Nat) (ha : a < 2 ^ 24) (hb : b < 2 ^ 17)
    (hz : zval z p = (zn : Int)) (hs : zn + a * b < 2 ^ 48) : pOut z a b p = zn + a * b := by
  unfold pOut mulM
  rw [hz, sext25_small a ha, sext18_small b hb, ← Int.natCast_mul, ← Int.natCast_add]
  exact u48_nat _ hs

/-! ## 3. The three-DSP cascade is C's 32-bit multiply -/

/-- Low slice `x[16:0]`. -/
def lo17 (x : Nat) : Nat := x % 2 ^ 17
/-- High slice `x[31:17]`. -/
def hi15 (x : Nat) : Nat := x / 2 ^ 17 % 2 ^ 15

/-- Head P (= PCOUT): A = a[16:0], B = b[16:0], Z = 0. -/
def headP (a b : Nat) : Nat := pOut .zero (lo17 a) (lo17 b) 0
/-- Head ACOUT (A_INPUT DIRECT). -/
def headAc (a : Nat) : Nat := acoutF head.aCascade (lo17 a) 0
/-- Middle PCOUT: own A pins tied 0, multiplier reads ACIN = head ACOUT (A_INPUT CASCADE),
B = b[31:17], Z = head PCOUT >>> 17. -/
def midP (a b : Nat) : Nat := pOut .pcinShr17 (acoutF mid.aCascade 0 (headAc a)) (hi15 b) (headP a b)
/-- Tail P: A = a[31:17], B = b[16:0], Z = middle PCOUT. -/
def tailP (a b : Nat) : Nat := pOut .pcin (hi15 a) (lo17 b) (midP a b)

/-- The bundled 32-bit output `w_n36`: bits [16:0] = head P[16:0], [31:17] = tail P[14:0]. -/
def ipowMul (a b : Nat) : Nat := headP a b % 2 ^ 17 + 2 ^ 17 * (tailP a b % 2 ^ 15)

/-- C's (and shard C's `Ops.muli 32`) 32-bit wrap-around multiply. -/
def muli32 (a b : Nat) : Nat := (a * b) % 2 ^ 32

theorem mul_lt_of_lt {a b m n : Nat} (ha : a < m) (hb : b < n) : a * b < m * n := by
  have h := Nat.mul_le_mul (Nat.le_pred_of_lt ha) (Nat.le_pred_of_lt hb)
  have h2 : (m - 1) * (n - 1) < m * n := by
    have hm : 0 < m := by omega
    have hn : 0 < n := by omega
    have : (m - 1) * (n - 1) ≤ (m - 1) * n := Nat.mul_le_mul_left _ (by omega)
    have : (m - 1) * n < m * n := Nat.mul_lt_mul_of_pos_right (by omega) hn
    omega
  omega

theorem expand4 (a0 a1 b0 b1 : Nat) :
    (a0 + 131072 * a1) * (b0 + 131072 * b1)
      = a0 * b0 + 131072 * (a0 * b1 + a1 * b0) + 131072 * (131072 * (a1 * b1)) := by
  grind

/-- **The cascade computes the 32-bit product**, for every pair of naturals (only the low 32
bits of each operand are wired, and only they matter for the result). -/
theorem ipowMul_eq (a b : Nat) : ipowMul a b = muli32 a b := by
  have ha0 : lo17 a < 2 ^ 17 := Nat.mod_lt _ (by decide)
  have hb0 : lo17 b < 2 ^ 17 := Nat.mod_lt _ (by decide)
  have ha1 : hi15 a < 2 ^ 15 := Nat.mod_lt _ (by decide)
  have hb1 : hi15 b < 2 ^ 15 := Nat.mod_lt _ (by decide)
  have p00 : lo17 a * lo17 b < 2 ^ 34 := mul_lt_of_lt ha0 hb0
  have p01 : lo17 a * hi15 b < 2 ^ 32 := mul_lt_of_lt ha0 hb1
  have p10 : hi15 a * lo17 b < 2 ^ 32 := mul_lt_of_lt ha1 hb0
  have hH : headP a b = 0 + lo17 a * lo17 b :=
    pOut_nat .zero _ _ 0 0 (by omega) (by omega) rfl (by omega)
  have hAc : acoutF mid.aCascade 0 (headAc a) = lo17 a := by
    show (headAc a) % 2 ^ 30 = lo17 a
    show (lo17 a % 2 ^ 30) % 2 ^ 30 = lo17 a
    omega
  have hM : midP a b = (lo17 a * lo17 b) / 2 ^ 17 + lo17 a * hi15 b := by
    unfold midP
    rw [hAc]
    exact pOut_nat .pcinShr17 _ _ _ _ (by omega) (by omega)
      (by rw [zval_shr _ (by omega), hH, Nat.zero_add]) (by omega)
  have hT : tailP a b = midP a b + hi15 a * lo17 b := by
    unfold tailP
    exact pOut_nat .pcin _ _ _ _ (by omega) (by omega) (zval_pcin _ (by omega)) (by omega)
  have hsplit : ∀ x : Nat, x % 2 ^ 32 = lo17 x + 131072 * hi15 x := by
    intro x; unfold lo17 hi15; omega
  have hprod : (a * b) % 2 ^ 32
      = (lo17 a * lo17 b + 131072 * (lo17 a * hi15 b + hi15 a * lo17 b)
          + 131072 * (131072 * (hi15 a * hi15 b))) % 2 ^ 32 := by
    rw [Nat.mul_mod, hsplit a, hsplit b, expand4]
    omega
  unfold ipowMul muli32
  rw [hprod, hT, hM, hH]
  omega

/-- Concrete vectors from the C source's own `main` (b = 3, e = 7 gives 3^7 = 2187, through
r*b and b*b) and two wrap-around cases, by evaluation. Expected values are C arithmetic, not
a run's output. -/
theorem ipowMul_examples :
    ipowMul 729 3 = 2187 ∧ ipowMul 81 81 = 6561 ∧
    ipowMul 4294967295 4294967295 = 1 ∧ ipowMul 1 4294967295 = 4294967295 ∧
    ipowMul 65536 65536 = 0 := by decide

/-! ## 4. X propagation at the bit level -/

section Kleene
open K3

variable {n m : Nat}

/-- `g` is a monotone Kleene extension of `f`: it agrees with `f` on Boolean inputs and is
monotone in the information order. The ternary simulation of any gate network computing `f`
from Kleene-monotone gates is such a `g` (Core `Ternary`/`Kleene`). -/
def Ext (f : (Fin n → Bool) → Fin m → Bool) (g : (Fin n → K3) → Fin m → K3) : Prop :=
  (∀ x j, g (fun i => ofBool (x i)) j = ofBool (f x j)) ∧
  (∀ u v : Fin n → K3, (∀ i, u i ⊑ v i) → ∀ j, g u j ⊑ g v j)

/-- The coarse model: any X input bit makes every output bit X. -/
def coarse (f : (Fin n → Bool) → Fin m → Bool) (v : Fin n → K3) (j : Fin m) : K3 :=
  if ∀ i, v i ≠ X then ofBool (f (fun i => pick (v i)) j) else X

theorem pick_ofBool (b : Bool) : pick (ofBool b) = b := by cases b <;> rfl

theorem eq_ofBool_pick {a : K3} (h : a ≠ X) : a = ofBool (pick a) := by
  cases a <;> first | rfl | exact absurd rfl h

theorem coarse_ext (f : (Fin n → Bool) → Fin m → Bool) : Ext f (coarse f) := by
  refine ⟨fun x j => ?_, fun u v huv j => ?_⟩
  · unfold coarse
    rw [if_pos (fun i => ofBool_ne_X (x i))]
    simp only [pick_ofBool]
  · unfold coarse
    by_cases hu : ∀ i, u i ≠ X
    · have hv : ∀ i, v i = u i := fun i => by
        rcases huv i with h | h
        · exact absurd h (hu i)
        · exact h.symm
      have hv' : ∀ i, v i ≠ X := fun i => by rw [hv i]; exact hu i
      rw [if_pos hu, if_pos hv']
      have : (fun i => pick (v i)) = (fun i => pick (u i)) := funext fun i => by rw [hv i]
      rw [this]; exact le_refl _
    · rw [if_neg hu]; exact X_le _

/-- `coarse` is below every monotone extension: sound for every internal realisation. -/
theorem coarse_le_ext {f : (Fin n → Bool) → Fin m → Bool} {g : (Fin n → K3) → Fin m → K3}
    (hg : Ext f g) (v : Fin n → K3) (j : Fin m) : coarse f v j ⊑ g v j := by
  unfold coarse
  by_cases hv : ∀ i, v i ≠ X
  · rw [if_pos hv]
    have : v = fun i => ofBool (pick (v i)) := funext fun i => eq_ofBool_pick (hv i)
    rw [this, hg.1]
    simp only [pick_ofBool]
    exact le_refl _
  · rw [if_neg hv]; exact X_le _

/-- `coarse` is sound against every Boolean resolution of its input. -/
theorem coarse_sound (f : (Fin n → Bool) → Fin m → Bool) (v : Fin n → K3) (x : Fin n → Bool)
    (hx : ∀ i, v i ⊑ ofBool (x i)) (j : Fin m) : coarse f v j ⊑ ofBool (f x j) := by
  have := (coarse_ext f).2 v (fun i => ofBool (x i)) hx j
  rwa [(coarse_ext f).1] at this

/-- Kleene XOR. -/
def kxor : K3 → K3 → K3
  | zero, zero => zero
  | zero, one => one
  | one, zero => one
  | one, one => zero
  | _, _ => X

theorem kxor_ofBool (a b : Bool) : kxor (ofBool a) (ofBool b) = ofBool (a != b) := by
  cases a <;> cases b <;> rfl

theorem kxor_mono {a b a' b' : K3} : a ⊑ a' → b ⊑ b' → kxor a b ⊑ kxor a' b' := by
  cases a <;> cases b <;> cases a' <;> cases b' <;> decide

theorem kxor_X_right (a : K3) : kxor a X = X := by cases a <;> rfl

/-- **Poisoning**: from any gate network `g` for `f` and any input bit `i`, the network
`g xor (x_i xor x_i)` also computes `f`, and outputs X on every bit whenever `x_i` is X. -/
theorem poison {f : (Fin n → Bool) → Fin m → Bool} {g : (Fin n → K3) → Fin m → K3}
    (hg : Ext f g) (i : Fin n) :
    Ext f (fun v j => kxor (g v j) (kxor (v i) (v i))) ∧
    ∀ v j, v i = X → kxor (g v j) (kxor (v i) (v i)) = X := by
  refine ⟨⟨fun x j => ?_, fun u v huv j => ?_⟩, fun v j hv => ?_⟩
  · simp only [hg.1, kxor_ofBool]
    cases f x j <;> cases x i <;> rfl
  · exact kxor_mono (hg.2 u v huv j) (kxor_mono (huv i) (huv i))
  · rw [hv]; exact kxor_X_right _

/-- `coarse` is the most defined model that is sound for every realisation: any model below
every monotone extension is below `coarse` (which is one), and at any input with an X bit it
must be X (`poison`). -/
theorem coarse_greatest {f : (Fin n → Bool) → Fin m → Bool}
    (M : (Fin n → K3) → Fin m → K3)
    (hM : ∀ g, Ext f g → ∀ v j, M v j ⊑ g v j) (v : Fin n → K3) (j : Fin m) :
    M v j ⊑ coarse f v j ∧ ((∃ i, v i = X) → M v j = X) := by
  refine ⟨hM _ (coarse_ext f) v j, fun ⟨i, hi⟩ => ?_⟩
  have h := hM _ (poison (coarse_ext f) i).1 v j
  rw [(poison (coarse_ext f) i).2 v j hi] at h
  rcases h with h | h <;> exact h

/-- A natural number `x` is a Boolean resolution of the Kleene word `v` (bit `i` = `v i`). -/
def Rep {k : Nat} (v : Fin k → K3) (x : Nat) : Prop := ∀ i : Fin k, v i ⊑ ofBool (x.testBit i)

/-- Two resolutions of a word agree on every bit whose Kleene value is defined. -/
theorem rep_bit_eq {k : Nat} {v : Fin k → K3} {x x' : Nat} (hx : Rep v x) (hx' : Rep v x')
    (i : Fin k) (hi : v i ≠ X) : x.testBit i = x'.testBit i := by
  have h1 : v i = ofBool (x.testBit i) := by
    rcases hx i with h | h
    · exact absurd h hi
    · exact h
  have h2 : v i = ofBool (x'.testBit i) := by
    rcases hx' i with h | h
    · exact absurd h hi
    · exact h
  exact ofBool_inj.mp (h1.symm.trans h2)

/-- Agreement on bits `0..j-1` gives agreement mod `2^j`. -/
theorem mod_eq_of_bits {x x' j : Nat} (h : ∀ i, i < j → x.testBit i = x'.testBit i) :
    x % 2 ^ j = x' % 2 ^ j := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases hi : i < j
  · rw [h i hi]
  · simp [hi]

/-- **Low-bit model, sound against the function**: if bits `0..j` of both 32-bit operands are
defined, bit `j` of the 32-bit product is the same for every Boolean resolution. -/
theorem lowBits_sound {va vb : Fin 32 → K3} {x x' y y' : Nat}
    (hx : Rep va x) (hx' : Rep va x') (hy : Rep vb y) (hy' : Rep vb y') (j : Nat)
    (hdef : ∀ i : Fin 32, i.val ≤ j → va i ≠ X ∧ vb i ≠ X) :
    (muli32 x y).testBit j = (muli32 x' y').testBit j := by
  unfold muli32
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases hj : j < 32
  · have ex : x % 2 ^ (j + 1) = x' % 2 ^ (j + 1) := mod_eq_of_bits fun i hi =>
      rep_bit_eq hx hx' ⟨i, by omega⟩ (hdef ⟨i, by omega⟩ (by simp; omega)).1
    have ey : y % 2 ^ (j + 1) = y' % 2 ^ (j + 1) := mod_eq_of_bits fun i hi =>
      rep_bit_eq hy hy' ⟨i, by omega⟩ (hdef ⟨i, by omega⟩ (by simp; omega)).2
    have ep : (x * y) % 2 ^ (j + 1) = (x' * y') % 2 ^ (j + 1) := by
      rw [Nat.mul_mod, ex, ey, ← Nat.mul_mod]
    have hb : ∀ z : Nat, z.testBit j = (z % 2 ^ (j + 1)).testBit j := fun z => by
      rw [Nat.testBit_mod_two_pow]; simp
    rw [hb (x * y), hb (x' * y'), ep]
  · simp [hj]

/-- The low-bit model as a Kleene value, given any one resolution `x, y` of the operands. -/
def lowK (va vb : Fin 32 → K3) (x y : Nat) (j : Fin 32) : K3 :=
  if ∀ i : Fin 32, i.val ≤ j.val → va i ≠ X ∧ vb i ≠ X then ofBool ((muli32 x y).testBit j) else X

theorem lowK_sound {va vb : Fin 32 → K3} {x x' y y' : Nat}
    (hx : Rep va x) (hx' : Rep va x') (hy : Rep vb y) (hy' : Rep vb y') (j : Fin 32) :
    lowK va vb x y j ⊑ ofBool ((muli32 x' y').testBit j) := by
  unfold lowK
  by_cases h : ∀ i : Fin 32, i.val ≤ j.val → va i ≠ X ∧ vb i ≠ X
  · rw [if_pos h, lowBits_sound hx hx' hy hy' j h]; exact le_refl _
  · rw [if_neg h]; exact X_le _

/-- Bit 0 of a radix-4 Booth partial product with the two's-complement correction
(digit 0: `one = b0`, `two = b1 & ~b0`, `neg = b1`; `pp0 = (one & a0) xor neg`, then `+ neg`). -/
def boothBit0 (a0 b0 b1 : K3) : K3 := kxor (kxor (K3.and b0 a0) b1) b1

theorem boothBit0_bool (a0 b0 b1 : Bool) :
    boothBit0 (ofBool a0) (ofBool b0) (ofBool b1) = ofBool (a0 && b0) := by
  cases a0 <;> cases b0 <;> cases b1 <;> rfl

theorem boothBit0_mono {a b c a' b' c' : K3} (h1 : a ⊑ a') (h2 : b ⊑ b') (h3 : c ⊑ c') :
    boothBit0 a b c ⊑ boothBit0 a' b' c' :=
  kxor_mono (kxor_mono (K3.and_mono h2 h1) h3) h3

/-- **The Booth structure breaks the low-bit model**: with `a0 = b0 = 1` and `b1 = X` the
function's bit 0 is 1 for every resolution, but the Booth cell gives X. -/
theorem booth_breaks_lowBits :
    boothBit0 one one X = X ∧ ∀ b1 : Bool, boothBit0 one one (ofBool b1) = one := by
  refine ⟨rfl, fun b1 => ?_⟩
  cases b1 <;> rfl

end Kleene

end Formal.Core.Prims.Dsp
