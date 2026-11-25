import Formal.Core.Prims.Muxf

/-!
# Formal.Core.Prims.Carry — CARRY4 as its MUXCY/XORCY chain (Kleene, timed)

Shard A, probe PrimsComb (north star 1). Core Lean only (no Mathlib).
Notes: `formal/notes/A-prims-comb.md`.

## Model

A 7-series CARRY4 (UG474 "Carry Logic") is four MUXCY and four XORCY stages:
`c[i+1] = S[i] ? c[i] : DI[i]` (`CO[i] = c[i+1]`) and `O[i] = S[i] xor c[i]`.
The carry-in `c[0]` comes from the site's PRECYINIT mux, a *configuration* mux
(bitstream bits) choosing `0`, `1`, `AX` or `CIN` (`PreCy`); it is static during
operation and modelled as a selection, not as logic.

* Values: a pin vector `v : Fin 9 → K3`, index `0` = `c[0]` (the PRECYINIT
  output), `1..4` = `DI0..DI3`, `5..8` = `S0..S3`.
* Each MUXCY is the pass-transistor 2:1 mux `mux2` of `Muxf.lean` (same
  hypothesis **H_MUXF_PASS**, here **H_MUXCY_PASS**): select `X` with equal data
  passes the data. Each XORCY is the exact Kleene XOR `kxor` (`X` if either
  input is `X`). `kout` is therefore the pin-wise Kleene extension of the
  Boolean chain `bout`.
* Timing (**H_C4_PERPIN**): prjxray gives only end-to-end IOPATHs `pin -> out`
  per CARRY4 variant, not the internal stage delays. So each output is modelled
  as `kout` of the nine pins, each delayed by ITS OWN arc to that output
  (`Timed`, the per-pin transport model used for SDF IOPATHs). `support_matches_xray`
  checks that the model's dependency structure is exactly prjxray's arc list.

## Results

* `kout_ofBool`, `kout_mono`, `kout_contain`: Boolean agreement, monotonicity,
  X containment.
* `adder`: with `S = a xor b`, `DI = a` (yosys' `$alu` mapping), `O0..O3, CO3`
  are `a + b + c0` (all 512 cases).
* `kout_sic`: **no function hazard on any single-pin change** (each output is a
  read-once formula of the pins): if one pin moves and the output's old and
  new Boolean values agree, the Kleene value with that pin `X` is that value.
  With `Timed.sound` this gives glitch freedom for ANY delays (`sic_glitch_free`).
* `two_pin_hazard`: an operand-bit change of an adder moves `S[i]` and `DI[i]`
  together; the carry out is unchanged but its Kleene value is `X`.
  `co0_glitch` is the timed trace: with admissible SLICEL fast-corner delays
  (S0->CO0 89 ps, DI0->CO0 112 ps, both inside prjxray's bands) the carry out
  glitches to 0 on `[89, 112)`; `co0_no_glitch_other_order` shows the opposite
  arrival order does not glitch. prjxray's bands overlap, so neither order is
  excluded by the data.
* `support_matches_xray`: output `o` depends on pin `i` in the Boolean model iff
  prjxray (SLICEL, some CARRY4 variant) lists an arc `i -> o` (CIN and CYINIT
  both stand for `c[0]`).

## Not covered
The internal stage delays (prjxray has none), slews, the PRECYINIT bits
changing during operation, and the CARRY4 variants' meaning (`_LBOTH`/`_LFF`
are prjxray fuzzer names; `Hops.lean` takes the hull over variants).
-/

namespace Formal.Core.Prims

open Formal.Core K3

/-! ## XORCY -/

/-- Kleene XOR (the exact extension: defined iff both inputs are). -/
def kxor : K3 → K3 → K3
  | .zero, b => b
  | .one, b => K3.not b
  | .X, _ => .X

theorem kxor_ofBool (a b : Bool) : kxor (ofBool a) (ofBool b) = ofBool (a ^^ b) := by
  cases a <;> cases b <;> rfl

theorem kxor_mono {a b a' b' : K3} (ha : a ⊑ a') (hb : b ⊑ b') : kxor a b ⊑ kxor a' b' := by
  revert ha hb; cases a <;> cases b <;> cases a' <;> cases b' <;> decide

/-! ## PRECYINIT -/

/-- The PRECYINIT configuration (bitstream): carry-in from constant 0, 1, the
`AX` bypass pin, or `CIN` (the previous CARRY4's `CO3`). -/
inductive PreCy where
  | zero | one | ax | cin
  deriving DecidableEq, Repr

/-- `c[0]` for a configuration, given the `CIN` and `AX` values. -/
def precy : PreCy → K3 → K3 → K3
  | .zero, _, _ => .zero
  | .one, _, _ => .one
  | .ax, _, ax => ax
  | .cin, ci, _ => ci

/-! ## The chain -/

/-- Carries `c[1..4]` (`CO0..CO3`) of the Kleene chain. -/
def kc1 (v : Fin 9 → K3) : K3 := mux2 (v 5) (v 1) (v 0)
def kc2 (v : Fin 9 → K3) : K3 := mux2 (v 6) (v 2) (kc1 v)
def kc3 (v : Fin 9 → K3) : K3 := mux2 (v 7) (v 3) (kc2 v)
def kc4 (v : Fin 9 → K3) : K3 := mux2 (v 8) (v 4) (kc3 v)

/-- Kleene CARRY4 outputs. -/
def kout (v : Fin 9 → K3) : COut → K3
  | .o0 => kxor (v 5) (v 0)
  | .o1 => kxor (v 6) (kc1 v)
  | .o2 => kxor (v 7) (kc2 v)
  | .o3 => kxor (v 8) (kc3 v)
  | .co0 => kc1 v
  | .co1 => kc2 v
  | .co2 => kc3 v
  | .co3 => kc4 v

/-- Boolean CARRY4 (`S ? c : DI`, `S xor c`). -/
def bc1 (x : Fin 9 → Bool) : Bool := bmux (x 5) (x 1) (x 0)
def bc2 (x : Fin 9 → Bool) : Bool := bmux (x 6) (x 2) (bc1 x)
def bc3 (x : Fin 9 → Bool) : Bool := bmux (x 7) (x 3) (bc2 x)
def bc4 (x : Fin 9 → Bool) : Bool := bmux (x 8) (x 4) (bc3 x)

def bout (x : Fin 9 → Bool) : COut → Bool
  | .o0 => x 5 ^^ x 0
  | .o1 => x 6 ^^ bc1 x
  | .o2 => x 7 ^^ bc2 x
  | .o3 => x 8 ^^ bc3 x
  | .co0 => bc1 x
  | .co1 => bc2 x
  | .co2 => bc3 x
  | .co3 => bc4 x

instance decForallCOut {P : COut → Prop} [DecidablePred P] : Decidable (∀ o, P o) :=
  if h : P .o0 ∧ P .o1 ∧ P .o2 ∧ P .o3 ∧ P .co0 ∧ P .co1 ∧ P .co2 ∧ P .co3 then
    isTrue (fun o => by cases o <;> simp_all)
  else
    isFalse (fun H => h ⟨H _, H _, H _, H _, H _, H _, H _, H _⟩)

theorem kout_ofBool (x : Fin 9 → Bool) (o : COut) :
    kout (ofBoolVec x) o = ofBool (bout x o) := by
  cases o <;> simp only [kout, bout, kc1, kc2, kc3, kc4, bc1, bc2, bc3, bc4, ofBoolVec,
    mux2_ofBool, kxor_ofBool]

theorem kout_mono {u v : Fin 9 → K3} (h : VLe u v) (o : COut) : kout u o ⊑ kout v o := by
  have h1 : kc1 u ⊑ kc1 v := mux2_mono (h 5) (h 1) (h 0)
  have h2 : kc2 u ⊑ kc2 v := mux2_mono (h 6) (h 2) h1
  have h3 : kc3 u ⊑ kc3 v := mux2_mono (h 7) (h 3) h2
  have h4 : kc4 u ⊑ kc4 v := mux2_mono (h 8) (h 4) h3
  cases o
  · exact kxor_mono (h 5) (h 0)
  · exact kxor_mono (h 6) h1
  · exact kxor_mono (h 7) h2
  · exact kxor_mono (h 8) h3
  · exact h1
  · exact h2
  · exact h3
  · exact h4

/-- X containment: a defined Kleene output is the Boolean output of every
resolution of the pins. -/
theorem kout_contain {v : Fin 9 → K3} {x : Fin 9 → Bool} (h : Consistent v x) (o : COut) :
    kout v o ⊑ ofBool (bout x o) :=
  kout_ofBool x o ▸ kout_mono h o

/-! ## The adder (yosys `$alu` -> CARRY4 mapping) -/

/-- Pins for `a + b + ci` on 4 bits: `c0 = ci`, `DI[i] = a[i]`, `S[i] = a[i] xor b[i]`. -/
def addVec (a b : Nat) (ci : Bool) : Fin 9 → Bool := fun i =>
  match i.val with
  | 0 => ci
  | 1 => a.testBit 0 | 2 => a.testBit 1 | 3 => a.testBit 2 | 4 => a.testBit 3
  | 5 => a.testBit 0 ^^ b.testBit 0 | 6 => a.testBit 1 ^^ b.testBit 1
  | 7 => a.testBit 2 ^^ b.testBit 2 | _ => a.testBit 3 ^^ b.testBit 3

/-- The value of `O0..O3` plus `16 * CO3`. -/
def sumOf (x : Fin 9 → Bool) : Nat :=
  (bout x .o0).toNat + 2 * (bout x .o1).toNat + 4 * (bout x .o2).toNat +
    8 * (bout x .o3).toNat + 16 * (bout x .co3).toNat

/-- The chain is a 4-bit adder (all 512 cases). -/
theorem adder : ∀ a, a < 16 → ∀ b, b < 16 → ∀ ci : Bool,
    sumOf (addVec a b ci) = a + b + ci.toNat := by decide

/-! ## Hazards -/

/-- **No function hazard on any single-pin change** (all 512 × 9 × 8 cases): the
pin moving is `X`, every other pin is defined; if the Boolean output is the same
for both values of that pin, the Kleene output is that value. -/
theorem kout_sic : ∀ (x : Fin 9 → Bool) (j : Fin 9) (o : COut),
    bout x o = bout (setAt x j (!x j)) o →
    kout (setAt (ofBoolVec x) j .X) o = ofBool (bout x o) := by
  decide +kernel

/-- **Two-pin hazard of the adder.** `a[0]` flips `0 -> 1` with `b[0] = 1` and a
carry in of 1: `S0` goes `1 -> 0` and `DI0` goes `0 -> 1` together. `CO0` is 1
before and after, but its Kleene value over the transition is `X`. -/
theorem two_pin_hazard :
    bout (addVec 0 1 true) .co0 = true ∧ bout (addVec 1 1 true) .co0 = true ∧
    kout (setAt (setAt (ofBoolVec (addVec 0 1 true)) 1 .X) 5 .X) .co0 = .X := by
  decide

/-! ## Timed: per-pin transport -/

/-- A generic `n`-pin primitive output under per-pin transport: pin waveforms,
one delay per pin (to THIS output), the output waveform. -/
structure Timed (n : Nat) where
  pin : Fin n → Wave
  d : Fin n → Int
  y : Wave

namespace Timed

variable {n : Nat}

/-- **H_PERPIN_TRANSPORT** for output function `f`: at every instant the
output is at least as defined as `f` of the pins, each delayed by its own arc. -/
def H (f : (Fin n → K3) → K3) (T : Timed n) : Prop :=
  ∀ τ, f (fun i => T.pin i (τ - T.d i)) ⊑ T.y τ

/-- The exact instance (the output IS `f` of the delayed pins). -/
def exact (f : (Fin n → K3) → K3) (pin : Fin n → Wave) (d : Fin n → Int) : Timed n :=
  ⟨pin, d, fun τ => f (fun i => pin i (τ - d i))⟩

theorem exact_H (f : (Fin n → K3) → K3) (pin : Fin n → Wave) (d : Fin n → Int) :
    (exact f pin d).H f := fun _ => le_refl _

/-- Soundness for ANY delays, for a monotone `f`. -/
theorem sound {f : (Fin n → K3) → K3} (hf : ∀ u v, VLe u v → f u ⊑ f v) {T : Timed n}
    (h : T.H f) {v : Fin n → K3} (hv : ∀ i, MuxTimed.Abs (v i) (T.pin i)) (τ : Int) :
    f v ⊑ T.y τ :=
  le_trans (hf _ _ (fun i => hv i _)) (h τ)

end Timed

/-- **Single-pin-change glitch freedom of a CARRY4 output, any delays.** All pins
but `j` hold their Boolean value; pin `j` may do anything (any edge, mid-rail,
ringing). If the output's old and new values agree, it never leaves that value. -/
theorem sic_glitch_free (o : COut) (T : Timed 9) (h : T.H (fun v => kout v o))
    (x : Fin 9 → Bool) (j : Fin 9) (hsame : bout x o = bout (setAt x j (!x j)) o)
    (hpins : ∀ i, i ≠ j → ∀ τ, T.pin i τ = ofBool (x i)) (τ : Int) :
    T.y τ = ofBool (bout x o) := by
  have hv : ∀ i, MuxTimed.Abs (setAt (ofBoolVec x) j .X i) (T.pin i) := by
    intro i τ'
    by_cases e : i = j
    · simp only [setAt, e, ite_true]; exact X_le _
    · simp only [setAt, e, ite_false, ofBoolVec]; rw [hpins i e τ']; exact le_refl _
  have := Timed.sound (fun u v huv => kout_mono huv o) h hv τ
  rw [kout_sic x j o hsame] at this
  exact ofBool_le_iff.mp this

/-- The two-pin hazard as a timed trace. Pins: `c0 = 1`, `S0` steps `1 -> 0` and
`DI0` steps `0 -> 1` at pin time 0, everything else 0. With `S0 -> CO0` faster
than `DI0 -> CO0` (`dS < dD`) the carry out is 1, then 0 on `[dS, dD)`, then 1. -/
def co0Pins : Fin 9 → Wave := fun i =>
  match i.val with
  | 0 => fun _ => .one
  | 1 => step false true 0
  | 5 => step true false 0
  | _ => fun _ => .zero

def co0Delays (dD dS : Int) : Fin 9 → Int := fun i =>
  match i.val with
  | 1 => dD
  | 5 => dS
  | _ => 0

theorem co0Pins_0 : co0Pins 0 = fun _ => .one := rfl
theorem co0Pins_1 : co0Pins 1 = step false true 0 := rfl
theorem co0Pins_5 : co0Pins 5 = step true false 0 := rfl
theorem co0Delays_0 (dD dS : Int) : co0Delays dD dS 0 = 0 := rfl
theorem co0Delays_1 (dD dS : Int) : co0Delays dD dS 1 = dD := rfl
theorem co0Delays_5 (dD dS : Int) : co0Delays dD dS 5 = dS := rfl

theorem co0_glitch (dD dS : Int) (h : dS < dD) :
    let T := Timed.exact (fun v => kout v .co0) co0Pins (co0Delays dD dS)
    (∀ τ, τ < dS → T.y τ = .one) ∧ (∀ τ, dS ≤ τ → τ < dD → T.y τ = .zero) ∧
    (∀ τ, dD ≤ τ → T.y τ = .one) := by
  refine ⟨fun τ hτ => ?_, fun τ h1 h2 => ?_, fun τ hτ => ?_⟩
  · have e1 : τ - dD < 0 := by omega
    have e5 : τ - dS < 0 := by omega
    simp [Timed.exact, kout, kc1, co0Pins_0, co0Pins_1, co0Pins_5, co0Delays_0, co0Delays_1, co0Delays_5, step, e1, e5, mux2]
  · have e1 : τ - dD < 0 := by omega
    have e5 : ¬ τ - dS < 0 := by omega
    simp [Timed.exact, kout, kc1, co0Pins_0, co0Pins_1, co0Pins_5, co0Delays_0, co0Delays_1, co0Delays_5, step, e1, e5, mux2]
  · have e1 : ¬ τ - dD < 0 := by omega
    by_cases e5 : τ - dS < 0
    · simp [Timed.exact, kout, kc1, co0Pins_0, co0Pins_1, co0Pins_5, co0Delays_0, co0Delays_1, co0Delays_5, step, e1, e5, mux2]
    · simp [Timed.exact, kout, kc1, co0Pins_0, co0Pins_1, co0Pins_5, co0Delays_0, co0Delays_1, co0Delays_5, step, e1, e5, mux2]

/-- The opposite order (`DI0` first) never glitches. -/
theorem co0_no_glitch_other_order (dD dS : Int) (h : dD ≤ dS) (τ : Int) :
    (Timed.exact (fun v => kout v .co0) co0Pins (co0Delays dD dS)).y τ = .one := by
  by_cases e5 : τ - dS < 0
  · have e1 : τ - dD < 0 ∨ ¬ τ - dD < 0 := Classical.em _
    rcases e1 with e1 | e1 <;>
      simp [Timed.exact, kout, kc1, co0Pins_0, co0Pins_1, co0Pins_5, co0Delays_0, co0Delays_1, co0Delays_5, step, e1, e5, mux2]
  · have e1 : ¬ τ - dD < 0 := by omega
    simp [Timed.exact, kout, kc1, co0Pins_0, co0Pins_1, co0Pins_5, co0Delays_0, co0Delays_1, co0Delays_5, step, e1, e5, mux2]

/-- prjxray admits the glitching order at both corners (SLICEL): `S0 -> CO0`
(`CARRY4`) and `DI0 -> CO0` (`CARRY4_O5`, DI from the LUT's O5) overlap, and
`dS = S.lo`, `dD = DI.hi` are admissible with `dS < dD` (fast: 89 < 112,
glitch up to 23 ps; slow: 258 < 329, up to 71 ps). The other order is admissible
too (`DI.lo < S.hi`), so the data decides neither. -/
theorem co0_orders_admissible (c : Corner) :
    ∃ bS bD, carry4Arc .slicel .base .s0 .co0 = some bS ∧
      carry4Arc .slicel .o5 .di0 .co0 = some bD ∧
      bS.In c (bS.lo c) ∧ bD.In c (bD.hi c) ∧ bS.lo c < bD.hi c ∧ bD.lo c < bS.hi c := by
  cases c <;> exact ⟨_, _, rfl, rfl, by decide⟩

/-! ## The model's support equals prjxray's arc list -/

/-- Pins of the 9-vector as prjxray pins (`c0` is CIN or CYINIT). -/
def vPins : Fin 9 → List CPin := fun i =>
  match i.val with
  | 0 => [.cin, .cyinit]
  | 1 => [.di0] | 2 => [.di1] | 3 => [.di2] | 4 => [.di3]
  | 5 => [.s0] | 6 => [.s1] | 7 => [.s2] | _ => [.s3]

/-- prjxray (SLICEL) has an arc from some pin of `i` to `o` in some CARRY4 variant. -/
def xrayHasArc (i : Fin 9) (o : COut) : Bool :=
  (vPins i).all fun p => C4Var.all.any fun var => (carry4Arc .slicel var p o).isSome

/-- Output `o` depends on pin `i` in the Boolean chain. -/
def depends (i : Fin 9) (o : COut) : Prop := ∃ x : Fin 9 → Bool, bout x o ≠ bout (setAt x i (!x i)) o

instance (i : Fin 9) (o : COut) : Decidable (depends i o) :=
  decidable_of_iff (¬ ∀ x : Fin 9 → Bool, bout x o = bout (setAt x i (!x i)) o)
    (by unfold depends; exact ⟨fun h => Classical.byContradiction fun h' =>
      h fun x => Classical.byContradiction fun hx => h' ⟨x, hx⟩,
      fun ⟨x, hx⟩ h => hx (h x)⟩)

/-- **The dependency structure is prjxray's**: for all 9 × 8 (pin, output) pairs. -/
theorem support_matches_xray : ∀ (i : Fin 9) (o : COut), depends i o ↔ xrayHasArc i o = true := by
  decide +kernel

end Formal.Core.Prims
