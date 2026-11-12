import Formal.Cells.SpecCElem
import Formal.Timing.SpecLoop

/-!
# Formal.Cells.SpecCElemFact — the INIT facts of `SpecCElem` as a decidable check

Shard B, THE goal, S3.

## Problem, plainly
`SpecCElem.celem_forced` needs two facts about a gate's INIT (`hall`, `hhold`: "it is a C-element over the C
inputs `ci` with polarities `pol`, the other pins held at `ov`, the feedback on pin `j`"), quantified over
every pin assignment `v : Nat → Bool`. For a concrete gate of THE target's netlist they should be checkable by
`decide`, i.e. by looking at its `2^k` INIT addresses.

## Results
* `cfact k init j ci pol ov : Bool` (all `2^k` addresses checked).
* `hall_of_cfact`, `hhold_of_cfact`: `cfact ... = true` gives exactly `celem_forced`'s `hall` and `hhold`.
* `ctl151633_fact`: the link controller C-element of THE target named by allpaths.py (SLICE_X40Y49.ALUT.O6,
  INIT 0x08080e0e08080e0e, feedback pin 1, C inputs 0 and 4 with pin 4 inverted, pins 2, 3, 5 low) passes;
  `ctl151633_wrong_pol` (pin 0 inverted instead) fails: a negative control.

## Not covered
That the gate data are those of `DecodedPS.net` (a generated instance table does that); the environment.
-/

namespace Formal.Cells.SpecCElemFact

open Formal.Target Formal.Timing.SpecLoop

/-- The two INIT facts at one address `a` (bit `i` of `a` = pin `i`). -/
def cfactAt (k init j : Nat) (ci pol ov : Nat → Bool) (a : Nat) : Bool :=
  [false, true].all fun w =>
    (!((List.range k).all fun i => i == j || (ci i && ((a.testBit i ^^ pol i) == w)) ||
        (!ci i && (a.testBit i == ov i))) || init.testBit a == w) &&
    (!(a.testBit j == !w && ((List.range k).all fun i => i == j || ci i || (a.testBit i == ov i)) &&
        init.testBit a == w) ||
      (List.range k).all fun i => i == j || !ci i || ((a.testBit i ^^ pol i) == w))

/-- The INIT facts at every address. -/
def cfact (k init j : Nat) (ci pol ov : Nat → Bool) : Bool :=
  (List.range (2 ^ k)).all (cfactAt k init j ci pol ov)

theorem cfactAt_of {k init j : Nat} {ci pol ov : Nat → Bool} (h : cfact k init j ci pol ov = true)
    (v : Nat → Bool) : cfactAt k init j ci pol ov (addr k v) = true := by
  simp only [cfact, List.all_eq_true, List.mem_range] at h
  exact h _ (addr_lt k v)

theorem hall_of_cfact {k init j : Nat} {ci pol ov : Nat → Bool} (h : cfact k init j ci pol ov = true) :
    ∀ (w : Bool) (v : Nat → Bool), (∀ i, i < k → i ≠ j → ci i = true → (v i ^^ pol i) = w) →
      (∀ i, i < k → i ≠ j → ci i = false → v i = ov i) → init.testBit (addr k v) = w := by
  intro w v h1 h2
  have ha := cfactAt_of h v
  simp only [cfactAt, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at ha
  have hw : ∀ w : Bool, ((!((List.range k).all fun i => i == j || (ci i && (((addr k v).testBit i ^^ pol i) == w)) ||
        (!ci i && ((addr k v).testBit i == ov i)))) || init.testBit (addr k v) == w) = true := by
    intro w; cases w
    · exact ha.1.1
    · exact ha.2.1
  have hall' : ((List.range k).all fun i => i == j || (ci i && (((addr k v).testBit i ^^ pol i) == w)) ||
      (!ci i && ((addr k v).testBit i == ov i))) = true := by
    simp only [List.all_eq_true, List.mem_range]
    intro i hi
    rw [addr_testBit k v i hi]
    by_cases hij : i = j
    · simp [hij]
    · cases hc : ci i
      · simp [hij, hc, h2 i hi hij hc]
      · simp [hij, hc, h1 i hi hij hc]
  have := hw w
  rw [hall'] at this
  simpa using this

theorem hhold_of_cfact {k init j : Nat} {ci pol ov : Nat → Bool} (h : cfact k init j ci pol ov = true)
    (hj : j < k) :
    ∀ (w : Bool) (v : Nat → Bool), v j = !w →
      (∀ i, i < k → i ≠ j → ci i = false → v i = ov i) → init.testBit (addr k v) = w →
      ∀ i, i < k → i ≠ j → ci i = true → (v i ^^ pol i) = w := by
  intro w v hvj h2 hout i hi hij hci
  have ha := cfactAt_of h v
  simp only [cfactAt, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at ha
  have hw : ∀ w : Bool, (!((addr k v).testBit j == !w && ((List.range k).all fun i => i == j || ci i ||
        ((addr k v).testBit i == ov i)) && init.testBit (addr k v) == w) ||
      (List.range k).all fun i => i == j || !ci i || (((addr k v).testBit i ^^ pol i) == w)) = true := by
    intro w; cases w
    · exact ha.1.2
    · exact ha.2.2
  have hprem : ((addr k v).testBit j == !w && ((List.range k).all fun i => i == j || ci i ||
      ((addr k v).testBit i == ov i)) && init.testBit (addr k v) == w) = true := by
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range]
    refine ⟨⟨by rw [addr_testBit k v j hj, hvj], fun i' hi' => ?_⟩, hout⟩
    rw [addr_testBit k v i' hi']
    by_cases hij' : i' = j
    · simp [hij']
    · cases hc : ci i'
      · simp [hij', hc, h2 i' hi' hij' hc]
      · simp [hij', hc]
  have := hw w
  rw [hprem] at this
  simp only [Bool.not_true, Bool.false_or, List.all_eq_true, List.mem_range] at this
  have := this i hi
  rw [addr_testBit k v i hi] at this
  simpa [hij, hci] using this

/-- `ci`/`pol`/`ov` from lists (pin `i` = element `i`, default `false`). -/
def fl (l : List Bool) : Nat → Bool := fun i => l.getD i false

theorem ctl151633_fact :
    cfact 6 0x08080e0e08080e0e 1 (fl [true, false, false, false, true, false])
      (fl [false, false, false, false, true, false]) (fl [false, false, false, false, false, false]) = true := by
  decide

theorem ctl151633_wrong_pol :
    cfact 6 0x08080e0e08080e0e 1 (fl [true, false, false, false, true, false])
      (fl [true, false, false, false, false, false]) (fl [false, false, false, false, false, false]) = false := by
  decide

end Formal.Cells.SpecCElemFact
