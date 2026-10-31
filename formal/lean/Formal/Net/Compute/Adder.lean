import Formal.Net.Compute.Word
import Formal.Net.GcdHwLib

/-!
# H_COMPUTE_FN, part 3: ripple-carry adders (CARRY4 chains) by cut points

`AddOK cells outs cuts`: a decidable certificate that a 32-bit unit is a ripple adder of
eight 4-bit slices: with the slice carry-outs `cuts` as cut points, output bit `i` (slice
`j = i / 4`) is checked exhaustively as bit `i % 4` of `A_j + B_j + c_j` over its 8 operand
bits and the incoming carry leaf, and each carry-out as `16 ≤ A_j + B_j + c_j`
(`A_j` = bits `4j..4j+3` of port 0, `B_j` of port 1). Each check evaluates only the cone of
its net (`eval_filt`).

`add_sound`: a passing certificate means the unit computes `Ops.addi 32 a b` for every `a, b`.
The certificate does not have to be trusted: `cut_sound` makes any choice of cut nets sound,
`local_sound` makes each check a statement about every environment, and the composition
(`nib_step`) is the generic ripple-carry arithmetic, proved once.
-/

namespace Formal.Net.Compute
open Formal.Net.GcdHw

/-! ## The certificate -/

def nibL (l : List Bool) (o : Nat) : Nat :=
  (l.getD o false).toNat + 2 * (l.getD (o + 1) false).toNat + 4 * (l.getD (o + 2) false).toNat +
    8 * (l.getD (o + 3) false).toNat

def sumL (l : List Bool) : Nat := nibL l 0 + nibL l 4 + (l.getD 8 false).toNat

def addS (cuts : List Nat) (j : Nat) : List Leaf :=
  [.inp 0 (4 * j), .inp 0 (4 * j + 1), .inp 0 (4 * j + 2), .inp 0 (4 * j + 3),
   .inp 1 (4 * j), .inp 1 (4 * j + 1), .inp 1 (4 * j + 2), .inp 1 (4 * j + 3)] ++
  (if j = 0 then [] else [.cut (cuts.getD (j - 1) 0)])

def cinC (cuts : List Nat) (j : Nat) : List Nat := if j = 0 then [] else [cuts.getD (j - 1) 0]

def outNet (outs : List W) (i : Nat) : Nat :=
  match outs.getD i .c0 with
  | .net n => n
  | _ => 0

/-- One net checked over its slice: local check on its cone, leaf list duplicate-free and
covering the cone's support. -/
def SliceOK (cells : List Cell) (cuts : List Nat) (j n : Nat) (spec : List Bool → Bool) : Prop :=
  LocalOK (cinC cuts j) (filt cells [n]).1 (.net n) (addS cuts j) spec ∧ (addS cuts j).Nodup ∧
    (swOf (cinC cuts j) (filt cells [n]).1 (.net n)).all (fun l => decide (l ∈ addS cuts j)) = true

instance (cells : List Cell) (cuts : List Nat) (j n : Nat) (spec : List Bool → Bool) :
    Decidable (SliceOK cells cuts j n spec) := by
  unfold SliceOK; exact inferInstance

def AddOK (cells : List Cell) (outs : List W) (cuts : List Nat) : Prop :=
  outs.length = 32 ∧ (cells.flatMap Cell.outs).Nodup ∧
  (∀ i, i < 32 → outs.getD i .c0 = .net (outNet outs i) ∧
    SliceOK cells cuts (i / 4) (outNet outs i) (fun l => (sumL l).testBit (i % 4))) ∧
  (∀ j, j < 7 → SliceOK cells cuts j (cuts.getD j 0) (fun l => decide (16 ≤ sumL l)))

/-! ## Ripple-carry arithmetic -/

theorem mod16_bits (x : Nat) : x % 16 = (x.testBit 0).toNat + 2 * (x.testBit 1).toNat +
    4 * (x.testBit 2).toNat + 8 * (x.testBit 3).toNat := by
  simp only [Nat.testBit_eq_decide_div_mod_eq]
  have h0 : x / 2 ^ 0 = x := by simp
  have h1 : x / 2 ^ 1 = x / 2 := by simp
  have h2 : x / 2 ^ 2 = x / 4 := rfl
  have h3 : x / 2 ^ 3 = x / 8 := rfl
  rw [h0, h1, h2, h3]
  rcases Nat.mod_two_eq_zero_or_one x with a | a <;>
  rcases Nat.mod_two_eq_zero_or_one (x / 2) with b | b <;>
  rcases Nat.mod_two_eq_zero_or_one (x / 4) with c | c <;>
  rcases Nat.mod_two_eq_zero_or_one (x / 8) with d | d <;>
  simp [a, b, c, d] <;> omega

/-- The slice nibble `A_j` from the bits of `a`. -/
theorem nib_bits (a j : Nat) :
    (a.testBit (4 * j)).toNat + 2 * (a.testBit (4 * j + 1)).toNat +
      4 * (a.testBit (4 * j + 2)).toNat + 8 * (a.testBit (4 * j + 3)).toNat =
    a / 2 ^ (4 * j) % 16 := by
  rw [mod16_bits]
  simp only [Nat.testBit_div_two_pow]
  simp only [Nat.zero_add, Nat.add_comm]

/-- The carry into bit `4j` of `a + b`. -/
def carryIn (a b j : Nat) : Nat := (a % 2 ^ (4 * j) + b % 2 ^ (4 * j)) / 2 ^ (4 * j)

theorem pow_step (j : Nat) : 2 ^ (4 * (j + 1)) = 2 ^ (4 * j) * 16 := by
  rw [show 4 * (j + 1) = 4 * j + 4 by omega, Nat.pow_add]

/-- **One slice of ripple-carry addition.** With `P = 2^(4j)`: the low `4(j+1)` bits of `a`
and `b` add to `P * (A_j + B_j + c_j) + (low remainder)`. -/
theorem slice_eq (a b j : Nat) :
    (a % 2 ^ (4 * (j + 1)) + b % 2 ^ (4 * (j + 1))) / 2 ^ (4 * j) =
      a / 2 ^ (4 * j) % 16 + b / 2 ^ (4 * j) % 16 + carryIn a b j := by
  rw [pow_step, Nat.mod_mul, Nat.mod_mul]
  have hP : 0 < 2 ^ (4 * j) := Nat.two_pow_pos _
  have e : a % 2 ^ (4 * j) + 2 ^ (4 * j) * (a / 2 ^ (4 * j) % 16) +
      (b % 2 ^ (4 * j) + 2 ^ (4 * j) * (b / 2 ^ (4 * j) % 16)) =
      (a % 2 ^ (4 * j) + b % 2 ^ (4 * j)) +
        2 ^ (4 * j) * (a / 2 ^ (4 * j) % 16 + b / 2 ^ (4 * j) % 16) := by
    rw [Nat.mul_add]; omega
  rw [e, Nat.add_mul_div_left _ _ hP, carryIn]
  omega

theorem carryIn_lt (a b j : Nat) : carryIn a b j < 2 := by
  have hP : 0 < 2 ^ (4 * j) := Nat.two_pow_pos _
  have h1 := Nat.mod_lt a hP
  have h2 := Nat.mod_lt b hP
  unfold carryIn
  apply (Nat.div_lt_iff_lt_mul hP).mpr
  omega

theorem carryIn_succ (a b j : Nat) :
    carryIn a b (j + 1) = (a / 2 ^ (4 * j) % 16 + b / 2 ^ (4 * j) % 16 + carryIn a b j) / 16 := by
  rw [← slice_eq]
  show (a % 2 ^ (4 * (j + 1)) + b % 2 ^ (4 * (j + 1))) / 2 ^ (4 * (j + 1)) = _
  rw [Nat.div_div_eq_div_mul, ← pow_step]

/-- Bit `4j + k` (`k < 4`) of `a + b` is bit `k` of `A_j + B_j + c_j`. -/
theorem add_bit (a b j k : Nat) (hk : k < 4) :
    (a + b).testBit (4 * j + k) =
      (a / 2 ^ (4 * j) % 16 + b / 2 ^ (4 * j) % 16 + carryIn a b j).testBit k := by
  have hlt : 4 * j + k < 4 * (j + 1) := by omega
  rw [← slice_eq, Nat.testBit_div_two_pow, Nat.add_comm k]
  have h1 : (a + b).testBit (4 * j + k) = ((a + b) % 2 ^ (4 * (j + 1))).testBit (4 * j + k) := by
    rw [Nat.testBit_mod_two_pow]; simp [hlt]
  have h2 : (a % 2 ^ (4 * (j + 1)) + b % 2 ^ (4 * (j + 1))).testBit (4 * j + k) =
      ((a % 2 ^ (4 * (j + 1)) + b % 2 ^ (4 * (j + 1))) % 2 ^ (4 * (j + 1))).testBit (4 * j + k) := by
    rw [Nat.testBit_mod_two_pow]; simp [hlt]
  rw [h1, h2, ← Nat.add_mod]

/-! ## Soundness -/

/-- The value of a checked slice net, from its certificate (any cut set, any cone). -/
theorem slice_val {cells : List Cell} {cuts : List Nat} {j n : Nat} {spec : List Bool → Bool}
    (hnd : (cells.flatMap Cell.outs).Nodup) (h : SliceOK cells cuts j n spec) (env : Leaf → Bool) :
    run env [] cells (fun _ => false) n =
      spec ((addS cuts j).map (fun l => match l with
        | .inp p k => env (.inp p k)
        | .cut m => run env [] cells (fun _ => false) m)) := by
  obtain ⟨hok, hS, hsup⟩ := h
  let env' : Leaf → Bool := fun l => match l with
    | .inp p k => env (.inp p k)
    | .cut m => run env [] cells (fun _ => false) m
  have hcut := cut_sound env env' (cinC cuts j) (fun _ _ => rfl) cells (fun _ => false) hnd
    (fun _ _ => rfl) n
  have h1 : eval env' (cinC cuts j) cells (.net n) = run env [] cells (fun _ => false) n := hcut
  rw [← h1, eval_filt]
  exact local_sound hok hS (fun l hl => by simpa using List.all_eq_true.mp hsup l hl) env'

theorem toNat_decide_le (s : Nat) (hs : s < 32) : (decide (16 ≤ s)).toNat = s / 16 := by
  by_cases h : 16 ≤ s
  · simp [h]; omega
  · simp [h]; omega

/-- **A certified ripple adder computes `a + b` (mod 2^32)** for every pair of inputs. -/
theorem add_sound {cells : List Cell} {outs : List W} {cuts : List Nat}
    (h : AddOK cells outs cuts) (a b : Nat) : unitVal cells outs [a, b] = Ops.addi 32 a b := by
  obtain ⟨hlen, hnd, hbits, hcar⟩ := h
  let env := inEnv [a, b]
  let R := run env [] cells (fun _ => false)
  -- the leaf values of slice `j`
  have hmap : ∀ j, (addS cuts j).map (fun l => match l with
      | .inp p k => env (.inp p k) | .cut m => R m) =
      [a.testBit (4 * j), a.testBit (4 * j + 1), a.testBit (4 * j + 2), a.testBit (4 * j + 3),
       b.testBit (4 * j), b.testBit (4 * j + 1), b.testBit (4 * j + 2), b.testBit (4 * j + 3)] ++
      (if j = 0 then [] else [R (cuts.getD (j - 1) 0)]) := by
    intro j
    simp only [addS, List.map_append, List.map_cons, List.map_nil]
    by_cases hj : j = 0 <;> simp [hj, env, inEnv]
  have hsum : ∀ j, sumL ((addS cuts j).map (fun l => match l with
      | .inp p k => env (.inp p k) | .cut m => R m)) =
      a / 2 ^ (4 * j) % 16 + b / 2 ^ (4 * j) % 16 +
        (if j = 0 then 0 else (R (cuts.getD (j - 1) 0)).toNat) := by
    intro j
    rw [hmap j, ← nib_bits a j, ← nib_bits b j]
    by_cases hj : j = 0 <;> simp [hj, sumL, nibL]
  -- the real carries are the arithmetic carries
  have hc : ∀ j, j ≤ 7 →
      (if j = 0 then 0 else (R (cuts.getD (j - 1) 0)).toNat) = carryIn a b j := by
    intro j
    induction j with
    | zero => intro _; simp [carryIn, Nat.mod_one]
    | succ j ih =>
      intro hj
      have hv := slice_val hnd (hcar j (by omega)) env
      simp only [Nat.add_sub_cancel, Nat.add_one_ne_zero, if_false]
      show (R (cuts.getD j 0)).toNat = _
      rw [show R (cuts.getD j 0) = _ from hv, hsum j, ih (by omega), carryIn_succ]
      apply toNat_decide_le
      have := carryIn_lt a b j
      have := Nat.mod_lt (a / 2 ^ (4 * j)) (show 16 > 0 by decide)
      have := Nat.mod_lt (b / 2 ^ (4 * j)) (show 16 > 0 by decide)
      omega
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_unitVal, hlen, Ops.addi, Nat.testBit_mod_two_pow]
  by_cases hi : i < 32
  · simp only [hi, decide_true, Bool.true_and]
    obtain ⟨hw, hs⟩ := hbits i hi
    have hv := slice_val hnd hs env
    have hj : i / 4 ≤ 7 := by omega
    have e : eval env [] cells (outs.getD i .c0) = R (outNet outs i) := by
      rw [hw]; rfl
    rw [e, show R (outNet outs i) = _ from hv, hsum, hc _ hj]
    have hi4 : i = 4 * (i / 4) + i % 4 := by omega
    conv => rhs; rw [hi4]
    rw [add_bit a b (i / 4) (i % 4) (Nat.mod_lt _ (by decide))]
  · simp [hi]

end Formal.Net.Compute
