import Formal.Net.Compute.Adder

/-!
# H_COMPUTE_FN, part 9: general ripple-carry chains (operands from any leaves, complements,
carry-in)

`RipOK cells r`: the 32 output nets `r.outs` of a CARRY4 ripple chain compute
`A' + B' + cin` (mod 2^32), where `A` is read from the leaves `r.a i` (input bits or cut nets),
`B` likewise (optional), `A' = A` or its 32-bit complement (`r.na`), the same for `B`. Each
4-bit slice is checked exhaustively over its operand leaves and the incoming carry (the
previous slice's carry-out as a cut point); `rip_sound` composes them with the generic
ripple-carry arithmetic. This covers `a + b` (as `Adder.lean`), `a - b = a + ~b + 1`, and
`0 - d = ~d + 1` with `d` itself a cut word.
-/

namespace Formal.Net.Compute

/-! ## Arithmetic with a carry-in -/

def cIn (x y c j : Nat) : Nat := (x % 2 ^ (4 * j) + y % 2 ^ (4 * j) + c) / 2 ^ (4 * j)

theorem pow_step' (j : Nat) : 2 ^ (4 * (j + 1)) = 2 ^ (4 * j) * 16 := by
  rw [show 4 * (j + 1) = 4 * j + 4 by omega, Nat.pow_add]

theorem slice_eq' (x y c j : Nat) :
    (x % 2 ^ (4 * (j + 1)) + y % 2 ^ (4 * (j + 1)) + c) / 2 ^ (4 * j) =
      x / 2 ^ (4 * j) % 16 + y / 2 ^ (4 * j) % 16 + cIn x y c j := by
  rw [pow_step', Nat.mod_mul, Nat.mod_mul]
  have hP : 0 < 2 ^ (4 * j) := Nat.two_pow_pos _
  have e : x % 2 ^ (4 * j) + 2 ^ (4 * j) * (x / 2 ^ (4 * j) % 16) +
      (y % 2 ^ (4 * j) + 2 ^ (4 * j) * (y / 2 ^ (4 * j) % 16)) + c =
      (x % 2 ^ (4 * j) + y % 2 ^ (4 * j) + c) +
        2 ^ (4 * j) * (x / 2 ^ (4 * j) % 16 + y / 2 ^ (4 * j) % 16) := by
    rw [Nat.mul_add]; omega
  rw [e, Nat.add_mul_div_left _ _ hP, cIn]
  omega

theorem cIn_lt (x y c j : Nat) (hc : c ≤ 1) : cIn x y c j < 2 ∨ j = 0 := by
  rcases Nat.eq_zero_or_pos j with h | h
  · exact Or.inr h
  · left
    have hP : 16 ≤ 2 ^ (4 * j) := by
      calc 16 = 2 ^ 4 := rfl
        _ ≤ 2 ^ (4 * j) := Nat.pow_le_pow_right (by decide) (by omega)
    have h1 := Nat.mod_lt x (Nat.two_pow_pos (4 * j))
    have h2 := Nat.mod_lt y (Nat.two_pow_pos (4 * j))
    unfold cIn
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
    omega

theorem cIn_zero (x y c : Nat) : cIn x y c 0 = c := by simp [cIn, Nat.mod_one]

theorem cIn_succ (x y c j : Nat) :
    cIn x y c (j + 1) = (x / 2 ^ (4 * j) % 16 + y / 2 ^ (4 * j) % 16 + cIn x y c j) / 16 := by
  rw [← slice_eq']
  show (x % 2 ^ (4 * (j + 1)) + y % 2 ^ (4 * (j + 1)) + c) / 2 ^ (4 * (j + 1)) = _
  rw [Nat.div_div_eq_div_mul, ← pow_step']

theorem add_bit' (x y c j k : Nat) (hk : k < 4) :
    (x + y + c).testBit (4 * j + k) =
      (x / 2 ^ (4 * j) % 16 + y / 2 ^ (4 * j) % 16 + cIn x y c j).testBit k := by
  have hlt : 4 * j + k < 4 * (j + 1) := by omega
  rw [← slice_eq', Nat.testBit_div_two_pow, Nat.add_comm k]
  have h1 : (x + y + c).testBit (4 * j + k) = ((x + y + c) % 2 ^ (4 * (j + 1))).testBit (4 * j + k) := by
    rw [Nat.testBit_mod_two_pow]; simp [hlt]
  have h2 : (x % 2 ^ (4 * (j + 1)) + y % 2 ^ (4 * (j + 1)) + c).testBit (4 * j + k) =
      ((x % 2 ^ (4 * (j + 1)) + y % 2 ^ (4 * (j + 1)) + c) % 2 ^ (4 * (j + 1))).testBit (4 * j + k) := by
    rw [Nat.testBit_mod_two_pow]; simp [hlt]
  rw [h1, h2]
  congr 1
  rw [Nat.add_mod (x + y), Nat.add_mod x y, Nat.add_mod (x % _ + y % _), Nat.add_mod (x % _),
    Nat.mod_mod, Nat.mod_mod]

end Formal.Net.Compute

/-! ## The certificate -/

namespace Formal.Net.Compute

structure Rip where
  outs : List Nat
  cuts : List Nat
  a : Nat → Leaf
  b : Option (Nat → Leaf)
  na : Bool
  nb : Bool
  cin : Bool
  C : List Nat

def nibR (l : List Bool) (o : Nat) : Nat :=
  (l.getD o false).toNat + 2 * (l.getD (o + 1) false).toNat + 4 * (l.getD (o + 2) false).toNat +
    8 * (l.getD (o + 3) false).toNat

def Rip.bL (r : Rip) (j : Nat) : List Leaf :=
  match r.b with
  | some b => (List.range 4).map (fun t => b (4 * j + t))
  | none => []

def Rip.leaves (r : Rip) (j : Nat) : List Leaf :=
  (List.range 4).map (fun t => r.a (4 * j + t)) ++ r.bL j ++
    (if j = 0 then [] else [.cut (r.cuts.getD (j - 1) 0)])

def Rip.cutset (r : Rip) (j : Nat) : List Nat :=
  r.C ++ (if j = 0 then [] else [r.cuts.getD (j - 1) 0])

def Rip.sum (r : Rip) (j : Nat) (l : List Bool) : Nat :=
  (if r.na then 15 - nibR l 0 else nibR l 0) +
  (match r.b with
   | some _ => if r.nb then 15 - nibR l 4 else nibR l 4
   | none => 0) +
  (if j = 0 then r.cin.toNat else (l.getD (if r.b.isSome then 8 else 4) false).toNat)

def RipOK (cells : List Cell) (r : Rip) : Prop :=
  r.outs.length = 32 ∧ (cells.flatMap Cell.outs).Nodup ∧
  (∀ i, i < 32 → NetOK cells (r.cutset (i / 4)) (r.outs.getD i 0) (r.leaves (i / 4))
    (fun l => (r.sum (i / 4) l).testBit (i % 4))) ∧
  (∀ j, j < 7 → NetOK cells (r.cutset j) (r.cuts.getD j 0) (r.leaves j)
    (fun l => decide (16 ≤ r.sum j l)))

/-! ## Soundness -/

/-- The 32-bit operand read from leaves. -/
def opVal (lv : Leaf → Bool) (a : Nat → Leaf) : Nat := word (fun i => lv (a i)) 32

def comp32 (neg : Bool) (x : Nat) : Nat := if neg then 2 ^ 32 - 1 - x else x

theorem word_lt (f : Nat → Bool) : ∀ n, word f n < 2 ^ n
  | 0 => by simp [word]
  | n + 1 => by
    have := word_lt f n
    simp only [word]
    rw [Nat.pow_succ]
    cases f n
    · simp; omega
    · simp only [if_true]
      have h1 : word f n < 2 ^ (n + 1) := Nat.lt_trans this (Nat.pow_lt_pow_right (by decide) (by omega))
      have h2 : 2 ^ n < 2 ^ (n + 1) := Nat.pow_lt_pow_right (by decide) (by omega)
      have h3 := Nat.or_lt_two_pow h1 h2
      rw [Nat.pow_succ] at h3; exact h3

theorem nib_word (f : Nat → Bool) (j : Nat) (hj : j < 8) :
    (f (4 * j)).toNat + 2 * (f (4 * j + 1)).toNat + 4 * (f (4 * j + 2)).toNat +
      8 * (f (4 * j + 3)).toNat = word f 32 / 2 ^ (4 * j) % 16 := by
  rw [mod16_bits]
  simp only [Nat.testBit_div_two_pow, testBit_word]
  have h : ∀ k, k < 4 → decide (k + 4 * j < 32) = true := fun k hk => by simp; omega
  rw [h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide)]
  simp only [Bool.true_and, Nat.add_comm _ (4 * j), Nat.add_zero]

theorem nib_bit (y j k : Nat) (hk : k < 4) : (y / 2 ^ (4 * j) % 16).testBit k = y.testBit (4 * j + k) := by
  rw [show (16 : Nat) = 2 ^ 4 from rfl, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  simp [hk, Nat.add_comm]

theorem comp_nib (x j : Nat) (hx : x < 2 ^ 32) (hj : j < 8) :
    (2 ^ 32 - 1 - x) / 2 ^ (4 * j) % 16 = 15 - x / 2 ^ (4 * j) % 16 := by
  have hn : x / 2 ^ (4 * j) % 16 < 16 := Nat.mod_lt _ (by decide)
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 4
  · rw [nib_bit _ _ _ hk, show 2 ^ 32 - 1 - x = 2 ^ 32 - (x + 1) by omega,
      Nat.testBit_two_pow_sub_succ hx, ← nib_bit x j k hk]
    have key : ∀ n, n < 16 → ∀ k, k < 4 → (15 - n).testBit k = !n.testBit k := by decide
    rw [key _ hn k hk]
    simp; omega
  · have h1 : (2 ^ 32 - 1 - x) / 2 ^ (4 * j) % 16 < 2 ^ k :=
      Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by
        calc 16 = 2 ^ 4 := rfl
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega))
    have h2 : 15 - x / 2 ^ (4 * j) % 16 < 2 ^ k :=
      Nat.lt_of_lt_of_le (show 15 - x / 2 ^ (4 * j) % 16 < 16 by omega) (by
        calc 16 = 2 ^ 4 := rfl
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega))
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]

theorem comp_nib' (neg : Bool) (x j : Nat) (hx : x < 2 ^ 32) (hj : j < 8) :
    comp32 neg x / 2 ^ (4 * j) % 16 = if neg then 15 - x / 2 ^ (4 * j) % 16 else x / 2 ^ (4 * j) % 16 := by
  cases neg
  · rfl
  · exact comp_nib x j hx hj

theorem comp32_lt (neg : Bool) (x : Nat) (hx : x < 2 ^ 32) : comp32 neg x < 2 ^ 32 := by
  cases neg <;> simp [comp32] <;> omega

/-- **A certified ripple chain computes `A' + B' + cin`** (each output bit), for every
environment. -/
theorem rip_sound {cells : List Cell} {r : Rip} (h : RipOK cells r) (env : Leaf → Bool) (i : Nat)
    (hi : i < 32) :
    run env [] cells (fun _ => false) (r.outs.getD i 0) =
      (comp32 r.na (opVal (cutEnv env cells) r.a) +
        (match r.b with
         | some b => comp32 r.nb (opVal (cutEnv env cells) b)
         | none => 0) + r.cin.toNat).testBit i := by
  obtain ⟨_, hnd, hbits, hcar⟩ := h
  let lv := cutEnv env cells
  let R := run env [] cells (fun _ => false)
  let A := comp32 r.na (opVal lv r.a)
  let B := match r.b with
    | some b => comp32 r.nb (opVal lv b)
    | none => 0
  have hAl : opVal lv r.a < 2 ^ 32 := word_lt _ 32
  have hsum : ∀ j, j < 8 → r.sum j ((r.leaves j).map lv) =
      A / 2 ^ (4 * j) % 16 + B / 2 ^ (4 * j) % 16 +
        (if j = 0 then r.cin.toNat else (R (r.cuts.getD (j - 1) 0)).toNat) := by
    intro j hj
    have hA : nibR ((r.leaves j).map lv) 0 = opVal lv r.a / 2 ^ (4 * j) % 16 := by
      show _ = word (fun i => lv (r.a i)) 32 / 2 ^ (4 * j) % 16
      rw [← nib_word (fun i => lv (r.a i)) j hj]
      simp [nibR, Rip.leaves, List.getD_eq_getElem?_getD, List.getElem?_append_left, Nat.add_comm]
    have hAc : (if r.na then 15 - nibR ((r.leaves j).map lv) 0 else nibR ((r.leaves j).map lv) 0) =
        A / 2 ^ (4 * j) % 16 := by
      rw [hA]; exact (comp_nib' r.na _ j hAl hj).symm
    unfold Rip.sum
    rw [hAc]
    cases hb : r.b with
    | none =>
      have hB0 : B = 0 := by simp only [B, hb]
      rw [hB0]
      simp only [Nat.zero_div, Nat.zero_mod, Option.isSome_none, Bool.false_eq_true, if_false]
      by_cases hj0 : j = 0
      · simp [hj0]
      · simp only [hj0, if_false]
        congr 2
        simp [Rip.leaves, Rip.bL, hb, hj0, List.getD_eq_getElem?_getD, lv, cutEnv, R]
    | some b =>
      have hBl : opVal lv b < 2 ^ 32 := word_lt _ 32
      have hBv : B = comp32 r.nb (opVal lv b) := by simp only [B, hb]
      have hBn : nibR ((r.leaves j).map lv) 4 = opVal lv b / 2 ^ (4 * j) % 16 := by
        show _ = word (fun i => lv (b i)) 32 / 2 ^ (4 * j) % 16
        rw [← nib_word (fun i => lv (b i)) j hj]
        simp [nibR, Rip.leaves, Rip.bL, hb, List.getD_eq_getElem?_getD, List.getElem?_append_left,
          List.getElem?_append_right, Nat.add_comm]
      simp only [Option.isSome_some, if_true]
      rw [hBn, hBv, comp_nib' r.nb _ j hBl hj]
      by_cases hj0 : j = 0
      · simp [hj0]
      · simp only [hj0, if_false]
        congr 2
        simp [Rip.leaves, Rip.bL, hb, hj0, List.getD_eq_getElem?_getD, List.getElem?_append_right,
          lv, cutEnv, R]
  have hcinle : r.cin.toNat ≤ 1 := by cases r.cin <;> decide
  have hc : ∀ j, j ≤ 7 →
      (if j = 0 then r.cin.toNat else (R (r.cuts.getD (j - 1) 0)).toNat) = cIn A B r.cin.toNat j := by
    intro j
    induction j with
    | zero => intro _; simp [cIn_zero]
    | succ j ih =>
      intro hj
      obtain ⟨c1, c2, c3⟩ := hcar j (by omega)
      have hv := cert_val hnd c1 c2 c3 env
      simp only [Nat.add_sub_cancel, Nat.add_one_ne_zero, if_false]
      show (R (r.cuts.getD j 0)).toNat = _
      rw [show R (r.cuts.getD j 0) = _ from hv, hsum j (by omega), ih (by omega), cIn_succ]
      apply toNat_decide_le
      have := Nat.mod_lt (A / 2 ^ (4 * j)) (show 16 > 0 by decide)
      have := Nat.mod_lt (B / 2 ^ (4 * j)) (show 16 > 0 by decide)
      rcases cIn_lt A B r.cin.toNat j hcinle with h | h
      · omega
      · subst h; rw [cIn_zero]; omega
  obtain ⟨b1, b2, b3⟩ := hbits i hi
  have hv := cert_val hnd b1 b2 b3 env
  show R (r.outs.getD i 0) = _
  rw [show R (r.outs.getD i 0) = _ from hv, hsum _ (by omega), hc _ (by omega)]
  have hi4 : i = 4 * (i / 4) + i % 4 := by omega
  conv => rhs; rw [hi4]
  rw [add_bit' A B r.cin.toNat (i / 4) (i % 4) (Nat.mod_lt _ (by decide))]

end Formal.Net.Compute
