import Formal.Net.GcdHwProof
import Formal.Net.KahnGcd

/-!
# The gcd_hw C function is `Nat.gcd` on non-negative i32 inputs (probe C-8k)

Core Lean only. Discharges H_NONNEG31, the open goal of probe C-8i
(`Wip/C8i/Nonneg31.lean`), with an explicit fuel bound.

`gcdC` (in `GcdHwProof`) transcribes Dynamatic's `cf_transformed.mlir` for the
gcd fixture at bdc's i32 op semantics (`Ops.*`, Nat mod 2^32, signed compares by
sign-bit flip). Here:

* per-op lemmas: on values `< 2^31` the i32 ops are the Nat ones
  (`shrsi1`, `eq0`, `cEv_iff`, `slt1`, `cSc_iff`, `absd_eq`, `minC_eq`,
  `shli_eq` while the shifted value fits, `addi1`);
* the loops are 8b's Nat transcription (`Formal.Net.Kahn.Gcd`): bb3 is
  `shared` (`loop3_eq`), bb5/bb7/bb11 are `strip2` (`strip_eq`, `strip_fuel`);
  the main loop returns `gcd` (`main_eq`), reusing 8b's `gcd_strip2`,
  `strip2_odd`, `strip2_pos`, `strip2_le`, `shared_spec`, `gcd_strip2_both`;
* the fuel bound: strips take at most 32 steps (values `< 2^31`), and the main
  loop's product `a * b` more than halves per iteration, so fuel
  `fuelBound a b = log2 (a * b) + 34` suffices (`gcdC_fuel`); 96 always does
  (`gcdC_nonneg31_96`); C-8i's stated goal `gcdC_nonneg31` (fuel `a + b + 64`).

`gcdC` is fuel-monotone in the sense used here: every fuel above the bound
gives the same `some (Nat.gcd a b)`. Kernel `decide` is never used on symbolic
i32 values (it blows up memory); literal powers are normalised by
`Nat.reducePow` and closed by `omega`. `rw` is avoided where its closing `rfl`
would try to evaluate `x + 2^31` on symbolic `x`.
-/

namespace Formal.Net.GcdHw.Gcd
open Formal.Net.GcdHw

theorem isT_b2n (b : Bool) : isT (Ops.b2n b) = b := by cases b <;> rfl

theorem shrsi1 {x : Nat} (h : x < 2 ^ 31) : Ops.shrsi 32 x 1 = x / 2 := by
  have h' : x % 2 ^ 32 = x := Nat.mod_eq_of_lt (by omega)
  unfold Ops.shrsi; rw [h', if_pos (by simpa using h), Nat.shiftRight_eq_div_pow]

theorem eq0 {x : Nat} (h : x < 2 ^ 31) : isT (Ops.cmpi .eq 32 x 0) = decide (x = 0) := by
  have h' : x % 2 ^ 32 = x := Nat.mod_eq_of_lt (by omega)
  unfold Ops.cmpi; simp only [isT_b2n, h', Nat.zero_mod]
  by_cases hx : x = 0 <;> simp [hx]

theorem or_mod2 (x y : Nat) : (x ||| y) % 2 = if x % 2 = 0 ∧ y % 2 = 0 then 0 else 1 := by
  rw [← Nat.and_one_is_mod, Nat.and_or_distrib_right, Nat.and_one_is_mod, Nat.and_one_is_mod]
  have hx : x % 2 = 0 ∨ x % 2 = 1 := by omega
  have hy : y % 2 = 0 ∨ y % 2 = 1 := by omega
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> simp [hx, hy]

theorem cEv_iff (x y : Nat) : isT (cEv x y) = decide (x % 2 = 0 ∧ y % 2 = 0) := by
  unfold cEv; rw [andi32_one]
  have e : Ops.ori 32 x y % 2 = (x ||| y) % 2 := by
    unfold Ops.ori; rw [Nat.mod_mod_of_dvd _ (by decide)]
  unfold Ops.cmpi; simp only [isT_b2n, e, or_mod2]
  split <;> simp_all

theorem flip32 {x : Nat} (h : x < 2 ^ 31) : Ops.flip 32 x = x + 2 ^ 31 := by
  unfold Ops.flip; simp only [Nat.reducePow, Nat.reduceSub] at h ⊢; omega

theorem slt1 {x : Nat} (h : x < 2 ^ 31) : Ops.cmpi .slt 32 x 1 = Ops.b2n (decide (x = 0)) := by
  unfold Ops.cmpi; simp only
  have e : decide (Ops.flip 32 x < Ops.flip 32 1) = decide (x = 0) := by
    simp only [flip32 h, flip32 (x := 1) (by simp only [Nat.reducePow]; omega), decide_eq_decide]; omega
  simp only [e]

theorem cSc_iff {x : Nat} (h : x < 2 ^ 31) : isT (cSc x) = decide (x % 2 = 1 ∨ x = 0) := by
  unfold cSc; rw [andi32_one, slt1 h]
  have hx : x % 2 = 0 ∨ x % 2 = 1 := by omega
  rcases hx with hx | hx <;> by_cases h0 : x = 0 <;>
    simp [Ops.cmpi, Ops.ori, Ops.b2n, isT, hx, h0]

theorem subi_le {a b : Nat} (ha : a < 2 ^ 32) (hba : b ≤ a) : Ops.subi 32 a b = a - b := by
  unfold Ops.subi; simp only [Nat.reducePow] at ha ⊢
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (by omega : b < 4294967296)]; omega

theorem subi_lt {a b : Nat} (hb : b < 2 ^ 32) (hab : a < b) :
    Ops.subi 32 a b = 2 ^ 32 - (b - a) := by
  unfold Ops.subi; simp only [Nat.reducePow] at hb ⊢
  rw [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (by omega : a < 4294967296)]; omega

theorem flipM1 : Ops.flip 32 4294967295 = 2 ^ 31 - 1 := by
  unfold Ops.flip; simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]

theorem flip_hi {v : Nat} (h1 : 2 ^ 31 ≤ v) (h2 : v < 2 ^ 32) : Ops.flip 32 v = v - 2 ^ 31 := by
  unfold Ops.flip; simp only [Nat.reducePow, Nat.reduceSub] at h1 h2 ⊢; omega

theorem b2n_true : Ops.b2n true % 2 = 1 := rfl
theorem b2n_false : ¬ Ops.b2n false % 2 = 1 := by decide

theorem absd_eq {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    absd a b = Kahn.Gcd.absdiff a b := by
  unfold absd Kahn.Gcd.absdiff Ops.select
  simp only [Nat.reducePow] at ha hb
  by_cases hab : b ≤ a
  · have hs : Ops.subi 32 a b = a - b := subi_le (by simp only [Nat.reducePow]; omega) hab
    have hc : Ops.cmpi .sgt 32 (Ops.subi 32 a b) 4294967295 = 1 := by
      unfold Ops.cmpi; simp only
      have e : decide (Ops.flip 32 4294967295 < Ops.flip 32 (Ops.subi 32 a b)) = true := by
        simp only [flipM1, hs, flip32 (x := a - b) (by simp only [Nat.reducePow]; omega)]
        simp only [Nat.reducePow, Nat.reduceSub, decide_eq_true_eq]; omega
      simp only [e]; rfl
    simp only [hc]; simp only [hs, hab, ↓reduceIte]
  · have hs : Ops.subi 32 a b = 2 ^ 32 - (b - a) := subi_lt (by simp only [Nat.reducePow]; omega) (by omega)
    have hc : Ops.cmpi .sgt 32 (Ops.subi 32 a b) 4294967295 = 0 := by
      unfold Ops.cmpi; simp only
      have e : decide (Ops.flip 32 4294967295 < Ops.flip 32 (Ops.subi 32 a b)) = false := by
        simp only [flipM1, hs]
        rw [flip_hi (by simp only [Nat.reducePow]; omega) (by simp only [Nat.reducePow]; omega)]
        simp only [Nat.reducePow, Nat.reduceSub, decide_eq_false_iff_not]; omega
      simp only [e]; rfl
    have h2 : Ops.subi 32 0 (Ops.subi 32 a b) = b - a := by
      rw [hs, subi_lt (by simp only [Nat.reducePow]; omega) (by simp only [Nat.reducePow]; omega)]
      simp only [Nat.reducePow]; omega
    simp only [hc]; simp only [h2, hab, Nat.zero_mod]; simp

theorem minC_eq {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) : minC a b = min a b := by
  unfold minC Ops.select Ops.cmpi; simp only [flip32 ha, flip32 hb]
  by_cases hab : a < b
  · have e : decide (a + 2 ^ 31 < b + 2 ^ 31) = true := decide_eq_true (by omega)
    simp only [e]; simp only [Ops.b2n, ↓reduceIte, Nat.one_mod]; omega
  · have e : decide (a + 2 ^ 31 < b + 2 ^ 31) = false := decide_eq_false (by omega)
    simp only [e]; simp [Ops.b2n]; omega

theorem shli_eq {r k : Nat} (h : r * 2 ^ k < 2 ^ 32) : Ops.shli 32 r k = r * 2 ^ k := by
  unfold Ops.shli; rw [Nat.shiftLeft_eq]; exact Nat.mod_eq_of_lt h

theorem addi1 {k : Nat} (h : k + 1 < 2 ^ 32) : Ops.addi 32 k 1 = k + 1 := Nat.mod_eq_of_lt h


open Kahn.Gcd (strip2 absdiff shared)

theorem pow31_le {f : Nat} (h : 31 ≤ f) : 2 ^ 31 ≤ 2 ^ f := Nat.pow_le_pow_right (by decide) h

/-- bb5/bb7/bb11 strip with fuel `f + 1` on `x < 2^f` is 8b's `strip2`. -/
theorem strip_eq : ∀ f x, x < 2 ^ f → x < 2 ^ 31 → strip (f + 1) x = some (strip2 x) := by
  intro f; induction f with
  | zero =>
    intro x h _
    have : x = 0 := by simp at h; omega
    subst this; simp only [strip, cSc_iff (by decide : 0 < 2 ^ 31)]; simp [strip2]
  | succ f ih =>
    intro x h h31
    rw [strip.eq_2]; simp only [cSc_iff h31]
    by_cases hc : x % 2 = 1 ∨ x = 0
    · simp only [hc, decide_true, ↓reduceIte]
      rw [strip2]; rw [if_neg (by omega)]
    · simp only [hc, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [shrsi1 h31, ih (x / 2) (by rw [Nat.pow_succ] at h; omega) (by omega)]
      rw [strip2.eq_1 x, if_pos (by omega)]

theorem strip_fuel {F x : Nat} (hF : 32 ≤ F) (h : x < 2 ^ 31) : strip F x = some (strip2 x) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 1 := ⟨F - 1, by omega⟩
  exact strip_eq f x (Nat.lt_of_lt_of_le h (pow31_le (by omega))) h

/-- bb3 with fuel `f + 1` on `0 < x < 2^f` is 8b's `shared`. -/
theorem loop3_eq : ∀ f x y k, 0 < x → x < 2 ^ f → x * 2 ^ k < 2 ^ 31 → y < 2 ^ 31 →
    loop3 (f + 1) x y k = some (shared x y k) := by
  intro f; induction f with
  | zero => intro x _ _ hx h; simp at h; omega
  | succ f ih =>
    intro x y k hx h hk hy
    have hx31 : x < 2 ^ 31 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right x (Nat.two_pow_pos k)) hk
    rw [loop3.eq_2]; simp only [cEv_iff]
    by_cases hc : x % 2 = 0 ∧ y % 2 = 0
    · simp only [hc, and_self, decide_true, ↓reduceIte]
      have hk1 : k + 1 < 2 ^ 32 := by
        have := @Nat.lt_two_pow_self k
        have := Nat.le_mul_of_pos_left (2 ^ k) hx
        simp only [Nat.reducePow] at *; omega
      have e2 : x / 2 * 2 ^ (k + 1) = x * 2 ^ k := by
        rw [Nat.pow_succ]
        have hx2 : x = x / 2 * 2 := by omega
        conv => rhs; rw [hx2]
        rw [Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc]
      rw [shrsi1 hx31, shrsi1 hy, addi1 hk1,
        ih (x / 2) (y / 2) (k + 1) (by omega) (by rw [Nat.pow_succ] at h; omega) (by omega) (by omega)]
      rw [shared.eq_1 x, if_pos ⟨hx, hc⟩]
    · simp only [hc, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [shared.eq_1 x, if_neg (by omega)]

/-- `shared` only divides by the factor it counts. -/
theorem shared_bound (a b k : Nat) :
    (shared a b k).1 * 2 ^ (shared a b k).2.2 ≤ a * 2 ^ k ∧ (shared a b k).2.1 ≤ b := by
  rw [shared]
  split
  · rename_i h
    have ih := shared_bound (a / 2) (b / 2) (k + 1)
    have e2 : a / 2 * 2 ^ (k + 1) = a * 2 ^ k := by
      rw [Nat.pow_succ]
      have hx2 : a = a / 2 * 2 := by omega
      conv => rhs; rw [hx2]
      rw [Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc]
    omega
  · exact ⟨Nat.le_refl _, Nat.le_refl _⟩
termination_by a
decreasing_by omega

theorem gcd_absdiff_min (a b : Nat) : Nat.gcd (absdiff a b) (min a b) = Nat.gcd a b := by
  unfold absdiff
  split
  · rename_i h; rw [Nat.min_eq_right h, Nat.gcd_sub_self_left h]
  · rename_i h
    rw [Nat.min_eq_left (by omega), Nat.gcd_sub_self_left (by omega), Nat.gcd_comm]

theorem strip2_half {d : Nat} (h0 : 0 < d) (he : d % 2 = 0) : 2 * strip2 d ≤ d := by
  rw [strip2, if_pos ⟨h0, he⟩]; have := Kahn.Gcd.strip2_le (d / 2); omega

/-- The main loop (bb10/bb11/bb9) on odd `a, b < 2^31` with `a * b < 2^n` and fuel
`n + 33` returns `gcd a b`: the product at least halves per iteration. -/
theorem main_eq : ∀ f n a b, a % 2 = 1 → b % 2 = 1 → a < 2 ^ 31 → b < 2 ^ 31 →
    a * b < 2 ^ n → n + 33 ≤ f → mainLoop f a b = some (Nat.gcd a b) := by
  intro f; induction f with
  | zero => intro _ _ _ _ _ _ _ _ hf; omega
  | succ f ih =>
    intro n a b ha hb ha31 hb31 hn hf
    have hd31 : absdiff a b < 2 ^ 31 := by unfold absdiff; split <;> omega
    have hle := Kahn.Gcd.strip2_le (absdiff a b)
    have hx31 : strip2 (absdiff a b) < 2 ^ 31 := by omega
    rw [mainLoop.eq_2]
    simp only [absd_eq ha31 hb31, strip_fuel (F := f) (by omega) hd31, eq0 hx31, minC_eq ha31 hb31]
    by_cases hx : strip2 (absdiff a b) = 0
    · simp only [hx, decide_true, ↓reduceIte, Option.some.injEq]
      have hd : absdiff a b = 0 := by
        rcases Nat.eq_zero_or_pos (absdiff a b) with h | h
        · exact h
        · have := Kahn.Gcd.strip2_pos h; omega
      have hab : a = b := by unfold absdiff at hd; split at hd <;> omega
      subst hab; simp
    · simp only [hx, decide_false, Bool.false_eq_true, ↓reduceIte]
      have hm : min a b % 2 = 1 := by
        rcases Nat.le_total a b with h | h
        · rw [Nat.min_eq_left h]; exact ha
        · rw [Nat.min_eq_right h]; exact hb
      have hxo : strip2 (absdiff a b) % 2 = 1 := by
        rcases Kahn.Gcd.strip2_odd (absdiff a b) with h | h
        · exact absurd h hx
        · exact h
      have hdpos : 0 < absdiff a b := by
        rcases Nat.eq_zero_or_pos (absdiff a b) with h | h
        · rw [h] at hx; simp [strip2] at hx
        · exact h
      have hdev : absdiff a b % 2 = 0 := by unfold absdiff; split <;> omega
      have h2 := strip2_half hdpos hdev
      -- the product of the new pair is less than half the old one
      have hprod : 2 * (strip2 (absdiff a b) * min a b) < a * b := by
        have hdm : absdiff a b * min a b < a * b := by
          unfold absdiff; split
          · rename_i h; rw [Nat.min_eq_right h]
            exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
          · rename_i h; rw [Nat.min_eq_left (by omega), Nat.mul_comm a b]
            exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
        have := Nat.mul_le_mul_right (min a b) h2
        rw [Nat.mul_assoc] at this; omega
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := by
        rcases n with _ | n'
        · have : 0 < a * b := Nat.mul_pos (by omega) (by omega)
          simp at hn; omega
        · exact ⟨n', rfl⟩
      rw [Nat.pow_succ] at hn
      rw [ih n' _ _ hxo hm hx31 (by rcases Nat.le_total a b with h | h <;> simp [h] <;> omega)
        (by omega) (by omega)]
      rw [Kahn.Gcd.gcd_strip2 _ _ hm, gcd_absdiff_min]


/-- The fuel the C function needs on `a, b < 2^31`: logarithmic in `a * b`. -/
def fuelBound (a b : Nat) : Nat := Nat.log2 (a * b) + 34

/-- **H_NONNEG31 discharged.** On non-negative i32 inputs the C function of the
gcd_hw fixture (as transcribed, at bdc's i32 op semantics) terminates within
`fuelBound a b = log2 (a*b) + 34` fuel (any larger fuel too) and returns
`Nat.gcd a b`. -/
theorem gcdC_fuel {fuel a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) (hf : fuelBound a b ≤ fuel) :
    gcdC fuel a b = some (Nat.gcd a b) := by
  unfold fuelBound at hf
  unfold gcdC
  rw [eq0 ha]
  by_cases ha0 : a = 0
  · subst ha0; simp
  rw [eq0 hb]
  by_cases hb0 : b = 0
  · subst hb0; simp [ha0]
  simp only [ha0, hb0, decide_false, Bool.false_eq_true, ↓reduceIte]
  have hap : 0 < a := Nat.pos_of_ne_zero ha0
  have hbp : 0 < b := Nat.pos_of_ne_zero hb0
  have htr : (if isT (cEv a b) then
        loop3 fuel (Ops.shrsi 32 a 1) (Ops.shrsi 32 b 1) (Ops.addi 32 0 1)
      else some (a, b, 0)) = some (shared a b 0) := by
    rw [cEv_iff]
    by_cases hc : a % 2 = 0 ∧ b % 2 = 0
    · simp only [hc, and_self, decide_true, ↓reduceIte]
      obtain ⟨g, rfl⟩ : ∃ g, fuel = g + 1 := ⟨fuel - 1, by omega⟩
      have h1 : Ops.addi 32 0 1 = 1 := rfl
      rw [shrsi1 ha, shrsi1 hb, h1, loop3_eq g (a / 2) (b / 2) 1 (by omega)
        (Nat.lt_of_lt_of_le (by simp only [Nat.reducePow] at *; omega) (pow31_le (by omega)))
        (by simp only [Nat.reducePow] at *; omega) (by omega)]
      rw [shared.eq_1 a, if_pos ⟨hap, hc⟩]
    · simp only [hc, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [shared.eq_1 a, if_neg (by omega)]
  rw [htr]
  obtain ⟨hx0, hy0, hodd, hg⟩ := Kahn.Gcd.shared_spec a b 0 hap hbp
  obtain ⟨hxb, hyb⟩ := shared_bound a b 0
  generalize shared a b 0 = p at hx0 hy0 hodd hg hxb hyb
  obtain ⟨x, y, K⟩ := p
  simp only [Nat.pow_zero, Nat.mul_one] at hx0 hy0 hodd hg hxb hyb ⊢
  have hxa : x ≤ a := Nat.le_trans (Nat.le_mul_of_pos_right x (Nat.two_pow_pos K)) hxb
  have hx31 : x < 2 ^ 31 := by omega
  have hy31 : y < 2 ^ 31 := by omega
  rw [strip_fuel (by omega) hx31, strip_fuel (by omega) hy31]
  simp only
  have hx2le := Kahn.Gcd.strip2_le x
  have hy2le := Kahn.Gcd.strip2_le y
  have hx2pos := Kahn.Gcd.strip2_pos hx0
  have hy2pos := Kahn.Gcd.strip2_pos hy0
  rw [eq0 (by omega)]
  simp only [show strip2 x ≠ 0 by omega, decide_false, Bool.false_eq_true, ↓reduceIte]
  have hodd2 : ∀ z, 0 < z → strip2 z % 2 = 1 := fun z hz => by
    rcases Kahn.Gcd.strip2_odd z with h | h
    · have := Kahn.Gcd.strip2_pos hz; omega
    · exact h
  have hprod : strip2 x * strip2 y < 2 ^ (Nat.log2 (a * b) + 1) :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul (by omega) (by omega)) Nat.lt_log2_self
  rw [main_eq fuel _ _ _ (hodd2 x hx0) (hodd2 y hy0) (by omega) (by omega) hprod (by omega)]
  simp only [Option.map_some, Option.some.injEq]
  rw [Kahn.Gcd.gcd_strip2_both hx0 hy0 hodd]
  have hgl : Nat.gcd a b ≤ a := Nat.gcd_le_left b hap
  rw [hg] at hgl ⊢
  rw [shli_eq (by simp only [Nat.reducePow] at *; omega)]

/-- Every non-negative i32 input terminates within 96 fuel (`a * b < 2^62`). -/
theorem gcdC_nonneg31_96 {fuel a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) (hf : 96 ≤ fuel) :
    gcdC fuel a b = some (Nat.gcd a b) := by
  apply gcdC_fuel ha hb
  unfold fuelBound
  rcases Nat.eq_zero_or_pos (a * b) with h | h
  · rw [h]; simp only [Nat.log2_zero]; omega
  · have : Nat.log2 (a * b) < 62 := (Nat.log2_lt (by omega)).2
      (Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' ha hb) (by simp))
    omega

/-- The statement left open in `Wip/C8i/Nonneg31.lean`, now proved. -/
theorem gcdC_nonneg31 (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    gcdC (a + b + 64) a b = some (Nat.gcd a b) := by
  apply gcdC_fuel ha hb
  unfold fuelBound
  rcases Nat.eq_zero_or_pos (a * b) with h | h
  · rw [h]; simp only [Nat.log2_zero]; omega
  · have : Nat.log2 (a * b) < a + b + 1 := (Nat.log2_lt (by omega)).2 (by
      rw [Nat.pow_succ, Nat.pow_add]
      exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' Nat.lt_two_pow_self Nat.lt_two_pow_self)
        (Nat.le_mul_of_pos_right _ (by decide)))
    omega

end Formal.Net.GcdHw.Gcd
