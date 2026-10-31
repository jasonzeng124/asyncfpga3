import Formal.Net.Compute.Word
import Formal.Net.Compute.Fold
import Formal.Net.GcdHwLib

/-!
# H_COMPUTE_FN, part 5: shifters with a fixed shift amount

gcd_hw's `ushrsi*` units are general 32-bit barrel shifters (`$signed(e0) >>> e1`), but in
gcd_hw their `e1` port is fed by the constant token 1 (the Ops join is
`.bin .shrsi 32 (.var 0) (.lit 1)`). This file proves what the capstone uses: with `e1 = 1`
the unit computes `Ops.shrsi 32 a 1`, for every `a`.

* `LocalOKF`: an exhaustive local check where some leaves are FIXED (`fix l = some b`), the
  others enumerated; `localF_sound`: sound for every environment that agrees with `fix`.
* `ShrOK` + `shr1_sound`.
-/

namespace Formal.Net.Compute
open Formal.Net.GcdHw

def envFix (fix : Leaf → Option Bool) (S : List Leaf) (m : Nat) : Leaf → Bool := fun l =>
  match fix l with
  | some b => b
  | none => envOf S m l

def LocalOKF (C : List Nat) (cells : List Cell) (w : W) (S : List Leaf)
    (fix : Leaf → Option Bool) (spec : List Bool → Bool) : Prop :=
  ∀ m, m < 2 ^ S.length → eval (envFix fix S m) C cells w = spec (S.map (envFix fix S m))

instance (C : List Nat) (cells : List Cell) (w : W) (S : List Leaf) (fix : Leaf → Option Bool)
    (spec : List Bool → Bool) : Decidable (LocalOKF C cells w S fix spec) := by
  unfold LocalOKF; exact Nat.decidableBallLT _ _

/-- **Soundness with fixed leaves.** If the check passes, the leaves of the FOLDED support
(`afOf`: constants propagated from `fix`) are enumerated, the enumerated leaves are not fixed,
and `env` agrees with `fix`, then `eval = spec`. -/
theorem localF_sound {C : List Nat} {cells : List Cell} {w : W} {S : List Leaf}
    {fix : Leaf → Option Bool} {spec : List Bool → Bool} (hok : LocalOKF C cells w S fix spec)
    (hnd : S.Nodup) (hfree : ∀ l ∈ S, fix l = none)
    (hsup : ∀ l ∈ (afOf fix C cells w).supp, l ∈ S)
    (env : Leaf → Bool) (henv : ∀ l b, fix l = some b → env l = b) :
    eval env C cells w = spec (S.map env) := by
  let env2 := envFix fix S (enc S env)
  have hag : ∀ l ∈ S, env2 l = env l := by
    intro l hl
    simp only [env2, envFix, hfree l hl]
    exact testBit_enc env S hnd l hl
  have h2 : Agrees fix env2 := by
    intro l b hf; simp only [env2, envFix, hf]
  have hrel := fold_sound C cells w henv h2
  have heq : eval env C cells w = eval env2 C cells w := by
    cases hA : afOf fix C cells w with
    | known b => rw [hA] at hrel; exact hrel.1.trans hrel.2.symm
    | sup L =>
      rw [hA] at hrel
      apply hrel
      intro l hl
      have : l ∈ S := hsup l (by rw [hA]; exact hl)
      exact (hag l this).symm
  rw [heq, show S.map env = S.map env2 from List.map_congr_left (fun l hl => (hag l hl).symm)]
  exact hok _ (enc_lt env S)

/-- The cone of a wire (empty for an input bit or a constant). -/
def coneW (cells : List Cell) : W → List Cell
  | .net n => (filt cells [n]).1
  | _ => []

theorem eval_coneW (env : Leaf → Bool) (C : List Nat) (cells : List Cell) (w : W) :
    eval env C cells w = eval env C (coneW cells w) w := by
  cases w with
  | net n => exact eval_filt env C cells n
  | inp p k => rfl
  | c0 => rfl
  | c1 => rfl

/-- Port 1 carries the constant 1. -/
def fixOne : Leaf → Option Bool
  | .inp 1 k => some (k == 0)
  | _ => none

/-- The source bit of output bit `i` of an arithmetic shift right by one. -/
def shr1Src (i : Nat) : Nat := if i < 31 then i + 1 else 31

/-- The enumerated leaves of output bit `i`: its source bit and the sign bit (the folded support
keeps the sign bit: the sign-fill path is not folded away). -/
def shrS (i : Nat) : List Leaf :=
  if shr1Src i = 31 then [.inp 0 31] else [.inp 0 (shr1Src i), .inp 0 31]

def ShrOK (cells : List Cell) (outs : List W) : Prop :=
  outs.length = 32 ∧
  ∀ i, i < 32 →
    LocalOKF [] (coneW cells (outs.getD i .c0)) (outs.getD i .c0) (shrS i) fixOne
      (fun l => l.getD 0 false) ∧
    (afOf fixOne [] (coneW cells (outs.getD i .c0)) (outs.getD i .c0)).supp.all
      (fun l => decide (l ∈ shrS i)) = true

instance (cells : List Cell) (outs : List W) : Decidable (ShrOK cells outs) := by
  unfold ShrOK; exact inferInstance

theorem testBit_one (k : Nat) : (1 : Nat).testBit k = (k == 0) := by
  cases k with
  | zero => rfl
  | succ k =>
    rw [Nat.testBit_succ]
    simp

theorem shrsi1_bit (a i : Nat) :
    (Ops.shrsi 32 a 1).testBit i =
      (decide (i < 32) && a.testBit (shr1Src i)) := by
  have hx : a % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hbit : ∀ j, j < 32 → (a % 2 ^ 32).testBit j = a.testBit j := by
    intro j hj; rw [Nat.testBit_mod_two_pow]; simp [hj]
  unfold Ops.shrsi
  by_cases hs : a % 2 ^ 32 < 2 ^ (32 - 1)
  · rw [if_pos hs, Nat.testBit_shiftRight]
    simp only [shr1Src]
    by_cases hi : i < 31
    · rw [if_pos hi, Nat.add_comm 1 i, hbit (i + 1) (by omega)]; simp [show i < 32 by omega]
    · rw [if_neg hi]
      have h31 : a.testBit 31 = false := by
        rw [← hbit 31 (by decide)]
        exact Nat.testBit_lt_two_pow (by simpa using hs)
      rw [h31, Nat.testBit_mod_two_pow]
      simp
      omega
  · rw [if_neg hs]
    have e : 2 ^ 32 - 1 - ((2 ^ 32 - 1 - a % 2 ^ 32) >>> 1) =
        2 ^ 32 - (((2 ^ 32 - 1 - a % 2 ^ 32) >>> 1) + 1) := by omega
    have hy : (2 ^ 32 - 1 - a % 2 ^ 32) >>> 1 < 2 ^ 32 := by
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    rw [e,
      Nat.testBit_two_pow_sub_succ hy, Nat.testBit_shiftRight,
      show 2 ^ 32 - 1 - a % 2 ^ 32 = 2 ^ 32 - (a % 2 ^ 32 + 1) by omega,
      Nat.testBit_two_pow_sub_succ hx]
    simp only [shr1Src]
    by_cases hi : i < 31
    · rw [if_pos hi, Nat.add_comm 1 i, hbit (i + 1) (by omega)]
      simp [show i < 32 by omega, show i + 1 < 32 by omega]
    · rw [if_neg hi]
      have h31 : a.testBit 31 = true := by
        rw [← hbit 31 (by decide), Nat.testBit_eq_decide_div_mod_eq]
        simp only [Nat.not_lt, decide_eq_true_eq] at hs ⊢
        omega
      rw [h31]
      by_cases h32 : i < 32
      · simp [h32, show ¬ (1 + i < 32) by omega]
      · simp [h32]

/-- **A certified shifter computes `$signed(a) >>> 1`** for every `a`, when port 1 carries 1. -/
theorem shr1_sound {cells : List Cell} {outs : List W} (h : ShrOK cells outs) (a : Nat) :
    unitVal cells outs [a, 1] = Ops.shrsi 32 a 1 := by
  obtain ⟨hlen, hb⟩ := h
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_unitVal, hlen, shrsi1_bit]
  by_cases hi : i < 32
  · simp only [hi, decide_true, Bool.true_and]
    obtain ⟨hok, hsup⟩ := hb i hi
    have hnd : (shrS i).Nodup := by
      unfold shrS; split
      · simp
      · simp only [List.nodup_cons, List.mem_singleton, List.not_mem_nil, not_false_eq_true,
          List.nodup_nil, and_true]
        intro h; injection h with _ h2; simp_all
    have hfree : ∀ l ∈ shrS i, fixOne l = none := by
      intro l hl; unfold shrS at hl; split at hl <;> simp at hl <;> rcases hl with rfl | rfl <;> rfl
    have := localF_sound hok hnd hfree
      (fun l hl => by
        have := List.all_eq_true.mp hsup l hl
        simpa using this)
      (inEnv [a, 1]) (by
        intro l b hf
        cases l with
        | inp p k =>
          simp only [fixOne] at hf
          split at hf <;> simp_all [inEnv, testBit_one]
        | cut n => simp [fixOne] at hf)
    rw [eval_coneW, this]
    unfold shrS; split <;> simp_all [inEnv]
  · simp [hi]

end Formal.Net.Compute
