import Formal.Rewrite.Plain.CountloopSame

/-!
# Formal.Rewrite.Plain.CountloopTotal -- countloop's C returns on every input; CountloopSame without its fuel hypothesis (shard A, 2026-11-18)

**Problem, plainly.** `CountloopSame.same` holds on every input on which the C (`kC`, cfront's transcription of
`kernels/countloop/countloop.c`) returns within the given fuel. The auditor (T162) noted that this is true but was not
proved. Does the C return on every input?

**Proved** (`kC_total`): for every `a n`, `kC (2^31 + 1) a n = some r` for some `r`. The loop counter `i` starts at
0 and counts up by one while `slt(i, n)`. If `n` is negative as a 32-bit value, the test fails at once. Otherwise
`i` never passes `n < 2^31`, so it never wraps, and the loop stops after at most `2^31 - 1` trips.
`same_all`: hence, for EVERY input `(a, n)`, both graphs (research's fixture and the plain rewrite) have a complete
run, and every complete run of either ends with the C's result on the output.

**Not covered:** token level only (as `CountloopSame`).
-/

namespace Formal.Rewrite.Plain.CountloopTotal

open Formal.Net.Kahn Formal.Net.GcdHw Formal.Net.Auto Formal.Net.AutoApClorig

theorem slt_small (i n : Nat) (hi : i < 2147483648) :
    Ops.cmpi .slt 32 i n % 2 = 1 ↔ (n % 4294967296 < 2147483648 ∧ i < n % 4294967296) := by
  have h32 : (2:Nat) ^ 32 = 4294967296 := rfl
  have h31 : (2:Nat) ^ (32 - 1) = 2147483648 := rfl
  simp only [Ops.cmpi, Ops.flip, Ops.b2n, h32, h31]
  have hn := Nat.mod_lt n (show 0 < 4294967296 by decide)
  generalize n % 4294967296 = m at hn ⊢
  rw [Nat.mod_eq_of_lt (show i < 4294967296 by omega)]
  by_cases hm : m < 2147483648
  · rw [Nat.mod_eq_of_lt (show i + 2147483648 < 4294967296 by omega),
        Nat.mod_eq_of_lt (show m + 2147483648 < 4294967296 by omega)]
    by_cases h : i < m <;> simp [h, hm]
  · rw [Nat.mod_eq_of_lt (show i + 2147483648 < 4294967296 by omega),
        show (m + 2147483648) % 4294967296 = m - 2147483648 by omega]
    have : ¬ (i + 2147483648 < m - 2147483648) := by omega
    simp [this, hm]

theorem pick_t {a n s i : Nat} (h : isT (Ops.cmpi .slt 32 i n) = true) : P.pick 0 [a, n, s, i] = some ce0 := by
  have hev : ((P.tests.getD 0 (.lit 0)).eval [a, n, s, i]) = Ops.cmpi .slt 32 i n := rfl
  unfold CProg.pick; rw [hev, h]; rfl

theorem pick_f {a n s i : Nat} (h : isT (Ops.cmpi .slt 32 i n) = false) : P.pick 0 [a, n, s, i] = some ce1 := by
  have hev : ((P.tests.getD 0 (.lit 0)).eval [a, n, s, i]) = Ops.cmpi .slt 32 i n := rfl
  unfold CProg.pick; rw [hev, h]; rfl

theorem step_t {a n s i : Nat} (k : Nat) (h : isT (Ops.cmpi .slt 32 i n) = true) :
    P.run (k + 1) 0 [a, n, s, i] = P.run k 0 [a, n, Ops.xori 32 (Ops.addi 32 s i) a, Ops.addi 32 i 1] := by
  rw [CProg.run.eq_2, pick_t h]; rfl

theorem step_f {a n s i : Nat} (k : Nat) (h : isT (Ops.cmpi .slt 32 i n) = false) :
    P.run (k + 1) 0 [a, n, s, i] = some s := by
  rw [CProg.run.eq_2, pick_f h]; rfl

theorem isT_iff (v : Nat) : isT v = true ↔ v % 2 = 1 := by simp [isT]

theorem run_total (a n : Nat) : ∀ k i s, i < 2147483648 →
    (n % 4294967296 < 2147483648 → i ≤ n % 4294967296) →
    (n % 4294967296 < 2147483648 → n % 4294967296 - i ≤ k) →
    ∃ r, P.run (k + 1) 0 [a, n, s, i] = some r := by
  intro k
  induction k with
  | zero =>
    intro i s hi hle hk
    have ht : isT (Ops.cmpi .slt 32 i n) = false := by
      cases h : isT (Ops.cmpi .slt 32 i n)
      · rfl
      · rw [isT_iff, slt_small i n hi] at h; omega
    exact ⟨s, step_f 0 ht⟩
  | succ k ih =>
    intro i s hi hle hk
    cases ht : isT (Ops.cmpi .slt 32 i n)
    · exact ⟨s, step_f (k + 1) ht⟩
    · have h2 := (slt_small i n hi).mp ((isT_iff _).mp ht)
      have hadd : Ops.addi 32 i 1 = i + 1 := by
        simp only [Ops.addi, show (2:Nat) ^ 32 = 4294967296 from rfl]; omega
      rw [step_t (k + 1) ht, hadd]
      exact ih (i + 1) _ (by omega) (fun _ => by omega) (fun _ => by omega)

theorem kC_run (F a n : Nat) : kC F a n = P.run F 0 [a, n, 0, 0] := rfl

theorem kC_total (a n : Nat) : ∃ r, kC (2147483648 + 1) a n = some r := by
  rw [kC_run]
  exact run_total a n 2147483648 0 0 (by decide) (fun _ => Nat.zero_le _) (fun _ => by omega)

/-- **Every input.** For every `(a, n)` the C returns some `r` (within `2^31 + 1` steps), and both graphs (research's
fixture and the plain rewrite) have a complete run ending with `[r]` on the output; every complete run of either, under
any schedule, ends there. -/
theorem same_all (a n : Nat) : ∃ r, kC (2147483648 + 1) a n = some r ∧
    ((∃ k, Run (step Formal.Net.AutoApClorig.G) (Formal.Net.AutoApClorig.St Formal.Rewrite.ApClorigHw.T0 [a, n]) k
        (Formal.Net.AutoApClorig.St Formal.Rewrite.ApClorigHw.T2 [r])) ∧
      ∀ m t, Run (step Formal.Net.AutoApClorig.G) (Formal.Net.AutoApClorig.St Formal.Rewrite.ApClorigHw.T0 [a, n]) m t →
        Terminal (step Formal.Net.AutoApClorig.G) t → t = Formal.Net.AutoApClorig.St Formal.Rewrite.ApClorigHw.T2 [r]) ∧
    ((∃ k, Run (step Formal.Net.AutoApClPlain.G) (Formal.Net.AutoApClPlain.St Formal.Rewrite.ApClPlainHw.T0 [a, n]) k
        (Formal.Net.AutoApClPlain.St Formal.Rewrite.ApClPlainHw.T2 [r])) ∧
      ∀ m t, Run (step Formal.Net.AutoApClPlain.G) (Formal.Net.AutoApClPlain.St Formal.Rewrite.ApClPlainHw.T0 [a, n]) m t →
        Terminal (step Formal.Net.AutoApClPlain.G) t → t = Formal.Net.AutoApClPlain.St Formal.Rewrite.ApClPlainHw.T2 [r]) := by
  obtain ⟨r, hr⟩ := kC_total a n
  exact ⟨r, hr, CountloopSame.same hr⟩

end Formal.Rewrite.Plain.CountloopTotal

