import Formal.Net.AutoLib
open Formal.Net.GcdHw Formal.Net.Auto

-- abs swap (the gcd equivalent mutant)
example : ∀ σ : List Nat, ([] : List E).map (E.eval σ) = ([] : List E).map (E.eval σ) → isT ((E.lit 1).eval σ) = true →
    isT ((E.lit 1).eval σ) = true ∧ [(E.sel (.bin (.cmpi .sgt) 32 (.bin .subi 32 (.var 0) (.var 1)) (.lit 4294967295)) (.bin .subi 32 (.var 0) (.var 1)) (.bin .subi 32 (.lit 0) (.bin .subi 32 (.var 0) (.var 1))))].map (E.eval σ) = [(E.sel (.bin (.cmpi .sgt) 32 (.bin .subi 32 (.var 1) (.var 0)) (.lit 4294967295)) (.bin .subi 32 (.var 1) (.var 0)) (.bin .subi 32 (.lit 0) (.bin .subi 32 (.var 1) (.var 0))))].map (E.eval σ) ∧ ([] : List E).map (E.eval σ) = ([] : List E).map (E.eval σ) := by
  auto_match

-- ipow body
example : ∀ σ : List Nat, ([] : List E).map (E.eval σ) = ([] : List E).map (E.eval σ) → isT ((E.bin (.cmpi .sgt) 32 (.var 2) (.lit 0)).eval σ) = true →
    isT ((E.bin (.cmpi .sgt) 32 (.var 2) (.lit 0)).eval σ) = true ∧
    [(E.sel (.bin (.cmpi .eq) 1 (.bin .andi 1 (.un .trunci 1 (.var 2)) (.lit 1)) (.lit 0)) (.var 0) (.bin .muli 32 (.var 0) (.var 1))).eval σ] =
    [(E.sel (.bin (.cmpi .eq) 32 (.bin .andi 32 (.var 2) (.lit 1)) (.lit 1)) (.bin .muli 32 (.var 0) (.var 1)) (.var 0)).eval σ] ∧ True := by
  intro σ hI h
  refine ⟨?_, ?_, trivial⟩
  · auto_ops
  · simp only [List.cons.injEq, and_true]; auto_ops

-- collatz strength reduction
example (σ : List Nat) :
    (E.bin .addi 32 (.bin .addi 32 (.var 0) (.bin .shli 32 (.var 0) (.lit 1))) (.lit 1)).eval σ =
    (E.bin .addi 32 (.bin .muli 32 (.lit 3) (.var 0)) (.lit 1)).eval σ := by
  auto_ops

-- gcd strip guard, negated polarity
example (σ : List Nat) (h : isT ((E.sel (.bin (.cmpi .eq) 32 (.bin .andi 32 (.var 0) (.lit 1)) (.lit 0)) (.bin (.cmpi .sge) 32 (.var 0) (.lit 1)) (.lit 0)).eval σ) = false) :
    isT ((E.bin .ori 1 (.bin (.cmpi .ne) 1 (.bin .andi 1 (.un .trunci 1 (.var 0)) (.lit 1)) (.lit 0)) (.bin (.cmpi .slt) 32 (.var 0) (.lit 1))).eval σ) = true := by
  auto_ops

-- invariant use: graph extui 1 q + 1 vs C k+1 under k = 0
example (σ : List Nat) (hI : σ.getD 2 0 = 0) :
    (E.bin .addi 32 (.un .extui 1 (.var 2)) (.lit 1)).eval σ = (E.bin .addi 32 (.var 2) (.lit 1)).eval σ := by
  auto_ops

-- shrsi
example (σ : List Nat) :
    (E.bin .shrsi 32 (E.bin .shrsi 32 (.var 0) (.lit 1)) (.lit 1)).eval σ = (E.bin .shrsi 32 (.var 0) (.lit 2)).eval σ := by
  auto_ops

-- a FALSE one must fail: abs vs plain subtraction
example (σ : List Nat) :
    (E.sel (.bin (.cmpi .sgt) 32 (.bin .subi 32 (.var 0) (.var 1)) (.lit 4294967295)) (.bin .subi 32 (.var 0) (.var 1)) (.bin .subi 32 (.lit 0) (.bin .subi 32 (.var 0) (.var 1)))).eval σ = (E.bin .subi 32 (.var 0) (.var 1)).eval σ := by
  auto_ops
