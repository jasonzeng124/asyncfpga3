import Formal.Net.AutoLib
open Formal.Net.GcdHw Formal.Net.Auto

def absE (x y : E) : E :=
  .sel (.bin (.cmpi .sgt) 32 (.bin .subi 32 x y) (.lit 4294967295)) (.bin .subi 32 x y)
    (.bin .subi 32 (.lit 0) (.bin .subi 32 x y))

example : ∀ σ : List Nat, isT ((E.lit 1).eval σ) = true →
    isT ((E.lit 1).eval σ) = true ∧ [(absE (.var 0) (.var 1)).eval σ] = [(absE (.var 1) (.var 0)).eval σ] := by
  auto_match

-- ipow body: graph select vs C if-converted select
example : ∀ σ : List Nat, isT ((E.bin (.cmpi .sgt) 32 (.var 2) (.lit 0)).eval σ) = true →
    isT ((E.bin (.cmpi .sgt) 32 (.var 2) (.lit 0)).eval σ) = true ∧
    [(E.sel (.bin (.cmpi .eq) 1 (.bin .andi 1 (.un .trunci 1 (.var 2)) (.lit 1)) (.lit 0)) (.var 0) (.bin .muli 32 (.var 0) (.var 1))).eval σ] =
    [(E.sel (.bin (.cmpi .eq) 32 (.bin .andi 32 (.var 2) (.lit 1)) (.lit 1)) (.bin .muli 32 (.var 0) (.var 1)) (.var 0)).eval σ] := by
  auto_match

-- collatz strength reduction
example : ∀ σ : List Nat, isT ((E.lit 1).eval σ) = true →
    [(E.bin .addi 32 (.bin .addi 32 (.var 0) (.bin .shli 32 (.var 0) (.lit 1))) (.lit 1)).eval σ] =
    [(E.bin .addi 32 (.bin .muli 32 (.lit 3) (.var 0)) (.lit 1)).eval σ] := by
  auto_match

-- gcd strip guard: graph ori i1 form vs C  (x&1)==0 && x>=1 , negated polarity
example : ∀ σ : List Nat,
    isT ((E.sel (.bin (.cmpi .eq) 32 (.bin .andi 32 (.var 0) (.lit 1)) (.lit 0)) (.bin (.cmpi .sge) 32 (.var 0) (.lit 1)) (.lit 0)).eval σ) = false →
    isT ((E.bin .ori 1 (.bin (.cmpi .ne) 1 (.bin .andi 1 (.un .trunci 1 (.var 0)) (.lit 1)) (.lit 0)) (.bin (.cmpi .slt) 32 (.var 0) (.lit 1))).eval σ) = true := by
  intro σ h
  auto_ops
-- a FALSE one must fail: abs vs plain subtraction
example : ∀ σ : List Nat, isT ((E.lit 1).eval σ) = true →
    [(absE (.var 0) (.var 1)).eval σ] = [(E.bin .subi 32 (.var 0) (.var 1)).eval σ] := by
  auto_match
