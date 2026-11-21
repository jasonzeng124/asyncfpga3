import Formal.Net.AutoLib
open Formal.Net.GcdHw Formal.Net.Auto
set_option maxHeartbeats 400000
theorem c1 (σ : List Nat) (hI : σ.getD 1 0 = 0) (h : isT (E.eval σ (.bin (.cmpi .ne) 32 (.var 0) (.lit 1))) = true) :
  E.eval σ (.sel (.bin (.cmpi .eq) 1 (.bin .andi 1 (.un .trunci 1 (.var 0)) (.lit 1)) (.lit 0)) (.bin .shrsi 32 (.var 0) (.lit 1)) (.bin .addi 32 (.bin .addi 32 (.var 0) (.bin .shli 32 (.var 0) (.lit 1))) (.lit 1))) =
  E.eval σ (.sel (.bin (.cmpi .eq) 32 (.bin .andi 32 (.var 0) (.lit 1)) (.lit 0)) (.bin .shrsi 32 (.var 0) (.lit 1)) (.bin .addi 32 (.bin .muli 32 (.lit 3) (.var 0)) (.lit 1))) := by
  auto_ops
theorem c3 (σ : List Nat) (z : Nat) :
  E.eval (σ ++ [z]) (.bin (.cmpi .eq) 32 (.var 2) (.lit 1)) = E.eval (σ ++ [z])  (.bin (.cmpi .eq) 32 (.bin (.cmpi .ne) 32 (.var 2) (.lit 1)) (.lit 0)) := by
  auto_ops
