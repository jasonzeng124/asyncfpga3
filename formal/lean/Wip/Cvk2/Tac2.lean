import Formal.Net.AutoLib
import Lean
open Formal.Net.GcdHw Formal.Net.Auto

open Lean Meta Elab Tactic in
/-- Case on the condition of one `if` (one whose condition has no `if` inside) and
rewrite it away. -/
elab "ite_case" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let isIte (e : Expr) : Bool := e.isAppOfArity ``ite 5
  let some e := t.find? (fun e => isIte e && !(e.getArg! 1).hasLooseBVars &&
      ((e.getArg! 1).find? isIte).isNone) | throwError "ite_case: no if"
  let stx ← Term.exprToSyntax (e.getArg! 1)
  evalTactic (← `(tactic| (by_cases hc : $stx
                           · simp only [hc, ↓reduceIte]
                           · simp only [hc, ↓reduceIte])))

example : ∀ σ : List Nat, isT ((E.lit 1).eval σ) = true →
    [(E.sel (.bin (.cmpi .sgt) 32 (.bin .subi 32 (.var 0) (.var 1)) (.lit 4294967295)) (.bin .subi 32 (.var 0) (.var 1)) (.bin .subi 32 (.lit 0) (.bin .subi 32 (.var 0) (.var 1))))].map (E.eval σ) = [(E.sel (.bin (.cmpi .sgt) 32 (.bin .subi 32 (.var 1) (.var 0)) (.lit 4294967295)) (.bin .subi 32 (.var 1) (.var 0)) (.bin .subi 32 (.lit 0) (.bin .subi 32 (.var 1) (.var 0))))].map (E.eval σ) := by
  intro σ h
  simp only [List.map, List.cons.injEq, and_true] at *
  try simp only [E.eval, BOp.ev, UOp.ev, c_eq, c_ne, c_ult, c_ule, c_ugt, c_uge, c_slt, c_sle,
    c_sgt, c_sge, sel_ite, isT_ite_t, isT_ite_f, ite_mod2, ite_mod32, ite_eq0, ite_eq1,
    ori1_ite, ori32_ite, andi1_ite, andi32_ite, trunci1_ite, extui1_ite, andi1_ite1,
    Nat.reducePow, Nat.reduceMod, Nat.zero_mod] at *
  try simp only [Ops.addi, Ops.subi, Ops.muli, Ops.andi, Ops.ori, Ops.xori, Ops.shli,
    Ops.shrui, Ops.shrsi, Ops.flip, Ops.trunci, Ops.extui, Ops.extsi, select_def,
    isT_true, isT_false, Nat.and_one_is_mod, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
    Nat.pow_one, Nat.pow_zero] at *
  repeat' ite_case
  all_goals omega
