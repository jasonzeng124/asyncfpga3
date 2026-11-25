#!/usr/bin/env python3
"""opsx2_patch.py TOOLSCOPY -- runtime patch (after opsx_patch.py) to a COPY of autoproof.py, AP_OPSX2=1:
auto_ops2_pre also rewrites `x &&& 255` / `x &&& 65535` to `x % 2^n`, and unsigned `Ops.cmpi` at ANY
width to an `if` on `% 2^w` (AutoLib's auto_ops only has widths 1 and 32; packed ring cells compare at
8 / 9 / 33 bits). All lemmas proved in the generated file, Core Lean only."""
import sys, os
T = sys.argv[1]
a = os.path.join(T, 'autoproof', 'autoproof.py'); s = open(a).read()
def rep(old, new, cnt=1):
    global s
    assert s.count(old) == cnt, (old, s.count(old))
    s = s.replace(old, new)
LEM = r'''theorem and_m255 (x : Nat) : x &&& 255 = x % 256 := Nat.and_two_pow_sub_one_eq_mod x 8
theorem and_m65535 (x : Nat) : x &&& 65535 = x % 65536 := Nat.and_two_pow_sub_one_eq_mod x 16
theorem cw_eq {w a b : Nat} : Ops.cmpi .eq w a b = if a % 2 ^ w = b % 2 ^ w then 1 else 0 := by
  unfold Ops.cmpi Ops.b2n; by_cases h : a % 2 ^ w = b % 2 ^ w <;> simp [h]
theorem cw_ne {w a b : Nat} : Ops.cmpi .ne w a b = if ¬ a % 2 ^ w = b % 2 ^ w then 1 else 0 := by
  unfold Ops.cmpi Ops.b2n; by_cases h : a % 2 ^ w = b % 2 ^ w <;> simp [h]
theorem cw_ult {w a b : Nat} : Ops.cmpi .ult w a b = if a % 2 ^ w < b % 2 ^ w then 1 else 0 := by
  unfold Ops.cmpi Ops.b2n; by_cases h : a % 2 ^ w < b % 2 ^ w <;> simp [h]
theorem cw_ule {w a b : Nat} : Ops.cmpi .ule w a b = if a % 2 ^ w ≤ b % 2 ^ w then 1 else 0 := by
  unfold Ops.cmpi Ops.b2n; by_cases h : a % 2 ^ w ≤ b % 2 ^ w <;> simp [h]
theorem cw_ugt {w a b : Nat} : Ops.cmpi .ugt w a b = if b % 2 ^ w < a % 2 ^ w then 1 else 0 := by
  unfold Ops.cmpi Ops.b2n; by_cases h : b % 2 ^ w < a % 2 ^ w <;> simp [h]
theorem cw_uge {w a b : Nat} : Ops.cmpi .uge w a b = if b % 2 ^ w ≤ a % 2 ^ w then 1 else 0 := by
  unfold Ops.cmpi Ops.b2n; by_cases h : b % 2 ^ w ≤ a % 2 ^ w <;> simp [h]
theorem mod_mod_le (x a b : Nat) (h0 : 0 < a) (h : a ≤ b) : x % a % b = x % a :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ h0) h)
theorem xb16 (a b : Nat) : a < 65536 → b < 65536 → a ^^^ b < 65536 := fun h1 h2 => Nat.xor_lt_two_pow (n := 16) h1 h2
theorem xb32 (a b : Nat) : a < 4294967296 → b < 4294967296 → a ^^^ b < 4294967296 :=
  fun h1 h2 => Nat.xor_lt_two_pow (n := 32) h1 h2
open Lean Meta Elab Tactic in
partial def xorTerms (e : Expr) (acc : Array Expr) : Array Expr :=
  let acc := if (e.isAppOfArity ``HXor.hXor 6 || e.isAppOfArity ``HAnd.hAnd 6) && (e.getArg! 0).isConstOf ``Nat &&
      !e.hasLooseBVars && !acc.contains e
    then acc.push e else acc
  match e with
  | .app f a => xorTerms a (xorTerms f acc)
  | .lam _ t b _ => xorTerms b (xorTerms t acc)
  | .forallE _ t b _ => xorTerms b (xorTerms t acc)
  | .letE _ t v b _ => xorTerms b (xorTerms v (xorTerms t acc))
  | .mdata _ b => xorTerms b acc
  | _ => acc
open Lean Meta Elab Tactic in
/-- For every Nat `a ^^^ b` in the goal and the hypotheses, add `a, b < 2^16 → a ^^^ b < 2^16` and the
same for 2^32; for every `a &&& b`, `a &&& b ≤ a` and `≤ b` (proved facts, for omega). -/
elab "xor_bounds" : tactic => withMainContext do
  let mut ts : Array Expr := xorTerms (← instantiateMVars (← getMainTarget)) #[]
  for d in ← getLCtx do
    if !d.isImplementationDetail then ts := xorTerms (← instantiateMVars d.type) ts
  for x in ts do
    let a ← Term.exprToSyntax (x.getArg! 4)
    let b ← Term.exprToSyntax (x.getArg! 5)
    if x.isAppOfArity ``HXor.hXor 6 then
      evalTactic (← `(tactic| have := xb16 $a $b))
      evalTactic (← `(tactic| have := xb32 $a $b))
    else
      evalTactic (← `(tactic| have := @Nat.and_le_left $a $b))
      evalTactic (← `(tactic| have := @Nat.and_le_right $a $b))
/-- AutoLib's `auto_ops` with, after the case split on each `if`, literal folding again and the xor bounds
(local, opsx2 patch). -/
macro "auto_ops3" : tactic => `(tactic| (
  try simp only [E.eval, BOp.ev, UOp.ev, Ops.addi, Ops.subi, Ops.muli, Ops.andi, Ops.ori,
    Ops.xori, Ops.shli, Ops.shrui, Ops.trunci, Ops.extui, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod, Nat.reducePow, Nat.reduceMod, Nat.pow_one] at *
  try simp only [c_eq1, c_ne1, c_ult1, c_ule1, c_ugt1, c_uge1, c_slt1, c_sle1, c_sgt1, c_sge1, c_eq32, c_ne32, c_ult32, c_ule32, c_ugt32, c_uge32, c_slt32, c_sle32, c_sgt32, c_sge32, shrsi32, sel_ite, select_ite, isT_ite_t, isT_ite_f, ite_mod2, ite_mod32,
    ite_eq0, ite_eq1, ite_eq0m2, ite_eq1m2, ite_eq0m32, ite_eq1m32, ite_or, ite_and, ite_xor,
    isT_true, isT_false] at *
  all_goals revert_props
  all_goals (repeat' ite_case)
  all_goals (intros; (try simp only [Nat.reducePow, Nat.reduceMod, Nat.reduceAnd, Nat.reduceXor, Nat.reduceOr,
    Nat.reduceDiv, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.xor_zero, Nat.zero_xor] at *); all_goals (xor_bounds; omega))))

/-- `auto_ops` after'''
rep("\\n/-- `auto_ops` after", "\\n" + LEM.replace("\\", "\\\\").replace("'", "\\'").replace("\n", "\\n"))
rep("and_m3, and_m7, and_m15, and_m31, xor31_shr27] at *",
    "and_m3, and_m7, and_m15, and_m31, xor31_shr27, and_m255, and_m65535, List.getD_cons_zero, List.getD_cons_succ] at *\\n  try simp only [cw_eq, cw_ne, cw_ult, cw_ule, cw_ugt, cw_uge, Nat.reducePow, Nat.reduceMod] at *\\n  try simp only [Nat.mod_mod, mod_mod_le, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceMod, Nat.reduceAdd] at *")
rep("     auto_ops))\\n'", "     auto_ops)\\n  | (auto_ops2_pre; auto_ops3))\\n'")
rep('w("  first | rfl | (simp only [ρ, P, List.getD, List.map, List.cons.injEq, and_true]; auto_ops)\\n")',
    'w("  first | rfl | (simp only [ρ, P, List.getD, List.getD_cons_zero, List.getD_cons_succ, List.map, List.cons.injEq, and_true]; auto_ops2)\\n")')
rep('w("  first | rfl | (simp only [InvH, Is, P, List.getD, List.map, List.cons.injEq, and_true]; auto_ops)\\n")',
    'w("  first | rfl | (simp only [InvH, Is, P, List.getD, List.map, List.cons.injEq, and_true]; auto_ops2)"\n'
    '      " | (rw [show Is.getD 0 [] = [" + ", ".join(f"({e_lean(a)}, {e_lean(b)})" for a, b in C.Is[0]) + "] from rfl]; "\n'
    '      "simp only [InvH, P, List.map, List.cons.injEq, and_true]; (repeat\' apply And.intro); all_goals auto_ops2)\\n")')
open(a, 'w').write(s)
