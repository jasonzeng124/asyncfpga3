#!/usr/bin/env python3
"""opsx4_patch.py TOOLSCOPY -- runtime patch (after opsx_patch.py and opsx2_patch.py) to a COPY of autoproof.py,
AP_OPSX4=1: generated files get one more local fallback of auto_ops2, `auto_ops2_pre; all_goals auto_ops4` (pre may already close the goal), with `auto_ops4` = AutoLib's auto_ops whose last
step folds `if True` / `if False` before the case split and, after it, also simplifies the conjunction hypotheses (`ite_case` also splits an `if`
inside the reverted invariant hypothesis hI, which can leave `.. ∧ False` there; omega does not see through it):
omega, else `simp only [and_false, ...] at *` (closes the goal on a False hypothesis), else simp then omega.
The leaf lemma's last line becomes `all_goals auto_ops2` (the preceding\n`simp only [hI]` may already close the goal). Proof search only: every lemma is still checked by Lean."""
import sys, os
T = sys.argv[1]
a = os.path.join(T, 'autoproof', 'autoproof.py'); s = open(a).read()
def rep(old, new):
    global s
    assert s.count(old) == 1, (old, s.count(old))
    s = s.replace(old, new)
LEM = '''/-- AutoLib's `auto_ops` whose last step also simplifies conjunctions in the hypotheses (local, opsx4 patch). -/
macro "auto_ops4" : tactic => `(tactic| (
  try simp only [E.eval, BOp.ev, UOp.ev, Ops.addi, Ops.subi, Ops.muli, Ops.andi, Ops.ori,
    Ops.xori, Ops.shli, Ops.shrui, Ops.trunci, Ops.extui, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod, Nat.reducePow, Nat.reduceMod, Nat.pow_one] at *
  try simp only [c_eq1, c_ne1, c_ult1, c_ule1, c_ugt1, c_uge1, c_slt1, c_sle1, c_sgt1, c_sge1, c_eq32, c_ne32, c_ult32, c_ule32, c_ugt32, c_uge32, c_slt32, c_sle32, c_sgt32, c_sge32, shrsi32, sel_ite, select_ite, isT_ite_t, isT_ite_f, ite_mod2, ite_mod32,
    ite_eq0, ite_eq1, ite_eq0m2, ite_eq1m2, ite_eq0m32, ite_eq1m32, ite_or, ite_and, ite_xor,
    isT_true, isT_false, ↓reduceIte, not_true_eq_false, not_false_eq_true] at *
  all_goals revert_props
  all_goals (repeat' ite_case)
  all_goals (intros; first
    | omega
    | (simp only [and_false, false_and] at *; done)
    | (simp only [and_false, false_and, and_true, true_and, and_self, not_true_eq_false, not_false_eq_true] at *; omega))))

/-- `auto_ops` after'''
rep("\\n/-- `auto_ops` after", "\\n" + LEM.replace("\\", "\\\\").replace("'", "\\'").replace("\n", "\\n"))
rep("  | (auto_ops2_pre; auto_ops3))\\n'", "  | (auto_ops2_pre; auto_ops3)\\n  | (auto_ops2_pre; all_goals auto_ops4))\\n'")
# the leaf's `try simp only [hI] at h ⊢` can already close the goal (an invariant hypothesis is the target):
# run the tactic on the remaining goals only
rep('        L.append("  auto_ops2")\n', '        L.append("  all_goals auto_ops2")\n')
open(a, 'w').write(s)
