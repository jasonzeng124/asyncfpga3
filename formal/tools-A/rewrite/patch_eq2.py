#!/usr/bin/env python3
"""patch_eq2.py FILE.lean -- shard A: close the collatz `n' == 1 <=> n == 2` obligations of an autoproof file.

autoproof's generic tactic (`auto_ops`) times out on the one obligation that IS the rewrite (graph: `eq(n, 2)`; C:
`eq(ne(n', 1), 0)` with n' the collatz update). Each such theorem's proof is replaced by the hand lemma
`Formal.Rewrite.Eq2.collatz_eq2` (any width w >= 3). Every other generated line is kept. Lean checks the result;
nothing here is trusted. Refuses unless it patches at least one theorem and each patched statement has exactly the
expected shape.
"""
import re, sys
p = sys.argv[1]
src = open(p).read()
W = sys.argv[2] if len(sys.argv) > 2 else "32"
upd = ("(.sel (.bin (.cmpi .eq) %s (.bin .andi %s (.var 0) (.lit 1)) (.lit 0)) (.bin .shrsi %s (.var 0) (.lit 1)) "
       "(.bin .addi %s (.bin .muli %s (.lit 3) (.var 0)) (.lit 1)))") % ((W,) * 5)
stmt = ("E.eval σ (.bin (.cmpi .eq) %s (.var 0) (.lit 2)) = E.eval σ (.bin (.cmpi .eq) %s (.bin (.cmpi .ne) %s %s "
        "(.lit 1)) (.lit 0)) := by\n") % (W, W, W, upd)
pat = re.compile(r"(theorem (o\d+_\d+) \(σ : List Nat\)[^\n]*\n(?:    [^\n]*\n)*?    " + re.escape(stmt) + r")((?:  [^\n]*\n)+)")
n = 0
def rep(m):
    global n
    n += 1
    return m.group(1) + ("  simp only [E.eval, BOp.ev]\n"
                         "  exact (Formal.Rewrite.Eq2.collatz_eq2 %s _ (by decide)).symm\n" % W)
src = pat.sub(rep, src)
if n == 0: sys.exit("patch_eq2: no obligation of the expected shape")
if "import Formal.Rewrite.Eq2" not in src:
    src = src.replace("import Formal.Net.AutoLib\n", "import Formal.Net.AutoLib\nimport Formal.Rewrite.Eq2\n", 1)
open(p, "w").write(src)
print("patch_eq2: %d obligation(s) closed by collatz_eq2" % n)
