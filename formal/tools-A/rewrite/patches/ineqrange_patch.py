#!/usr/bin/env python3
"""ineqrange_patch.py TOOLSCOPY -- runtime patch (after ineq_patch.py) to a COPY of autoproof.py, AP_INEQR=1:
the inequality-invariant candidates also include range facts `cmpi ult x 2^w = 1` (w = 1, 8, 16; the
smallest w true on every observation), e.g. twoloops' m = x & 255 < 256, which the graph's 8-bit channel
for m needs; and signed bounds `sle(0, x)`, `sle(x, c)` for c the smallest positive literal of the C program
above every observation (lfsrfind's i <= 256). Same Houdini filter (observations, inductive along the pairing),
with half the samples put at a candidate's bound; the minimisation never drops these (extra true invariants only
add hypotheses). Lean re-checks everything."""
import sys, os
T = sys.argv[1]
a = os.path.join(T, 'autoproof', 'autoproof.py'); s = open(a).read()
old = "            cand[k] = cs\n"
new = '''            for i in range(nv):
                for w in (1, 8, 16):
                    e = ("bin", ("cmpi", "ult"), 32, ("var", i), ("lit", 2 ** w))
                    if all(ev(e, o[1]) == 1 for o in self.obs[k]) and not all(o[1][i] == o[1][i] * 0 for o in self.obs[k]):
                        cs.append(e)
                        break
            # signed bounds against the C program's literals: sle(0, x), and sle(x, c) for the smallest such c
            lits = sorted({x[1] for e_ in P.tests + [y for ce_ in P.edges for y in ce_[2]] for x in _lits(e_)
                           if 0 < x[1] < 2 ** 31})
            for i in range(nv):
                if all(o[1][i] < 2 ** 31 for o in self.obs[k]) and len({o[1][i] for o in self.obs[k]}) > 1:
                    cs.append(("bin", ("cmpi", "sle"), 32, ("lit", 0), ("var", i)))
                    for c in lits:
                        if all(o[1][i] <= c for o in self.obs[k]):
                            cs.append(("bin", ("cmpi", "sle"), 32, ("var", i), ("lit", c)))
                            break
            cand[k] = cs
'''
assert s.count(old) == 1
s = s.replace(old, new)
# Houdini sampling: half the samples put one range-candidate variable at its bound - 1 / - 2 (else
# random sampling rarely reaches the boundary and a non-inductive range fact survives)
old = "                    st = self.rand_state(k, rnd)\n                    if (ev(P.tests[ce[0]], st) % 2 == 1) != ce[1] or not holds(self.Is[k], st):\n"
new = """                    st = self.rand_state(k, rnd)
                    rc = [e for e in cand.get(k, []) if e[3][0] == "lit" or e[4][0] == "lit"]
                    if rc and rnd.random() < 0.5:
                        e = rnd.choice(rc)
                        if e[4][0] == "lit":
                            st[e[3][1]] = e[4][1] - rnd.choice([0, 1, 2]) - (e[1][1] == "ult")
                        else:
                            st[e[4][1]] = e[3][1] + rnd.choice([0, 1])
                        self._fill_inv(st, k) if hasattr(self, "_fill_inv") else None
                    if (ev(P.tests[ce[0]], st) % 2 == 1) != ce[1] or not holds(self.Is[k], st):
"""
assert s.count(old) == 1
s = s.replace(old, new)
# minimisation never drops a range fact (an extra true inductive invariant only adds hypotheses)
old = "                for e in list(cand[k]):\n"
new = "                for e in [x for x in cand[k] if not (x[3][0] == 'lit' or x[4][0] == 'lit')]:\n"
assert s.count(old) == 1
s = s.replace(old, new)
s = s.replace("class Corr:\n", """def _lits(e):
    if e[0] == "lit":
        return [e]
    if e[0] == "var":
        return []
    return [y for x in e[1:] if isinstance(x, tuple) and x and x[0] in ("var", "lit", "un", "bin", "sel") for y in _lits(x)]


class Corr:
""", 1)
open(a, 'w').write(s)
