#!/usr/bin/env python3
"""truncinv_patch.py TOOLSCOPY -- runtime patch (after ineq_patch.py) to a COPY of autoproof.py, AP_TRUNCINV=1:
template invariants `trunci 32 x = x` (x < 2^32 as a Nat) for each C variable x that is < 2^32 on every reachable
state for a syntactic reason: its entry value and every update of it is a literal < 2^32, an operator result of
width <= 32 (every Ops result is reduced mod 2^w), a select of such, or itself / another such variable (a fixed
point over the variables; parameters are raw Nats at entry and are never included). The C state is a list of Nats
and the obligations quantify over all of them, so e.g. `return i` against the graph's literal 256 needs i < 2^32.
Lean re-checks the entry and every target obligation. Also guards two samplers against invariants whose left side
is not a variable."""
import sys, os
T = sys.argv[1]
a = os.path.join(T, 'autoproof', 'autoproof.py'); s = open(a).read()
def rep(old, new, cnt=1):
    global s
    assert s.count(old) == cnt, (old, s.count(old))
    s = s.replace(old, new)
rep('eqs = [(a[1], b[1]) for a, b in self.Is[k] if b[0] == "var"]',
    'eqs = [(a[1], b[1]) for a, b in self.Is[k] if b[0] == "var" and a[0] == "var"]')
rep('eqs = [(a[1], b[1]) for a, b in self.Is[m[0]] if b[0] == "var"]',
    'eqs = [(a[1], b[1]) for a, b in self.Is[m[0]] if b[0] == "var" and a[0] == "var"]')
rep("        self.infer_rho()\n", '''        if os.environ.get('AP_TRUNCINV') == '1':
            def bnd(e, ok, entry):
                t = e[0]
                if t == "lit":
                    return e[1] < 2 ** 32
                if t == "var":
                    return (not entry) and e[1] in ok
                if t == "un":
                    return (e[2] <= 32) if e[1] in ("trunci", "extui") else (e[1][1] <= 32)
                if t == "bin":
                    return e[2] <= 32
                return bnd(e[2], ok, entry) and bnd(e[3], ok, entry)
            ok = set(range(len(P.params), len(P.vars)))
            while True:
                ok2 = {i for i in ok if bnd(P.entry[i], ok, True) and all(bnd(ce[2][i], ok, False) for ce in P.edges)}
                if ok2 == ok:
                    break
                ok = ok2
            for k in self.K:
                if self.obs[k]:
                    for i in sorted(ok):
                        self.Is[k].append((("un", "trunci", 32, ("var", i)), ("var", i)))
            print(f"  trunc inv: {[P.vars[i] for i in sorted(ok)]}", file=sys.stderr)
        self.infer_rho()
''')
open(a, 'w').write(s)
