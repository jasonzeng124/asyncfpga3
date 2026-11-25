#!/usr/bin/env python3
"""entryinv_patch.py TOOLSCOPY -- runtime patch (after ineq_patch.py) to a COPY of autoproof.py, AP_ENTRYINV=1:
the start template's invariants also include `x = e` for each C local x whose entry value e (cfront's P.entry,
an expression over the parameters) is neither a variable nor a literal (e.g. lfsrfind's x = seed & 0xFFFF).
These hold at entry by construction; Lean re-checks the entry and every obligation that targets the template.
The numerical samplers (polarity, rand_state, samples, check) compute such variables from the others instead
of drawing them at random (otherwise no random state satisfies them)."""
import sys, os, re
T = sys.argv[1]
a = os.path.join(T, 'autoproof', 'autoproof.py'); s = open(a).read()
def rep(old, new, cnt=1):
    global s
    assert s.count(old) == cnt, (old, s.count(old))
    s = s.replace(old, new)
rep("        self.infer_inv()\n        self.infer_rho()\n",
    "        self.infer_inv()\n"
    "        if os.environ.get('AP_ENTRYINV') == '1':\n"
    "            for i, e in enumerate(P.entry):\n"
    "                if e[0] not in ('var', 'lit') and maxvar(e) < len(P.params) and (('var', i), e) not in self.Is[0]:\n"
    "                    self.Is[0].append((('var', i), e))\n"
    "                    print(f'  entry inv T0: {P.vars[i]} = {show(e, P.vars)}', file=sys.stderr)\n"
    "        self.infer_rho()\n")
# every sampler: after the var = var copies, compute var = expression invariants
pat = re.compile(r"( +)for i, j in eqs:\n\1    st\[i\] = st\[j\]\n")
KS = iter(["k", "k", "m[0]", "k"])   # polarity, rand_state, samples, check (file order)
def fix(m):
    ind = m.group(1)
    return m.group(0) + f"{ind}self._fill_inv(st, {next(KS)})\n"
s, n = pat.subn(fix, s)
assert n == 4, n
s = s.replace("    def polarity(self, k, n=400, seed=5):\n",
    "    def _fill_inv(self, st, k):\n"
    "        for a_, b_ in self.Is[k]:\n"
    "            if a_[0] == 'var' and b_[0] in ('bin', 'un', 'sel'):\n"
    "                st[a_[1]] = ev(b_, st)\n\n"
    "    def polarity(self, k, n=400, seed=5):\n", 1)
open(a, 'w').write(s)
