#!/usr/bin/env python3
"""ineq_patch.py TOOLSCOPY -- runtime patch to a COPY of autoproof.py: reachability invariants.

autoproof's template invariants `Is` are equations var = lit / var = var only. This adds
inequality invariants, encoded as equations `cmpi p x y = 1` (so AutoLib's InvH / MatchSem /
sim_call and the generated proof shape are unchanged; auto_ops turns `ite .. = 1` into the
proposition). Candidates: slt / sle between two C variables. Kept: those true on every
co-simulation observation of the template (Houdini start), then iteratively dropped when not
numerically inductive along the pairing M (and the entry), then greedily minimised: dropped
when the numerical check still passes without it. Lean re-checks everything (the hypotheses
`hI` and target obligations `ja/jb` are generated as for the equations).
Enabled when AP_INEQ=1."""
import sys, os
T = sys.argv[1]
a = os.path.join(T, 'autoproof', 'autoproof.py'); s = open(a).read()

def rep(old, new, cnt=1):
    global s
    assert s.count(old) == cnt, (old, s.count(old))
    s = s.replace(old, new)

# 1. hook after infer_matches
rep("        self.infer_matches()\n        self.bad = self.search()\n",
    "        self.infer_matches()\n        if os.environ.get('AP_INEQ') == '1':\n            self.infer_ineq()\n"
    "        self.bad = self.search()\n")

# 2. samples(): also filter on all invariants
rep("            if (ev(ob[\"t\"], st) % 2 == 1) == ob[\"br\"]:\n                out.append(st)\n",
    "            if (ev(ob[\"t\"], st) % 2 == 1) == ob[\"br\"] and all(ev(x, st) == ev(y, st) for x, y in zip(ob[\"ia\"], ob[\"ib\"])):\n                out.append(st)\n")

# 3. polarity(): filter on invariants
rep("            if (ev(t, st) % 2) == (ev(gf, st) % 2):\n",
    "            if any(ev(x, st) != ev(y, st) for x, y in self.Is[k]):\n                continue\n"
    "            if (ev(t, st) % 2) == (ev(gf, st) % 2):\n")

# 4. check(): only literal equations go into `fixed`; more tries
rep("            fixed = {a[1]: b[1] for a, b in self.Is[k]}\n",
    "            fixed = {a[1]: b[1] for a, b in self.Is[k] if a[0] == 'var' and b[0] == 'lit'}\n"
    "            eqs = [(a[1], b[1]) for a, b in self.Is[k] if a[0] == 'var' and b[0] == 'var']\n")
rep("                      for i in range(nv)]\n                if (ev(ob[\"t\"], st) % 2 == 1) != ob[\"br\"]:\n",
    "                      for i in range(nv)]\n                for i, j in eqs:\n                    st[i] = st[j]\n"
    "                if (ev(ob[\"t\"], st) % 2 == 1) != ob[\"br\"]:\n")

# 5. the inference
rep("    # ---- obligations in substituted form, and their numerical check ----\n", '''    def rand_state(self, k, rnd):
        nv = len(self.P.vars)
        special = [0, 1, 2, 3, 2 ** 31 - 1, 2 ** 31, 2 ** 32 - 1, 2 ** 31 + 1, 2 ** 31 - 2, 2 ** 32 - 2]
        fixed = {a[1]: b[1] for a, b in self.Is[k] if a[0] == 'var' and b[0] == 'lit'}
        eqs = [(a[1], b[1]) for a, b in self.Is[k] if a[0] == 'var' and b[0] == 'var']
        st = [fixed.get(i, rnd.choice([rnd.randrange(M32), rnd.randrange(40), rnd.choice(special)])) for i in range(nv)]
        for i, j in eqs:
            st[i] = st[j]
        return st

    def infer_ineq(self, tries=20000):
        P = self.P
        nv = len(P.vars)
        ONE = ("lit", 1)
        base = {k: list(self.Is[k]) for k in range(len(self.Is))}
        cand = {}
        for k in self.K:
            if not self.obs[k]:
                continue
            cs = []
            for i in range(nv):
                for j in range(nv):
                    if i == j:
                        continue
                    for p in ("slt", "sle"):
                        e = ("bin", ("cmpi", p), 32, ("var", i), ("var", j))
                        if all(ev(e, o[1]) == 1 for o in self.obs[k]) and \\
                           not all(ev(x, o[1]) == ev(y, o[1]) for o in self.obs[k] for x, y in [(("var", i), ("var", j))]):
                            cs.append(e)
                        elif p == "sle" and all(ev(e, o[1]) == 1 for o in self.obs[k]):
                            pass
            # sle implied by slt on the same pair: keep only slt then
            cs = [e for e in cs if not (e[1][1] == "sle" and ("bin", ("cmpi", "slt"), 32, e[3], e[4]) in cs)]
            cand[k] = cs
        rnd = random.Random(3)

        def setIs(c):
            for k in range(len(self.Is)):
                self.Is[k] = base[k] + [(e, ONE) for e in c.get(k, [])]

        def holds(I, st):
            return all(ev(x, st) == ev(y, st) for x, y in I)

        changed = True
        while changed:
            changed = False
            setIs(cand)
            for (k, ci, gi) in self.M:
                ce = P.edges[ci]
                if ce[3] is None:
                    continue
                k2 = self.ga.edges[gi]["dst"]
                if not cand.get(k2):
                    continue
                n = 0
                for _ in range(tries):
                    st = self.rand_state(k, rnd)
                    if (ev(P.tests[ce[0]], st) % 2 == 1) != ce[1] or not holds(self.Is[k], st):
                        continue
                    n += 1
                    new = [ev(x, st) for x in ce[2]]
                    bad = [e for e in cand[k2] if ev(e, new) != 1]
                    if bad:
                        cand[k2] = [e for e in cand[k2] if e not in bad]
                        changed = True
                        setIs(cand)
                        break
                    if n > 400:
                        break
        setIs(cand)
        # minimise: drop each one if the check still passes without it (and no new failure)
        if self.check(n=400):
            pass  # not enough on its own; keep all
        else:
            for k in list(cand):
                for e in list(cand[k]):
                    trial = dict(cand)
                    trial[k] = [x for x in cand[k] if x != e]
                    setIs(trial)
                    # dropping must keep both the obligations and inductiveness (checked by check's ja/jb)
                    if not self.check(n=600):
                        cand = trial
                    setIs(cand)
        setIs(cand)
        for k in cand:
            if cand[k]:
                print(f"  ineq T{k}: " + ", ".join(show(e, P.vars) for e in cand[k]), file=sys.stderr)

    # ---- obligations in substituted form, and their numerical check ----
''')
open(a, 'w').write(s)
