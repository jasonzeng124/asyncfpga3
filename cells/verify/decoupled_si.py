#!/usr/bin/env python3
"""State-space exploration of the decoupled link controller (rtl/bd_link.v,
bd_link_dctl).

The four controller equations plus the two matched-delay chains are gates
with arbitrary delay; a four-phase source drives (req_in, a) and a
four-phase sink answers (req_out, ack_out).  Every interleaving of enabled
transitions is explored and the run reports

  hazards     a gate that was enabled and got disabled before it fired
              (semi-modularity -- the speed-independence test)
  protocol    an acknowledge or request edge out of four-phase order
  opacity     the latch reopening while the token it holds is still the
              one being offered, or an acknowledge without a fresh capture
  deadlocks   states with nothing enabled
  unreturned  states from which the initial state is unreachable

The controller is not fully speed-independent: `lt` is one LUT arc from `b`
and `a`, and the design relies on it settling before the neighbouring
controller can answer through a matched-delay chain, a wire, its own LUTs
and a wire back.  `--rt env` encodes exactly that assumption and nothing
else (while lt is stale the environment holds still; every internal gate,
including the request chain, may still race it).  Under it the LDN=0
controller is hazard-free in both BROAD modes; without it every hazard
reported is of the kind "lt was still stale after a whole round trip".
The bundled-data consequences of the same one-arc-versus-many facts are what
rules H, I and L of tighten.py measure on the routed netlist.

    decoupled_si.py [--broad 0|1] [--ldn 0|1] [--rt none|env] [-v]
"""
import argparse
import sys
from collections import deque

INTERNAL = ["B", "A", "R", "S", "Ld", "Lt"]
ENV = ["Rin", "Aout"]
ORDER = INTERNAL + ENV + ["Taken"]
INIT = dict(B=0, A=0, R=0, S=1, Ld=1, Lt=1, Rin=0, Aout=0, Taken=1)


def key(s):
    return tuple(s[k] for k in ORDER)


class Model:
    def __init__(self, broad=True, ldn=0, rt="none"):
        self.broad = broad
        self.ldn = ldn
        self.rt = rt

    # bd_link_dctl's LUT INITs, as set/reset equations
    def nxt(self, s):
        B, A, R, S, Ld, Lt, Rin, Aout = (s[k] for k in INTERNAL + ENV)
        n = {}
        n["B"] = (1 - (Aout & (1 - Ld))) if B else (Rin & Ld & (1 - Aout))
        n["A"] = (Rin | Ld) if A else (Rin & B & Ld)
        n["Ld"] = (1 - A) if Ld else (Lt & S & (1 - A))
        gate = Aout if self.broad else 0
        n["Lt"] = (1 - B) & (1 - A) & (1 - gate)
        n["R"] = B                          # rdly, any length
        n["S"] = Lt if self.ldn else 1      # us, or the constant when LDN=0
        return n

    @staticmethod
    def env_enabled(s):
        out = []
        if s["Rin"] == 0 and s["A"] == 0:
            out.append("Rin")
        if s["Rin"] == 1 and s["A"] == 1:
            out.append("Rin")
        if s["Aout"] != s["R"]:
            out.append("Aout")
        return out

    def enabled(self, s):
        n = self.nxt(s)
        g = [k for k in INTERNAL if n[k] != s[k]]
        if self.rt == "env" and "Lt" in g:
            return g, []
        return g, self.env_enabled(s)

    @staticmethod
    def fire(s, k):
        t = dict(s)
        t[k] = 1 - s[k]
        if k == "Aout" and t["Aout"] == 1:
            t["Taken"] = 1
        if k == "R" and t["R"] == 1:
            t["Taken"] = 0
        return t

    def explore(self):
        seen = {key(INIT): INIT}
        stack = [INIT]
        edges = []
        res = dict(hazards=[], protocol=[], opacity=[], deadlocks=[],
                   decoupled=False)
        while stack:
            s = stack.pop()
            g, e = self.enabled(s)
            if not g and not e:
                res["deadlocks"].append(s)
            for k in g + e:
                t = self.fire(s, k)
                edges.append((key(s), k, key(t)))
                n2 = self.nxt(t)
                g2 = [x for x in INTERNAL if n2[x] != t[x]]
                for other in g:
                    if other != k and other not in g2:
                        res["hazards"].append((s, k, other))
                if k == "A":
                    if t["A"] == 1 and s["Rin"] != 1:
                        res["protocol"].append(("A+ without Rin", s))
                    if t["A"] == 0 and s["Rin"] != 0:
                        res["protocol"].append(("A- without Rin-", s))
                    if t["A"] == 1 and not (s["B"] == 1 and s["Ld"] == 1):
                        res["opacity"].append(("A+ without a fresh capture", s))
                    if t["A"] == 0 and s["R"] == 1 and s["Aout"] == 0:
                        res["decoupled"] = True
                if k == "R":
                    if t["R"] == 1 and s["Aout"] != 0:
                        res["protocol"].append(("R+ while Aout", s))
                    if t["R"] == 0 and s["Aout"] != 1:
                        res["protocol"].append(("R- without Aout", s))
                    if t["R"] == 1 and s["B"] != 1:
                        res["opacity"].append(("R+ without a captured token", s))
                if k == "Lt" and t["Lt"] == 1:
                    if self.broad and not (s["Aout"] == 0 and s["R"] == 0):
                        res["opacity"].append(("reopen before sink RTZ", s))
                    if not self.broad and not s["Taken"]:
                        res["opacity"].append(("reopen before sink ack", s))
                if key(t) not in seen:
                    seen[key(t)] = t
                    stack.append(t)
        succ = {}
        for a, _, b in edges:
            succ.setdefault(a, set()).add(b)
        home = key(INIT)
        res["unreturned"] = [k for k in seen if home not in reach(succ, k)]
        res["states"] = len(seen)
        res["edges"] = edges
        return res


def reach(succ, a):
    seen = {a}
    st = [a]
    while st:
        x = st.pop()
        for y in succ.get(x, ()):
            if y not in seen:
                seen.add(y)
                st.append(y)
    return seen


def witness(edges, target):
    pred = {key(INIT): None}
    dq = deque([key(INIT)])
    while dq:
        a = dq.popleft()
        for x, k, b in edges:
            if x == a and b not in pred:
                pred[b] = (a, k)
                dq.append(b)
    path = []
    cur = key(target)
    while pred.get(cur):
        a, k = pred[cur]
        path.append(k + ("+" if dict(zip(ORDER, cur))[k] else "-"))
        cur = a
    return " ".join(reversed(path))


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--broad", type=int, default=1, choices=(0, 1))
    ap.add_argument("--ldn", type=int, default=0, choices=(0, 1))
    ap.add_argument("--rt", default="none", choices=("none", "env"))
    ap.add_argument("-v", action="store_true", help="show one witness per hazard")
    args = ap.parse_args(argv)
    m = Model(broad=bool(args.broad), ldn=args.ldn, rt=args.rt)
    r = m.explore()
    print(f"{r['states']} states, {len(r['edges'])} edges")
    for k in ("hazards", "protocol", "opacity", "deadlocks", "unreturned"):
        print(f"{k}: {len(r[k])}")
    print("input handshake completes while output pending:", r["decoupled"])
    for what, s in r["protocol"][:5] + r["opacity"][:5]:
        print("  ", what, s)
    if args.v:
        shown = set()
        for s, k, other in r["hazards"]:
            if (k, other) in shown:
                continue
            shown.add((k, other))
            print(f"hazard {k} disables {other}: {witness(r['edges'], s)}")
    ok = not (r["protocol"] or r["opacity"] or r["deadlocks"] or r["unreturned"])
    ok = ok and (args.rt == "none" or not r["hazards"])
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
