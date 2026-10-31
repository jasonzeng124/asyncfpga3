"""SI exploration of a bdc loop ring: mux -> N links -> steer -> mux, real LUT INITs.
Env: one-shot entry source on mux.x (H_START_ONCE), mux select sm flips 0->1 once after
the entry token has been accepted and the mux is idle, steer select ss = 1 (loop forever),
mux ctl channel from a free bd_src (ctl_req = ~ctl_ack = ~z_ack).
Prints reachable states, deadlocks, persistence violations, wavefront counts on the links."""
import sys, os
MODE = os.environ.get("MODE", "idle")
def lut(init, pins):
    return (init >> sum(int(p) << k for k, p in enumerate(pins))) & 1 == 1
C2N, C2, MJ0, MJ1 = 0x00B2, 0x00E8, 0xAE08, 0xEA80

def build(N, ss_const=True):
    names = [f"c{i}" for i in range(N)] + ["j0", "j1", "zq", "xa", "ya", "ctlq", "r1", "r0", "a0", "sa"]
    ix = {n: k for k, n in enumerate(names)}
    env = ["xq", "sm", "cnt", "ss"]
    for e in env: ix[e] = len(names) + env.index(e)
    G = {}
    for i in range(N):
        a = "zq" if i == 0 else f"c{i-1}"
        b = f"c{i+1}" if i < N - 1 else "sa"
        G[f"c{i}"] = (lambda s, a=a, b=b, q=f"c{i}": lut(C2N, [s[ix[a]], s[ix[b]], s[ix[q]], 0]))
    G["j0"] = lambda s: lut(MJ0, [s[ix["xq"]], s[ix["ctlq"]], s[ix["sm"]], s[ix["j0"]], 0])
    G["j1"] = lambda s: lut(MJ1, [s[ix["r1"]], s[ix["ctlq"]], s[ix["sm"]], s[ix["j1"]], 0])
    G["zq"] = lambda s: s[ix["j0"]] or s[ix["j1"]]           # LUT2 OR + delay chain, one gate
    G["xa"] = lambda s: lut(C2, [s[ix["j0"]], s[ix["c0"]], s[ix["xa"]], 0])
    G["ya"] = lambda s: lut(C2, [s[ix["j1"]], s[ix["c0"]], s[ix["ya"]], 0])
    G["ctlq"] = lambda s: not s[ix["c0"]]                     # bd_src LUT1 INIT 1, ack = z_ack
    G["r1"] = lambda s: s[ix[f"c{N-1}"]] and s[ix["ss"]]      # bd_steer O6
    G["r0"] = lambda s: s[ix[f"c{N-1}"]] and not s[ix["ss"]]  # bd_steer O5
    G["a0"] = lambda s: s[ix["r0"]]                           # bd_snk
    G["sa"] = lambda s: s[ix["a0"]] or s[ix["ya"]]            # steer ack OR
    gates = list(G)
    def envmoves(s):
        out = []
        xq, sm, cnt, ss = (s[ix[e]] for e in env)
        if not xq and not s[ix["xa"]] and cnt == 0 and not sm:
            out.append({"xq": 1, "cnt": 1})
        if xq and s[ix["xa"]]:
            out.append({"xq": 0})
        idle = not any(s[ix[k]] for k in ("j0", "j1", "zq", "xa", "ya"))
        if cnt == 1 and not xq and not sm and (idle if MODE == "idle" else not s[ix["ctlq"]]):
            out.append({"sm": 1})
        return out
    return names, env, ix, G, gates, envmoves

def explore(N):
    names, env, ix, G, gates, envmoves = build(N)
    s0 = tuple([0] * (len(names)) + [0, 0, 0, 1])
    def exc(s): return [g for g in gates if G[g](s) != bool(s[ix[g]])]
    def fire(s, g):
        l = list(s); l[ix[g]] = 1 - l[ix[g]]; return tuple(l)
    def D(s):
        c = [s[ix[f"c{i}"]] for i in range(N)]
        return sum(1 for i in range(N) if c[i - 1] != c[i]) if N > 1 else 0
    seen = {s0}; st = [s0]; dead = []; pv = []; Ds = {}
    while st:
        s = st.pop()
        E = exc(s)
        nxt = []
        for g in E:
            t = fire(s, g); nxt.append(t)
            for h in E:
                if h != g and h not in exc(t): pv.append((s, g, h))
        for m in envmoves(s):
            l = list(s)
            for k, v in m.items(): l[ix[k]] = v
            nxt.append(tuple(l))
        if not nxt: dead.append(s)
        key = (s[ix["cnt"]], s[ix["sm"]])
        Ds.setdefault(key, set()).add(D(s))
        for t in nxt:
            if t not in seen: seen.add(t); st.append(t)
    allnames = names + env
    print(f"N={N}: {len(seen)} states, {len(dead)} deadlocks, {len(pv)} persistence violations")
    print("   D on the link ring by (entered, sm):", {k: sorted(v) for k, v in sorted(Ds.items())})
    for d in dead[:3]:
        print("   dead:", {allnames[k]: d[k] for k in range(len(d)) if d[k]})
    for p in pv[:2]:
        print("   pv: fire", p[1], "disables", p[2], "in", {allnames[k]: p[0][k] for k in range(len(p[0])) if p[0][k]})

for N in range(1, int(sys.argv[1]) + 1 if len(sys.argv) > 1 else 6):
    explore(N)
