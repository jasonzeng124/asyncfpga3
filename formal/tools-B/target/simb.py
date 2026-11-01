#!/usr/bin/env python3
"""simb.py: shard B copy of shard A's tools-A/target/sim.py (2026-11-01, commit 3d3ebb61-era),
with ONE addition: --posmap FILE (JSON {gate index: position in [0,1]}) overrides --pos per gate,
for adversarial in-band delay assignments. Everything else is A's code, unchanged.

sim.py (shard A, THE goal): event-driven simulation of the DECODED TARGET netlist
(build_net.py's gate list, the Spec.lean gate relation with one fixed delay per pin arc).

    python3 sim.py NET.json BND.json --pairs 6,18 3,5 [--corner 0.5] [--pos 0.5] [--pipelined]
                   [--R 20000] [--dout 3000] [--tmax 2000000] [--seed S] [--scatter 0.0]

Delay of each pin arc: at corner c, window [lerp(fmin,smin,c), lerp(fmax,smax,c)], position p in
that window (p=0 fast end, 1 slow end), optional uniform scatter. Every such delay is inside
Spec.Adm for g = 1 and any κ ≥ the scatter used, so a run is one behaviour of Spec.Behaves (with
transport semantics: f i t = t - d_i), if the simulator is right. UNTRUSTED (no Lean check).

Environment (Spec.Env): reset high on [0, R); the shared input request (a, b, start are one node
in the target) rises when all three acks are low and data are set (data set `su` ps before), falls
when all three acks are high. Sequential: the next pair is offered only after the out0 handshake of
the previous one. Pipelined (--pipelined): as soon as the input handshake completes (all acks low).
out0 / end acks rise `dout` ps after their request (Spec's Δo) and fall `dout` after it falls.
Prints every out0 value, its pair index, and checks gcd in order.
"""
import argparse
import heapq
import json
import math
import random
import sys
from bisect import bisect_right
from collections import defaultdict


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("net")
    ap.add_argument("bnd")
    ap.add_argument("--pairs", nargs="+", required=True)
    ap.add_argument("--corner", type=float, default=0.5)
    ap.add_argument("--pos", type=float, default=0.5)
    ap.add_argument("--scatter", type=float, default=0.0)
    ap.add_argument("--posmap", default=None)
    ap.add_argument("--filter", default=None, help="JSON {\"gate:pin\": W}: that pin skips input pulses narrower than W ps (B; needs W <= the pin's delay)")
    ap.add_argument("--gfilter", default=None, help="W,T1: from T1 on every pin whose window allows it skips pulses narrower than W (B)")
    ap.add_argument("--watch", default=None, help="gate name; stop once it has flipped --maxflips times (B)")
    ap.add_argument("--maxflips", type=int, default=6)
    ap.add_argument("--maxevents", type=int, default=0, help="stop and print CHAOS after this many events (B)")
    ap.add_argument("--g", type=float, default=1.0, help="guard: global band [FAST_MIN/g, SLOW_MAX*g] (B)")
    ap.add_argument("--kappa", type=float, default=0.0, help="posmap value -1/2 = fast/slow end of the κ-widened window")
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--pipelined", action="store_true")
    ap.add_argument("--R", type=int, default=20000)
    ap.add_argument("--su", type=int, default=0)
    ap.add_argument("--dout", type=int, default=3000)
    ap.add_argument("--tmax", type=int, default=5_000_000)
    ap.add_argument("--trace", default=None)
    ap.add_argument("--dump", default=None, help="write every node's (v0, flip times) as JSON")
    ap.add_argument("--full", action="store_true", help="simulate every circuit gate, not only the kernel cone")
    ap.add_argument("--datachange", choices=["handshake", "broad", "rtz", "next"], default="handshake",
                    help="when the env moves the data to the next pair: right after the input "
                         "handshake (Spec.Env allows it) or only just before the next request")
    a = ap.parse_args()
    rnd = random.Random(a.seed)
    N = json.load(open(a.net))
    B = json.load(open(a.bnd))["boundary"]
    names = N["nodes"]
    idx = {n: i for i, n in enumerate(names)}
    gates = N["gates"]
    nb = lambda k: idx[B[k]]
    ENV = set(idx[x] for x in json.load(open(a.bnd))["env"])
    # drop the drivers of env nodes (Spec.circuit)
    drv = {}
    for gi, g in enumerate(gates):
        if g["out"] not in ENV:
            drv[g["out"]] = gi
    # cone of the kernel's outputs, stopping at env nodes
    outs = [nb("a_ack"), nb("b_ack"), nb("start_ack"), nb("out0_req")] + [idx[x] for x in B["out0_data"]]
    cone, todo = set(), list(outs)
    seen = set(todo)
    while todo:
        n = todo.pop()
        gi = drv.get(n)
        if gi is None:
            continue
        cone.add(gi)
        for i in gates[gi]["ins"]:
            if i not in seen and i not in ENV:
                seen.add(i)
                todo.append(i)
    if a.full:
        cone = set(drv.values())
    print("sim: cone %d gates of %d (%d nodes)" % (len(cone), len(gates), len(seen)), file=sys.stderr)
    c, p = a.corner, a.pos

    PMraw = json.load(open(a.posmap)) if a.posmap else {}
    PM = {int(k): v for k, v in PMraw.items() if ":" not in k}
    PMpin = {tuple(int(x) for x in k.split(":")): v for k, v in PMraw.items() if ":" in k}   # "gate:pin" (B)

    def dly(e, gi=None, pin=None):
        lo = (1 - c) * e["fmin"] + c * e["smin"]
        hi = (1 - c) * e["fmax"] + c * e["smax"]
        pp = PMpin.get((gi, pin), PM.get(gi, p))
        if pp == -1:
            d = max((1 - a.kappa) * lo, e["fmin"] / a.g)  # Adm: (1-κ)·lerp_lo and ≥ FAST_MIN/g
            return int(-(-d // 1))                       # ceil: stay inside the window
        if pp == 2:
            d = min((1 + a.kappa) * hi, e["smax"] * a.g)  # Adm: (1+κ)·lerp_hi and ≤ SLOW_MAX·g
            return int(d // 1)
        d = lo + pp * (hi - lo)
        if a.scatter:
            d *= 1 + rnd.uniform(-a.scatter, a.scatter)
            d = min(max(d, lo * (1 - a.scatter)), hi * (1 + a.scatter))
        return int(round(d))

    WATCH = next((i for i, gg in enumerate(gates) if gg['name'] == a.watch), None) if a.watch else None
    G = {}
    readers = defaultdict(list)   # node -> [(gi, pin, d)]
    for gi in cone:
        g = gates[gi]
        ds = [dly(e, gi, pin) for pin, e in enumerate(g["arcs"])]
        G[gi] = (g["k"], g["init"], g["ins"], ds, g["out"])
        for pin, (n, d) in enumerate(zip(g["ins"], ds)):
            readers[n].append((gi, pin, d))
    # node histories: times (sorted) and values
    ht = defaultdict(lambda: [0])
    hv = defaultdict(lambda: [False])

    def val(n, t):
        ts = ht[n]
        return hv[n][bisect_right(ts, t) - 1] if t >= 0 else hv[n][0]

    def setv(n, t, v):
        ts, vs = ht[n], hv[n]
        if ts[-1] == t:
            if len(ts) > 1 and vs[-2] == v:
                ts.pop(); vs.pop()
                return True
            if vs[-1] != v:
                vs[-1] = v
                return True
            return False
        if t < ts[-1]:
            raise RuntimeError("time went back on node %s" % names[n])
        if vs[-1] == v:
            return False
        ts.append(t); vs.append(v)
        return True

    Q = []
    seq = [0]

    def sched(t, gi):
        seq[0] += 1
        heapq.heappush(Q, (t, 0, seq[0], gi))

    def changed(n, t):
        for gi, pin, d in readers.get(n, ()):
            sched(t + d, gi)

    FILT = {tuple(int(x) for x in kk.split(":")): (w if isinstance(w, list) else [w, 0])
            for kk, w in json.load(open(a.filter)).items()} if a.filter else {}

    def fval(n, r, t, wt):
        """value of n read at r, skipping a pulse narrower than w (starting at or after t1) that contains r and
        has ended by t"""
        w, t1 = wt
        ts = ht[n]; vs = hv[n]
        k = bisect_right(ts, r) - 1
        if k >= 1 and k + 1 < len(ts) and ts[k] >= t1 and ts[k + 1] - ts[k] < w and ts[k + 1] <= t:
            return vs[k - 1]
        return vs[k] if r >= 0 else vs[0]

    GW = [int(x) for x in a.gfilter.split(",")] if a.gfilter else None
    GOK = set()
    if GW:
        for gi_ in G:
            for i_, e_ in enumerate(gates[gi_]["arcs"]):
                lo_ = (1 - c) * e_["fmin"] + c * e_["smin"]
                if lo_ >= GW[0] and G[gi_][3][i_] >= GW[0]:      # pin's window start and its delay >= W
                    GOK.add((gi_, i_))

    def ev(gi, t):
        k, init, ins, ds, o = G[gi]
        ad = 0
        for i in range(k):
            w = FILT.get((gi, i))
            if w is None and GW and (gi, i) in GOK:
                w = [GW[0], GW[1]]
            if (fval(ins[i], t - ds[i], t, w) if w else val(ins[i], t - ds[i])):
                ad |= 1 << i
        v = bool(init >> ad & 1)
        if setv(o, t, v):
            changed(o, t)

    # env events are (t, 1, seq, ("set", node, value)) and are applied before gate evals at t
    def env_set(t, n, v):
        seq[0] += 1
        heapq.heappush(Q, (t, -1, seq[0], (n, v)))

    pairs = [tuple(int(x, 0) for x in s.split(",")) for s in a.pairs]
    # data encodings per node (merged bits must agree; constant bits must match)
    def drive_data(t, vals, key):
        want = {}
        for i, nm in enumerate(B[key]):
            bit = bool(vals >> i & 1)
            if nm.startswith("const"):
                if bit != (nm == "const1"):
                    sys.exit("pair value %#x not representable on %s: bit %d tied to %s" % (vals, key, i, nm))
                continue
            n = idx[nm]
            if want.get(n, bit) != bit:
                sys.exit("pair value %#x not representable on %s: bit %d shares a node" % (vals, key, i))
            want[n] = bit
        for n, b in want.items():
            env_set(t, n, b)

    rst, req = nb("rst"), nb("req")
    aA, aB, aS = nb("a_ack"), nb("b_ack"), nb("start_ack")
    oR, oA, eA = nb("out0_req"), nb("out0_ack"), nb("pend_ack")
    env_set(0, rst, True)
    env_set(a.R, rst, False)
    for gi in G:            # power-up: evaluate everything once
        sched(0, gi)
    st = {"k": 0, "phase": "idle", "outs": [], "out_pending": False, "next_ok": True, "done_in": 0}
    if pairs:
        drive_data(a.R - a.su - 1 if a.su else a.R, pairs[0][0], "a_data")
        drive_data(a.R - a.su - 1 if a.su else a.R, pairs[0][1], "b_data")
    t = 0
    last = {}
    nev = 0
    outvals = []

    def acks(t):
        return val(aA, t), val(aB, t), val(aS, t)

    req_state = False
    pend_state = False
    t_req_rise = None
    while Q:
        t, pri, _, x = heapq.heappop(Q)
        if t > a.tmax:
            break
        nev += 1
        if a.maxevents and nev > a.maxevents:
            print('CHAOS: %d events by %d ps' % (nev, t), file=sys.stderr)
            break
        if WATCH is not None and len(ht[WATCH]) > a.maxflips + 1:
            print('WATCH: %s flipped %d times by %d ps' % (a.watch, len(ht[WATCH]) - 1, t), file=sys.stderr)
            break
        if pri == -1:
            n, v = x
            if setv(n, t, v):
                changed(n, t)
        elif pri == -2:
            pass
        else:
            ev(x, t)
        if Q and Q[0][0] == t:
            continue
        if t < a.R:
            continue
        # ---- the environment reacts to the settled state at t
        A = acks(t)
        if a.datachange == "broad" and 0 < st["k"] < len(pairs):
            for key, ackn, j in (("a_data", aA, 0), ("b_data", aB, 1)):
                if not val(ackn, t) and st.get("broad_" + key) != st["k"]:
                    st["broad_" + key] = st["k"]
                    print("env: %s -> pair %d at %d ps (its ack fell)" % (key, st["k"], t + 1))
                    drive_data(t + 1, pairs[st["k"]][j], key)
        if (a.datachange == "rtz" and not req_state and not any(A) and 0 < st["k"] < len(pairs)
                and st.get("rtz_done") != st["k"]):
            st["rtz_done"] = st["k"]
            print("env: data -> pair %d at %d ps (all acks low, before out0)" % (st["k"], t + 1))
            drive_data(t + 1, pairs[st["k"]][0], "a_data")
            drive_data(t + 1, pairs[st["k"]][1], "b_data")
        if not req_state and not any(A) and st["k"] < len(pairs) and st["next_ok"]:
            # data were set at the previous fall (or initially); raise the request
            if a.datachange == "next" and st["k"] > 0:
                drive_data(t + 1, pairs[st["k"]][0], "a_data")
                drive_data(t + 1, pairs[st["k"]][1], "b_data")
                env_set(t + 1 + max(a.su, 1), req, True)
            else:
                env_set(t + max(a.su, 1), req, True)
            req_state = True
        elif req_state and all(A) and val(req, t):
            env_set(t + 1, req, False)
            req_state = False
            st["k"] += 1
            st["done_in"] += 1
            if st["k"] < len(pairs) and a.datachange == "handshake":
                drive_data(t + 2, pairs[st["k"]][0], "a_data")
                drive_data(t + 2, pairs[st["k"]][1], "b_data")
            if not a.pipelined:
                st["next_ok"] = False
        r0 = val(oR, t)
        if r0 and not val(oA, t) and not st["out_pending"]:
            st["out_pending"] = True
            env_set(t + a.dout, oA, True)
            heapq.heappush(Q, (t + a.dout, -2, 0, None))
            st["sample_at"] = t + a.dout - 1
        if st.get("sample_at") is not None and t >= st["sample_at"]:
            v = sum((1 << i) for i, nm in enumerate(B["out0_data"]) if val(idx[nm], st["sample_at"]))
            outvals.append((st["sample_at"], v))
            print("out0 #%d at %d ps: %d" % (len(outvals) - 1, st["sample_at"], v))
            st["sample_at"] = None
            if not a.pipelined:
                st["next_ok"] = True
        if not r0 and val(oA, t) and st["out_pending"]:
            st["out_pending"] = False
            env_set(t + a.dout, oA, False)
        pr = val(nb("req"), t)
        # the end channel's request IS the shared input request in the target; its ack is a
        # delayed copy (as the rig's bd_snk): rise dout after the request, fall dout after
        if pr != pend_state:
            pend_state = pr
            env_set(t + a.dout, eA, pr)
    if a.trace and a.trace != "1":
        W = json.load(open(a.trace))   # {"req": node, "bus": [nodes]}
        rn = idx[W["req"]]
        rises = [tt for tt, vv in zip(ht[rn], hv[rn]) if vv]
        for tt in rises[:12]:
            v = sum((1 << i) for i, nm in enumerate(W["bus"]) if val(idx[nm], tt))
            print("watch %d ps: %#x (%d)" % (tt, v, v if v < 2**31 else v - 2**32), file=sys.stderr)
    if a.trace:
        late = sorted(((sum(1 for x in ht[n] if x > 1000000), names[n]) for n in list(ht)), reverse=True)[:8]
        print("late toggles", late, file=sys.stderr)
        for k in ["rst", "req", "a_ack", "b_ack", "start_ack", "out0_req", "out0_ack", "pend_ack"]:
            n = nb(k)
            print("trace %-9s %s" % (k, list(zip(ht[n], hv[n]))[:12]), file=sys.stderr)
    print("sim: %d events, t = %d ps, %d pairs offered, %d accepted, %d outputs" %
          (nev, t, len(pairs), st["done_in"], len(outvals)), file=sys.stderr)
    if a.dump:
        json.dump({"tend": t, "nodes": {str(n): [hv[n][0], ht[n][1:]] for n in ht if len(ht[n]) > 1 or hv[n][0]},
                   "outs": outvals, "pairs": pairs, "args": vars(a)}, open(a.dump, "w"))
    want = [math.gcd(x, y) for x, y in pairs]
    got = [v for _, v in outvals]
    ok = got == want
    print("RESULT %s: want %s got %s" % ("OK" if ok else "MISMATCH", want, got))
    sys.exit(0 if ok else 2)


if __name__ == "__main__":
    main()
