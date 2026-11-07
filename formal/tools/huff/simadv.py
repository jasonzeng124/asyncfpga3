#!/usr/bin/env python3
"""simadv.py (shard C copy of shard A's tools-A/target/sim.py, plus --slow/--kappa: an adversary that
puts the pin arcs of the named gates at (1+kappa) x the slow end of their window and every other arc at
(1-kappa) x the fast end; every such delay is inside Spec.Adm at g = 1 with scatter kappa. Original doc:)
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
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--pipelined", action="store_true")
    ap.add_argument("--R", type=int, default=20000)
    ap.add_argument("--slow", nargs="*", default=[], help="node names whose driving gate is made slow")
    ap.add_argument("--kappa", type=float, default=None)
    ap.add_argument("--fast", nargs="*", default=None, help="only these gates (and their input routes) fast; all others mid-window")
    ap.add_argument("--data0", action="store_true", help="the first pair's operands from time 0")
    ap.add_argument("--exact", action="store_true", help="kappa 0.84 at corner 0 with exact integer delays")
    ap.add_argument("--slowroutes", action="store_true", help="also slow the copy chains (pips, hops) into the slow gates' pins")
    ap.add_argument("--w", type=int, default=0, help="H_RUNT(w) on LUT pins (shard A's simrunt.py logic, ported)")
    ap.add_argument("--classes", default=None, help="JSON {S: [nodes], F: [nodes]}: per-gate delay class (exact, corner 0); others --cdefault")
    ap.add_argument("--gfrac", default=None, help="guard g = N/D for --classes at kappa 0: S = floor(N fmax / D), F = ceil(D fmin / N)")
    ap.add_argument("--cdefault", choices=["S", "F", "M"], default="M")
    ap.add_argument("--why", default=None, help="write JSON: for every flip after R of the --whynodes, its transport cause chain")
    ap.add_argument("--whynodes", nargs="*", default=[])
    ap.add_argument("--watch", nargs="*", default=[], help="node names: print their flip times")
    ap.add_argument("--su", type=int, default=0)
    ap.add_argument("--dout", type=int, default=3000)
    ap.add_argument("--tmax", type=int, default=5_000_000)
    ap.add_argument("--trace", default=None)
    ap.add_argument("--dump", default=None, help="write every node's (v0, flip times) as JSON")
    ap.add_argument("--full", action="store_true", help="simulate every circuit gate, not only the kernel cone")
    ap.add_argument("--datachange", choices=["handshake", "broad", "rtz", "next"], default="handshake",
                    help="when the env moves the data to the next pair: right after the input "
                         "handshake (Spec.Env allows it) or only just before the next request")
    ap.add_argument("--dfall", type=int, default=None,
                    help="out0/end acks FALL this many ps after their request falls (default: --dout); "
                         "Spec.Env puts no lower bound on a fall, so 1 is the adversarial env")
    ap.add_argument("--nextreq", choices=["sample", "seq"], default="sample",
                    help="sample: next pair may be offered once out0 is sampled (before its ack rises: more "
                         "than SeqEnv allows); seq: exactly SeqEnv, at the earliest: once out0's req and ack "
                         "are both low again")
    ap.add_argument("--reqgap", type=int, default=0,
                    help="extra ps the env waits, once it may raise the next request, before raising it")
    a = ap.parse_args()
    if a.dfall is None:
        a.dfall = a.dout
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

    SLOW = set(idx[x] for x in a.slow)
    FAST = None
    if a.fast:
        FAST = set(idx[x] for x in a.fast)
        for n0 in list(FAST):
            gi0 = drv.get(n0)
            if gi0 is None: continue
            for u in gates[gi0]["ins"]:
                while u in drv and gates[drv[u]]["k"] == 1 and gates[drv[u]]["init"] == 2:
                    FAST.add(u); u = gates[drv[u]]["ins"][0]
    if a.slowroutes:
        for n0 in list(SLOW):
            gi0 = drv.get(n0)
            if gi0 is None: continue
            for u in gates[gi0]["ins"]:
                while u in drv and gates[drv[u]]["k"] == 1 and gates[drv[u]]["init"] == 2:
                    SLOW.add(u); u = gates[drv[u]]["ins"][0]
    CLS = None
    if a.classes:
        CJ = json.load(open(a.classes)); CLS = {}
        ACL = {}
        for k in ("F", "S"):
            for x in CJ.get(k, []):
                if isinstance(x, list): ACL[(idx[x[0]], x[1])] = k
                else: CLS[idx[x]] = k
        PK = round(a.kappa * 25); assert a.corner in (0, 1) and abs(a.kappa - PK / 25) < 1e-12
        FMX, FMN = ("fmax", "fmin") if a.corner == 0 else ("smax", "smin")   # corner 1: the slow-corner window
    def dly(e, gi=None, pin=None):
        if CLS is not None:   # exact formulas (same as --exact): S = floor((25+P) fmax / 25), F = ceil((25-P) fmin / 25)
            k = CLS.get(gates[gi]["out"], a.cdefault) if gi is not None else a.cdefault
            if gi is not None: k = ACL.get((gates[gi]["out"], pin), k)
            if a.gfrac:
                gn, gd = map(int, a.gfrac.split("/")); assert PK == 0
                if k == "S": return (gn * e[FMX]) // gd
                if k == "F": return (gd * e[FMN] + gn - 1) // gn
            if k == "S": return ((25 + PK) * e[FMX]) // 25
            if k == "F": return ((25 - PK) * e[FMN] + 24) // 25
            return (e[FMN] + e[FMX]) // 2
        if a.kappa is not None:
            lo = (1 - c) * e["fmin"] + c * e["smin"]; hi = (1 - c) * e["fmax"] + c * e["smax"]
            if a.exact:   # kappa = P/25 exactly, corner 0: integer formulas used by the Lean witness (CexPS.dK)
                P = round(a.kappa * 25); assert c == 0 and abs(a.kappa - P / 25) < 1e-12
                if gi is not None and gates[gi]["out"] in SLOW: return ((25 + P) * e["fmax"]) // 25
                return ((25 - P) * e["fmin"] + 24) // 25
            if gi is not None and gates[gi]["out"] in SLOW: return int(math.floor(hi * (1 + a.kappa)))
            if FAST is not None and not (gi is not None and gates[gi]["out"] in FAST): return int(round(lo + 0.5 * (hi - lo)))
            return int(math.ceil(lo * (1 - a.kappa)))
        lo = (1 - c) * e["fmin"] + c * e["smin"]
        hi = (1 - c) * e["fmax"] + c * e["smax"]
        d = lo + p * (hi - lo)
        if a.scatter:
            d *= 1 + rnd.uniform(-a.scatter, a.scatter)
            d = min(max(d, lo * (1 - a.scatter)), hi * (1 + a.scatter))
        return int(round(d))

    G = {}
    readers = defaultdict(list)   # node -> [(gi, pin, d)]
    LUTG = set(); HI = {}
    gmul = (lambda f: int(f.split("/")[0]) / int(f.split("/")[1]))(a.gfrac) if a.gfrac else 1.0
    for gi in cone:
        g = gates[gi]
        ds = [dly(e, gi, pi) for pi, e in enumerate(g["arcs"])]
        if a.w and (g["name"].endswith("LUT.O6") or g["name"].endswith("LUT.O5")):
            LUTG.add(gi)
            his = [((1 - c) * e["fmax"] + c * e["smax"]) * (1 + (a.kappa or 0)) * gmul for e in g["arcs"]]
            HI[gi] = his
            for i_ in range(len(ds)):
                if ds[i_] < a.w:
                    assert a.w <= his[i_], (g["name"], i_, his[i_])
                    ds[i_] = a.w
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

    INF = defaultdict(int); NSKIP = [0]

    def fval(n, r):
        """value at the greatest u <= r in no pulse narrower than W; returns (value, u)"""
        ts = ht[n]; vs = hv[n]
        if r < 0:
            return vs[0], r
        k = bisect_right(ts, r) - 1
        u = r
        while k + 1 < len(ts) and ts[k + 1] - ts[k] < a.w and ts[k + 1] <= r + a.w:
            if k == 0:
                break  # the power-up interval [0, ts[1]): reads before reset settle; not filtered
            u = ts[k] - 1; k -= 1; NSKIP[0] += 1
        return vs[k], u

    def ev(gi, t):
        k, init, ins, ds, o = G[gi]
        ad = 0
        if gi in LUTG:
            for i in range(k):
                v_, u_ = fval(ins[i], t - ds[i])
                if t - u_ > HI[gi][i]:
                    INF[(gi, i)] += 1
                if v_:
                    ad |= 1 << i
        else:
          for i in range(k):
            if val(ins[i], t - ds[i]):
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
        t0d = 0 if a.data0 else (a.R - a.su - 1 if a.su else a.R)
        drive_data(t0d, pairs[0][0], "a_data")
        drive_data(t0d, pairs[0][1], "b_data")
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
                env_set(t + max(a.su, 1) + (a.reqgap if st["k"] > 0 else 0), req, True)
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
            if not a.pipelined and a.nextreq == "sample":
                st["next_ok"] = True
        if not r0 and val(oA, t) and st["out_pending"]:
            st["out_pending"] = False
            env_set(t + a.dfall, oA, False)
            if not a.pipelined and a.nextreq == "seq":
                st["seq_wait"] = True
        if st.get("seq_wait") and not r0 and not val(oA, t):
            st["seq_wait"] = False
            st["next_ok"] = True
            heapq.heappush(Q, (t + 1, -2, 0, None))
        pr = val(nb("req"), t)
        # the end channel's request IS the shared input request in the target; its ack is a
        # delayed copy (as the rig's bd_snk): rise dout after the request, fall dout after
        if pr != pend_state:
            pend_state = pr
            env_set(t + (a.dout if pr else a.dfall), eA, pr)
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
    for nmw in a.watch:
        n = idx[nmw]; ts = ht[n]; vs = hv[n]
        pw = [ts[i + 1] - ts[i] for i in range(1, len(ts) - 1)]
        print("watchnode %s flips %d min pulse %s : %s" % (nmw, len(ts) - 1, min(pw) if pw else None, list(zip(ts, vs))[:40]))
    print("sim: %d events, t = %d ps, %d pairs offered, %d accepted, %d outputs" %
          (nev, t, len(pairs), st["done_in"], len(outvals)), file=sys.stderr)
    if a.w:
        print("HRUNT w=%d: LUT gates %d, skipped reads %d, INFEASIBLE pins %d %s" % (a.w, len(LUTG), NSKIP[0], len(INF), sorted(((v, names[G[g][4]], i) for (g, i), v in INF.items()), reverse=True)[:5]), file=sys.stderr)
    if a.why:
        def cause(n, t):
            gi = drv.get(n)
            if gi is None or gi not in G: return None
            k, init, ins, ds, o = G[gi]
            best = None
            for i in range(k):
                ts = ht[ins[i]]; j = bisect_right(ts, t - ds[i]) - 1
                if j >= 1 and ts[j] == t - ds[i]:
                    if best is None or ds[i] > best[2]: best = (ins[i], t - ds[i], ds[i], i)
            return best
        WY = {}
        for nmw in a.whynodes:
            n = idx[nmw]; out = []
            for tt, vv in zip(ht[n][1:], hv[n][1:]):
                if tt < a.R: continue
                ch = [(n, tt, -1)]; m, u = n, tt
                while True:
                    c0 = cause(m, u)
                    if c0 is None or c0[1] < a.R: break
                    ch[-1] = (m, u, c0[3])
                    m, u = c0[0], c0[1]; ch.append((m, u, -1))
                out.append([tt, vv, ch])
            WY[nmw] = out
        json.dump(WY, open(a.why, "w"))
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
