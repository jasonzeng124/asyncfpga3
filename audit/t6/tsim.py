#!/usr/bin/env python3
"""T6 (auditor, own code): transport event simulator for the decoded target netlist.

Independent of shard A/B simulators: own netlist (/root/t4work2/net.json, the auditor's decoder
output), own boundary (/root/t4work2/bnd.json), own delay computation (exact rationals, Spec.Adm),
own event engine and own sequential environment.

Semantics (Spec.GateOK with f i t = t - d_i, one fixed integer delay per pin arc = transport):
  x out (t) = INIT[ addr( x in_i (t - d_i) ) ].
Engine: a pin event (T, gate, pin, v) means "pin's delayed copy becomes v at T".  All events at one
ps are applied, then zero-delay arcs are iterated to a fixpoint (delta cycles) and only the FINAL
value of a node at T is published (to readers with d > 0) -- a node holds one value per ps.

usage: tsim.py --kappa K [--corner C] [--posmap B_POSMAP --leannet B_net.json] [--tmax PS]
               [--pairs 0xC,0x12] [--out PREFIX]
posmap: shard B's file (keys = gate indices of the LEAN net, or "gate:pin"); values -1 = fast end
of the Adm window, 2 = slow end, other p = lerp position p in the corner window.  Mapped to the
auditor's net by gate name (leading "~" stripped).
"""
import argparse, heapq, json, math, sys
from fractions import Fraction as Fr
from collections import defaultdict


def adm_window(e, c, k, g=Fr(1)):
    """Spec.Adm as an integer interval [lo, hi] (None if empty)."""
    llo = (1 - c) * e["fmin"] + c * e["smin"]
    lhi = (1 - c) * e["fmax"] + c * e["smax"]
    lo = max(Fr(e["fmin"]) / g, (1 - k) * llo)
    hi = min(Fr(e["smax"]) * g, (1 + k) * lhi)
    lo_i, hi_i = math.ceil(lo), math.floor(hi)
    return (lo_i, hi_i) if lo_i <= hi_i else None


def delay(e, c, k, pos):
    w = adm_window(e, c, k)
    if pos == -1:
        return w[0]
    if pos == 2:
        return w[1]
    llo = (1 - c) * e["fmin"] + c * e["smin"]
    lhi = (1 - c) * e["fmax"] + c * e["smax"]
    # same rounding as the shards' mid assignment: Python round() of the float value
    return int(round(float(llo + Fr(pos) * (lhi - llo))))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--net", default="/root/t4work2/net.json")
    ap.add_argument("--bnd", default="/root/t4work2/bnd.json")
    ap.add_argument("--kappa", default="0")
    ap.add_argument("--corner", default="0.5")
    ap.add_argument("--posmap")
    ap.add_argument("--leannet", default="/dev/shm/t6/run/net.json")
    ap.add_argument("--pairs", default="0xC,0x12")
    ap.add_argument("--R", type=int, default=20000)
    ap.add_argument("--dout", type=int, default=3000)
    ap.add_argument("--tmax", type=int, default=2_000_000)
    ap.add_argument("--out", default=None)
    ap.add_argument("--watchcap", type=int, default=400000)
    ap.add_argument("--stop_after_out", type=int, default=20000,
                    help="stop this many ps after the last env step once all outputs are in")
    a = ap.parse_args()
    c, k = Fr(a.corner), Fr(a.kappa)

    N = json.load(open(a.net))
    names = N["nodes"]
    idx = {n: i for i, n in enumerate(names)}
    gates = N["gates"]
    gname = {g["name"].lstrip("~"): gi for gi, g in enumerate(gates)}
    BJ = json.load(open(a.bnd))
    B = BJ["boundary"]
    ENV = set(idx[x] for x in BJ["env"])

    # position map (B's gate indices -> names -> my indices)
    PM, PMpin, used = {}, {}, []
    if a.posmap:
        L = json.load(open(a.leannet))
        for key, v in json.load(open(a.posmap)).items():
            gi_l, _, pin = key.partition(":")
            nm = L["gates"][int(gi_l)]["name"].lstrip("~")
            gi = gname[nm]
            # sanity: same k and arcs in both nets
            assert gates[gi]["arcs"] == L["gates"][int(gi_l)]["arcs"], nm
            if pin:
                PMpin[(gi, int(pin))] = v
            else:
                PM[gi] = v
            used.append((key, nm, v))

    drv = {g["out"]: gi for gi, g in enumerate(gates) if g["out"] not in ENV}
    outs = [idx[B[x]] for x in ("a_ack", "b_ack", "start_ack", "out0_req")] + [idx[x] for x in B["out0_data"]]
    cone, todo, seen = set(), list(outs), set(outs)
    while todo:
        n = todo.pop()
        gi = drv.get(n)
        if gi is None:
            continue
        cone.add(gi)
        for i in gates[gi]["ins"]:
            if i not in seen and i not in ENV:
                seen.add(i); todo.append(i)
    print("cone: %d gates" % len(cone), file=sys.stderr)

    init, out, adr = {}, {}, {}
    rd_pos = defaultdict(list)   # node -> [(gi, pin, d)] d > 0
    rd_zero = defaultdict(list)  # node -> [(gi, pin)]   d == 0
    D = {}
    for gi in cone:
        g = gates[gi]
        init[gi], out[gi], adr[gi] = g["init"], g["out"], 0
        for pin, (n, e) in enumerate(zip(g["ins"], g["arcs"])):
            d = delay(e, c, k, PMpin.get((gi, pin), PM.get(gi, 0.5)))
            w = adm_window(e, c, k)
            assert w and w[0] <= d <= w[1], (g["name"], pin, d, w)
            D[(gi, pin)] = d
            (rd_pos[n].append((gi, pin, d)) if d > 0 else rd_zero[n].append((gi, pin)))

    val = defaultdict(int)
    UA1 = out[gname["SLICE_X2Y18.DLUT.O6"]]
    GN = out[gname["SLICE_X0Y18.ALUT.O6"]]
    bn = {x: idx[B[x]] for x in ("rst", "req", "a_ack", "b_ack", "start_ack", "out0_req", "out0_ack", "pend_ack")}
    watch = {UA1: "ua1", GN: "g(SLICE_X0Y18.ALUT.O6)"}
    for x, n in bn.items():
        watch[n] = x
    ua1g = gates[gname["SLICE_X2Y18.DLUT.O6"]]
    for p, n in enumerate(ua1g["ins"]):
        watch.setdefault(n, "ua1.pin%d" % p)
    # arbiters (shard B's Lean arbs.json names -> my nodes)
    arbs = json.load(open("/dev/shm/t6/run/arbs.json"))
    for j, ar in enumerate(arbs):
        watch.setdefault(idx[ar["q"]], "arb%d.q" % j)
        for i, nm in enumerate(ar["ins"]):
            watch.setdefault(idx[nm], "arb%d.in%d" % (j, i))
    hist = {n: [] for n in watch}
    togg = defaultdict(int)       # 10 ns bucket -> node changes
    lastchg = defaultdict(int)

    Q = []
    def env_set(t, n, v):
        heapq.heappush(Q, (t, -1, n, int(v)))

    pairs = [tuple(int(x, 0) for x in s.split(",")) for s in a.pairs.split()]
    def drive(t, v, key):
        want = {}
        for i, nm in enumerate(B[key]):
            bit = v >> i & 1
            if nm in ("const0", "const1"):
                assert bit == (nm == "const1"), ("not representable", key, i)
                continue
            assert want.get(idx[nm], bit) == bit, ("merged bit conflict", key, i)
            want[idx[nm]] = bit
        for n, b in want.items():
            env_set(t, n, b)

    env_set(0, bn["rst"], 1)
    env_set(a.R, bn["rst"], 0)
    drive(a.R, pairs[0][0], "a_data")
    drive(a.R, pairs[0][1], "b_data")
    st = dict(k=0, req=False, next_ok=True, pend=False, sample=None, pendack=False, done_t=None)
    outvals = []
    first = True
    nev = 0
    T = 0
    import signal
    stop = [False]
    signal.signal(signal.SIGINT, lambda *x: stop.__setitem__(0, True))
    while Q or first:
        if stop[0]:
            print("interrupted (SIGINT) at T=%d: dumping what was simulated" % T, file=sys.stderr)
            break
        T = Q[0][0] if Q else 0
        if T > a.tmax:
            break
        touched = set(cone) if first else set()
        first = False
        old = {}
        while Q and Q[0][0] == T:
            _, gi, p, v = heapq.heappop(Q)
            nev += 1
            if gi < 0:
                if val[p] != v:
                    old.setdefault(p, val[p]); val[p] = v
                    for rg, rp in rd_zero[p]:
                        adr[rg] = adr[rg] | (1 << rp) if v else adr[rg] & ~(1 << rp); touched.add(rg)
            else:
                adr[gi] = adr[gi] | (1 << p) if v else adr[gi] & ~(1 << p)
                touched.add(gi)
        it = 0
        while touched:
            it += 1
            if it > 10000:
                sys.exit("zero-delay loop at %d" % T)
            nxt = set()
            for gi in touched:
                o = out[gi]
                v = init[gi] >> adr[gi] & 1
                if v != val[o]:
                    old.setdefault(o, val[o]); val[o] = v
                    for rg, rp in rd_zero[o]:
                        adr[rg] = adr[rg] | (1 << rp) if v else adr[rg] & ~(1 << rp); nxt.add(rg)
            touched = nxt
        for o, ov in old.items():
            v = val[o]
            if v == ov:
                continue
            togg[T // 10000] += 1
            lastchg[o] = T
            if o in hist and len(hist[o]) < a.watchcap:
                hist[o].append((T, v))
            for rg, rp, d in rd_pos[o]:
                heapq.heappush(Q, (T + d, rg, rp, v))
        if T // 10000 != st.get("lastprog"):
            st["lastprog"] = T // 10000
            if T >= 590000:
                print("prog T=%d events=%d ua1_flips=%d changes_last_bucket=%d" % (T, nev, len(hist[UA1]), togg[T // 10000 - 1]), file=sys.stderr, flush=True)
        if T < a.R:
            continue
        # ---- own sequential environment (Spec.Env + SeqEnv, n = len(pairs))
        acks = (val[bn["a_ack"]], val[bn["b_ack"]], val[bn["start_ack"]])
        if not st["req"] and not any(acks) and st["k"] < len(pairs) and st["next_ok"]:
            env_set(T + 1, bn["req"], 1); st["req"] = True
        elif st["req"] and all(acks) and val[bn["req"]]:
            env_set(T + 1, bn["req"], 0); st["req"] = False
            st["k"] += 1; st["next_ok"] = False
            if st["k"] < len(pairs):
                drive(T + 2, pairs[st["k"]][0], "a_data"); drive(T + 2, pairs[st["k"]][1], "b_data")
        r0, a0 = val[bn["out0_req"]], val[bn["out0_ack"]]
        if r0 and not a0 and not st["pend"]:
            st["pend"] = True; env_set(T + a.dout, bn["out0_ack"], 1); st["sample"] = T + a.dout - 1
            heapq.heappush(Q, (T + a.dout - 1, -2, 0, 0))
        if st["sample"] is not None and T >= st["sample"]:
            v = sum(1 << i for i, nm in enumerate(B["out0_data"]) if val[idx[nm]])
            outvals.append((T, v)); print("out0 #%d sampled at %d ps: %d" % (len(outvals) - 1, T, v)); st["sample"] = None
        if not r0 and a0 and st["pend"]:
            st["pend"] = False; env_set(T + a.dout, bn["out0_ack"], 0); st["next_ok"] = True
            if len(outvals) == len(pairs):
                st["done_t"] = T + a.dout
        rq = val[bn["req"]]
        if rq != st["pendack"]:
            st["pendack"] = rq; env_set(T + a.dout, bn["pend_ack"], rq)
        if st["done_t"] is not None and T > st["done_t"] + a.stop_after_out:
            break
    print("end: T=%d events=%d outputs=%s" % (T, nev, outvals))
    print("delays on ua1 pins:", [D.get((gname["SLICE_X2Y18.DLUT.O6"], p)) for p in range(6)])
    h = hist[UA1]
    print("ua1 flips: %d, first: %s" % (len(h), h[:10]))
    print("g flips: %d, first: %s" % (len(hist[GN]), hist[GN][:10]))
    bk = sorted(togg)
    print("node changes per 10ns bucket (last 8):", [(b * 10, togg[b]) for b in bk[-8:]])
    if a.out:
        json.dump({"args": vars(a), "used_posmap": used, "outs": outvals, "T": T,
                   "hist": {str(n): [watch[n], hist[n]] for n in hist},
                   "togg": {str(b): togg[b] for b in bk},
                   "delays": {"%d:%d" % kk: d for kk, d in D.items() if kk[0] in PM or kk in PMpin
                              or kk[0] == gname["SLICE_X2Y18.DLUT.O6"]}},
                  open(a.out + ".json", "w"))
    want = [math.gcd(x, y) for x, y in pairs]
    ok = [v for _, v in outvals] == want
    print("RESULT %s want %s got %s" % ("OK" if ok else "MISMATCH", want, [v for _, v in outvals]))
    sys.exit(0 if ok else 2)


if __name__ == "__main__":
    main()
