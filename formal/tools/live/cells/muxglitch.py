#!/usr/bin/env python3
"""Can bd_mux's select-change hazard (x_ack = C(j0, z_ack) disabled while
falling) produce a WRONG handshake?

Topology: explore.py's free-mode fork-mux loop (bd_src on x, select an
environment bit held while ctl is mid-handshake).  Three models of the uxa
LUT (x_ack):
  si     : the cell as is (atomic LUT; a disabled transition simply does not
           happen -- the fall comes one handshake late);
  early  : the disabled fall may still complete (the node resolved to 0);
  runt   : while uxa's inputs disagree (j0 != z_ack) its output may change
           either way (a runt pulse: a fall that recovers).
Checks: four-phase protocol on every channel, and 'x_ack rises only while
j0 = 1' (an acknowledge without the mux having taken x = a lost token);
'j0 rises only while x_req = 1 and x_ack = 0' (taking a token twice)."""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import explore  # noqa: E402
from explore2 import Net2, explore_from, hazards, monitors, fmt_state, trace_to  # noqa: E402


def build(LP, LQ, LR, variant):
    explore.Net = lambda: Net2()
    try:
        net, meta = explore.build_forkjoin("mux", [LP, LQ], LR, mode="free")
    finally:
        explore.Net = Net2.__mro__[1]
    for c in (("M.x", "mx_r", "mx_a"), ("M.y", "ji1_r", "ji1_a"), ("M.ctl", "ji0_r", "ji0_a"),
              ("M.z", "jz_r", "jz_a")):
        net.channels.append(c)
    gi = [i for i, g in enumerate(net.gates) if g["name"] == "M.uxa"][0]
    g = net.gates[gi]
    if variant in ("early", "runt"):
        # inputs: j0, z_ack, q
        t = 0
        for v in range(8):
            j0, za, q = v & 1, (v >> 1) & 1, (v >> 2) & 1
            if j0 == za:
                o = j0
            elif variant == "early":
                o = 0 if (j0 == 0) else q      # a pending fall may complete
            else:
                o = 1 - q                      # runt: may toggle either way
            if o:
                t |= 1 << v
        g["tab"] = t
    return net, gi


def run(LP, LQ, LR, variant):
    net, ux = build(LP, LQ, LR, variant)
    comp = explore.make_completion(net)[0]
    S, E = net.S, len(net.env)
    guards = explore.stage_modes(net)[3]
    starts = []
    for x in range(1 << (S + E)):
        if all(((x >> l) & 1) == 0 for gl in guards for l in gl):
            c = comp(x)
            if c is not None:
                starts.append(c)
    adj = explore_from(net, starts)
    mon = monitors(net, adj)
    sig = lambda n: net.find(net.sig(n))  # noqa: E731
    j0, xr, xa = net.bit[sig("M.j0")], net.bit[sig("mx_r")], net.bit[sig("mx_a")]
    lost, dup = [], []
    for st, succ in adj.items():
        for ns in succ:
            gi = (st ^ ns).bit_length() - 1
            if gi == xa and (ns >> xa) & 1 and not (st >> j0) & 1:
                lost.append((st, gi))
            if gi == j0 and (ns >> j0) & 1 and not ((st >> xr) & 1 and not (st >> xa) & 1):
                dup.append((st, gi))
    hz, _, _ = hazards(net, adj, exclude=set(net.env))
    ex = None
    bad = mon or lost or dup
    if bad:
        st = bad[0][2] if mon else bad[0][0]
        best = None
        for s0 in starts:
            tr = trace_to(net, s0, st)
            if tr is not None and (best is None or len(tr) < len(best[1])):
                best = (s0, tr)
        what = mon[0][:2] if mon else ("x_ack rose with j0 = 0 (lost token)" if lost else "j0 rose twice")
        ex = f"{what} in {fmt_state(net, st)}; from {fmt_state(net, best[0])}: {' '.join(best[1])}"
    return dict(states=len(adj), hz=len(hz), mon=len(mon), lost=len(lost), dup=len(dup), ex=ex)


if __name__ == "__main__":
    for variant in ("si", "early"):
        tot = dict(states=0, hz=0, mon=0, lost=0, dup=0)
        ex = None
        for LP in range(0, 3):
            for LQ in range(0, 3):
                for LR in (1, 2):
                    r = run(LP, LQ, LR, variant)
                    for k in tot:
                        tot[k] += r[k]
                    ex = ex or (r["ex"] and f"LP={LP} LQ={LQ} LR={LR}: {r['ex']}")
        print(f"{variant}: {tot}")
        if ex:
            print("   example:", ex)


def runt_scenario():
    """Hand-built continuation of the SI hazard: in the state just after the
    disabling firing, x_ack (uxa) dips to 0 and recovers (a runt), with the x
    producer reacting in between.  Returns the narrated steps."""
    for LP in range(0, 3):
        for LQ in range(0, 3):
            for LR in (1, 2):
                net, ux = build(LP, LQ, LR, "si")
                comp = explore.make_completion(net)[0]
                S, E = net.S, len(net.env)
                guards = explore.stage_modes(net)[3]
                starts = [comp(x) for x in range(1 << (S + E))
                          if all(((x >> l) & 1) == 0 for gl in guards for l in gl)]
                starts = [s for s in starts if s is not None]
                adj = explore_from(net, starts)
                hz, _, _ = hazards(net, adj, exclude=set(net.env))
                hz = [h for h in hz if h[2] == ux]
                if not hz:
                    continue
                st, gi, _ = hz[0]
                p = st ^ (1 << gi)                       # uxa now disabled, still 1
                src = [i for i, g in enumerate(net.gates) if g["name"] == "SRC"][0]
                steps = [f"hazard state after {net.gates[gi]['name']} fires: {fmt_state(net, p)}"]
                p ^= 1 << ux                             # runt: x_ack dips to 0
                steps.append("runt: M.uxa dips to 0")
                if src in explore.excited(net, p):
                    p ^= 1 << src
                    steps.append("SRC (x producer, req = ~ack) rises: next x token offered")
                p |= 1 << ux                             # runt recovers to 1
                steps.append("runt ends: M.uxa back to 1 (its function still holds 1: j0=0, z_ack=1)")
                if src in explore.excited(net, p):
                    p ^= 1 << src
                    steps.append("SRC falls: the producer took ack=1 as the acknowledge of the new "
                                 "token, which M never joined (j0 = 0 throughout): LOST TOKEN")
                return f"LP={LP} LQ={LQ} LR={LR}: " + "; ".join(steps)
    return None


if __name__ == "__main__":
    print("runt scenario:", runt_scenario())
