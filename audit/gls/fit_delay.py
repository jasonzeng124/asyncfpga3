#!/usr/bin/env python3
"""Fit iverilog SLICE_LUTX O6 traces against candidate delay semantics.
usage: fit_delay.py LOG INIT D1 D2 D3
Models (all with per-pin delay d_k):
  transport   : o(t) = f(a1(t-d1), a2(t-d2), a3(t-d3))
  inertial    : on each f-change at t via pin k, cancel pending, schedule f@t at t+d_k
  saf_pin     : every pin change at t schedules a fire at t+d_k that copies f(now)
  saf_f       : every f-change at t (via pin k) schedules a fire at t+d_k copying f(now)
Compares the set of output change events (t, value) after t>=1000."""
import sys, bisect
log, INIT, D = sys.argv[1], int(sys.argv[2], 0), [int(x) for x in sys.argv[3:6]]
ins, outs = [], []
for ln in open(log):
    p = ln.split()
    if p[0] == 'I': ins.append((int(p[1]), int(p[2]), tuple(int(c) for c in p[3])))
    elif p[0] == 'O' and p[2] in '01': outs.append((int(p[1]), int(p[2])))
f = lambda v: (INIT >> (v[0] | v[1] << 1 | v[2] << 2)) & 1
outs = [e for e in outs if e[0] >= 1000]
times = [t for t, _, _ in ins]
def val_at(t):  # input vector just before t: a fire coinciding with an input
    # change reads the old value (the change reaches f a delta later)
    i = bisect.bisect_left(times, t) - 1
    return ins[i][2] if i >= 0 else (0, 0, 0)
def edges(seq, init=0):
    res, cur = [], init
    for t, v in sorted(seq, key=lambda x: x[0]):
        if v != cur: res.append((t, v)); cur = v
    return res
def transport():
    # each pin delayed separately, evaluate f on delayed pins
    ev = []
    for t, k, v in ins: ev.append((t + D[k], k, v[k]))
    ev.sort(); cur = [0, 0, 0]; seq = []
    i = 0
    while i < len(ev):
        t = ev[i][0]
        while i < len(ev) and ev[i][0] == t:
            cur[ev[i][1]] = ev[i][2]; i += 1
        seq.append((t, f(cur)))
    return edges(seq)
def inertial():
    import heapq
    q = []; pend = None; out = 0; res = []; prevf = 0
    evs = sorted(ins)
    # event-driven: process input events and pending fire in time order
    i = 0
    while i < len(evs) or pend:
        if pend and (i >= len(evs) or pend[0] <= evs[i][0]):
            t, v = pend; pend = None
            if v != out: out = v; res.append((t, v))
            continue
        t, k, v = evs[i]; i += 1
        fv = f(v)
        if fv != prevf:
            prevf = fv
            pend = (t + D[k], fv) if fv != out else None
    return res
def saf(trigger_on_f):
    fires = []; prevf = 0
    for t, k, v in ins:
        fv = f(v)
        if (not trigger_on_f) or fv != prevf: fires.append(t + D[k])
        prevf = fv
    return edges(sorted((tf, f(val_at(tf))) for tf in fires))
models = {'transport': transport(), 'inertial': inertial(), 'saf_pin': saf(False), 'saf_f': saf(True)}
for name, m in models.items():
    ok = m == outs
    first = next(((a, b) for a, b in zip(m, outs) if a != b), None)
    print("%-10s %s  model_edges=%d gls_edges=%d first_diff(model,gls)=%s" % (name, 'MATCH' if ok else 'differ', len(m), len(outs), first))
