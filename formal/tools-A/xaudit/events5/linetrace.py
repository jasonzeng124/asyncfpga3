"""linetrace.py -- concrete fixed-delay transport trace of ONE routed delay line (UNTRUSTED,
cross-check only).

    python3 linetrace.py NET.json BANDS.json SRCNET OUTNET L_ps [--slow ELEM ...] [--all lo|hi]

Cuts the line (every LUT between net SRCNET and net OUTNET, with SRCNET as a free input), gives
every element ONE fixed delay: the band's `--all` end (default lo = FAST_MIN on an indep band
file), except the elements named by --slow (cell names = LUT, cell/I<k> = routed arc), which
get the band's hi (SLOW_MAX).  Drives SRCNET: rise at 10 ns, fall at 40 ns, rise again L ps
later, fall at +40 ns.  Pure transport, binary, event driven (csim.py's semantics).
Prints every transition of OUTNET and of the chain nets, and the matched-delay check:
the second rise of OUTNET must come no earlier than (second rise of SRCNET + the first
rise's delay) -- otherwise the request skipped its bundling delay.
"""
import argparse, heapq, json

ap = argparse.ArgumentParser()
ap.add_argument("net"); ap.add_argument("bands"); ap.add_argument("src", type=int); ap.add_argument("out", type=int)
ap.add_argument("L", type=int); ap.add_argument("--slow", nargs="*", default=[]); ap.add_argument("--all", default="lo")
a = ap.parse_args()
m = next(iter(json.load(open(a.net))["modules"].values()))
B = json.load(open(a.bands))
drv = {c["connections"]["O"][0]: cn for cn, c in m["cells"].items()}
# cells of the line: backward from OUT to SRC
cells, todo = set(), [a.out]
while todo:
    x = todo.pop()
    if x == a.src or x not in drv or drv[x] in cells:
        continue
    cn = drv[x]; cells.add(cn)
    c = m["cells"][cn]
    for k in range(int(c["type"][3:])):
        b = c["connections"]["I%d" % k][0]
        if isinstance(b, int):
            todo.append(b)
slow = set(a.slow)
pick = lambda key, band: band[1] if (key in slow or a.all == "hi") else max(1, band[0])
gates, sinks, val = [], {}, {}
for cn in sorted(cells):
    c = m["cells"][cn]; k = int(c["type"][3:])
    g = [int(c["parameters"]["INIT"], 2), [0] * k, c["connections"]["O"][0], pick(cn, B["cells"][cn]), cn]
    for i in range(k):
        b = c["connections"]["I%d" % i][0]
        if isinstance(b, str):
            g[1][i] = int(b)
        else:
            sinks.setdefault(b, []).append((len(gates), i, pick("%s/I%d" % (cn, i), B["arcs"]["%s/I%d" % (cn, i)])))
    gates.append(g)
outs = {g[2]: g[4] for g in gates}
missing = [b for b in sinks if b not in outs and b != a.src]
assert not missing, f"line has inputs other than SRC: {missing}"
q, seq = [], [0]
def push(t, *e):
    seq[0] += 1; heapq.heappush(q, (t, seq[0]) + e)
T1, F1 = 10000, 40000
T2 = F1 + a.L
for t, v in ((T1, 1), (F1, 0), (T2, 1), (T2 + 40000, 0)):
    push(t, "net", a.src, v)
rises = {a.src: [], a.out: []}
log = []
while q:
    t, _, kind, x, y = heapq.heappop(q)
    if kind == "net":
        if val.get(x, 0) == y:
            continue
        val[x] = y
        if x in rises and y == 1:
            rises[x].append(t)
        log.append((t, "SRC" if x == a.src else outs.get(x, x), y))
        for gi, pi, d in sinks.get(x, []):
            push(t + d, "pin", gi, (pi, y))
    elif kind == "pin":
        pi, v = y; g = gates[x]
        if g[1][pi] != v:
            g[1][pi] = v; push(t, "eval", x, None)
    else:
        g = gates[x]; addr = sum(b << i for i, b in enumerate(g[1]))
        push(t + g[3], "net", g[2], (g[0] >> addr) & 1)
print(f"line: {len(gates)} LUTs; L = {a.L} ps; slow elements: {sorted(slow)}")
for t, nm, v in log:
    if nm == "SRC" or "g[0]" in str(nm) or "g[1]" in str(nm) or nm == outs.get(a.out) or "uor" in str(nm):
        print(f"  {t:8d} ps  {nm} = {v}")
r = rises[a.out]
d1 = r[0] - T1 if r else None
print(f"OUT rises at {r}; matched delay (1st rise) {d1} ps")
if len(r) >= 2:
    early = r[1] - T2
    print(f"2nd SRC rise at {T2}; first OUT rise after it at +{early} ps: " +
          ("SKIPS the matched delay (early by %d ps)" % (d1 - early) if early < d1 else "matched (not early)"))
    print(f"OUT rose {len(r)} times for 2 SRC rises" + (" -> GLITCH (extra request pulse)" if len(r) > 2 else ""))
