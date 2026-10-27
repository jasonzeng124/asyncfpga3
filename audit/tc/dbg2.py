import sys, re, collections; sys.path.insert(0, '/home/user/asyncfpga3/audit/tc')
import xrc
R = xrc.Route(sys.argv[1])
why = collections.Counter(); ex = {}
big = []
for b in R.routes:
    if b not in R.driver: continue
    dc, dp = R.driver[b]
    for cn, p in R.sinks_of[b]:
        if not re.fullmatch(r"A[1-6]", p) or "LUT" not in R.cells[cn]["type"]: continue
        sd = R.ic.get((f"{dc}/{dp}", f"{cn}/{p}"))
        if sd is None: continue
        n, s = R.sink_of_cellpin(cn, p)
        if n is None: k = 'nonet'
        elif not n.ok: k = re.sub(r"[XY]\d+", "", n.why)[:60]
        elif s is None: k = 'nosink'
        else:
            if s['d'][3] - sd > 1500: big.append((s['d'][3]-sd, sd, cn, p, dc))
            continue
        why[k] += 1; ex.setdefault(k, (cn, p, dc))
for k, v in why.most_common(15): print(v, k, ex[k])
big.sort(reverse=True); print(len(big)); [print(x) for x in big[:5]]
