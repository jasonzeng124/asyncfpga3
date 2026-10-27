import sys, re, collections; sys.path.insert(0,'/home/user/asyncfpga3/audit/tc'); import xrc
R = xrc.Route(sys.argv[1])
c = collections.Counter(); w = collections.Counter()
for (src, dst), d in R.ic.items():
    cs, ps = src.rsplit('/',1); cd, pd = dst.rsplit('/',1)
    if cd not in R.cells: continue
    ok = False
    if re.fullmatch(r"A[1-6]", pd) and "LUT" in R.cells[cd]["type"]:
        n, s = R.sink_of_cellpin(cd, pd); ok = s is not None and n.ok
    if not ok:
        k = (R.cells[cd]['type'], pd, R.cells[cs]['type'] if cs in R.cells else '?'); c[k] += 1; w[k] += d
for k, v in w.most_common(15): print(k, c[k], v)
io = collections.Counter()
for (inst, a, z), d in R.io.items():
    if inst in R.cells and 'LUT' not in R.cells[inst]['type']: io[(R.cells[inst]['type'], a, z, d)] += 1
for k, v in io.most_common(15): print(k, v)
