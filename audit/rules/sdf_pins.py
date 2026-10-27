# Own check: does nextpnr's SDF INTERCONNECT into a LUT input depend on the physical pin (A1..A6)?
# For in-slice hops (LUT O6 -> LUT A<k>), prjxray site-pin delays would make A1/A2 ~0.4-0.5 ns slower than A6.
import re, sys, collections
by = collections.defaultdict(list); io = collections.Counter()
for f in sys.argv[1:]:
    t = open(f).read()
    for m in re.finditer(r"\(INTERCONNECT (\S+)/O6 (\S+)/(A[1-6]) \((\d+):", t):
        by[m.group(3)].append(int(m.group(4)))
    for m in re.finditer(r"\(IOPATH (A[1-6]) (O[56]) \((\d+):\d+:(\d+)\) \((\d+):", t):
        io[(m.group(2), m.group(3), m.group(5))] += 1
for p in sorted(by):
    v = sorted(by[p]); print(p, "n", len(v), "min", v[0], "values", collections.Counter(v).most_common(4))
print("LUT IOPATH (out, rise, fall) counts:", dict(io))
