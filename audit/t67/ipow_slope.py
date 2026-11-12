# T67: per-iteration cost from an own oracle table (t46 oracle check output): least-squares slope of cycles (2 runs)
# vs iterations over the b=3, e=2^k-1 vectors; ratio = slope(base)/slope(cand).
import sys
def slope(f):
    pts = []
    for l in open(f):
        w = l.split()
        if len(w) > 10 and w[-1] == 'OK' and w[1] == '00000003' and int(w[2], 16) & (int(w[2], 16) + 1) == 0:
            pts.append((int(w[3]), int(w[9])))
    n = len(pts); mx = sum(x for x, _ in pts) / n; my = sum(y for _, y in pts) / n
    return sum((x - mx) * (y - my) for x, y in pts) / sum((x - mx) ** 2 for x, _ in pts), n
for base, cand, tag in [(sys.argv[1], sys.argv[2], 'FAST_MIN'), (sys.argv[3], sys.argv[4], 'worst')]:
    sb, nb = slope(base); sc, nc = slope(cand)
    print(f"{tag}: base {sb/2*12:.2f} ns/iter ({nb} pts), cand {sc/2*12:.2f} ns/iter ({nc} pts), ratio {sb/sc:.3f}")
