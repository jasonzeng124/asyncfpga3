# T67: period per round from two BENCHRES lines (rounds r1 < r2, same seed): P = (latmin2 - latmin1) * fclk / (r2 - r1).
# Also checks both results against the audit's own xorshift (t40/oracle.py semantics, re-implemented here).
import re, sys
M = 0xFFFFFFFF
def xs(s, r):
    x = s
    for _ in range(r & 0xFFF): x ^= (x << 13) & M; x ^= x >> 17; x ^= (x << 5) & M
    return x
rows = []
for l in open(sys.argv[1]):
    m = re.search(r'BENCHRES .*fclk_ps=(\d+) .*op0=([0-9a-f]+) op1=([0-9a-f]+) n=(\d+) completed=(\d+) .*latmin=(\d+) latmax=(\d+) .*odata=([0-9a-f]+) .*(DONE|HANG)', l)
    if m: rows.append(m)
ok = all(int(m[8], 16) == xs(int(m[2], 16), int(m[3], 16)) and m[9] == 'DONE' and m[4] == m[5] for m in rows)
(a, b) = rows[0], rows[1]
f = int(a[1]); r1, r2 = int(a[3], 16), int(b[3], 16); l1, l2 = int(a[6]), int(b[6])
P = (l2 - l1) * f / (r2 - r1)
print(f"{sys.argv[1]}: oracle {'OK' if ok else 'MISMATCH'} ({len(rows)} rows); rounds {r1}/{r2} latmin {l1}/{l2} (latmax {a[7]}/{b[7]}); "
      f"period {P/1000:.3f} ns (+-{f/(r2-r1)/1000*1:.3f})")
