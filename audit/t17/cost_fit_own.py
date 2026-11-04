# T17: own least-squares fit of latency (ns, 10 ns/cycle) = base + k*K + ctzpre*P + main*M + ctzin*I
# over the 24 gcd_cost vectors, for the board (gcd_cost.tsv latmin) and a BENCHRES log.  usage: cost_fit_own.py TSV LOG
import re, sys, numpy as np
rows = [l.split('\t') for l in open(sys.argv[1]).read().split('\n')[1:] if l.strip()]
X = np.array([[1, int(r[2]), int(r[3]), int(r[4]), int(r[5])] for r in rows], float)
keys = [(int(r[0]), int(r[1])) for r in rows]
brd = np.array([10 * int(r[8]) for r in rows], float)
sim = {(int(m.group(1), 16), int(m.group(2), 16)): int(m.group(3)) for m in
       re.finditer(r"op0=([0-9a-f]+) op1=([0-9a-f]+) .*?latmin=(\d+)", open(sys.argv[2]).read())}
y = np.array([10 * sim[k] for k in keys], float)
for name, v in (("board", brd), ("log", y)):
    c, *_ = np.linalg.lstsq(X, v, rcond=None)
    print("%-6s base %.1f  k %.1f  ctzpre %.1f  main %.1f  ctzin %.1f  rms %.1f" %
          (name, *c, np.sqrt(np.mean((X @ c - v) ** 2))))
