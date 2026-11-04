# T21: own extraction of the board's FIXED-mode latencies for one August build from the owner's logs.
# Takes every log that programs build/hw/BUILD/BUILD.bit (owner README pairing: all such ipow logs are match=yes),
# and every "(a) FIXED-mode repeatability: op0=A op1=B" block's latmin/latmax/odata.  usage: board_own.py LOGDIR BUILD
import glob, os, re, sys
d, b = sys.argv[1:3]
rows = {}
for p in sorted(glob.glob(os.path.join(d, "_*.log"))):
    s = open(p, errors="replace").read()
    if "programming build/hw/%s/%s.bit" % (b, b) not in s: continue
    for m in re.finditer(r"FIXED-mode repeatability: op0=(\d+) op1=(\d+), N=(\d+) ===\s*\n\s*completed=(\d+) latmin=(\d+) latmax=(\d+) cyc.*?odata=(\d+)", s):
        a, bb, n, c, lo, hi, od = m.groups()
        rows.setdefault((int(a), int(bb)), []).append((int(lo), int(hi), int(od), int(n), int(c), os.path.basename(p)))
for k in sorted(rows, key=lambda k: min(r[0] for r in rows[k])):
    print(k[0], k[1], " ".join("%d-%d:%d(%d/%d,%s)" % r for r in rows[k]))
