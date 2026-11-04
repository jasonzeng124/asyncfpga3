# T21: x = (board - FAST_MIN)/(SLOW_MAX - FAST_MIN) per vector for an August kernel; every simulated result checked
# against the board's odata.  usage: kernel_x_own.py BOARD_OWN_TXT MIN_LOG MAX_LOG [MINLAT=50]
import re, sys, statistics as st
brd = {}
for l in open(sys.argv[1]):
    f = l.split(); m = re.match(r"(\d+)-(\d+):(\d+)", f[2]); brd[(int(f[0]), int(f[1]))] = (int(m.group(1)), int(m.group(3)))
def L(p):
    return {(int(m.group(1), 16), int(m.group(2), 16)): (int(m.group(3)), int(m.group(4)), int(m.group(5)), int(m.group(6), 16), m.group(7))
            for m in re.finditer(r"op0=([0-9a-f]+) op1=([0-9a-f]+) n=(\d+) completed=(\d+).*?latmin=(\d+) latmax=\d+.*?odata=([0-9a-f]+) mism_st=(\d+)", open(p).read())}
mn, mx = L(sys.argv[2]), L(sys.argv[3]); lim = int(sys.argv[4]) if len(sys.argv) > 4 else 50
bad = [(k, c) for c, d in (("min", mn), ("max", mx)) for k, v in d.items() if v[3] != brd[k][1] or v[0] != v[1]]
print("vectors board %d min %d max %d; results != board or incomplete: %s" % (len(brd), len(mn), len(mx), bad or "none"))
xs = []
for k in sorted(brd, key=lambda k: brd[k][0]):
    b, lo, hi = brd[k][0], mn[k][2], mx[k][2]; x = (b - lo) / (hi - lo); print(k, b, lo, hi, "%.3f" % x)
    if b >= lim: xs.append(x)
print("x over vectors with board >= %d (%d): median %.3f range %.3f-%.3f" % (lim, len(xs), st.median(xs), min(xs), max(xs)))
