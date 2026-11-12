"""truncated (50 ms cap) runs: compare reader-latch held values per closed phase on the common prefix, and out0_data
sampled values (none: no output before the cap) -- prefix comparison against the mid run."""
import sys, pickle, glob
sys.path.insert(0, "/tmp/claude-0/arbh")
from chk import captures, ev
for a, b in ((2147483648, 1073741824), (3280387012, 271041745)):
    for c in (1, 0):
        R = pickle.load(open("/tmp/claude-0/arbh/runs/b_%d_%d_c%d_mid.pkl" % (a, b, c), "rb")); cr = captures(R)
        for tag in ("adv_k0", "adv2_k0", "adv_k0.44", "adv2_k0.44"):
            H = pickle.load(open("/tmp/claude-0/arbh/runs/b_%d_%d_c%d_%s.pkl" % (a, b, c, tag), "rb")); ch = captures(H)
            res = {}
            for L in cr:
                x, y = cr[L][0], ch[L][0]; n = min(len(x), len(y)); res[L.split("_")[1]] = (n, sum(1 for i in range(n) if x[i] != y[i]))
            print("(%d,%d) c=%d %-10s reader held values (phases compared, mismatches): %s" % (a, b, c, tag, res))
