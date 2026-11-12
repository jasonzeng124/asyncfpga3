# U->H margins of the target latches in a datal pickle (event ids decoded via the ao preamble)
import sys, pickle
cc = sys.argv[1]; pk = sys.argv[2]
sys.argv = ["ao.py", cc, "0"]
src = open("/tmp/claude-0/arbh/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
def s_(e): return "%s(%d)@%d" % (nm[el[e][0]], el[e][1], el[e][2])
D = pickle.load(open(pk, "rb"))
for k, m, x in D["OBL"]:
    if "U->H" in k and isinstance(x, tuple) and x[0] in ("SLICE_X36Y63.B6", "SLICE_X36Y68.B6", "SLICE_X37Y47.B6"):
        print(x[0], "U.B", s_(x[1]), "close", s_(x[2]), "margin", m)
