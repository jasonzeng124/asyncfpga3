import sys, threading
sys.setrecursionlimit(400000); threading.stack_size(1024 * 1024 * 1024)
def main():
    c_ = sys.argv[1]; pairs = [tuple(map(int, x.split(":"))) for x in sys.argv[2:]]; sys.argv = ["ao.py", c_, "0"]
    g_ = {"__name__": "x"}
    src = open("/tmp/claude-0/bsub1/tocc/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
    exec(src, g_)
    exec(open("/home/user/asyncfpga3/formal/tools/tocc/r1b/relup.py").read().split("# ---------------- emission")[0], g_)
    g_["CURD"][0] = g_["RELD"]
    el, nm = g_["el"], g_["nm"]
    for a, b in pairs:
        print("%s(%d)@%d -> %s(%d)@%d" % (nm[el[a][0]], el[a][1], el[a][2], nm[el[b][0]], el[b][1], el[b][2]), "sep23", g_["sep23"](a, b), "sepAny", g_["sepAny"](a, b), "form4", g_["form4"](a, b), "leqP", g_["leqP"](a, b), flush=True)
th = threading.Thread(target=main); th.start(); th.join()
