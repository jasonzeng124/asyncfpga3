# profile the relative Up for the R1 pair E=SLICE_X39Y47.D6(1), B=SLICE_X30Y76.A6(2) at c=1
import sys, os, cProfile, pstats, time
sys.argv = ["ao.py", "1", "0"]
src = open("/tmp/claude-0/arbh/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
exec(open("/tmp/claude-0/arbh/relup.py").read())
r = {nm[n]: n for n in EX}
E = eid[(r["SLICE_X39Y47.D6"], 1)]; B = eid[(r["SLICE_X30Y76.A6"], 2)]
sys.setrecursionlimit(100000)
import threading
threading.stack_size(512*1024*1024)
def main():
    for D in [int(x) for x in os.environ.get("DS","0 1 2").split()]:
        t = time.time()
        pr = cProfile.Profile(); pr.enable()
        res = form4(E, B, None, D)
        pr.disable()
        print("depth", D, "form4", res, "%.1fs" % (time.time() - t), dict(RELSTAT), len(UPST), flush=True)
        if D == max(int(x) for x in os.environ.get("DS","0 1 2").split()): pstats.Stats(pr).sort_stats("cumulative").print_stats(12)
th = threading.Thread(target=main); th.start(); th.join()
