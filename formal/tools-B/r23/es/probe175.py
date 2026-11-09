import sys, threading, pickle
sys.setrecursionlimit(400000); threading.stack_size(1024 * 1024 * 1024)
def main():
    c_ = sys.argv[1]; sys.argv = ["ao.py", c_, "0"]
    G = {"__name__": "x"}
    src = open("/tmp/claude-0/bsub1/tocc175/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
    exec(src, G)
    exec(open("/home/user/asyncfpga3/formal/tools/tocc/r1b/relup.py").read().split("# ---------------- emission")[0], G)
    G["CURD"][0] = G["RELD"]
    el, nm, eid, sepAny, up_get, leqP = G["el"], G["nm"], G["eid"], G["sepAny"], G["up_get"], G["leqP"]
    idx = {n: i for i, n in enumerate(nm)}; E = lambda e: None if e is None else "%s(%d)@%d" % (nm[el[e][0]], el[e][1], el[e][2])
    M = pickle.load(open("/tmp/claude-0/bsub1/tocc175/x4_c%s.pkl" % c_, "rb"))["MEMO"]
    bank = eid[(idx["SLICE_X30Y76.A6"], 2)]
    for n in ("SLICE_X33Y91.B6", "SLICE_X33Y91.B5", "SLICE_X31Y75.B5"):
        for k, cl in M.items():
            if nm[k[0]] == n and cl.get("kind") == "latch":
                A = cl.get("A"); s = sepAny(A, bank)[0] if A is not None else None
                print(n, "claim key", k[1:3], "A", E(A), "a", cl.get("a"), "B", E(cl.get("B")), "Sep(A->bank reopen)", s, "leqP", leqP(A, bank) if A is not None else None, flush=True)
th = threading.Thread(target=main); th.start(); th.join()
