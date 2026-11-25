import pickle, sys
sys.path.insert(0, "/tmp/claude-0/tocc")
from classify import load
C = load(); nm = C["names"]
A = pickle.load(open(sys.argv[1], "rb")); B = pickle.load(open(sys.argv[2], "rb")); R = A["R"]
def cnt(H, n): return len([x for x in H["hist"].get(n, (0, []))[1] if x >= R])
diff = [(nm[n], cnt(A, n), cnt(B, n)) for n in C["EXACT"] if cnt(A, n) != cnt(B, n)]
print("outputs mid", A["res"], "adv", B["res"], "; exact nodes with a different number of events:", len(diff), diff[:8])
for nmx in sys.argv[3:]:
    i = nm.index(nmx); print("  ", nmx, "mid", [x for x in A["hist"][i][1] if x >= R], "adv", [x for x in B["hist"][i][1] if x >= R])
