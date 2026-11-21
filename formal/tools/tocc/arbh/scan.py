"""scan operand pairs (mid, c=0): does X22Y81.B5 ever change after its first change, i.e. do the mux inputs ever differ at a select change?"""
import sys, os, subprocess, pickle, random
sys.path.insert(0, "/tmp/claude-0/arbh")
from chk import ev, val
pairs = [(0, 5), (5, 0), (1, 1), (0xffffffff, 0xfffffffe), (0x80000000, 0x40000000), (3, 0x7fffffff), (0xdeadbeef, 0x1234567)]
rng = random.Random(1); pairs += [(rng.getrandbits(32), rng.getrandbits(32)) for _ in range(6)] + [(rng.getrandbits(8), rng.getrandbits(8)) for _ in range(6)]
for a, b in pairs:
    fn = "/tmp/claude-0/arbh/runs/scan_%d_%d.pkl" % (a, b)
    r = subprocess.run(["python3", "/tmp/claude-0/arbh/simk.py", "0", str(a), str(b)], env=dict(os.environ, ADV="{}", OUT=fn), capture_output=True, text=True, timeout=900)
    H = pickle.load(open(fn, "rb"))
    sel = ev(H, "SLICE_X27Y80.B6")
    diff = [t for t in sel if val(H, "SLICE_X22Y87.D5", t) != val(H, "SLICE_X22Y79.D5", t)]
    print("(%d,%d) res %s | X22Y81.B5 changes %d, X27Y80.B6 changes %d, D5/D5' differ at a select change %d, X22Y87.D5 %d X22Y79.D5 %d changes" % (
        a, b, H["res"], len(ev(H, "SLICE_X22Y81.B5")), len(sel), len(diff), len(ev(H, "SLICE_X22Y87.D5")), len(ev(H, "SLICE_X22Y79.D5"))), flush=True)
