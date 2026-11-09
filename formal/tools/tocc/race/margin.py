"""settle margin of X22Y81.B5 before each reader latch opens (UNTRUSTED): for the last D change t_D before the reader's
next transparent phase: (enable rise + enable pin delay) - (t_D + D pin delay), per reader; plus the closed-window check."""
import sys, pickle
sys.path.insert(0, "/tmp/claude-0/race")
from chk import ev, pin, READERS
def margins(fn):
    H = pickle.load(open(fn, "rb")); D = ev(H, "SLICE_X22Y81.B5"); out = {}
    if len(D) < 2: return H, None
    for L, en in READERS.items():
        dD = pin(H, L, "SLICE_X22Y81.B5"); dE = pin(H, L, en); E = ev(H, en)
        # enable value 1 = transparent; rises are even-indexed (v0 = 0)
        tlast = D[-1] + dD
        nxt = [t + dE for i, t in enumerate(E) if i % 2 == 0 and t + dE > D[1] + dD]
        prv = [t + dE for i, t in enumerate(E) if i % 2 == 1 and t + dE <= D[1] + dD]
        out[L] = (nxt[0] - tlast if nxt else None, (D[1] + dD) - prv[-1] if prv else None)
    return H, out
if __name__ == "__main__":
    for fn in sys.argv[1:]:
        H, m = margins(fn)
        print(fn.split("/")[-1], "glitch/change", ev(H, "SLICE_X22Y81.B5")[1:], "per reader (settle-before-open ps, change-after-close ps):", m)
