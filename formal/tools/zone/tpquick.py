"""tpquick.py -- probe C-12d: targeted transport (pure-delay) checks at one
corner, one tck-reach run per (corner, property, parameter), `-l bad` BFS.
A REACHABLE answer comes back fast (a witness exists); UNREACHABLE needs the
whole zone graph and may time out (reported as '?').
Run: [ROWS=i,j,..] [TMO=s] python3 -I tpquick.py [corner,...]   (default FASTp,SLOWp,FMINp,FAST)
"""
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from onecorner import CORNERS, build  # noqa: E402
from arb import props  # noqa: E402
from tckmodel import reach  # noqa: E402

ROWS = [  # (label, property, build kwargs)
    ("wq_g=0.1 (12c: mutex_nr fails for every wq_g > 0)", "mutex_nr", dict(wq_g=(0.1, 0.1))),
    ("wq_g=8", "mutex_nr", dict(wq_g=(8, 8))),
    ("wq_g=8 wq_s=8 (equal copies)", "mutex_nr", dict(wq_g=(8, 8), wq_s=(8, 8))),
    ("wq_g=8, no runt anywhere", "mutex_nra", dict(wq_g=(8, 8))),
    ("srv=[0,20] ack exclusion, no q runt", "amutex_nr", dict(srv=(0, 20))),
    ("srv=[0,20] tx, no q runt", "tx_nr", dict(srv=(0, 20))),
]


TMO = int(os.environ.get('TMO', '300'))   # s per check; machine shared by ~12 probes, '?' = not finished


def main():
    cors = sys.argv[1].split(",") if len(sys.argv) > 1 else ["FASTp", "SLOWp", "FMINp", "FAST"]
    for cor in cors:
        o6 = CORNERS[cor]["o6"][0]
        rows = ROWS + [(f"wa={2*o6+4-0.1:.1f} (A0-rise fork, just below 2*O6lo+c_lo)", "tx_nr",
                        dict(wa=(2 * o6 + 4 - 0.1,) * 2)),
                       (f"wa={2*o6+4:.1f} (at 2*O6lo+c_lo)", "tx_nr", dict(wa=(2 * o6 + 4,) * 2))]
        sel = os.environ.get("ROWS")
        if sel:
            rows = [rows[int(i)] for i in sel.split(",")]
        for label, pr, kw in rows:
            t = time.time()
            c = build(CORNERS[cor], mode="transport", **kw)
            r = reach(c.tck(props("transport")[pr]), mem_gb=2.5, timeout=TMO)
            v = {True: "REACHABLE", False: "unreachable", None: "? (" + str(r.get("err", ""))[:40] + ")"}[r["reachable"]]
            print(f"[tran] {cor:6} {pr:10} {label:58} {v:12} zones={r.get('VISITED_STATES')} "
                  f"{time.time()-t:.1f}s", flush=True)


if __name__ == "__main__":
    main()
