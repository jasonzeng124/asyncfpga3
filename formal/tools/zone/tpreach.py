"""tpreach.py -- probe C-12d: targeted transport (pure-delay) reachability
checks with one consistent corner.  A full transport exploration with rise =
fall arcs does not finish (> 10 min, > 0.8 GB per row under load): with equal
rise/fall pure delays a runt on q never shrinks, so tier-3 oscillations stay
alive and the zone graph explodes (with 12c's 56/124 asymmetry they die).
So here only REACHABLE answers are sought (tck-reach stops at the first hit);
an unreachable answer would need the full graph and is not attempted.
Run: python3 -I tpreach.py
"""
import os
import sys
import time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from onecorner import CORNERS, build  # noqa: E402
from arb import props  # noqa: E402
from tckmodel import reach  # noqa: E402

ROWS = [
    # (corner, property, kwargs)
    ("FASTp", "mutex", dict()),                       # q runt, tier 3, zero routing
    ("SLOWp", "mutex", dict()),
    ("FASTp", "mutex_nr", dict(wq_g=(8, 8))),         # grant-fork runt, no q runt
    ("SLOWp", "mutex_nr", dict(wq_g=(8, 8))),
    ("FASTp", "mutex_nr", dict(wq_g=(0.5, 0.5))),
    ("SLOWp", "mutex_nr", dict(wq_g=(0.5, 0.5))),
    ("FAST", "mutex_nr", dict(wq_g=(8, 8))),
    ("SLOW", "mutex_nr", dict(wq_g=(8, 8))),
    ("CM.5k20", "mutex_nr", dict(wq_g=(8, 8))),
    ("FASTp", "amutex_nr", dict(srv=(0, 20))),        # 12c: transport needs s_lo >= 56
    ("SLOWp", "amutex_nr", dict(srv=(0, 20))),
]

if __name__ == "__main__":
    t0 = time.time()
    for cor, p, kw in ROWS:
        r = reach(build(CORNERS[cor], mode="transport", K=3, **kw).tck(props("transport")[p]),
                  mem_gb=2.5, timeout=900)
        print(f"[tran] {cor:8} {p:10} {kw}: reachable={r['reachable']} "
              f"zones={r.get('VISITED_STATES')} {r['seconds']:.1f}s "
              + (str(r.get('err', ''))[-120:].replace(chr(10), ' ') if r['reachable'] is None else ''),
              flush=True)
    print(f"total {time.time()-t0:.1f}s")
