"""witness1c.py -- probe C-12d: symbolic witness (event sequence + zones) for
one onecorner.py configuration, via tck-reach -a reach -C symbolic.

Usage: python3 -I witness1c.py CORNER MODE PROP [key=lo,hi ...] [unheld] [-z]
(-z: also print each zone)
  e.g. python3 -I witness1c.py CM0k20 inertial amutex srv=0,20
       python3 -I witness1c.py FAST transport mutex_nr wq_g=24,24
Prints, per step, the synchronised event (the node that fired), the int
variables that changed, and the zone (clock constraints, units 0.1 ps).
"""
import os
import re
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from onecorner import CORNERS, build  # noqa: E402
from arb import props  # noqa: E402
from tckmodel import TCK  # noqa: E402


ZONES = "-z" in sys.argv


def main():
    if ZONES:
        sys.argv.remove("-z")
    cor, mode, prop = sys.argv[1:4]
    kw = {}
    for a in sys.argv[4:]:
        if a == "unheld":
            kw["held"] = False
            continue
        k, v = a.split("=")
        lo, hi = v.split(",")
        kw[k] = (float(lo), float(hi))
    c = build(CORNERS[cor], mode=mode, **kw)
    text = c.tck(props(mode)[prop])
    fd, path = tempfile.mkstemp(suffix=".tck")
    with os.fdopen(fd, "w") as fh:
        fh.write(text)
    p = subprocess.run(["bash", "-c", f"ulimit -v 3000000; exec {TCK} -a reach -l bad "
                        f"-s bfs -C symbolic {path}"], capture_output=True, text=True,
                       timeout=3600)
    os.unlink(path)
    out = p.stdout
    nodes, edges = {}, {}
    for m in re.finditer(r'^\s*(\d+) \[(.*)\]\s*$', out, re.M):
        nodes[int(m.group(1))] = dict(re.findall(r'(\w+)="([^"]*)"', m.group(2)))
    for m in re.finditer(r'^\s*(\d+) -> (\d+) \[(.*)\]\s*$', out, re.M):
        edges[int(m.group(1))] = (int(m.group(2)),
                                  dict(re.findall(r'(\w+)="([^"]*)"', m.group(3))))
    if not nodes:
        print(out[-3000:], p.stderr[-2000:])
        return
    print(f"# {cor} {mode} {prop} {kw}: REACHABLE, {len(nodes)} steps")
    cur = next(k for k, a in nodes.items() if a.get("initial") == "true")
    prev = {}
    while True:
        a = nodes[cur]
        iv = dict(kv.split("=") for kv in a.get("intval", "").split(",") if kv)
        ch = {k: v for k, v in iv.items() if prev.get(k) != v}
        names = [k for k in ch if not k.startswith(("mlt_", "ovf_", "hz_"))]
        print("  ", " ".join(f"{k}={ch[k]}" for k in names) or "-",
              *(("| zone:", a.get("zone", "")) if ZONES else ()))
        prev = iv
        if cur not in edges:
            print("   final node, labels:", a.get("labels", ""))
            break
        nxt, ea = edges[cur]
        ev = re.findall(r'f_(\w+)', ea.get("vedge", ""))
        print("   --> fire", ",".join(sorted(set(ev))))
        cur = nxt


if __name__ == "__main__":
    main()
