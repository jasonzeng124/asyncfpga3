#!/usr/bin/env python3
# PS_MON_GEN wrapper (build_ps.sh runs it with python3): both audit monitors into one file
import subprocess, sys, os
d = os.path.dirname(os.path.abspath(__file__)); a, b, c = sys.argv[3] + ".a", sys.argv[3] + ".b", sys.argv[3] + ".c"
mons = [("mon_latch.py", a), ("mon_steer.py", b)] + ([("mon_mux.py", c)] if os.environ.get("MON_KERNEL") else [])
for s, o in mons:
    subprocess.run([sys.executable, "-I", os.path.join(d, s), sys.argv[1], sys.argv[2], o], check=True)
open(sys.argv[3], "w").write("".join(open(o).read() for _, o in mons))
