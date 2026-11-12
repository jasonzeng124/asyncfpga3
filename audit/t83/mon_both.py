#!/usr/bin/env python3
# PS_MON_GEN wrapper (build_ps.sh runs it with python3): both audit monitors into one file
import subprocess, sys, os
d = os.path.dirname(os.path.abspath(__file__)); a, b = sys.argv[3] + ".a", sys.argv[3] + ".b"
for s, o in (("mon_latch.py", a), ("mon_steer.py", b)):
    subprocess.run([sys.executable, "-I", os.path.join(d, s), sys.argv[1], sys.argv[2], o], check=True)
open(sys.argv[3], "w").write(open(a).read() + open(b).read())
