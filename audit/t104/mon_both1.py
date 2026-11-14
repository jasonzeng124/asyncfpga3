#!/usr/bin/env python3
# T104 PS_MON_GEN wrapper: t104/mon_latch1.py (1-bit latches included) + t83 steer (+ mux with MON_KERNEL)
import subprocess, sys, os
d = os.path.dirname(os.path.abspath(__file__)); t83 = os.path.join(d, '..', 't83')
a, b, c = sys.argv[3] + ".a", sys.argv[3] + ".b", sys.argv[3] + ".c"
mons = [(os.path.join(d, "mon_latch1.py"), a), (os.path.join(t83, "mon_steer.py"), b)] + ([(os.path.join(t83, "mon_mux.py"), c)] if os.environ.get("MON_KERNEL") else [])
for s, o in mons:
    subprocess.run([sys.executable, "-I", s, sys.argv[1], sys.argv[2], o], check=True)
open(sys.argv[3], "w").write("".join(open(o).read() for _, o in mons))
