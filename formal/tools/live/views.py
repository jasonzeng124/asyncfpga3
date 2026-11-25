#!/usr/bin/env python3
"""views.py OUT.tsv -- research's ring_tokens.py, both views separately, on every fixture x {def, auto} x floor {on, off}.
Columns: fixture flow floor cycle_view(short/ok) walk_view(short/ok/refused). Read-only use of /home/user/rs (research's tree)."""
import os, subprocess, sys, glob
RS = "/home/user/rs"
out = open(sys.argv[1], "w")
for d in sorted(glob.glob(RS + "/cloud/fixtures/frontend/*/comp/handshake_transformed.mlir")):
    fx = d.split("/")[-3]
    for flow in ("def", "auto"):
        for floor in ("on", "off"):
            env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
            if flow == "auto": env["BDC_AUTO"] = "1"
            if floor == "off": env["BDC_TOKEN_FLOOR"] = "0"
            try:
                p = subprocess.run([sys.executable, "-B", "research/tools/suite/ring_tokens.py", d], cwd=RS, env=env,
                                   capture_output=True, text=True, timeout=300)
                t = p.stdout + p.stderr
            except subprocess.TimeoutExpired:
                t = "TIMEOUT"
            if "worst cycle" in t:
                cyc = "short" if "short when" in t and ("(short)" in t or "nodes on cycles" in t) else "ok"
            elif "every cycle has more" in t:
                cyc = "ok"
            else:
                cyc = "refused"
            wlk = "ok" if "every walk holds a token" in t else ("short" if "walk" in t else "refused")
            out.write(f"{fx}\t{flow}\t{floor}\t{cyc}\t{wlk}\n"); out.flush()
