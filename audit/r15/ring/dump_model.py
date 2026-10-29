#!/usr/bin/env python3
"""Auditor r15: dump per-ring, per-draw P_model (research's own delay model via ring128_summary.model_periods)
with P_pre / P_np, so the summary statistics + verdict can be recomputed by mystats.py (auditor code).
usage: dump_model.py CONFIG DRAWS OUT.tsv ROUTE_DIR..."""
import sys, os, importlib.util
from pathlib import Path
F = Path.home() / "r15work/wt-ring/cells/gls/fid"
spec = importlib.util.spec_from_file_location("R", F / "ring128_summary.py"); R = importlib.util.module_from_spec(spec)
sys.path.insert(0, str(F)); spec.loader.exec_module(R)
cfg, draws, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
db = os.environ["XRAY_DB"]; grid = R.tile_grid(db)
routes = [R.Route(d, db, grid) for d in sys.argv[4:]]
which, env = R.CONFIGS[cfg]
nd = draws if R.scattered(env) else 1
with open(out, "w") as f:
    f.write("sample\troute\tdraw\tring\tlinks\tP_model_ps\tP_pre_ps\tP_np_ps\n")
    for rt in routes:
        for s in range(1, nd + 1):
            pm = R.model_periods(rt, which, env, s)
            for r in sorted(rt.length):
                f.write(f"{rt.dir.name}:{s}\t{rt.dir.name}\t{s}\t{r}\t{rt.length[r]}\t{pm[r]}\t{rt.p_pre[r]}\t{rt.p_np[r]}\n")
            print(rt.dir.name, s, flush=True)
