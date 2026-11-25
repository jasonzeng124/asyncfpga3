#!/usr/bin/env python3
"""Shard B (UNTRUSTED): which readers of ua1 must see its runts for the run to fail? Each run lets ONE reader pin
see them (others skip pulses < W); reports CHAOS / RESULT. usage: readers.py NET.json BND.json POSMAP FILTALL.json KAPPA"""
import json, subprocess, sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
NET, BND, PM, FA, K = sys.argv[1:6]
allf = json.load(open(FA)); tmp = os.path.join(os.environ.get("TMPDIR", "/tmp"), "filt_one.json")
for key in [None] + list(allf):
    f = {k: v for k, v in allf.items() if k != key}
    json.dump(f, open(tmp, "w"))
    out = subprocess.run([sys.executable, "-I", os.path.join(HERE, "simb.py"), NET, BND, "--pairs", "0xC,0x12", "--corner", "0.5",
                          "--kappa", K, "--tmax", "1200000", "--posmap", PM, "--filter", tmp, "--maxevents", "3000000"],
                         capture_output=True, text=True)
    res = [l for l in (out.stdout + out.stderr).splitlines() if "RESULT" in l or "CHAOS" in l]
    print("reader seeing the runts:", key or "none", "->", res[-1] if res else out.stderr[-200:], flush=True)
