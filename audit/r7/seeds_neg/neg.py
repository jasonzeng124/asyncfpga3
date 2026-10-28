#!/usr/bin/env python3
"""Negative controls for seeds_fid.py's verdict: build_fid/run_fid are stubbed (sh -> 0), the sweep logs are
written by this script, and sim() is called as seeds_fid calls it.  Expect PASS only for the all-good case."""
import sys, os, shutil, types, importlib.util
spec = importlib.util.spec_from_file_location("seeds_fid", sys.argv[1]); m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
m.sh = lambda cmd, log, env=None, cwd=None: 0
root = os.path.abspath(sys.argv[2]); shutil.rmtree(root, ignore_errors=True); os.makedirs(root)
hw = os.path.join(root, "hw"); os.makedirs(hw)
for f in ("gcd_hw.sdf", "gcd_hw_xray.sdf"): open(os.path.join(hw, f), "w").write("x")
GOOD = "# VEC={v}\nRESULT timeout: vec={v} laps=40 errs=0 oks=40\nSUMMARY vec={v} laps=40 errs=0 oks=40 hk=1 t_end=1\n"
cases = {
  "all_good": {},
  "v7_missing_file": {7: None},
  "v7_empty": {7: ""},
  "v7_truncated_before_result": {7: "# VEC=7\nLAP 1 t=5\n"},
  "v7_result_no_summary": {7: "# VEC=7\nRESULT timeout: vec=7 laps=40 errs=0 oks=40\n"},
  "v7_summary_no_result": {7: "SUMMARY vec=7 laps=40 errs=0 oks=40\n"},
  "v7_garbled_bytes": {7: "\x00\x13garbage RESULT SUMM ARY vec=7 laps=x\n"},
  "v7_deadlock": {7: "RESULT deadlock: vec=7 laps=3 last\nSUMMARY vec=7 laps=3 errs=0 oks=3\n"},
  "v7_zero_laps": {7: "RESULT timeout: vec=7 laps=0 errs=0 oks=0\nSUMMARY vec=7 laps=0 errs=0 oks=0\n"},
  "v7_errs": {7: "RESULT timeout: vec=7 laps=40 errs=2 oks=38\nSUMMARY vec=7 laps=40 errs=2 oks=38\n"},
  "v7_ring_stopped": {7: "RESULT ring-stopped: x\nSUMMARY vec=7 laps=40 errs=0 oks=40\n"},
}
for name, over in cases.items():
    a = types.SimpleNamespace(out=os.path.join(root, name)); os.makedirs(a.out)
    work = os.path.join(a.out, "s", "min", "sweep"); os.makedirs(work)
    for v in range(16):
        t = over.get(v, GOOD.format(v=v))
        if t is None: continue
        open(os.path.join(work, "v%d.log" % v), "w").write(t)
    print("%-28s" % name, end=" "); sys.stdout.flush()
    m.sim(a, "s", hw, "min", None)
