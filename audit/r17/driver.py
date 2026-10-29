#!/usr/bin/env python3
"""Audit r17 driver (from audit/r9/driver.py): at most 2 heavy jobs.  usage: driver.py TAG REGION WIRE DRAW [vecs]
Builds ~/r17work/s9_TAG with research build_fid.sh, compiles the auditor tb_audit.v (audit/r7/judge), runs vectors."""
import subprocess, threading, os, time, sys
A = "/home/user/asyncfpga3/audit/r17"; J = "/home/user/asyncfpga3/audit/r7/judge"
HW = os.path.expanduser("~/r17work/wt-s9/cells/build/hw/gcd_hw"); GLS = os.path.expanduser("~/r17work/wt-s9/cells/gls")
NJ = int(os.environ.get("NJ", "2")); TEND = os.environ.get("TEND", "150000")
sem = threading.Semaphore(NJ); lk = threading.Lock()
def log(s):
    with lk: open(A + "/driver.log", "a").write(time.strftime("%H:%M:%S ") + s + "\n")
def heavy(cmd, out):
    with sem:
        log("START " + cmd)
        rc = subprocess.run(cmd, shell=True, stdout=open(out, "w"), stderr=subprocess.STDOUT, executable="/bin/bash").returncode
        log("END rc=%d %s" % (rc, cmd)); return rc
tag, reg, wire, draw = sys.argv[1:5]
vecs = [int(v) for v in sys.argv[5].split(",")] if len(sys.argv) > 5 else list(range(16))
work = os.path.expanduser("~/r17work/s9_" + tag)
if not os.path.exists(work + "/netlist_baked.v"):
    # build_fid also compiles research's run_baked.vvp; we only need gen.py output, but keep the recipe unchanged
    if heavy(f"{A}/fid_build.sh {HW} {work} {reg} {wire} {draw}", f"{A}/build_{tag}.log"): log("BUILD FAIL " + tag); sys.exit(1)
    if os.path.exists(work + "/run_baked.vvp") and os.environ.get("KEEP_RB") != "1": os.remove(work + "/run_baked.vvp")
if not os.path.exists(work + "/audit.vvp"):
    subprocess.run(f"cd {work} && python3 {J}/mkvh.py routed.json judge.vh && cp {J}/tb_audit.v .", shell=True, check=True)
    if heavy(f"cd {work} && iverilog -gspecify -DGLS_TRANSPORT_IC -DGLS_FID -I{GLS} -I. -o audit.vvp tb_audit.v netlist_baked.v {GLS}/prims.v 2>&1 | grep -v 'procedural continuous'; test -f audit.vvp", f"{work}/audit_compile.log"):
        log("AUDIT COMPILE FAIL " + tag); sys.exit(1)
os.makedirs(work + "/ajlog", exist_ok=True)
ts = []
for v in vecs:
    t = threading.Thread(target=heavy, args=(f"cd {work} && vvp audit.vvp +VEC={v} +TEND={TEND} +QUIET=200000", f"{work}/ajlog/v{v}.log")); t.start(); ts.append(t); time.sleep(1)
for t in ts: t.join()
subprocess.run(f"python3 {J}/check.py {J}/oracle_C.txt {work}/ajlog {' '.join(map(str,vecs))} > {A}/judge_{tag}.txt 2>&1", shell=True)
os.remove(work + "/audit.vvp") if os.environ.get("KEEP_VVP") != "1" else None
log("DONE " + tag)
