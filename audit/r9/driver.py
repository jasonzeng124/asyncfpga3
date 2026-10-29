#!/usr/bin/env python3
"""Audit r9 job driver (from audit/r8/bq3/driver.py) (copy of audit/r7/driver.py, paths changed): at most 2 heavy (iverilog/vvp) jobs at once. Logs to audit/r9/driver.log."""
import subprocess, threading, os, time, sys
R7 = "/home/user/asyncfpga3/audit/r9"; J = "/home/user/asyncfpga3/audit/r7/judge"
sem = threading.Semaphore(2); lk = threading.Lock()
def log(s):
    with lk:
        open(R7 + "/driver.log", "a").write(time.strftime("%H:%M:%S ") + s + "\n")
def heavy(cmd, out):
    with sem:
        log("START " + cmd)
        rc = subprocess.run(cmd, shell=True, stdout=open(out, "w"), stderr=subprocess.STDOUT, executable="/bin/bash").returncode
        log("END rc=%d %s" % (rc, cmd))
        return rc
def compile_audit(work, GLS):
    subprocess.run(f"cd {work} && python3 {J}/mkvh.py routed.json judge.vh && cp {J}/tb_audit.v .", shell=True, check=True)
    return heavy(f"cd {work} && iverilog -gspecify -DGLS_TRANSPORT_IC -DGLS_FID -I{GLS} -I. -o audit.vvp tb_audit.v netlist_baked.v {GLS}/prims.v 2>&1 | grep -v 'procedural continuous'; test -f audit.vvp",
                 f"{work}/audit_compile.log")
def run_vecs(work, tag):
    os.makedirs(f"{work}/ajlog", exist_ok=True)
    ts = []
    for v in range(16):
        t = threading.Thread(target=heavy, args=(f"cd {work} && vvp audit.vvp +VEC={v} +TEND=150000 +QUIET=200000", f"{work}/ajlog/v{v}.log"))
        t.start(); ts.append(t); time.sleep(1)
    for t in ts: t.join()
    log("DONE vectors " + tag)
def pipeline(hw, work, col, tag):
    wt = hw.split("/cells/")[0]; GLS = wt + "/cells/gls"
    if not os.path.exists(f"{work}/run_baked.vvp"):
        if heavy(f"{R7}/fid_build.sh {wt} {hw} {work} {col}", f"{R7}/{tag}_build.log"):
            log("BUILD FAIL " + tag); return
    if compile_audit(work, GLS): log("AUDIT COMPILE FAIL " + tag); return
    run_vecs(work, tag)
jobs = [(sys.argv[i], sys.argv[i+1], sys.argv[i+2], sys.argv[i+3]) for i in range(1, len(sys.argv), 4)]
# serialize pipelines by priority but let them overlap through the semaphore
ths = []
for j in jobs:
    t = threading.Thread(target=pipeline, args=j); t.start(); ths.append(t); time.sleep(2)
for t in ths: t.join()
log("ALL DONE")
