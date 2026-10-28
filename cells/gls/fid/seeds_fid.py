#!/usr/bin/env python3
"""Full board-fidelity stack over several placer seeds of one gcd_hw recipe.

    python3 cells/gls/fid/seeds_fid.py OUTDIR --seeds d,3,4 [--cols min,max]
            [--scatter REGION:WIRE:DRAW,...] [--route-jobs 3] [--sim-jobs 3]
            [--env K=V ...]

For each seed (d = no NEXTPNR_SEED): a git worktree at OUTDIR/wt-<seed> of the
current HEAD, `hw/build_hw.sh gcd_hw` there with --env (the BQ recipe) and
NEXTPNR_SEED, then xray_delay.py's prjxray SDF of that route, then, per column
(and per scatter draw), build_fid.sh from the .bit with GLS_MODEL=fid and
run_fid.sh -j1.  Each sim is one vvp (~3.1 GB RSS; its compile ~3.7 GB), so
--sim-jobs bounds memory.  A run whose log lacks a verdict line for any vector
is reported INCOMPLETE, never as a pass (an OOM kill truncates silently).

Writes OUTDIR/results.tsv (one row per run) and OUTDIR/<seed>/... logs.
Does not touch git beyond `git worktree add` (detached).
"""
import argparse, os, re, subprocess, sys, threading, hashlib
from concurrent.futures import ThreadPoolExecutor

REPO = os.path.abspath(os.path.join(os.path.dirname(__file__), "../../.."))
TC = os.environ.get("TC", os.path.expanduser("~/dev2/lib/fpgatoolchain"))
PRJXRAY = os.path.join(TC, "openxc7-src/prjxray")
lock = threading.Lock()


def md5(p):
    return hashlib.md5(open(p, "rb").read()).hexdigest()[:8]


def sh(cmd, log, env=None, cwd=None):
    with open(log, "a") as f:
        f.write("$ " + cmd + "\n"); f.flush()
        r = subprocess.run(cmd, shell=True, stdout=f, stderr=subprocess.STDOUT,
                           env=env, cwd=cwd, executable="/bin/bash")
    return r.returncode


def route(a, seed):
    wt = os.path.join(a.out, "wt-" + seed)
    log = os.path.join(a.out, seed, "route.log")
    os.makedirs(os.path.dirname(log), exist_ok=True)
    hw = os.path.join(wt, "cells/build/hw/gcd_hw")
    if os.path.exists(os.path.join(hw, "gcd_hw.bit")):
        return hw
    if not os.path.isdir(wt):
        with lock:
            if sh(f"git -C {REPO} worktree add --detach {wt} HEAD", log):
                raise RuntimeError("worktree " + seed)
    env = dict(os.environ)
    for kv in a.env:
        k, v = kv.split("=", 1)
        env[k] = v.replace("@WT", wt)
    env.pop("NEXTPNR_SEED", None)
    if seed != "d":
        env["NEXTPNR_SEED"] = seed
    if sh("./hw/build_hw.sh gcd_hw", log, env=env, cwd=os.path.join(wt, "cells")):
        raise RuntimeError("build_hw failed for seed " + seed)
    xs = os.path.join(hw, "gcd_hw_xray.sdf")
    env2 = dict(os.environ, PYTHONPATH=PRJXRAY)
    if sh(f"python3 {REPO}/cells/gls/fid/xray_delay.py --routed {hw}/gcd_hw_routed.json "
          f"--sdf {hw}/gcd_hw.sdf --out {xs}", log, env=env2):
        raise RuntimeError("xray_delay failed for seed " + seed)
    return hw


def sim(a, seed, hw, col, scat):
    tag = col + ("" if scat is None else "_s" + scat.replace(":", "-"))
    work = os.path.join(a.out, seed, tag)
    log = os.path.join(a.out, seed, tag + ".log")
    env = dict(os.environ, GLS_SDF=os.path.join(hw, "gcd_hw_xray.sdf"),
               GLS_SDF_FIELD=col, GLS_MODEL="fid", PYTHONPATH=PRJXRAY)
    if scat is not None:
        reg, wire, draw = scat.split(":")
        env.update(GLS_SCATTER_REGION=reg, GLS_SCATTER=wire,
                   GLS_SCATTER_MODE="wire", GLS_SCATTER_SEED=draw)
    rc = sh(f"{REPO}/cells/gls/fid/build_fid.sh {hw} {work} bit", log, env=env)
    if rc == 0:
        sh(f"{REPO}/cells/gls/fid/run_fid.sh {work} -j1", log, env=env)
    done = errs = 0; dead = []; incomplete = []; laps = {}; kinds = set()
    for v in range(16):
        f = os.path.join(work, "sweep", f"v{v}.log")
        t = open(f).read() if os.path.exists(f) else ""
        m = re.search(r"SUMMARY vec=\d+ laps=(\d+) errs=(\d+)", t)
        k = re.search(r"RESULT (\S+?):", t)
        if not m or not k:
            incomplete.append(str(v)); continue
        kinds.add(k.group(1))
        laps[str(v)] = int(m.group(1)); errs += int(m.group(2))
        if int(m.group(1)) > 0 and k.group(1) == "timeout":
            done += 1
        else:
            dead.append(str(v))
    verdict = ("BUILD_FAIL" if rc else "INCOMPLETE" if incomplete
               else "PASS" if done == 16 and errs == 0 else "FAIL")
    row = [seed, tag, md5(os.path.join(hw, "gcd_hw.sdf")), md5(os.path.join(hw, "gcd_hw_xray.sdf")),
           verdict, f"{done}/16", str(errs), "/".join(str(laps.get(v, "?")) for v in ("6", "12", "13")),
           ",".join(dead) or "-", ",".join(incomplete) or "-"]
    with lock:
        with open(os.path.join(a.out, "results.tsv"), "a") as f:
            f.write("\t".join(row) + "\n")
    print("\t".join(row), flush=True)


def main():
    p = argparse.ArgumentParser()
    p.add_argument("out")
    p.add_argument("--seeds", required=True)
    p.add_argument("--cols", default="min,max")
    p.add_argument("--scatter", default="")
    p.add_argument("--route-jobs", type=int, default=3)
    p.add_argument("--sim-jobs", type=int, default=3)
    p.add_argument("--env", nargs="*", default=[])
    a = p.parse_args()
    a.out = os.path.abspath(a.out); os.makedirs(a.out, exist_ok=True)
    seeds = a.seeds.split(",")
    sims = ThreadPoolExecutor(a.sim_jobs)
    futs = []

    def one(seed):
        try:
            hw = route(a, seed)
        except Exception as e:
            print(f"{seed}\tROUTE_FAIL\t{e}", flush=True); return
        for col in a.cols.split(","):
            futs.append(sims.submit(sim, a, seed, hw, col, None))
        for sc in filter(None, a.scatter.split(",")):
            col, rest = sc.split("@") if "@" in sc else ("band", sc)
            futs.append(sims.submit(sim, a, seed, hw, col, rest))

    with ThreadPoolExecutor(a.route_jobs) as rp:
        list(rp.map(one, seeds))
    for f in list(futs):
        f.result()
    sims.shutdown()


if __name__ == "__main__":
    main()
