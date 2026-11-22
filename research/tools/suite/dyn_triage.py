#!/usr/bin/env python3
"""Triage Dynamatic's integration tests through this compiler, without routing.

    python3 research/tools/suite/dyn_triage.py OUTDIR [test ...]

For every test (default: every directory of dynamatic/integration-test, in sorted order) it runs, from the repo root:

  1. ./bdc/frontend.sh <name>                         -> frontend ok?, first error line verbatim
  2. python3 bdc/emit.py <hs.mlir> --no-top -o OUTDIR/emit/<name>.v          (environment with every BDC_* removed)
     BDC_AUTO=1 python3 bdc/emit.py ... -o OUTDIR/emit/<name>.auto.v         -> ok?, the exception line verbatim
  3. the post-frontend signature (bdc/hs/parse.py on handshake_transformed.mlir): args, results, memrefs
  4. for every test whose default emit is OK: python3 cells/hw/gen_bench.py <name> -o OUTDIR/bench/<name>_bench_gen.v
     (run from OUTDIR/genwd/<name>, whose build/gen/ holds the emitted kernel, where gen_bench.py reads its delay
     parameters; cells/build/gen is never written), then a yosys elaboration of bench + kernel + cells/rtl
     (read_verilog; hierarchy -check -top; no synthesis, no routing): does the generated bench connect to the kernel?

The bench ABI (cells/hw/gen_bench.py: MAX_WORDS = 2 operand words; one 32-bit out0; start/end control) is checked
here from the signature, independently of gen_bench.py, because gen_bench.py itself checks only the operand words
(see research/data/suite/dyn/README.md: it accepts memref arguments as 0 words and never looks at the result).

Writes OUTDIR/triage.tsv (one row per test) and OUTDIR/logs/<name>.{fe,emit,auto,bench,lint}.log.
Nothing here names a test; nothing is routed; nothing under dynamatic/ is touched.
"""
import json
import os
import re
import shutil
import subprocess
import sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "bdc"))
from hs import parse  # noqa: E402

ITEST = os.path.join(ROOT, "dynamatic", "integration-test")
MAX_WORDS = 2


def clean_env(**extra):
    env = {k: v for k, v in os.environ.items() if not k.startswith("BDC_")}
    env.update(extra)
    return env


def run(cmd, log, env=None, cwd=ROOT, timeout=900):
    with open(log, "w") as f:
        try:
            p = subprocess.run(cmd, cwd=cwd, env=env or clean_env(), stdout=f, stderr=subprocess.STDOUT,
                               timeout=timeout)
            return p.returncode
        except subprocess.TimeoutExpired:
            f.write(f"\nTIMEOUT after {timeout} s\n")
            return 124


def first_error(log):
    lines = open(log, errors="replace").read().splitlines()
    for l in lines:
        if l.startswith("== "):
            continue
        if re.search(r"\berror\b", l, re.I):
            return l.strip()
    for l in lines:
        if l.startswith("FAILED at step") or l.startswith("no such kernel source"):
            return l.strip()
    return (lines[-1].strip() if lines else "(empty log)")


def exc_line(log):
    """The exception a Python tool died with: the last line that looks like `SomeError: ...`, verbatim."""
    lines = open(log, errors="replace").read().splitlines()
    for l in reversed(lines):
        if re.match(r"^[A-Za-z_][\w.]*(Error|Exception|Unmapped|Exit)\b.*:", l) or l.startswith("AssertionError"):
            return l.strip()
    return (lines[-1].strip() if lines else "(empty log)")


def signature(mlir):
    funcs = [f for f in parse.parse_module(open(mlir).read(), filename=mlir) if not f.is_declaration]
    f = funcs[0]
    args = []
    for a in f.args:
        if a.raw.startswith("memref"):
            args.append(("memref", a.name, a.raw))
        elif a.is_control:
            args.append(("ctrl", a.name, 0))
        else:
            args.append(("data", a.name, a.width))
    res = [("ctrl" if r.is_control else "data", r.name, r.width) for r in f.results]
    return f.name, args, res


def abi(args, res):
    """(fits, why) for the bench ABI, from the signature alone."""
    why = []
    mem = [a for a in args if a[0] == "memref"]
    data = [a for a in args if a[0] == "data"]
    if mem:
        why.append(f"{len(mem)} memref arg(s)")
    odd = [a for a in data if a[2] % 32]
    if odd:
        why.append("arg width(s) " + ",".join(f"{a[1]}:i{a[2]}" for a in odd) + " not a multiple of 32")
    words = sum(max(1, a[2] // 32) for a in data)
    if words > MAX_WORDS:
        why.append(f"{words} operand words > {MAX_WORDS}")
    dres = [r for r in res if r[0] == "data"]
    if len(dres) != 1:
        why.append(f"{len(dres)} data result(s), the bench reads exactly one")
    elif dres[0][2] != 32:
        why.append(f"result {dres[0][1]}:i{dres[0][2]}, the bench reads i32")
    return (not why), "; ".join(why)


def tests(argv):
    if argv:
        return argv
    return sorted(d for d in os.listdir(ITEST) if os.path.isdir(os.path.join(ITEST, d)))


def main():
    out = os.path.abspath(sys.argv[1])
    names = tests(sys.argv[2:])
    for sub in ("emit", "logs", "bench"):
        os.makedirs(os.path.join(out, sub), exist_ok=True)
    tc = os.environ.get("TC", os.path.expanduser("~/dev2/lib/fpgatoolchain"))
    yosys = os.path.join(tc, "openxc7", "bin", "yosys")
    cells_sim = os.path.join(tc, "openxc7", "share", "yosys", "xilinx", "cells_sim.v")
    cells_xtra = os.path.join(tc, "openxc7", "share", "yosys", "xilinx", "cells_xtra.v")
    rows = []
    for name in names:
        L = lambda k: os.path.join(out, "logs", f"{name}.{k}.log")
        row = {"name": name}
        rc = run(["./bdc/frontend.sh", name], L("fe"))
        row["fe"] = "ok" if rc == 0 else "FAIL"
        row["fe_err"] = "" if rc == 0 else first_error(L("fe"))
        mlir = os.path.join(ROOT, "build", "frontend", name, "comp", "handshake_transformed.mlir")
        if rc == 0:
            try:
                fname, args, res = signature(mlir)
                row["args"] = " ".join(f"{a[1]}:{a[2] if a[0] == 'memref' else ('i%d' % a[2] if a[0] == 'data' else 'ctrl')}"
                                       for a in args)
                row["results"] = " ".join(f"{r[1]}:{'i%d' % r[2] if r[0] == 'data' else 'ctrl'}" for r in res)
                fits, why = abi(args, res)
                row["abi"] = "fits" if fits else "no"
                row["abi_why"] = why
            except Exception as e:  # a parse failure is a result too
                row["args"] = row["results"] = ""
                row["abi"], row["abi_why"] = "?", f"parse: {type(e).__name__}: {e}"
            for tag, env, suffix in (("emit", clean_env(), ".v"), ("auto", clean_env(BDC_AUTO="1"), ".auto.v")):
                vout = os.path.join(out, "emit", name + suffix)
                if os.path.exists(vout):
                    os.remove(vout)
                rc2 = run([sys.executable, "bdc/emit.py", mlir, "--no-top", "-o", vout], L(tag), env=env)
                ok = rc2 == 0 and os.path.exists(vout)
                row[tag] = "ok" if ok else "FAIL"
                row[tag + "_err"] = "" if ok else exc_line(L(tag))
            if row["emit"] == "ok":
                # gen_bench.py reads the kernel's delay parameters from cells/build/gen/<name>_kernel_bench.v, else
                # from ./build/gen/ relative to its working directory.  Never write into cells/build/gen (a real
                # build's file may be there): run it from OUTDIR/genwd/<name>, holding the kernel just emitted.
                # If cells/build/gen already has a DIFFERENT file for this name, gen_bench.py would read that one,
                # so the elaboration below would not be testing this emit: say so instead of checking.
                wd = os.path.join(out, "genwd", name)
                os.makedirs(os.path.join(wd, "build", "gen"), exist_ok=True)
                kfile = os.path.join(wd, "build", "gen", f"{name}_kernel_bench.v")
                shutil.copy(os.path.join(out, "emit", name + ".v"), kfile)
                theirs = os.path.join(ROOT, "cells", "build", "gen", f"{name}_kernel_bench.v")
                shadowed = os.path.exists(theirs) and open(theirs).read() != open(kfile).read()
                bv = os.path.join(out, "bench", f"{name}_bench_gen.v")
                if os.path.exists(bv):
                    os.remove(bv)
                rc3 = run([sys.executable, os.path.join(ROOT, "cells", "hw", "gen_bench.py"), name, "--top",
                           f"{name}_bench_gen", "-o", bv], L("bench"), cwd=wd)
                row["gen_bench"] = "ok" if rc3 == 0 and os.path.exists(bv) else "FAIL"
                row["gen_bench_err"] = "" if row["gen_bench"] == "ok" else exc_line(L("bench"))
                if row["gen_bench"] == "ok" and shadowed:
                    row["lint"], row["lint_err"] = "skipped", f"{theirs} exists and differs from this emit"
                elif row["gen_bench"] == "ok":
                    rtl = sorted(os.path.join(ROOT, "cells", "rtl", f) for f in os.listdir(os.path.join(ROOT, "cells", "rtl"))
                                 if f.endswith(".v"))
                    script = (f"read_verilog -lib -specify {cells_sim}; read_verilog -lib {cells_xtra}; "
                              f"read_verilog {' '.join(rtl)} {kfile} {bv}; hierarchy -check -top {name}_bench_gen")
                    rc4 = run([yosys, "-q", "-p", script], L("lint"))
                    txt = open(L("lint"), errors="replace").read()
                    warn = sorted(set(re.findall(r"(Resizing cell port [^\n]*|[^\n]*does not have a port[^\n]*)", txt)))
                    row["lint"] = "ok" if rc4 == 0 and not warn else "FAIL"
                    row["lint_err"] = "" if row["lint"] == "ok" else (first_error(L("lint")) if rc4 else warn[0])
        rows.append(row)
        print("\t".join(str(row.get(k, "")) for k in ("name", "fe", "emit", "auto", "abi", "gen_bench", "lint")),
              flush=True)
    cols = ["name", "fe", "fe_err", "args", "results", "emit", "emit_err", "auto", "auto_err", "abi", "abi_why",
            "gen_bench", "gen_bench_err", "lint", "lint_err"]
    with open(os.path.join(out, "triage.tsv"), "w") as f:
        f.write("\t".join(cols) + "\n")
        for r in rows:
            f.write("\t".join(str(r.get(c, "")).replace("\t", " ") for c in cols) + "\n")
    json.dump(rows, open(os.path.join(out, "triage.json"), "w"), indent=1)


if __name__ == "__main__":
    main()
