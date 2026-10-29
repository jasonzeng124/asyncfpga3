#!/usr/bin/env python3
"""Mutant sweep for autoproof (probe C-vk2): every operand swap of every two-operand op.

    python3 sweep.py KERNEL [--only NAME,...] [--no-lean] [--out DIR]

For each MLIR op of the kernel with two data operands (addi subi muli andi ori xori shli
shrsi shrui; mutate.py cannot swap `cmpi` operands), formal/tools/verify/mutate.py swaps its operands. A swap of a
commutative op (addi muli andi ori xori), and gcd's subi0 (EQUIV_EXTRA), is an EQUIVALENT mutant: autoproof must
PROVE it (Lean checks the generated graph + segments + proof in one file). Any other swap
changes the function unless the operands happen to be equal: autoproof must NOT prove it
(a counterexample or a refusal; if Lean were to accept one, the sweep reports it as WRONG).

Prints one line per mutant: name, op, expected (equiv / real), autoproof verdict, Lean verdict.
"""
import argparse
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "formal", "tools", "verify"))
from kernels import KERNELS  # noqa: E402

COMM = {"addi", "muli", "andi", "ori", "xori"}
# non-commutative swaps that are nevertheless equivalent, with the reason
EQUIV_EXTRA = {("gcd", "subi0"): "|b - a| = |a - b|: subi0 only feeds the absolute value"}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("kernel")
    ap.add_argument("--only", default="")
    ap.add_argument("--no-lean", action="store_true")
    ap.add_argument("--out", default=os.path.join(ROOT, "build", "autoproof", "sweep"))
    a = ap.parse_args()
    k = KERNELS[a.kernel]
    fix = os.path.join(ROOT, "cloud", "fixtures", "frontend", k["mlir"], "comp", "handshake_transformed.mlir")
    cfile = os.path.join(ROOT, k.get("autoc") or k["c"])
    os.makedirs(a.out, exist_ok=True)
    ops = []
    for l in open(fix):
        m = re.match(r"^\s*%\S+\s*=\s*(\w+)\s+%[\w#]+,\s*%[\w#]+.*handshake.name = \"(\w+)\"", l)
        if m and m.group(1) in COMM | {"subi", "shli", "shrsi", "shrui", "cmpi"}:
            pred = re.search(r"cmpi (\w+),", l)
            ops.append((m.group(2), m.group(1) + (f" {pred.group(1)}" if pred else "")))
    only = set(a.only.split(",")) if a.only else None
    wrong = 0
    for name, op in ops:
        if only and name not in only:
            continue
        kind = op.split()[0]
        equiv = kind in COMM or op in ("cmpi eq", "cmpi ne") or (a.kernel, name) in EQUIV_EXTRA
        mut = os.path.join(a.out, f"{a.kernel}_{name}.mlir")
        subprocess.run([sys.executable, os.path.join(ROOT, "formal/tools/verify/mutate.py"), fix, mut,
                        "--swap", name], check=True, capture_output=True)
        nm = f"Sw{a.kernel.capitalize()}{name.capitalize()}"
        gns = f"Formal.Net.Auto{nm}G"
        out = os.path.join(a.out, f"Auto{nm}.lean")
        r = subprocess.run([sys.executable, os.path.join(HERE, "autoproof.py"), mut, cfile, k["func"],
                            "--name", nm, "--graph-ns", gns, "--combined", out,
                            "--dfargs", f"--ns {gns} --graph-module X --label {name} --short {a.kernel}"],
                           capture_output=True, text=True)
        av = {0: "lean-file", 1: "COUNTEREXAMPLE", 2: "refused"}.get(r.returncode, f"error {r.returncode}")
        why = [l for l in r.stdout.split("\n") if l.startswith("AUTOPROOF")]
        lv = "-"
        if r.returncode == 0 and not a.no_lean:
            with open(out, "a") as f:
                f.write(f"\n#print axioms Formal.Net.Auto{nm}.auto_computes\n")
            lr = subprocess.run([os.path.join(ROOT, "formal", "slot.sh"), "lake", "env", "lean", out],
                                capture_output=True, text=True)
            log = lr.stdout + lr.stderr
            ok = lr.returncode == 0 and ": error" not in log and "sorry" not in log
            m = re.search(r"depends on axioms: \[([^\]]*)\]", log)
            axs = set(x.strip() for x in m.group(1).split(",")) if m else {"?"}
            ok = ok and axs <= {"propext", "Classical.choice", "Quot.sound"}
            lv = "PROVED" if ok else "rejected"
            open(out + ".log", "w").write(log)
        proved = lv == "PROVED"
        good = (proved if equiv else not proved) if not a.no_lean else (
            r.returncode == 0 if equiv else r.returncode != 0)
        # a non-commutative swap whose operands are equal on every run is equivalent too: report
        note = "" if good else "  <-- WRONG"
        if not good and not equiv and proved:
            note = "  <-- PROVED a swap of a non-commutative op: check whether its operands are always equal"
        wrong += 0 if good else 1
        print(f"{name:10s} {op:10s} {'equiv' if equiv else 'real ':5s}  autoproof: {av:14s} lean: {lv:8s}"
              f"{('  (' + why[0][:110] + ')') if why else ''}{note}", flush=True)
    print(f"sweep {a.kernel}: {'OK' if not wrong else f'{wrong} WRONG'}")
    return 1 if wrong else 0


if __name__ == "__main__":
    sys.exit(main())
