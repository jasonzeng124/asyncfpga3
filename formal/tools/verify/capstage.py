#!/usr/bin/env python3
"""Stage 3 of verify.sh: the circuit-level capstone (probe C-vk).

    python3 capstage.py KERNEL MLIR OUTDIR

1. If formal/tools/capnet/capnet.py (C-8y; called, never edited) has a PROFILE for the
   kernel, regenerate the circuit network files (links, ring, net) FROM THE GIVEN MLIR
   (capnet reads only the committed fixture, so its `kernel_mlir` is redirected in-process)
   and compare them with the committed Formal/Net files the circuit proof is about.
   Different = the committed circuit proof is not about this design: FAIL.
2. If identical: the proof's module must be up to date (`lake build --no-build MOD`;
   with VERIFY_LAKE_BUILD=1 it is built, targeted) and its main theorem's axioms are
   audited with a one-line Lean file.
Prints `CAP PASS|FAIL|SKIP: ...`. Exit 0 PASS, 1 FAIL, 3 SKIP.
"""
import difflib
import io
import os
import subprocess
import sys
import contextlib

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
NET = os.path.join(ROOT, "formal", "lean", "Formal", "Net")
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(ROOT, "formal", "tools", "capnet"))
from kernels import KERNELS  # noqa: E402

AXIOMS_OK = {"propext", "Classical.choice", "Quot.sound"}


def main():
    kname, mlir, outdir = sys.argv[1], os.path.abspath(sys.argv[2]), sys.argv[3]
    k = KERNELS[kname]
    cap = k.get("capstone")
    try:
        import capnet
    except Exception as e:  # noqa: BLE001
        print(f"CAP SKIP: capnet.py does not import ({e})")
        return 3
    if not cap or cap["profile"] not in capnet.PROFILES:
        print(f"CAP SKIP: no circuit-level generator for {kname} (capnet PROFILES: "
              f"{', '.join(sorted(capnet.PROFILES))}; verify's kernels.py capstone: {'set' if cap else 'none'})")
        return 3
    os.makedirs(outdir, exist_ok=True)
    capnet.kernel_mlir = lambda _k: mlir
    drift = []
    for what, committed in cap["gen"]:
        out = os.path.join(outdir, committed)
        sys.argv = ["capnet.py", "--kernel", cap["profile"]] + (["--gcd-compat"] if cap.get("compat") else []) + \
                   [what, "-o", out]
        with contextlib.redirect_stderr(io.StringIO()):
            try:
                capnet.main()
            except SystemExit as e:
                if e.code not in (None, 0):
                    print(f"CAP FAIL: capnet {what} refused this design: {e}")
                    return 1
        new, old = open(out).read(), open(os.path.join(NET, committed)).read()
        if new != old:
            d = list(difflib.unified_diff(old.split("\n"), new.split("\n"), committed, "regenerated", n=0, lineterm=""))
            drift.append((committed, d))
            print(f"  capnet {what}: DIFFERS from committed {committed} ({len(d)} diff lines)")
        else:
            print(f"  capnet {what}: identical to committed {committed}")
    if drift:
        for f, d in drift[:2]:
            for l in d[2:8]:
                print("     ", l[:200])
        print(f"CAP FAIL: the circuit network of this MLIR is not the one {cap['theorem']} is about "
              "(re-instantiating the circuit proof for a new network is not automated: capnet/instantiate.py "
              "copies the gcd proof files with renames, then Lean must re-check them)")
        return 1
    lean = os.path.join(ROOT, "formal", "lean")
    slot = os.path.join(ROOT, "formal", "slot.sh")
    r = subprocess.run([slot, "lake", "build", "--no-build", cap["module"]], capture_output=True, text=True)
    if r.returncode != 0:
        if os.environ.get("VERIFY_LAKE_BUILD") == "1":
            r = subprocess.run([slot, "lake", "build", cap["module"]], capture_output=True, text=True)
            if r.returncode != 0:
                print(f"CAP FAIL: lake build {cap['module']} failed:\n" + (r.stdout + r.stderr)[-1500:])
                return 1
        else:
            print(f"CAP SKIP: network identical, but {cap['module']} is not built/up to date "
                  "(rerun with VERIFY_LAKE_BUILD=1 for a targeted build)")
            return 3
    f = os.path.join(outdir, "CapAxioms.lean")
    open(f, "w").write(f"import {cap['module']}\n#print axioms {cap['theorem']}\n")
    r = subprocess.run([slot, "lake", "env", "lean", os.path.abspath(f)], capture_output=True, text=True,
                       cwd=lean)
    log = r.stdout + r.stderr
    import re
    m = re.search(r"depends on axioms: \[([^\]]*)\]", log)
    axs = {x.strip() for x in m.group(1).split(",")} if m else None
    if r.returncode != 0 or axs is None or not axs <= AXIOMS_OK:
        print(f"CAP FAIL: axiom audit of {cap['theorem']}: {log.strip()[:600]}")
        return 1
    print(f"CAP PASS: network regenerated from this MLIR == committed; {cap['module']} up to date; "
          f"{cap['theorem']} axioms {sorted(axs)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
