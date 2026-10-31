#!/usr/bin/env python3
"""Stage 4 of verify.sh: the verified timing checker (tcheck, C-10e..) on a route (probe C-vk).

    python3 tstage.py ROUTE [ROUTE ...] [--max-rows N]

ROUTE is one of
  * an obligation file `*.tc` / `*.tc.gz` (e.g. kcheck's build/<k>/s<seed>/check/obl.tc.gz),
  * a kcheck seed directory (uses its check/obl.tc.gz),
  * a nextpnr output directory holding soak.sdf, soak_routed.json, soak.fasm: the
    obligations are extracted first with formal/tools/tcheck/extract.py (the worktree front
    end, `--rules2 AEFJWR --cert`, as kcheck runs it; UNTRUSTED, see the note).
The compiled checker is a snapshot of formal/tools/tcheck built through slot.sh into
$VERIFY_BUILD (default <repo>/build/verify), after `sync.sh --check` (the proved modules
are verbatim copies) and its two self-tests.

Every FAIL / ILLFORMED / CERTBAD row is printed as the counterexample: its verdict line,
then (for plain arc instances) the path that gives the request its EARLIEST change and
the path that gives a data node its LATEST change, arc by arc with each [lo, hi] interval
(ps); the obligation is violated because data_late + setup > req_early along exactly these
arcs. extract.py's per-obligation metadata (obl.json) is printed when present.
Exit 0 all rows PASS, 1 some row fails, 3 nothing to check.
"""
import argparse
import gzip
import json
import os
import re
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
TC = os.path.join(ROOT, "formal", "tools", "tcheck")
BUILD = os.environ.get("VERIFY_BUILD", os.path.join(ROOT, "build", "verify"))


def tcheck_exe():
    snap = os.path.join(BUILD, "tcheck_snap")
    exe = os.path.join(snap, ".lake", "build", "bin", "tcheck")
    r = subprocess.run([os.path.join(TC, "sync.sh"), "--check"], capture_output=True, text=True)
    if r.returncode != 0:
        raise SystemExit("tcheck sync.sh --check: DRIFT (the checker's proved modules differ from formal/lean)\n" + r.stdout)
    want = subprocess.run("cat Main.lean Tcheck/*.lean Formal/*/*.lean | sha256sum", shell=True, cwd=TC,
                          capture_output=True, text=True).stdout.split()[0]
    stamp = os.path.join(snap, "SOURCE_SHA256")
    if not (os.path.exists(exe) and os.path.exists(stamp) and open(stamp).read().strip() == want):
        shutil.rmtree(snap, ignore_errors=True)
        os.makedirs(snap)
        for x in ["lakefile.toml", "lean-toolchain", "lake-manifest.json", "Main.lean", "Tcheck", "Formal", "test"]:
            s = os.path.join(TC, x)
            (shutil.copytree if os.path.isdir(s) else shutil.copy)(s, os.path.join(snap, x))
        env = dict(os.environ, FORMAL_SLOT_CWD=snap)
        r = subprocess.run([os.path.join(ROOT, "formal", "slot.sh"), "lake", "build"], cwd=snap, env=env,
                           capture_output=True, text=True)
        if r.returncode != 0 or not os.path.exists(exe):
            raise SystemExit("tcheck snapshot build failed:\n" + (r.stdout + r.stderr)[-2000:])
        open(stamp, "w").write(want + "\n")
    for t in ["toy", "toycert"]:
        out = subprocess.run([exe, os.path.join(snap, "test", f"{t}.tc")], capture_output=True, text=True).stdout
        if out != open(os.path.join(snap, "test", f"{t}.expected")).read():
            raise SystemExit(f"tcheck self-test {t} FAILED")
    return exe, want[:16]


def resolve(route, workdir):
    """-> (tc path, json path or None, description)."""
    if os.path.isfile(route):
        j = os.path.join(os.path.dirname(route), "obl.json")
        return route, (j if os.path.exists(j) else None), route
    for c in [os.path.join(route, "check", "obl.tc.gz"), os.path.join(route, "check", "obl.tc"),
              os.path.join(route, "obl.tc.gz"), os.path.join(route, "obl.tc")]:
        if os.path.exists(c):
            j = os.path.join(os.path.dirname(c), "obl.json")
            return c, (j if os.path.exists(j) else None), c
    pnr = route if os.path.exists(os.path.join(route, "soak.sdf")) else os.path.join(route, "pnr")
    if os.path.exists(os.path.join(pnr, "soak.sdf")):
        os.makedirs(workdir, exist_ok=True)
        tc, js = os.path.join(workdir, "obl.tc"), os.path.join(workdir, "obl.json")
        r = subprocess.run([sys.executable, os.path.join(TC, "extract.py"), pnr, "soak",
                            "--cells", os.path.join(ROOT, "cells"), "--rules2", "AEFJWR", "--cert",
                            "--out", tc, "--json", js], capture_output=True, text=True)
        if r.returncode != 0:
            raise SystemExit(f"extract.py failed on {pnr}:\n{r.stderr[-1500:]}")
        return tc, js, f"{pnr} (extracted: {r.stderr.strip().splitlines()[-1] if r.stderr.strip() else ''})"
    raise SystemExit(f"{route}: no obl.tc(.gz) and no soak.sdf found")


VARIANTS = ("sdf", "sdfband", "fast", "slow", "fastG", "slowG")
VERDICT = ("fastG", "slowG", "-")


def variant(label):
    w = label.split()
    return next((x for x in reversed(w) if x in VARIANTS), "-")


def strip_variant(label):
    return " ".join(x for x in label.split() if x not in VARIANTS and not x.startswith("fallback="))


def read_insts(tc):
    op = gzip.open if tc.endswith(".gz") else open
    insts, cur = {}, None
    with op(tc, "rt") as f:
        for line in f:
            w = line.split()
            if not w:
                continue
            if w[0] == "inst":
                cur = {"label": line[5:].rstrip("\n"), "arcs": [], "data": [], "req": None, "setup": 0}
                insts[cur["label"]] = cur
            elif cur is None:
                continue
            elif w[0] == "arc":
                cur["arcs"].append(tuple(int(x) for x in w[1:5]))
            elif w[0] == "req":
                cur["req"] = int(w[1])
            elif w[0] == "data":
                cur["data"] += [int(x) for x in w[1:]]
            elif w[0] == "setup":
                cur["setup"] = int(w[1])
            elif w[0] == "end":
                cur = None
            else:
                cur.setdefault("other", set()).add(w[0])
    return insts


def explain(I, tag):
    lo, hi, plo, phi = {0: 0}, {0: 0}, {}, {}
    for a, b, l, h in sorted(I["arcs"]):
        if a in lo:
            if b not in lo or lo[a] + l < lo[b]:
                lo[b] = lo[a] + l
                plo[b] = (a, l, h)
            if b not in hi or hi[a] + h > hi[b]:
                hi[b] = hi[a] + h
                phi[b] = (a, l, h)

    def path(n, P):
        out = []
        while n in P:
            a, l, h = P[n]
            out.append((a, n, l, h))
            n = a
        return out[::-1]
    lines = []
    if I["req"] in lo:
        p = path(I["req"], plo)
        lines.append(f"      request node {I['req']} earliest change {lo[I['req']]} ps via {len(p)} arcs:")
        lines += [f"        arc {a:>5} -> {b:<5} [{l}, {h}] ps (takes lo)" for a, b, l, h in p]
    ds = [d for d in I["data"] if d in hi]
    if ds:
        d = max(ds, key=lambda x: hi[x])
        p = path(d, phi)
        lines.append(f"      data node {d} latest change {hi[d]} ps via {len(p)} arcs:")
        lines += [f"        arc {a:>5} -> {b:<5} [{l}, {h}] ps (takes hi)" for a, b, l, h in p]
        if I["req"] in lo and tag == "FAIL":
            lines.append(f"      violated by {hi[d] + I['setup'] - lo[I['req']]} ps: data_late {hi[d]} + setup "
                         f"{I['setup']} > req_early {lo[I['req']]}")
    if tag == "ILLFORMED":
        lines.append("      ILLFORMED: the instance is not a DAG in index order; the checker refuses it (front-end bug)")
    if I.get("other"):
        lines.append(f"      (instance also has {sorted(I['other'])} lines: a certificate instance; the late side "
                     "is a checked potential, so the arc path above is only indicative; see tcheck/diag.py)")
    return lines


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("routes", nargs="+")
    ap.add_argument("--max-rows", type=int, default=10)
    ap.add_argument("--workdir", default=os.path.join(BUILD, "tstage"))
    a = ap.parse_args()
    exe, sha = tcheck_exe()
    print(f"  tcheck snapshot {sha} (sync.sh --check ok, self-tests ok)")
    worst = 0
    for n, route in enumerate(a.routes):
        tc, js, desc = resolve(route, os.path.join(a.workdir, str(n)))
        op = gzip.open if tc.endswith(".gz") else open
        with op(tc, "rt") as f:
            r = subprocess.run([exe, "-"], stdin=f, capture_output=True, text=True)
        if r.returncode != 0:
            print(f"  {desc}: tcheck error: {r.stderr.strip()[-300:]}")
            worst = 1
            continue
        rows = [l.split("\t") for l in r.stdout.splitlines() if l.strip()]
        cnt = {}
        for x in rows:
            v = variant(x[0])
            cnt.setdefault(v, [0, 0])[0 if x[1] == "PASS" else 1] += 1
        print(f"  route {desc}: {len(rows)} rows; PASS/not-PASS per delay variant: " +
              ", ".join(f"{v} {p}/{f}" for v, (p, f) in sorted(cnt.items())))
        # the verdict (as kcheck): every row PASSes at fastG and slowG (one prjxray corner at a
        # time, times the project's guard band); rows of a .tc without variants count as verdict rows
        bad = [x for x in rows if len(x) > 1 and x[1] != "PASS" and variant(x[0]) in VERDICT]
        # strongest counterexamples first: rows that also fail at an UNGUARDED prjxray corner
        unguarded = {strip_variant(x[0]) for x in rows if len(x) > 1 and x[1] != "PASS"
                     and variant(x[0]) in ("fast", "slow")}
        # then rows with no SDF-fallback arcs (prjxray numbers only) before fallback-dominated ones
        def nfb(lab):
            m = re.search(r"fallback=(\d+)/", lab)
            return int(m.group(1)) if m else 0
        bad.sort(key=lambda x: (strip_variant(x[0]) not in unguarded, nfb(x[0]) > 0,
                                int(x[2]) if x[2].lstrip("-").isdigit() else 0))
        print(f"  verdict rows (fastG/slowG): {len(bad)} not PASS; of their obligations, "
              f"{len({strip_variant(x[0]) for x in bad} & unguarded)} also fail at an unguarded corner (fast/slow)")
        if not bad:
            continue
        worst = 1
        insts = read_insts(tc)
        meta = {}
        if js:
            try:
                for o in json.load(open(js)).get("obligations", []):
                    if isinstance(o, dict) and "label" in o:
                        meta[o["label"]] = o
            except Exception:  # noqa: BLE001
                pass
        for x in bad[:a.max_rows]:
            ug = " [also fails UNGUARDED]" if strip_variant(x[0]) in unguarded else " [band-only at this row]"
            fb = re.search(r"fallback=(\d+)/(\d+)", x[0])
            if fb and int(fb.group(1)) > 0:
                ug += (f" [{fb.group(1)}/{fb.group(2)} arcs use the SDF fallback band (H_FALLBACK_BAND; DSP48E1/"
                       "CARRY4/F7F8 nets): a front-end gap candidate, not a trusted counterexample]")
            print("    COUNTEREXAMPLE ROW  " + "  ".join(x) + (ug if variant(x[0]) != "-" else ""))
            I = insts.get(x[0])
            if I:
                for l in explain(I, x[1]):
                    print(l)
            m = next((v for k, v in meta.items() if x[0].startswith(k)), None)
            if m:
                print("      extract metadata: " + json.dumps(m)[:400])
        if len(bad) > a.max_rows:
            print(f"    ... {len(bad) - a.max_rows} more failing rows (--max-rows)")
    if not a.routes:
        return 3
    return worst


if __name__ == "__main__":
    sys.exit(main())
