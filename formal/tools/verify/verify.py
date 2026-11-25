#!/usr/bin/env python3
"""verify: one entry point from a kernel's handshake MLIR to proof-or-counterexample (probe C-vk).

    formal/tools/verify/verify.sh KERNEL [--mlir FILE] [--c FILE] [--vecs "a,b a,b"]
                                  [--route DIR_OR_TC ...] [--out DIR] [--no-lean] [--no-cap]

Stages (each prints PASS / FAIL / SKIP, what it proves and what it does not):
  1  import   dfimport (C-8i) exports the graph bdc emits; drift vs the committed Lean
  2a lean     the committed hand proof re-checked on the FRESH import (leanstage.py)
  2e auto     a GENERATED all-inputs proof, no hand proof (autostage.py -> formal/tools/autoproof)
  2b search   bounded explicit-state search of every schedule against the compiled C
              (tokensearch.py); prints a counterexample schedule on mismatch
  2d vectors  generated Lean theorems, one per vector, for ANY kernel (vecgen.py): every
              complete run ends with exactly the compiled C's value
  2c transcr  the Lean transcription of the C (`#eval`) vs the compiled C on the vectors
  2f auto-tr  the GENERATED transcription (stage 2e's kC, `#eval`) vs the compiled C on the vectors
  3  circuit  capnet (C-8y) regenerates the circuit network; the committed circuit proof
              covers it iff identical (capstage.py)
  4  timing   tcheck (C-10e) on the route(s); failing rows printed with their arcs (tstage.py)
Overall: PASS iff no stage refutes and stage 2a or 2e PASSes. Exit 0 PASS, 1 FAIL, 2 not proved.
"""
import argparse
import os
import re
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
NET = os.path.join(ROOT, "formal", "lean", "Formal", "Net")
sys.path.insert(0, HERE)
from kernels import KERNELS  # noqa: E402
from cref import c_reference  # noqa: E402

PY = sys.executable


def kernel_mlir(name):
    b = os.path.join(ROOT, f"build/frontend/{name}/comp/handshake_transformed.mlir")
    return b if os.path.exists(b) else os.path.join(ROOT, f"cloud/fixtures/frontend/{name}/comp/handshake_transformed.mlir")


def norm(text):
    return re.sub(r"^Source: `[^`]*`", "Source: <mlir>", text, flags=re.M)


def rel(p):
    p = os.path.abspath(p)
    return os.path.relpath(p, ROOT) if p.startswith(ROOT) else p


def run(cmd, **kw):
    r = subprocess.run(cmd, capture_output=True, text=True, **kw)
    return r.returncode, r.stdout + r.stderr


class Report:
    def __init__(self):
        self.rows = []

    def stage(self, name, verdict, proves, not_):
        self.rows.append((name, verdict))
        print(f"[{name}] {verdict}")
        print(f"    proves:       {proves}")
        print(f"    does NOT:     {not_}")
        sys.stdout.flush()


def indent(text, n=4):
    return "\n".join(" " * n + l for l in text.rstrip().split("\n"))


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("kernel", choices=sorted(KERNELS))
    ap.add_argument("--mlir")
    ap.add_argument("--c")
    ap.add_argument("--vecs")
    ap.add_argument("--route", action="append", default=[])
    ap.add_argument("--out")
    ap.add_argument("--no-lean", action="store_true")
    ap.add_argument("--no-cap", action="store_true")
    ap.add_argument("--no-auto", action="store_true", help="skip stage 2e (generated all-inputs proof)")
    ap.add_argument("--max-states", type=int, default=300000)
    a = ap.parse_args()
    k = KERNELS[a.kernel]
    mlir = os.path.abspath(a.mlir or kernel_mlir(k["mlir"]))
    cfile = os.path.abspath(a.c or os.path.join(ROOT, k["c"]))
    out = os.path.abspath(a.out or os.path.join(os.environ.get("VERIFY_BUILD", os.path.join(ROOT, "build", "verify")),
                                                 a.kernel + time.strftime("-%m%d%H%M%S")))
    os.makedirs(out, exist_ok=True)
    if a.vecs:
        vecs = [tuple(int(x) for x in v.split(",")) for v in a.vecs.split()]
    else:
        vecs = [v for v in k["vectors"] if k["domain"](v)]
    R = Report()
    print(f"verify {a.kernel}\n  MLIR      {rel(mlir)}\n  C ref     {rel(cfile)} : {k['func']}\n"
          f"  vectors   {' '.join(','.join(map(str, v)) for v in vecs)}\n  work dir  {rel(out)}\n")

    # ---- 1 import + drift -------------------------------------------------------------
    imp = os.path.join(out, "import")
    os.makedirs(imp, exist_ok=True)
    K = k["K"]
    env = {x: y for x, y in os.environ.items() if not x.startswith("BDC_")}
    rc, log = run([PY, os.path.join(ROOT, "formal/tools/dfimport/mlir2lean.py"), mlir,
                   "-o", os.path.join(imp, f"{K}.lean"), "--segments", os.path.join(imp, f"{K}Seg.lean"),
                   "--summary"] + (k["dfargs"] or []), env=env)
    if rc != 0:
        R.stage("1 import", "FAIL", "-", "dfimport refused the MLIR:\n" + indent(log))
        return finish(R)
    summ = log.strip().split("\n")[0]
    nseg = sum(1 for l in log.split("\n") if l.startswith("seg"))
    drift = []
    have = [f for f in (f"{K}.lean", f"{K}Seg.lean") if os.path.exists(os.path.join(NET, f))]
    for f in have:
        # the docstring's `Source:` line names the MLIR path (build/frontend vs its committed
        # fixture copy); the drift check is about content, so that one line is ignored
        if norm(open(os.path.join(imp, f)).read()) != norm(open(os.path.join(NET, f)).read()):
            drift.append(f)
    if not have:
        dv = "no committed graph for this kernel (new kernel)"
    elif drift:
        dv = f"DIFFERS from committed {', '.join(drift)}: committed proofs are about another graph"
    else:
        dv = f"identical to committed {', '.join(have)}"
    R.stage("1 import", "PASS",
            f"bdc's own parser/fusion/lowering read the MLIR: {summ}, {nseg} symbolic segments; drift: {dv}",
            "anything about bdc's Verilog emission or cells; H_SOURCE_ETERNAL (source/constant "
            "chains are always-valid channels) is the importer's modelling step")

    # ---- C reference ------------------------------------------------------------------
    try:
        crefs = c_reference(cfile, k["func"], vecs)
    except Exception as e:  # noqa: BLE001
        R.stage("2 C reference", "FAIL", "-", f"could not compile/run the C reference: {e}")
        return finish(R)

    # ---- 2a Lean ----------------------------------------------------------------------
    leanref = {}
    if a.no_lean:
        R.stage("2a lean", "SKIP", "- (--no-lean)", "-")
        lean_v = "SKIP"
    else:
        rc, log = run([PY, os.path.join(HERE, "leanstage.py"), a.kernel, mlir, os.path.join(out, "lean")], env=env)
        print(indent("\n".join(l for l in log.split("\n") if not l.startswith("LEANREF"))))
        for l in log.split("\n"):
            m = re.match(r"LEANREF (\S+) -> (.*)$", l)
            if m:
                leanref[m.group(1)] = m.group(2).strip()
        last = [l for l in log.split("\n") if l.startswith("LEAN ")]
        lv = last[-1].split()[1].rstrip(":") if last else "FAIL"
        if lv == "PASS":
            R.stage("2a lean", "PASS",
                    f"{k['theorem']}: from one token per input, EVERY complete run of the graph imported "
                    "from THIS MLIR (any schedule, any arbiter outcome) ends with exactly the hand "
                    "transcription's result; no run is longer (Lean kernel, axioms audited)",
                    "that the hand transcription is the C (stage 2c tests it on vectors; a reviewer reads it); "
                    "termination of the C; gates, delays, cells")
        elif lv == "PARTIAL":
            R.stage("2a lean", "SKIP",
                    "(partial) the generated graph is well formed and every symbolic schedule segment "
                    "is kernel-checked; no theorem about the C function",
                    "functional correctness: this kernel has no hand-written token proof "
                    "(write Formal/Net/<K>HwProof.lean following IpowHwProof.lean)")
        else:
            R.stage("2a lean", "FAIL",
                    "nothing: the committed proof does not check against the graph this MLIR produces",
                    "a FAIL here is 'not proved', not 'wrong'; stage 2b looks for a real counterexample")
        lean_v = {"PASS": "PASS", "PARTIAL": "SKIP"}.get(lv, "FAIL")

    # ---- 2e generated all-inputs proof -------------------------------------------------
    autoref = {}
    auto_v = "SKIP"
    if a.no_lean or a.no_auto:
        R.stage("2e auto", "SKIP", "- (--no-lean/--no-auto)", "-")
    else:
        cmd = [PY, os.path.join(HERE, "autostage.py"), a.kernel, mlir, os.path.join(out, "auto"),
               "--vecs", " ".join(",".join(map(str, v)) for v in vecs)]
        if a.c:
            cmd += ["--c", cfile]
        rc, log = run(cmd, env=env)
        print(indent("\n".join(l for l in log.split("\n") if not l.startswith("AUTOREF"))))
        for l in log.split("\n"):
            m = re.match(r"AUTOREF (\S+) -> (.*)$", l)
            if m:
                autoref[m.group(1)] = m.group(2).strip()
        if rc == 0:
            auto_v = "PASS"
            R.stage("2e auto", "PASS",
                    f"Formal.Net.Auto{K}V.auto_computes, GENERATED (no hand proof): from one token per input, "
                    "EVERY complete run of the graph imported from THIS MLIR (any schedule, any arbiter outcome) "
                    "ends with exactly [r] where r is what the generated C transcription `kC` returns, for ALL "
                    "inputs on which it returns; no run is longer (Lean kernel, axioms audited)",
                    "that cfront's transcription is the C (2c tests it on the vectors); termination of the C; "
                    "gates, delays, cells")
        elif rc == 1:
            auto_v = "FAIL"
            R.stage("2e auto", "FAIL",
                    "a COUNTEREXAMPLE input from autoproof's co-simulation (graph template run vs C "
                    "transcription, Python semantics; printed above)",
                    "the Python semantics is a transcription (2b/2d re-check with their own engines)")
        else:
            auto_v = "NOTPROVED"
            R.stage("2e auto", "SKIP",
                    "nothing: no generated proof (see the reason above)",
                    "a SKIP here is 'not proved', not 'wrong'")

    # ---- 2b search --------------------------------------------------------------------
    rc, log = run([PY, os.path.join(HERE, "tokensearch.py"), mlir, "--c", cfile, "--func", k["func"],
                   "--vecs", " ".join(",".join(map(str, v)) for v in vecs), "--max-states", str(a.max_states)],
                  env=env)
    print(indent(log))
    R.stage("2b search", {0: "PASS", 1: "FAIL", 2: "SKIP"}.get(rc, "FAIL"),
            "on each listed vector, EVERY schedule of the imported graph (persistent-set reduced, "
            "exact for terminal stores) ends with the compiled C's value and nothing else, "
            "and no schedule runs forever" if rc == 0 else
            ("a counterexample schedule (printed above) whose final store is not the C result"
             if rc == 1 else "inconclusive: state bound hit"),
            "inputs outside the vector list; the Python semantics is a transcription of "
            "GcdHwLib's Rule.fire (not proved equal)")

    # ---- 2d generated per-vector theorems ---------------------------------------------
    if a.no_lean:
        R.stage("2d vectors", "SKIP", "- (--no-lean)", "-")
    else:
        rc2, log = run([PY, os.path.join(HERE, "vecgen.py"), a.kernel, mlir, os.path.join(out, "vec"),
                        "--c", cfile, "--vecs", " ".join(",".join(map(str, v)) for v in vecs)], env=env)
        print(indent(log))
        if rc2 == 0:
            R.stage("2d vectors", "PASS",
                    f"generated Lean theorems {k['ns']}.vec<i>, no hand proof involved: for each of the "
                    f"{len(vecs)} vectors, from one token per input EVERY complete run of the graph imported "
                    "from THIS MLIR ends with exactly [compiled C result] on the output and nothing else "
                    "(the Lean kernel re-executes the witness schedule; C-8i's `determinate` covers all others)",
                    "inputs not listed; termination is shown only for the listed vectors")
        else:
            R.stage("2d vectors", "FAIL",
                    "no theorem for at least one vector (its counterexample is in stage 2b)" if rc == 1
                    else "the generated vector theorems did not check (see above)",
                    "-")

    # ---- 2c transcription vs C --------------------------------------------------------
    if autoref:
        bad = []
        for v, c in zip(vecs, crefs):
            key = ",".join(map(str, v))
            want = f"some {c % (1 << 32)}"
            if autoref.get(key) != want:
                bad.append(f"({key}): generated transcription {autoref.get(key)}, compiled C {want} (= {c})")
        R.stage("2f auto-tr", "FAIL" if bad else "PASS",
                f"the generated C transcription (kC) agrees with the compiled C on all {len(vecs)} vectors"
                if not bad else "COUNTEREXAMPLE to 'generated transcription = C':\n      " + "\n      ".join(bad),
                "agreement on other inputs (testing, not proof)")
    if leanref:
        bad = []
        for v, c in zip(vecs, crefs):
            key = ",".join(map(str, v))
            want = f"some {c % (1 << 32)}"
            if leanref.get(key) != want:
                bad.append(f"({key}): Lean transcription {leanref.get(key)}, compiled C {want} (= {c})")
        R.stage("2c transcr", "FAIL" if bad else "PASS",
                f"the Lean transcription in the hand proof agrees with the compiled C on all {len(vecs)} vectors"
                if not bad else "COUNTEREXAMPLE to 'transcription = C':\n      " + "\n      ".join(bad),
                "agreement on other inputs (this is testing, not proof)")
    else:
        R.stage("2c transcr", "SKIP", "-", "no hand transcription evaluated (no proof, or stage 2a failed)")

    # ---- 3 circuit --------------------------------------------------------------------
    if a.no_cap:
        R.stage("3 circuit", "SKIP", "- (--no-cap)", "-")
    else:
        rc, log = run([PY, os.path.join(HERE, "capstage.py"), a.kernel, mlir, os.path.join(out, "cap")], env=env)
        print(indent(log))
        cv = {0: "PASS", 1: "FAIL", 3: "SKIP"}.get(rc, "FAIL")
        cap = k.get("capstone") or {}
        R.stage("3 circuit", cv,
                f"{cap.get('theorem')}: the committed circuit-level safety theorem is about exactly the "
                "network this MLIR produces (links, ring certificate, operator network regenerated), "
                "and it checks (olean current, axioms audited)" if cv == "PASS" else
                ("the circuit network of this MLIR differs from the proved one (see diff)" if cv == "FAIL"
                 else "- (see reason above)"),
                "its named hypotheses (H_CELLS, H_BUNDLE, H_START_ONCE: formal/notes/C-gcd_hw-hypotheses.md); "
                "routed delays (stage 4); the bitstream")

    # ---- 4 timing ---------------------------------------------------------------------
    if not a.route:
        R.stage("4 timing", "SKIP", "- (no --route given)", "-")
    else:
        rc, log = run([PY, os.path.join(HERE, "tstage.py")] + a.route + ["--workdir", os.path.join(out, "tstage")])
        print(indent(log))
        tv = {0: "PASS", 1: "FAIL"}.get(rc, "FAIL")
        R.stage("4 timing", tv,
                "every extracted obligation row PASSes the verified checker (Tcheck.verdict_sound): "
                "data settles before its request under the per-arc delay intervals" if tv == "PASS" else
                "failing rows above: each with the arcs that make data late or the request early",
                "the front end (extract.py: graph, intervals, obligation choice) is untrusted; one route is "
                "a sample (>= 4 seeds); prjxray delays are a model")

    return finish(R, "PASS" if "PASS" in (lean_v, auto_v) else lean_v)


def finish(R, lean_v="FAIL"):
    vs = dict(R.rows)
    print("\nsummary: " + "  ".join(f"{n.split()[0]}={v}" for n, v in R.rows))
    # a FAIL of 2a (committed proof does not check on this graph) or of 3 (network differs from
    # the proved one) means "not proved"; only the other stages refute (counterexample / failed check)
    refuting = [n for n, v in R.rows if v == "FAIL" and not n.startswith(("2a", "3 "))]
    proved_by = [n for n, v in R.rows if v == "PASS" and n.startswith(("2a", "2e"))]
    if refuting:
        print(f"VERDICT: FAIL ({', '.join(refuting)}; counterexamples printed above)")
        return 1
    # a 2a FAIL (the hand proof is syntactic) is excused by a generated 2e PASS; a stage-3 FAIL
    # (the circuit network differs from the proved one) is not
    unexcused = [n for n, v in R.rows if v == "FAIL" and not (n.startswith("2a") and "2e auto" in proved_by)]
    if unexcused:
        print("VERDICT: NOT PROVED (no counterexample found; the committed proofs do not apply to this "
              "design: " + ", ".join(unexcused) + ")")
        return 2
    if lean_v == "PASS":
        print(f"VERDICT: PASS (token-level all-inputs theorem checked on this MLIR by {', '.join(proved_by)}; "
              "other stages as listed)")
        return 0
    if vs.get("2d vectors") == "PASS":
        print("VERDICT: PROVED ON THE LISTED VECTORS ONLY (generated per-vector theorems checked; "
              "no all-inputs theorem applies)")
        return 2
    print("VERDICT: NOT PROVED (no counterexample found; no proof applies)")
    return 2


if __name__ == "__main__":
    sys.exit(main())
