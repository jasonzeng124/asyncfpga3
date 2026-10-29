"""Auditor negative controls for research cells/gls/fid/acceptance.py (r8).
Imports the research module; replaces only the child processes with fakes."""
import os, sys, types, subprocess, tempfile
from pathlib import Path
src = Path(sys.argv[1]); fake = Path(sys.argv[2]).resolve()
sys.path.insert(0, str(src)); import acceptance as A
tmp = Path(tempfile.mkdtemp())
def show(name, f):
    try: print("%-34s -> %r" % (name, f()))
    except Exception as e: print("%-34s -> RAISES %s: %s" % (name, type(e).__name__, str(e)[:90]))
# --- soak path (DSP items): fake soak_fid.py
A.HERE = fake
for mode in ("empty", "garbled", "pass_rc1"):
    os.environ["FAKE_MODE"] = mode
    show("soak_bit[%s]" % mode, lambda: A.soak_bit(tmp, tmp / "patched.bit", tmp / "x.sdf", tmp / ("w" + mode), {})[0])
os.environ["FAKE_MODE"] = "crash_on_unpatched"
runs = {}
for tag in ("patched", "unpatched"):
    p, lines, ref = A.soak_bit(tmp, tmp / (tag + ".bit"), tmp / "x.sdf", tmp / ("w" + tag), {})
    runs[tag] = {"sim_passes": p, "refused": [l for l in lines if "refuses" in l] if ref else []}
show("judge_full[gen.py crash on unpatched]", lambda: A.judge_full(runs))
# --- gcd path: gls_gcd with a fake subprocess.run (vvp prints garbage / nothing)
real = subprocess.run
def fake_run(cmd, *a, **k):
    c = cmd[0] if isinstance(cmd, list) else cmd
    if c == "vvp" and cmd[1] == "gate.vvp":
        return types.SimpleNamespace(returncode=0, stdout="ANNOTATE_DONE\n", stderr="")
    if c == "vvp":
        out = {"garbled": "VVP error: out of memory\n", "nores": "LAP 1 t=1\n",
               "deadlock": "RESULT deadlock: vec=0 laps=3 last lap at t=1, quiet for 9\n",
               "xerr": "RESULT timeout: vec=0 laps=9 errs=0 oks=9\n"}[os.environ["FAKE_VVP"]]
        return types.SimpleNamespace(returncode=0, stdout=out, stderr="")
    return types.SimpleNamespace(returncode=0, stdout="", stderr="")
A.subprocess.run = fake_run
nl = tmp / "n.json"; nl.write_text("{}"); sd = tmp / "s.sdf"; sd.write_text("")
for m in ("garbled", "nores", "deadlock", "xerr"):
    os.environ["FAKE_VVP"] = m
    show("gls_gcd[%s]" % m, lambda: A.gls_gcd(nl, sd, tmp / ("g" + m), [0, 1]))
show("gls_gcd[no vectors] all([])", lambda: A.gls_gcd(nl, sd, tmp / "gnone", list(range(5, 4 + 1 - 1))))
# patched clean, unpatched vvp garbage -> judge
os.environ["FAKE_VVP"] = "xerr"; good, gok = A.gls_gcd(nl, sd, tmp / "gp", [0])
os.environ["FAKE_VVP"] = "garbled"; bad, bok = A.gls_gcd(nl, sd, tmp / "gu", [0])
runs = {"patched": {"sim_passes": all(c for c, _ in good.values()), "gate_ok": gok, "refused": []},
        "unpatched": {"sim_passes": all(c for c, _ in bad.values()), "gate_ok": bok, "refused": []}}
show("judge_full[unpatched vvp garbled]", lambda: A.judge_full(runs))
