#!/usr/bin/env python3
"""sweep.py OUT.jsonl [fixture ...] -- reentry.py on every fixture x {def, auto}, floor on, one process at a time.
Also the configured extra rows (fixes and negative controls). Appends one JSON line per row."""
import json, os, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
FIX = "/home/user/rs/cloud/fixtures/frontend"
FLOWS = {"def": {}, "auto": {"BDC_AUTO": "1"}}
EXTRA = [  # (fixture, label, env)
    ("matrix", "n26=2", {"BDC_LINK_DEPTHS": "ulink_n26=2"}),
    ("matrix", "olink cm1", {"BDC_MERGE_OUT_LINK": "ucontrol_merge1"}),
    ("matrix", "n32=4", {"BDC_LINK_DEPTHS": "ulink_n32=4"}),
    ("matrix", "n49__5=2", {"BDC_LINK_DEPTHS": "ulink_n49__5=2"}),
    ("matrix", "n35=2", {"BDC_LINK_DEPTHS": "ulink_n35=2"}),
    ("stencil_2d", "n45=2", {"BDC_LINK_DEPTHS": "ulink_n45=2"}),
    ("stencil_2d", "olink cm1", {"BDC_MERGE_OUT_LINK": "ucontrol_merge1"}),
    ("stencil_2d", "n54=2", {"BDC_LINK_DEPTHS": "ulink_n54=2"}),
]


def env_for(extra):
    env = {k: v for k, v in os.environ.items() if not k.startswith("BDC_")}
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    env.update(extra)
    return env


def run(fix, flow, label, extra):
    mlir = os.path.join(FIX, fix, "comp", "handshake_transformed.mlir")
    p = subprocess.run([sys.executable, "-B", os.path.join(HERE, "reentry.py"), mlir], env=env_for(extra),
                       capture_output=True, text=True, timeout=600)
    lines = p.stdout.splitlines()
    if p.returncode not in (0, 1) or not lines or not lines[-1].endswith(("FLAGGED", "clean")):
        v = "REFUSED" if "Error" in p.stderr else "CRASH"
        return {"fixture": fix, "flow": flow, "label": label, "env": extra, "reentry": v,
                "error": (p.stderr.strip().splitlines() or ["?"])[-1][:300]}
    short = [l for l in lines if "SHORT" in l]
    return {"fixture": fix, "flow": flow, "label": label, "env": extra,
            "reentry": "FLAGGED" if p.returncode == 1 else "clean",
            "iterating_short": any("view iterating" in l for l in short),
            "walks": [l.split(": ", 1)[1] for l in short]}


def main():
    out = sys.argv[1]
    fixes = sys.argv[2:] or sorted(os.listdir(FIX))
    with open(out, "a") as f:
        for fx in fixes:
            if not os.path.exists(os.path.join(FIX, fx, "comp", "handshake_transformed.mlir")):
                continue
            for flow, ev in FLOWS.items():
                r = run(fx, flow, "", ev)
                f.write(json.dumps(r) + "\n"); f.flush()
                print(fx, flow, r["reentry"], flush=True)
        if not sys.argv[2:]:
            for fx, label, ev in EXTRA:
                r = run(fx, "def", label, ev)
                f.write(json.dumps(r) + "\n"); f.flush()
                print(fx, label, r["reentry"], flush=True)


if __name__ == "__main__":
    main()
