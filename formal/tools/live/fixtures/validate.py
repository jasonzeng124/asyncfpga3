#!/usr/bin/env python3
"""validate.py OUTDIR -- the 34 configurations of research/data/suite/ringfloor/validation.txt through live.py."""
import json
import os
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from run_all import FIX, RS, base_env, run_live  # noqa: E402

# (name, kernel, env, simcheck verdict from validation.txt)
Q = "quadrec"


def d(**kw):
    return ",".join(f"ulink_n_trueResult_{k[1:]}={v}" for k, v in kw.items())


OFF = {"BDC_TOKEN_FLOOR": "0"}
CONFIGS = [
    ("quadrec base", Q, OFF, "deadlock"),
    ("quadrec A tR14=7", Q, {**OFF, "BDC_LINK_DEPTHS": d(t14=7)}, "deadlock"),
    ("quadrec B tR20=3,18=2,16=2", Q, {**OFF, "BDC_LINK_DEPTHS": d(t20=3, t18=2, t16=2)}, "live"),
    ("quadrec C tR14=3,16=2,18=2", Q, {**OFF, "BDC_LINK_DEPTHS": d(t14=3, t16=2, t18=2)}, "deadlock"),
    ("quadrec Cm tR16=2,18=2", Q, {**OFF, "BDC_LINK_DEPTHS": d(t16=2, t18=2)}, "deadlock"),
    ("quadrec D tR14=4,16=2", Q, {**OFF, "BDC_LINK_DEPTHS": d(t14=4, t16=2)}, "deadlock"),
    ("quadrec suite fix all four=3", Q, {**OFF, "BDC_LINK_DEPTHS": d(t14=3, t16=3, t18=3, t20=3)}, "live"),
    ("quadrec floor default", Q, {}, "live"),
    ("quadrec floor AUTO", Q, {"BDC_AUTO": "1"}, "live"),
]
for t in (16, 18, 20):
    rest = {f"t{k}": 2 for k in (14, 16, 18, 20) if k != t}
    for fl, e in (("default", {}), ("AUTO", {"BDC_AUTO": "1"})):
        CONFIGS.append((f"quadrec floor-1 (tR{t}) {fl}", Q, {**OFF, **e, "BDC_LINK_DEPTHS": d(**rest)}, "deadlock"))
KNOBS = "KNOBS"   # olink / rlink / ruleF: filled from bdc/auto.py's own rule functions per kernel
for k, rows in (("lfsrfind", [("base", "deadlock"), ("olink", "live"), ("rlink", "deadlock"), ("ruleF", "deadlock"),
                              ("floor", "live"), ("AUTO", "live")]),
                ("nested", [("base", "deadlock"), ("olink", "live"), ("rlink", "live"), ("floor", "live"),
                            ("AUTO", "live")]),
                ("nest3", [("base", "deadlock"), ("olink", "live"), ("rlink", "live"), ("ruleF", "deadlock"),
                           ("floor", "live"),
                           ("floor-1 (no falseResult_17 stage)", "deadlock"),
                           ("floor-1 (no falseResult_33 stage)", "deadlock"), ("AUTO", "live")])):
    for name, want in rows:
        if name == "base":
            env = OFF
        elif name in ("olink", "rlink", "ruleF"):
            env = {**OFF, KNOBS: name}
        elif name == "floor":
            env = {}
        elif name == "AUTO":
            env = {"BDC_AUTO": "1"}
        elif "falseResult_17" in name:
            env = {**OFF, "BDC_LINK_DEPTHS": "ulink_n_falseResult_33=2"}
        else:
            env = {**OFF, "BDC_LINK_DEPTHS": "ulink_n_falseResult_17=2"}
        CONFIGS.append((f"{k} {name}", k, env, want))

KNOB_PY = r"""
import sys, emit, auto
from hs import parse
p = sys.argv[1]
f = [f for f in parse.parse_module(open(p).read(), filename=p) if not f.is_declaration][0]
print(",".join(sorted(auto.loop_header_merges(f, emit.instname))))
print(",".join(sorted(auto.steer_fork_outputs(f, emit.vname))))
"""


def knobs(mlir):
    p = subprocess.run([sys.executable, "-c", KNOB_PY, mlir], env=base_env({}), cwd=os.path.join(RS, "bdc"),
                       capture_output=True, text=True)
    hdr, fo = (p.stdout.splitlines() + ["", ""])[:2]
    return hdr, fo


def main():
    out = os.path.abspath(sys.argv[1])
    os.makedirs(os.path.join(out, "graphs"), exist_ok=True)
    rows = []
    done = {}
    vp = os.path.join(out, "validation.jsonl")
    if os.path.exists(vp):
        for l in open(vp):
            d_ = json.loads(l)
            if d_.get("verdict") in ("LIVE", "DEADLOCK", "SAMPLED-LIVE"):
                done[d_["config"]] = d_
    open(vp, "w").write("".join(json.dumps(v) + "\n" for v in done.values()))
    rows = list(done.values())
    for name, k, env, want in CONFIGS:
        if name in done:
            continue
        mlir = os.path.join(FIX, k, "comp", "handshake_transformed.mlir")
        env = dict(env)
        if KNOBS in env:
            hdr, fo = knobs(mlir)
            kind = env.pop(KNOBS)
            env.update({"olink": {"BDC_MERGE_OUT_LINK": hdr}, "rlink": {"BDC_MERGE_RES_LINK": hdr},
                        "ruleF": {"BDC_FORK_OUT_LINK": fo}}[kind])
        tag = "validate." + name.replace(" ", "_").replace("(", "").replace(")", "").replace(",", "_").replace("=", "")
        r = run_live(mlir, base_env(env), tag, out)
        if r.get("verdict") in ("BLOWUP", "BLOWUP-MEM", "TIMEOUT"):
            rr = run_live(mlir, base_env(env), tag + ".rand", out, extra=["--random", "300", "--steps", "100000"])
            r["exhaustive"] = r.get("verdict")
            r["verdict"] = rr.get("verdict")
            r["walks"] = rr.get("walks")
            r["z_checked"], r["z_traps"] = rr.get("z_checked"), rr.get("z_traps")
            r["trace_choices"] = rr.get("trace_choices")
        got = {"DEADLOCK": "deadlock", "LIVE": "live", "SAMPLED-LIVE": "live"}.get(r.get("verdict"), r.get("verdict"))
        r.update(config=name, env={k_: v for k_, v in env.items()}, simcheck=want, agree=(got == want))
        rows.append(r)
        print(f"{name}: live.py {got} ({r.get('states')} states) simcheck {want} {'OK' if got == want else 'MISMATCH'}"
              f"  {r.get('trace_choices') or ''}", flush=True)
        with open(os.path.join(out, "validation.jsonl"), "a") as fh:
            fh.write(json.dumps(r) + "\n")
    n = sum(r["agree"] for r in rows)
    print(f"validation: {n} / {len(rows)} agree with simcheck")


if __name__ == "__main__":
    main()
