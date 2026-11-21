#!/usr/bin/env python3
"""C-10i: per-instance summary of build/grantfork.json -> build/summary.md (evidence;
the verdicts are re-decided by the kernel in Formal/Timing/GrantForkInst.lean)."""
import json, pathlib
H = pathlib.Path(__file__).resolve().parent
rows = json.load(open(H / "build/grantfork.json"))
VS = ["FMIN", "FMAX", "SMIN", "SMAX", "fast", "slow", "sdf"]
out = ["| design | instance | k | pins ug q,r / st q,r | fb | W ps: " + " ".join(VS) + " | transport ok at | inertial width/thr (SMAX) | inertial ok at |",
       "|---|---|---|---|---|---|---|---|---|"]
tot = {v: [0, 0] for v in VS}
for r in rows:
    V = r["V"]
    W = " ".join(str(V[v]["W"][1]) for v in VS)
    tok = ",".join(v for v in VS if V[v]["transport_ok"]) or "none"
    iok = ",".join(v for v in VS if V[v]["inertial_ok"]) or "none"
    for v in VS:
        tot[v][0] += V[v]["transport_ok"]; tot[v][1] += V[v]["inertial_ok"]
    p = r["pins"]
    out.append(f"| {r['design']} | {r['inst'].replace('urig.udut.ucontrol_', '')} | {r['client']} | "
               f"{p['ugrant_q']},{p['ugrant_r']} / {p['ustate_q']},{p['ustate_r']} | {','.join(r['fallback']) or '-'} | "
               f"{W} | {tok} | {V['SMAX']['width_hi']}/{V['SMAX']['thr_lo']} | {iok} |")
out.append("")
out.append(f"totals over {len(rows)} arbiter-clients (transport ok / inertial ok): " +
           ", ".join(f"{v} {a}/{b}" for v, (a, b) in tot.items()))
inst = {}
for r in rows:
    inst.setdefault((r["design"], r["inst"]), []).append(r)
n_all = sum(1 for k, rs in inst.items() if all(x["V"][v]["transport_ok"] for x in rs for v in VS[:4]))
n_none = sum(1 for k, rs in inst.items() if all(not x["V"]["SMAX"]["transport_ok"] for x in rs))
out.append(f"instances: {len(inst)}; transport H_GRANT_FORK holds for both clients at all 4 consistent corners: {n_all}; "
           f"fails for both clients at SMAX: {n_none}")
(H / "build/summary.md").write_text("\n".join(out) + "\n")
print("\n".join(out[-3:]))
