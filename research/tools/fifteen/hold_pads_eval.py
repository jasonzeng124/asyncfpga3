#!/usr/bin/env python3
"""hold_pads_eval.py BASE.vh OUT.vh REQUEST [PS_PER_LINK] -- hold_pads.py's knob mapping, from a farm request's
eval.txt "hold/close:" lists instead of corner_audit reports (requests submitted before eval_task returned
report_hi_*.txt carry only the margins, not corner_audit's "PAD to k").

Each H / I row below 0, on any route and either corner, raises its knob by ceil(-margin / PS_PER_LINK) over BASE
(the largest over all rows). PS_PER_LINK defaults to 300 ps, under the ~400 ps a link costs on these routes
(tighten.chain_link_costs), so the estimate over-pads rather than under-pads -- the longer number, as CLAUDE.md asks.
Knobs as in hold_pads.py: H <link>.ctl / <pipe>.many.stage[i] -> _UACK; I <pipe>.many.stage[i>0] -> _SDELAY.
"""
import re, sys, math, subprocess

base_p, out_p, req = sys.argv[1:4]
per = float(sys.argv[4]) if len(sys.argv) > 4 else 300.0
P = "BD_SZ_BRIDGE_I_UDUT_"
def macro(inst): return P + re.sub(r"[^A-Za-z0-9]", "_", inst).upper()
base = {}
lines = open(base_p).read().splitlines()
for ln in lines:
    m = re.match(r"`define\s+(\S+)\s+(\d+)", ln)
    if m: base[m.group(1)] = int(m.group(2))
need, why, odd = {}, {}, []
for t in range(1, 257):
    r = subprocess.run(["git", "show", f"origin/claude/cluster:results/{req}/{t}/eval.txt"], capture_output=True, text=True)
    if r.returncode: continue
    for ln in r.stdout.splitlines():
        m = re.match(r"static (nom|worst) .*hold/close: (.*)$", ln)
        if not m: continue
        for row in m.group(2).split(";"):
            x = re.match(r"\s*([HI]) (-\d+) (\S+)", row)
            if not x: continue
            rule, mg, lab = x.group(1), int(x.group(2)), x.group(3)
            mp = re.match(r"(.+?)\.many\.stage\[(\d+)\]\.u\.ctl\.u\.u$", lab)
            ml = re.match(r"(.+?)\.ctl\.u\.u$", lab)
            if rule == "H" and (mp or ml):
                knob = macro((mp or ml).group(1)) + "_UACK"
            elif rule == "I" and mp and int(mp.group(2)) > 0:
                knob = macro(mp.group(1)) + "_SDELAY"
            else:
                odd.append(f"{rule} {mg} {lab} (task {t}): no knob"); continue
            k = base.get(knob, 0) + math.ceil(-mg / per)
            if k > need.get(knob, -1): need[knob] = k
            why.setdefault(knob, []).append((mg, t, m.group(1)))
out, done, moved = [], set(), 0
for ln in lines:
    m = re.match(r"`define\s+(\S+)\s+(\d+)", ln)
    if m and m.group(1) in need and need[m.group(1)] > int(m.group(2)):
        k = m.group(1); w = min(why[k])
        out.append(f"`define {k} {need[k]}   // hold_pads_eval.py {req}: was {m.group(2)}; {len(why[k])} rows below 0 "
                   f"(worst {w[0]} task {w[1]} {w[2]})"); moved += 1
    else:
        out.append(ln)
    if m: done.add(m.group(1))
for k in sorted(set(need) - done):
    w = min(why[k])
    out.append(f"`define {k} {need[k]}   // hold_pads_eval.py {req}: not in base; {len(why[k])} rows below 0 "
               f"(worst {w[0]} task {w[1]} {w[2]})"); moved += 1
open(out_p, "w").write("\n".join(out) + "\n")
for o in odd: print("  " + o)
print(f"{moved} knob(s) moved ({per:.0f} ps a link) -> {out_p}")
