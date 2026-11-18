#!/usr/bin/env python3
"""compare.py -- agreement of reentry.py with live.py: floor-on sweep (sweep.jsonl vs fixtures/results.jsonl +
live_extra.jsonl), the fix / non-fix configurations (live_cfg.jsonl), formal's 34 validation configurations
(valctl.jsonl) and floor-off rows (flooroff.jsonl). Prints a table of counts and every disagreement."""
import json, os
H = os.path.dirname(os.path.abspath(__file__))
L = lambda p: [json.loads(l) for l in open(os.path.join(H, p))] if os.path.exists(os.path.join(H, p)) else []
live = {}
for r in L("../fixtures/results.jsonl"):
    if r.get("floor") == "on":
        live[(r["fixture"], r["flow"])] = r["verdict"]
for r in L("live_extra.jsonl"):
    live.setdefault((r["fixture"], r["flow"]), r["verdict"])
for r in L("../fixtures/validation.jsonl"):           # nest3 floor-on rows (exhaustive over budget)
    if r["config"] in ("nest3 floor", "nest3 AUTO"):
        live.setdefault(("nest3", "auto" if "AUTO" in r["config"] else "def"), r["verdict"])
for r in L("live_cfg.jsonl"):
    live[(r["fixture"], r["label"])] = r["verdict"]
dead = lambda v: v == "DEADLOCK"
proved = lambda v: v in ("LIVE", "SAMPLED-LIVE", "DEADLOCK")


def tally(name, rows):
    c = {"agree": 0, "disagree": 0, "no live verdict": 0}
    dis = []
    for key, re_v, lv, extra in rows:
        if lv is None or not proved(lv):
            c["no live verdict"] += 1
            dis.append(("NO-ORACLE", key, re_v, lv, extra))
            continue
        if (re_v == "FLAGGED") == dead(lv):
            c["agree"] += 1
        else:
            c["disagree"] += 1
            dis.append(("DISAGREE", key, re_v, lv, extra))
    print(f"{name}: {c}")
    for d in dis:
        print("   ", *d)


sw = [r for r in L("sweep.jsonl") if r["reentry"] != "REFUSED"]
tally("floor on, fixtures x {def, auto}",
      [((r["fixture"], r["flow"]), r["reentry"], live.get((r["fixture"], r["flow"])), "") for r in sw if not r["label"]])
tally("fix / non-fix configurations (def, floor on)",
      [((r["fixture"], r["label"]), r["reentry"], live.get((r["fixture"], r["label"])), "") for r in sw if r["label"]])
tally("formal validation configurations (34)",
      [(r["label"], r["reentry"], r["live"], "iter" if r.get("iterating_short") else "") for r in L("valctl.jsonl")])
tally("floor off, fixtures x {def, auto}",
      [((r["fixture"], r["flow"]), r["reentry"], r["live"], "iter" if r.get("iterating_short") else "")
       for r in L("flooroff.jsonl") if r["reentry"] != "REFUSED"])
