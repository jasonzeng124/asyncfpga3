"""table.py -- per-seed tables for A-events5 from ana5's JSON (strict margins: <= 0 fails)."""
import json, sys, collections
O = sys.argv[1] if len(sys.argv) > 1 else "/tmp/events5/out"
CASCADE = "ucontrol_merge12.uarb"
print("seed corner | stages clean (contig5) | cascade-excl. | Back min / <=0 | guard entry min / <=0 | guard exit min / <=0 | "
      "contig4 min / fail | contig5 min / fail | merges cert. | W min")
for s in "d 3 4 5".split():
    for c in "slow fast indep gb".split():
        r = json.load(open(f"{O}/{s}/ana5_{c}.json"))
        real = [e for e in r["stages"] if not e["virtual"]]
        stg = {e["stage"] for e in real}
        bad = collections.defaultdict(set)
        for e in real:
            if e["rule"] == "Back" and e["margin"] <= 0: bad[e["stage"]].add("Back")
            if e["rule"] == "Guard" and (e["entry"] is None or e["entry"] <= 0): bad[e["stage"]].add("GE")
            if e["rule"] == "Guard" and (e["exit"] is None or e["exit"] <= 0): bad[e["stage"]].add("GX")
            if e["rule"] == "NONE": bad[e["stage"]].add("NONE")
        for m in r["contig5"]:
            if m["stage"] in stg and (m.get("margin") is None or m["margin"] <= 0): bad[m["stage"]].add("C5")
        nb = [k for k, v in bad.items() if v]
        nbx = [k for k in nb if CASCADE not in k]
        back = [e["margin"] for e in real if e["rule"] == "Back"]
        g = [e for e in real if e["rule"] == "Guard"]
        ge = [e["entry"] for e in g if e["entry"] is not None]
        gx = [e["exit"] for e in g if e["exit"] is not None]
        c4 = [m["margin"] for m in r["multis"] if m["margin"] is not None]
        c5 = [m["margin"] for m in r["contig5"] if m.get("margin") is not None]
        W = [w for w in r["W"].values() if w is not None]
        mg = r["merges"]
        print(f"{s} {c:5s} | {len(stg)-len(nb)}/{len(stg)} | {len(nbx)} bad | {min(back)} / {sum(x <= 0 for x in back)} | "
              f"{min(ge)} / {sum(x <= 0 for x in ge)} | {min(gx)} / {sum(x <= 0 for x in gx)} | "
              f"{min(c4)} / {sum(x <= 0 for x in c4)} | {min(c5)} / {sum(x <= 0 for x in c5)} | "
              f"{sum(m['ok'] for m in mg)}/{len(mg)} | {min(W)}")
    print()
print("== every failing item, non-cascade, mixed (indep) and guardband (gb) ==")
for s in "d 3 4 5".split():
    for c in ("indep", "gb"):
        r = json.load(open(f"{O}/{s}/ana5_{c}.json"))
        out = []
        for e in r["stages"]:
            if e["virtual"] or CASCADE in e["stage"]:
                continue
            nm = e["stage"].replace("urig.udut.", "")
            if e["rule"] == "Back" and e["margin"] <= 0:
                out.append(f"Back {e['margin']} {nm} <- {e['src'].replace('urig.udut.', '')}")
            if e["rule"] == "Guard" and e["entry"] is not None and e["entry"] <= 0:
                out.append(f"GuardEntry {e['entry']} {nm}")
            if e["rule"] == "Guard" and e["exit"] is not None and e["exit"] <= 0:
                out.append(f"GuardExit {e['exit']} {nm}")
        for m in r["contig5"]:
            if CASCADE in m["stage"]:
                continue
            if m.get("margin") is not None and m["margin"] <= 0:
                out.append(f"Contig5 {m['margin']} {m['stage'].replace('urig.udut.', '')} <- {m['src'].replace('urig.udut.', '')} "
                           f"(window {m['window']} at {str(m['at']).replace('urig.udut.', '')}, W {m['W']})")
        print(f"-- seed {s} {c}: {len(out)}")
        for l in sorted(out, key=lambda l: int(l.split()[1])):
            print("   " + l)
