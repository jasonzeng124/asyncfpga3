"""report.py -- tables for the A-events4 notes from ana.py's JSON (slow, fast, indep)."""
import collections, json, re, sys

def fam(name):
    n = re.sub(r"^urig\.(udut\.)?", "", name)
    for k, f in [("uarb", "arbiter ack C (A1/A2)"), ("vctl", "virtual"), ("arb:", "virtual"),
                 ("ucond_br", "cond_br join"), ("umux", "mux join/ack"), ("_f.", "control_merge fork"),
                 ("ucontrol_merge", "control_merge (1-input fork)"), ("ufork", "fork"),
                 ("ulink", "link stage"), ("ujoin", "compute-unit join"), ("uenv", "rig env"), ]:
        if k in n:
            return f
    return "other"

runs = {c: json.load(open(p)) for c, p in zip(("slow", "fast", "indep"), sys.argv[1:4])}
print("== per-stage verdicts (real stages; a stage is CLEAN if every pin's rule holds) ==")
print(f"{'family':32s} " + " ".join(f"{c:>18s}" for c in runs))
fams = collections.defaultdict(lambda: collections.defaultdict(lambda: [0, 0]))
for c, r in runs.items():
    bad = collections.defaultdict(bool); stg = set()
    for e in r["stages"]:
        if e["virtual"]:
            continue
        stg.add(e["stage"])
        if e["rule"] == "Back" and e["margin"] < 0: bad[e["stage"]] = True
        if e["rule"] == "Guard" and (e["entry"] is None or e["entry"] < 0 or e["exit"] is None or e["exit"] < 0): bad[e["stage"]] = True
        if e["rule"] == "NONE": bad[e["stage"]] = True
    for m in r["multis"]:
        if (m["margin"] is None or m["margin"] < 0) and m["stage"] in stg: bad[m["stage"]] = True
    for s_ in stg:
        fams[fam(s_)][c][0] += 1
        fams[fam(s_)][c][1] += bad[s_]
for f in sorted(fams):
    print(f"{f:32s} " + " ".join(f"{fams[f][c][0]-fams[f][c][1]:>8d} clean/{fams[f][c][1]:<3d}bad" for c in runs))
for c, r in runs.items():
    print(f"\n== {c}: every negative or missing margin (ps) ==")
    for e in sorted(r["stages"], key=lambda e: e.get("margin", 0) if e["rule"] == "Back" else 0):
        if e["rule"] == "Back" and e["margin"] < 0:
            print(f"  Back  {e['margin']:6d}  {e['stage']} pin{e['pin']} <- {e['src']}  (lo {e['lo']} + d {e['d']} - hiQ {e['hiQ']}){' VIRTUAL' if e['virtual'] else ''}")
        if e["rule"] == "NONE":
            print(f"  NONE          {e['stage']} pin{e['pin']} <- {e['src']}")
    for e in r["stages"]:
        if e["rule"] == "Guard" and (e["entry"] is None or e["entry"] < 0 or e["exit"] is None or e["exit"] < 0):
            print(f"  Guard entry {e['entry']} exit {e['exit']} (W {e['W']})  {e['stage']} <- {e['src']}")
    bad = [m for m in r["multis"] if m["margin"] is None or m["margin"] < 0]
    print(f"  delay-line contiguity failures: {len(bad)}" + (f"; worst {min((m['margin'] for m in bad if m['margin'] is not None), default=None)} ps" if bad else ""))
    for m in sorted(bad, key=lambda m: m["margin"] if m["margin"] is not None else -10**9)[:6]:
        print(f"     {m['margin']}  {m['stage']} pin{m['pin']} <- {m['src']} ({m['op']}, {m['ntaps']} taps, window {m['pair']}, W {m['W']})")
    for m in r["merges"]:
        if not m["ok"]:
            print(f"  merge NOT certified: {m['merge']}")
    backs = [e["margin"] for e in r["stages"] if e["rule"] == "Back" and not e["virtual"]]
    gs = [e for e in r["stages"] if e["rule"] == "Guard" and not e["virtual"]]
    print(f"  Back pins {len(backs)}: min {min(backs)}, median {sorted(backs)[len(backs)//2]}")
    print(f"  Guard pins {len(gs)}: min entry {min(e['entry'] for e in gs if e['entry'] is not None)}, min exit {min(e['exit'] for e in gs if e['exit'] is not None)}")
    ms = [m["margin"] for m in r["multis"] if m["margin"] is not None]
    print(f"  delay-line pins {len(r['multis'])}: min contiguity margin {min(ms)}")
    print(f"  merges {len(r['merges'])}: certified {sum(m['ok'] for m in r['merges'])}")
    Ws = sorted((w, j) for j, w in r["W"].items() if w is not None)
    print(f"  per-window bound: every real stage fires at most once per W; min W {Ws[0][0]} ps ({Ws[0][1]}), median {Ws[len(Ws)//2][0]}, max {Ws[-1][0]}")
    print(f"    => a full 4-phase handshake of the fastest stage takes >= {2*Ws[0][0]} ps ({1e6/(2*Ws[0][0]):.0f} MHz bound)")
