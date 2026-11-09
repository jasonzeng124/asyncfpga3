#!/usr/bin/env python3
"""analyze.py WORK ROUTED_JSON KERNEL_V MARKER [--out DIR] -- one iteration's time, from the full-stack trace.

WORK: a build_ps.sh ... bit run dir that also ran dump.v (dump.vcd).  ROUTED_JSON: the route's nextpnr JSON
(cell names by BEL).  KERNEL_V: the bdc kernel Verilog the route was built from (instance -> bundled data nets).
MARKER: a kernel net (e.g. n8_u_req) whose rises mark iterations.

1. The critical cycle: walk causes back (trace.py) from a steady-state rise of MARKER until the walk reaches the
   previous rise.  It must close on the marker itself and every hop must be exact (slack 0); otherwise stop.
2. Split it into categories (categorize.py), per stage (kernel instance) and in total.
3. Self-check: the categories sum to the measured period (to the ps; the gate is 1%).
Writes DIR/cycle_hops.tsv, DIR/stages.tsv, DIR/delays.tsv, DIR/summary.txt.
"""
import sys, os, re, collections, statistics as st
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from trace import Net, load_vcd, Trace
from categorize import bel_names, load_names, logical, role, delay_inst

a = [x for x in sys.argv[1:] if not x.startswith("--")]
W, RJ, KV, MK = a[:4]
OUT = sys.argv[sys.argv.index("--out") + 1] if "--out" in sys.argv else W + "/itercost"
if OUT in a: a.remove(OUT)
os.makedirs(OUT, exist_ok=True)
PRIMS = os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../cells/gls/prims.v")
N = Net(W, PRIMS); ev = load_vcd(W + "/dump.vcd"); T = Trace(N, ev)
bels = bel_names(RJ); cn = load_names(W)
P = "bridge_i.udut."

# ---- bundled data per delay instance, from the kernel Verilog --------------------------------------------------
src = open(KV).read()
ports = {}
for m in re.finditer(r"^\s*(\w+)\s*(?:#\((.*?)\))?\s+(u\w+)\s*\((.*?)\);", src, re.S | re.M):
    typ, par, inst, body = m.groups()
    ports[inst] = (typ, par or "", dict(re.findall(r"\.(\w+)\(([^()]*?)\)", body)))
# routed-JSON net aliases -> the name nets.map uses
import json
j = json.load(open(RJ)); mods = j["modules"]
top = [k for k in mods if mods[k].get("attributes", {}).get("top")] or list(mods)
bit2name, alias = {}, {}
for k, v in mods[top[0]]["netnames"].items():
    for i, b in enumerate(v["bits"]):
        nm = k if len(v["bits"]) == 1 else "%s[%d]" % (k, i)
        alias[nm] = b
        if nm in N.inv: bit2name[b] = N.inv[nm]


def nets_of(name, w=None):
    """kernel signal name (no prefix) -> list of n* nets (all its bits)"""
    out = []
    for nm in [P + name] + [P + name + "[%d]" % i for i in range(64)]:
        if nm in alias and alias[nm] in bit2name: out.append(bit2name[alias[nm]])
    return sorted(set(out))


def bundled(inst):
    """delay instance path (e.g. ucmpi1, ulink_n12__1.many.stage[1].u) -> data nets its request certifies"""
    base = inst.split(".")[0]
    if base not in ports: return None, "?"
    typ, par, pc = ports[base]
    m = re.match(r".*many\.stage\[(\d+)\]\.u$", inst)
    if m:
        k = int(m.group(1)); n = int(re.search(r"\.N\((\d+)\)", par).group(1)); w = int(re.search(r"\.W\((\d+)\)", par).group(1))
        if k + 1 < n:
            return sorted(set(x for i in range((k + 1) * w, (k + 2) * w) for x in nets_of(base + ".many.dat[%d]" % i)[:1]
                              if x)) or nets_of(base + ".many.dat"), "stage%d dat" % k
    for p in ("data_out", "z_data", "index"):
        if p in pc and pc[p].strip():
            nm = re.sub(r"\[.*\]$", "", pc[p].strip())
            got = nets_of(nm)
            if not got and nm.endswith("_data"):        # aliased away: a fork shares one data net with its outputs
                ch = nm[:-5]
                for fi, (ft, fpar, fpc) in ports.items():
                    if ft == "bd_fork" and fpc.get("req", "").strip() == ch + "_req":
                        for o in re.findall(r"(\w+)_req", fpc.get("req_out", "")):
                            got += nets_of(o + "_data")
                got = sorted(set(got))
            return got, "%s=%s" % (p, nm)
    return [], "none"


def settle(nets, t_lo, t_hi):
    """last arrival (edge + wire to each load) of any edge of `nets` with edge time in (t_lo, t_hi]"""
    best = None
    for n in nets:
        for t, v in ev.get(n, []):
            if t_lo < t <= t_hi:
                for _, _, D in N.loads.get(n, []):
                    if best is None or t + D > best: best = t + D
    return best


# ---- 1. the critical cycle ---------------------------------------------------------------------------------------
m = N.inv[P + MK]
rises = [t for t, v in ev[m] if v == "1"]
pers = [b - a for a, b in zip(rises, rises[1:])]
mode = collections.Counter(pers).most_common(1)[0][0]
k = len(rises) * 3 // 4
while pers[k - 1] != mode: k -= 1
hops, end = T.chain(m, rises[k], stop=lambda n, t: t <= rises[k - 1])
closes = end[1] == m and end[2] == rises[k - 1]
period = rises[k] - rises[k - 1]
bad = [h for h in hops if h["slack"] != 0]
summ = []
summ.append("marker %s: %d rises, period histogram %s" % (MK, len(rises), sorted(collections.Counter(pers).items())))
summ.append("cycle: %d hops, period %d ps, closes on the marker: %s, inexact hops: %d" % (len(hops), period, closes, len(bad)))
if not closes or bad:
    open(OUT + "/summary.txt", "w").write("\n".join(summ) + "\nNOT A CYCLE: stop\n"); print("\n".join(summ)); sys.exit(1)
hops = hops[::-1]

# ---- 2. categories -----------------------------------------------------------------------------------------------
for h in hops:
    h["lname"] = logical(h["cell"], h["port"], cn, bels)
    h["role"] = role(h["lname"])
    h["dt"] = h["tout"] - h["t"]
    nm = h["lname"][len(P):] if h["lname"].startswith(P) else h["lname"]
    h["stage"] = nm.split(".")[0]
    h["ctl"] = h["role"] != "logic"
    h["fall"] = h["edge"] == "0" and h["ctl"]
# delay instance runs on the cycle (consecutive hops through one instance, rising)
runs, cur = [], None
for i, h in enumerate(hops):
    if h["role"] == "delay" and not h["fall"]:
        di = delay_inst(h["lname"])
        if cur and cur["inst"] == di and cur["end"] == i - 1: cur["end"] = i; cur["d"] += h["dt"]
        else:
            cur = dict(inst=di, start=i, end=i, d=h["dt"], t_a=h["t"]); runs.append(cur)
    else: cur = None
cat = collections.Counter(); stage = collections.defaultdict(collections.Counter); rtz_by = collections.Counter()
for h in hops:
    s = h["stage"]
    if h["fall"]:
        cat["rtz"] += h["dt"]; stage[s]["rtz"] += h["dt"]; rtz_by[h["role"]] += h["dt"]
    elif h["role"] == "delay": pass                       # split below
    elif h["role"] == "logic":
        cat["logic"] += h["dt"]; stage[s]["logic"] += h["dt"]
    else:
        cat["routing"] += h["wire"]; cat["handshake"] += h["arc"]
        stage[s]["routing"] += h["wire"]; stage[s]["handshake"] += h["arc"]
drows = []
for r in runs:
    inst, kind = r["inst"]; t_a = r["t_a"]; t_b = hops[r["end"]]["tout"]
    nets, what = bundled(inst) if kind != "uack" else ([], "ack delay (no data)")
    s = settle(nets or [], t_a - period // 2, t_b) if nets else None
    lg = 0 if s is None else max(0, min(s - t_a, r["d"]))
    ex = r["d"] - lg
    cat["logic"] += lg; cat["excess"] += ex
    st_ = inst.split(".")[0]; stage[st_]["logic"] += lg; stage[st_]["excess"] += ex
    drows.append((inst, kind, r["end"] - r["start"] + 1, r["d"], lg, ex, "-" if s is None else s - t_a, what, len(nets or [])))
tot = sum(cat.values())

# ---- the same delays over the WHOLE run: worst settle relative to the delay's own input rise ----------------------
def worst_over_run(inst, kind):
    nets, what = bundled(inst) if kind != "uack" else ([], "")
    if not nets: return None, None, 0
    # the instance's output net: the chain element whose output leaves the instance on the cycle
    outs = [h["out"] for h in hops if h["role"] == "delay" and delay_inst(h["lname"]) == (inst, kind)]
    zo = outs[-1]; wl, ml, n = None, None, 0
    for t, v in ev[zo]:
        if v != "1": continue
        ch, _ = T.chain(zo, t, stop=lambda nn, tt: not (N.drv.get(nn) and role(logical(N.drv[nn][0], N.drv[nn][1], cn, bels)) == "delay"
                                                         and delay_inst(logical(N.drv[nn][0], N.drv[nn][1], cn, bels)) == (inst, kind)))
        if not ch: continue
        t_in = ch[-1]["t"]; s = settle(nets, t_in - period // 2, t)
        n += 1
        if s is not None:
            if wl is None or s - t_in > wl: wl = s - t_in
            if ml is None or t - s < ml: ml = t - s
    return wl, ml, n

# ---- outputs -----------------------------------------------------------------------------------------------------
with open(OUT + "/cycle_hops.tsv", "w") as f:
    f.write("i\tt_out_ps\tdt_ps\twire_ps\tarc_ps\tedge\tcategory\trole\tstage\tcell\tnet\n")
    for i, h in enumerate(hops):
        c = "rtz" if h["fall"] else {"delay": "delay", "logic": "logic"}.get(h["role"], "routing+handshake")
        f.write("%d\t%d\t%d\t%d\t%d\t%s\t%s\t%s\t%s\t%s\t%s\n" % (i, h["tout"], h["dt"], h["wire"], h["arc"], "R" if h["edge"] == "1" else "F",
                c, h["role"], h["stage"], h["lname"], N.name.get(h["out"], h["out"])))
with open(OUT + "/delays.tsv", "w") as f:
    f.write("instance\tkind\telements_on_cycle\ttime_on_cycle_ps\tlogic_ps\texcess_ps\tsettle_minus_entry_ps\tbundles\tbits\t"
            "worst_settle_over_run_ps\tmin_margin_over_run_ps\trises_seen\n")
    for d in drows:
        wl, ml, n = worst_over_run(d[0], d[1])
        f.write("%s\t%s\t%d\t%d\t%d\t%d\t%s\t%s\t%d\t%s\t%s\t%d\n" % (d + (("-" if wl is None else wl), ("-" if ml is None else ml), n)))
with open(OUT + "/stages.tsv", "w") as f:
    keys = ("logic", "excess", "handshake", "routing", "rtz")
    f.write("stage\t" + "\t".join(k + "_ps" for k in keys) + "\ttotal_ps\n")
    for s in sorted(stage, key=lambda s: -sum(stage[s].values())):
        f.write("%s\t%s\t%d\n" % (s, "\t".join(str(stage[s][k]) for k in keys), sum(stage[s].values())))
summ.append("stages on the cycle: %d (%s)" % (len(stage), ", ".join(sorted(stage))))
for k in ("logic", "excess", "handshake", "routing", "rtz"):
    summ.append("  %-10s %7d ps  %5.1f%%" % (k, cat[k], 100.0 * cat[k] / period))
summ.append("  sum        %7d ps vs period %d ps: %s (%+.3f%%)" % (tot, period, "OK" if abs(tot - period) <= 0.01 * period else "FAIL",
                                                                 100.0 * (tot - period) / period))
summ.append("  rtz by cell role: %s" % dict(rtz_by))
summ.append("  bound logic + handshake: %.2f ns per iteration" % ((cat["logic"] + cat["handshake"]) / 1e3))
open(OUT + "/summary.txt", "w").write("\n".join(summ) + "\n")
print("\n".join(summ))
