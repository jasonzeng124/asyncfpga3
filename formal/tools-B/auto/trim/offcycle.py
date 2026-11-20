#!/usr/bin/env python3
"""tools-B/auto/trim/offcycle.py CLU_RESULTS_GLOB B_DIR  (shard B, 2026-11-20, untrusted bookkeeping)
For every finished task of research's trim-step requests (e.g. 'results/suite13t_*/*'): its trim record
(auto/trim_<it>.txt, MACRO=LEN), the built lengths (auto/sizes_<it>.vh), the critical cycle after the trim
(auto/cyc_<it>.txt and cyc_<it>_untrimmed.txt: instance rows, either cycle counts) and P / P_untrimmed from result.txt; with formal's steer bounds on the same route
untrimmed and trimmed when B_DIR/<kernel>_<seed>/{u,t/j}/steersafe.txt exist (watch_trim.sh). One row per route:
trimmed macros on / off the critical cycle, P change, min steer kappa_lo before -> after, and the steers whose bound fell
the most."""
import glob, os, re, sys
res, B = sys.argv[1], sys.argv[2]
def inst(macro):
    m = re.sub(r"^BD_SZ_BRIDGE_I_UDUT_", "", macro).lower()
    return re.sub(r"_(uack|sdelay|olink|rlink|folink_uack|short)$", "", m)
def steers(p):
    d = {}
    if not os.path.exists(p): return d
    for l in open(p):
        m = re.match(r"^(\S+)\s.*kappa_lo (-?[0-9.]+)$", l.strip())
        if m: d[m.group(1)] = float(m.group(2))
    return d
print("route | trims on cycle | trims off cycle | P untrimmed -> trimmed | min steer kappa_lo untrimmed -> trimmed | largest drops")
for d in sorted(glob.glob(res)):
    if not os.path.exists(d + "/result.txt"): continue
    l = open(d + "/result.txt").read().strip().splitlines()[-1]
    K, S = l.split()[:2]; it = re.search(r" it=(\d+)", l)
    if not it: continue
    it = it.group(1); tr = d + "/auto/trim_%s.txt" % it
    if not os.path.exists(tr) or not os.path.getsize(tr): continue
    trims = dict(x.strip().split("=") for x in open(tr) if "=" in x)
    built = {m.group(1): int(m.group(2)) for m in re.finditer(r"`define (BD_SZ_\S+) (\d+)", open(d + "/auto/sizes_%s.vh" % it).read())}
    cyc = "".join(open(f).read() for f in (d + "/auto/cyc_%s.txt" % it, d + "/auto/cyc_%s_untrimmed.txt" % it) if os.path.exists(f))
    oncyc = {x.lower() for x in re.findall(r"^\s+(\S+)\s+chain", cyc, re.M)}
    on = ["%s %s->%s" % (inst(k), built.get(k, "?"), v) for k, v in trims.items() if inst(k) in oncyc]
    off = ["%s %s->%s" % (inst(k), built.get(k, "?"), v) for k, v in trims.items() if inst(k) not in oncyc]
    P = re.search(r" P=(\S+)", l); Pu = re.search(r"P_untrimmed=(\S+)", l)
    u = steers("%s/%s_%s/u/steersafe.txt" % (B, K, S)); t = steers("%s/%s_%s/t/j/steersafe.txt" % (B, K, S))
    mu = min(u.values()) if u else None; mt = min(t.values()) if t else None
    drops = sorted(((u[k] - t[k], k) for k in t if k in u), reverse=True)[:2]
    print("%s s%s | %s | %s | %s -> %s | %s -> %s | %s" % (K, S, ", ".join(on) or "-", ", ".join(off) or "-",
          Pu.group(1) if Pu else "?", P.group(1) if P else "?", "%.3f" % mu if mu is not None else "-",
          "%.3f" % mt if mt is not None else "-", "; ".join("%s %.3f->%.3f" % (k.replace("$LUT", "/"), u[k], t[k]) for _, k in drops if _ > 0.01) or "-"))
