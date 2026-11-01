#!/usr/bin/env python3
"""rt_own.py (audit T4): the auditor's OWN round trip of shard A's decoded target netlist.

    python3 -I rt_own.py NET.json CANON_READBACK.fasm OUT_PREFIX

Imports nothing from formal/. Re-encodes every gate of NET.json as FASM features with the
auditor's own encoder, deriving features from gate STRUCTURE (node names, pin order, INIT),
not from the decoder's `prov` fields, and checks node endpoints with xnode.py's own prjxray
node resolution. Then compares with the canonical read-back (one feature per set bit).

Writes OUT_PREFIX.json (counts, invented list, leftover classes with relevance) and prints a
summary. Exit 0 always (it is a measurement); problems are listed under "problems".
"""
import json
import os
import re
import sys
from collections import Counter, defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from xnode import XDB  # noqa: E402

LS = "ABCD"


def main():
    netp, canon, outp = sys.argv[1:4]
    N = json.load(open(netp))
    names = N["nodes"]
    R = set()
    for line in open(canon):
        t = line.split("#", 1)[0].strip()
        if t:
            # canonical FASM (fasm library) writes bit 0 of a vector without its index
            if re.search(r"\.[A-D]LUT\.INIT$", t):
                t += "[0]"
            R.add(t)
    X = XDB()
    E = Counter()
    problems = defaultdict(list)
    stat = Counter()

    def prob(k, msg):
        stat["problem:" + k] += 1
        if len(problems[k]) < 25:
            problems[k].append(msg)

    # R-side pip index: (tile, dst) -> [src] for every feature that is a pip of its tile
    rpip_dst = defaultdict(list)
    for f in R:
        p = f.split(".")
        if len(p) == 3 and p[0] in X.grid and (p[1], p[2]) in X.tt(X.ttype(p[0]))["_pip"]:
            rpip_dst[(p[0], p[1])].append(p[2])

    lut6 = {}
    gates_by_name = {}
    for g in N["gates"]:
        gates_by_name[g["name"]] = g
    for g in N["gates"]:
        k, nm = g["kind"], g["name"]
        if k == "pip":
            m = re.match(r"^([A-Z0-9_]+_X\d+Y\d+)\.([^.]+)\.([^.]+)$", nm)
            if not m:
                prob("pip name", nm)
                continue
            t, dw, sw = m.groups()
            if g["k"] != 1 or g["init"] != 2 or len(g["ins"]) != 1:
                prob("pip shape", nm)
            tt = X.tt(X.ttype(t))
            if (dw, sw) not in tt["_pip"]:
                prob("pip not in prjxray tile type", nm)
                continue
            # endpoints: own node resolution
            if names[g["ins"][0]] != X.nname(t, sw):
                prob("pip src node", "%s: %s vs own %s" % (nm, names[g["ins"][0]], X.nname(t, sw)))
            if names[g["out"]] != X.nname(t, dw):
                prob("pip dst node", "%s: %s vs own %s" % (nm, names[g["out"]], X.nname(t, dw)))
            if nm in R:
                E[nm] += 1
                stat["pip with feature"] += 1
            else:
                kind = X.ppips(X.ttype(t)).get((dw, sw))
                if kind is None:
                    prob("pip gate with no feature and not a pseudo pip (INVENTED connection)", nm)
                    continue
                stat["pseudo pip (%s)" % kind] += 1
                if kind == "default" and rpip_dst.get((t, dw)):
                    prob("default pseudo pip used although a feature drives its dst", nm)
                if kind == "hint":
                    prob("hint pseudo pip (LUT route-through) used as a wire", nm)
        elif k == "lut6":
            m = re.match(r"^(SLICE_X\d+Y\d+)\.([A-D])LUT\.O6$", nm)
            site, L = m.groups()
            tile, sx, tsite = X.slice_prefix(site)
            if names[g["out"]] != "%s.%s6" % (site, L):
                prob("lut6 out", nm)
            for i in range(6):
                w = tsite["site_pins"]["%s%d" % (L, i + 1)]["wire"]
                if names[g["ins"][i]] != X.nname(tile, w):
                    prob("lut6 pin node", "%s A%d: %s vs own %s" % (nm, i + 1, names[g["ins"][i]], X.nname(tile, w)))
            if not (0 <= g["init"] < 2 ** 64) or g["k"] != 6:
                prob("lut6 shape", nm)
            for b in range(64):
                if g["init"] >> b & 1:
                    E["%s.%s.%sLUT.INIT[%d]" % (tile, sx, L, b)] += 1
            lut6[(site, L)] = g
            stat["lut6"] += 1
        elif k == "lut5":
            stat["lut5"] += 1
        elif k == "hop":
            # which slice output pin is the hop's output node, and which site net feeds it
            on = names[g["out"]]
            t0, w0 = on.split("/", 1)
            pin = None
            for (t, w) in X.node(t0, w0):
                for s in X.tt(X.ttype(t))["sites"]:
                    for pn, v in s["site_pins"].items():
                        if v and v.get("wire") == w and s["type"].startswith("SLICE"):
                            pin = (t, s, pn)
            src = names[g["ins"][0]]
            if pin is None:
                stat["hop from non-slice site"] += 1
                continue
            t, s, pn = pin
            ms = re.match(r"^(SLICE_X\d+Y\d+)\.(\w+)$", src)
            if not ms:
                prob("hop src name", "%s <- %s" % (on, src))
                continue
            site, net = ms.groups()
            tile, sx, tsite = X.slice_prefix(site)
            if tile != t or tsite["x_coord"] != s["x_coord"]:
                prob("hop site mismatch", "%s <- %s" % (on, src))
            L = pn[0]
            i = LS.index(L) if L in LS else -1
            if pn in LS:
                ok = net == L + "6"
            elif pn == L + "Q":
                ok = net == L + "Q"
            elif pn == "COUT":
                ok = net == "CO3"
            elif pn == L + "MUX":
                sel = {L + "6": "O6", L + "5": "O5", "XOR%d" % i: "XOR", "CO%d" % i: "CY", L + "5Q": L + "5Q"}
                if L in "AC":
                    sel["F7A" if L == "A" else "F7B"] = "F7"
                if L == "B":
                    sel["F8"] = "F8"
                ok = net in sel
                if ok:
                    E["%s.%s.%sOUTMUX.%s" % (tile, sx, L, sel[net])] += 1
            else:
                ok = False
            if not ok:
                prob("hop pin/net mismatch", "%s pin %s <- %s" % (on, pn, src))
            stat["hop slice"] += 1
        elif k == "muxf":
            m = re.match(r"^(SLICE_X\d+Y\d+)\.(F7A|F7B|F8)$", nm)
            site, mx = m.groups()
            tile, sx, tsite = X.slice_prefix(site)
            want = {"F7A": (site + ".B6", site + ".A6", "AX"), "F7B": (site + ".D6", site + ".C6", "CX"),
                    "F8": (site + ".F7B", site + ".F7A", "BX")}[mx]
            got = [names[i] for i in g["ins"]]
            sn = X.nname(tile, tsite["site_pins"][want[2]]["wire"])
            if got != [want[0], want[1], sn] or g["init"] != 0xCA or names[g["out"]] != "%s.%s" % (site, mx):
                prob("muxf structure", "%s: %s" % (nm, got))
            stat["muxf"] += 1
        elif k == "carry":
            stat["carry"] += 1
        elif k == "const":
            stat["const"] += 1
        else:
            prob("unknown gate kind", nm)

    # LUT5 halves: same pins, low INIT half
    for g in N["gates"]:
        if g["kind"] == "lut5":
            m = re.match(r"^(SLICE_X\d+Y\d+)\.([A-D])LUT\.O5$", g["name"])
            site, L = m.groups()
            g6 = lut6.get((site, L))
            if g6 is None or g["init"] != (g6["init"] & 0xFFFFFFFF) or g["ins"] != g6["ins"][:5] \
                    or names[g["out"]] != "%s.%s5" % (site, L):
                prob("lut5 vs lut6", g["name"])

    # CARRY4: structure, own truth table, PRECYINIT / CY0 from structure
    carry_sites = defaultdict(dict)
    for g in N["gates"]:
        if g["kind"] == "carry":
            m = re.match(r"^(SLICE_X\d+Y\d+)\.CARRY4\.(CO|O)(\d)$", g["name"])
            carry_sites[m.group(1)][(m.group(2), int(m.group(3)))] = g
    for site, gs in sorted(carry_sites.items()):
        tile, sx, tsite = X.slice_prefix(site)
        if len(gs) != 8:
            prob("carry4 gate count", site)
            continue
        g3 = gs[("CO", 3)]
        ins = [names[i] for i in g3["ins"]]
        CI, CY = ins[0], ins[1]
        S = ins[2:6]
        DI = ins[6:10]
        pinnode = lambda p: X.nname(tile, tsite["site_pins"][p]["wire"])
        # PRECYINIT
        if CI != "CONST0":
            if CI != pinnode("CIN") or CY != "CONST0":
                prob("carry CI", "%s %s %s" % (site, CI, CY))
            precy = "CIN"
        elif CY == "CONST1":
            precy = "C1"
        elif CY == "CONST0":
            precy = "C0"
        else:
            if CY != pinnode("AX"):
                prob("carry CYINIT", "%s %s" % (site, CY))
            precy = "AX"
        E["%s.%s.PRECYINIT.%s" % (tile, sx, precy)] += 1
        for j, L in enumerate(LS):
            if S[j] != "%s.%s6" % (site, L):
                prob("carry S", "%s S%d=%s" % (site, j, S[j]))
            if DI[j] == "%s.%s5" % (site, L):
                E["%s.%s.CARRY4.%sCY0" % (tile, sx, L)] += 1
            elif DI[j] != pinnode(L + "X"):
                prob("carry DI", "%s DI%d=%s" % (site, j, DI[j]))
        for (o, i), g in gs.items():
            nd = i + 1 if o == "CO" else i
            want = [ins[0], ins[1]] + S[:i + 1] + DI[:nd]
            if [names[x] for x in g["ins"]] != want or names[g["out"]] != "%s.%s%d" % (site, "CO" if o == "CO" else "XOR", i):
                prob("carry pins", "%s %s%d" % (site, o, i))
            k = len(want)
            init = 0
            for a in range(2 ** k):
                v = [(a >> q) & 1 for q in range(k)]
                c = v[0] | v[1]
                s = v[2:3 + i]
                di = v[3 + i:]
                # MUXCY chain (UG474): carry out of stage j = S_j ? carry_in_j : DI_j; O_j = S_j xor carry_in_j
                for j in range(i):
                    c = c if s[j] else di[j]
                out = (c if s[i] else di[i]) if o == "CO" else (s[i] ^ c)
                init |= out << a
            if init != g["init"]:
                prob("carry truth table", "%s %s%d" % (site, o, i))

    made = set(E)
    dup = sorted(f for f, n in E.items() if n > 1)
    invented = sorted(made - R)
    left = sorted(R - made)

    # ---- classify leftovers with relevance (auditor's own rules, with per-slice context)
    slice_feats = defaultdict(set)
    for f in R:
        p = f.split(".")
        if len(p) >= 3 and re.match(r"SLICE[LM]_X[01]$", p[1]):
            slice_feats["%s.%s" % (p[0], p[1])].add(".".join(p[2:]))

    def has_ff(pre):
        return any(re.match(r"^[A-D]5?FFMUX\.", x) for x in slice_feats[pre])

    def has_ram(pre):
        return any(re.search(r"RAM|SRL|SMALL|WA[678]USED|WEMUX", x) for x in slice_feats[pre])

    used_carry_pre = set()
    for site in carry_sites:
        tile, sx, _ = X.slice_prefix(site)
        used_carry_pre.add("%s.%s" % (tile, sx))
    cls = Counter()
    ex = defaultdict(list)
    for f in left:
        p = f.split(".")
        pre = "%s.%s" % (p[0], p[1]) if len(p) > 1 else ""
        rest = ".".join(p[2:])
        if len(p) == 3 and p[0] in X.grid and (p[1], p[2]) in X.tt(X.ttype(p[0]))["_pip"]:
            c = "FUNCTIONAL: pip feature not reproduced"
        elif re.match(r"SLICE[LM]_X[01]$", p[1] if len(p) > 1 else ""):
            if re.search(r"LUT\.INIT\[", rest):
                c = "FUNCTIONAL: LUT INIT bit not reproduced"
            elif rest == "NOCLKINV":
                c = "FF config (clock polarity) in a slice WITH FFs" if has_ff(pre) else \
                    "default: NOCLKINV in a slice with no FF (no effect)"
            elif rest == "PRECYINIT.C0":
                c = "FUNCTIONAL: PRECYINIT of a used CARRY4" if pre in used_carry_pre else \
                    "default: PRECYINIT.C0 of an unused CARRY4 (no effect)"
            elif re.match(r"^[A-D]LUT\.DI1MUX\.", rest):
                c = "FUNCTIONAL? DI1MUX in a RAM slice" if has_ram(pre) else \
                    "default: SLICEM DI1MUX (LUTRAM data mux) in a non-RAM slice (no effect)"
            elif re.match(r"^([A-D]5?FF\.(ZINI|ZRST)|FFSYNC|CEUSEDMUX|SRUSEDMUX|[A-D]5?FFMUX\.\w+|CLKINV)$", rest):
                c = "FF config (FF modelled with no gate, output free): " + re.sub(r"^[A-D]", "?", rest).split(".")[0]
            elif re.match(r"^[A-D]OUTMUX\.", rest):
                c = "FUNCTIONAL?: OUTMUX select not reproduced"
            else:
                c = "slice other: " + re.sub(r"^[A-D]", "?", rest)
        elif re.match(r"^(BUFGCTRL|BUFHCE)\.", rest if rest else "") or "BUFGCTRL" in f or "BUFHCE" in f:
            c = "clock buffer config (BUFG/BUFHCE: identity buffers, modelled with no gate)"
        elif re.search(r"GCLK\d+_ENABLE|CK_GCLK\d+_ACTIVE|BUFHCLK\d+_USED|ENABLE_BUFFER\.HCLK", f):
            c = "clock spine enables (clock network)"
        elif re.match(r"^[LR]?IO[BI]", p[0]) or re.match(r"^[LR]IO[BI]3?3?", p[0]):
            c = "IOB/IOI config (2 LED outputs + unused input logic)"
        elif p[0].startswith("CFG_CENTER"):
            c = "configuration tile (BSCAN chain, ALWAYS_ON)"
        else:
            c = "other: " + re.sub(r"_X\d+Y\d+", "", f)
        cls[c] += 1
        if len(ex[c]) < 3:
            ex[c].append(f)

    res = {"target_features": len(R), "produced": len(made), "duplicated": len(dup),
           "invented": len(invented), "invented_list": invented[:200], "left": len(left),
           "left_classes": {k: [n, ex[k]] for k, n in cls.most_common()},
           "stats": dict(stat), "problems": {k: v for k, v in problems.items()}}
    json.dump(res, open(outp + ".json", "w"), indent=1, sort_keys=True)
    with open(outp + ".left.txt", "w") as f:
        f.write("\n".join(left) + "\n")
    print("rt_own: read-back %d features; re-encoded %d (%d duplicated); INVENTED %d; LEFT %d"
          % (len(R), len(made), len(dup), len(invented), len(left)))
    for f in invented[:20]:
        print("  INVENTED", f)
    for k, n in cls.most_common():
        print("  left %6d  %s   e.g. %s" % (n, k, ex[k][0]))
    print("stats:", dict(stat))
    for k, v in problems.items():
        print("PROBLEM %s (%d): %s" % (k, stat["problem:" + k], v[:5]))


if __name__ == "__main__":
    main()
