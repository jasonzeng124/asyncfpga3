#!/usr/bin/env python3
"""gen3 (probe C-11f): physical netlist (fasm2lean3 JSON, from the .bit) + the yosys
netlist nextpnr was given (hierarchical JSON, flattened here) + nextpnr's placement
(routed JSON, used ONLY as a hint for the renaming) -> Lean data + certificates.

    python3 gen3.py PHYS.json SYNTH.json ROUTED.json OUTDIR NS [--chunk N] [--report R.json]

Writes OUTDIR/Rho.lean, OUTDIR/C<k>.lean (instances + one `decide +kernel` theorem
each), OUTDIR/All.lean. Lean namespace Formal.Net.FasmDesign.<NS>.

Logical side: every primitive cell of the flattened yosys netlist, as a
`Formal.Gen.Cell` (same conventions as formal/tools/gen/yosys2lean.py: LUTk INIT as a
Nat, CARRY4 bit-blasted, FD* with a synthetic master net M, BUFG = .buf, INV = LUT1
INIT 1 (stated, see notes), BSCANE2 = .opaque). Nets are fresh ids per flattened bit.

Physical side: fasm2lean3's cells, with conn on dense physical net ids.

Renaming (hint -> checked): a logical cell is paired with the physical BEL nextpnr put
it on (NEXTPNR_BEL); the physical output net gets the logical output net. Physical
outputs nextpnr added (route-through LUTs `...$LUT$n`, constant LUTs
`$PACKER_*_NET$LUT$n`, F7/F8 used as route-throughs, BUFHCE clock row buffers) get the
logical source their function passes (found here by brute force, re-checked in Lean).
"""
import argparse
import itertools
import json
import os
import re
import sys
from collections import defaultdict

PRIM_IN = {
    "LUT6_2": ["I0", "I1", "I2", "I3", "I4", "I5"],
    "MUXF7": ["I0", "I1", "S"], "MUXF8": ["I0", "I1", "S"],
    "CARRY4": ["CI", "CYINIT", "DI", "S"],
    "FDRE": ["C", "CE", "D", "R"], "FDSE": ["C", "CE", "D", "S"],
    "FDCE": ["C", "CE", "CLR", "D"], "FDPE": ["C", "CE", "PRE", "D"],
    "BUFG": ["I"], "INV": ["I"], "OBUF": ["I"],
}
PRIM_OUT = {"LUT6_2": ["O5", "O6"], "MUXF7": ["O"], "MUXF8": ["O"], "CARRY4": ["O", "CO"],
            "FDRE": ["Q"], "FDSE": ["Q"], "FDCE": ["Q"], "FDPE": ["Q"], "BUFG": ["O"],
            "INV": ["O"], "OBUF": ["O"]}
for k in range(1, 7):
    PRIM_IN["LUT%d" % k] = ["I%d" % i for i in range(k)]
    PRIM_OUT["LUT%d" % k] = ["O"]
BSCAN_PINS = ["CAPTURE", "DRCK", "RESET", "RUNTEST", "SEL", "SHIFT", "TCK", "TDI", "TMS", "UPDATE", "TDO"]
FFS = {"FDRE", "FDSE", "FDCE", "FDPE"}


def die(msg):
    print("gen3: ERROR: " + msg, file=sys.stderr)
    sys.exit(1)


# ---------------------------------------------------------------- logical side
def flatten(synth):
    mods = synth["modules"]
    top = [n for n, m in mods.items() if m.get("attributes", {}).get("top")]
    if len(top) != 1:
        die("no unique top: %s" % top)
    top = top[0]
    ctr = itertools.count(10)          # net ids; 0/1 are never used as nets
    parent = {}
    alias_const = {}

    def find(x):
        while parent.get(x, x) != x:
            x = parent[x]
        return x

    def union(x, y):
        if x in ("0", "1") or y in ("0", "1"):
            c, o = (x, y) if x in ("0", "1") else (y, x)
            if o not in ("0", "1"):
                alias_const[find(o)] = c
            return
        rx, ry = find(x), find(y)
        if rx != ry:
            parent[max(rx, ry)] = min(rx, ry)
    cells = []                         # (name, type, params, {pin: [id|'0'|'1']})
    outports = {}

    def is_prim(t):
        return t in PRIM_IN or t in ("BSCANE2", "$scopeinfo") or t not in mods \
            or mods[t].get("attributes", {}).get("blackbox") or not mods[t].get("cells") and t != top

    def inst(mname, prefix, bind, stack=()):
        m = mods[mname]
        local = {}

        def gid(b):
            if b in ("0", "1"):
                return b
            if b in ("x", "z"):
                die("x/z constant in %s" % prefix)
            if b not in local:
                local[b] = bind.get(b) if b in bind else next(ctr)
            return local[b]
        for pn, p in m["ports"].items():
            for b in p["bits"]:
                gid(b)
        for cn, c in sorted(m["cells"].items()):
            t = c["type"]
            if t == "$scopeinfo":
                continue
            if t in mods and not mods[t].get("attributes", {}).get("blackbox") and mods[t].get("cells") is not None \
                    and t not in PRIM_IN and t != "BSCANE2":
                sub = mods[t]
                sb = {}
                for pn, bits in c["connections"].items():
                    for b, sbit in zip(bits, sub["ports"][pn]["bits"]):
                        g = gid(b)
                        if sbit in ("0", "1"):
                            # a submodule port tied to a constant inside: the parent net IS that constant
                            if g not in ("0", "1"):
                                alias_const[g] = sbit
                            continue
                        if sbit in sb and sb[sbit] != g:
                            union(sb[sbit], g)     # two parent nets joined through a pass-through port
                        else:
                            sb[sbit] = g
                inst(t, prefix + cn + ".", sb, stack + ((prefix + cn + ".", t),))
                continue
            if t not in PRIM_IN and t != "BSCANE2":
                die("unknown primitive %s (%s)" % (t, prefix + cn))
            conn = {pn: [gid(b) for b in bits] for pn, bits in c["connections"].items()}
            cells.append((prefix + cn, t, c.get("parameters", {}), conn, stack,
                          c.get("attributes", {}).get("src", "")))
        return local
    loc = inst(top, "", {})

    def canon(b):
        if b in ("0", "1"):
            return b
        r = find(b)
        return alias_const.get(r, r)
    cells = [(n, t, pr, {pn: [canon(b) for b in bits] for pn, bits in conn.items()}, st, src)
             for (n, t, pr, conn, st, src) in cells]
    loc = {k: canon(v) for k, v in loc.items()}
    print("gen3: flatten: %d nets joined through pass-through ports, %d tied to constants"
          % (sum(1 for k in parent if parent[k] != k), len(alias_const)), file=sys.stderr)
    for pn, p in mods[top]["ports"].items():
        if p["direction"] == "output":
            outports[pn] = [loc[b] if b not in ("0", "1") else b for b in p["bits"]]
    return cells, outports, ctr


def pnum(v):
    if isinstance(v, int):
        return v
    if re.fullmatch(r"[01xz]+", v):
        if re.search("[xz]", v):
            die("x/z parameter %r" % v)
        return int(v, 2)
    return int(v)


def lsrc(b):
    if b == "0":
        return ("const", False)
    if b == "1":
        return ("const", True)
    return ("net", b)


def logical_cell(name, t, params, conn, ctr):
    """-> dict(kind, init, conn {GenPin: src}, outs {GenPin: src})"""
    c = {"name": name, "type": t, "conn": {}, "init": 0, "inv": []}
    if t.startswith("LUT") and t != "LUT6_2":
        k = int(t[3])
        c["kind"] = ".lut %d" % k
        c["init"] = pnum(params["INIT"]) % (1 << (1 << k))
        for i in range(k):
            c["conn"]["I%d" % i] = lsrc(conn["I%d" % i][0])
        c["conn"]["O"] = lsrc(conn["O"][0])
    elif t == "INV":
        c["kind"] = ".lut 1"; c["init"] = 1
        c["conn"]["I0"] = lsrc(conn["I"][0]); c["conn"]["O"] = lsrc(conn["O"][0])
    elif t == "LUT6_2":
        c["kind"] = ".lut6_2"; c["init"] = pnum(params["INIT"])
        for i in range(6):
            c["conn"]["I%d" % i] = lsrc(conn["I%d" % i][0])
        for o in ("O5", "O6"):
            if conn.get(o):
                c["conn"][o] = lsrc(conn[o][0])
    elif t in ("MUXF7", "MUXF8"):
        c["kind"] = "." + t.lower()
        for p in ("I0", "I1", "S", "O"):
            c["conn"][p] = lsrc(conn[p][0])
    elif t == "CARRY4":
        c["kind"] = ".carry4"
        c["conn"]["CI"] = lsrc(conn["CI"][0]) if conn.get("CI") else ("const", False)
        c["conn"]["CYINIT"] = lsrc(conn["CYINIT"][0]) if conn.get("CYINIT") else ("const", False)
        for i in range(4):
            c["conn"]["DI%d" % i] = lsrc(conn["DI"][i])
            c["conn"]["S%d" % i] = lsrc(conn["S"][i])
            if conn.get("O") and conn["O"][i] not in ("0", "1"):
                c["conn"]["O%d" % i] = lsrc(conn["O"][i])
            if conn.get("CO") and conn["CO"][i] not in ("0", "1"):
                c["conn"]["CO%d" % i] = lsrc(conn["CO"][i])
    elif t in FFS:
        c["kind"] = "." + t.lower()
        c["init"] = pnum(params.get("INIT", 0))
        for p in PRIM_IN[t]:
            c["conn"][p] = lsrc(conn[p][0])
        q = conn["Q"][0]
        c["conn"]["Q"] = lsrc(q)
        c["conn"]["M"] = ("net", next(ctr))       # synthetic master (H_FF_MS)
        for p in PRIM_IN[t]:
            if pnum(params.get("IS_%s_INVERTED" % p, 0)):
                c["inv"].append(p)
    elif t == "BUFG":
        c["kind"] = '.buf "BUFG"'
        c["conn"]["I"] = lsrc(conn["I"][0]); c["conn"]["O"] = lsrc(conn["O"][0])
    elif t == "BSCANE2":
        c["kind"] = '.opaque "BSCANE2" []'
        for p in BSCAN_PINS:
            if conn.get(p) and conn[p][0] not in ("0", "1") or p == "TDO":
                c["conn"][p] = lsrc(conn[p][0])
    elif t == "OBUF":
        c["kind"] = None
        c["conn"]["I"] = lsrc(conn["I"][0]); c["conn"]["O"] = lsrc(conn["O"][0])
    else:
        die("no model for %s" % t)
    return c


# ---------------------------------------------------------------- semantics (Python mirror of Formal.Gen.Cell.out)
def tb(init, ins):
    a = 0
    for k, v in enumerate(ins):
        a |= int(v) << k
    return bool((init >> a) & 1)


def pout(cell, pin, val):
    """physical cell output, val: pin -> bool (only combinational kinds needed here)."""
    k = cell["kind"]
    if k == "lut6_2":
        ins = [val("I%d" % i) for i in range(6)]
        return tb(cell["init"], ins) if pin == "O6" else tb(cell["init"] & 0xFFFFFFFF, ins[:5])
    if k in ("muxf7", "muxf8"):
        return val("I1") if val("S") else val("I0")
    if k == "buf":
        return val("I")
    return None


# ---------------------------------------------------------------- main
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("phys"); ap.add_argument("synth"); ap.add_argument("routed")
    ap.add_argument("outdir"); ap.add_argument("ns")
    ap.add_argument("--chunk", type=int, default=250)
    ap.add_argument("--report")
    ap.add_argument("--genjson", default=os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "gen", "json"))
    a = ap.parse_args()
    P = json.load(open(a.phys))
    S = json.load(open(a.synth))
    R = list(json.load(open(a.routed))["modules"].values())[0]

    lcells_raw, outports, ctr = flatten(S)
    obufs = {}
    L = {}
    for name, t, params, conn, stack, src in lcells_raw:
        c = logical_cell(name, t, params, conn, ctr)
        c["stack"] = stack
        m = re.search(r"(?:^|/)(rtl/[\w.]+\.v:[\d.\-]+)$", src.split("|")[0])
        c["src"] = m.group(1) if m else None
        if t == "OBUF":
            obufs[c["conn"]["O"]] = c
            continue
        if name in L:
            die("duplicate flattened name %s" % name)
        L[name] = c

    # physical nets -> dense ids
    pcells = {c["name"]: c for c in P["cells"]}
    keys = set()
    for c in P["cells"]:
        for v in c["conn"].values():
            if "net" in v:
                keys.add(v["net"])
        for v in c["outs"].values():
            keys.add(v)
    for v in P["outputs"].values():
        if "net" in v:
            keys.add(v["net"])
    pid = {k: i for i, k in enumerate(sorted(keys))}
    for c in P["cells"]:
        for o, v in c["outs"].items():
            c["conn"].setdefault(o, {"net": v})

    def psrc(v):
        return ("const", v["const"]) if "const" in v else ("net", pid[v["net"]])

    # ---- the hint: logical cell -> (physical cell, physical out pin, logical out pin)
    rho = {}
    pairs = defaultdict(list)       # (pcell name, lname) -> [(ppin, lpin)]
    added = []                      # packer-inserted SLICE_LUTX names (no logical cell)
    unmatched_routed = []
    for n, v in R["cells"].items():
        t = v["type"]
        at = v.get("attributes", {})
        bel = at.get("NEXTPNR_BEL", "")
        if t in ("PAD", "IOB33_OUTBUF", "PSEUDO_VCC", "PSEUDO_GND"):
            continue
        site, b = bel.split("/")[0], bel.split("/")[-1]
        if t == "SLICE_LUTX":
            pc = "%s.%sLUT" % (site, b[0])
            ppin = "O6" if b[1] == "6" else "O5"
            m = re.match(r"^(.*)\$LUT([56])$", n)
            if m and m.group(1) in L and L[m.group(1)]["type"] == "LUT6_2":
                pairs[(pc, m.group(1))].append((ppin, "O" + m.group(2)))
            elif n in L:
                pairs[(pc, n)].append((ppin, "O6" if L[n]["type"] == "LUT6_2" else "O"))
            elif re.search(r"\$LUT\$\d+$", n):
                added.append((pc, ppin, n))
            else:
                unmatched_routed.append(n)
        elif t == "SLICE_FFX":
            pairs[("%s.%s" % (site, b), n)] += [("Q", "Q"), ("M", "M")]
        elif t == "SELMUX2_1":
            pc = "%s.%s" % (site, {"F7AMUX": "F7A", "F7BMUX": "F7B", "F8MUX": "F8"}[b])
            pairs[(pc, n)].append(("O", "O"))
        elif t == "CARRY4":
            pairs[("%s.CARRY4" % site, n)] += [("O%d" % i, "O%d" % i) for i in range(4)] + \
                                               [("CO%d" % i, "CO%d" % i) for i in range(4)]
        elif t == "BUFGCTRL":
            pairs[(site, n)].append(("O", "O"))
        elif t == "BSCAN":
            pairs[(site, n)].append(("BSCAN", "BSCAN"))
        else:
            unmatched_routed.append(n)
    # logical nets that something reads (a cell input, an OBUF)
    lread = set()
    for c in list(L.values()) + list(obufs.values()):
        for q, v in c["conn"].items():
            if q not in ("O", "O5", "O6", "Q", "O0", "O1", "O2", "O3", "CO0", "CO1", "CO2", "CO3") and v[0] == "net":
                lread.add(v[1])
    dangling = []
    for (pc, ln) in list(pairs):
        if ln not in L:
            die("hint names logical %s, not in the flattened yosys netlist" % ln)
        if pc not in pcells:
            outs_l = [v for q, v in L[ln]["conn"].items() if q in ("O", "O5", "O6") and v[0] == "net"]
            if L[ln]["type"] in ("MUXF7", "MUXF8") and not any(v[1] in lread for v in outs_l):
                dangling.append(ln)          # a wide mux whose output nothing reads: unobservable
                del pairs[(pc, ln)]
                continue
            die("hint names physical %s (for %s), which the bits do not contain" % (pc, ln))

    insts = []
    for (pc, ln), outs in sorted(pairs.items()):
        p, l = pcells[pc], L[ln]
        if outs == [("BSCAN", "BSCAN")]:
            for o, v in p["outs"].items():
                pin = o
                if pin not in l["conn"]:
                    die("BSCAN output %s used physically but not logically" % pin)
                rho[pid[v]] = l["conn"][pin]
            insts.append((p, l, [], True))
            continue
        good = []
        for ppin, lpin in outs:
            if lpin not in l["conn"]:
                continue        # e.g. a CARRY4 output yosys left unconnected
            if ppin not in p["outs"]:
                die("%s has no output %s" % (pc, ppin))
            k = pid[p["outs"][ppin]]
            if k in rho and rho[k] != l["conn"][lpin]:
                die("physical net %s renamed twice" % p["outs"][ppin])
            rho[k] = l["conn"][lpin]
            good.append((ppin, lpin))
        insts.append((p, l, good, False))
    matched_l = {ln for (_, ln) in pairs}

    # ---- route-throughs / constants / buffers: physical outputs read by something, not yet renamed
    def renamed_ins(p):
        out = {}
        for q, v in p["conn"].items():
            if q in p["outs"]:
                continue
            s = psrc(v)
            out[q] = s if s[0] == "const" else rho.get(s[1], ("?", s[1]))
        return out
    read_ids = set()
    for c in P["cells"]:
        for q, v in c["conn"].items():
            if q not in c["outs"] and "net" in v:
                read_ids.add(pid[v["net"]])
    for v in P["outputs"].values():
        if "net" in v:
            read_ids.add(pid[v["net"]])
    rt = []
    for _ in range(20):
        progress = False
        for c in P["cells"]:
            if c["kind"] not in ("lut6_2", "muxf7", "muxf8", "buf"):
                continue
            for o, net in c["outs"].items():
                k = pid[net]
                if k in rho or k not in read_ids:
                    continue
                ins = renamed_ins(c)
                if any(s[0] == "?" for q, s in ins.items()
                       if c["kind"] != "lut6_2" or True):
                    # an input not yet renamed: try again later unless it is irrelevant
                    pass
                nets = sorted({s for s in ins.values() if s[0] != "const"}, key=str)
                if any(s[0] == "?" for s in nets) and c["kind"] != "lut6_2":
                    continue
                found = None
                cands = nets + [("const", False), ("const", True)]
                for cand in cands:
                    if cand[0] == "?":
                        continue
                    ok = True
                    for bits in itertools.product([False, True], repeat=len(nets)):
                        env = dict(zip(nets, bits))
                        val = lambda q: (ins[q][1] if ins[q][0] == "const" else env[ins[q]])
                        want = cand[1] if cand[0] == "const" else env[cand]
                        if pout(c, o, val) != want:
                            ok = False
                            break
                    if ok:
                        found = cand
                        break
                if found is None:
                    if not any(s[0] == "?" for s in nets):
                        die("physical %s.%s is read but is neither a logical cell nor a route-through" % (c["name"], o))
                    continue
                rho[k] = found
                rt.append((c, o))
                progress = True
        if not progress:
            break
    rt_by = defaultdict(list)
    for c, o in rt:
        rt_by[c["name"]].append(o)
    for n, os_ in sorted(rt_by.items()):
        insts.append((pcells[n], None, [(o, o) for o in sorted(os_)], False))

    missing = [k for k in read_ids if k not in rho]
    inv_pid = {v: k for k, v in pid.items()}
    if missing:
        die("%d read physical nets have no renaming, e.g. %s" % (len(missing), [inv_pid[k] for k in missing[:8]]))

    # ---- ports
    ports = []
    for port, v in sorted(P["outputs"].items()):
        ob = obufs.get(("net", outports[port][0])) if port in outports else None
        if ob is None:
            die("output %s: no OBUF in the logical netlist" % port)
        ports.append((port, psrc(v), ob["conn"]["I"]))

    # ---- coverage
    unmatched_l = sorted(set(L) - matched_l)
    used_p = {p["name"] for p, _, _, _ in insts}
    unused_p = sorted(set(pcells) - used_p)

    # ---- emit Lean
    os.makedirs(a.outdir, exist_ok=True)
    NS = "Formal.Net.FasmDesign." + a.ns
    MOD = "Formal.Net.FasmDesign." + a.ns

    def lpin(p):
        return "." + p if p in ("I", "I0", "I1", "I2", "I3", "I4", "I5", "O", "O5", "O6", "S", "CI", "CYINIT",
                                "DI0", "DI1", "DI2", "DI3", "S0", "S1", "S2", "S3", "O0", "O1", "O2", "O3",
                                "CO0", "CO1", "CO2", "CO3", "C", "CE", "D", "R", "CLR", "PRE", "G", "GE", "Q", "M") \
            else '(.other "%s")' % p

    def lsrc_s(s):
        return "(.const %s)" % ("true" if s[1] else "false") if s[0] == "const" else "(.net %d)" % s[1]

    def pkind(c):
        k = c["kind"]
        if k == "buf":
            return '(.buf "%s")' % c.get("prim", "BUFGCTRL")
        if k == "opaque":
            return '(.opaque "%s" [])' % c["prim"]
        return "." + k

    def cell_s(name, kind, init, conn, inv):
        return '⟨"%s", %s, 0x%X, false, [%s], [%s]⟩' % (
            name, kind, init, ", ".join("(%s, %s)" % (lpin(q), s) for q, s in conn),
            ", ".join(lpin(q) for q in inv))

    def pcell_s(p):
        conn = [(q, lsrc_s(psrc(v))) for q, v in sorted(p["conn"].items())]
        return cell_s(p["name"], pkind(p), p["init"], conn, p["inv"])

    def lcell_s(l):
        conn = [(q, lsrc_s(s)) for q, s in sorted(l["conn"].items())]
        return cell_s(l["name"], "(%s)" % l["kind"], l["init"], conn, l["inv"])

    def gen_inpins(kind):
        k = kind.strip("()").split()[0].lstrip(".")
        if k == "lut":
            return ["I%d" % i for i in range(int(kind.strip("()").split()[1]))]
        return {"lut6_2": ["I%d" % i for i in range(6)], "muxf7": ["I0", "I1", "S"], "muxf8": ["I0", "I1", "S"],
                "carry4": ["CI", "CYINIT", "DI0", "DI1", "DI2", "DI3", "S0", "S1", "S2", "S3"],
                "fdre": ["C", "CE", "D", "R", "Q", "M"], "fdse": ["C", "CE", "D", "S", "Q", "M"],
                "fdce": ["C", "CE", "CLR", "D", "Q", "M"], "fdpe": ["C", "CE", "PRE", "D", "Q", "M"],
                "buf": ["I"], "opaque": []}[k]

    def supp_of(p, l):
        s = set()
        for q in gen_inpins(p["kind"]):
            ps = psrc(p["conn"][q])
            r = ps if ps[0] == "const" else rho.get(ps[1])
            if r and r[0] == "net":
                s.add(r[1])
        if l:
            for q in gen_inpins(l["kind"]):
                v = l["conn"].get(q)
                if v and v[0] == "net":
                    s.add(v[1])
        return sorted(s)

    # Trie (Braun-style, see Basic.lean); subtrees at depth SPLIT become their own defs
    SPLIT = 6
    subdefs = []

    def trie(d, depth=0, path="r"):
        if not d:
            return ".leaf"
        if depth == SPLIT:
            subdefs.append((path, trie(d, depth + 100, path)))
            return "rho_%s" % path
        v = d.get(0)
        left = {(k - 1) // 2: x for k, x in d.items() if k % 2 == 1}
        right = {(k - 2) // 2: x for k, x in d.items() if k > 0 and k % 2 == 0}
        vs = "(some %s)" % lsrc_s(v) if v is not None else "none"
        return "(.node %s\n  %s\n  %s)" % (vs, trie(left, depth + 1, path + "l"), trie(right, depth + 1, path + "r"))
    sys.setrecursionlimit(100000)
    hdr = ("/-! GENERATED by formal/tools/fasm2lean3/gen3.py (probe C-11f). Do not edit; regenerate.\n"
           "    Physical side: %s.  Logical side: %s. -/\n" % (os.path.basename(a.phys), os.path.basename(a.synth)))
    with open(os.path.join(a.outdir, "Rho.lean"), "w") as f:
        f.write("import Formal.Net.FasmDesign.Basic\n\n" + hdr + "\nnamespace %s\nopen Formal.Gen Formal.Net.FasmDesign\n\n" % NS)
        top = trie(rho)
        for path, body in subdefs:
            f.write("def rho_%s : Trie :=\n  %s\n\n" % (path, body))
        f.write("/-- The renaming, physical net id -> logical source (%d entries). -/\n" % len(rho))
        f.write("def rho : Trie :=\n  %s\n\n" % top)
        f.write("/-- Output ports: (name, physical source, logical source = the OBUF's input). -/\n")
        f.write("def ports : List (String × Src × Src) := [%s]\n\n" % ", ".join(
            '("%s", %s, %s)' % (n, lsrc_s(ps), lsrc_s(ls)) for n, ps, ls in ports))
        f.write("theorem ports_ok : ports.all (fun x => ren rho x.2.1 == some x.2.2) = true := by decide +kernel\n\n")
        f.write("end %s\n" % NS)
    # ---- H_CELLS (INIT half): bind each library-cell primitive of the logical netlist
    # (yosys src = a line of cells/rtl/*.v) to the Formal.Gen cell generated from the
    # same source line (formal/tools/gen/json/<target>.json), same kind and INIT.
    gidx = defaultdict(list)
    gen_targets = set()
    for fn in sorted(os.listdir(a.genjson)):
        if not fn.endswith(".json"):
            continue
        tgt = fn[:-5]
        gj = json.load(open(os.path.join(a.genjson, fn)))
        for mn, m in gj["modules"].items():
            if m.get("attributes", {}).get("blackbox"):
                continue
            for cn, c in m["cells"].items():
                src = c.get("attributes", {}).get("src", "")
                mm = re.search(r"(?:^|/)(rtl/[\w.]+\.v:[\d.\-]+)$", src.split("|")[0])
                if mm and c["type"].startswith("LUT"):
                    ini = pnum(c["parameters"]["INIT"])
                    gidx[mm.group(1)].append((tgt, cn, c["type"], ini))
                    gen_targets.add(tgt)
    bind_of = {}
    unbound = defaultdict(int)
    for idx, (p, l, outs, opq) in enumerate(insts):
        if not l or not l.get("src") or not l["type"].startswith("LUT"):
            continue
        init = l["init"]
        cand = [g for g in gidx.get(l["src"], []) if g[2] == l["type"] and
                (pnum(g[3]) % (1 << (1 << int(g[2][3]))) if g[2] != "LUT6_2" else g[3]) == init]
        if cand:
            bind_of[idx] = sorted(cand)[0]
        else:
            unbound[l["src"]] += 1
    lib_luts = sum(1 for (p, l, o, q) in insts if l and l.get("src") and l["type"].startswith("LUT"))
    chunks = [insts[i:i + a.chunk] for i in range(0, len(insts), a.chunk)]
    for ci, ch in enumerate(chunks):
        with open(os.path.join(a.outdir, "C%03d.lean" % ci), "w") as f:
            f.write("import %s.Rho\nimport Formal.Gen.Cells\n\n" % MOD + hdr + "\nset_option maxRecDepth 20000\n\nnamespace %s.C%03d\nopen Formal.Gen Formal.Net.FasmDesign\n\n" % (NS, ci))
            f.write("def insts : List Inst := [\n")
            rows = []
            for p, l, outs, opq in ch:
                rows.append("  ⟨%s,\n   %s,\n   [%s], [%s]⟩" % (
                    pcell_s(p), ("some " + lcell_s(l)) if l else "none",
                    ", ".join("(%s, %s)" % (lpin(x), lpin(y)) for x, y in outs),
                    ", ".join(str(n) for n in supp_of(p, l))))
            f.write(",\n".join(rows) + "]\n\n")
            f.write("theorem ok : checkAll rho insts = true := by decide +kernel\n\n")
            bl = [(k - ci * a.chunk, bind_of[k]) for k in range(ci * a.chunk, ci * a.chunk + len(ch)) if k in bind_of]
            f.write("/-- H_CELLS, INIT half: (instance index, Formal.Gen target, cell name there). -/\n")
            f.write("def binds : List (Nat × Netlist × String) := [%s]\n\n" % ", ".join(
                '(%d, Formal.Gen.Cells.%s, "%s")' % (k, g[0], g[1]) for k, g in bl))
            f.write("theorem binds_ok : bindsOk insts binds = true := by decide +kernel\n\n")
            f.write("end %s.C%03d\n" % (NS, ci))
    with open(os.path.join(a.outdir, "All.lean"), "w") as f:
        for ci in range(len(chunks)):
            f.write("import %s.C%03d\n" % (MOD, ci))
        f.write("\n" + hdr + "\nnamespace %s\nopen Formal.Gen Formal.Net.FasmDesign\n\n" % NS)
        f.write("/-- Every instance of the routed design (%d). -/\n" % len(insts))
        f.write("def insts : List Inst :=\n  %s\n\n" % " ++\n  ".join("C%03d.insts" % ci for ci in range(len(chunks))))
        f.write("theorem all_ok : checkAll rho insts = true := by\n")
        f.write("  simp only [insts, checkAll, List.append_assoc, List.all_append, Bool.and_eq_true]\n")
        f.write("  exact ⟨%s⟩\n\n" % ", ".join("C%03d.ok" % ci for ci in range(len(chunks))))
        f.write("/-- H_NETLIST for this route (gate level): every instance is sound. -/\n")
        f.write("theorem sound : ∀ i ∈ insts, i.Sound rho := checkAll_sound rho insts all_ok\n\n")
        f.write("/- H_CELLS (INIT half) for this route: every bound library-cell LUT has the kind and\n"
                "INIT of the Formal.Gen cell generated from the same line of cells/rtl (%d of %d). -/\n"
                % (len(bind_of), lib_luts))
        f.write("/-- The chunks: (instances, library-cell bindings), in order. -/\n")
        f.write("def chunks : List (List Inst × List (Nat × Netlist × String)) :=\n  [%s]\n\n" % ",\n   ".join(
            "(C%03d.insts, C%03d.binds)" % (ci, ci) for ci in range(len(chunks))))
        f.write("theorem chunks_insts : (chunks.map Prod.fst).flatten = insts := by\n"
                "  simp only [chunks, insts, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,\n"
                "    List.append_nil, List.append_assoc]\n\n")
        f.write("theorem cells_init : chunks.all (fun c => bindsOk c.1 c.2) = true := by\n")
        f.write("  simp only [chunks, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]\n")
        f.write("  exact ⟨%s⟩\n\n" % ", ".join("C%03d.binds_ok" % ci for ci in range(len(chunks))))
        f.write("theorem binds_count : (chunks.map (fun c => c.2.length)).sum = %d := by decide +kernel\n\n" % len(bind_of))
        f.write("end %s\n" % NS)

    rep = {"lib_luts": lib_luts, "bound": len(bind_of), "unbound_by_src": dict(unbound), "dangling_logical": dangling, "logical_cells": len(L), "logical_matched": len(matched_l), "logical_unmatched": unmatched_l[:50],
           "logical_unmatched_n": len(unmatched_l), "logical_by_type": dict(sorted(
               defaultdict(int, {t: sum(1 for c in L.values() if c["type"] == t) for t in {c["type"] for c in L.values()}}).items())),
           "physical_cells": len(pcells), "physical_by_kind": P["census"],
           "physical_unused": len(unused_p), "physical_unused_ex": unused_p[:30],
           "route_through_outputs": len(rt), "route_through_by_kind": dict(defaultdict(int, {k: sum(1 for c, _ in rt if c["kind"] == k) for k in {c["kind"] for c, _ in rt}})),
           "packer_added_luts": len(added), "routed_unmatched": unmatched_routed[:20],
           "insts": len(insts), "chunks": len(chunks), "rho": len(rho), "ports": len(ports),
           "max_supp": max(len(supp_of(p, l)) for p, l, _, _ in insts)}
    if a.report:
        json.dump(rep, open(a.report, "w"), indent=1)
        # debugging aid: names of the logical nets (first flattened name per id) and physical nets
        lname = {}
        def walkn(mname, prefix, bind):
            pass
        json.dump({"phys": {str(v): k for k, v in pid.items()}}, open(a.report + ".nets.json", "w"))
    print("gen3: %d insts in %d chunks, rho %d, logical %d (%d matched), physical %d (%d unused), %d route-through outputs, max supp %d"
          % (len(insts), len(chunks), len(rho), len(L), len(matched_l), len(pcells), len(unused_p), len(rt), rep["max_supp"]),
          file=sys.stderr)


if __name__ == "__main__":
    main()
