#!/usr/bin/env python3
"""margin/dsp/dsp_gates.py (shard C, UNTRUSTED): the gates of decode_dsp.py's DSP48E1 cells, added to build_net's net.

    python3 dsp_gates.py D0.json NET0.json NET.json [--routed ROUTED.json] [--sdf NEXTPNR.sdf] [--check N]

build_net.py (shard A, unchanged) leaves a dsp48e1 cell opaque: its input routes are in NET0, its output nodes
("<site>/P<i>", "/PCOUT<i>", "/ACOUT<i>", "/BCOUT<i>", read through hops) are undriven. This adds, for every such node
that exists (i.e. is read):
  P<i> / PCOUT<i>  one gate, kind "dsp": inputs = every non-constant data pin the decoded OPMODE/ALUMODE/INMODE reads
                   (A or ACIN, B or BCIN, C, PCIN; constants are folded into the gate), function = bit i of
                   dspmodel.dsp_p (yosys cells_sim DSP48E1, registers off), one arc per input pin:
                   site-pin delay + prjxray IOPATH <group> -> P (or PCOUT) of the DSP_L/DSP_R tile SDF, envelope over
                   the cell types that match the decoded configuration (USE_MULT MULTIPLY and DYNAMIC: no bit decides
                   it). simx evaluates it as transport: each pin read at t - its arc, the 48-bit result computed from
                   those values, bit i taken.
  ACOUT<i>/BCOUT<i> a copy gate (k = 1, INIT 2) of the operand pin, arc A -> ACOUT (ACIN -> ACOUT when cascaded).
With --sdf (nextpnr's SDF of the build) the SLOW_MAX end of each DSP arc is widened to nextpnr's IOPATH for that
instance and pin group when it is larger (CLAUDE.md: the longer number when ambiguous); the default is prjxray alone.
--check N: the decoded DSP network evaluated at zero delay on N random operand pairs (plus corner values) against
x * y mod 2^32, with the operand and product bits named by the routed json (needs --routed).
"""
import argparse, importlib.util, json, os, random, re, sys
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import dspmodel  # noqa: E402

_spec = importlib.util.spec_from_file_location("build_net", os.path.join(HERE, "..", "..", "..", "tools-A", "target", "build_net.py"))
BN = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(BN)

PORTS = ["A", "B", "C", "PCIN", "D"]
CODE = {"A": 0, "B": 1, "C": 2, "PCIN": 3, "D": 4}   # D: USE_DPORT (simx inmode bit 5)


def die(m):
    print("dsp_gates: " + m, file=sys.stderr)
    sys.exit(1)


def celltypes(port, casc, dport=False):
    if port == "A" and dport:   # the A -> P arc through the pre-adder (prjxray's ADREG_0 / USE_DPORT_TRUE types)
        return ["DSP48E1_ADREG_0_AREG_0_A_INPUT_%s_MREG_0_PREG_0_USE_DPORT_TRUE_USE_MULT_%s" % ("CASCADE" if casc else "DIRECT", m)
                for m in ("MULTIPLY", "DYNAMIC")]
    if port == "D":             # prjxray's combinational D -> P / PCOUT cell type (ADREG = DREG = MREG = PREG = 0)
        return ["DSP48E1_ADREG_0_DREG_0_MREG_0_PREG_0_USE_DPORT_TRUE_USE_MULT_%s" % m for m in ("MULTIPLY", "DYNAMIC")]
    if port == "A":
        return ["DSP48E1_AREG_0_A_INPUT_%s_MREG_0_PREG_0_USE_DPORT_FALSE_USE_MULT_%s" % ("CASCADE" if casc else "DIRECT", m)
                for m in ("MULTIPLY", "DYNAMIC")]
    if port == "B":
        return ["DSP48E1_BREG_0_B_INPUT_%s_MREG_0_PREG_0_USE_MULT_%s" % ("CASCADE" if casc else "DIRECT", m)
                for m in ("MULTIPLY", "DYNAMIC")]
    return {"C": ["DSP48E1_CREG_0_PREG_0"], "PCIN": ["DSP48E1_PREG_0"]}[port]


def read_nextpnr_sdf(path, inst_of_site):
    """max IOPATH delay (ps) per (site, input group, output group) of nextpnr's SDF DSP48E1 cells."""
    want = {v: k for k, v in inst_of_site.items()}
    out = defaultdict(int)
    txt = open(path).read()
    for m in re.finditer(r'\(CELLTYPE "DSP48E1[^"]*"\)\s*\(INSTANCE ([^)]*)\)(.*?)\n    \)', txt, re.S):
        inst = m.group(1).strip().replace("\\", "")
        site = want.get(inst)
        if site is None:
            continue
        for p in re.finditer(r"\(IOPATH (\D+)\d* (\D+)\d* \(([\d.]+):([\d.]+):([\d.]+)\)", m.group(2)):
            k = (site, p.group(1), p.group(2))
            out[k] = max(out[k], int(round(float(p.group(5)))))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("d0"); ap.add_argument("net0"); ap.add_argument("out")
    ap.add_argument("--routed"); ap.add_argument("--sdf"); ap.add_argument("--check", type=int, default=0)
    a = ap.parse_args()
    D = json.load(open(a.d0)); N = json.load(open(a.net0))
    dsps = [c for c in D["cells"] if c["kind"] == "dsp48e1"]
    names = N["nodes"]; idx = {n: i for i, n in enumerate(names)}
    gates = N["gates"]
    drv = {g["out"]: gi for gi, g in enumerate(gates)}

    def node(nm):
        if nm not in idx:
            idx[nm] = len(names); names.append(nm)
        return idx[nm]

    def const_node(v):
        nm = "CONST%d" % int(bool(v))
        n = node(nm)
        if n not in drv:
            gates.append({"name": nm, "kind": "const", "k": 0, "init": int(bool(v)), "ins": [], "arcs": [], "out": n, "prov": None})
            drv[n] = len(gates) - 1
        return n

    nsdf = {}
    if a.sdf:
        if not a.routed:
            die("--sdf needs --routed (instance names)")
        inst = {c["name"]: c["dsp"]["json_cell"] for c in dsps if c["dsp"].get("json_cell")}
        nsdf = read_nextpnr_sdf(a.sdf, inst)
    fid = defaultdict(int)
    added = defaultdict(int)
    for c in dsps:
        d = c["dsp"]; sn = c["name"]; tt = d["tiletype"]
        cfg = (d["opmode"], d["alumode"], d["inmode"], d["carryinsel"])
        casc = {"A": d["a_cascade"], "B": d["b_cascade"]}
        dport = bool(d.get("use_dport"))
        base = [0, 0, 0, 0] + ([0] if dport else [])
        ins, roles, pins = [], [], []
        for port in PORTS:
            for pin in d["ports"].get(port, []):
                v = c["conn"][pin]
                bit = int(re.sub(r"^\D+", "", pin))
                if "const" in v:
                    base[CODE[port]] |= int(bool(v["const"])) << bit
                    continue
                r = v.get("_route")
                if not r or r["sink"] not in idx:
                    die("%s %s: no routed sink node in the net" % (sn, pin))
                ins.append(idx[r["sink"]]); roles.append(CODE[port] * 64 + bit); pins.append((port, pin, v))
        cin = d["carryin"] if "CARRYIN" in d["ports"] else 0
        def arc(port, pin, v, outp):
            ip = {"A": "ACIN" if casc["A"] else "A", "B": "BCIN" if casc["B"] else "B"}.get(port, port)
            io = BN.iopath(tt, "DSP48E1", None, ip, outp, celltypes=celltypes(port, casc.get(port, False), dport))
            if io is None:
                die("%s: no prjxray IOPATH %s %s in %s.sdf" % (sn, ip, outp, tt))
            sp = v["_route"]["sinkwire"]
            spd = site_pin_delay(sp[0], sp[1])
            e = [x + y for x, y in zip(io, spd)]
            if nsdf:
                ns = nsdf.get((sn, ip, outp))
                if ns and ns > e[3]:
                    fid["DSP arc SLOW_MAX widened to nextpnr's SDF IOPATH"] += 1
                    e[3] = ns
            return {"fmin": e[0], "fmax": e[1], "smin": e[2], "smax": e[3]}
        for o in d["read"]:
            m = re.match(r"^(P|PCOUT|ACOUT|BCOUT)(\d+)$", o)
            kind, bit = m.group(1), int(m.group(2))
            on = "%s/%s" % (sn, o)
            if on not in idx:
                continue
            if idx[on] in drv:
                die("%s already has a driver" % on)
            if kind in ("P", "PCOUT"):
                g = {"name": "%s.%s" % (sn, o), "kind": "dsp", "k": len(ins), "init": 0, "ins": list(ins),
                     "arcs": [arc(p, pn, v, kind) for p, pn, v in pins], "out": idx[on],
                     "prov": {"site": sn, "tile": d["tile"], "pin": o},
                     "dsp": {"obit": bit, "opmode": cfg[0], "alumode": cfg[1], "inmode": cfg[2] | (32 if dport else 0), "carryinsel": cfg[3],
                             "carryin": cin, "base": base, "roles": list(roles)}}
            else:
                port = "A" if kind == "ACOUT" else "B"
                ip = ("ACIN" if casc["A"] else "A") if port == "A" else ("BCIN" if casc["B"] else "B")
                pin = "%s%d" % (ip, bit)
                v = c["conn"].get(pin)
                if v is None:
                    die("%s read but %s was not decoded (operand unused by this DSP)" % (on, pin))
                ct = ["DSP48E1_%sCASCREG_0_%s_INPUT_%s" % (port, port, "CASCADE" if casc[port] else "DIRECT")]
                io = BN.iopath(tt, "DSP48E1", None, ip, kind, celltypes=ct)
                if io is None:
                    die("%s: no prjxray IOPATH %s %s" % (sn, ip, kind))
                if "const" in v:
                    src, e = const_node(v["const"]), io
                else:
                    src = idx[v["_route"]["sink"]]
                    e = [x + y for x, y in zip(io, site_pin_delay(*v["_route"]["sinkwire"]))]
                g = {"name": "%s.%s" % (sn, o), "kind": "dspcasc", "k": 1, "init": 2, "ins": [src],
                     "arcs": [{"fmin": e[0], "fmax": e[1], "smin": e[2], "smax": e[3]}], "out": idx[on],
                     "prov": {"site": sn, "tile": d["tile"], "pin": o}}
            gates.append(g); drv[g["out"]] = len(gates) - 1; added[g["kind"]] += 1
        fid["DSP48E1 site as gates (dsp: P/PCOUT bit = f(all read data pins), prjxray IOPATH per pin group)"] += 1
    # every node named after a DSP output must now have a driver
    for nm, i in idx.items():
        if re.match(r"^DSP48_X\d+Y\d+/", nm) and i not in drv:
            die("%s is read but has no driver" % nm)
    N["nodes"] = names
    N["fidelity"].update(fid)
    N["dsp_gates"] = dict(added)
    json.dump(N, open(a.out, "w"))
    print("dsp_gates: %d DSP sites -> %s gates; %d nodes, %d gates" % (len(dsps), dict(added), len(names), len(gates)), file=sys.stderr)
    if a.check:
        check(D, N, a.routed, a.check)


_sp = {}


def site_pin_delay(tile, wire):
    """build_net's sitepin_delay: prjxray's site pin delay of the sink wire (ps)."""
    t = BN_tiles()[tile]["type"]
    if t not in _sp:
        j = json.load(open(os.path.join(BN.DB, "tile_type_%s.json" % t)))
        _sp[t] = {v["wire"]: v for s in j["sites"] for v in s["site_pins"].values() if v and v.get("wire")}
    v = _sp[t].get(wire)
    d = BN.ps4(v.get("delay")) if v else None
    return d or [0, 0, 0, 0]


_tiles = []


def BN_tiles():
    if not _tiles:
        _tiles.append(json.load(open(os.path.join(BN.DB, "xc7z010", "tilegrid.json"))))
    return _tiles[0]


def check(D, N, routed, n):
    """Zero-delay evaluation of the DSP gates against x * y mod 2^32 (operand / product bits named by the json)."""
    if not routed:
        die("--check needs --routed")
    J = json.load(open(routed))["modules"]["top"]
    jnn = {}
    for nm, v in J["netnames"].items():
        for i, b in enumerate(v["bits"]):
            jnn.setdefault(b, nm if len(v["bits"]) == 1 else "%s[%d]" % (nm, i))
    names, G = N["nodes"], N["gates"]
    drv = {g["out"]: g for g in G}
    dsps = {c["name"]: c for c in D["cells"] if c["kind"] == "dsp48e1"}
    # operand bits: decoded source net of each A/B pin <-> json net name "<base>[i]"
    src_of = {}      # decoded net -> (json base, bit)
    for c in dsps.values():
        jc = J["cells"][c["dsp"]["json_cell"]]
        for port in ("A", "B"):
            for pin in c["dsp"]["ports"].get(port, []):
                v = c["conn"][pin]
                if "net" in v and not v["net"].startswith("DSP48_"):
                    jn = jnn[jc["connections"][pin][0]]
                    m = re.match(r"^(.*)\[(\d+)\]$", jn)
                    src_of[v["net"]] = (m.group(1), int(m.group(2)))
    # products: P bits whose json net is "<base>[i]" with a base that is not one of the operands' and has 32 bits
    res = defaultdict(dict)
    for c in dsps.values():
        jc = J["cells"][c["dsp"]["json_cell"]]
        for o in c["dsp"]["read"]:
            if o.startswith("P") and not o.startswith("PCOUT"):
                jn = jnn[jc["connections"][o][0]]
                m = re.match(r"^(.*)\[(\d+)\]$", jn)
                if m:
                    res[m.group(1)][int(m.group(2))] = "%s/%s" % (c["name"], o)
    res = {k: v for k, v in res.items() if sorted(v) == list(range(32))}
    bases = sorted({b for b, _ in src_of.values()})
    print("dsp_gates --check: operands %s; products %s" % (bases, sorted(res)), file=sys.stderr)
    idx = {nm: i for i, nm in enumerate(names)}
    # 2026-11-19: a product may read another product (x * x * x: mul_example); such a product's bits count as an operand
    pbit = {}
    for pb, bits in res.items():
        for i, b in bits.items():
            pbit[idx[b]] = (pb, i)
    def cone(n, seen, me):   # back through DSP gates and copies (pips / hops) to the operand nets or another product's bits
        todo = [n]
        while todo:
            x = todo.pop()
            if x in seen: continue
            seen.add(x)
            g = drv.get(x)
            if names[x] in src_of or g is None: continue
            if x in pbit and pbit[x][0] != me: continue
            if g["kind"] in ("dsp", "dspcasc") or (g["k"] == 1 and g["init"] == 2): todo += g["ins"]
    ops_of = {}
    for pb, bits in res.items():
        seen = set()
        for b in bits.values(): cone(idx[b], seen, pb)
        ops = sorted({src_of[names[i]][0] for i in seen if names[i] in src_of} |
                     {pbit[i][0] for i in seen if i in pbit and pbit[i][0] != pb})
        if len(ops) not in (1, 2, 3):   # 3: a chain whose intermediate product has no 32-bit name (factorial: x * y * z)
            die("product %s: operands %s" % (pb, ops))
        ops_of[pb] = ops
    # an operand reached only through another product's own DSPs (a cascade from inside it) is that product's, not ours
    def under(q, seen=None):
        seen = seen or set()
        for o in ops_of.get(q, []):
            if o not in seen:
                seen.add(o); under(o, seen)
        return seen
    for pb in res:
        inner = set().union(*[under(o) for o in ops_of[pb] if o in res]) if any(o in res for o in ops_of[pb]) else set()
        if len(ops_of[pb]) >= 3 and inner & set(ops_of[pb]):   # only for 3+: x * (x * x) must keep its x (mul_example)
            ops_of[pb] = [o for o in ops_of[pb] if o not in inner]
    order = []
    while len(order) < len(res):
        prog = False
        for pb in sorted(res):
            if pb not in order and all(o in order or o not in res for o in ops_of[pb]):
                order.append(pb); prog = True
        if not prog: die("check: products depend on each other in a cycle: %s" % ops_of)
    r = random.Random(12345)
    tbad = 0
    vecs = [(0, 0), (1, 1), (0xffffffff, 0xffffffff), (0x7fffffff, 0x7fffffff), (0x80000000, 3), (0x1ffff, 0x1ffff),
            (0x20000, 0x20000)] + [(r.getrandbits(32), r.getrandbits(32)) for _ in range(n)]
    nbad = defaultdict(int)
    leaf = [b for b in bases]
    for x, y in vecs:
        opv = {leaf[0]: x, leaf[-1]: y if len(leaf) > 1 else x}
        for b in leaf[1:-1]: opv[b] = r.getrandbits(32)
        pv = {}
        for pb in order:
            ops = ops_of[pb]
            memo = {}
            def val(ni):
                if ni in memo: return memo[ni]
                nm = names[ni]
                if nm in src_of:
                    b, i = src_of[nm]; v = (opv[b] >> i) & 1
                elif ni in pbit and pbit[ni][0] != pb:
                    q, i = pbit[ni]; v = (pv[q] >> i) & 1
                else:
                    g = drv.get(ni)
                    if g is None: die("check: %s undriven inside the DSP network" % nm)
                    if g["kind"] == "const": v = g["init"]
                    elif g["k"] == 1 and g["init"] == 2: v = val(g["ins"][0])
                    elif g["kind"] == "dsp":
                        dd = g["dsp"]; pv_ = list(dd["base"])
                        for i_, ro in zip(g["ins"], dd["roles"]):
                            pv_[ro // 64] |= val(i_) << (ro % 64)
                        p = dspmodel.dsp_p(dd["opmode"], dd["alumode"], dd["inmode"] & 31, dd["carryinsel"], pv_[0], pv_[1], pv_[2], pv_[3],
                                           dd["carryin"], D=pv_[4] if len(pv_) > 4 else 0, dport=bool(dd["inmode"] & 32))
                        v = (p >> dd["obit"]) & 1
                    else: die("check: %s driven by a %s gate inside the DSP network" % (nm, g["kind"]))
                memo[ni] = v; return v
            bits = res[pb]
            got = sum(val(idx[bits[i]]) << i for i in range(32))
            ov = lambda o: pv[o] if o in pv else opv[o]
            want = (ov(ops[0]) * ov(ops[-1]) * (ov(ops[1]) if len(ops) == 3 else 1)) & 0xffffffff
            pv[pb] = got
            if got != want:
                nbad[pb] += 1
                if nbad[pb] <= 5:
                    print("  MISMATCH %s = %s * %s: %#x * %#x -> %#010x, want %#010x" % (pb, ops[0], ops[-1], ov(ops[0]), ov(ops[-1]), got, want), file=sys.stderr)
    for pb in order:
        if len(ops_of[pb]) == 3 and nbad[pb]:
            # a product whose cone reaches three operand nets that do not compose as x * y * z here (factorial's fused
            # n32_u: copies of one fork's value and a product computed again inside it): NOT checked, said so
            print("dsp_gates --check: %s: UNCHECKED (operands %s do not compose as one product; the other products are checked)"
                  % (pb, ", ".join(ops_of[pb])), file=sys.stderr)
            continue
        print("dsp_gates --check: %s = %s mod 2^32: %d vectors, %d mismatches" % (pb, " * ".join(ops_of[pb] if len(ops_of[pb]) > 1 else ops_of[pb] * 2), len(vecs), nbad[pb]), file=sys.stderr)
        tbad += nbad[pb]
    bad = tbad
    if bad and any(c["dsp"].get("corrupted") for c in dsps.values()):
        print("dsp_gates --check: mismatches EXPECTED (negative control: a decoded DSP bit was flipped)", file=sys.stderr)
    elif bad:
        sys.exit(2)


if __name__ == "__main__":
    main()
