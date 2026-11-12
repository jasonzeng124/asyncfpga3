#!/usr/bin/env python3
"""UNTRUSTED (shard C helper, 2026-11-09). One-unit check: the decoded gates of THE target
(gcd_ps e6bb4aec, Formal.Target.NetPS -> net.json via tools-B/target/lean2json.py) at the sites
nextpnr placed a bdc_fused unit's yosys cells compute those cells, for every input.

    python3 check_unit.py ps.json ps.routed.json net.json UNIT [--verbose]

For each combinational yosys cell in the cone of the unit's z_data (the same cone and cell list as
formal/tools/compute/extract.py, i.e. exactly the cells Formal/Gen/Compute/GcdD/<Unit>.lean lists):
  1. routed cell = 'bridge_i.udut.<inst>.<cell>' in nextpnr's routed JSON -> its BEL;
  2. BEL -> decoded gate(s) (A6LUT -> 'S.ALUT.O6' / node S.A6, A5LUT -> S.ALUT.O5 / S.A5, F7AMUX -> S.F7A,
     F8MUX -> S.F8, CARRY4 -> S.CARRY4.O<i>/CO<i> with nodes S.XOR<i>/S.CO<i>);
  3. phi(net) = decoded node of the cell driving the net (unit cells) or, for the unit's input bits and
     constants, the decoded node of the routed driver of the routed net on the corresponding routed pin
     (found via X_ORIG_PORT_*); the two must agree for every use;
  4. every decoded input of the gate is resolved: follow pip copies (k=1, INIT 2), stop at a node in the
     expected set {phi(w) : w input of the cell} or at a constant (VCC/GND wires, CONST0/1); if neither,
     follow a route-through LUT (a LUT gate equal to one of its pins); anything else is a FAIL;
  5. exhaustive comparison over the distinct expected nodes: synth semantics (LUT INIT, MUXF S?I1:I0,
     INV, CARRY4 with c0 = CI | CYINIT) == decoded gate INIT over its resolved inputs.
Output: per-cell lines (with --verbose) and a summary incl. pin permutations, O5 packing, route-throughs,
and the decoded node of every z_data bit and every input bit.
"""
import json, sys, re, itertools, collections

COMB = {"LUT1", "LUT2", "LUT3", "LUT4", "LUT5", "LUT6", "MUXF7", "MUXF8", "INV", "CARRY4"}
OUTP = {"O", "CO"}


def bits_init(s):  # yosys prints MSB first
    return int(s, 2) if set(s) <= {"0", "1"} else int(s)


def main():
    synth, routed, netf, unit = sys.argv[1:5]
    verbose = "--verbose" in sys.argv
    S = json.load(open(synth))["modules"]
    R = json.load(open(routed))["modules"]["top"]["cells"]
    N = json.load(open(netf))
    nodes, gates = N["nodes"], N["gates"]
    nid = {n: i for i, n in enumerate(nodes)}
    gname = {g["name"]: g for g in gates}
    gout = {g["out"]: g for g in gates}

    mods = [k for k in S if k.endswith(f"bdc_fused_{unit}") or f"bdc_fused_{unit}\\" in k]
    assert len(mods) == 1, mods
    m = S[mods[0]]
    insts = [(pm, cn) for pm, v in S.items() for cn, c in v["cells"].items() if c["type"] == mods[0]]
    assert len(insts) == 1, insts
    prefix = "bridge_i.udut." + insts[0][1] + "."
    # cone of z_data (same as extract.py)
    inb = {}
    for p, v in m["ports"].items():
        if v["direction"] == "input" and p.startswith("e") and p.endswith("_data"):
            for k, b in enumerate(v["bits"]):
                inb[b] = (int(p[1:-5]), k)
    drv = {}
    for cn, c in m["cells"].items():
        if c["type"].startswith("$"): continue
        for p, bs in c["connections"].items():
            if p in OUTP:
                for i, b in enumerate(bs):
                    if isinstance(b, int): drv[b] = (cn, p, i)
    order, seen = [], set()

    def visit(b):
        if isinstance(b, str) or b in inb: return
        cn = drv[b][0]
        if cn in seen: return
        seen.add(cn)
        c = m["cells"][cn]
        assert c["type"] in COMB, c["type"]
        for p, bs in sorted(c["connections"].items()):
            if p not in OUTP:
                for bb in bs: visit(bb)
        order.append(cn)
    zs = m["ports"]["z_data"]["bits"]
    for b in zs: visit(b)

    # routed driver map
    rdrv = {}
    for rn, rc in R.items():
        for p, d in rc.get("port_directions", {}).items():
            if d == "output":
                for b in rc["connections"].get(p, []):
                    rdrv[b] = (rn, p)

    def rnode(rn, port):
        """decoded node of a routed cell's output port"""
        rc = R[rn]; bel = rc["attributes"]["NEXTPNR_BEL"]; site, b = bel.split("/")
        t = rc["type"]
        if t == "SLICE_LUTX":
            return f"{site}.{b[0]}{b[1]}"  # A6LUT -> A6, A5LUT -> A5
        if t == "SELMUX2_1":
            return {"F7AMUX": f"{site}.F7A", "F7BMUX": f"{site}.F7B", "F8MUX": f"{site}.F8"}[b]
        if t == "CARRY4":
            return f"{site}.XOR{port[1]}" if port[0] == "O" else f"{site}.CO{port[2]}"
        if t == "SLICE_FFX":
            return f"{site}.{b[0]}{'5' if b[1] == '5' else ''}Q"
        if t == "PSEUDO_GND": return "GND"
        if t == "PSEUDO_VCC": return "VCC"
        return f"{rn}:{port}"

    def rcell(cn):
        return R.get(prefix + cn)

    stats = collections.Counter()
    fails = []
    phi = {}      # synth net bit -> decoded node name
    psi = {}      # (p,k) -> decoded node name (unit input bits)

    def const_of(node):
        g = gout.get(nid[node]) if node in nid else None
        if g is not None and g["k"] == 0: return g["init"] & 1
        return None

    def follow_copies(i):
        while True:
            g = gout.get(i)
            if g is None or not (g["k"] == 1 and g["init"] == 2): return i
            i = g["ins"][0]

    def cof(g):
        """LUT gate g with pins tied to constants folded: returns ('const', v) or ('pin', j) or None"""
        k = g["k"]
        if k > 6 or not (g["name"].endswith(".O6") or g["name"].endswith(".O5")): return None
        cp = {}
        for j, di in enumerate(g["ins"]):
            c = const_of(nodes[follow_copies(di)])
            if c is not None: cp[j] = c
        free = [j for j in range(k) if j not in cp]
        def val(asg):
            a = sum(cp[j] << j for j in cp) + sum(asg[t] << j for t, j in enumerate(free))
            return (g["init"] >> a) & 1
        tab = {asg: val(asg) for asg in itertools.product((0, 1), repeat=len(free))}
        if len(set(tab.values())) == 1: return ("const", next(iter(tab.values())))
        for t, j in enumerate(free):
            if all(v == asg[t] for asg, v in tab.items()): return ("pin", j)
        return None

    def resolve(i, expect):
        path = []
        while True:
            i = follow_copies(i)
            nm = nodes[i]
            if nm in expect: return nm, path
            c = const_of(nm)
            if c is not None: return ("CONST%d" % c), path
            g = gout.get(i)
            if g is None: return None, path + [nm]
            r = cof(g)
            if r is None: return None, path + [nm]
            if r[0] == "const": return ("CONST%d" % r[1]), path + [nm + "(const LUT)"]
            path.append(nm); i = g["ins"][r[1]]

    # pass 1: phi of every unit-cell output from its BEL
    for cn in order:
        rc = rcell(cn)
        if rc is None:
            fails.append((cn, "no routed cell")); continue
        c = m["cells"][cn]
        rmap = {v: k for k, v in rc["attributes"].items() if k.startswith("X_ORIG_PORT_")}
        for p, bs in c["connections"].items():
            if p in OUTP:
                for i, b in enumerate(bs):
                    if not isinstance(b, int): continue
                    lp = f"{p}[{i}]" if c["type"] == "CARRY4" else p
                    rp = rmap.get(lp, "X_ORIG_PORT_?")[len("X_ORIG_PORT_"):]
                    if rp not in rc["connections"]: continue
                    phi[b] = rnode(prefix + cn, rp)
    # pass 2: inputs/constants via routed nets
    def wire_expect(c, rc, p, i, b):
        if b in ("0", "1"): return "CONST" + b
        if isinstance(b, int) and b in phi and b not in inb: return phi[b]
        rmap = {v: k[len("X_ORIG_PORT_"):] for k, v in rc["attributes"].items() if k.startswith("X_ORIG_PORT_")}
        lp = f"{p}[{i}]" if c["type"] == "CARRY4" and p in ("DI", "S") else p
        rp = rmap.get(lp)
        if rp is None or not rc["connections"].get(rp):
            return "CONST0" if b == "0" else "CONST1" if b == "1" else None
        rb = rc["connections"][rp][0]
        if rb not in rdrv: return None
        # follow nextpnr-inserted route-through LUTs ('$LUT$' cells, LUT1 INIT 2) on the routed side
        while True:
            dn, dp = rdrv[rb]; dc = R[dn]
            if dc["type"] == "SLICE_LUTX" and "$LUT$" in dn and dc["attributes"].get("X_ORIG_TYPE") == "LUT1" \
                    and int(dc["parameters"]["INIT"], 2) == 2:
                ip = [k[len("X_ORIG_PORT_"):] for k, v in dc["attributes"].items() if k.startswith("X_ORIG_PORT_") and v == "I0"]
                rb = dc["connections"][ip[0]][0]; continue
            break
        nd = rnode(*rdrv[rb])
        if nd == "GND": return "CONST0"
        if nd == "VCC": return "CONST1"
        return nd

    perm, o5, rts = 0, 0, 0
    for cn in order:
        c = m["cells"][cn]; rc = rcell(cn)
        if rc is None: continue
        t = c["type"]
        if t == "CARRY4":
            ins = [("CI", 0), ("CYINIT", 0)] + [("DI", i) for i in range(4)] + [("S", i) for i in range(4)]
        elif t in ("MUXF7", "MUXF8"):
            ins = [("I0", 0), ("I1", 0), ("S", 0)]
        elif t == "INV":
            ins = [("I", 0)]
        else:
            ins = [(f"I{j}", 0) for j in range(int(t[3]))]
        wires = [c["connections"][p][i] for p, i in ins]
        exp = []
        for (p, i), b in zip(ins, wires):
            e = wire_expect(c, rc, p, i, b)
            if b in inb:
                if e is None: fails.append((cn, f"input {inb[b]} unresolved in routed json")); continue
                if psi.setdefault(inb[b], e) != e: fails.append((cn, f"input {inb[b]}: {psi[inb[b]]} vs {e}"))
            if b in ("0", "1") and e not in ("CONST0", "CONST1"):
                pass  # constant may be a GND/VCC LUT; resolved below
            exp.append(e)
        expect = set(e for e in exp if e and not e.startswith("CONST"))
        # synth evaluation
        def synth(vals, port, idx):
            v = dict(((p, i), x) for (p, i), x in zip(ins, vals))
            if t == "CARRY4":
                cy = v[("CI", 0)] | v[("CYINIT", 0)]; o, co = [], []
                for k in range(4):
                    o.append(v[("S", k)] ^ cy); cy = cy if v[("S", k)] else v[("DI", k)]; co.append(cy)
                return (o if port == "O" else co)[idx]
            if t in ("MUXF7", "MUXF8"): return v[("I1", 0)] if v[("S", 0)] else v[("I0", 0)]
            if t == "INV": return 1 - v[("I", 0)]
            init = bits_init(c["parameters"]["INIT"])
            a = sum(x << j for j, x in enumerate(vals)); return (init >> a) & 1
        rmap = {v: k[len("X_ORIG_PORT_"):] for k, v in rc["attributes"].items() if k.startswith("X_ORIG_PORT_")}
        if t.startswith("LUT") and any(rmap.get(f"I{j}") != f"A{j+1}" for j in range(int(t[3]))): perm += 1
        if t.startswith("LUT") and rc["attributes"]["NEXTPNR_BEL"].endswith("5LUT"): o5 += 1
        for p, bs in c["connections"].items():
            if p not in OUTP: continue
            for idx, b in enumerate(bs):
                if not isinstance(b, int) or b not in phi: continue
                node = phi[b]
                if nid.get(node) is None or nid[node] not in gout:
                    fails.append((cn, f"decoded node {node} missing")); continue
                g = gout[nid[node]]
                res = []
                ok = True
                kk = g["k"]
                for jj, di in enumerate(g["ins"]):
                    r, path = resolve(di, expect)
                    if path: rts += 1
                    if r is None and all(((g["init"] >> a) & 1) == ((g["init"] >> (a ^ (1 << jj))) & 1) for a in range(1 << kk)):
                        stats["pins outside support (shared LUT6_2 pin)"] += 1
                        r = "CONST0"  # the gate does not depend on this pin: any value
                    if r is None:
                        ok = False; fails.append((cn, f"{g['name']} pin {nodes[di]} -> {path} not an expected source")); break
                    res.append(r)
                if not ok: continue
                vars_ = sorted(expect)
                bad = 0
                for asg in itertools.product((0, 1), repeat=len(vars_)):
                    env = dict(zip(vars_, asg)); env["CONST0"] = 0; env["CONST1"] = 1
                    sv = [env[e] if e else None for e in exp]
                    if None in sv: ok = False; break
                    dv = sum(env[r] << j for j, r in enumerate(res))
                    if ((g["init"] >> dv) & 1) != synth(sv, p, idx): bad += 1
                if None in [e for e in exp]:
                    fails.append((cn, f"unresolved expected input {exp}")); continue
                stats["outputs checked"] += 1
                if bad: fails.append((cn, f"{g['name']}: {bad} assignments differ"))
                elif verbose: print(f"ok {t:6} {cn[-40:]:40} -> {g['name']} over {res}")
        stats[t] += 1
    zmap = [phi.get(b) for b in zs]
    print(f"unit {unit}: inst {prefix[:-1]}, {len(order)} cone cells {dict(stats)}")
    print(f"LUTs with permuted pins (I_j not on A_(j+1)): {perm}; LUTs packed on a 5LUT (O5): {o5}; route-through hops resolved: {rts}")
    print(f"inputs resolved: {len(psi)} bits; z_data -> {zmap}")
    print(f"input map (port,bit)->decoded node: {dict(sorted(psi.items()))}")
    print(f"FAILS: {len(fails)}")
    for f in fails[:30]: print("  FAIL", f)
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
