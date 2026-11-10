#!/usr/bin/env python3
"""UNTRUSTED generator (shard C helper, 2026-11-09): the correspondence certificate between one
bdc_fused unit's yosys cells (Formal/Gen/Compute/GcdD/<Unit>.lean) and THE target's DECODED gates
(Formal.Target.DecodedPS.net), checked in Lean by Formal/Net/Compute/OnDecoded.lean (`cellOK`,
`corr_sound`). Nothing here is trusted: every gate, map entry and cell certificate is re-checked by
the kernel against DecodedPS's gate list.

    python3 psmap.py ps.json ps.routed.json net.json UNIT OUTDIR [--per-check N] [--max-cells M] [--per-file F]

Port of check_unit.py: the placement (routed JSON NEXTPNR_BEL / X_ORIG_PORT_*) only proposes
  phi : yosys net -> decoded node   (cell outputs in the cone)
  psi : (port, bit) -> decoded node (unit input bits)
and, per yosys cell (in extract.py's order = the Lean `cells` order), a local certificate
  B : boundary nodes (the nodes of the cell's input wires; a gate pin outside B and L must be don't-care),
  L : decoded gates (out, k, init, ins) in topological order: the gate(s) at the cell's outputs,
      the pip/hop copies, route-through LUTs and constant generators between them and B.
Writes, under OUTDIR (= formal/lean/Formal/Gen/Compute/PSMap/<Unit>/):
  Data.lean   maps, certs, D (all decoded gates used, sorted by out), the chunk split of D;
  Sub<c>.lean subOK g<c> d<c> = true for each decoded chunk c used (imports only that chunk);
  Chk<j>.lean cellOK for a range of cells (decide +kernel).
"""
import json, sys, os, itertools, collections

COMB = {"LUT1", "LUT2", "LUT3", "LUT4", "LUT5", "LUT6", "MUXF7", "MUXF8", "INV", "CARRY4"}
OUTP = {"O", "CO"}
CHUNK = 2500
# namespace of the unit's extracted cells: GcdD (gcd_hw's synthesis; identical for 19 units) or GcdPS (THE target's own
# synthesis, used for uori4 whose cells differ; 2026-11-10)
GNS = os.environ.get("GEN_NS", "GcdD")


def main():
    synth, routed, netf, unit, outdir = sys.argv[1:6]
    per = int(sys.argv[sys.argv.index("--per-check") + 1]) if "--per-check" in sys.argv else 20
    # at most this many cells per kernel check (0 = no limit): kernel memory grows with the cells of one check
    maxc = int(sys.argv[sys.argv.index("--max-cells") + 1]) if "--max-cells" in sys.argv else 0
    U = unit[0].upper() + unit[1:]
    S = json.load(open(synth))["modules"]
    R = json.load(open(routed))["modules"]["top"]["cells"]
    N = json.load(open(netf))
    nodes, gates = N["nodes"], N["gates"]
    nid = {n: i for i, n in enumerate(nodes)}
    gout = {g["out"]: g for g in gates}

    mods = [k for k in S if k.endswith(f"bdc_fused_{unit}") or f"bdc_fused_{unit}\\" in k]
    assert len(mods) == 1, mods
    m = S[mods[0]]
    insts = [(pm, cn) for pm, v in S.items() for cn, c in v["cells"].items() if c["type"] == mods[0]]
    assert len(insts) == 1, insts
    prefix = "bridge_i.udut." + insts[0][1] + "."
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

    rdrv = {}
    for rn, rc in R.items():
        for p, d in rc.get("port_directions", {}).items():
            if d == "output":
                for b in rc["connections"].get(p, []):
                    rdrv[b] = (rn, p)

    def rnode(rn, port):
        rc = R[rn]; bel = rc["attributes"]["NEXTPNR_BEL"]; site, b = bel.split("/")
        t = rc["type"]
        if t == "SLICE_LUTX": return f"{site}.{b[0]}{b[1]}"
        if t == "SELMUX2_1":
            return {"F7AMUX": f"{site}.F7A", "F7BMUX": f"{site}.F7B", "F8MUX": f"{site}.F8"}[b]
        if t == "CARRY4":
            return f"{site}.XOR{port[1]}" if port[0] == "O" else f"{site}.CO{port[2]}"
        if t == "SLICE_FFX": return f"{site}.{b[0]}{'5' if b[1] == '5' else ''}Q"
        if t == "PSEUDO_GND": return "GND"
        if t == "PSEUDO_VCC": return "VCC"
        return f"{rn}:{port}"

    def rcell(cn): return R.get(prefix + cn)

    phi, psi = {}, {}
    for cn in order:
        rc = rcell(cn); c = m["cells"][cn]
        assert rc is not None, cn
        rmap = {v: k for k, v in rc["attributes"].items() if k.startswith("X_ORIG_PORT_")}
        for p, bs in c["connections"].items():
            if p in OUTP:
                for i, b in enumerate(bs):
                    if not isinstance(b, int): continue
                    lp = f"{p}[{i}]" if c["type"] == "CARRY4" else p
                    rp = rmap.get(lp, "X_ORIG_PORT_?")[len("X_ORIG_PORT_"):]
                    if rp not in rc["connections"]: continue
                    phi[b] = nid[rnode(prefix + cn, rp)]

    def wire_expect(c, rc, p, i, b):
        rmap = {v: k[len("X_ORIG_PORT_"):] for k, v in rc["attributes"].items() if k.startswith("X_ORIG_PORT_")}
        lp = f"{p}[{i}]" if c["type"] == "CARRY4" and p in ("DI", "S") else p
        rp = rmap.get(lp)
        rb = rc["connections"][rp][0]
        while True:
            dn, dp = rdrv[rb]; dc = R[dn]
            if dc["type"] == "SLICE_LUTX" and "$LUT$" in dn and dc["attributes"].get("X_ORIG_TYPE") == "LUT1" \
                    and int(dc["parameters"]["INIT"], 2) == 2:
                ip = [k[len("X_ORIG_PORT_"):] for k, v in dc["attributes"].items() if k.startswith("X_ORIG_PORT_") and v == "I0"]
                rb = dc["connections"][ip[0]][0]; continue
            break
        nd = rnode(*rdrv[rb])
        if nd in ("GND", "VCC"):
            # input bit tied to a constant in the placed design: no decoded node of that name; take the
            # decoded LUT pin's driver chain (pips) down to its constant gate (INT_*/GND_WIRE, VCC_WIRE).
            assert c["type"].startswith("LUT") and rp.startswith("A"), (c["type"], rp)
            g = gout[phi[c["connections"]["O"][0]]]
            e = follow_copies(g["ins"][int(rp[1]) - 1])
            assert gout[e]["k"] == 0 and gout[e]["init"] == (1 if nd == "VCC" else 0), nodes[e]
            return e
        return nid[nd]

    def const_of(i):
        g = gout.get(i)
        return (g["init"] & 1) if g is not None and g["k"] == 0 else None

    def follow_copies(i):
        while True:
            g = gout.get(i)
            if g is None or not (g["k"] == 1 and g["init"] == 2): return i
            i = g["ins"][0]

    def cof(g):
        k = g["k"]
        if k > 6 or not (g["name"].endswith(".O6") or g["name"].endswith(".O5")): return None
        cp = {}
        for j, di in enumerate(g["ins"]):
            c = const_of(follow_copies(di))
            if c is not None: cp[j] = c
        free = [j for j in range(k) if j not in cp]
        def val(asg):
            a = sum(cp[j] << j for j in cp) + sum(asg[t] << j for t, j in enumerate(free))
            return (g["init"] >> a) & 1
        tab = {asg: val(asg) for asg in itertools.product((0, 1), repeat=len(free))}
        if len(set(tab.values())) == 1: return ("const", None, cp, free)
        for t, j in enumerate(free):
            if all(v == asg[t] for asg, v in tab.items()): return ("pin", j, cp, free)
        return None

    certs, stats = [], collections.Counter()
    for cn in order:
        c = m["cells"][cn]; rc = rcell(cn); t = c["type"]
        if t == "CARRY4":
            ins = [("CI", 0), ("CYINIT", 0)] + [("DI", i) for i in range(4)] + [("S", i) for i in range(4)]
        elif t in ("MUXF7", "MUXF8"): ins = [("I0", 0), ("I1", 0), ("S", 0)]
        elif t == "INV": ins = [("I", 0)]
        else: ins = [(f"I{j}", 0) for j in range(int(t[3]))]
        B, Lset, Lord = [], set(), []

        def addB(x):
            if x not in B: B.append(x)
        for p, i in ins:
            b = c["connections"][p][i]
            if b in ("0", "1"): continue
            if b in inb:
                e = wire_expect(c, rc, p, i, b)
                assert psi.setdefault(inb[b], e) == e, (cn, b)
            else:
                e = phi[b]
            addB(e)
        expect = set(B)

        def addL(i):
            if i not in Lset: Lset.add(i); Lord.append(i)

        def walk_const(i):  # a pin that cof found constant: copies down to a k=0 gate
            chain = []
            while True:
                g = gout[i]
                chain.append(i)
                if g["k"] == 0: break
                i = g["ins"][0]
            for x in reversed(chain): addL(x)

        def walk(i, depth):
            """make node i available (in B or in L, inputs first); returns False if not resolvable"""
            if i in expect or i in Lset: return True
            if depth > 200: return False
            g = gout.get(i)
            if g is None: return False
            if g["k"] == 0: addL(i); return True
            if g["k"] == 1 and g["init"] == 2:
                if not walk(g["ins"][0], depth + 1): return False
                addL(i); return True
            r = cof(g)
            if r is None: return False
            kind, j, cp, free = r
            for jj in cp: walk_const(g["ins"][jj])
            for jj in free:
                if jj == j:
                    if not walk(g["ins"][jj], depth + 1): return False
                else:
                    stats["don't-care pins"] += 1  # Lean checks the gate does not depend on it
            stats["route-through" if kind == "pin" else "const LUT"] += 1
            addL(i); return True

        for p, bs in c["connections"].items():
            if p not in OUTP: continue
            for b in bs:
                if not isinstance(b, int) or b not in phi: continue
                d = phi[b]; g = gout[d]
                for jj, di in enumerate(g["ins"]):
                    if not walk(di, 0):
                        # pin outside the gate's support: left unavailable (Lean checks it is don't-care)
                        stats["don't-care pins"] += 1
                addL(d)
        L = [(x, gout[x]["k"], gout[x]["init"], gout[x]["ins"]) for x in Lord]
        certs.append((B, L))
        stats["cells"] += 1
        stats["maxB"] = max(stats["maxB"], len(B))
        stats["L"] += len(L)

    # self-check: simulate the Lean `cellOK` (closedness with don't-care masks, exhaustive values)
    def wnode(b):
        if b in ("0", "1"): return None
        return psi[inb[b]] if b in inb else phi.get(b)
    bad = 0
    for cn, (B, L) in zip(order, certs):
        c = m["cells"][cn]; t = c["type"]; con = c["connections"]
        av = set(B) | {x[0] for x in L}; ok = True
        for p, bs in con.items():
            if p in OUTP:
                for b in bs:
                    if isinstance(b, int) and b in phi and phi[b] not in av: ok = False
        for asg in range(1 << len(B)):
            val = {x: (asg >> i) & 1 for i, x in enumerate(B)}
            avl = set(B)
            for (o, k, init, gins) in L:
                if not all(x in avl for x in gins):  # Lean's gOK: unavailable pins are don't-care here
                    msk = sum(1 << i for i, x in enumerate(gins) if x in avl)
                    base = sum(val.get(x, 0) << i for i, x in enumerate(gins)) & msk
                    if any((x & msk) == base and ((init >> x) & 1) != ((init >> base) & 1) for x in range(1 << k)):
                        ok = False
                a = sum(val.get(x, 0) << i for i, x in enumerate(gins))
                val[o] = (init >> a) & 1
                avl.add(o)
            def r(b):
                if b == "0": return 0
                if b == "1": return 1
                return val[wnode(b)]
            if t.startswith("LUT"):
                n = int(t[3]); a = sum(r(con[f"I{i}"][0]) << i for i in range(n))
                outv = {con["O"][0]: (int(c["parameters"]["INIT"], 2) >> a) & 1}
            elif t in ("MUXF7", "MUXF8"):
                outv = {con["O"][0]: r(con["I1"][0]) if r(con["S"][0]) else r(con["I0"][0])}
            elif t == "INV":
                outv = {con["O"][0]: 1 - r(con["I"][0])}
            else:
                cy = r(con["CI"][0]) | r(con["CYINIT"][0]); outv = {}
                for i in range(4):
                    sv = r(con["S"][i]); outv[con.get("O", ["x"] * 4)[i]] = sv ^ cy
                    cy = cy if sv else r(con["DI"][i]); outv[con.get("CO", ["x"] * 4)[i]] = cy
            for b, x in outv.items():
                if isinstance(b, int) and b in phi and val[phi[b]] != x: ok = False
            if not ok: break
        if not ok:
            bad += 1; print(f"SELFCHECK FAIL {cn} B={len(B)} L={len(L)}", file=sys.stderr)
    print(f"selfcheck: {bad} failing cells", file=sys.stderr)
    # dedupe by out (gate i drives node i, so one entry per out)
    Dd = {}
    for _, L in certs:
        for x in L: Dd[x[0]] = x
    D = [Dd[o] for o in sorted(Dd)]
    chunks = collections.OrderedDict()
    for x in D: chunks.setdefault(x[0] // CHUNK, []).append(x)
    print(f"psmap {unit}: {dict(stats)}; |D| = {len(D)} in chunks {list(chunks)}; phi {len(phi)}, psi {len(psi)}",
          file=sys.stderr)

    def gc(x): return "⟨%d, %d, %d, [%s]⟩" % (x[0], x[1], x[2], ", ".join(map(str, x[3])))
    ns = f"Formal.Gen.Compute.PSMap.{U}"
    os.makedirs(outdir, exist_ok=True)
    hdr = "/-! GENERATED by formal/tools/compute/ps/psmap.py (untrusted; every entry is re-checked in Lean). -/\n\n"
    dat = [f"import Formal.Net.Compute.OnDecoded\nimport Formal.Gen.Compute.{GNS}.{U}\n", hdr,
           f"namespace {ns}\nopen Formal.Net.Compute Formal.Net.Compute.OnDecoded\n",
           "set_option maxRecDepth 100000\n",
           f"/-- The unit's yosys cells (Formal.Gen.Compute.{GNS}.{U}). -/\nabbrev cells : List Cell := Formal.Gen.Compute.{GNS}.{U}.cells\n"]
    dat.append("def maps : Maps := ⟨[%s],\n  [%s]⟩\n" % (
        ", ".join(f"({n}, {d})" for n, d in sorted(phi.items())),
        ", ".join(f"({p}, {k}, {d})" for (p, k), d in sorted(psi.items()))))
    for ci, xs in chunks.items():
        dat.append(f"def d{ci:03d} : List GC := [\n  " + ",\n  ".join(gc(x) for x in xs) + "]\n")
    dat.append("def D : List GC := " + " ++ ".join(f"d{ci:03d}" for ci in chunks) + "\n")
    dat.append("/-- The decoded nodes the unit's statement needs settled. -/\ndef S : List Nat := D.map GC.out\n")
    def lg(B, L):
        seq, out = list(B), []   # available nodes, oldest first
        for x in L:
            n = len(seq); pos = {y: i for i, y in enumerate(seq)}  # last occurrence wins
            dist = [n - 1 - pos[i] if i in pos else n for i in x[3]]
            out.append("⟨%s, [%s]⟩" % (gc(x), ", ".join(map(str, dist))))
            seq.append(x[0])
        return ", ".join(out), seq

    def local(cn, seq):
        c = m["cells"][cn]; ph, ps, od = {}, {}, {}
        n = len(seq); pos = {y: i for i, y in enumerate(seq)}
        for p, bs in c["connections"].items():
            for b in bs:
                if not isinstance(b, int): continue
                if b in inb: ps[inb[b]] = psi[inb[b]]
                elif b in phi:
                    ph[b] = phi[b]
                    if p in OUTP: od[b] = n - 1 - pos[phi[b]]
        return "⟨[%s], [%s]⟩, [%s]" % (", ".join(f"({n_}, {d})" for n_, d in sorted(ph.items())),
                                      ", ".join(f"({p}, {k}, {d})" for (p, k), d in sorted(ps.items())),
                                      ", ".join(f"({o}, {d})" for o, d in sorted(od.items())))
    for j, (cn, (B, L)) in enumerate(zip(order, certs)):
        lgs, seq = lg(B, L)
        dat.append("def cc%d : CC := ⟨[%s], [%s],\n   %s⟩\n" % (j, ", ".join(map(str, B)), lgs, local(cn, seq)))
    dat.append("def certs : List CC := [%s]\n" % ", ".join(f"cc{j}" for j in range(len(certs))))
    dat.append(f"\nend {ns}\n")
    open(os.path.join(outdir, "Data.lean"), "w").write("\n".join(dat))
    for ci in chunks:
        open(os.path.join(outdir, f"Sub{ci:03d}.lean"), "w").write(
            f"import Formal.Target.NetPS.G{ci:03d}\nimport {ns}.Data\n\n" + hdr +
            f"namespace {ns}\nopen Formal.Net.Compute.OnDecoded Formal.Target.DecodedPS\n\n"
            f"theorem sub{ci:03d} : subOK g{ci:03d} d{ci:03d} = true := by decide +kernel\n\nend {ns}\n")
    # kernel checks: small cells (<= 64 assignments) grouped by cost; big cells: static + parts of 64
    n = len(certs)
    cost = lambda B, L: (1 << len(B)) * (len(L) + 8)
    budget = per * 80
    small, big = [], []
    for i, (B, L) in enumerate(certs):
        (small if (1 << len(B)) <= 64 else big).append(i)
    groups, cur, cc_ = [], [], 0
    for i in small:
        c_ = cost(*certs[i])
        if cur and (cc_ + c_ > budget or (maxc and len(cur) >= maxc)): groups.append(cur); cur, cc_ = [], 0
        cur.append(i); cc_ += c_
    if cur: groups.append(cur)
    thms = [("grp%d" % g, "idxOK maps D cells certs [%s]" % ", ".join(map(str, is_))) for g, is_ in enumerate(groups)]
    if big:
        thms.append(("st", "idxStatic maps D cells certs [%s]" % ", ".join(map(str, big))))
    parts = {}
    for i in big:
        P = ((1 << len(certs[i][0])) + 63) // 64
        parts[i] = P
        for q in range(P):
            thms.append((f"a{i}_{q}", f"asgRange (certs.getD {i} dfltCC) (cells.getD {i} dfltCell) {64 * q} {64 * q + 64}"))
    # kernel checks per Chk file (memory accumulates within one file)
    per_file = int(sys.argv[sys.argv.index("--per-file") + 1]) if "--per-file" in sys.argv else 3
    files = [thms[k:k + per_file] for k in range(0, len(thms), per_file)]
    pre = (f"import {ns}.Data\n\n" + hdr +
           f"namespace {ns}\nopen Formal.Net.Compute Formal.Net.Compute.OnDecoded\n\n")
    for j, th in enumerate(files):
        body = "".join(f"set_option maxRecDepth 100000 in\ntheorem {nm} : {st} = true := by decide +kernel\n\n" for nm, st in th)
        open(os.path.join(outdir, f"Chk{j}.lean"), "w").write(
            pre + body + f"end {ns}\n")
    # assembly
    grp_of = {i: g for g, is_ in enumerate(groups) for i in is_}
    imports = [f"import {ns}.Sub{ci:03d}" for ci in chunks] + [f"import {ns}.Chk{j}" for j in range(len(files))]
    out = ["\n".join(imports) + "\nimport Formal.Target.NetPS.All\n", hdr,
           f"namespace {ns}\nopen Formal.Net.Compute Formal.Net.Compute.OnDecoded Formal.Target\n"]
    for ci in chunks:
        path = "List.mem_append_right _ (" * ci + ("List.mem_append_left _ hg" if ci < 74 else "hg") + ")" * ci
        out.append(f"theorem gin{ci:03d} : ∀ g ∈ DecodedPS.g{ci:03d}, g ∈ DecodedPS.net.gates := fun g hg => by\n"
                   f"  show g ∈ DecodedPS.gates\n  unfold DecodedPS.gates\n  exact {path}\n")
    out.append("theorem mem_chunk {gs : List Gate} {ds : List GC} (hs : subOK gs ds = true)\n"
               "    (hg : ∀ g ∈ gs, g ∈ DecodedPS.net.gates) {c : GC} (h : c ∈ ds) :\n"
               "    ∃ g ∈ DecodedPS.net.gates, GC.ofGate g = c := by\n"
               "  obtain ⟨g, h1, h2⟩ := subOK_sound gs ds hs c h\n  exact ⟨g, hg g h1, h2⟩\n")
    ch = list(chunks)
    pr = ["  intro c hc", "  unfold D at hc"]
    for ci in reversed(ch[1:]):
        pr.append("  rcases List.mem_append.mp hc with hc | h")
        pr.append(f"  case inr => exact mem_chunk sub{ci:03d} gin{ci:03d} h")
    pr.append(f"  exact mem_chunk sub{ch[0]:03d} gin{ch[0]:03d} hc")
    out.append("/-- Every checked gate content is a gate of THE target's decoded netlist. -/\n"
               "theorem D_ok : ∀ c ∈ D, ∃ g ∈ DecodedPS.net.gates, GC.ofGate g = c := by\n" + "\n".join(pr) + "\n")
    out.append("set_option maxRecDepth 100000 in\ntheorem topo_ok : topoOK cells [] = true := by decide +kernel\n")
    out.append(f"set_option maxRecDepth 100000 in\ntheorem cells_len : cells.length = {n} := rfl\n")
    cases = []
    for i in range(n):
        if i in grp_of:
            cases.append(f"  | {i}, _ => exact idxOK_sound grp{grp_of[i]} {i} (by decide)")
        else:
            P = parts[i]
            out.append(f"set_option maxRecDepth 100000 in\ntheorem big{i} : cellOK maps D (cells.getD {i} dfltCell) (certs.getD {i} dfltCC) = true := by\n"
                       f"  apply cellOK_of_parts (idxStatic_sound st {i} (by decide)) {P} (by decide +kernel)\n"
                       f"  intro p hp\n  match p, hp with\n" +
                       "".join(f"  | {q}, _ => exact a{i}_{q}\n" for q in range(P)) +
                       f"  | _ + {P}, h => exact absurd h (by omega)\n")
            cases.append(f"  | {i}, _ => exact big{i}")
    out.append("set_option maxRecDepth 100000 in\n/-- Every cell passes the correspondence check. -/\n"
               "theorem cells_ok : ∀ i, i < cells.length →\n"
               "    cellOK maps D (cells.getD i dfltCell) (certs.getD i dfltCC) = true := by\n"
               "  intro i hi\n  rw [cells_len] at hi\n  match i, hi with\n" + "\n".join(cases) +
               f"\n  | _ + {n}, h => exact absurd h (by omega)\n")
    out.append(f"end {ns}\n")
    open(os.path.join(outdir, "All.lean"), "w").write("\n".join(out))


if __name__ == "__main__":
    main()
