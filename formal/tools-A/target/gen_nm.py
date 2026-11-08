#!/usr/bin/env python3
"""gen_nm.py -- data for Formal.Target.NodeMerge (the netlist's pip endpoints are prjxray's nodes).

    python3 gen_nm.py TILEGRID.json TILECONN.json OUTDIR

Reads THE target's Lean netlist SOURCE (formal/lean/Formal/Target/NetPS/{Nodes,G*}.lean, parsed) and prjxray-db's
tilegrid.json / tileconn.json for the part (prjxray-db master, zynq7/xc7z010). Writes FormalWit/NM/:
  DB.lean     the trusted tables (tiles, wires, the tileconn rules and wire pairs that some path uses)
  C.lean      the canonical wire of every node a pip touches (the wire its decoder name gives), certificate only
  Kccc.lean   per gate chunk g<ccc>: every pip gate's certificate (tile, wires, two tileconn paths), checked by
              `chkList` in sub-chunks of 250 gates (`decide +kernel`), combined to `kccc : ∀ g ∈ gccc, isPip g → PipOK`
  All.lean    `pips_ok : ∀ g ∈ DecodedPS.net.gates, isPip g = true → PipOK D C g`
UNTRUSTED: everything it emits is re-checked by the kernel, except DB (prjxray's data, H_DECODE).
"""
import collections, glob, json, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
NETD = os.path.join(HERE, "..", "..", "lean", "Formal", "Target", "NetPS")
SUB = 250


def parse_net():
    src = open(os.path.join(NETD, "Nodes.lean")).read()
    names = []
    defs = re.findall(r'def (n\d\d) : List String := \[(.*?)\]\n', src, re.S)
    order = re.search(r'def names : List String := (.*)\n', src).group(1).split(" ++ ")
    d = dict(defs)
    for k in order:
        names += re.findall(r'"((?:[^"\\]|\\.)*)"', d[k.strip()])
    chunks = []
    pP = re.compile(r'^  P "([^"]*)" (\d+) (\d+) (\d+) (\d+) (\d+) (\d+)')
    pG = re.compile(r'^  ⟨"([^"]*)", (\d+), (\d+), \[([^\]]*)\], .*, (\d+)⟩')
    files = sorted(glob.glob(os.path.join(NETD, "G*.lean")))
    for f in files:
        gs = []
        for line in open(f):
            m = pP.match(line)
            if m:
                gs.append((m.group(1), 1, [int(m.group(2))], int(m.group(3))))
                continue
            m = pG.match(line)
            if m:
                ins = [int(x) for x in m.group(4).split(",") if x.strip()]
                gs.append((m.group(1), int(m.group(2)), ins, int(m.group(5))))
                continue
            if line.startswith("  ") and ('P "' in line or '⟨"' in line):
                sys.exit("unparsed: " + line[:80])
        chunks.append(gs)
    return names, chunks


def main():
    tg_path, tc_path, out = sys.argv[1:4]
    ttdir = os.path.dirname(os.path.abspath(tc_path))  # tile_type_*.json next to tileconn.json
    names, chunks = parse_net()
    grid = json.load(open(tg_path))
    at = {(t["grid_x"], t["grid_y"]): n for n, t in grid.items()}
    rules = json.load(open(tc_path))
    conn = collections.defaultdict(list)
    for ri, e in enumerate(rules):
        (dx, dy), (t1, t2) = e["grid_deltas"], e["tile_types"]
        for k, (w1, w2) in enumerate(e["wire_pairs"]):
            conn[(t1, w1)].append((dx, dy, t2, w2, ri, k, False))
            conn[(t2, w2)].append((-dx, -dy, t1, w1, ri, k, True))

    def nbrs(t, w):
        g = grid[t]
        for dx, dy, t2, w2, ri, k, b in conn.get((g["type"], w), ()):
            o = at.get((g["grid_x"] + dx, g["grid_y"] + dy))
            if o and grid[o]["type"] == t2:
                yield (o, w2), (ri, k, b, o)

    def path(a, b):
        if a == b:
            return []
        prev = {a: None}
        q = collections.deque([a])
        while q:
            x = q.popleft()
            for y, st in nbrs(*x):
                if y not in prev:
                    prev[y] = (x, st)
                    if y == b:
                        p, z = [], b
                        while prev[z]:
                            p.append(prev[z][1])
                            z = prev[z][0]
                        return p[::-1]
                    q.append(y)
        sys.exit("no tileconn path %s -> %s" % (a, b))

    # certificates
    certs = []   # per chunk: list of None | (til, T, D, S, pin, pout)
    used_rules = collections.defaultdict(set)
    tiles, wires = set(), set()
    canon = {}
    npips = 0
    for gs in chunks:
        cc = []
        for (nm, k, ins, o) in gs:
            if k != 1 or nm.startswith("hop "):
                cc.append(None)
                continue
            npips += 1
            til = nm.startswith("~")
            T, Dw, Sw = (nm[1:] if til else nm).split(".")
            tiles.add(T); wires.update((Dw, Sw))
            ps = []
            for (w, n) in ((Sw, ins[0]), (Dw, o)):
                a, b = names[n].split("/", 1)
                canon[n] = (a, b); tiles.add(a); wires.add(b)
                p = path((T, w), (a, b))
                for (ri, kk, bb, tt) in p:
                    used_rules[ri].add(kk); tiles.add(tt)
                ps.append(p)
            cc.append((til, T, Dw, Sw, ps[0], ps[1]))
        certs.append(cc)
    for ri, ks in used_rules.items():
        e = rules[ri]
        tiles.update(())  # tiles of steps already added
        for kk in ks:
            wires.update(e["wire_pairs"][kk])
    types = sorted({grid[t]["type"] for t in tiles} | {t for ri in used_rules for t in rules[ri]["tile_types"]})
    TY = {t: i for i, t in enumerate(types)}
    TL = sorted(tiles); TI = {t: i for i, t in enumerate(TL)}
    WL = sorted(wires); WI = {w: i for i, w in enumerate(WL)}

    WX = {}   # wires added for the site-pin paths (NodeMergePin), indices after WL
    def tree(items, leaf):
        """balanced NT literal over sorted (key, value) items"""
        if not items:
            return ".nil"
        if len(items) == 1:
            return "(.leaf %d %s)" % (items[0][0], leaf(items[0][1]))
        m = len(items) // 2
        return "(.node %d %s %s)" % (items[m][0], tree(items[:m], leaf), tree(items[m:], leaf))

    os.makedirs(out, exist_ok=True)
    hdr = "/-! GENERATED by formal/tools-A/target/gen_nm.py. Do not edit. -/\n\n"
    # DB
    L = ["import Formal.Target.NodeMerge", "", hdr, "namespace Formal.Target.NM.Data", "open Formal.Target.NM", ""]
    L.append("/-- Tile types (index -> prjxray name), for the record. -/")
    L.append("def tyNames : List String := [%s]" % ", ".join('"%s"' % t for t in types))
    L.append("")
    sys.setrecursionlimit(100000)
    L.append("set_option maxRecDepth 100000 in")
    L.append("def tiles : NT Tl := " + tree([(i, t) for i, t in enumerate(TL)],
             lambda t: '⟨"%s", %d, %d, %d⟩' % (t, TY[grid[t]["type"]], grid[t]["grid_x"], grid[t]["grid_y"])))
    L.append("")
    L.append("set_option maxRecDepth 100000 in")
    L.append("def wires : NT String := " + tree(list(enumerate(WL)), lambda w: '"%s"' % w))
    L.append("")
    rl = []
    for ri in sorted(used_rules):
        e = rules[ri]
        (dx, dy), (t1, t2) = e["grid_deltas"], e["tile_types"]
        prs = tree([(kk, e["wire_pairs"][kk]) for kk in sorted(used_rules[ri])],
                   lambda p: "(%d, %d)" % (WI[p[0]], WI[p[1]]))
        rl.append((ri, "⟨%d, %d, %d, %d, %d, %d, %s⟩" % (max(dx, 0), max(-dx, 0), max(dy, 0), max(-dy, 0),
                                                        TY[t1], TY[t2], prs)))
    L.append("-- tileconn.json entries (keyed by their index in the file), restricted to the wire pairs used.")
    L.append("set_option maxRecDepth 100000 in")
    L.append("def rules : NT Rl := " + tree(rl, lambda s: s))
    L.append("")
    L.append("def D : DB := ⟨tiles, wires, rules⟩")
    L.append("")
    L.append("end Formal.Target.NM.Data")
    open(os.path.join(out, "DB.lean"), "w").write("\n".join(L) + "\n")
    # C: pieces of PIECE leaves, FILES files
    items = sorted((n, (TI[a], WI[b])) for n, (a, b) in canon.items())
    PIECE, NF = 2000, 8
    pieces = [items[i:i + PIECE] for i in range(0, len(items), PIECE)]
    per = (len(pieces) + NF - 1) // NF
    parts = []
    for f in range(NF):
        L = ["import Formal.Target.NodeMerge", "", hdr, "namespace Formal.Target.NM.Data", "open Formal.Target.NM", ""]
        for pi in range(f * per, min((f + 1) * per, len(pieces))):
            sl = pieces[pi]
            L.append("set_option maxRecDepth 100000 in")
            L.append("def c%03d : NT (Nat × Nat) := %s" % (pi, tree(sl, lambda v: "(%d, %d)" % v)))
            L.append("")
            parts.append((sl[0][0], "c%03d" % pi))
        L.append("end Formal.Target.NM.Data")
        open(os.path.join(out, "C%d.lean" % f), "w").write("\n".join(L) + "\n")
    def comb(ps):
        if len(ps) == 1:
            return ps[0][1]
        m = len(ps) // 2
        return "(.node %d %s %s)" % (ps[m][0], comb(ps[:m]), comb(ps[m:]))
    L = ["import FormalWit.NM.C%d" % f for f in range(NF)] + ["", hdr, "namespace Formal.Target.NM.Data",
         "open Formal.Target.NM", "", "def C : NT (Nat × Nat) := " + comb(parts), "", "end Formal.Target.NM.Data"]
    open(os.path.join(out, "C.lean"), "w").write("\n".join(L) + "\n")
    # K chunks
    def pth(p):
        return "[%s]" % ", ".join("(%d, %d, %s, %d)" % (ri, kk, "true" if bb else "false", TI[tt]) for ri, kk, bb, tt in p)
    for ci, (gs, cc) in enumerate(zip(chunks, certs)):
        L = ["import FormalWit.NM.DB", "import FormalWit.NM.C", "import Formal.Target.NetPS.G%03d" % ci, "", hdr,
             "namespace Formal.Target.NM.Data", "open Formal.Target Formal.Target.NM Formal.Target.DecodedPS", "",
             "theorem g%03d_len : g%03d.length = %d := by decide +kernel" % (ci, ci, len(gs)), "",
             "abbrev PP%03d : Gate → Prop := fun g => isPip g = true → PipOK D C g" % ci, ""]
        nsub = (len(gs) + SUB - 1) // SUB
        for s in range(nsub):
            row = []
            for c in cc[s * SUB:(s + 1) * SUB]:
                if c is None:
                    row.append("none")
                else:
                    til, T, Dw, Sw, pin, pout = c
                    row.append("some ⟨%s, %d, %d, %d, %s, %s⟩" % ("true" if til else "false", TI[T], WI[Dw], WI[Sw],
                                                                   pth(pin), pth(pout)))
            L.append("def q%03d_%d : List (Option PC) := [%s]" % (ci, s, ", ".join(row)))
            L.append("")
            L.append("theorem k%03d_%d : ∀ g ∈ (g%03d.drop %d).take %d, isPip g = true → PipOK D C g :=" %
                     (ci, s, ci, s * SUB, SUB))
            L.append("  chk_slice D C g%03d %d %d q%03d_%d (by decide +kernel)" % (ci, s * SUB, SUB, ci, s))
            L.append("")
        chain = "(all_drop_len PP%03d g%03d %d (Nat.le_of_eq g%03d_len))" % (ci, ci, nsub * SUB, ci) if nsub * SUB == len(gs) \
            else "(all_drop_len PP%03d g%03d %d (by rw [g%03d_len]; decide))" % (ci, ci, nsub * SUB, ci)
        for s in reversed(range(nsub)):
            chain = "(all_drop_take PP%03d g%03d %d %d k%03d_%d %s)" % (ci, ci, s * SUB, SUB, ci, s, chain)
        L.append("theorem k%03d : ∀ g ∈ g%03d, isPip g = true → PipOK D C g := by" % (ci, ci))
        L.append("  have h := %s" % chain)
        L.append("  rwa [List.drop_zero] at h")
        L.append("")
        L.append("end Formal.Target.NM.Data")
        open(os.path.join(out, "K%03d.lean" % ci), "w").write("\n".join(L) + "\n")
    # LUT pins (NodeMergeLut): sites, pin wires, per-chunk checks
    def ttj(ty, _c={}):
        if ty not in _c:
            _c[ty] = json.load(open(os.path.join(ttdir, "tile_type_%s.json" % ty)))
        return _c[ty]
    site_tile = {}
    for t, v in grid.items():
        for sn in v.get("sites", {}):
            if sn.startswith("SLICE_"):
                site_tile[sn] = t
    def rank(site):
        t = site_tile[site]
        xs = sorted(int(re.match(r"SLICE_X(\d+)Y", s2).group(1)) for s2 in grid[t]["sites"] if s2.startswith("SLICE_"))
        return xs.index(int(re.match(r"SLICE_X(\d+)Y", site).group(1)))
    lre = re.compile(r"(SLICE_X\d+Y\d+)\.([A-D])LUT\.O([56])$")
    lsites = sorted({lre.match(g[0]).group(1) for gs in chunks for g in gs if lre.match(g[0])})
    SI = {x: i for i, x in enumerate(lsites)}
    for x in lsites:
        assert site_tile[x] in TI, x
    keys = {}
    for x in lsites:
        t = site_tile[x]; ty = grid[t]["type"]; r = rank(x)
        k = TY[ty] * 2 + r
        if k in keys:
            continue
        site = [z for z in ttj(ty)["sites"] if z["x_coord"] == r and z["prefix"] == "SLICE"]
        assert len(site) == 1, (ty, r)
        row = []
        for li, Lt in enumerate("ABCD"):
            for j in range(6):
                w = site[0]["site_pins"]["%s%d" % (Lt, j + 1)]["wire"]
                if w not in WI:
                    sys.exit("pin wire %s not interned" % w)
                row.append((li * 6 + j, WI[w]))
        keys[k] = row
    L = ["import Formal.Target.NodeMergeLut", "", hdr, "namespace Formal.Target.NM.Data", "open Formal.Target.NM", ""]
    L.append("-- slice sites (tilegrid.json): name, tile index, rank among the tile's slices (prjxray X0/X1)")
    L.append("set_option maxRecDepth 100000 in")
    L.append("def sites : NT Site := " + tree([(SI[x], x) for x in lsites],
             lambda x: '⟨"%s", %d, %d⟩' % (x, TI[site_tile[x]], rank(x))))
    L.append("")
    L.append("-- site pins <L><j+1> (tile_type_*.json): key ty * 2 + rank, then L * 6 + j -> wire")
    L.append("set_option maxRecDepth 100000 in")
    L.append("def pins : NT (NT Nat) := " + tree(sorted(keys.items()), lambda row: tree(row, lambda w: "%d" % w)))
    L.append("")
    L.append("def P : SP := ⟨sites, pins⟩")
    L.append("")
    L.append("end Formal.Target.NM.Data")
    open(os.path.join(out, "S.lean"), "w").write("\n".join(L) + "\n")
    nl = 0
    for ci, gs in enumerate(chunks):
        row = []
        for g in gs:
            m = lre.match(g[0])
            if m:
                nl += 1
                # pin wires must equal the canonical wire of each input node
                for j, n in enumerate(g[2]):
                    t = site_tile[m.group(1)]
                    want = (TI[t], dict(keys[TY[grid[t]["type"]] * 2 + rank(m.group(1))])["ABCD".index(m.group(2)) * 6 + j])
                    if canon.get(n) is None or (TI[canon[n][0]], WI[canon[n][1]]) != want:
                        sys.exit("LUT pin mismatch %s %d" % (g[0], j))
                row.append("some ⟨%d, %d, %s⟩" % (SI[m.group(1)], "ABCD".index(m.group(2)), "true" if m.group(3) == "6" else "false"))
            else:
                row.append("none")
        L = ["import FormalWit.NM.S", "import FormalWit.NM.DB", "import FormalWit.NM.C", "import Formal.Target.NetPS.G%03d" % ci, "", hdr,
             "namespace Formal.Target.NM.Data", "open Formal.Target Formal.Target.NM Formal.Target.DecodedPS", "",
             "def l%03d : List (Option LC) := [%s]" % (ci, ", ".join(row)), "",
             "theorem lk%03d : ∀ g ∈ g%03d, isLut g = true → LutOK D P C g :=" % (ci, ci),
             "  chkLutList_sound D P C g%03d l%03d (by decide +kernel)" % (ci, ci), "",
             "end Formal.Target.NM.Data"]
        open(os.path.join(out, "L%03d.lean" % ci), "w").write("\n".join(L) + "\n")
    print("gen_nm: %d LUT gates on %d sites" % (nl, len(lsites)))
    # MUXF select / CARRY4 carry-in pins (NodeMergePin)
    xre = re.compile(r"(SLICE_X\d+Y\d+)\.(F7A|F7B|F8|CARRY4\.C?O\d)$")
    EXP = {"F7A": (2, "AX"), "F7B": (2, "CX"), "F8": (2, "BX")}
    PK = {"AX": 0, "BX": 1, "CX": 2, "CIN": 3}
    xsites = sorted({xre.match(g[0]).group(1) for gs in chunks for g in gs if xre.match(g[0])})
    for x in xsites:
        assert x in SI, "site %s not in the LUT site table" % x
    keys2 = {}
    for x in xsites:
        t = site_tile[x]; ty = grid[t]["type"]; r = rank(x); k = TY[ty] * 2 + r
        if k in keys2:
            continue
        site = [z for z in ttj(ty)["sites"] if z["x_coord"] == r and z["prefix"] == "SLICE"][0]
        row = []
        for pn, pk in sorted(PK.items(), key=lambda kv: kv[1]):
            w = site["site_pins"][pn]["wire"]
            if w not in WI and w not in WX:
                WX[w] = len(WL) + len(WX)
            row.append((pk, WI.get(w, WX.get(w))))
        keys2[k] = row
    def site_pin_name(t, site, pn):
        z = [z for z in ttj(grid[t]["type"])["sites"] if z["x_coord"] == rank(site) and z["prefix"] == "SLICE"][0]
        return z["site_pins"][pn]["wire"]
    extra = collections.defaultdict(set)
    Kc = sorted({g[2][0] for gs in chunks for g in gs if xre.match(g[0]) and names[g[2][0]].startswith("CONST")})
    nx = 0
    for ci, gs in enumerate(chunks):
        row = []
        for g in gs:
            m = xre.match(g[0])
            if not m:
                row.append("none")
                continue
            nx += 1
            site, suf = m.groups()
            j, pn = EXP.get(suf, (0, "CIN"))
            n = g[2][j]
            if n in Kc:
                row.append('some ⟨%d, "%s", none⟩' % (SI[site], suf))
                continue
            t = site_tile[site]
            wn = site_pin_name(t, site, pn)
            a, b = canon[n]
            pth_ = path((t, wn), (a, b))
            steps = []
            for (ri, kk, bb, tt2) in pth_:
                if tt2 not in TI:
                    sys.exit("pin path needs a tile not in DB: %s" % g[0])
                for w2 in rules[ri]["wire_pairs"][kk]:
                    if w2 not in WI and w2 not in WX:
                        WX[w2] = len(WL) + len(WX)
                if kk in used_rules.get(ri, ()):
                    steps.append("(%d, %d, %s, %d)" % (ri, kk, "true" if bb else "false", TI[tt2]))
                else:
                    extra[ri].add(kk)
                    steps.append("(%d, %d, %s, %d)" % (10000 + ri, kk, "true" if bb else "false", TI[tt2]))
            row.append('some ⟨%d, "%s", some [%s]⟩' % (SI[site], suf, ", ".join(steps)))
        L = ["import FormalWit.NM.S2", "import FormalWit.NM.S", "import FormalWit.NM.DB", "import FormalWit.NM.C",
             "import Formal.Target.NetPS.G%03d" % ci, "", hdr,
             "namespace Formal.Target.NM.Data", "open Formal.Target Formal.Target.NM Formal.Target.DecodedPS", "",
             "theorem gx%03d_len : g%03d.length = %d := by decide +kernel" % (ci, ci, len(gs)), "",
             "abbrev PX%03d : Gate → Prop := fun g => isX g = true → XOK D2 P Q C K g" % ci, ""]
        nsub = (len(gs) + SUB - 1) // SUB
        for sb in range(nsub):
            L += ["set_option maxRecDepth 100000 in",
                  "def x%03d_%d : List (Option XC) := [%s]" % (ci, sb, ", ".join(row[sb * SUB:(sb + 1) * SUB])), "",
                  "theorem xk%03d_%d : ∀ g ∈ (g%03d.drop %d).take %d, PX%03d g :=" % (ci, sb, ci, sb * SUB, SUB, ci),
                  "  chkXList_sound D2 P Q C K _ x%03d_%d (by decide +kernel)" % (ci, sb), ""]
        chain = ("(all_drop_len PX%03d g%03d %d (Nat.le_of_eq gx%03d_len))" if nsub * SUB == len(gs) else
                 "(all_drop_len PX%03d g%03d %d (by rw [gx%03d_len]; decide))") % (ci, ci, nsub * SUB, ci)
        for sb in reversed(range(nsub)):
            chain = "(all_drop_take PX%03d g%03d %d %d xk%03d_%d %s)" % (ci, ci, sb * SUB, SUB, ci, sb, chain)
        L += ["theorem xk%03d : ∀ g ∈ g%03d, isX g = true → XOK D2 P Q C K g := by" % (ci, ci),
              "  have h := %s" % chain, "  rwa [List.drop_zero] at h", ""]
        for kn in Kc:
            if kn // 2500 == ci:
                L += ["/-- The listed constant node is driven by a constant-0 gate. -/",
                      "theorem kconst%d : ∃ g ∈ g%03d, g.out = %d ∧ g.k = 0 ∧ g.init = 0 := by decide +kernel" % (kn, ci, kn), ""]
        L.append("end Formal.Target.NM.Data")
        open(os.path.join(out, "X%03d.lean" % ci), "w").write("\n".join(L) + "\n")
    L = ["import Formal.Target.NodeMergePin", "import FormalWit.NM.DB", "", hdr, "namespace Formal.Target.NM.Data", "open Formal.Target.NM", "",
         "-- site pins AX, BX, CX, CIN (tile_type_*.json): key ty * 2 + rank, then pin key -> wire",
         "def pins2 : NT (NT Nat) := " + tree(sorted(keys2.items()), lambda row: tree(row, lambda w: "%d" % w)), "",
         "def Q : SP2 := ⟨pins2⟩", "",
         "-- wires added for the carry-in paths (indices after DB's), and the tileconn pairs they use, under key",
         "-- 10000 + (index of the entry in tileconn.json)",
         "def wiresX : NT String := " + tree(sorted((i, w) for w, i in WX.items()), lambda w: '"%s"' % w), "",
         "set_option maxRecDepth 100000 in",
         "def rulesX : NT Rl := " + tree([(10000 + ri, "⟨%d, %d, %d, %d, %d, %d, %s⟩" % (
             max(rules[ri]["grid_deltas"][0], 0), max(-rules[ri]["grid_deltas"][0], 0),
             max(rules[ri]["grid_deltas"][1], 0), max(-rules[ri]["grid_deltas"][1], 0),
             TY[rules[ri]["tile_types"][0]], TY[rules[ri]["tile_types"][1]],
             tree([(kk, rules[ri]["wire_pairs"][kk]) for kk in sorted(extra[ri])],
                  lambda pr: "(%d, %d)" % (WI.get(pr[0], WX.get(pr[0])), WI.get(pr[1], WX.get(pr[1])))))) for ri in sorted(extra)],
             lambda s_: s_), "",
         "/-- `D` extended by those wires and pairs (same tiles; old keys unchanged). -/",
         "def D2 : DB := ⟨D.tiles, .node %d D.wires wiresX, .node 10000 D.rules rulesX⟩" % len(WL), "",
         "/-- Constant nodes a carry-in may read. -/",
         "def K : List Nat := [%s]" % ", ".join(map(str, Kc)), "", "end Formal.Target.NM.Data"]
    open(os.path.join(out, "S2.lean"), "w").write("\n".join(L) + "\n")
    n = len(chunks)
    L = ["import Formal.Target.NetPS.All"] + ["import FormalWit.NM.X%03d" % i for i in range(n)] + ["", hdr,
         "namespace Formal.Target.NM.Data", "open Formal.Target Formal.Target.NM Formal.Target.DecodedPS", "",
         "/-- **Every MUXF7/F8 gate reads its select, and every CARRY4 output gate its carry-in, from the node of its",
         "site's pin wire (AX/CX/BX; CIN through tileconn), or the carry-in is the constant node `K`.** -/",
         "theorem xs_ok : ∀ g ∈ net.gates, isX g = true → XOK D2 P Q C K g := by",
         "  intro g hg",
         "  simp only [net, gates, List.mem_append] at hg",
         "  rcases hg with " + " | ".join("h" for _ in range(n))] + ["  · exact xk%03d g h" % i for i in range(n)]
    for kn in Kc:
        L += ["", "/-- The constant node a carry-in may read is driven by a constant-0 gate of the netlist. -/",
              "theorem k_const%d : ∃ g ∈ net.gates, g.out = %d ∧ g.k = 0 ∧ g.init = 0 := by" % (kn, kn),
              "  obtain ⟨g, hg, h⟩ := kconst%d" % kn,
              "  exact ⟨g, by simp only [net, gates, List.mem_append]; tauto, h⟩"]
    L += ["", "end Formal.Target.NM.Data"]
    open(os.path.join(out, "AllX.lean"), "w").write("\n".join(L) + "\n")
    print("gen_nm: %d MUXF/CARRY4 gates, constants %s" % (nx, Kc))
    # All
    n = len(chunks)
    L = ["import Formal.Target.NetPS.All"] + ["import FormalWit.NM.K%03d" % i for i in range(n)] + \
        ["import FormalWit.NM.L%03d" % i for i in range(n)] + ["", hdr,
         "namespace Formal.Target.NM.Data", "open Formal.Target Formal.Target.NM Formal.Target.DecodedPS", "",
         "/-- **Every pip gate of THE target's decoded netlist** (implicit pips included) is named `[~]T.D.S` by a",
         "tile and two wires of prjxray's tables, and the nodes it reads and drives are, by tileconn, the electrical",
         "nodes of `T.S` and `T.D` (each node's canonical wire `C`). -/",
         "theorem pips_ok : ∀ g ∈ net.gates, isPip g = true → PipOK D C g := by",
         "  intro g hg",
         "  simp only [net, gates, List.mem_append] at hg"]
    L.append("  rcases hg with " + " | ".join("h" for _ in range(n)))
    for i in range(n):
        L.append("  · exact k%03d g h" % i)
    L += ["", "/-- **Every pip-to-pip connection of the netlist is a connection of the chip.** -/",
          "theorem pips_linked {g h : Gate} (hg : g ∈ net.gates) (hh : h ∈ net.gates) (pg : isPip g = true)",
          "    (ph : isPip h = true) (ih : h.ins = [g.out]) :",
          "    ∃ (tg dg th sh : Nat) (Ag Ah : Tl) (dng shn : String),",
          "      D.tiles.get tg = some Ag ∧ D.wires.get dg = some dng ∧ D.tiles.get th = some Ah ∧",
          "      D.wires.get sh = some shn ∧ (∃ pre s, g.name = pre ++ Ag.name ++ \".\" ++ dng ++ \".\" ++ s) ∧",
          "      (∃ pre d, h.name = pre ++ Ah.name ++ \".\" ++ d ++ \".\" ++ shn) ∧ Conn D (tg, dg) (th, sh) :=",
          "  pip_link (pips_ok g hg pg) (pips_ok h hh ph) ih", "",
          "/-- **Every LUT gate** reads, on input `j`, the node of its site's pin `<L><j+1>` wire (prjxray site pins). -/",
          "theorem luts_ok : ∀ g ∈ net.gates, isLut g = true → LutOK D P C g := by",
          "  intro g hg",
          "  simp only [net, gates, List.mem_append] at hg",
          "  rcases hg with " + " | ".join("h" for _ in range(n))] + ["  · exact lk%03d g h" % i for i in range(n)] + ["",
          "/-- **The pip driving LUT input `j` reaches the site wire of pin `<L><j+1>`** (the chip's pin order). -/",
          "theorem lut_pins_driven {g h : Gate} (hg : g ∈ net.gates) (hh : h ∈ net.gates) (lg : isLut g = true)",
          "    (ph : isPip h = true) {j : Nat} (hj : g.ins[j]? = some h.out) :",
          "    ∃ (s : Nat) (S : Site) (T : Tl) (L : Nat) (o6 : Bool) (w th dh : Nat) (Ah : Tl) (dnh : String),",
          "      P.sites.get s = some S ∧ D.tiles.get S.tile = some T ∧ g.name = lutName S L o6 ∧",
          "      pinWire P T.ty S.rank L j = some w ∧ D.tiles.get th = some Ah ∧ D.wires.get dh = some dnh ∧",
          "      (∃ pre sn, h.name = pre ++ Ah.name ++ \".\" ++ dnh ++ \".\" ++ sn) ∧ Conn D (th, dh) (S.tile, w) :=",
          "  lut_pin_driver (luts_ok g hg lg) (pips_ok h hh ph) hj", "",
          "end Formal.Target.NM.Data"]
    open(os.path.join(out, "All.lean"), "w").write("\n".join(L) + "\n")
    print("gen_nm: %d pips, %d tiles, %d wires, %d types, %d rules (%d pairs), %d canonical nodes, %d chunks" %
          (npips, len(TL), len(WL), len(types), len(used_rules), sum(len(v) for v in used_rules.values()),
           len(canon), n))


if __name__ == "__main__":
    main()
