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
    L.append("/-- tileconn.json entries (keyed by their index in the file), restricted to the wire pairs used. -/")
    L.append("set_option maxRecDepth 100000 in")
    L.append("def rules : NT Rl := " + tree(rl, lambda s: s))
    L.append("")
    L.append("def D : DB := ⟨tiles, wires, rules⟩")
    L.append("")
    L.append("end Formal.Target.NM.Data")
    open(os.path.join(out, "DB.lean"), "w").write("\n".join(L) + "\n")
    # C
    items = sorted((n, (TI[a], WI[b])) for n, (a, b) in canon.items())
    L = ["import Formal.Target.NodeMerge", "", hdr, "namespace Formal.Target.NM.Data", "open Formal.Target.NM", ""]
    parts = []
    K = 8
    step = (len(items) + K - 1) // K
    for p in range(K):
        sl = items[p * step:(p + 1) * step]
        L.append("set_option maxRecDepth 100000 in")
        L.append("def c%d : NT (Nat × Nat) := %s" % (p, tree(sl, lambda v: "(%d, %d)" % v)))
        L.append("")
        parts.append((sl[0][0], "c%d" % p))
    def comb(ps):
        if len(ps) == 1:
            return ps[0][1]
        m = len(ps) // 2
        return "(.node %d %s %s)" % (ps[m][0], comb(ps[:m]), comb(ps[m:]))
    L.append("def C : NT (Nat × Nat) := " + comb(parts))
    L.append("")
    L.append("end Formal.Target.NM.Data")
    open(os.path.join(out, "C.lean"), "w").write("\n".join(L) + "\n")
    # K chunks
    def pth(p):
        return "[%s]" % ", ".join("(%d, %d, %s, %d)" % (ri, kk, "true" if bb else "false", TI[tt]) for ri, kk, bb, tt in p)
    for ci, (gs, cc) in enumerate(zip(chunks, certs)):
        L = ["import FormalWit.NM.DB", "import FormalWit.NM.C", "import Formal.Target.NetPS.G%03d" % ci, "", hdr,
             "namespace Formal.Target.NM.Data", "open Formal.Target Formal.Target.NM Formal.Target.DecodedPS", "",
             "theorem g%03d_len : g%03d.length = %d := by decide +kernel" % (ci, ci, len(gs)), ""]
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
        chain = "all_drop_len _ g%03d %d (Nat.le_of_eq g%03d_len)" % (ci, nsub * SUB, ci) if nsub * SUB == len(gs) \
            else "all_drop_len _ g%03d %d (by rw [g%03d_len]; decide)" % (ci, nsub * SUB, ci)
        for s in reversed(range(nsub)):
            chain = "(all_drop_take _ g%03d %d %d k%03d_%d %s)" % (ci, s * SUB, SUB, ci, s, chain)
        L.append("theorem k%03d : ∀ g ∈ g%03d, isPip g = true → PipOK D C g := by" % (ci, ci))
        L.append("  have h := %s" % chain)
        L.append("  rwa [List.drop_zero] at h")
        L.append("")
        L.append("end Formal.Target.NM.Data")
        open(os.path.join(out, "K%03d.lean" % ci), "w").write("\n".join(L) + "\n")
    # All
    n = len(chunks)
    L = ["import Formal.Target.NetPS.All"] + ["import FormalWit.NM.K%03d" % i for i in range(n)] + ["", hdr,
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
          "end Formal.Target.NM.Data"]
    open(os.path.join(out, "All.lean"), "w").write("\n".join(L) + "\n")
    print("gen_nm: %d pips, %d tiles, %d wires, %d types, %d rules (%d pairs), %d canonical nodes, %d chunks" %
          (npips, len(TL), len(WL), len(types), len(used_rules), sum(len(v) for v in used_rules.values()),
           len(canon), n))


if __name__ == "__main__":
    main()
