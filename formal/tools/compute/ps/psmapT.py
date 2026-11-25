#!/usr/bin/env python3
"""UNTRUSTED generator (shard C, 2026-11-09): the TIMED certificate of one bdc_fused unit on THE target's
decoded netlist, checked in Lean by Formal/Net/Compute/PS/<Unit>T.lean.

    python3 psmapT.py UNIT [LEANROOT]      (LEANROOT default: formal/lean)

Reads Formal/Target/NetPS/G*.lean (the decoded gates; gate i drives node i) and the untimed certificate
Formal/Gen/Compute/PSMap/<Unit>/Data.lean (S = the nodes to settle, psi = the unit's input nodes).
Proposes:
  * a topological order of the gates driving S (inputs external = the unit's input nodes), cut into segments,
    each segment a pick (skip counts) from ONE decoded chunk g<c>, so gate membership is by construction;
  * SN : node -> slow-max depth (longest path, prjxray slow-max units), as a balanced search tree;
  * D = max SN over S.
Writes Formal/Gen/Compute/PSMap/<Unit>T/{Data,Pk*,Cover,All}.lean.  Nothing here is trusted: certOKN,
the coverage of S and the bounds SN <= D are decided by the kernel.
"""
import re, glob, os, sys, heapq, collections

CHUNK = 2500
PIECE_COST = 12000   # kernel steps (skips + picks) per piece
PIECE_GATES = 150
PER_FILE = 4
# uselect1 (2026-11-09) used the two 32-bit inputs explicitly; every later unit uses the whole input map
KNOWN_E01 = os.environ.get("KNOWN_E01") == "1"


def main():
    unit = sys.argv[1]
    root = sys.argv[2] if len(sys.argv) > 2 else os.path.join(os.path.dirname(__file__), "../../../lean")
    U = unit[0].upper() + unit[1:]
    P = re.compile(r'^\s*P "((?:[^"\\]|\\.)*)" (\d+) (\d+) (\d+) (\d+) (\d+) (\d+)[,\]]?$')
    G = re.compile(r'^\s*⟨"((?:[^"\\]|\\.)*)", (\d+), (\d+), \[([^\]]*)\], \[(.*)\], (\d+)⟩[,\]]?$')
    A = re.compile(r'⟨(\d+), (\d+), (\d+), (\d+)⟩')
    gates = []
    for f in sorted(glob.glob(os.path.join(root, "Formal/Target/NetPS/G*.lean"))):
        for line in open(f):
            m = P.match(line)
            if m:
                _, i, o, _, _, _, e = m.groups()
                gates.append(dict(k=1, ins=[int(i)], smax=[int(e)], out=int(o)))
                continue
            m = G.match(line)
            if m:
                _, k, _, ins, arcs, o = m.groups()
                gates.append(dict(k=int(k), ins=[int(x) for x in ins.split(",")] if ins.strip() else [],
                                  smax=[int(t[3]) for t in A.findall(arcs)], out=int(o)))
    assert all(g["out"] == i for i, g in enumerate(gates)), "gate i must drive node i"
    src = open(os.path.join(root, f"Formal/Gen/Compute/PSMap/{U}/Data.lean")).read()
    S = []
    for m in re.finditer(r"def d(\d+) : List GC := \[(.*?)\]\n", src, re.S):
        S += [int(x) for x in re.findall(r"⟨(\d+), \d+, \d+, \[", m.group(2))]
    psi = re.search(r"def maps : Maps := ⟨\[.*?\],\s*\[(.*?)\]⟩", src, re.S).group(1)
    psi = [tuple(map(int, t)) for t in re.findall(r"\((\d+), (\d+), (\d+)\)", psi)]
    inp = {d for _, _, d in psi}
    Ss = set(S)
    for o in S:
        g = gates[o]
        assert len(g["ins"]) == g["k"] == len(g["smax"])
        for i in g["ins"]:
            assert i in Ss or i in inp, ("pin outside S and inputs", o, i)
    # Kahn, smallest node first (keeps runs of one chunk long)
    indeg = {o: sum(1 for i in set(gates[o]["ins"]) if i in Ss) for o in S}
    users = collections.defaultdict(list)
    for o in S:
        for i in set(gates[o]["ins"]):
            if i in Ss: users[i].append(o)
    h = [o for o in S if indeg[o] == 0]; heapq.heapify(h); order = []
    while h:
        o = heapq.heappop(h); order.append(o)
        for u in users[o]:
            indeg[u] -= 1
            if indeg[u] == 0: heapq.heappush(h, u)
    assert len(order) == len(S), "cycle"
    # segments: maximal runs, same chunk, increasing
    segs = []
    for o in order:
        c = o // CHUNK
        if segs and segs[-1][0] == c and segs[-1][1][-1] < o: segs[-1][1].append(o)
        else: segs.append((c, [o]))
    # SN: longest slow-max path
    SN = {}
    for o in order:
        g = gates[o]
        SN[o] = max([max(g["smax"], default=0)] + [SN.get(i, 0) + s for i, s in zip(g["ins"], g["smax"])])
    D = max(SN.values())
    # known-stack depth (cost estimate of certOKN)
    stack = [d for _, _, d in sorted(psi)]
    pos = {}
    for j, n in enumerate([d for _, _, d in psi]):
        pos[n] = j
    cost = 0; t = len(pos)
    for o in order:
        for i in gates[o]["ins"]:
            cost += t - pos[i]
        pos[o] = t; t += 1
    print(f"psmapT {unit}: |S| = {len(S)}, segments {len(segs)}, D = {D}, known-search ~{cost}", file=sys.stderr)

    def tree(kv):
        if not kv: return ".lf"
        m = len(kv) // 2
        return "(.nd %d %d %s %s)" % (kv[m][0], kv[m][1], tree(kv[:m]), tree(kv[m + 1:]))
    # pieces: consecutive segments, bounded kernel work each (a segment walks its chunk from the start)
    pcs, cur, cost = [], [], 0
    for c, os_ in segs:
        w = os_[-1] - c * CHUNK + 1 + 4 * len(os_)
        if cur and (cost + w > PIECE_COST or sum(len(x[1]) for x in cur) + len(os_) > PIECE_GATES):
            pcs.append(cur); cur, cost = [], 0
        cur.append((c, os_)); cost += w
    if cur: pcs.append(cur)
    pidx = {o: i for i, pc in enumerate(pcs) for _, os_ in pc for o in os_}
    chunks = sorted({o // CHUNK for o in S})
    ns = f"Formal.Gen.Compute.PSMap.{U}T"
    hdr = "/-! GENERATED by formal/tools/compute/ps/psmapT.py (untrusted; every entry is re-checked in Lean). -/\n\n"
    out = os.path.join(root, f"Formal/Gen/Compute/PSMap/{U}T")
    os.makedirs(out, exist_ok=True)
    for f in glob.glob(os.path.join(out, "*.lean")): os.remove(f)
    dat = ["\n".join(f"import Formal.Target.NetPS.G{c:03d}" for c in chunks) +
           f"\nimport Formal.Gen.Compute.PSMap.{U}.Data\nimport Formal.Timing.SpecSettleSym\n", hdr,
           f"namespace {ns}\nopen Formal.Target Formal.Target.DecodedPS Formal.Net.Compute.OnDecoded\n",
           "set_option maxRecDepth 100000\n",
           "/-- One step of `pickR`: on index list `0 :: ds` take the gate, on `(d+1) :: ds` skip it. -/\n"
           "def stepP (g : Gate) (ih : List Nat → List Gate) : List Nat → List Gate\n  | [] => []\n"
           "  | 0 :: ds => g :: ih ds\n  | (d + 1) :: ds => ih (d :: ds)\n",
           "/-- `pickR l ds`: skip `ds[0]` entries of `l`, take one, skip `ds[1]`, take one, ... (a bare recursor:\n"
           "cheap for the kernel). -/\nnoncomputable def pickR (l : List Gate) : List Nat → List Gate :=\n"
           "  @List.rec Gate (fun _ => List Nat → List Gate) (fun _ => []) (fun g _ ih => stepP g ih) l\n",
           "/-- A search tree node -> value (0 when absent). -/\ninductive NT where\n  | lf\n  | nd (k v : Nat) (l r : NT)\n",
           "def NT.find : NT → Nat → Nat\n  | .lf, _ => 0\n"
           "  | .nd k v l r, n => cond (Nat.blt n k) (NT.find l n) (cond (Nat.blt k n) (NT.find r n) v)\n",
           "/-- The decoded chunks the unit uses. -/\ndef chunk : Nat → List Gate\n" +
           "".join(f"  | {c} => g{c:03d}\n" for c in chunks) + "  | _ => []\n",
           "/-- A segment: picks from one chunk. -/\nnoncomputable def seg (s : Nat × List Nat) : List Gate := pickR (chunk s.1) s.2\n"]
    for pi, pc in enumerate(pcs):
        sl = []
        for c, os_ in pc:
            prev, ds = c * CHUNK - 1, []
            for o in os_:
                ds.append(o - prev - 1); prev = o
            sl.append("(%d, [%s])" % (c, ", ".join(map(str, ds))))
        dat.append(f"def pc{pi} : List (Nat × List Nat) := [\n  " + ",\n  ".join(sl) + "]\n")
        dat.append(f"def o{pi} : List Nat := [{', '.join(str(o) for _, os_ in pc for o in os_)}]\n")
    dat.append("def pcs : List (List (Nat × List Nat)) := [%s]\n" % ", ".join(f"pc{i}" for i in range(len(pcs))))
    dat.append("/-- Each piece's gate outputs, in order. -/\ndef oAll : List (List Nat) := [%s]\n" % ", ".join(f"o{i}" for i in range(len(pcs))))
    dat.append(f"def nP : Nat := {len(pcs)}\n")
    dat.append("/-- Piece `i`: its segments' gates. -/\nnoncomputable def A (i : Nat) : List Gate := (pcs.getD i []).flatMap seg\n")
    dat.append("/-- The unit's gates in topological order. -/\nnoncomputable def gs : List Gate := ((List.range nP).map A).flatten\n")
    dat.append("/-- The known nodes before piece `i`: earlier outputs (latest first), then `K`. -/\n"
               "def Kof : List (List Nat) → List Nat → Nat → List Nat\n  | _, K, 0 => K\n  | [], K, _ + 1 => K\n"
               "  | o :: os, K, i + 1 => Kof os (o.reverse ++ K) i\n")
    dat.append("def snT : NT := " + tree(sorted(SN.items())) + "\n")
    dat.append("/-- Slow-max depth of each node (prjxray slow-max units; 0 for the unit's input nodes). -/\n"
               "def SN (n : Nat) : Nat := snT.find n\n")
    dat.append("/-- The piece holding each node's driver. -/\ndef ptT : NT := " + tree(sorted(pidx.items())) + "\n")
    dat.append(f"/-- The unit's depth. -/\ndef D : Nat := {D}\n")
    if KNOWN_E01:
        dat.append(f"/-- The unit's input nodes. -/\ndef known : List Nat := "
                   f"(List.range 32).map (inNode Formal.Gen.Compute.PSMap.{U}.maps 0) ++ "
                   f"(List.range 32).map (inNode Formal.Gen.Compute.PSMap.{U}.maps 1)\n")
    else:
        dat.append(f"/-- The unit's input nodes (every node of the untimed certificate's input map). -/\n"
                   f"def known : List Nat := Formal.Gen.Compute.PSMap.{U}.maps.psi.map (fun e => e.2.2)\n")
    dat.append("/-- A gate's output and pins have depth at most `D`. -/\n"
               "def bnd (g : Gate) : Bool := decide (SN g.out ≤ D) &&\n"
               "  (List.range g.k).all fun i => decide (SN (g.ins.getD i 0) ≤ D)\n")
    dat.append("/-- What each piece file decides. -/\nnoncomputable def pieceOK (i : Nat) : Bool :=\n"
               "  Formal.Timing.SpecSettle.certOKN SN (Kof oAll known i) (A i) && ((A i).map Gate.out == oAll.getD i []) && (A i).all bnd\n")
    dat.append(f"\nend {ns}\n")
    open(os.path.join(out, "Data.lean"), "w").write("\n".join(dat))
    pre = f"import {ns}.Data\n\n" + hdr + f"namespace {ns}\nopen Formal.Target Formal.Timing.SpecSettle Formal.Net.Compute.OnDecoded\n\n"
    files = [list(range(k, min(k + PER_FILE, len(pcs)))) for k in range(0, len(pcs), PER_FILE)]
    for fi, ix in enumerate(files):
        open(os.path.join(out, f"Pk{fi}.lean"), "w").write(pre + "".join(
            f"set_option maxRecDepth 100000 in\ntheorem pk{i} : pieceOK {i} = true := by decide +kernel\n\n" for i in ix) + f"end {ns}\n")
    open(os.path.join(out, "Cover.lean"), "w").write(pre +
        "set_option maxRecDepth 100000 in\ntheorem known_ok : known.all (fun n => SN n == 0) = true := by decide +kernel\n\n" +
        "".join(f"set_option maxRecDepth 100000 in\ntheorem cov{c:03d} : (Formal.Gen.Compute.PSMap.{U}.d{c:03d}.map GC.out).all "
                f"(fun n => mem n (oAll.getD (ptT.find n) [])) = true := by decide +kernel\n\n" for c in chunks) + f"end {ns}\n")
    al = ["\n".join(f"import {ns}.Pk{fi}" for fi in range(len(files))) + f"\nimport {ns}.Cover\n", hdr,
          f"namespace {ns}\nopen Formal.Target Formal.Timing.SpecSettle Formal.Net.Compute.OnDecoded\n",
          f"theorem nP_eq : nP = {len(pcs)} := rfl\n",
          "theorem pieces_ok : ∀ i, i < nP → pieceOK i = true := by\n  intro i hi\n  rw [nP_eq] at hi\n  match i, hi with\n" +
          "".join(f"  | {i}, _ => exact pk{i}\n" for i in range(len(pcs))) + f"  | _ + {len(pcs)}, h => exact absurd h (by omega)\n",
          "/-- Every node of `S` is in some piece's output list. -/\n"
          f"theorem cover_ok : ∀ n ∈ Formal.Gen.Compute.PSMap.{U}.S, mem n (oAll.getD (ptT.find n) []) = true := by\n"
          f"  intro n hn\n  simp only [Formal.Gen.Compute.PSMap.{U}.S, Formal.Gen.Compute.PSMap.{U}.D, List.map_append, List.mem_append, or_assoc] at hn\n"
          "  rcases hn with " + " | ".join("h" for _ in chunks) + "\n" +
          "".join(f"  · exact List.all_eq_true.mp cov{c:03d} n h\n" for c in chunks),
          f"end {ns}\n"]
    open(os.path.join(out, "All.lean"), "w").write("\n".join(al))
    print(f"pieces {len(pcs)} in {len(files)} files; chunks {chunks}", file=sys.stderr)


if __name__ == "__main__":
    main()
