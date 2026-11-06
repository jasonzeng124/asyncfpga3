#!/usr/bin/env python3
"""gen_rtsel.py (shard A, THE goal, S1 part 3): the output-mux / carry select round trip, as data for
Formal/Target/RoundTripSel.lean, on top of the pip/INIT round trip FormalWit/RTPS (gen_rt.py).

    python3 gen_rtsel.py [--lean DIR] [--out DIR] [--slice 500]

Reads ONLY Lean sources (so the data is about exactly what the kernel sees):
  DIR/Formal/Target/NetPS/G*.lean, Nodes.lean   the decoded netlist (gates, node names)
  DIR/FormalWit/RTPS/F*.lean, Top.lean, Rows.lean  the target features (leaf index = position), the site
                                                     prefix table `siteT`, the old leftovers `lft`
Writes DIR/FormalWit/RTPSSel/ (namespace Formal.Target.RTPSSel.Data):
  N         node-name certificate tree `NT` (every node a select gate reads, with its name) and `hNT`:
            every leaf is right for `DecodedPS.names` (checked chunk-wise against n00..n09)
  S000..    per gate chunk: `RTS.selF` of the chunk = `js.map get` (index certificate, chkI)
  All       the new leftovers `lft2`, `(J ++ lft2).Perm lft`, `sel_perm`
  Final     `roundtrip_sel` (combines with RTPS.Data.roundtrip; needs FormalWit.RTPS.All built)
Untrusted: nothing the theorems depend on; the Python below only proposes certificates.
"""
import glob
from collections import Counter
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))


def arg(name, default):
    return sys.argv[sys.argv.index(name) + 1] if name in sys.argv else default


LEAN = arg("--lean", os.path.normpath(os.path.join(HERE, "../../lean")))
OUT = arg("--out", os.path.join(LEAN, "FormalWit/RTPSSel"))
SL = int(arg("--slice", "250"))
NS = "Formal.Target.RTPSSel.Data"
MP = "FormalWit.RTPSSel"
STR = re.compile(r'"([^"\\]*)"')

# ---- the netlist, from the Lean sources
PG = re.compile(r'^\s*P "([^"]*)" (\d+) (\d+) (\d+) (\d+) (\d+) (\d+)[,\]]?\s*$')
GG = re.compile(r'^\s*⟨"([^"]*)", (\d+), (\d+), \[([^\]]*)\], \[(.*)\], (\d+)⟩[,\]]?\s*$')
chunks = []
for f in sorted(glob.glob(os.path.join(LEAN, "Formal/Target/NetPS/G0*.lean"))):
    gs = []
    for line in open(f):
        m = PG.match(line)
        if m:
            gs.append((m.group(1), 1, 2, [int(m.group(2))], int(m.group(3))))
            continue
        m = GG.match(line)
        if m:
            ins = [int(v) for v in m.group(4).split(",") if v.strip()]
            gs.append((m.group(1), int(m.group(2)), int(m.group(3)), ins, int(m.group(6))))
    m = re.search(r"theorem g(\d+)_len : g\d+\.length = (\d+)", open(f).read())
    assert m and int(m.group(2)) == len(gs), (f, len(gs))
    chunks.append(gs)
gates = [g for c in chunks for g in c]
assert all(g[4] == i for i, g in enumerate(gates)), "gate i drives node i"
ntxt = open(os.path.join(LEAN, "Formal/Target/NetPS/Nodes.lean")).read()
nchunks = []
for k in range(100):
    m = re.search(r"^def n%02d : List String := \[(.*)\]$" % k, ntxt, re.M)
    if not m:
        break
    nchunks.append(STR.findall(m.group(1)))
assert re.search(r"^def names : List String := " + " \\+\\+ ".join("n%02d" % k for k in range(len(nchunks))) + "$",
                 ntxt, re.M)
names = [s for c in nchunks for s in c]
noff = [sum(len(c) for c in nchunks[:k]) for k in range(len(nchunks))]

# ---- the target features, site table and old leftovers, from FormalWit/RTPS
FT = {}
for f in sorted(glob.glob(os.path.join(LEAN, "FormalWit/RTPS/F*.lean"))):
    for s, j in re.findall(r'\(\.leaf "([^"\\]*)" (\d+)\)', open(f).read()):
        FT[int(j)] = s
N = len(FT)
assert sorted(FT) == list(range(N))
top = open(os.path.join(LEAN, "FormalWit/RTPS/Top.lean")).read()
assert "def N : Nat := %d" % N in top
site_pre = dict(re.findall(r'\(\.leaf "([^"\\]*)" "([^"\\]*)"\)', top.split("def siteT")[1].split("\n")[0]))
pos = {s: j for j, s in FT.items()}
rtxt = open(os.path.join(LEAN, "FormalWit/RTPS/Rows.lean")).read()
m = re.search(r"^def rowL : List \(List Nat\) := (\[.*\])$", rtxt, re.M)
LFT = [x for r in eval(m.group(1)) for x in r]
assert LFT == sorted(LFT) and len(set(LFT)) == len(LFT)


# ---- the Python mirror of RoundTripSel.selF
def splitC(s):
    return s.split(".")


def out_sel(L, pin):
    if pin == L + "6":
        return "O6"
    if pin == L + "5":
        return "O5"
    if pin == L + "5Q":
        return L + "5Q"
    if pin in ("F7A", "F7B"):
        return "F7"
    if pin == "F8":
        return "F8"
    if pin.startswith("XOR"):
        return "XOR"
    if pin.startswith("CO"):
        return "CY"
    return None


looked = set()   # node indices the kernel looks up


def nm(i):
    looked.add(i)
    return names[i] if i < len(names) else ""


def pre(site):
    return site_pre.get(site, "")


def is_const(s):
    return s in ("CONST0", "CONST1")


def sel_f(g):
    name, k, _, ins, _ = g
    if k == 1 and name.startswith("hop "):
        if not (name.endswith("MUX") and len(name) >= 4) or len(ins) != 1:
            return []
        L = name[-4]
        p = splitC(nm(ins[0]))
        if len(p) != 2 or not p[0].startswith("SLICE"):
            return []
        o = out_sel(L, p[1])
        if o is None or pre(p[0]) == "":
            return []
        return ["%s.%sOUTMUX.%s" % (pre(p[0]), L, o)]
    if k == 10 and name.endswith(".CARRY4.CO3"):
        if len(ins) != 10:
            return []
        p = splitC(name)
        if len(p) != 3:
            return []
        pr = pre(p[0])
        if pr == "":
            return []
        ci, cy = nm(ins[0]), nm(ins[1])
        pc = "CIN" if not is_const(ci) else "AX" if not is_const(cy) else "C1" if cy == "CONST1" else "C0"
        out = ["%s.PRECYINIT.%s" % (pr, pc)]
        for j, l in enumerate("ABCD"):
            d = nm(ins[6 + j])
            if d.startswith("SLICE") and d.endswith("5"):
                out.append("%s.CARRY4.%sCY0" % (pr, l))
        return out
    return []


nopre = Counter()
lset = set(LFT)
hit = {}
GI = []
for c, gs in enumerate(chunks):
    gi = []
    for g in gs:
        one = []
        for f in sel_f(g):
            if f not in pos:
                sys.exit("gen_rtsel: gate %s produces %s, not in the target" % (g[0], f))
            j = pos[f]
            if j not in lset:
                sys.exit("gen_rtsel: gate %s produces %s, not an old leftover" % (g[0], f))
            if j in hit:
                sys.exit("gen_rtsel: %s produced twice (%s, %s)" % (f, hit[j], g[0]))
            hit[j] = g[0]
            one.append(j)
        gi.append(one)
    GI.append(gi)
LFT2 = [j for j in LFT if j not in hit]
cls = Counter(re.sub(r"^.*\.(PRECYINIT|CARRY4|[A-D]OUTMUX)\.", r"\1.", FT[j]) for j in hit)
print("gen_rtsel: %d target features, %d old leftovers, %d re-encoded selects, %d new leftovers; %d names looked up"
      % (N, len(LFT), len(hit), len(LFT2), len(looked)))
print("  ", sorted(cls.items()))


def q(s):
    return '"' + s + '"'


def itree(items, lo, hi):
    """ITree over (name, index) items[lo:hi] (sorted by index), keyed by index."""
    if hi <= lo:
        return ".nil"
    if hi - lo == 1:
        return "(.leaf %s %d)" % (q(items[lo][0]), items[lo][1])
    mid = (lo + hi) // 2
    return "(.node %d %s %s)" % (items[mid][1], itree(items, lo, mid), itree(items, mid, hi))


os.makedirs(OUT, exist_ok=True)
_open = open


class _W:
    """Write a file only if its content changes (keeps mtimes, so built oleans stay current)."""
    def __init__(self, path):
        self.path, self.buf = path, []

    def __enter__(self):
        return self

    def write(self, t):
        self.buf.append(t)

    def __exit__(self, *a):
        t = "".join(self.buf)
        if not (os.path.exists(self.path) and _open(self.path).read() == t):
            with _open(self.path, "w") as f:
                f.write(t)


def wopen(path, mode="r"):
    return _W(path) if mode == "w" else _open(path, mode)


HDR = "/-! GENERATED by formal/tools-A/target/gen_rtsel.py. Do not edit. -/\n\nset_option linter.unusedSimpArgs false\n\n"
OPEN = "namespace %s\nopen Formal.Target Formal.Target.RT Formal.Target.RTS Formal.Target.DecodedPS\n\n" % NS
END = "\nend %s\n" % NS

# ---- N.lean: the name certificate
K = len(nchunks)
per = []
for k in range(K):
    lo, hi = noff[k], noff[k] + len(nchunks[k])
    per.append([(names[i], i) for i in sorted(looked) if lo <= i < hi])
assert all(i < len(names) for i in looked)
with wopen(os.path.join(OUT, "N.lean"), "w") as f:
    f.write("import Formal.Target.NetPS.Nodes\nimport Formal.Target.RoundTripSel\n\n" + HDR + OPEN)
    for k in range(K):
        f.write("theorem nl%02d : n%02d.length = %d := by decide +kernel\n\n" % (k, k, len(nchunks[k])))
    for k in range(K):
        f.write("set_option maxRecDepth 100000 in\ndef nt%02d : ITree := %s\n\n" % (k, itree(per[k], 0, len(per[k]))))
    # the whole tree: split at the chunk boundaries (keys < noff[k+1] go left)

    def top_tree(lo, hi):
        if hi - lo == 1:
            return "nt%02d" % lo
        mid = (lo + hi) // 2
        return "(.node %d %s %s)" % (noff[mid], top_tree(lo, mid), top_tree(mid, hi))
    f.write("/-- Every node a select gate reads, with its name (certificate; checked by `hNT`). -/\n")
    f.write("def NT : ITree := %s\n\n" % top_tree(0, K))
    for k in range(K):
        A = " ++ ".join("n%02d" % i for i in range(k)) or "[]"
        B = " ++ ".join("n%02d" % i for i in range(k + 1, K)) or "[]"
        lens = ", ".join("nl%02d" % i for i in range(k))
        f.write("set_option maxRecDepth 100000 in\n")
        f.write("theorem hn%02d : ∀ p ∈ nt%02d.leaves, names.getD p.2 \"\" = p.1 := by\n" % (k, k))
        f.write("  have e : names = (%s) ++ n%02d ++ (%s) := by simp only [names, List.append_assoc, List.nil_append, List.append_nil]\n" % (A, k, B))
        f.write("  rw [e]\n  exact chkN_mid _ _ _ %d (by simp only [List.length_append, List.length_nil%s]) _ (by decide +kernel)\n\n"
                % (noff[k], (", " + lens) if lens else ""))

    def top_proof(lo, hi):
        if hi - lo == 1:
            return "hn%02d" % lo
        mid = (lo + hi) // 2
        return "(ITree.forall_node _ _ _ %s %s)" % (top_proof(lo, mid), top_proof(mid, hi))
    f.write("/-- Every leaf of `NT` is the name of its node. -/\n")
    f.write("theorem hNT : ∀ p ∈ NT.leaves, names.getD p.2 \"\" = p.1 :=\n  %s\n\n" % top_proof(0, K))
    f.write("/-- The checked node-name lookup the kernel computes with. -/\n")
    f.write("def nmc : Nat → String := nmC NT (fun i => names.getD i \"\")\n\n")
    f.write("theorem nmc_eq : nmc = fun i => names.getD i \"\" := nmC_eq NT _ hNT\n")
    f.write(END)

# ---- S000..: per gate chunk
OPENS = OPEN.replace("Formal.Target.DecodedPS\n", "Formal.Target.DecodedPS Formal.Target.RTPS.Data\n")
nC = len(chunks)
for c in range(nC):
    gi = GI[c]
    sl = [(a, min(SL, len(gi) - a)) for a in range(0, len(gi), SL)]
    with wopen(os.path.join(OUT, "S%03d.lean" % c), "w") as f:
        f.write("import %s.N\nimport FormalWit.RTPS.Top\nimport Formal.Target.NetPS.G%03d\n\n" % (MP, c) + HDR + OPENS)
        for k_, (a_, n_) in enumerate(sl):
            cert = [x for gg in gi[a_:a_ + n_] for x in gg]
            f.write("def j%03d_%d : List Nat := [%s]\n\n" % (c, k_, ", ".join(map(str, cert))))
            f.write("theorem s%03d_%d : ((g%03d.drop %d).take %d).flatMap (selF pre nmc) = j%03d_%d.map get :=\n"
                    "  chkI_sound T hidx _ _ (by decide +kernel)\n\n" % (c, k_, c, a_, n_, c, k_))
        f.write("def jc%03d : List Nat := %s\n\n" % (c, " ++ (".join("j%03d_%d" % (c, k_) for k_ in range(len(sl))) + " ++ []" + ")" * (len(sl) - 1)))
        term = "fm_drop_len (selF pre nmc) g%03d %d (Nat.le_of_eq g%03d_len)" % (c, len(gi), c)
        for k_ in reversed(range(len(sl))):
            a_, n_ = sl[k_]
            term = "fm_drop_take (selF pre nmc) g%03d %d %d s%03d_%d (%s)" % (c, a_, n_, c, k_, term)
        f.write("set_option maxRecDepth 100000 in\ntheorem es%03d : g%03d.flatMap (selF pre nmc) = jc%03d.map get := by\n"
                "  have h := %s\n  rw [List.drop_zero] at h\n  rw [h, jc%03d]\n  simp only [List.map_append, List.map_nil]\n"
                % (c, c, c, term, c))
        f.write(END)

# ---- All.lean
J = [x for gi in GI for gg in gi for x in gg]
assert sorted(J + LFT2) == LFT
DOC = """/-!
# THE round trip of the decoder, part 3: output-mux and carry selects (S1)

GENERATED by formal/tools-A/target/gen_rtsel.py.

**Plainly.** `RTPS.Data.roundtrip` shows that the pips and LUT6 INIT bits re-encoded from the Lean gates plus
%d leftover features are exactly the target's read-back features. Here `RTS.selF` re-encodes, from the Lean gates
and the names of the nodes they read (`net.names`), every slice output-mux select (`<L>OUTMUX.<..>`, from the
`hop …<L>MUX` gates) and every CARRY4 `PRECYINIT` / `<L>CY0` select (from the `CARRY4.CO3` gates). `sel_perm`: those
%d features plus %d new leftovers `lft2` are exactly the old leftovers, each once; with `roundtrip`
(`roundtrip_sel_of`, and `roundtrip_sel` in Final.lean) the extended re-encoder `RTS.featsX` plus `lft2` is exactly
the target's features. Node names are looked up through the certificate tree `NT`, checked against
`DecodedPS.names` (N.lean); the site prefixes are RTPS's `pre` (prjxray data, as before).

**Not shown.** That the select's meaning in the Spec matches the hop / carry gate (the hop gate copies the node it
reads; the CARRY4 gates' tables are the decoder's); and, as for `roundtrip`, FASM parsing and the site table.
-/

"""
with wopen(os.path.join(OUT, "All.lean"), "w") as f:
    f.write("\n".join("import %s.S%03d" % (MP, c) for c in range(nC)) + "\nimport FormalWit.RTPS.Rows\nimport Formal.Target.NetPS.All\n\n" + DOC + OPENS)
    f.write("def J : List Nat := %s\n\n" % (" ++ (".join("jc%03d" % c for c in range(nC)) + ")" * (nC - 1)))
    f.write("set_option maxRecDepth 100000 in\ntheorem hselc : gates.flatMap (selF pre nmc) = J.map get := by\n"
            "  simp only [gates, List.flatMap_append, %s, J, List.map_append]\n\n" % ", ".join("es%03d" % c for c in range(nC)))
    f.write("theorem hsel : gates.flatMap (selF pre (fun i => net.names.getD i \"\")) = J.map get := by\n"
            "  rw [show (fun i => net.names.getD i \"\") = nmc from nmc_eq.symm]\n  exact hselc\n\n")
    f.write("set_option maxRecDepth 100000 in\n/-- The new leftovers (%d target features). -/\ndef lft2 : List Nat := [%s]\n\n"
            % (len(LFT2), ", ".join(map(str, LFT2))))
    f.write("theorem hs2 : msortF 20 (J ++ lft2) = lft := by decide +kernel\n\n")
    f.write("theorem hperm2 : (J ++ lft2).Perm lft := by\n  have h := msortF_perm 20 (J ++ lft2)\n  rw [hs2] at h\n  exact h.symm\n\n")
    f.write("/-- **The selects**: the select features re-encoded from the gates plus the new leftovers are exactly the old\n"
            "leftovers, each once. -/\n")
    f.write("theorem sel_perm : ((gates.flatMap (selF pre (fun i => net.names.getD i \"\"))) ++ lft2.map get).Perm (lft.map get) := by\n"
            "  rw [hsel, ← List.map_append]\n  exact hperm2.map get\n\n")
    f.write("/-- The extended round trip, from the pip/INIT one (`RTPS.Data.roundtrip` has exactly this hypothesis's type). -/\n")
    f.write("theorem roundtrip_sel_of (hrt : ((gates.flatMap (feats pre)) ++ lft.map get).Perm tf) :\n"
            "    ((gates.flatMap (featsX pre (fun i => net.names.getD i \"\"))) ++ lft2.map get).Perm tf :=\n"
            "  roundtrip_ext gates pre _ get lft lft2 tf hrt sel_perm\n")
    f.write(END)
with wopen(os.path.join(OUT, "Final.lean"), "w") as f:
    f.write("import %s.All\nimport FormalWit.RTPS.All\n\n" % MP + HDR + OPENS)
    f.write("/-- **The extended round trip**: pips, LUT6 INIT bits, output-mux and carry selects re-encoded from the Lean\n"
            "gates (`RTS.featsX`), plus the %d leftover features `lft2`, are exactly the target's read-back features,\n"
            "each once. -/\n" % len(LFT2))
    f.write("theorem roundtrip_sel :\n    ((gates.flatMap (featsX pre (fun i => net.names.getD i \"\"))) ++ lft2.map get).Perm tf :=\n"
            "  roundtrip_sel_of roundtrip\n")
    f.write(END)
print("gen_rtsel: wrote %s (N, S000..S%03d, All, Final)" % (OUT, nC - 1))
