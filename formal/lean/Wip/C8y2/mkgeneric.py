#!/usr/bin/env python3
"""One-off: derive the kernel-parametric KernelCap*.lean drafts from the gcd Capstone* sources.

Probe C-8y2. The drafts are then fixed by hand (the committed KernelCap*.lean are the source of
truth, not this script). Every substitution must match the stated number of times.
"""
import os, re, sys
NET = os.path.join(os.path.dirname(__file__), "..", "..", "Formal", "Net")
OUT = sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(__file__), "draft")
os.makedirs(OUT, exist_ok=True)

def rd(n): return open(os.path.join(NET, f"Capstone{n}.lean")).read()

class S:
    def __init__(s, t, name): s.t, s.n = t, name
    def r(s, old, new, k=1):
        c = s.t.count(old)
        if c != k: raise SystemExit(f"{s.n}: expected {k} x {old!r}, found {c}")
        s.t = s.t.replace(old, new)
    def x(s, pat, new, k=1, fl=re.M):
        c = len(re.findall(pat, s.t, fl))
        if c != k: raise SystemExit(f"{s.n}: expected {k} x /{pat}/, found {c}")
        s.t = re.sub(pat, new, s.t, flags=fl)

def strip_doc(t):
    m = re.search(r"\n/-!.*?-/\n", t, re.S)
    return t[:m.start() + 1] + t[m.end():]

HDR = ("open Formal.Net Formal.Net.Kahn Formal.Net.GcdHw Formal.Net.Handshake Formal.Net.Ops\n"
       "open Formal.Net.CapNet hiding R Hh Hh_pr Hh_cn NoEnd JOK FoldOK OpChk\n"
       "open Formal.Net.CapSafe (cntL perL cntL_zero cntL_cons_succ cnt_take cnt_add cnt_periodic perL_ne "
       "perL_mod len_pos cnt_per filter_rank filter_len sel tst sel_rank sel_len)\n"
       "open KD KP\n")

def fix_ns(s, src_ns, extra_open=""):
    s.x(r"^namespace .*?\n((?:open .*\n)+)", "namespace Formal.Net.KCap\n" + HDR + extra_open, 1, re.M)
    s.r(f"end {src_ns}", "end Formal.Net.KCap")

def out(name, imp, doc, s):
    t = strip_doc(s.t)
    t = re.sub(r"^(import .*\n)+", "", t, count=1, flags=re.M)
    open(os.path.join(OUT, f"KernelCap{name}.lean"), "w").write(imp + "\n" + doc + t)

# ---- Hist (SafeHist) ----
s = S(rd("SafeHist"), "SafeHist")
fix_ns(s, "Formal.Net.CapSafe")
s.r("structure TS where", "variable [KD] [KP]\n\n/-- A store with its consumed and produced histories. -/\nstructure TS where".replace("/-- A store with its consumed and produced histories. -/\n", ""), 1)
s.x(r"^def sideOK : Rule → Bool\n(?:  .*\n)+\ntheorem side_ok .*\n\n", "")
s.x(r"^def produced .*\n\n", "")
s.x(r"^def consumed .*\n\n", "")
s.x(r"^theorem final_empty .*?\n(?:  .*\n)+\n", "")
s.x(r"^theorem init_empty .*\n\n", "")
s.r("  fin : y.s = final (Nat.gcd a b)\n", "  fin : y.s = final (spec a b)\n")
s.r("theorem good_exists {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) : ∃ y, Good a b y := by\n"
    "  obtain ⟨⟨n, hn⟩, -⟩ := gcd_hw_graph_computes_gcd ha hb\n",
    "theorem good_exists {a b : Nat} (hd : dom a b) : ∃ y, Good a b y := by\n"
    "  obtain ⟨n, hn⟩ := good_run a b hd\n")
out("Hist", "import Formal.Net.KernelCapDefs\n",
    "/-!\n# Kernel-parametric: per-channel histories of a token run (from C-8m's CapstoneSafeHist)\n-/\n", s)

# ---- Sound (NetDef slice + NetSound) ----
nd = rd("NetDef")
b = re.search(r"/-! ## The histories of a complete run -/\n.*?(?=^def NoEnd)", nd, re.S | re.M).group(0)
s = S(rd("NetSound"), "NetSound")
fix_ns(s, "Formal.Net.CapNet")
s.r("variable {n : Nat} {a b : Nat} {y : TS} {T : Tab}\n",
    "variable [KD] [KP]\n\n" + b + "variable {n : Nat} {a b : Nat} {y : TS} {T : Tab}\n")
s.r("def Hh (a b : Nat) (y : TS) (c : Nat) : List Nat := GcdHw.Gcd.init a b c ++ y.pr c",
    "def Hh (a b : Nat) (y : TS) (c : Nat) : List Nat := init a b c ++ y.pr c")
s.r("(h : 3 ≤ c) : Hh a b y c", "(h : nIn ≤ c) : Hh a b y c")
s.r("(h3 : c ≠ 3) (h250 : c ≠ 250)", "(h3 : c ≠ chEnd) (h250 : c ≠ chOut)")
s.r("(srcV a b) k", "(srcVal a b) k")
s.x(r"  \| src z which d =>\n.*?(?=  \| sink i => trivial)",
    "  | src z which d =>\n"
    "    intro k\n"
    "    rcases hc with ⟨hw, hd⟩ | ⟨hw, hd⟩\n"
    "    · show refT T (Hh a b y) z.val k = srcVal a b which\n"
    "      have h0 : Hh a b y which = [srcVal a b which] := by\n"
    "        simp only [Hh, hy.np which (env_np which (by omega)), List.append_nil]; exact init_src a b which hw\n"
    "      rw [ref_hist T _ hd hnf, h0]; simp [perL, Nat.mod_one]\n"
    "    · subst hw\n"
    "      show refT T (Hh a b y) z.val k = srcVal a b (nIn - 1)\n"
    "      rw [src_start]\n"
    "      exact ref_zero T _ hd hnf k\n", 1, re.M | re.S)
out("Sound", "import Formal.Net.KernelCapHist\n",
    "/-!\n# Kernel-parametric: the checker is sound (from C-8m's CapstoneNetDef / CapstoneNetSound)\n-/\n", s)

# ---- Safe (NetChk tail + Safe + O1) ----
chk = rd("NetChk")
net = re.search(r"/-- The network \(Ops `Net`\). -/\n.*?(?=\ntheorem out0_desc)", chk, re.S).group(0)
s1 = S(rd("Safe"), "Safe"); fix_ns(s1, "Formal.Net.CapNet.Gcd")
s1.r("def omOf", "variable [KD] [KP]\n\n" + net + "\n/-- The oracle of arbiter stage `w`: the labels of the complete token run `y`. -/\ndef omOf".replace("/-- The oracle of arbiter stage `w`: the labels of the complete token run `y`. -/\n", ""))
s1.r("theorem out0_hist {a b : Nat} {y : TS} (hy : Good a b y) : Hh a b y 250 = [Nat.gcd a b] := by\n"
     "  have hf := hy.fifo 250\n  rw [hy.fin, hy.nc 250 (by decide), List.nil_append] at hf\n"
     "  have hi : GcdHw.Gcd.init a b 250 = [] := init_empty a b 250 (by decide)\n"
     "  rw [hi, List.nil_append] at hf\n  rw [Hh_pr (by decide), hf]\n  exact (GcdHw.Gcd.final_store (Nat.gcd a b)).1\n",
     "theorem out0_hist {a b : Nat} {y : TS} (hy : Good a b y) : Hh a b y chOut = [spec a b] := by\n"
     "  have hf := hy.fifo chOut\n  rw [hy.fin, hy.nc chOut out_nc, List.nil_append] at hf\n"
     "  have hi : init a b chOut = [] := init_empty a b chOut out_ge\n"
     "  rw [hi, List.nil_append] at hf\n  rw [Hh_pr out_ge, hf]\n  exact final_out (spec a b)\n")
s1.r("theorem cm_oracle_exists {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) : ∃ y, Good a b y :=\n  good_exists ha hb",
     "theorem cm_oracle_exists {a b : Nat} (hd : dom a b) : ∃ y, Good a b y :=\n  good_exists hd")
s2 = S(rd("O1"), "O1"); fix_ns(s2, "Formal.Net.CapNet.Gcd", "open Formal.Net.Capstone.O1\n")
o1 = strip_doc(s2.t)
o1 = re.sub(r"^(import .*\n)+", "", o1, count=1, flags=re.M)
o1 = o1[o1.index("variable {n : Nat}"):]
o1 = o1.replace("end Formal.Net.KCap", "")
s1.r("end Formal.Net.KCap", "section o1\nopen Formal.Net.Capstone.O1\n" + o1 + "end o1\n\nend Formal.Net.KCap")
s1.t = s1.t.replace("Nat.gcd a b", "spec a b").replace("srcV a b", "srcVal a b")
out("Safe", "import Formal.Net.KernelCapSound\nimport Formal.Net.Capstone\nimport Formal.Net.CapstoneO1Stage\n",
    "/-!\n# Kernel-parametric: safety modulo H_CM_FORCED / H_CUT (from C-8m/8q's CapstoneSafe, CapstoneO1)\n-/\n", s1)

# ---- CutSpine ----
s = S(rd("CutSpine"), "CutSpine"); fix_ns(s, "Formal.Net.CapNet.Gcd")
s.x(r"^def spL : List Bool := .*?^theorem sp_start : sp start = true := by decide\n",
    "variable [KD] [KP]\n\n"
    "theorem noloop' (c : Fin NC) : prodOf c ≠ consOf c := noloop c\n", 1, re.M | re.S)
s.x(r"^def bn \(b : Bool\) : Nat := if b then 1 else 0\n", "")
out("CutSpine", "import Formal.Net.KernelCapSafe\nimport Formal.Net.CapstoneCutCells\n",
    "/-!\n# Kernel-parametric: the control spine and the token's walk (from C-8r's CapstoneCutSpine)\n-/\n", s)

# ---- Cut ----
s = S(rd("Cut"), "Cut"); fix_ns(s, "Formal.Net.CapNet.Gcd", "open Formal.Net.Capstone.O1 Formal.Net.Capstone.Cut\n")
s.r("theorem prod_start : opAt (prodOf start) = .src start 2 0 := rfl\n", "variable [KD] [KP]\n")
s.t = s.t.replace("Nat.gcd a b", "spec a b").replace("srcV a b", "srcVal a b").replace("gcd_hw_", "kernel_")
out("Cut", "import Formal.Net.KernelCapCutSpine\n",
    "/-!\n# Kernel-parametric: H_CUT from H_START_ONCE and H_WALK (from C-8r's CapstoneCut)\n-/\n", s)

# ---- WalkRun ----
s = S(rd("WalkRun"), "WalkRun"); fix_ns(s, "Formal.Net.CapNet.Gcd")
s.r("/-- Invariants of every reachable traced state. -/\n", "variable [KD] [KP]\n\n/-- Invariants of every reachable traced state. -/\n")
s.t = (s.t.replace("x.pr 249", "x.pr cidx").replace("x'.pr 249", "x'.pr cidx")
       .replace("x.cn 13", "x.cn cq1").replace("x'.cn 13", "x'.cn cq1")
       .replace("x.cn 27", "x.cn cq2").replace("x'.cn 27", "x'.cn cq2"))
s.r("by_cases ho : 249 ∈ r.outsL", "by_cases ho : cidx ∈ r.outsL")
s.r("have n13 : 13 ∉ r.insL", "have n13 : cq1 ∉ r.insL")
s.r("have n27 : 27 ∉ r.insL", "have n27 : cq2 ∉ r.insL")
s.r("by_cases hl' : l = 154", "by_cases hl' : l = cl1")
s.r("by_cases hl' : l = 155", "by_cases hl' : l = cl2")
s.t = s.t.replace("lab249_chk", "lab_chk").replace("lab249OK", "labOK")
out("WalkRun", "import Formal.Net.KernelCapCut\n",
    "/-!\n# Kernel-parametric: invariants of the token run for the walk (from C-8s's CapstoneWalkRun)\n-/\n", s)

# ---- Walk ----
s = S(rd("Walk"), "Walk"); fix_ns(s, "Formal.Net.CapNet.Gcd")
s.r("/-! ## Table lemmas -/\n", "variable [KD] [KP]\n\n/-! ## Table lemmas -/\n")
s.r("theorem noend {g : Nat} (hg : g ∈ spine) : g ≠ 3 ∧ g ≠ 250", "theorem noend {g : Nat} (hg : g ∈ spine) : g ≠ chEnd ∧ g ≠ chOut")
s.r("(h3 : gc ≠ 3) (h250 : gc ≠ 250)", "(h3 : gc ≠ chEnd) (h250 : gc ≠ chOut)")
s.t = (s.t.replace(".pr 249", ".pr cidx").replace(".cn 251", ".cn cres")
       .replace("(texec_pre ls x y hls 249)", "(texec_pre ls x y hls cidx)"))
s.r("(hsp2 13 (by decide)).2, (hsp2 27 (by decide)).2", "(hsp2 cq1 cq1_sp).2, (hsp2 cq2 cq2_sp).2")
s.t = s.t.replace("(ha : a < 2 ^ 31) (hb : b < 2 ^ 31)", "(hd : dom a b)")
s.r("  obtain ⟨⟨n, hn⟩, -⟩ := gcd_hw_graph_computes_gcd ha hb\n", "  obtain ⟨n, hn⟩ := good_run a b hd\n")
s.t = s.t.replace("good_run ha hb", "good_run' hd").replace("theorem good_run {a b", "theorem good_run' {a b")
s.t = s.t.replace("a b ha hb", "a b hd")
s.t = s.t.replace("Nat.gcd a b", "spec a b").replace("srcV a b", "srcVal a b").replace("gcd_hw_", "kernel_")
out("Walk", "import Formal.Net.KernelCapWalkRun\n",
    "/-!\n# Kernel-parametric: H_WALK proved, and the final theorem (from C-8s's CapstoneWalk)\n-/\n", s)
print("ok", OUT)
