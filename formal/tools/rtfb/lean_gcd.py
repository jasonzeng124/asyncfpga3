#!/usr/bin/env python3
"""Probe C-10f / C-10f2: write Formal/Timing/RtFbGcd.lean (summary theorems over the gcd_hw seeds
whose data files RtFbGcdS<seed>.lean exist; with --freq F: RtFbGcdF<F>.lean over RtFbGcdF<F>S<seed>).
Expected numbers come from rtfb_design.py's reports (Python); the kernel re-checks every one.
C-10f2: the data carries the driver-side OUTMUX hop; per one-corner variant v the theorem
gcdS_v_exact (passing entries safe in every run, failing entries have a violating fixed run)
replaces the conditional reading of C-10f's gcdS_slowE_safe / gcdS_fastE_safe, which are still
emitted, unchanged, whenever they hold.
    python3 -I formal/tools/rtfb/lean_gcd.py [--freq F] [--nextpnr SHA16] SEED...
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.join(HERE, "..", "..", "lean", "Formal", "Timing")
V = ["indep", "fast", "slow", "fastE", "slowE", "sdf"]
args = sys.argv[1:]
FREQ, NPR = None, "?"
while args and args[0].startswith("--"):
    if args[0] == "--freq":
        FREQ = args[1]
    elif args[0] == "--nextpnr":
        NPR = args[1]
    args = args[2:]
seeds = args
PRE = "RtFbGcd" + ("F%s" % FREQ if FREQ else "")
TAG = lambda s: s + ("_f%s" % FREQ if FREQ else "")  # noqa: E731
P = "gcd" + ("f%s_" % FREQ if FREQ else "")
info = {}
for s in seeds:
    t = open(os.path.join(HERE, "build", "gcd", "s%s" % TAG(s), "rtd.txt")).read()
    assert "driver-side OUTMUX hop: on;" in t, s
    fail = {v: int(re.search(r"^%s\s+failing (\d+)/" % v, t, re.M).group(1)) for v in V}
    worst = {v: int(re.search(r"^%s\s+failing \d+/\d+\s+worst \((-?\d+)," % v, t, re.M).group(1)) for v in V}
    nce = int(re.search(r"C-elements (\d+),", t).group(1))
    nlean = int(re.search(r"def nEntries : Nat := (\d+)", open(os.path.join(LEAN, "%sS%s.lean" % (PRE, s))).read()).group(1))
    nnone = int(re.search(r"no response path inside the bound: (\d+)", t).group(1))
    assert nlean + nnone == nce
    info[s] = (fail, worst, nce, nlean, nnone)
L = ["import Formal.Timing.RtFbCore"] + ["import Formal.Timing.%sS%s" % (PRE, s) for s in seeds]
L.append('''
/-!
# RT_FB on every C-element of the routed, shipped gcd_hw kernel (probes C-10f, C-10f2)

gcd_hw = the board-measured design: bdc-compiled gcd (cloud/fixtures/frontend/gcd) + cells/hw/gcd_rig.v,
built by the project flow (cells/hw/build_hw.sh gcd_hw, BDC_SELECT_PADS = cells/hw/gcd_hw_pads.json,
BD_RLOC=v4, %s, nextpnr %s, toolchain.sh ok, fasm_audit PASS; routes by
formal/tools/rtfb/route_gcd.sh = C-10e's recipe), read back from the bitstream by
formal/tools/rtfb/rtfb_design.py.

C-10f2 (2026-10-29): routes that leave a slice through AMUX..DMUX now carry the driver-side OUTMUX
hop (prjxray slicel/slicem.sdf, e.g. a6lut -> amux (0.071::0.088)(0.168::0.209) ns), on the
feedback and on every response net.  C-10f's data had no such hop (audit P4).
''' % ("--freq %s" % FREQ if FREQ else "no --freq (BOARD-QUEUE #1's command; nextpnr's 12 MHz default)", NPR) + '''
Data `RtFbGcdS<seed>`: one entry per C-element (bd_c2/c2n/_set/c3/c4) that has a response path
whose H_INDEP lower bound is below its feedback's H_INDEP upper bound: the tree of its feedback
route and every such simple response path through any number of LUTs.  The other C-elements
(H_CONE, Python-checked by Dijkstra, not in Lean) have no response that can arrive before the
latest feedback in ANY bound variant.

| seed | C-elements | in Lean | failing indep | fast | slow | fastE | slowE | worst slowE (ps) |
|---|---|---|---|---|---|---|---|---|''')
for s in seeds:
    f, w, nce, nl, nn = info[s]
    L.append("| %s | %d | %d | %s | %d |" % (s, nce, nl, " | ".join(str(f[v]) for v in V[:5]), w["slowE"]))
L.append("-/")
L.append('''
namespace Formal.Timing.RtFb
open Formal.Timing Formal.Net Formal.Timing.Routed
''')
for s in seeds:
    f, w, nce, nl, nn = info[s]
    n = "%sS%s" % (PRE, s)
    s = P[3:] + s
    L.append("theorem gcd%s_len : %s.slowE.length = %d := by decide +kernel" % (s, n, nl))
    L.append("theorem gcd%s_pass :\n    %s := by decide +kernel" % (s, " ∧\n    ".join(
        "nPass %s.%s = %d" % (n, v, nl - f[v]) for v in V)))
    L.append("theorem gcd%s_worst :\n    %s := by decide +kernel" % (s, " ∧\n    ".join(
        "worstSlack %s.%s = some (%d)" % (n, v, w[v]) for v in V)))
    L.append("theorem gcd%s_wf : %s.indep.all wfOne = true ∧ %s.fastE.all wfOne = true ∧ %s.slowE.all wfOne = true := by\n  decide +kernel" % (s, n, n, n))
    L.append("theorem gcd%s_sep : %s.indep.all sepOne = true := by decide +kernel" % (s, n))
    L.append("theorem gcd%s_wf1 : %s.fast.all wfOne = true ∧ %s.slow.all wfOne = true := by\n  decide +kernel" % (s, n, n))
    L.append("theorem gcd%s_sep1 : %s.fast.all sepOne = true ∧ %s.slow.all sepOne = true ∧ %s.fastE.all sepOne = true ∧ %s.slowE.all sepOne = true := by\n  decide +kernel" % (s, n, n, n, n))
    for v, wf, sp in (("fast", "wf1.1", "sep1.1"), ("slow", "wf1.2", "sep1.2.1"), ("fastE", "wf.2.1", "sep1.2.2.1"),
                      ("slowE", "wf.2.2", "sep1.2.2.2")):
        L.append('''/-- gcd_hw seed %s, one-corner variant `%s`: the %d passing entries hold RT_FB in every run, the %d
failing entries each have a real violating fixed-delay run. -/
theorem gcd%s_%s_exact :
    (∀ e ∈ %s.%s, rtOne e = true → ∀ {sig : Nat → Trace}, Run (ofBuckets e.1) sig →
      ∀ r ∈ e.2.1, ∀ s t, changes (sig e.2.2.1) s → changes (sig r) t → s ≤ t) ∧
    (∀ e ∈ %s.%s, rtOne e = false → ∃ r ∈ e.2.1, ∃ sig, Nonempty (FixedRun (ofBuckets e.1) sig) ∧
      ∃ s t, changes (sig e.2.2.1) s ∧ changes (sig r) t ∧ t < s) :=
  ⟨rt_sound_of _ gcd%s_%s, rt_violated_of _ gcd%s_%s gcd%s_%s⟩
''' % (s, v, nl - f[v], f[v], s, v, n, v, n, v, s, wf, s, wf, s, sp))
    for v, k in (("slowE", 2), ("fastE", 1)):
        if f[v]:
            continue
        L.append('''/-- gcd_hw seed %s, H_ONE_CORNER + H_RC_EXACT (%s): every C-element in the data satisfies RT_FB
in every run. -/
theorem gcd%s_%s_safe : ∀ e ∈ %s.%s, ∀ {sig : Nat → Trace}, Run (ofBuckets e.1) sig →
    ∀ r ∈ e.2.1, ∀ s t, changes (sig e.2.2.1) s → changes (sig r) t → s ≤ t := by
  have hall : %s.%s.all rtOne = true := by decide +kernel
  intro e he
  exact rt_sound_of _ gcd%s_wf.%s e he (List.all_eq_true.1 hall e he)
''' % (s, v, s, v, n, v, n, v, s, "2.2" if v == "slowE" else "2.1"))
    L.append('''/-- gcd_hw seed %s, H_INDEP: the %d failing C-elements each have a real violating fixed-delay run. -/
theorem gcd%s_indep_violated : ∀ e ∈ %s.indep, rtOne e = false → ∃ r ∈ e.2.1, ∃ sig,
    Nonempty (FixedRun (ofBuckets e.1) sig) ∧ ∃ s t, changes (sig e.2.2.1) s ∧ changes (sig r) t ∧ t < s :=
  rt_violated_of _ gcd%s_wf.1 gcd%s_sep
''' % (s, f["indep"], s, n, s, s))
L.append("end Formal.Timing.RtFb")
open(os.path.join(LEAN, PRE + ".lean"), "w").write("\n".join(L) + "\n")
