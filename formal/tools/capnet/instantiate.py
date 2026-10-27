#!/usr/bin/env python3
"""instantiate: the kernel-specific Lean layer of the circuit-safety proof, for a new kernel.

Probe C-8y. The gcd_hw circuit-safety chain (C-8m/8q/8r) is mostly generic Lean that happens to
be written against gcd's `rules`. The generic modules are IMPORTED unchanged (CapstoneNetDef's
operator kinds, gate models `Cell`, equations, `cell_op`, the descriptor solution `refT`;
CapstoneSafePer; Capstone's `latched_const`; CapstoneCM / O1Stage / O1Cells / CutCells). The
modules that mention the kernel's `rules`, its init/final store or its spec are COPIED from the
gcd files and rewritten here by an explicit substitution table. Every substitution must match
exactly the stated number of times, so a change to a gcd source file makes this script fail
loudly instead of producing a silently different proof (check.sh then reports drift).

    instantiate.py --kernel ipow [--out-dir formal/lean/Formal/Net]

Inputs: the gcd sources under formal/lean/Formal/Net (read-only), the kernel profile below,
and `capnet.py --kernel K spine` (for `spL` / `start`). Outputs: <Prefix>SafeHist, NetDef,
NetSound, NetChk, Safe, O1, CutSpine, Cut (.lean). <Prefix>Net/Links/Ring come from capnet.py.

A profile is the whole kernel-specific input. For a third kernel with the same shape (two data
arguments + start on channels 0,1,2; one result; 2- or 3-input control_merges) it is ~15 lines:
the graph module, the spec, the token-level existence theorem, the out/end channels.
"""
import argparse, os, re, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
NET = os.path.join(ROOT, "formal", "lean", "Formal", "Net")

PROFILES = {
    "ipow": dict(
        prefix="IpowCap", ns="Formal.Net.IpowCap", label="ipow_ps",
        gmod="Formal.Net.IpowHw", gns="Formal.Net.IpowHw", gq="IpowHw", live="Formal.Net.IpowHwLive",
        spec="IpowHw.ipowSpec a b", tpre="ipow_hw_", tpre2="ipowhw_", chOut=57, chEnd=4,
        # final_empty: the final store is empty off out0/end (the kernel's own store lemma)
        final_empty="theorem final_empty (r c : Nat) (h3 : c ≠ 4) (h250 : c ≠ 57) : final r c = [] :=\n"
                    "  final_store_only r c h250 h3",
        # the token-level theorem: a complete run from init a b to final (spec)
        good_hyps="(a : Nat) {b : Nat} (hb : b < 2 ^ 32)",
        good_args="a hb",
        good_thm="ipow_hw_graph_computes_pow a hb",
        input_doc="for every Nat `a` (base) and every i32 bit pattern `b < 2^32` (exponent)",
        # H_WALK proof (C-8s's, instantiated). gcd's 3-input cascade (stage-1 output acc251 over
        # control_merge12 = rules 154/155: cm 13|27 -> res 251, idx 249) has no counterpart here;
        # its constants are mapped to a real 2-input control_merge (rules 19/20: cm 22|41 -> res 39,
        # idx 40), for which every cascade fact the proof states is still true (kernel-checked),
        # and `acc` to a non-spine channel, so the cascade branches are never taken.
        walk=dict(acc=0, q1=22, q2=41, res=39, idx=40, l1=19, l2=20,
                  hyps="(hb : b < 2 ^ 32)", args="a b hb", grun="good_run hb",
                  gthm="IpowHw.ipow_hw_graph_computes_pow a hb"),
    ),
}

GCD_SPEC = "Nat.gcd a b"
SAFEPER = ("cntL perL cntL_zero cntL_cons_succ cnt_take cnt_add cnt_periodic perL_ne perL_mod len_pos "
           "cnt_per filter_rank filter_len sel tst sel_rank sel_len")
HIDE = "R Hh Hh_pr Hh_cn NoEnd JOK FoldOK OpChk"
COPIED = ["SafeHist", "NetDef", "NetSound", "NetChk", "Safe", "O1", "CutSpine", "Cut", "WalkTab", "WalkRun", "Walk"]


class Sub:
    def __init__(self, text, name):
        self.t, self.name, self.log = text, name, []

    def rep(self, old, new, n=1):
        k = self.t.count(old)
        if k != n:
            raise SystemExit(f"[instantiate] {self.name}: expected {n} x {old!r}, found {k}")
        self.t = self.t.replace(old, new)
        self.log.append((old, new, n))

    def rex(self, pat, new, n=1, flags=re.M):
        k = len(re.findall(pat, self.t, flags))
        if k != n:
            raise SystemExit(f"[instantiate] {self.name}: expected {n} x /{pat}/, found {k}")
        self.t = re.sub(pat, new, self.t, flags=flags)
        self.log.append((pat, new, n))


def banner(P, src, extra=""):
    return (f"/-!\n# INSTANTIATED for {P['label']} by formal/tools/capnet/instantiate.py -- DO NOT EDIT\n\n"
            f"Source: `Formal/Net/{src}.lean` (the gcd_hw proof), rewritten by the substitution table in\n"
            f"instantiate.py (namespace, the kernel's graph module, out/end channels {P['chOut']}/{P['chEnd']}, the spec\n"
            f"`{P['spec']}` in place of `{GCD_SPEC}`, theorem prefix `{P['tpre']}`). Everything else is the gcd text;\n"
            f"its comments below still speak of gcd_hw where they describe the shared argument.{extra}\n-/\n\n")


def opens_std(P):
    return (f"open Formal.Net.CapNet hiding {HIDE}\n"
            f"open Formal.Net.CapSafe ({SAFEPER})\n")


def common(s, P):
    """Substitutions valid in every copied file except the namespace/open lines."""
    pre = P["prefix"]
    for m in COPIED:
        s.t = s.t.replace(f"import Formal.Net.Capstone{m}\n", f"import Formal.Net.{pre}{m}\n")
    s.t = s.t.replace("import Formal.Net.CapstoneNet\n", f"import Formal.Net.{pre}Net\n")
    s.t = s.t.replace(GCD_SPEC, P["spec"])
    s.t = s.t.replace("gcd_hw_", P["tpre"]).replace("gcdhw_", P["tpre2"])
    s.t = s.t.replace("GcdHw.Gcd.", P["gq"] + ".")


def strip_header(t):
    """Drop the source's module docstring (the first /-! ... -/ after the imports)."""
    m = re.search(r"\n/-!.*?-/\n", t, re.S)
    return t[:m.start() + 1] + t[m.end():] if m else t


def put_banner(t, P, src, extra=""):
    t = strip_header(t)
    lines = t.split("\n")
    k = 0
    while k < len(lines) and (lines[k].startswith("import ") or lines[k] == ""):
        k += 1
    imps = [l for l in lines[:k] if l.startswith("import ")]
    return "\n".join(imps) + "\n\n" + banner(P, src, extra) + "\n".join(lines[k:])


def read(name):
    return open(os.path.join(NET, f"Capstone{name}.lean")).read()


def inst_safehist(P):
    s = Sub(read("SafeHist"), "SafeHist")
    s.rep("import Formal.Net.GcdHwLive\n", f"import {P['live']}\n")
    s.rep("namespace Formal.Net.CapSafe\n", f"namespace {P['ns']}\n")
    s.rep("end Formal.Net.CapSafe", f"end {P['ns']}")
    s.rep("open Formal.Net.Kahn Formal.Net.GcdHw Formal.Net.GcdHw.Gcd\n",
          f"open Formal.Net.Kahn Formal.Net.GcdHw {P['gns']}\n")
    s.rex(r"^theorem final_empty .*?\n(?:  .*\n)+", P["final_empty"] + "\n")
    s.rep("theorem good_exists {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) : ∃ y, Good a b y := by\n"
          "  obtain ⟨⟨n, hn⟩, -⟩ := gcd_hw_graph_computes_gcd ha hb\n",
          f"theorem good_exists {P['good_hyps']} : ∃ y, Good a b y := by\n"
          f"  obtain ⟨⟨n, hn⟩, -⟩ := {P['good_thm']}\n")
    s.rep("  fin : y.s = final (Nat.gcd a b)\n", f"  fin : y.s = final ({P['spec']})\n")
    common(s, P)
    return put_banner(s.t, P, "CapstoneSafeHist")


def inst_netdef(P):
    src = read("NetDef")
    a = re.search(r"^abbrev R : List Rule := GcdHw\.Gcd\.rules\n", src, re.M)
    b = re.search(r"/-! ## The histories of a complete run -/\n.*?^def NoEnd .*?\n", src, re.S | re.M)
    c = re.search(r"/-- Justification `j` produces.*?(?=^end Formal\.Net\.CapNet)", src, re.S | re.M)
    assert a and b and c, "NetDef markers moved"
    body = (f"abbrev R : List Rule := {P['gq']}.rules\n\n" + b.group(0) + "\n/-! ## The checker -/\n\n"
            "variable {n : Nat}\n\n" + c.group(0))
    t = (f"import Formal.Net.{P['prefix']}SafeHist\nimport Formal.Net.CapstoneNetDef@\nimport Formal.Net.CapstoneSafePer\n\n"
         f"namespace {P['ns']}\n"
         f"open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.GcdHw\n" + opens_std(P) + "\n" + body +
         f"end {P['ns']}\n")
    s = Sub(t, "NetDef")
    s.rep("def NoEnd (g : Nat) : Prop := g ≠ 3 ∧ g ≠ 250\n",
          f"def NoEnd (g : Nat) : Prop := g ≠ {P['chEnd']} ∧ g ≠ {P['chOut']}\n")
    s.rep("(h3 : c ≠ 3) (h250 : c ≠ 250)", f"(h3 : c ≠ {P['chEnd']}) (h250 : c ≠ {P['chOut']})")
    common(s, P)
    s.rep("import Formal.Net.CapstoneNetDef@\n", "import Formal.Net.CapstoneNetDef\n")
    extra = ("\n\nOnly the kernel-dependent slice of CapstoneNetDef is copied: `R`, the run histories `Hh`,\n"
             "`NoEnd`, and the checker `JOK`/`FoldOK`/`OpChk`. The operator kinds `K`, the gate models\n"
             "`Cell`, the equations `Eqn`, `Forced`, `cell_op` and the solution `refT` are gcd's own\n"
             "(imported from `Formal.Net.CapstoneNetDef`, namespace `Formal.Net.CapNet`).")
    return put_banner(s.t, P, "CapstoneNetDef", extra)


def retarget(s, P, src_ns):
    s.rep(f"namespace {src_ns}\n", f"namespace {P['ns']}\n")
    s.rep(f"end {src_ns}", f"end {P['ns']}")


def fix_opens(s, P):
    """Rewrite the `open` lines: drop CapNet / CapSafe (re-opened in the standard way)."""
    lines = s.t.split("\n")
    out, done = [], False
    for l in lines:
        if l.startswith("open "):
            toks = l[5:].split()
            keep = [x for x in toks if x not in ("Formal.Net.CapNet", "Formal.Net.CapSafe")]
            if keep:
                out.append("open " + " ".join(keep))
            if not done:
                out.append(opens_std(P).rstrip("\n"))
                done = True
        else:
            out.append(l)
    assert done, (s.name, "no open line")
    s.t = "\n".join(out)


def inst_generic(P, name, src_ns, subs=()):
    s = Sub(read(name), name)
    retarget(s, P, src_ns)
    fix_opens(s, P)
    for old, new, n in subs:
        s.rep(old, new, n)
    common(s, P)
    return put_banner(s.t, P, f"Capstone{name}")


def inst_walk(P, kernel):
    """C-8s's H_WALK proof (CapstoneWalkTab/Run/Walk), instantiated."""
    W = P["walk"]
    E, O = P["chEnd"], P["chOut"]
    tabs = subprocess.run([sys.executable, os.path.join(HERE, "capnet.py"), "--kernel", kernel, "walktab"],
                          check=True, capture_output=True, text=True).stdout
    out = {}
    def opens_fix(sub):
        sub.t = re.sub(r"^(open .*)\bFormal\.Net\.GcdHw\.Gcd\b", r"\1" + P["gns"], sub.t, flags=re.M)
    t = Sub(read("WalkTab"), "WalkTab")
    t.rex(r"^def spN : List Nat := .*?^def recs : .*?$\n", tabs, flags=re.M | re.S)
    t.rep("def acc : Fin NC := 463\n", f"def acc : Fin NC := {W['acc']}\n")
    t.rep("gc != 3 && gc != 250", f"gc != {E} && gc != {O}")
    t.rep("idx != 250", f"idx != {O}")
    t.rep(".lo3 gi => gi == 249 && idx == 249 && al z == [13, 27]",
          f".lo3 gi => gi == {W['idx']} && idx == {W['idx']} && al z == [{W['q1']}, {W['q2']}]")
    t.rep("al z == [251] && tab.w w == .hi3 249", f"al z == [{W['res']}] && tab.w w == .hi3 {W['idx']}")
    t.rep("g != 3 && g != 250", f"g != {E} && g != {O}")
    t.rep("(res == 251 && idx == 249 && kk % 4 != 2)", f"(res == {W['res']} && idx == {W['idx']} && kk % 4 != 2)")
    t.rep("idx != 249 || ((i, kk) == (13, 0) || (i, kk) == (27, 1)",
          f"idx != {W['idx']} || ((i, kk) == ({W['q1']}, 0) || (i, kk) == ({W['q2']}, 1)")
    t.rep("theorem r154 : rules[154]? = some (.cm 13 251 249 0)",
          f"theorem r154 : rules[{W['l1']}]? = some (.cm {W['q1']} {W['res']} {W['idx']} 0)")
    t.rep("theorem r155 : rules[155]? = some (.cm 27 251 249 1)",
          f"theorem r155 : rules[{W['l2']}]? = some (.cm {W['q2']} {W['res']} {W['idx']} 1)")
    retarget(t, P, "Formal.Net.CapNet.Gcd"); opens_fix(t); fix_opens(t, P); common(t, P)
    out["WalkTab"] = put_banner(t.t, P, "CapstoneWalkTab", WALK_NOTE.format(**W))
    r = Sub(read("WalkRun"), "WalkRun")
    r.rep("lab : ((x.pr 249).filter (fun v => v % 4 != 2)).length = (x.cn 13).length + (x.cn 27).length",
          f"lab : ((x.pr {W['idx']}).filter (fun v => v % 4 != 2)).length = (x.cn {W['q1']}).length + "
          f"(x.cn {W['q2']}).length")
    r.rep("theorem pres_lab : Pres (fun x => ((x.pr 249).filter (fun v => v % 4 != 2)).length =\n"
          "    (x.cn 13).length + (x.cn 27).length) := by",
          f"theorem pres_lab : Pres (fun x => ((x.pr {W['idx']}).filter (fun v => v % 4 != 2)).length =\n"
          f"    (x.cn {W['q1']}).length + (x.cn {W['q2']}).length) := by")
    r.rep("  show ((x'.pr 249).filter _).length = (x'.cn 13).length + (x'.cn 27).length",
          f"  show ((x'.pr {W['idx']}).filter _).length = (x'.cn {W['q1']}).length + (x'.cn {W['q2']}).length")
    r.rep("  by_cases ho : 249 ∈ r.outsL", f"  by_cases ho : {W['idx']} ∈ r.outsL")
    r.rep("    have n13 : 13 ∉ r.insL := by", f"    have n13 : {W['q1']} ∉ r.insL := by")
    r.rep("    have n27 : 27 ∉ r.insL := by", f"    have n27 : {W['q2']} ∉ r.insL := by")
    r.rep("      by_cases hl' : l = 154", f"      by_cases hl' : l = {W['l1']}")
    r.rep("      by_cases hl' : l = 155", f"      by_cases hl' : l = {W['l2']}")
    retarget(r, P, "Formal.Net.CapNet.Gcd"); opens_fix(r); fix_opens(r, P); common(r, P)
    out["WalkRun"] = put_banner(r.t, P, "CapstoneWalkRun", WALK_NOTE.format(**W))
    w = Sub(read("Walk"), "Walk")
    w.rep("g ≠ 3 ∧ g ≠ 250", f"g ≠ {E} ∧ g ≠ {O}")
    w.rep("(h3 : gc ≠ 3) (h250 : gc ≠ 250)", f"(h3 : gc ≠ {E}) (h250 : gc ≠ {O})")
    w.rep("(x.pr 249)[(x.cn 251).length]?", f"(x.pr {W['idx']})[(x.cn {W['res']}).length]?")
    w.rep("(x'.pr 249)[(x'.cn 251).length]?", f"(x'.pr {W['idx']})[(x'.cn {W['res']}).length]?")
    w.rep("(x.cn 251).length", f"(x.cn {W['res']}).length", 3)
    w.rep("(texec_pre ls x y hls 249)", f"(texec_pre ls x y hls {W['idx']})")
    w.rep("(y.pr 249)[", f"(y.pr {W['idx']})[")
    w.rep("(x3.cn 251).length = (x2.pr 249).length", f"(x3.cn {W['res']}).length = (x2.pr {W['idx']}).length")
    w.rep("(x2.pr 249).filter", f"(x2.pr {W['idx']}).filter", 2)
    w.rep("(y.pr 249).filter", f"(y.pr {W['idx']}).filter")
    w.rep("(hsp2 13 (by decide)).2, (hsp2 27 (by decide)).2", f"(hsp2 {W['q1']} (by decide)).2, (hsp2 {W['q2']} (by decide)).2")
    w.rep("(ha : a < 2 ^ 31) (hb : b < 2 ^ 31)", W["hyps"], 5)
    w.rep("gcd_hw_graph_computes_gcd ha hb", W["gthm"])
    w.rep("good_run ha hb", W["grun"])
    w.rep("a b ha hb", W["args"], 3)
    retarget(w, P, "Formal.Net.CapNet.Gcd"); opens_fix(w); fix_opens(w, P); common(w, P)
    out["Walk"] = put_banner(w.t, P, "CapstoneWalk", WALK_NOTE.format(**W))
    return out


WALK_NOTE = ("\n\nH_WALK proof (C-8s). gcd's 3-input cascade (acc251 over control_merge12, rules 154/155) has no\n"
             "counterpart in this kernel: its constants are mapped to the 2-input control_merge of rules\n"
             "{l1}/{l2} (cm {q1}|{q2} -> {res}, index {idx}), for which every cascade fact stated here is true\n"
             "(kernel-checked), and `acc` to channel {acc}, which is not a spine channel, so the walk never\n"
             "takes the cascade branches. The tables (`spN` .. `recs`) are `capnet.py walktab`'s.")


def spine_info(kernel):
    out = subprocess.run([sys.executable, os.path.join(HERE, "capnet.py"), "--kernel", kernel, "spine"],
                         check=True, capture_output=True, text=True).stdout
    d = {}
    for line in out.strip().split("\n"):
        k, v = line.split(" ", 1)
        d[k] = v
    return d


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--kernel", required=True, choices=sorted(PROFILES))
    ap.add_argument("--out-dir", default=NET)
    a = ap.parse_args()
    P = PROFILES[a.kernel]
    sp = spine_info(a.kernel)
    assert int(sp["chOut"]) == P["chOut"] and int(sp["chEnd"]) == P["chEnd"], (sp, P)
    files = {}
    files["SafeHist"] = inst_safehist(P)
    files["NetDef"] = inst_netdef(P)
    files["NetSound"] = inst_generic(P, "NetSound", "Formal.Net.CapNet", [
        ("(GcdHw.Gcd.init_store a b)", f"({P['gq']}.init_store a b)", 2)])
    files["NetChk"] = inst_generic(P, "NetChk", "Formal.Net.CapNet.Gcd", [
        ("theorem out0_desc : tab.d out0.val = .hist 250 0 := by decide",
         f"theorem out0_desc : tab.d out0.val = .hist {P['chOut']} {sp['out0d']} := by decide", 1)])
    files["Safe"] = inst_generic(P, "Safe", "Formal.Net.CapNet.Gcd", [
        ("Hh a b y 250", f"Hh a b y {P['chOut']}", 1),
        ("hy.fifo 250", f"hy.fifo {P['chOut']}", 1),
        ("hy.nc 250", f"hy.nc {P['chOut']}", 1),
        ("GcdHw.Gcd.init a b 250 = [] := init_empty a b 250", f"{P['gq']}.init a b {P['chOut']} = [] := "
         f"init_empty a b {P['chOut']}", 1),
        ("theorem cm_oracle_exists {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) : ∃ y, Good a b y :=\n"
         "  good_exists ha hb",
         f"theorem cm_oracle_exists {P['good_hyps']} : ∃ y, Good a b y :=\n  good_exists {P['good_args']}", 1)])
    files["O1"] = inst_generic(P, "O1", "Formal.Net.CapNet.Gcd")
    cs = Sub(read("CutSpine"), "CutSpine")
    cs.rex(r"^def spL : List Bool := .*$", f"def spL : List Bool := {sp['spL']}")
    cs.rep("def start : Fin NC := 2\n", f"def start : Fin NC := {sp['start']}\n")
    retarget(cs, P, "Formal.Net.CapNet.Gcd")
    fix_opens(cs, P)
    common(cs, P)
    files["CutSpine"] = put_banner(cs.t, P, "CapstoneCutSpine",
                                   "\n\n`spL` and `start` are generated by `capnet.py --kernel K spine`.")
    files["Cut"] = inst_generic(P, "Cut", "Formal.Net.CapNet.Gcd")
    if "walk" in P:
        files.update(inst_walk(P, a.kernel))
    for k, t in files.items():
        dst = os.path.join(a.out_dir, f"{P['prefix']}{k}.lean")
        open(dst, "w").write(t)
        print(f"[instantiate] wrote {dst} ({t.count(chr(10))} lines)", file=sys.stderr)


if __name__ == "__main__":
    main()
