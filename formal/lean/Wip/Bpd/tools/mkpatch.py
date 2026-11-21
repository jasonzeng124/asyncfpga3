#!/usr/bin/env python3
"""Probe Bpd: generate the Prelim -> Core.LutList port.
usage: mkpatch.py OUTDIR   (reads the live tree at formal/lean, writes nothing there except
                           with --shadow, which writes formal/lean/Wip/Bpd/<path> copies)
OUTDIR/tree/<path>  patched files (real import names)
OUTDIR/B.patch      unified diff, shard B files (Formal/Cells/*), incl. deletion of Prelim.lean
OUTDIR/AC.patch     unified diff, shard A/C files
Rules
 R1 direct importers: `import Formal.Cells.Prelim` -> `import Formal.Core.LutList` (dropped if already imported)
 R2 Cells files in Prelim's closure that mention a Prelim short name: `open Formal.Core.LutList`
    after the last import line
 R2c non-Cells closure files that `open Formal.Cells` (bare) and mention a Prelim short name: same line
 R5 explicit-name open `open Formal.Cells (n1 n2)` with all ni Prelim names
    -> `open Formal.Core.LutList (n1 n2)` (Core/XAudit/Events8Arb)
 R3/R4 qualified `Formal.Cells.<PrelimName>` -> `Formal.Core.LutList.<PrelimName>` (code and comments)
"""
import os, re, sys, json, difflib, shutil
ROOT = "/home/user/asyncfpga3/formal/lean"
OUT = sys.argv[1]
SHADOW = "--shadow" in sys.argv
BONLY = "--bonly" in sys.argv
PFX = "Wip/Bpd/S2/" if BONLY else "Wip/Bpd/"
d = json.load(open("/tmp/claude-0/probes/Bpd/closure.json"))
CL = d["closure"]; CLS = set(CL)
NAMES = ["K3", "lutIdx", "lutB", "completions", "muxTree", "lutK", "o6B", "o5B", "o6K", "o5K",
         "mux_eq", "lutIdx_ofFn", "entry_eq_testBit", "lutB_ofFn", "muxTree_ofFn", "muxTree_congr",
         "lutK_ofFn", "lutK_ofFn_spec"]
NAMERE = r"(?:%s)" % "|".join(sorted(NAMES, key=len, reverse=True))
USE = re.compile(r"(?<![\w.'])" + NAMERE + r"(?![\w'])")
QUAL = re.compile(r"\bFormal\.Cells\.(" + NAMERE + r")(?![\w'])")
BAREOPEN = re.compile(r"^\s*open\s+(?:[^\n]*\s)?Formal\.Cells(?=[\s]|$)", re.M)
OPENLINE = "open Formal.Core.LutList\n"

def path(m): return m.replace(".", "/") + ".lean"

def strip_comments(s):
    s = re.sub(r"/-.*?-/", "", s, flags=re.S)
    return re.sub(r"--[^\n]*", "", s)

def patch(m, s):
    rules = []
    lines = s.splitlines(keepends=True)
    if any(re.match(r"\s*import\s+Formal\.Cells\.Prelim\s*$", l) for l in lines):
        has = any(re.match(r"\s*import\s+Formal\.Core\.LutList\s*$", l) for l in lines)
        nl = []
        for l in lines:
            if re.match(r"\s*import\s+Formal\.Cells\.Prelim\s*$", l):
                if not has:
                    nl.append("import Formal.Core.LutList\n")
                    has = True
            else:
                nl.append(l)
        lines = nl; rules.append("R1")
    s = "".join(lines)
    def r5(mo):
        ns = mo.group(1).split()
        if all(n in NAMES for n in ns): return "open Formal.Core.LutList (" + mo.group(1) + ")"
        raise SystemExit("mixed explicit open in " + m)
    s2 = re.sub(r"open Formal\.Cells \(([^)]*)\)", r5, s)
    if s2 != s: rules.append("R5"); s = s2
    s2 = QUAL.sub(r"Formal.Core.LutList.\1", s)
    if s2 != s: rules.append("R4"); s = s2
    code = strip_comments(s)
    need_open = False
    if m.startswith("Formal.Cells."):
        need_open = bool(USE.search(code))
        tag = "R2"
    else:
        need_open = bool(BAREOPEN.search(code)) and bool(USE.search(code))
        tag = "R2c"
    if need_open:
        lines = s.splitlines(keepends=True)
        last = max(i for i, l in enumerate(lines) if re.match(r"\s*import\s", l))
        lines.insert(last + 1, OPENLINE)
        s = "".join(lines); rules.append(tag)
    return s, rules

def shadow(s):
    def rep(mo):
        mods = mo.group(2).split()
        mods = [PFX.replace("/", ".") + x if x in CLS else x for x in mods]
        return mo.group(1) + " ".join(mods)
    return re.sub(r"^(\s*import\s+)([^\n]*)", rep, s, flags=re.M)

os.makedirs(OUT, exist_ok=True)
diffs = {"B": [], "AC": []}
report = []
for m in CL:
    p = path(m)
    old = open(os.path.join(ROOT, p)).read()
    new, rules = patch(m, old)
    if BONLY and not m.startswith("Formal.Cells."): new, rules = old, []
    side = "B" if m.startswith("Formal.Cells.") else "AC"
    report.append((side, m, rules))
    t = os.path.join(OUT, "tree", p); os.makedirs(os.path.dirname(t), exist_ok=True)
    open(t, "w").write(new)
    if new != old:
        diffs[side].append("".join(difflib.unified_diff(old.splitlines(keepends=True), new.splitlines(keepends=True),
                                                        "a/formal/lean/" + p, "b/formal/lean/" + p)))
    if SHADOW:
        sp = os.path.join(ROOT, PFX, p); os.makedirs(os.path.dirname(sp), exist_ok=True)
        open(sp, "w").write(shadow(new))
pre = open(os.path.join(ROOT, "Formal/Cells/Prelim.lean")).read().splitlines(keepends=True)
diffs["B"].append("".join(difflib.unified_diff(pre, [], "a/formal/lean/Formal/Cells/Prelim.lean", "/dev/null")))
for k in diffs:
    open(os.path.join(OUT, k + ".patch"), "w").write("".join(diffs[k]))
json.dump(report, open(os.path.join(OUT, "rules.json"), "w"), indent=0)
for side, m, r in report:
    if r: print(side, m, ",".join(r))
print("unchanged:", sum(1 for _, _, r in report if not r))
