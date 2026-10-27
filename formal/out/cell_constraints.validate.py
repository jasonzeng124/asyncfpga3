#!/usr/bin/env python3
"""Validate cell_constraints.json: schema fields, arc kinds, and that every cited
Lean name is declared in the cited file (tracked in git), or on the named branch."""
import json, re, subprocess, sys
from collections import Counter

import os
REPO = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
doc = json.load(open(sys.argv[1]))
KINDS = {"lut_arc", "site_pin", "wire", "feedback_wire", "line", "env", "cell_param"}
REQ = ["id", "cell", "obligation", "inequality", "forms", "lean", "exactness", "site_pins", "rule", "corner", "status", "check_scope", "combine"]
tracked = set(subprocess.run(["git", "-C", REPO, "ls-files", "formal/lean"], capture_output=True, text=True).stdout.split())
cache = {}

def text(ref):
    key = (ref.get("branch"), ref["file"])
    if key not in cache:
        if ref.get("branch"):
            r = subprocess.run(["git", "-C", REPO, "show", f"{ref['branch']}:{ref['file']}"], capture_output=True, text=True)
            cache[key] = r.stdout if r.returncode == 0 else None
        else:
            try:
                cache[key] = open(f"{REPO}/{ref['file']}").read()
            except OSError:
                cache[key] = None
    return cache[key]

errs, ids, nref = [], Counter(), 0
def chk_lean(where, refs):
    global nref
    for r in refs:
        nref += 1
        t = text(r)
        if t is None:
            errs.append(f"{where}: file missing {r['file']}"); continue
        if not re.search(rf"^\s*(private |protected )?(theorem|lemma|def|structure|abbrev|inductive) {re.escape(r['name'])}\b", t, re.M):
            errs.append(f"{where}: {r['name']} not declared in {r['file']}")
        if not r.get("branch") and r["file"] not in tracked:
            errs.append(f"{where}: {r['file']} is untracked")

for e in doc["constraints"]:
    ids[e["id"]] += 1
    for k in REQ:
        if k not in e:
            errs.append(f"{e.get('id')}: missing field {k}")
    if e["status"] not in ("proved", "unproved"):
        errs.append(f"{e['id']}: bad status")
    if e["status"] == "proved" and e["exactness"] not in ("hypothesis", "see_refers_to") and not any(r["role"] in ("sufficient", "exact") for r in e["lean"]):
        errs.append(f"{e['id']}: proved but no sufficient/exact theorem")
    for f in e["forms"]:
        if not f["data_paths"] or not f["request_paths"]:
            errs.append(f"{e['id']}: empty side")
        for p in f["data_paths"] + f["request_paths"]:
            for a in p:
                if a["kind"] not in KINDS:
                    errs.append(f"{e['id']}: bad arc kind {a['kind']}")
    chk_lean(e["id"], e["lean"])
for h in doc["hypotheses_not_inequalities"]:
    chk_lean(h["id"], h["lean"])
for i, n in ids.items():
    if n > 1:
        errs.append(f"duplicate id {i}")
# strictness (Bs) and cross references
for e in doc["constraints"]:
    st = e.get("strict")
    if st:
        for k in st.get("forms", []):
            if k >= len(e["forms"]) or e["forms"][k]["margin_ps"] < st["margin_added_ps"]:
                errs.append(f"{e['id']}: strict form {k} margin below {st['margin_added_ps']}")
        if st.get("margin_added_ps") and not any(r["file"].endswith("CElemStrict.lean") for r in e["lean"]):
            errs.append(f"{e['id']}: strict without a CElemStrict citation")
        if "strict_pending" in e:
            errs.append(f"{e['id']}: both strict and strict_pending")
    for r in e.get("refers_to", []):
        if r not in ids:
            errs.append(f"{e['id']}: refers_to unknown id {r}")
C = doc["constraints"]
print(f"constraints={len(C)} hypotheses={len(doc['hypotheses_not_inequalities'])} lean_refs={nref} files={len(cache)}")
print("status", Counter(e["status"] for e in C))
print("exactness", Counter(e["exactness"] for e in C))
print("rule verdicts", Counter(e["rule"]["verdict"] for e in C))
print("site pins needed", sum(e["site_pins"]["needed"] for e in C))
print("cells", Counter(e["cell"] for e in C))
print("strict", sum(bool(e.get("strict", {}).get("margin_added_ps")) for e in C), "strict_pending", sum("strict_pending" in e for e in C))
print("errors:", len(errs))
for x in errs:
    print("  ", x)
sys.exit(1 if errs else 0)
