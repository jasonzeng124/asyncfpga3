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
# Bj9: end of a declared name. Lean identifiers may end in a prime (KleeneWinBound.steer_win_bound'), after which '\b' cannot match
# before a space; so: no further identifier character (word character, prime, dot) follows.
NAME_END = r"(?![\w'.])"

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
        if not re.search(rf"^\s*(private |protected )?(theorem|lemma|def|structure|abbrev|inductive) {re.escape(r['name'])}{NAME_END}", t, re.M):
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
        # Bj5: KleeneBox (Bkx) is the strict backing of the select setup/hold rows (bd_steer, bd_mux, bdc_muxn)
        if st.get("margin_added_ps") and not any(r["file"].endswith(("CElemStrict.lean", "CElemStrict2.lean", "KleeneBox.lean")) for r in e["lean"]):
            errs.append(f"{e['id']}: strict without a CElemStrict / KleeneBox citation")
        if "KleeneBox" in st.get("source", "") and not {"H_KLEENE_LUT", "H_X_UNIFORM"} <= set(e.get("hypotheses", [])):
            errs.append(f"{e['id']}: KleeneBox strict row without H_KLEENE_LUT and H_X_UNIFORM in hypotheses")
        if "strict_pending" in e:
            errs.append(f"{e['id']}: both strict and strict_pending")
    for r in e.get("refers_to", []):
        if r not in ids:
            errs.append(f"{e['id']}: refers_to unknown id {r}")
# scope fields (Bj2)
hyp_ids = {h["id"] for h in doc["hypotheses_not_inequalities"]}
BYID = {e["id"]: e for e in doc["constraints"]}
for e in doc["constraints"]:
    if "exact_scope" in e and e["exactness"] != "exact":
        errs.append(f"{e['id']}: exact_scope on a non-exact entry")
    if e["exactness"] == "not_necessary" and e.get("replacement") not in hyp_ids | set(ids):
        errs.append(f"{e['id']}: not_necessary without a replacement (hypothesis or constraint id)")
    if e["exactness"] == "not_necessary" and e.get("replacement") in ids and BYID[e["replacement"]]["exactness"] == "not_necessary":
        errs.append(f"{e['id']}: replacement {e['replacement']} is itself not_necessary")
    if e.get("informational") and not e.get("refers_to"):
        errs.append(f"{e['id']}: informational without refers_to")
    if e["exactness"] == "not_necessary" and not any(r["role"].startswith("not_necessary") for r in e["lean"]):
        errs.append(f"{e['id']}: not_necessary without a not_necessary citation")
# citation roles (Bj3): known vocabulary; role 'exact' only for a statement with an iff
ROLES = {"sufficient", "exact", "exact_inner", "exact_formula", "necessary", "counter_trace", "non_vacuity", "instance", "lemma", "definition", "context",
         "corner", "function_equality", "exact_fixed_transport", "reduction", "relation", "not_necessary", "not_necessary_at_instance", "rule_as_coded",
         "uses", "bound", "twin", "checker_exactness", "redundancy", "necessary_loop_terms", "necessary_loop_term", "kleene", "partial", "exact_first_edge",
         "mirror", "exact_replacement_counter_trace", "counter_run", "numbers"}
# explicit exceptions: (file, name) cited as 'exact' although the statement has no '↔' (none at present)
EXACT_NOT_IFF = {}
def statement(r):
    t = text(r)
    if t is None:
        return None
    m = re.search(rf"^\s*(private |protected )?(theorem|lemma|def|structure|abbrev|inductive) {re.escape(r['name'])}{NAME_END}", t, re.M)
    if not m:
        return None
    s = t[m.start():]
    k = s.find(":=")
    return s[:k] if k >= 0 else s[:4000]
role_count = Counter()
for e in doc["constraints"] + doc["hypotheses_not_inequalities"]:
    for r in e["lean"]:
        role_count[r["role"]] += 1
        if r["role"] not in ROLES:
            errs.append(f"{e['id']}: unknown citation role {r['role']} ({r['name']})")
        if r["role"] == "exact" and (r["file"], r["name"]) not in EXACT_NOT_IFF:
            st = statement(r)
            if st is not None and "↔" not in st:
                errs.append(f"{e['id']}: {r['name']} cited as exact but its statement has no '↔'")
# Bj10 (audit P9): every 'exact' ROW must cite, with role 'exact', at least one theorem whose statement (the Lean text up to ':=')
# is an iff ('↔' or 'Iff'). Closed-form equalities (exact_formula) or a sufficient theorem plus a necessity theorem conditional on a
# supplied run do not make a row exact; such rows are labelled sufficient / sufficient+necessary_* with a necessity_scope.
nexiff = 0
for e in doc["constraints"]:
    if e["exactness"] != "exact":
        continue
    sts = [statement(r) for r in e["lean"] if r["role"] == "exact"]
    if any(st is not None and ("↔" in st or re.search(r"\bIff\b", st)) for st in sts):
        nexiff += 1
    else:
        errs.append(f"{e['id']}: exactness 'exact' but no citation with role exact whose Lean statement is an iff (audit P9)")
# binds_at (Bj4): counts ordered, cited names present in the entry's lean list, design-level by_row sums match the rows
nbind = 0
for e in doc["constraints"]:
    b = e.get("binds_at")
    if not b:
        continue
    nbind += 1
    try:
        rv, pc, nw = (b[k]["cells"] for k in ("reset_vector", "per_cell_model", "network"))
    except (KeyError, TypeError):
        errs.append(f"{e['id']}: binds_at needs reset_vector / per_cell_model / network with an integer 'cells'"); continue
    if not (isinstance(rv, int) and isinstance(pc, int) and isinstance(nw, int) and nw <= rv <= pc):
        errs.append(f"{e['id']}: binds_at counts not ordered network <= reset_vector <= per_cell_model ({nw}, {rv}, {pc})")
    if "of" in b["reset_vector"] and rv > b["reset_vector"]["of"]:
        errs.append(f"{e['id']}: binds_at reset_vector cells exceed 'of'")
    names = {f"{r['file'].split('/')[-1][:-5]}.{r['name']}" for r in e["lean"]}
    if not b.get("lean"):
        errs.append(f"{e['id']}: binds_at without lean names")
    for n in b.get("lean", []):
        if n not in names:
            errs.append(f"{e['id']}: binds_at cites {n}, not in the entry's lean list")
    for k in ("reset_vector", "per_cell_model"):
        br = b[k].get("by_row")
        if br is None:
            continue
        if sum(br.values()) != b[k]["cells"]:
            errs.append(f"{e['id']}: binds_at {k} by_row sums to {sum(br.values())}, not {b[k]['cells']}")
        for rid, n in br.items():
            if rid in BYID and BYID[rid].get("binds_at", {}).get(k, {}).get("cells") != n:
                errs.append(f"{e['id']}: binds_at {k} by_row {rid} = {n} disagrees with that row")
# Bj5 (audit P8): an 'exact' entry whose inequality carries the strict +1 must cite as 'exact' an iff that
# states the +1 form (a Kleene X-window iff), not only a binary '<=' iff.  Explicit list of such iffs:
STRICT_IFFS = {("CElemStrict.lean", n) for n in ("env_latency_iff", "env_latency_strict", "box_iff", "clean_iff")} | \
    {("CElemStrict2.lean", n) for n in ("c4_clean_iff", "reset_width_iff", "reset_width_strict")} | \
    {("LibGapLatch.lean", n) for n in ("box_exact_edges", "strict_edges")} | \
    {("KleeneBox.lean", n) for n in ("steer_edges_K", "steer_strict_K", "join_edges_K", "join_strict_K", "muxn_edges_K",
                                    "latch_edges_uniform", "latch_strict_uniform")} | \
    {("LinkExact.lean", "strict_edges")}
nkap = nhyp = nkx = 0
KAPPA_EXACT_ROWS = {"bd_arbiter.a0_fork_client1": 1, "bd_arbiter.a0_fork_client2": 2}
for e in doc["constraints"]:
    st = e.get("strict")
    if e["exactness"] == "exact" and st and st.get("margin_added_ps") and \
            not any(r["role"] == "exact" and (r["file"].split("/")[-1], r["name"]) in STRICT_IFFS for r in e["lean"]):
        errs.append(f"{e['id']}: exact with a strict +1 but no 'exact' citation of a strict-form iff (STRICT_IFFS)")
    if "hypotheses" in e:
        nhyp += 1
        if not (isinstance(e["hypotheses"], list) and all(isinstance(h, str) for h in e["hypotheses"])):
            errs.append(f"{e['id']}: hypotheses must be a list of strings")
    k = e["corner"].get("kappa")
    if k is not None:
        nkap += 1
        if k.get("see") not in hyp_ids:
            errs.append(f"{e['id']}: corner.kappa.see is not a hypotheses_not_inequalities id")
        # Bj7: audit row 18 is answered for the 16 link_arb A0-fork cases only (OnNetlistArbKappaExact); on those two rows a
        # results string may say 'exact' iff it cites OnNetlistArbKappaExact and the row cites all 8 of its client's exact_* iffs
        # with role 'exact'.  Every other results string, on every row, still may not call a kappa threshold exact.
        cl = KAPPA_EXACT_ROWS.get(e["id"])
        for s in k.get("results", []):
            # the word 'exact' only: identifiers such as LinkExact / exact_s1c1_lit and 'exactly' do not count
            if not re.search(r"(?<![a-z_])exact(?![a-z_])", s.lower().replace("not an exact", "").replace("not exact", "")):
                continue
            if cl is None or "OnNetlistArbKappaExact" not in s:
                errs.append(f"{e['id']}: corner.kappa.results calls a kappa threshold exact (audit row 18)")
        if cl is not None:
            nkx += 1
            have = {r["name"] for r in e["lean"] if r["role"] == "exact" and r["file"].endswith("/OnNetlistArbKappaExact.lean")}
            need = {f"exact_s{s}c{cl}_{rd}" for s in (1, 2, 3, 4) for rd in ("cons", "lit")}
            if not need <= have:
                errs.append(f"{e['id']}: kappa-exact row without 'exact' citations {sorted(need - have)} (OnNetlistArbKappaExact)")
            if "OnNetlistArbKappaExact" not in k.get("exact_source", ""):
                errs.append(f"{e['id']}: kappa-exact row without corner.kappa.exact_source")
        elif "exact_source" in k:
            errs.append(f"{e['id']}: corner.kappa.exact_source on a row outside KAPPA_EXACT_ROWS")
    elif e["corner"]["mode"] in ("1C", "1C_both_corners_required"):
        errs.append(f"{e['id']}: 1C row without corner.kappa")
# Bj6: KleeneWin (every strict +1 is H_X_UNIFORM at w = 1: the row must say so), KleenePess (kleene_dependence
# vocabulary; every K3-model row carries it), replacement_rows / replacement_scope (several rows replace one).
KDEP = {"pass0", "pass1", "both", "pass(reset value)", "none"}
nxw = nkd = 0
for e in doc["constraints"]:
    st = e.get("strict")
    k3 = any(h.startswith(("H_KLEENE_LUT", "H_MUX_KLEENE")) for h in e.get("hypotheses", []))
    if st and st.get("margin_added_ps"):
        k3 = True
        nxw += 1
        if not st.get("x_window"):
            errs.append(f"{e['id']}: strict +1 without strict.x_window (KleeneWin: the +1 is H_X_UNIFORM)")
        if not any(h.startswith("H_X_UNIFORM") for h in e.get("hypotheses", [])):
            errs.append(f"{e['id']}: strict +1 without H_X_UNIFORM in hypotheses")
    kd = e.get("kleene_dependence")
    if kd is not None:
        nkd += 1
        if kd.get("needs") not in KDEP or not kd.get("basis"):
            errs.append(f"{e['id']}: kleene_dependence needs one of {sorted(KDEP)} and a basis")
    elif k3:
        errs.append(f"{e['id']}: K3-model row (H_KLEENE_LUT / H_MUX_KLEENE / strict +1) without kleene_dependence")
    rr = e.get("replacement_rows")
    if rr is not None:
        if e["exactness"] != "not_necessary" or e.get("replacement") not in rr:
            errs.append(f"{e['id']}: replacement_rows on a non-not_necessary entry, or without its replacement")
        for r in rr:
            if r not in ids or BYID[r]["exactness"] == "not_necessary":
                errs.append(f"{e['id']}: replacement_rows entry {r} unknown or itself not_necessary")
    cg = e.get("combine_groups")
    if cg is not None:
        # Bj9: a disjunction of conjunctions of forms; only with combine 'any', groups disjoint and covering every form
        flat = [i for grp in cg for i in grp]
        if e["combine"] != "any" or sorted(flat) != list(range(len(e["forms"]))) or not all(cg):
            errs.append(f"{e['id']}: combine_groups needs combine 'any' and non-empty groups partitioning the form indices")
    if "replacement_scope" in e and e["exactness"] != "not_necessary":
        errs.append(f"{e['id']}: replacement_scope on a non-not_necessary entry")
# Bj7: '+W under H_W_BOUND' is proved for bd_steer only (SelfAuditB7.steer_win_bound): every other x_window must say UNPROVED;
# c_contract (status vocabulary, cited names in the row's lean list); boundary_point only on strict +1 boundary rows.
# Bj9 (Bwb, KleeneWinBound): the bound is now proved per row family. A row whose x_window speaks of a bound under H_W_BOUND and does not
# say UNPROVED must cite, from KleeneWinBound (or SelfAuditB7.steer_win_bound for steer), a bound theorem (role sufficient / bound) AND one of
# its necessity theorems (role necessary); a row citing the C-element bound must state '+W + Wq' and that '+W' holds only at 'wq = 0'.
nwb = nwb_unproved = ncc = nbp = 0
CC_STATUS = {"derived", "not_derivable", "needs_extra_hypothesis"}
WB_NEED = {"steer_win_bound'": {"steer_win_need_setup", "steer_win_need_hold"}, "join_win_bound": {"join_win_need_setup", "join_win_need_hold"},
           "muxn_win_bound": {"muxn_win_need"}, "latch_win_bound": {"latch_win_need_pulse", "latch_win_need_data", "latch_win_need_hold"},
           "cel_env_win_bound": {"cel_env_win_need"}}
for e in doc["constraints"]:
    xw = (e.get("strict") or {}).get("x_window", "")
    if "H_W_BOUND" in xw:
        nwb += 1
        if "UNPROVED" in xw:
            nwb_unproved += 1
        else:
            wbr = [r for r in e["lean"] if r["file"].endswith("/KleeneWinBound.lean")]
            bounds = {r["name"] for r in wbr if r["name"] in WB_NEED and r["role"] in ("sufficient", "bound")}
            if e["cell"] == "bd_steer" and any(r["name"] == "steer_win_bound" and r["file"].endswith("/SelfAuditB7.lean") and r["role"] == "sufficient"
                                               for r in e["lean"]):
                bounds.add("steer_win_bound'")
            needs = {r["name"] for r in wbr if r["role"] == "necessary"}
            if not bounds:
                errs.append(f"{e['id']}: bound 'under H_W_BOUND' claimed without a KleeneWinBound / SelfAuditB7 bound theorem and not labelled UNPROVED")
            for b in bounds:
                if not WB_NEED[b] & needs:
                    errs.append(f"{e['id']}: bound {b} cited without one of its necessity theorems {sorted(WB_NEED[b])} (role necessary)")
            if "cel_env_win_bound" in bounds and not ("+W + Wq" in xw and "wq = 0" in xw):
                errs.append(f"{e['id']}: C-element bound cited but x_window does not state '+W + Wq' and that '+W' holds only at 'wq = 0'")
    cc = e.get("c_contract")
    if cc is not None:
        ncc += 1
        names = {f"{r['file'].split('/')[-1][:-5]}.{r['name']}" for r in e["lean"]}
        if cc.get("status") not in CC_STATUS or not cc.get("basis") or not cc.get("field"):
            errs.append(f"{e['id']}: c_contract needs field, basis and status in {sorted(CC_STATUS)}")
        if cc.get("status") == "needs_extra_hypothesis" and not cc.get("extra"):
            errs.append(f"{e['id']}: c_contract needs_extra_hypothesis without 'extra'")
        for n in cc.get("lean", []):
            if n not in names:
                errs.append(f"{e['id']}: c_contract cites {n}, not in the entry's lean list")
    bp = e.get("boundary_point")
    if bp is not None:
        nbp += 1
        if e["exactness"] != "sufficient+necessary_at_boundary" or not (e.get("strict") or {}).get("margin_added_ps"):
            errs.append(f"{e['id']}: boundary_point on a row that is not a strict +1 necessary_at_boundary row")
        if bp.get("ticks_from_row_form") != bp.get("slack", -1) + 1 or "<=" not in e.get("necessity_scope", ""):
            errs.append(f"{e['id']}: boundary_point ticks_from_row_form != slack + 1, or necessity_scope does not name the '<=' form")
print(f"rows with a bound under H_W_BOUND: {nwb} (UNPROVED: {nwb_unproved}); rows with c_contract: {ncc}; rows with boundary_point: {nbp}; kappa-exact rows: {nkx}")
print(f"rows with strict.x_window checked: {nxw}; rows with kleene_dependence: {nkd}")
print(f"exact rows citing an iff with role exact: {nexiff}")
print(f"rows with hypotheses: {nhyp}; rows with corner.kappa: {nkap}")
C = doc["constraints"]
print(f"binds_at entries: {nbind}")
print(f"constraints={len(C)} hypotheses={len(doc['hypotheses_not_inequalities'])} lean_refs={nref} files={len(cache)}")
print("status", Counter(e["status"] for e in C))
print("exactness", Counter(e["exactness"] for e in C))
print("rule verdicts", Counter(e["rule"]["verdict"] for e in C))
print("site pins needed", sum(e["site_pins"]["needed"] for e in C))
print("cells", Counter(e["cell"] for e in C))
print("strict", sum(bool(e.get("strict", {}).get("margin_added_ps")) for e in C), "strict_pending", sum("strict_pending" in e for e in C))
print("citation roles: exact", role_count["exact"], "exact_inner", role_count["exact_inner"], "exact_formula", role_count["exact_formula"])
noex = [e["id"] for e in C if e["exactness"] == "exact" and not any(r["role"] == "exact" for r in e["lean"])]
print("exact entries without an 'exact' citation (exact_scope says why):", len(noex), noex)
for i in noex:
    if "exact_scope" not in BYID[i] and "exact_under" not in BYID[i]:
        errs.append(f"{i}: exact entry with no 'exact' citation and no exact_scope")
print("errors:", len(errs))
for x in errs:
    print("  ", x)
sys.exit(1 if errs else 0)
