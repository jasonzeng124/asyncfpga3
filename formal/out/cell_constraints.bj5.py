#!/usr/bin/env python3
"""Probe Bj5 (shard B, 2026-10-29): bring formal/out/cell_constraints.json up to date with
KleeneBox, Necessity3*, the kappa files and LinkExact, and fix the 'exact' labels the audit
(P8, P7-kappa row 18) flagged.  Written as one self-contained pass over the JSON so that it
can be ported into cell_constraints.gen.py as a "probe Bj5" section (the generator was not
in this probe's write set).

usage: python3 -I cell_constraints.bj5.py IN.json OUT.json  (run by cell_constraints.gen.py)
"""
import copy, json, sys

IN, OUT = sys.argv[1], sys.argv[2]
doc = json.load(open(IN))
C = doc["constraints"]
BY = {e["id"]: e for e in C}
LOG = []

F = "formal/lean/Formal/Cells/"
def L(file, name, role, note=None):
    r = {"file": F + file + ".lean", "name": name, "role": role}
    if note:
        r["note"] = note
    return r

def add_lean(e, refs):
    have = {(r["file"], r["name"], r["role"]) for r in e["lean"]}
    for r in refs:
        if (r["file"], r["name"], r["role"]) not in have:
            e["lean"].append(r)

def add_hyp(e, hs):
    cur = e.setdefault("hypotheses", [])
    for h in hs:
        if h not in cur:
            cur.append(h)

def note_append(e, txt):
    e["exactness_note"] = (e.get("exactness_note") or "").rstrip() + (" " if e.get("exactness_note") else "") + txt

def sub(e, field, old, new):
    s = e[field]
    assert s.count(old) == 1, (e["id"], field, old)
    e[field] = s.replace(old, new)

# ------------------------------------------------------------------ (1) KleeneBox
KB_HYP = ["H_KLEENE_LUT", "H_X_UNIFORM", "H_PIN_READ"]
KB_SRC = "Bkx (formal/notes/B-kleene-box.md, Formal/Cells/KleeneBox.lean)"
KB_COMMON = ("STRICT (Bkx, KleeneBox): with K3 traces on EVERY pin (request, ctl_req, select / index bits, "
             "feedback) and the real INITs through lutK (H_KLEENE_LUT: the exact, hazard-free ternary extension of "
             "the INIT, i.e. the OPTIMISTIC LUT model; its silicon fidelity is unverified, audit P8), two coordinate "
             "systems: (a) DEFINITE-WINDOW times (the windows on which each pin is definite): the condition is the "
             "binary one, '<=', and exact (K3 safety <-> binary safety); (b) BINARY-EDGE times under H_X_UNIFORM "
             "(every edge X on [T - a, T + c), the SAME split on every edge, w = a + c): every setup and hold gains "
             "+w, exact; at w = 1 tick (the grid minimum, NOT a measured slew) strict. The row's forms are in (b) "
             "with w = 1 (margin_ps + 1). With unequal splits per edge only (a) applies. Not covered: the X width, "
             "mid-rail selects beyond H_KLEENE_LUT, correlated corners.")

def kleene_row(rid, ineq_old, ineq_new, exact_refs, other_refs, backing, scope):
    e = BY[rid]
    sub(e, "inequality", ineq_old, ineq_new)
    assert len(e["forms"]) >= 1 and e["forms"][0]["margin_ps"] == 0, rid
    e["forms"][0]["margin_ps"] = 1
    e["strict"] = {"source": KB_SRC, "backing": backing, "forms": [0],
                   "terms": "setup and hold in binary-edge times (H_X_UNIFORM, w = 1)", "margin_added_ps": 1}
    e.pop("strict_pending", None)
    add_lean(e, exact_refs + other_refs)
    add_hyp(e, KB_HYP)
    note_append(e, KB_COMMON)
    assert "exact_scope" not in e or rid.startswith("bdc_muxn"), rid
    e["exact_scope"] = (e.get("exact_scope", "") + ("; " if e.get("exact_scope") else "") + scope)
    LOG.append(f"{rid}: strict (+1, binary-edge times, KleeneBox); hypotheses H_KLEENE_LUT, H_X_UNIFORM")

st_refs = [L("KleeneBox", "steer_box_exact_K", "exact", "K3 on every pin, definite-window times: same right side as steer_box_exact"),
           L("KleeneBox", "steer_edges_K", "exact", "binary-edge times under H_X_UNIFORM: setup and hold each + (a + c)"),
           L("KleeneBox", "steer_strict_K", "exact", "a + c = 1: both strict")]
st_oth = [L("KleeneBox", "steer_K_iff_binary", "kleene", "K3 box safety <-> binary box safety"),
          L("KleeneBox", "steer_atomic_K", "context", "zero-width windows: the binary '<=' back"),
          L("KleeneBox", "outK_sel", "function_equality", "real INIT: a definite-0 request masks an X select (3^n, decide)"),
          L("KleeneBox", "steer_witness_K", "non_vacuity", "X windows on every edge, strict margins, outputs definite and correct")]
kleene_row("bd_steer.bundled_s_setup",
           "S0 + ps_b.hi <= R + pr_b.lo;",
           "S0 + ps_b.hi + 1 <= R + pr_b.lo in binary-edge times (H_X_UNIFORM, 1-tick X: steer_strict_K), S0 + ps_b.hi <= R + pr_b.lo in definite-window times (steer_box_exact, steer_box_exact_K);",
           st_refs, st_oth + [L("KleeneBox", "steer_ct_setup_x", "counter_trace", "binary-edge equality, 1-tick X: unselected O5 reads X at 1299")],
           "steer_strict_K",
           "binary-edge form (+1) exact under H_KLEENE_LUT + H_X_UNIFORM at w = 1 (steer_strict_K); definite-window '<=' form exact (steer_box_exact, steer_box_exact_K); box necessity takes the two pins independent")
kleene_row("bd_steer.bundled_s_hold",
           "F + pr_b.hi <= S1 + ps_b.lo",
           "F + pr_b.hi + 1 <= S1 + ps_b.lo in binary-edge times (H_X_UNIFORM, 1-tick X: steer_strict_K), F + pr_b.hi <= S1 + ps_b.lo in definite-window times (steer_box_exact, steer_box_exact_K)",
           st_refs, st_oth + [L("KleeneBox", "steer_ct_hold_x", "counter_trace", "binary-edge equality, 1-tick X: unselected O5 reads X at 3599")],
           "steer_strict_K",
           "binary-edge form (+1) exact under H_KLEENE_LUT + H_X_UNIFORM at w = 1 (steer_strict_K); definite-window '<=' form exact (steer_box_exact, steer_box_exact_K); box necessity takes the two pins independent")

jn_refs = [L("KleeneBox", "join_box_exact_K", "exact", "K3 on every pin, definite-window times: same right side as join_box_exact; request and feedback pins drop out, X included"),
           L("KleeneBox", "join_edges_K", "exact", "binary-edge times under H_X_UNIFORM: setup and hold each + (xa + xc)"),
           L("KleeneBox", "join_strict_K", "exact", "xa + xc = 1: both strict")]
jn_oth = [L("KleeneBox", "join_K_iff_binary", "kleene", "K3 join safety <-> binary join safety"),
          L("KleeneBox", "jK_sel", "function_equality", "real uj0/uj1 INITs: a definite-0 ctl_req masks an X select"),
          L("KleeneBox", "unsel_definite", "lemma", "spec: the unselected join is definite 0 at every instant"),
          L("KleeneBox", "join_witness_K", "non_vacuity", "constructed K3 run, X windows on every edge, strict margins")]
kleene_row("bd_mux.bundled_s_setup",
           "S0 + ps_k.hi <= Cr + pc_k.lo;",
           "S0 + ps_k.hi + 1 <= Cr + pc_k.lo in binary-edge times (H_X_UNIFORM, 1-tick X: join_strict_K), S0 + ps_k.hi <= Cr + pc_k.lo in definite-window times (join_box_exact, join_box_exact_K);",
           jn_refs, jn_oth + [L("KleeneBox", "join_ct_setup_x", "counter_trace", "binary-edge equality, 1-tick X: uj0 = X at 1299 with x_req waiting")],
           "join_strict_K",
           "binary-edge form (+1) exact per join under H_KLEENE_LUT + H_X_UNIFORM at w = 1 (join_strict_K); definite-window '<=' form exact (join_box_exact, join_box_exact_K); box necessity takes pins independent")
kleene_row("bd_mux.bundled_s_hold",
           "Cf + pc_k.hi <= S1 + ps_k.lo",
           "Cf + pc_k.hi + 1 <= S1 + ps_k.lo in binary-edge times (H_X_UNIFORM, 1-tick X: join_strict_K), Cf + pc_k.hi <= S1 + ps_k.lo in definite-window times (join_box_exact, join_box_exact_K)",
           jn_refs, jn_oth + [L("KleeneBox", "join_ct_hold_x", "counter_trace", "binary-edge equality, 1-tick X: uj0 = X at 3299")],
           "join_strict_K",
           "binary-edge form (+1) exact per join under H_KLEENE_LUT + H_X_UNIFORM at w = 1 (join_strict_K); definite-window '<=' form exact (join_box_exact, join_box_exact_K); box necessity takes pins independent")

mx_refs = [L("KleeneBox", "muxn_sel_box_exact_K", "exact", "SELECTED join only, K3 on every pin, definite-window times: same right side (SelCond) as sel_box_exact"),
           L("KleeneBox", "muxn_edges_K", "exact", "SELECTED join, binary-edge times under H_X_UNIFORM: each of the four per-bit inequalities + (a + c); strict at a + c = 1 (no separate *_strict_K theorem: arithmetic from this iff)")]
mx_oth = [L("KleeneBox", "muxn_ok_K", "sufficient", "selected join, K3"),
          L("KleeneBox", "muxn_K_to_B", "lemma", "binary traces embed: LibGapMuxN's binary witnesses meet the K3 hypotheses (no X-specific witness)"),
          L("KleeneBox", "decK_sel", "function_equality", "real decode LUT3 INITs: a definite-0 ctl_req masks X index bits")]
MX_SCOPE = ("K3 / binary-edge (+1) form: exact for the SELECTED join (muxn_sel_box_exact_K, muxn_edges_K at a + c = 1); "
            "the UNSELECTED joins' Cover is binary only (unsel_box_exact), so whole-cell sufficiency of the +1 form in K3 rests on "
            "the binary Cover argument (sel_cond_cover), not on a K3 theorem; the +1 is necessary (selected join)")
kleene_row("bdc_muxn.s_setup",
           "S0_b + ps_b(k).hi <= Cr + pc(k).lo;",
           "S0_b + ps_b(k).hi + 1 <= Cr + pc(k).lo in binary-edge times (H_X_UNIFORM, 1-tick X: muxn_edges_K, selected join), S0_b + ps_b(k).hi <= Cr + pc(k).lo in definite-window times (decode_exact_all_tokens; muxn_sel_box_exact_K);",
           mx_refs, mx_oth, "muxn_edges_K at a + c = 1", MX_SCOPE)
kleene_row("bdc_muxn.s_hold",
           "Cf + pc(k).hi <= S1_b + ps_b(k).lo (",
           "Cf + pc(k).hi + 1 <= S1_b + ps_b(k).lo in binary-edge times (H_X_UNIFORM, 1-tick X: muxn_edges_K, selected join), Cf + pc(k).hi <= S1_b + ps_b(k).lo in definite-window times (decode_exact_all_tokens; muxn_sel_box_exact_K) (",
           mx_refs, mx_oth, "muxn_edges_K at a + c = 1", MX_SCOPE)

# latch rows: the any-split form (KleeneBox generalises box_exact_edges from c = 0)
for e in C:
    if e["id"].startswith("bd_latch[") and e["exactness"] == "exact":
        add_lean(e, [L("KleeneBox", "latch_edges_uniform", "exact", "box_exact_edges for ANY uniform split a + c (H_X_UNIFORM); box_exact_edges is c = 0"),
                     L("KleeneBox", "latch_strict_uniform", "exact", "a + c = 1: all three strict")])
        add_hyp(e, ["H_PIN_READ", "H_KLEENE_LUT", "H_EN_TOKEN", "H_D_STABLE", "H_X_UNIFORM (binary-edge form)"])
        LOG.append(f"{e['id']}: + KleeneBox.latch_edges_uniform / latch_strict_uniform (any uniform split); hypotheses recorded")

# ------------------------------------------------------------------ (2) Necessity3*
N3_PIPE_NOTE = ("Bsx3 (formal/notes/B-necessity3.md, {f}): in {thm}'s own hypothesis set ({setting}) the field {fld} cannot be weakened by 1 tick: "
                "an explicit run (real INITs, every gate relation for ALL t) meets every other hypothesis, violates {fld} by exactly 1 and breaks "
                "the conclusion ({fail}). One parameter point ({point}), binary model: necessary at the boundary, NOT an iff.")
def n3(rid, refs, note, label="sufficient+necessary_at_boundary"):
    e = BY[rid]
    old = e["exactness"]
    assert old == "sufficient", (rid, old)
    e["exactness"] = label
    add_lean(e, refs)
    note_append(e, note)
    LOG.append(f"{rid}: {old} -> {label}")

PIPE_SET = "PipeTimedN.Wit unit-delay control run, N = 2; one-bit latches = real ODD INIT as transport LUTs, point windows (one corner)"
n3("bd_pipe.boundary_I",
   [L("Necessity3Pipe", "tok0", "sufficient", "TokClaim 0 0 0 = PipeTimedN.token"),
    L("Necessity3Pipe", "I_false", "counter_trace", "not TokClaim 1 0 0: H_I weakened by 1"),
    L("Necessity3Pipe", "I_viol", "numbers", "Dl0 + dhi1 + fhi1 = Won + Rq.lo + L1.lo + elo1 + 1"),
    L("Necessity3Pipe", "dataS_I", "counter_run", "every other DataN field holds on run RI")],
   N3_PIPE_NOTE.format(f="Necessity3Pipe", thm="PipeTimedN.token", setting=PIPE_SET, fld="H_I",
                       fail="stage 1 still shows the reset value on [12, 16)", point="N = 2, unit control"))
n3("bd_pipe.boundary_H",
   [L("Necessity3Pipe", "tok0", "sufficient", "TokClaim 0 0 0 = PipeTimedN.token"),
    L("Necessity3Pipe", "H_false", "counter_trace", "not TokClaim 0 1 0: H_H weakened by 1"),
    L("Necessity3Pipe", "H_viol", "numbers", "ehi1 = aslow + L.lo + elo0 + dlo1 + 1"),
    L("Necessity3Pipe", "dataS_H", "counter_run", "every other DataN field holds on run RH")],
   N3_PIPE_NOTE.format(f="Necessity3Pipe", thm="PipeTimedN.token", setting=PIPE_SET, fld="H_H",
                       fail="stage 0's next token reaches stage 1 while its closing enable is in flight: wrong value at 15", point="N = 2, unit control"))
n3("bd_pipe.data_lead",
   [L("Necessity3Pipe", "tok0", "sufficient", "TokClaim 0 0 0 = PipeTimedN.token"),
    L("Necessity3Pipe", "L_false", "counter_trace", "not TokClaim 0 0 1: H_DATA_LEAD weakened by 1"),
    L("Necessity3Pipe", "L_viol", "numbers", "dS k + Sdr = rho(2k) + Lag + 1"),
    L("Necessity3Pipe", "dataS_L", "counter_run", "every other DataN field holds on run RL")],
   N3_PIPE_NOTE.format(f="Necessity3Pipe", thm="PipeTimedN.token", setting=PIPE_SET, fld="H_DATA_LEAD (the row's inequality, the Lean DataN form)",
                       fail="stage 0 holds the stale value at 10", point="N = 2, unit control") +
   " The classic request-after-data form stays sufficient and NOT necessary (Bundling.setup_not_classic); the label is for the Lean form only.")
n3("bd_pipe.output",
   [L("Necessity3Pipe", "out0", "sufficient", "OutClaim 0 = pipe_forward's second half"),
    L("Necessity3Pipe", "out_false", "counter_trace", "not OutClaim 1"),
    L("Necessity3Pipe", "O_viol", "numbers", "Dl 1 = Er + 1"),
    L("Necessity3Pipe", "dataN_O", "counter_run", "the DataN fields hold on run RO")],
   N3_PIPE_NOTE.format(f="Necessity3Pipe", thm="PipeTimedN.pipe_forward", setting=PIPE_SET, fld="Dl (N-1) b <= Er",
                       fail="the last stage shows the stale value at the receiver's ack rise, 10", point="N = 2, unit control"))
n3("bd_pipe.lat_lumped",
   [L("Necessity3PipeCtl", "ctl0", "sufficient", "CtlClaim 0 0 0 = PipeTimedN.nodes_clean"),
    L("Necessity3PipeCtl", "lat_false", "counter_trace", "not CtlClaim 1 0 0: H_LAT weakened by 1"),
    L("Necessity3PipeCtl", "lat_viol", "numbers", "L.hi + wh = L.lo + min Es Er + 1"),
    L("Necessity3PipeCtl", "timing_L", "counter_run", "TimingS (every other TimingN field) holds on run RLat"),
    L("Necessity3PipeCtl", "lat_exc", "numbers", "the node drops for one tick inside its high phase")],
   N3_PIPE_NOTE.format(f="Necessity3PipeCtl", thm="PipeTimedN.nodes_clean", setting="FIFO controllers, real bd_c2n INIT, feedback window [1, 3], open-loop sender/receiver",
                       fld="H_LAT", fail="node drops for one tick at 8 inside [5, 9)", point="N = 1, not a gcd_hw size; needs min(ER, EA) < max(ER, EA)") +
   " The run refutes the Lean '<=' form at slack 1; the JSON form's +1 (Bs) is the Kleene X window, so the JSON's own form is 2 ps from the refuted point (audit P8).")
e = BY["bd_pipe.rst_lines"]
add_lean(e, [L("Necessity3PipeCtl", "ctl0", "sufficient", "CtlClaim 0 0 0 = PipeTimedN.nodes_clean"),
             L("Necessity3PipeCtl", "long_false", "counter_trace", "not CtlClaim 0 1 0: H_RST_LONG (loop term) weakened by 1, N = 1"),
             L("Necessity3PipeCtl", "long_viol", "numbers"),
             L("Necessity3PipeCtl", "timing_R", "counter_run"),
             L("Necessity3PipeCtl", "lines_false", "counter_trace", "not CtlClaim 0 0 1: the request-line term L(b-1).hi + Rq_b.hi <= R weakened by 1, N = 2"),
             L("Necessity3PipeCtl", "lines_viol", "numbers"),
             L("Necessity3PipeCtl", "timing_q", "counter_run")])
e["necessity_scope"] = ("terms only: the loop term L_i.hi + wh_i (+1) <= R (H_RST_LONG; also NecessityReset.c2n_box_exact) and the request-line term "
                        "L(b-1).hi + Rq_b.hi <= R are necessary at the boundary (Necessity3PipeCtl.long_false N = 1, lines_false N = 2); the DACK term "
                        "L_b.hi + ahi_b <= R, the guard term Ag_b <= R and the per-pin (6g) H_RST_SEL terms have no necessity result")
note_append(e, "Bsx3 (B-necessity3.md): two of the terms are necessary at the boundary (necessity_scope); the row stays 'sufficient' because the other terms are not.")
LOG.append("bd_pipe.rst_lines: stays sufficient; necessity_scope names the 2 terms with boundary runs")
n3("bd_arbcell.grant_skew",
   [L("Necessity3Arb", "skew0", "sufficient", "SkewClaim 0 0 = ArbBinary.exclusion_transport"),
    L("Necessity3Arb", "formA_false", "counter_trace", "not SkewClaim 1 0: d6 <= d5 + L weakened by 1"),
    L("Necessity3Arb", "formB_false", "counter_trace", "not SkewClaim 0 1: d5 <= d6 + L weakened by 1"),
    L("Necessity3Arb", "A_viol", "numbers"), L("Necessity3Arb", "B_viol", "numbers"),
    L("Necessity3Arb", "A_sat", "counter_run"), L("Necessity3Arb", "B_sat", "counter_run"),
    L("Necessity3Arb", "A_overlap", "numbers", "both grants high at 16"),
    L("Necessity3Arb", "B_overlap", "numbers", "both grants high at 16"),
    L("ArbBinary", "opposite_sense_exclusion", "context", "its skew bound is tight too: the counter-runs are opposite-sense handovers with request edges 5 > L apart")],
   "Bsx3 (B-necessity3.md, Necessity3Arb): each form, weakened by 1 tick in exclusion_transport's own hypothesis set (transport model, real INITs, "
   "L = 4, H_INIT_SETTLED, H_REQ_SEP), is refuted by an explicit opposite-sense handover with both grants high at 16. One parameter point per form, "
   "binary model, no Kleene X: necessary at the boundary, NOT an iff. bd_arbcell is not instantiated in gcd_hw.")
e = BY["bdc_amerge.bundled_idx_ack_g"]
n3("bdc_amerge.bundled_idx_ack_g",
   [L("Necessity3AMerge", "gack0", "sufficient", "GackClaim 0 = AMergeTimed.bidx_old_owner"),
    L("Necessity3AMerge", "gack_counter", "necessary", "general: in ANY Run + Scn2 with a server answering in exactly smin, if both forms fail the consumer sees the previous owner su before the minimal capture"),
    L("Necessity3AMerge", "gack1_false", "counter_trace", "not GackClaim 1"),
    L("Necessity3AMerge", "W2G_viol", "numbers", "r2 form off by exactly 1, q form by 3"),
    L("Necessity3AMerge", "W2G_run", "counter_run"),
    L("Necessity3AMerge", "W2G_stale", "numbers", "index 1 at the capture 26")],
   "Bsx3 (B-necessity3.md, Necessity3AMerge): this supersedes 'no counter-trace for this leg'. gack is necessary at the minimal capture RRb + dz with a "
   "worst-case (smin) server (gack_counter, general), and GackClaim 1 is refuted by one run at one consistent corner (gack1_false). A slower server or a "
   "later capture can still pass. The Bfd caveat above is unchanged: the necessity holds only at an edge-sampling consumer (necessity_scope).")

# ------------------------------------------------------------------ (4) exact rows: inequality vs the Lean iff's form
def pend_from_strict(rid, ineq_pairs, why):
    e = BY[rid]
    st = e.pop("strict")
    for k in st["forms"]:
        assert e["forms"][k]["margin_ps"] >= 1
        e["forms"][k]["margin_ps"] -= 1
    for old, new in ineq_pairs:
        sub(e, "inequality", old, new)
    e["strict_pending"] = why
    LOG.append(f"{rid}: inequality now the iff's '<=' form (margin -1 on forms {st['forms']}); the +1 moved to strict_pending")

pend_from_strict("bd_ctree.node_loop",
                 [("arc(n.fb -> O6).hi + 1 <= dist_min", "arc(n.fb -> O6).hi <= dist_min")],
                 "own-feedback race of each node (Bs, CElemStrict): with a 1-tick Kleene X window the per-node race would read L + 1 <= R, by analogy with "
                 "CElemStrict.box_iff; NOT proved for the tree (tree_box_exact is binary, monotone read maps). A checker may add the +1 as a 1 ps guard, "
                 "which is sufficient (stronger than the exact '<=' form) but not shown necessary.")
e = BY["bd_ctree.node_loop"]
e["exact_scope"] = ("exact = tree_box_exact, the binary '<=' form above, over the per-pin box with MONOTONE input read maps (H_PIN_FIFO: "
                    "TreeOK quantifies over Mono read maps only; feedback maps arbitrary in their box), every leaf schedule obeying H_LEAF / H_ACK "
                    "(H_ACK relative to the IDEAL root edge: an open-loop leaf schedule; the closed-loop environment is argued by causality, not proved), "
                    "real bd_c2/c3/c4 laws (cSpec), fan-in >= 2. Strict +1: strict_pending (not re-proved here). NOT covered: the protocol (bd_ctree.ack_wait); "
                    "one lower bound E for all leaves (per-leaf E_i argued, not proved); correlated corners (pins independent in the box: evaluate per corner, "
                    "H_ONE_CORNER, or in the box); non-monotone (non-FIFO) input reads; Kleene X windows inside the tree model.")
add_hyp(e, ["H_PIN_FIFO (monotone input read maps)", "H_LEAF", "H_ACK (open loop, ideal root edge)", "feedback maps in box", "pins independent (box)"])
pend_from_strict("bd_merge.uxa_loop",
                 [("arc(uxa.I2 -> O6).hi + 1 <= Wxa.lo", "arc(uxa.I2 -> O6).hi <= Wxa.lo"),
                  ("(Qhi + 1 <= Xlo + Eo + Alo, Qhi + 1 <= Xlo + Eo + K + Blo)", "(Qhi <= Xlo + Eo + Alo, Qhi <= Xlo + Eo + K + Blo)")],
                 "own-feedback race of uxa/uya (Bs, CElemStrict): with a 1-tick Kleene X window the race would read Qhi + 1 <= ..., by analogy with "
                 "CElemStrict.box_iff; NOT proved for this form (uxa_box_exact is binary, monotone read maps, measured from uxa's own output edge). A checker "
                 "may add the +1 as a 1 ps guard (sufficient, not shown necessary).")
e = BY["bd_merge.uxa_loop"]
e["exact_scope"] = ("exact = uxa_box_exact, the binary '<=' form above, over the per-pin box with MONOTONE input read maps (H_PIN_FIFO: Mono pa, Mono pb; "
                    "feedback map arbitrary), env H_CLIENT / H_SERVER, real bd_c2 INIT. Strict +1: strict_pending. Protocol (which edges the zero-delay "
                    "C-element has) not covered: bd_merge.seq / isochronic_forks. The uor / delay / server path is one lower bound K. Box necessity takes pins independent.")
add_hyp(e, ["H_PIN_FIFO (monotone input read maps)", "H_CLIENT", "H_SERVER", "pins independent (box)"])

for rid in ("bd_mux.uxa_rtz", "bd_mux.uya_rtz"):
    e = BY[rid]
    for r in e["lean"]:
        if r["file"].endswith("CElemStrict.lean") and r["name"] == "box_iff":
            r["role"] = "exact"
            r["note"] = ("uxa/uya's own race at its pins: over the loop box D in [Dlo, dlmax + dwmax] and every release s >= slo, clean <-> tb + Dhi + wb <= slo; "
                         "in binary-edge times (te = tb + wb, tr = slo + wa) this is te + dlmax + dwmax + wa <= tr, the row's inequality at wa = 1")
    add_lean(e, [L("CElemStrict", "clean_iff", "exact", "per run: Spec <-> tb + D + wb <= s")])
    e["exact_scope"] = ("the row's '+1' inequality = CElemStrict.box_iff / clean_iff at wa = 1 for the bd_c2 race at uxa's pins (te, tr are pin times), "
                        "per-pin Kleene mux-tree model (H_TREE, H_MUX_KLEENE, H_FB_PURE; 1 tick = grid minimum, not a measured slew), Facts on the real "
                        "bd_c2 INIT (c2_all). In the binary fixed-delay model the exact form is '<=' (te + dl + dw <= tr), from two theorems: rtz_exact_safe "
                        "(w >= dl + dw: safe) and rtz_counter (0 < w < dl + dw: oscillates). The composed mux (MuxRtzTimed) is not re-proved in the Kleene model.")
    add_hyp(e, ["H_TREE", "H_MUX_KLEENE (1-tick X window)", "H_FB_PURE"])
    LOG.append(f"{rid}: CElemStrict.box_iff role exact_inner -> exact (+ clean_iff); exact_scope says which form each theorem gives")

for rid in ("bd_c2.pulse_width", "bd_c2n.pulse_width", "bd_c3.pulse_width", "bd_c4.pulse_width"):
    e = BY[rid]
    assert "exact_scope" not in e
    e["exact_scope"] = ("the row's '+1' inequality = CElemStrict.box_iff / clean_iff at wa = 1 (held width W = (s + wa) - (tb + wb) >= Dhi + wa), "
                        "per-pin Kleene mux-tree model (H_TREE, H_MUX_KLEENE, H_FB_PURE; 1 tick = grid minimum, not a measured slew). In the binary "
                        "fixed-transport model the exact form is '>= Dmax' (c2_follow_hold + runt_oscillates, two theorems).")
    add_hyp(e, ["H_TREE", "H_MUX_KLEENE (1-tick X window)", "H_FB_PURE"])
    LOG.append(f"{rid}: exact_scope added (which form each cited theorem gives); no change to the inequality")

# ------------------------------------------------------------------ (3) kappa
KAPPA_HYP_ID = "H_SHARED_CORNER / H_SCATTER (kappa)"
doc["hypotheses_not_inequalities"].append({
    "id": KAPPA_HYP_ID,
    "catalogue_row": "A's corner model (Formal/Core/Substrate/CornerNat.lean)",
    "cells": ["every row whose corner.mode is 1C or 1C_both_corners_required"],
    "statement": ("H_ENDPOINTS (each arc has a FAST and a SLOW endpoint F <= S), H_AFFINE (nominal delay at corner c = (1-c)F + cS), "
                  "H_SHARED_CORNER (ONE corner c for the whole die), H_SCATTER kappa (every actual delay within 1 +- kappa of its nominal; one delay per "
                  "arc id per run). kappa is UNMEASURED on the current toolchain (A-kappa.md: the 0.311 ring bound was withdrawn, it came from the "
                  "LUT-permutation SDF bug); kappa = 0 is the old one-column check. Every kappa verdict in this file is conditional on the model and on a kappa value."),
    "lean": [
        {"file": "formal/lean/Formal/Core/Substrate/CornerNat.lean", "name": "Kappa", "role": "definition"},
        {"file": "formal/lean/Formal/Core/Substrate/CornerNat.lean", "name": "Scat", "role": "definition", "note": "H_SCATTER"},
        {"file": "formal/lean/Formal/Core/Substrate/CornerNat.lean", "name": "CornerModel", "role": "definition", "note": "one shared corner per realization"},
        {"file": "formal/lean/Formal/Core/Substrate/CornerNat.lean", "name": "EndpointOK", "role": "definition"},
        L("ConstraintsKappa", "allOK_of_gen", "sufficient", "GenOK at the FAST and SLOW endpoints (with request-side constant b) implies the form for every realization"),
        L("ConstraintsKappa", "allOK_iff_gen", "exact", "exact only under H_DISJ (no arc id on both sides) and H_DIV (extremes whole ps)"),
        L("ConstraintsKappa", "sandwich", "bound", "no H_DIV: the N-exact condition lies between GenOK and GenOK relaxed by (|P|+|Q|)(den-1)"),
        L("ConstraintsKappa", "allOK_cancel", "exact", "a common prefix (same arc ids) cancels exactly"),
        L("ConstraintsKappa", "box_unsound_with_kappa", "counter_trace", "the box (hi at SLOW, lo at FAST, no kappa) is unsound for kappa > 0 (degenerate arc F = S)"),
        L("ConstraintsKappa", "one_corner_unsound_with_kappa", "counter_trace", "H_ONE_CORNER without kappa is unsound for kappa > 0"),
        L("ConstraintsKappa", "slow_only_unsound", "counter_trace", "a SLOW-only check is unsound even at kappa = 0"),
        L("ConstraintsKappa", "endpointNat_not_sufficient", "counter_trace", "rounding at the endpoints only is unsound (interior corner c = 5/6)"),
        L("ConstraintsKappa", "witness_exact", "non_vacuity"),
    ],
    "check": ("GenOK per form at both endpoints, unrounded (corner.kappa of each row); kappa must be measured first. Shared arc labels on both sides of a form "
              "are NOT cancelled automatically (two traversals or two pins; cancelling assumes H_SAME_TRAVERSAL). Audit P7-kappa: in a 'lit' reading the "
              "prjxray within-corner min..max spread must itself fit inside kappa, so 'lit' safety at small kappa implicitly assumes that spread is die-wide correlated."),
})
KB_HYP_ID = "H_KLEENE_LUT / H_X_UNIFORM"
doc["hypotheses_not_inequalities"].append({
    "id": KB_HYP_ID,
    "catalogue_row": "Bkx (formal/notes/B-kleene-box.md)",
    "cells": ["bd_steer", "bd_mux (uj0/uj1)", "bdc_muxn (decode + selected join)", "bd_latch"],
    "statement": ("H_KLEENE_LUT: a LUT output is lutK of its K3 pin reads (Core's mux tree with mux(X, a, b) = a if a = b else X), which is the exact "
                  "ternary closure of the INIT over all Boolean completions (audit P8 re-checked it on 729 vectors for 6 INITs): the hazard-free, "
                  "OPTIMISTIC LUT model (e.g. C2(1,1,X) = 1), pin-order independent. H_X_UNIFORM: every binary edge T carries an X window [T - a, T + c) "
                  "with the SAME split on every edge (w = a + c). w = 1 tick is the grid minimum, not a measured slew."),
    "lean": [
        {"file": "formal/lean/Formal/Cells/MuxTree.lean", "name": "muxTree_eq_lutK", "role": "reduction"},
        L("KleeneBox", "steer_K_iff_binary", "kleene", "definite-window coordinates: K3 adds no failure mode"),
        L("KleeneBox", "steer_edges_K", "exact", "binary-edge coordinates under H_X_UNIFORM: +w"),
        L("KleeneBox", "latch_edges_uniform", "exact"),
    ],
    "check": "none on this silicon: whether a real LUT is hazard-free with several mid-rail inputs is UNVERIFIED (physical hypothesis, audit P8); unequal splits per edge fall back to the definite-window form",
})

KAPPA_FIELD = {
    "hypotheses": ["H_ENDPOINTS", "H_AFFINE", "H_SHARED_CORNER", "H_SCATTER kappa"],
    "kappa": "unmeasured on the current toolchain",
    "check": ("GenOK at the FAST and SLOW endpoints, unrounded: (1+kappa)*sum_P ep + a <= (1-kappa)*sum_Q ep + b, a/b the data-side / request-side "
              "constants (ConstraintsKappa.allOK_of_gen: sound; allOK_iff_gen: exact under H_DISJ + H_DIV; sandwich otherwise). kappa = 0 is the one-column check."),
    "see": KAPPA_HYP_ID,
}
NEW_RULE = ("evaluate both sides in the SAME prjxray column, once at FAST_MIN and once at SLOW_MAX (H_ONE_CORNER): this is GenOK at kappa = 0, "
            "unsound in A's model for kappa > 0 (ConstraintsKappa.one_corner_unsound_with_kappa); with kappa use GenOK at both endpoints (corner.kappa). "
            "box (every hi at SLOW_MAX, every lo at FAST_MIN) is sound only when every delay lies in [FAST_MIN, SLOW_MAX] (H_DELAY_BOX), NOT in A's "
            "kappa model for kappa > 0 (box_unsound_with_kappa; with kappa: (1+kappa)S vs (1-kappa)F). A SLOW_MAX-only check is unsound in A's model "
            "even at kappa = 0 (slow_only_unsound); the guard As - Af/k (ArbCorners.fast_neg_iff) belongs to the H_WIRE_RATIO model only. "
            "Never rise=FAST / fall=SLOW.")
OLD_RULE = None
nk = 0
for e in C:
    c = e["corner"]
    if c["mode"] in ("1C", "1C_both_corners_required"):
        if OLD_RULE is None:
            OLD_RULE = c["rule"]
        assert c["rule"] == OLD_RULE, e["id"]
        c["rule"] = NEW_RULE
        c["kappa"] = copy.deepcopy(KAPPA_FIELD)
        nk += 1
LOG.append(f"corner.rule rewritten and corner.kappa added on {nk} rows (mode 1C / 1C_both_corners_required)")

# per-row kappa results on the arbiter rows
NL = "OnNetlistArbKappa"; GK = "OnGcdArbKappa"
NL_TXT = ("link_arb (4 routed seeds), A0 fork, 7g's condition (no_early_ack_iff) per seed x client, two endpoint readings (lit: FAST_MIN..SLOW_MAX for every "
          "arc; cons: early arcs FAST_MIN..SLOW_MIN, late arc FAST_MAX..SLOW_MAX + Elmore): SAFE for every kappa <= kappa* (safe_*), at rule A's 1/11 all 16 "
          "pair x reading cases safe (verdict_*_κA); at kappaE = 383/1927 one case fails (s1 client 2 cons: verdict_s1c2_cons_κE). UNSAFE is proved only "
          "for kappa >= kappa* + 6/(E+L) (unsafe_*); in between (width <= 0.0057) the whole-ps model is NOT decided, so kappa* is the safe bound of the "
          "real relaxation, not an exact threshold (audit row 18: inside the gap s1c2 cons is already violated at 200/1103; that is the auditor's "
          "theorem P7kAudit.s1c2_gap_unsafe_at_200, not in this repo). One fixed delay per arc per run; kappa unmeasured.")
def nl_refs(k):
    out = [L(NL, "fork_le_of_endpoint", "corner", "GenOK at both endpoints gives the 7g fork condition for every realization"),
           L(NL, "counter_core", "corner", "the worst realization at the binding endpoint breaks the fork")]
    for s in (1, 2, 3, 4):
        for rd in ("lit", "cons"):
            out.append(L(NL, f"safe_s{s}c{k}_{rd}", "corner"))
            out.append(L(NL, f"unsafe_s{s}c{k}_{rd}", "corner"))
    out.append(L(NL, "nonvacuous_lit", "non_vacuity"))
    return out
GK_COMMON = ("gcd_hw (36 routed arbiters, seeds 2/3/4/d), OnGcdArbKappa, per condition x reading (1296 decided rows): safe for kappa <= kappa* "
             "(row_safe), a violating realization of the ARC FORM for kappa >= kappa_u, kappa_u - kappa* < 1e-4 (row_unsafe; rows_gap checks < 1e-4, the note gives <= 1.8e-5): the gap is "
             "tiny but the unsafe side is at the arc-form level, not gate level, and not at kappa* itself. Design: every condition of every arbiter "
             "holds for kappa <= 16587/374773 ~ 0.0443 in the lit reading (lit_min, design_lit_safe; gate level: design_gate_lit), 0.0802 with the "
             "server credited (lit_srv_min). Arc data from probe Bar's extraction (UNTRUSTED; gcd_hw routes not on disk). Per-condition minima below "
             "are from B-gcd-arb-kappa.md's table (3 decimals; the fractions are in the Lean rows). kappa unmeasured.")
def gk_refs(gate):
    return [L(GK, "row_verdict", "corner"), L(GK, "rows_ok", "corner"), L(GK, "rows_gap", "corner"),
            L(GK, "lit_min", "corner"), L(GK, "design_lit_safe", "corner"), L(GK, "design_gate_lit", "corner"),
            L(GK, "design_gate_nonvacuous", "non_vacuity")] + [L(GK, g, "corner", "bridge from the arc form to this row's gate-level theorem") for g in gate]
GK_ROWS = {
    "bd_arbiter.a0_fork_client1": (["fork1_gate"], "fork1: lit min 0.328, cons min 0.238 (seed 4 merge12.uarb2); never binding."),
    "bd_arbiter.a0_fork_client2": (["fork2_gate"], "fork2: lit min 0.217, cons min 0.129 (seed 4 merge12.uarb2); never binding."),
    "bd_arbiter.rt1": (["rt1_gate", "rt1s_gate"], "RT1 server-free: lit min 0.088 (seed d merge9.uarb1); cons: FAILS at kappa = 0 on seed d merge9.uarb1 (cons_neg). RT1s (A0 branch + server): lit min 0.597."),
    "bd_arbiter.rt1b": (["rt1b_gate", "rt1bs_gate"], "RT1b server-free: lit min 16587/374773 ~ 0.0443 (seed 3 merge12.uarb1: the design minimum, design_lit_tight at the arc-form level); cons: FAILS at kappa = 0 on seed 2 merge3.uarb1 and seed 3 merge12.uarb1 (cons_neg). RT1bs: lit min 0.617."),
}
for rid in ("bd_arbiter.rt2_pulse", "bd_arbiter.rt2_g1", "bd_arbiter.rt2_forkA", "bd_arbiter.rt2_forkG"):
    GK_ROWS[rid] = (["rt2_gate"], "RT2 (forms mP, mG, mA, mGG with H_SERVER_GRAPH; the table's RT2 column also takes fork2): column lit min 0.217, cons min 0.129; never binding.")
for rid in ("bd_arbiter.rt2b_pulse2", "bd_arbiter.rt2b_g2", "bd_arbiter.rt2b_forkA2", "bd_arbiter.rt2b_forkG2"):
    GK_ROWS[rid] = (["rt2b_gate"], "RT2b (forms nP, nG, nA, nGG; the column also takes fork1): column lit min 0.328, cons min 0.238; never binding.")
for rid, (gate, txt) in GK_ROWS.items():
    e = BY[rid]
    res = [GK_COMMON + " " + txt]
    refs = gk_refs(gate)
    if rid in ("bd_arbiter.a0_fork_client1", "bd_arbiter.a0_fork_client2"):
        k = 1 if rid.endswith("client1") else 2
        res.insert(0, NL_TXT)
        refs = nl_refs(k) + refs
        refs.append(L(NL, f"verdict_s1c{k}_lit_κA", "corner", "one of the 16 decided verdicts at kappa = 1/11 (the others: verdict_s*c*_*_κA / _κE)"))
        if k == 2:
            refs.append(L(NL, "verdict_s1c2_cons_κE", "corner", "the one unsafe case at kappaE"))
    e["corner"]["kappa"]["results"] = res
    add_lean(e, refs)
    LOG.append(f"{rid}: corner.kappa.results + {len(refs)} kappa citations (role corner)")
LOG.append("OnGcdArbKappa's ArbPin2 forms h12 / h21 / o1x / o2x have no row in this file (ArbPin2 is not an entry); their minima stay in B-gcd-arb-kappa.md")

# ------------------------------------------------------------------ (5) LinkExact: one bd_link stage
LX = "LinkExact"
link = {
    "id": "bd_link.stage",
    "cell": "bd_link",
    "catalogue_row": "none (Blink, formal/notes/B-link-exact.md)",
    "obligation": "one bd_link stage (bd_c2n controller + one bd_latch bit, real INITs, one token, open loop): every behaviour in the per-pin box implements the one-token transfer with the datum captured and held",
    "inequality": ("H_RST_WIDTH Rhi + Qhi <= W + Rlo; H_RACE_UP U1 + Qhi <= min(Fa + Alo, Rb + Blo); H_RACE_DN V1 + Qhi <= Fb + Blo; "
                   "H_SETUP_PULSE U1 + Ehi + Fhi <= V0 + Elo; H_SETUP_DATA Td + Dhi + Fhi <= V0 + Elo; H_HOLD V1 + Ehi <= Tn + Dlo "
                   "(U1 = Ra1 + Ahi, V0 = max(Fa + Alo, Rb + Blo), V1 = max(Fa1 + Ahi, Rb1 + Bhi); A/B/Q/R/D/E/F = req, ack, controller loop, rst, data, "
                   "enable branch, latch loop windows: wire + SP + arc); definite-window times. In binary-edge times with one tick of X before each edge "
                   "(W1 = W + 1, Ra1 = Ra + 1, ...) each of the six is strict (strict_edges)."),
    "forms": [],
    "refers_to": ["bd_c2n.reset_width", "bd_c2n.env_latency", "bd_latch[odd].setup_pulse", "bd_latch[odd].setup_data", "bd_latch[odd].hold"],
    "informational": True,
    "lean": [
        L(LX, "exact", "exact", "under Wf and Split: SafeLink P v <-> Conj P"),
        L(LX, "no_cross", "exact", "the same iff with the per-cell theorems' own left sides (NecessityReset.c2n_box_exact, LibGapLatch.SafeBox at A, B, C := U1, V0, V1): composition adds no cross-cell condition"),
        L(LX, "strict_edges", "exact", "Conj <-> the six strict inequalities in binary-edge times (1-tick X convention)"),
        L(LX, "sufficient", "sufficient", "Wf and Conj give the spec for every behaviour (no Split needed)"),
        L(LX, "need_rst", "necessary"), L(LX, "need_up", "necessary", "needs Split"), L(LX, "need_dn", "necessary"),
        L(LX, "need_pulse", "necessary"), L(LX, "need_data", "necessary"), L(LX, "need_hold", "necessary"),
        L(LX, "Wf", "definition", "scope: ordered windows, H_RST_EARLY, H_RST_EARLY_ACK, H_ACK_ORDER"),
        L(LX, "Split", "definition", "H_REL_SPLIT: Fa + Alo != Rb + Blo (necessity of H_RACE_UP only)"),
        L(LX, "Spec", "definition"), L(LX, "SafeLink", "definition"), L(LX, "Conj", "definition"),
        L(LX, "witness", "non_vacuity", "P0 (illustrative slow-corner-scale numbers, one corner, not a route): Wf, Split, Conj, SafeLink, and a behaviour meeting Spec"),
        L(LX, "Pv_one_tick", "numbers", "six parameter sets, each violating exactly one conjunct by 1 ps, scope met"),
        L(LX, "Pv_breaks", "counter_trace", "each of the six is unsafe"),
        L(LX, "out_port", "context", "shard C's one-token PortUpTo for the output channel, from Spec plus H_ROUT, H_ACK, H_ORDER, H_X_LEAD"),
        L(LX, "rout_definite", "lemma"),
    ],
    "exactness": "exact",
    "exact_scope": ("iff relative to LinkExact's Spec (window-token node + capture), ONLY inside the scope Wf and Split. Wf holds conditions that are NOT in the "
                    "conjunction: ordered windows (0 <= lo <= hi for every pin, 1 <= Qlo, 1 <= Flo, W <= W1, Ra <= Ra1 <= Fa <= Fa1, Rb <= Rb1 <= Fb <= Fb1), "
                    "H_RST_EARLY (W1 + Rhi < Ra + Alo: rst surely read low before req can be read moved), H_RST_EARLY_ACK (W1 + Rhi < Rb + Blo, the same for "
                    "ack), H_ACK_ORDER (V1 <= Fb + Blo; implied by H_RACE_DN). Split (H_REL_SPLIT, Fa + Alo != Rb + Blo) is needed only for the necessity "
                    "of H_RACE_UP: at the release tie that necessity is NOT decided. Binary '<=' in definite-window times; strict in binary-edge times (strict_edges). "
                    "Data path: the en = c variant (not BD_LINK_DC). NOT covered: closed loop, more than one token, a W-bit bus as one theorem, the input port, "
                    "correlated corners (pins independent in the box)."),
    "exactness_note": ("Blink (formal/notes/B-link-exact.md, LinkExact.lean): all seven pins (req, ack, own feedback, rst, data, enable, latch loop) read through "
                       "their own NON-monotone windows (H_CTL_READ / H_PIN_READ, real INITs in Kleene semantics), power-up arbitrary, environment and data "
                       "arbitrary (X included) outside their definite windows (H_ENV, one token, open loop). Finding: no cross-cell condition (no_cross); the "
                       "coupling is substitution only: the controller's req-pin spread Ahi - Alo enters the latch's setup_pulse budget, the latch hold window "
                       "closes at the controller's slow reads V1, and latch hold rests on the controller's fall race. Audit P8: CONFIRMED (iff, both sides inhabited in scope)."),
    "hypotheses": ["H_CTL_READ / H_PIN_READ (non-monotone)", "H_KLEENE_LUT", "H_BOX", "H_ENV (one token, open loop)",
                   "Wf: ordered windows", "Wf: H_RST_EARLY", "Wf: H_RST_EARLY_ACK", "Wf: H_ACK_ORDER", "Split (H_REL_SPLIT; necessity of H_RACE_UP only)"],
    "site_pins": {"needed": True, "roles": ["every controller and latch pin, lo and hi (inside the seven windows)"]},
    "rule": {"rule": "none", "verdict": "none", "detail": "covered by the referred per-cell rows at the substituted times (no_cross); UNCHECKED as a composed row"},
    "corner": {"mode": "n/a", "rule": "see refers_to (pins independent in the box; per corner realisation the windows collapse)"},
    "check_scope": "route_plus_env",
    "evidence": "illustrative numbers only (witness P0, margins 1280 / 739 / 939 / 729 / 1970 / 1629 ps); no route",
    "status": "proved",
    "combine": "all",
}
assert "bd_link.stage" not in BY
C.append(link)
BY[link["id"]] = link
LOG.append("bd_link.stage: NEW row (LinkExact), exact inside Wf + Split, informational (refers_to the per-cell rows)")
for rid in link["refers_to"]:
    add_lean(BY[rid], [L(LX, "no_cross", "context", "in one bd_link stage (scope Wf: ordered windows, H_RST_EARLY, H_RST_EARLY_ACK, H_ACK_ORDER; Split for H_RACE_UP's necessity) this row, at the substituted times, is all the stage needs: bd_link.stage")])
    LOG.append(f"{rid}: + LinkExact.no_cross (context)")

# ------------------------------------------------------------------ conventions, provenance
cv = doc["conventions"]
cv["corner_rule"] = (cv["corner_rule"].rstrip() +
    " Bj5 (ConstraintsKappa, Bk2): '1C' as two columns is GenOK at kappa = 0 and unsound for kappa > 0 (one_corner_unsound_with_kappa); 'box' is "
    "sound only in the independent-box model (every delay in [FAST_MIN, SLOW_MAX], H_DELAY_BOX), not in A's kappa model (box_unsound_with_kappa); a "
    "SLOW_MAX-only check is unsound in A's model even at kappa = 0 (slow_only_unsound); the As - Af/k guard is the H_WIRE_RATIO model's. See conventions.kappa.")
cv["kappa"] = ("corner.kappa on every 1C / 1C_both_corners_required row: the form under A's corner model (hypotheses_not_inequalities '" + KAPPA_HYP_ID +
               "'). Check: GenOK at both endpoints, unrounded (sound: allOK_of_gen; exact only under H_DISJ + H_DIV: allOK_iff_gen; otherwise sandwich). "
               "kappa is UNMEASURED on the current toolchain, so every kappa verdict is conditional. corner.kappa.results (arbiter rows) quotes "
               "OnNetlistArbKappa / OnGcdArbKappa: kappa* is a proved SAFE bound; the unsafe side is proved only from a larger kappa (link_arb: kappa* + 6/(E+L), "
               "gap not decided; gcd_hw: kappa_u <= kappa* + 1.8e-5, arc-form level only). Per-pair thresholds are NOT exact (audit row 18).")
cv["hypotheses"] = ("optional list on an entry (Bj5): the named model hypotheses its cited theorems take (e.g. H_KLEENE_LUT, H_X_UNIFORM, H_PIN_FIFO, the "
                    "scope Wf of LinkExact). Rows touched before Bj5 carry them in exactness_note prose instead.")
cv["strictness"] = (cv["strictness"].rstrip() +
    " Bj5: the select setup/hold rows of bd_steer, bd_mux and bdc_muxn are strict on KleeneBox's backing (steer_strict_K, join_strict_K, muxn_edges_K at w = 1): "
    "in binary-edge times under H_KLEENE_LUT + H_X_UNIFORM they are exact WITH the +1; in definite-window times the '<=' form is exact. bd_ctree.node_loop "
    "and bd_merge.uxa_loop moved from strict to strict_pending: their iffs (tree_box_exact, uxa_box_exact) are binary '<=' and the +1 was not re-proved "
    "for them (audit P8). An entry labelled exact that carries `strict` must cite as 'exact' an iff that covers the +1 form (validator: STRICT_IFFS).")
doc["produced_by"] = (doc["produced_by"].rstrip() +
    " Updated by probe Bj5 (2026-10-29) from B-kleene-box.md (KleeneBox: select rows strict, H_KLEENE_LUT / H_X_UNIFORM), B-necessity3.md "
    "(Necessity3Pipe/PipeCtl/Arb/AMerge: 7 rows necessary at the boundary, rst_lines partly), B-constraints-kappa.md / B-arb-kappa.md / "
    "B-gcd-arb-kappa.md (corner.kappa, kappa unmeasured), B-link-exact.md (new bd_link.stage) and audit P8 / P7-kappa (exact rows' "
    "inequality vs iff form); JSON patched by cell_constraints.bj5.py, which cell_constraints.gen.py runs after its own pass.")

json.dump(doc, open(OUT, "w"), indent=1)
for x in LOG:
    print(x)
