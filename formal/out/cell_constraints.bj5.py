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

# ================================================================== probe Bj6 (2026-10-29)
# Second Bj pass of the day. Applies, from today's committed notes:
#   B-necessity4.md (Necessity4Mux / Necessity4MuxC / Necessity4MuxN), B-necessity5.md (Necessity5*),
#   B-kleene-win.md (KleeneWin), B-kleene-pess.md (KleenePess),
#   B-gcd-arb-kappa-tight.md (OnGcdArbKappaTight, OnGcdArbKappaTightA).
#   B-lutfb-bridge.md (LutFbBridge): no row of this file concerns C's LutFb / FbFirst premises; nothing added.
# Every name cited below is declared in the cited file (the validator greps each one).
from collections import Counter
LOG.append("---- probe Bj6")

def relabel(rid, new, refs, note, old_ok=None):
    e = BY[rid]
    old = e["exactness"]
    if old_ok is not None:
        assert old in old_ok, (rid, old)
    e["exactness"] = new
    add_lean(e, refs)
    note_append(e, note)
    LOG.append(f"{rid}: {old} -> {new}")
    return e

def new_row(row):
    assert row["id"] not in BY, row["id"]
    C.append(row)
    BY[row["id"]] = row
    LOG.append(f"{row['id']}: NEW row ({row['exactness']})")

def add_scope(e, field, txt):
    e[field] = (e.get(field, "") + ("; " if e.get(field) else "") + txt)

# ------------------------------------------------------------------ (1) Necessity4Mux* (Bnx4)
N4, N4C, N4N = "Necessity4Mux", "Necessity4MuxC", "Necessity4MuxN"
BIN_NOTE = ("Binary '<=' model (OpsTimedMux / MuxN3Timed: H_LUT_FIFO lumped LUT arcs, FIFO wires, FASTFALL = 0 line FIFO, "
            "port-level causal partners with minimum latencies, real INITs). The JSON form carries the Bs strict +1: a binary run "
            "refuted at slack 1 against '<=' is 2 ticks from the strict form; the +1 itself is CElemStrict's (boundary_x), "
            "not re-proved for these composed paths.")

old = BY["bd_mux.uj_env_latency_req"]
CS_MUX = [copy.deepcopy(r) for r in old["lean"] if r["file"].endswith("CElemStrict.lean")]

def mux_max_row(j):
    J = f"uj{j}"
    sig, ack = ("j0", "uxa") if j == 0 else ("j1", "uya")
    Lj, wjh, Wj, Wo, Wz, La, Wa, E, Wr = (("Lj0", "wj0h", "W0x", "W0o", "Wzx", "Lxa", "Wxa", "Ex", "Wx") if j == 0 else
                                          ("Lj1", "wj1h", "W1y", "W1o", "Wzy", "Lya", "Wya", "Ey", "Wy"))
    fa = copy.deepcopy(old["forms"][j])
    rp = fa["request_paths"][0]
    k = [i for i, a in enumerate(rp) if a["kind"] == "lut_arc" and a["from"] == f"{ack}.I0"]
    assert len(k) == 1, (j, rp)
    tail = copy.deepcopy(rp[k[0] + 1:])
    fa["note"] = fa["note"] + "R (a): the j -> ack C-element branch (= the shipped form)"
    fb = {"launch": fa["launch"], "data_paths": copy.deepcopy(fa["data_paths"]),
          "request_paths": [[
              {"kind": "lut_arc", "from": f"{J}.{{I0|I1}}", "to": f"{J}.O6", "lean_sym": f"{Lj}.lo"},
              {"kind": "wire", "from": sig, "to": f"uor.I{j}", "lean_sym": f"{Wo}.lo"},
              {"kind": "site_pin", "from": f"uor.I{j}@pip", "to": f"uor.I{j}", "pin_role": "join/request"},
              {"kind": "lut_arc", "from": f"uor.I{j}", "to": "uor.O6", "lean_sym": "Lor.lo"},
              {"kind": "line", "name": "udly", "edge": "any", "path": "chain",
               "spec": "uor.O6 -> bd_delay (FASTFALL=0, one FIFO channel) -> z_req at the server", "lean_sym": "Dz.lo"},
              {"kind": "env", "name": "Es", "spec": "server: z_req edge at its pin -> z_ack edge (H_SRV), min", "lean_sym": "Es"},
              {"kind": "wire", "from": "z_ack.drv", "to": f"{ack}.I1", "lean_sym": f"{Wz}.lo"},
              {"kind": "site_pin", "from": f"{ack}.I1@pip", "to": f"{ack}.I1", "pin_role": "z_ack"},
              {"kind": "lut_arc", "from": f"{ack}.I1", "to": f"{ack}.O6", "lean_sym": f"{La}.lo"}] + tail],
          "margin_ps": fa["margin_ps"],
          "note": fa["note"].split(" (a)")[0] + " (b): the z_ack branch (j -> uor -> line -> server -> z_ack -> ack C-element)"}
    r = copy.deepcopy(old)
    r.pop("also_applies_to", None)
    r["id"] = f"bd_mux.{J}_env_latency_req_max"
    r["catalogue_row"] = "none (Bnx4, formal/notes/B-necessity4.md)"
    r["obligation"] = (f"H_DEP_J{j} through the client, max form (Necessity4Mux.MuxStaticN, field S_J{j}_{'XR' if j == 0 else 'YR'} at slack 0): "
                       f"{J}'s own feedback settles before the client's answer returns to the join; the ack C-element {ack} waits for BOTH "
                       f"{sig} and z_ack, so the return path is the later of the two branches (combine any = the max)")
    r["inequality"] = (f"{Lj}.hi + {wjh} + 1 <= {Lj}.lo + max({Wj}.lo, {Wo}.lo + Lor.lo + Dz.lo + Es + {Wz}.lo) + {La}.lo + {Wa}.lo + {E} + {Wr}.lo "
                       f"(the z_ack branch uses the per-branch wire {Wo}.lo, {sig} -> uor.I{j}, not the min wo)")
    r["forms"] = [fa, fb]
    r["combine"] = "any"
    r["strict"] = dict(copy.deepcopy(old["strict"]), forms=[0, 1])
    lean = [L(N4, "mux_ok_staticN", "sufficient", "mux_ok's whole conclusion (both joins, z_req, both acks, order facts) from MuxStaticN ... 0 0 = MuxStatic with S_J0_X / S_J1_Y in max form"),
            L(N4, "mux_timing_of_staticN", "sufficient"),
            L(N4, "MuxStaticN", "definition"),
            L(N4, "staticN_of_static", "lemma", "the shipped MuxStatic implies the max form"),
            {"file": "formal/lean/Formal/Cells/OpsTimedMux.lean", "name": "MuxCausal", "role": "definition"}] + copy.deepcopy(CS_MUX)
    if j == 0:
        lean += [L(N4, "claimX0", "sufficient", "ClaimX 0 = mux_ok_staticN's hypothesis set"),
                 L(N4, "fail10", "counter_run", "N4.run 10: every MuxStaticN field with S_J0_XR weakened by 1 holds and S_J0_XR fails by exactly 1; the max is taken by the z_ack branch (5 > W0x = 1)"),
                 L(N4, "claimX1_false", "counter_trace", "not ClaimX 1: j0 = 0 at 32 inside its token-0 window [22, 35), z_req = 0 at 35 inside [25, 38)"),
                 L(N4, "pass8", "non_vacuity", "N4.run 8 meets the strict max form (1 + 8 + 1 <= 10), MuxStaticN and the full spec")]
        r["exactness"] = "sufficient+necessary_at_boundary"
        r["necessity_scope"] = ("the z_ack branch (form 1), one parameter point (N4.run 10, unit delays, uj0 feedback net 10), binary '<=' at slack 1 "
                                "(the strict +1 form is 2 ticks from it); form 0 (the j branch) has no boundary run of its own (in that run the max is the z_ack branch)")
        ex = "Bnx4: sufficient (mux_ok_staticN) and necessary at the boundary on its z_ack branch (claimX1_false). "
    else:
        lean += [L(N4, "pass8", "non_vacuity", "MuxStaticN (both joins) holds on N4.run 8")]
        r["exactness"] = "sufficient"
        ex = "Bnx4: sufficient (mux_ok_staticN covers both joins); the uj1 boundary run is the symmetric statement, NOT built. "
    r["lean"] = lean
    r["exactness_note"] = (ex + "Replacement of bd_mux.uj_env_latency_req (its uj%d form): that form charges only the j -> ack wire, the real "
                           "return also waits for z_ack. One row per join because the max is an OR of two forms (combine any) and the old "
                           "row's combine is all over both joins. LUT arcs lumped (Lj.hi / Lj.lo kept as the house's box; per-pin arcs NOT "
                           "covered). " % j + BIN_NOTE)
    r["hypotheses"] = ["H_LUT_FIFO (lumped LUT arcs)", "MuxCausal (port-level causal partners, minimum latencies)",
                       "FASTFALL = 0 line FIFO", "real uj0 / uj1 / uor / bd_c2 INITs"]
    r["site_pins"] = copy.deepcopy(old["site_pins"])
    r["site_pins"]["roles"] = sorted(set(r["site_pins"].get("roles", []) + [f"{ack}.I1 (z_ack) lo", f"uor.I{j} lo"]))
    r["rule"] = {"rule": "none", "verdict": "none", "detail": "UNCHECKED"}
    return r

mx0, mx1 = mux_max_row(0), mux_max_row(1)
new_row(mx0); new_row(mx1)
e = relabel("bd_mux.uj_env_latency_req", "not_necessary",
            [L(N4, "pass8", "not_necessary", "N4.run 8 (unit delays, uj0 feedback net 8, x/y alternating, Ex = 1, Ec = 6, Es = 1): S_J0_X reads 9 <= 6 (false by 3; by 4 in the strict form), every max-form field holds and the cell meets mux_ok's spec; with mux_ok_staticN, every run in the box at this point passes"),
             L(N4, "pass8_values", "numbers", "the race is live: j0 rises at 22, x_req low at the join's pin at 31"),
             L(N4, "SJ0X_iff", "numbers", "S_J0_X on run W holds iff W <= 5"),
             L(N4, "staticN_of_static", "lemma", "the shipped form implies the replacement"),
             L(N4, "mux_ok_staticN", "sufficient", "the replacement's sufficiency")],
            "Bnx4 (B-necessity4.md, Necessity4Mux): NOT necessary, in the box sense: the max form is sufficient over every run "
            "(mux_ok_staticN), and at the parameter point of pass8 it holds while S_J0_X fails, so every run there passes. Replacement: "
            "the max-form rows bd_mux.uj0_env_latency_req_max (necessary at the boundary on its z_ack branch) and bd_mux.uj1_env_latency_req_max "
            "(sufficient). This supersedes Lt4's analysis above (now proved). " + BIN_NOTE, old_ok=("sufficient",))
e["replacement"] = mx0["id"]
e["replacement_rows"] = [mx0["id"], mx1["id"]]

oldn = BY["bdc_muxn.uj_env_latency_req"]
fa = copy.deepcopy(oldn["forms"][0])
rp = fa["request_paths"][0]
k = [i for i, a in enumerate(rp) if a["kind"] == "lut_arc" and a["from"] == "ua_i.I0"]
assert len(k) == 1
tail = copy.deepcopy(rp[k[0] + 1:])
fa["note"] = "MN3StaticN.S_J_XR, per i (a): the j -> ack C-element branch (= the shipped form)"
fb = {"launch": fa["launch"], "data_paths": copy.deepcopy(fa["data_paths"]),
      "request_paths": [[
          {"kind": "lut_arc", "from": "uj_i.{I0|I1}", "to": "uj_i.O6", "lean_sym": "Lj.lo"},
          {"kind": "wire", "from": "uj_i.O6", "to": "or3.{I0|I1|I2}", "lean_sym": "wo"},
          {"kind": "site_pin", "from": "or3.{I0|I1|I2}@pip", "to": "or3.{I0|I1|I2}", "pin_role": "join/request"},
          {"kind": "lut_arc", "from": "or3.{I0|I1|I2}", "to": "or3.O6", "lean_sym": "Lo.lo"},
          {"kind": "line", "name": "udly", "edge": "any", "path": "chain", "spec": "|j -> bd_delay_gated FASTFALL line -> z_req at the server", "lean_sym": "Dl"},
          {"kind": "env", "name": "Es", "spec": "server: z_req edge at its pin -> z_ack edge, min", "lean_sym": "Es"},
          {"kind": "wire", "from": "z_ack.drv", "to": "ua_i.I1", "lean_sym": "Wza.lo"},
          {"kind": "site_pin", "from": "ua_i.I1@pip", "to": "ua_i.I1", "pin_role": "z_ack"},
          {"kind": "lut_arc", "from": "ua_i.I1", "to": "ua_i.O6", "lean_sym": "La.lo"}] + tail],
      "margin_ps": fa["margin_ps"],
      "note": "MN3StaticN.S_J_XR, per i (b): the z_ack branch (uses the shipped lower bounds wo over the three inputs and Dl)"}
rn = copy.deepcopy(oldn)
rn["id"] = "bdc_muxn.uj_env_latency_req_max"
rn["catalogue_row"] = "none (Bnx4, formal/notes/B-necessity4.md)"
rn["obligation"] = ("S_J_X max form (Necessity4MuxN: MN3StaticN.S_J_XR at slack 0): join i's own feedback settles before its answer returns; "
                    "the ack C-element ua_i waits for BOTH j_i and z_ack (combine any = the max)")
rn["inequality"] = "Lj(i).hi + wjh(i) + 1 <= Lj(i).lo + max(Wja(i).lo, wo + Lo.lo + Dl + Es + Wza(i).lo) + La(i).lo + Wak(i).lo + Ex + Wx(i).lo (per i)"
rn["forms"] = [fa, fb]
rn["combine"] = "any"
rn["strict"] = dict(copy.deepcopy(oldn["strict"]), forms=[0, 1])
rn["lean"] = [L(N4N, "muxn3_ok_staticN", "sufficient", "muxn3_ok's full conclusion (joins, z_req, acks) with S_J_X in max form; reset sequencing, the line flush and 1 <= N taken as before"),
              L(N4N, "muxn3_timing_of_staticN", "sufficient"),
              L(N4N, "MN3StaticN", "definition"),
              L(N4N, "staticN_of_static", "lemma", "the shipped MN3Static implies the max form"),
              L(N4N, "pass8", "non_vacuity", "Mn3Wit's unit run with every join's feedback net 8: the strict max form holds for every input and the cell's conclusion holds"),
              {"file": "formal/lean/Formal/Cells/MuxN3Timed.lean", "name": "MN3Causal", "role": "definition"}] + \
             [copy.deepcopy(r) for r in oldn["lean"] if r["file"].endswith("CElemStrict.lean")]
rn["exactness"] = "sufficient"
rn["exactness_note"] = ("Bnx4: sufficient (muxn3_ok_staticN). Replacement of bdc_muxn.uj_env_latency_req. Its boundary is NOT shown for muxn: in "
                        "Mn3Wit's run S_J_C has the same right side (10), so violating the max form by 1 also breaks S_J_C; an isolated "
                        "counter-run needs a slower control sender. " + BIN_NOTE)
rn["hypotheses"] = ["H_LUT_FIFO (lumped LUT arcs)", "MN3Causal (port-level causal partners, minimum latencies)", "H_FLUSH_STAGE (bd_delay[FASTFALL].flush_per_stage, taken)", "real INITs"]
rn["site_pins"] = copy.deepcopy(oldn["site_pins"])
rn["site_pins"]["roles"] = sorted(set(rn["site_pins"]["roles"] + ["ua_i.I1 (z_ack) lo", "or3 pin lo"]))
new_row(rn)
e = relabel("bdc_muxn.uj_env_latency_req", "not_necessary",
            [L(N4N, "pass8", "not_necessary", "Mn3Wit's unit run, every join's feedback net 8, reset held to 11: S_J_X fails for every input (9 <= 6), the max form holds, the cell's conclusion holds; with muxn3_ok_staticN every run in the box at this point passes"),
             L(N4N, "pass8_values", "numbers"),
             L(N4N, "staticN_of_static", "lemma", "the shipped form implies the replacement"),
             L(N4N, "muxn3_ok_staticN", "sufficient", "the replacement's sufficiency")],
            "Bnx4 (B-necessity4.md, Necessity4MuxN): NOT necessary (box sense, as bd_mux.uj_env_latency_req); replacement "
            "bdc_muxn.uj_env_latency_req_max (sufficient). " + BIN_NOTE, old_ok=("sufficient",))
e["replacement"] = rn["id"]

e = relabel("bd_mux.uj_env_latency_ctl", "sufficient+necessary_at_boundary",
            [L(N4C, "claimC0", "sufficient", "ClaimC 0 = the shipped mux_ok_static"),
             L(N4C, "MuxStaticC", "definition"),
             L(N4C, "failC8", "counter_run", "N5.run 8 (6-tick ack wires, 1-tick control sender, 8-tick uj0 net): every MuxStatic field holds (S_J0_X included, 9 <= 11), S_J0_C fails by exactly 1, reset sequencing holds"),
             L(N4C, "claimC1_false", "counter_trace", "not ClaimC 1: z_req = 0 at 33 inside [25, 40); ctl_req's fall reaches the join at 29 while x_req is high and the net shows j0's rise only from 30: a one-tick runt"),
             L(N4C, "pass7", "non_vacuity", "a 7-tick net: the shipped theorem applies")],
            "Bnx4 (B-necessity4.md, Necessity4MuxC): S_J0_C weakened by 1 tick in the SHIPPED mux_ok_static's own hypothesis set is "
            "refuted by one run (the control return is the only path, so no max form). One parameter point, NOT an iff; S_J1_C by "
            "symmetry, not built. " + BIN_NOTE, old_ok=("sufficient",))
e["necessity_scope"] = "S_J0_C form only (S_J1_C not built), one parameter point (N5.run 8), binary '<=' at slack 1 (the strict form is 2 ticks from it)"

# ------------------------------------------------------------------ (2) Necessity5* (Bnx5)
N5A, N5D, N5P, N5L, N5F, N5M = ("Necessity5Arb", "Necessity5Delay", "Necessity5PipeRst", "Necessity5Link", "Necessity5Flink", "Necessity5Mem")
e = relabel("bd_arbcell.grant_skew", "exact",
            [L(N5A, "grant_skew_exact", "exact", "for every delay triple (L >= 1): no trace meeting the hypotheses has both grants high <-> |d6 - d5| <= L"),
             L(N5A, "formA_iff", "exact", "given form B: Excl <-> d6 <= d5 + L"),
             L(N5A, "formB_iff", "exact", "given form A: Excl <-> d5 <= d6 + L"),
             L(N5A, "formA_run", "counter_run", "an opposite-sense handover with request edges exactly L + 1 apart, built for every violating triple"),
             L(N5A, "formB_run", "counter_run"),
             L(N5A, "nonvacuous", "non_vacuity"),
             L(N5A, "bsx3_points", "numbers", "Bsx3's two points (L = 4) are instances")],
            "Bnx5 (B-necessity5.md, Necessity5Arb): EXACT over the whole parameter space of ArbBinary's transport model; supersedes "
            "Bsx3's 'necessary at the boundary, NOT an iff' above.", old_ok=("sufficient+necessary_at_boundary",))
e["exact_scope"] = ("ArbBinary's transport model of bd_arbcell: real INITs, one q loop delay L >= 1 to both grant LUTs' I2, grant arcs d5, d6, "
                    "H_INIT_SETTLED, H_REQ_SEP; iff for every delay triple. NOT covered: Kleene X on q, skew between the two I2 branches of "
                    "the q net, request routing skew, inertial / involution channels (bd_arbcell.bbm). bd_arbcell is not instantiated in gcd_hw.")
add_hyp(e, ["transport model (ArbBinary)", "H_INIT_SETTLED", "H_REQ_SEP", "one q loop delay to both I2 pins (no q-branch skew)"])

e = relabel("bd_arbcell.settled_exclusion", "exact",
            [L(N5A, "settled_iff", "exact", "with g1 reading qa and g2 reading qb: exclusion for every request vector <-> NOT (qa = 1 and qb = 0)"),
             L(N5A, "settled_overlap_needs_both", "lemma", "an overlap also needs r1 = r2 = 1")],
            "Bnx5 (Necessity5Arb): exact on its precondition. The structural fact holds exactly when the two grant LUTs cannot read "
            "different q values; that is what q-branch skew (not modelled) would break.", old_ok=("sufficient",))
e["inequality"] = ("structural (no inequality); precondition: both grant LUTs read the same q value. Exact: g1 && g2 = false for every request "
                   "vector iff NOT (g1 reads q = 1 while g2 reads q = 0) (settled_iff)")
e["exact_scope"] = ("Boolean, one evaluation of the two grant LUTs on the real INITs; the iff is over the q values the two LUTs read. The timed "
                    "q-branch skew that would make them differ is not modelled (the timed exclusion is bd_arbcell.grant_skew).")
add_hyp(e, ["H_SAME_Q (both grant LUTs read one q value; no q-branch skew)"])

# FASTRISE ack_flush: exact at DACK = 2, not necessary from DACK = 3; replacement Succ
af = BY["bd_delay[FASTRISE].ack_flush"]
sr = copy.deepcopy(af)
sr["id"] = "bd_delay[FASTRISE].ack_succ"
sr["catalogue_row"] = "none (Bnx5, formal/notes/B-necessity5.md)"
sr["obligation"] = ("the DACK OR line turns a node high phase [a, a + w) into ONE high stretch [a + alo, a + w + ahi) at the stage's I1 pin "
                    "(orn_hold_true's conclusion, what pipe_ctl consumes): Pulse")
sr["inequality"] = ("Succ: for every copy k of the DACK OR line except the slowest, some later copy k' has d(k) < d(k') <= d(k) + Won_b "
                    "(every copy but the slowest has a later copy at most Won_b behind it; for a uniform chain: each hop <= Won_b)")
sr["forms"] = [{"launch": "stage b node rise (line input)",
                "data_paths": [[{"kind": "line", "name": "dack", "edge": "rise=fall (point delays)", "path": "copy k' (the nearest later copy of k)",
                                 "spec": "path delay of copy k'", "lean_sym": "δ k'"}]],
                "request_paths": [[{"kind": "line", "name": "dack", "edge": "rise=fall (point delays)", "path": "copy k",
                                    "spec": "path delay of copy k", "lean_sym": "δ k"},
                                   copy.deepcopy(af["forms"][0]["request_paths"][0][0])]],
                "margin_ps": 0,
                "note": "one form per copy k except the slowest; k' is chosen per k (Succ is an exists over the later copies)"}]
sr["lean"] = [L(N5D, "pulse_iff", "exact", "point delays, width w >= 1: Pulse <-> Succ"),
              L(N5D, "pulse_of_succ", "sufficient"),
              L(N5D, "succ_of_pulse", "necessary"),
              L(N5D, "succ_mono", "lemma", "Succ at a width implies Succ at every longer width (Won_b is a lower bound of the high width)"),
              L(N5D, "Succ", "definition"), L(N5D, "Pulse", "definition"),
              L(N5D, "flush_succ", "lemma", "the shipped H_ACK_FLUSH implies Succ"),
              L(N5D, "dack3_clean", "non_vacuity", "the real DACK = 3 chain (BUF 2'h2, FR_SIDE 4'hE, all t), unit hops, width 1: Succ holds, one pulse [11, 14)"),
              {"file": "formal/lean/Formal/Cells/PipeTimedN.lean", "name": "orn_hold_true", "role": "context", "note": "Pulse is its conclusion"}]
sr["exactness"] = "exact"
sr["exact_scope"] = ("line level, POINT delays (one corner, transport), one high pulse of width w >= 1: Pulse <-> Succ (pulse_iff). NOT covered: "
                     "window (non-point) delays (Succ's sufficiency over windows is NOT proved: with windows, evaluate the shipped "
                     "H_ACK_FLUSH, bd_delay[FASTRISE].ack_flush, which is sufficient there); the pipe level: pipe_ctl consumes orn_hold_true's "
                     "conclusion (= Pulse), but no PipeTimedN theorem takes Succ as its hypothesis, and no pipe-level run with the glitch exists")
sr["exactness_note"] = ("Bnx5 (B-necessity5.md, Necessity5Delay): the exact line condition bounds consecutive copy gaps, not the total spread. "
                        "Replacement of bd_delay[FASTRISE].ack_flush for DACK >= 3 (gcd_hw's DACK placeholder is 6, tightened per route 0-5).")
sr["hypotheses"] = ["point delays (one corner, transport)", "one high pulse, width w >= 1"]
sr["rule"] = {"rule": "none", "verdict": "none", "detail": "UNCHECKED"}
new_row(sr)
e = relabel("bd_delay[FASTRISE].ack_flush", "not_necessary",
            [L(N5D, "flush_succ", "sufficient", "H_ACK_FLUSH implies Succ (the shipped direction, point delays)"),
             L(N5D, "two_exact", "exact", "DACK = 2 (two copies): Pulse <-> Flush, the shipped form is exact"),
             L(N5D, "flush_not_necessary", "not_necessary", "three copies, delta = (3, 2, 1), w = 1: Flush fails by 1 and the output is one clean pulse"),
             L(N5D, "dack3_clean", "counter_run", "real INITs, all t: DACK = 3, unit hops, one pulse [11, 14) out"),
             L(N5D, "dack3_viol", "numbers", "H_ACK_FLUSH off by exactly 1"),
             L(N5D, "dack2_glitch", "counter_trace", "DACK = 2 boundary: buffer 1 + chain hop 2 vs tap 1, w = 1: two pulses, low at 12"),
             L(N5D, "dack2_viol", "numbers", "H_ACK_FLUSH off by exactly 1"),
             L(N5D, "dack2_ok", "non_vacuity", "the same line at w = 2: Flush and one pulse"),
             L(N5D, "Flush", "definition")],
            "Bnx5 (B-necessity5.md, Necessity5Delay), line level, point delays: H_ACK_FLUSH is EXACT for DACK = 2 (two_exact) and NOT "
            "necessary for DACK >= 3 (flush_not_necessary, dack3_clean); the exact condition is Succ (bd_delay[FASTRISE].ack_succ, "
            "pulse_iff). Pipe-level consequence of a glitch NOT examined (no PipeTimedN run).", old_ok=("sufficient",))
e["replacement"] = sr["id"]
e["necessity_scope"] = ("line level, point delays: DACK = 2 exact (two_exact; boundary run dack2_glitch); DACK >= 3 not necessary (dack3_clean). "
                        "With window delays the shipped form stays the proved sufficient one (the replacement's window sufficiency is not proved)")

e = BY["bd_pipe.rst_lines"]
add_lean(e, [L(N5P, "ctlA0", "sufficient", "CtlClaimA 0 0 = PipeTimedN.nodes_clean"),
             L(N5P, "dack_false", "counter_trace", "not CtlClaimA 1 0: the DACK term L_b.hi + ahi_b <= R weakened by 1"),
             L(N5P, "guard_false", "counter_trace", "not CtlClaimA 0 1: the guard term Ag_b <= R weakened by 1"),
             L(N5P, "dack_viol", "numbers", "L1.hi + ahi1 = R + 1"),
             L(N5P, "guard_viol", "numbers", "Ag 1 = R + 1"),
             L(N5P, "run_live", "counter_run", "stage 0 rises at 6 instead of 5; the nominal run shifted by one tick, for ever")])
e["necessity_scope"] = ("terms: all four PipeTimedN terms are necessary at the boundary, one parameter point each, binary '<=' (the loop terms' strict "
                        "+1 not addressed): the loop term L_i.hi + wh_i (+1) <= R (H_RST_LONG; Necessity3PipeCtl.long_false, N = 1; also "
                        "NecessityReset.c2n_box_exact), the request-line term L(b-1).hi + Rq_b.hi <= R (Necessity3PipeCtl.lines_false, N = 2), "
                        "the DACK term L_b.hi + ahi_b <= R and the guard term Ag_b <= R (Necessity5PipeRst.dack_false, guard_false; two-stage "
                        "Wit run, real bd_c2n INIT, R = 4). The per-pin (6g) H_RST_SEL terms (PipePerPin; the row's representative form) have "
                        "no necessity result")
note_append(e, "Bnx5 (B-necessity5.md, Necessity5PipeRst): the DACK and guard terms are now necessary at the boundary too (a stray ack at "
               "release costs a tick in these runs, it does not corrupt); the row stays 'sufficient' because its representative per-pin "
               "H_RST_SEL form has no necessity result.")
LOG.append("bd_pipe.rst_lines: stays sufficient; necessity_scope: all four PipeTimedN terms boundary-tight (H_RST_SEL open)")

LINK_SCOPE = ("binary '<=' at guard 0, one parameter point per rule (a whole bd_link_dc stage, every LUT its real INIT as a transport gate, one corner, "
              "four-phase environment, feedback-pin arc 1); the strict +1 for guard >= 1 not addressed; guards > 0, wider windows and "
              "H_LT_FALL_K/L themselves NOT covered")
e = relabel("bd_link_dc.rule_K_corrected", "sufficient+necessary_at_boundary",
            [L(N5L, "Claim", "definition"),
             L(N5L, "claim0", "sufficient", "Claim 0 0 = RulesKL.dc_capture's hypothesis set"),
             L(N5L, "k1_false", "counter_trace", "not Claim 1 0: Bk's counter_K run, RuleK' off by exactly 1, RuleL' met: the bit sees D = 1 from 8 and holds 0 at 11"),
             L(N5L, "k_viol", "numbers"), L(N5L, "k_L_ok", "numbers", "RuleL' holds on the K run"),
             L(N5L, "witness", "non_vacuity", "the K stage with a 2-tick loop meets both corrected rules and captures")],
            "Bnx5 (B-necessity5.md, Necessity5Link): necessary at the boundary in dc_capture's own hypothesis set. NOT an iff.", old_ok=("sufficient",))
e["necessity_scope"] = LINK_SCOPE
e = relabel("bd_link_dc.rule_L_corrected", "sufficient+necessary_at_boundary",
            [L(N5L, "Claim", "definition"),
             L(N5L, "claim0", "sufficient", "Claim 0 0 = RulesKL.dc_capture's hypothesis set"),
             L(N5L, "l1_false", "counter_trace", "not Claim 0 1: Bk's counter_L run with the sender re-raising its request at 4 and req_in -> ub 3: RuleK' holds with equality, RuleL' off by exactly 1, the bit holds 0 at 9"),
             L(N5L, "l_stage", "counter_run"), L(N5L, "l_viol", "numbers"), L(N5L, "l_k_ok", "numbers", "RuleK' holds on the L run"),
             L(N5L, "witness", "non_vacuity")],
            "Bnx5 (B-necessity5.md, Necessity5Link): necessary at the boundary in dc_capture's own hypothesis set. NOT an iff.", old_ok=("sufficient",))
e["necessity_scope"] = LINK_SCOPE

e = relabel("bd_flink.qfb_first", "sufficient+necessary_at_boundary",
            [L(N5F, "QClaim", "definition"),
             L(N5F, "q0", "sufficient", "QClaim 0 = ConstraintsMore.flink_qfb_first_timed"),
             L(N5F, "q1_false", "counter_trace", "not QClaim 1: every other hypothesis holds (A = B = 0, Tq = 6, Td = 5, Toff2 = 7, Tnext = 9), H_QFB_FIRST_T is 9 <= 8 + 1"),
             L(N5F, "q_viol", "numbers"),
             L(N5F, "f_runt", "numbers", "done rises at 6, falls at 8, period 3 for ever"),
             L(N5F, "f_clean", "context", "the clean twin at fhi = 2")],
            "Bnx5 (B-necessity5.md, Necessity5Flink): the flink twin of mlink's qfb_counter in Claim form; necessary at the boundary, "
            "Lean '<=' form (one parameter point). The JSON's strict +1 is not addressed: the refuted point is 2 ticks from the JSON form.",
            old_ok=("sufficient",))
e["necessity_scope"] = "binary '<=' (general Lean form H_QFB_FIRST_T), one parameter point; the strict +1 (Bs, latch_facts) not addressed"

MEM_SCOPE = ("MemPort event model (H_SETUP_LINE, H_CO_LINE, H_FOUR_PHASE_ENV; RAMB18E1 datasheet numbers as constants; the BRAM is NOT a gate "
             "model): the iff is over every port with the same line bounds and datasheet numbers ('Same'), whose fastest access attains the "
             "bound. NOT covered: BRAM behaviour on violation, payload route skew at the RAM pins")
for rid, nm, txt in (("bd_mem.setup", "setup_exact", "(every port meets tPay + tSU <= tClkR) <-> tSU <= dsLo"),
                     ("bd_mem.hold", "hold_exact", "(every port meets tClkR + tHD <= tPayNext) <-> tHD <= dcLo + dsLoF + dcLoF")):
    e = relabel(rid, "exact", [L(N5M, nm, "exact", txt), L(N5M, "fast_same", "lemma", "the fastest port has the same numbers"),
                               L(N5M, "nonvacuous", "non_vacuity")],
                "Bnx5 (B-necessity5.md, Necessity5Mem): exact in the event model.", old_ok=("sufficient",))
    e["exact_scope"] = MEM_SCOPE
e = relabel("bd_mem.rdata_before_ack", "exact",
            [L(N5M, "rdata_exact", "exact", "(every port meets tClkR + tCO <= tAckR) <-> tCO <= dcLo"), L(N5M, "nonvacuous", "non_vacuity")],
            "Bnx5 (Necessity5Mem): the tCO <= dcLo part is exact in the event model; the added H_RDATA_ROUTE skew term is not in the Lean.",
            old_ok=("sufficient",))
e["exact_scope"] = ("the tCO <= dcLo part only (" + MEM_SCOPE + "); the consumer's rdata vs ack route-skew term (H_RDATA_ROUTE) the row adds is "
                    "NOT in the Lean: with it the row is sufficient only")
ch = BY["bd_mem.clk_high_width"]
cr = copy.deepcopy(ch)
cr["id"] = "bd_mem.clk_high_width_exact"
cr["catalogue_row"] = "none (Bnx5, formal/notes/B-necessity5.md)"
cr["obligation"] = "RAM clock high width vs tPWH, exact form: the clock high phase is measured from the clock's own rise"
cr["inequality"] = "tPWH <= dcLo + dsLoF"
cr["forms"] = [{"launch": "RAM clock rise",
                "data_paths": [[copy.deepcopy(ch["forms"][0]["data_paths"][0][0])]],
                "request_paths": [[copy.deepcopy(ch["forms"][0]["request_paths"][0][1]), copy.deepcopy(ch["forms"][0]["request_paths"][0][2])]],
                "margin_ps": 0}]
cr["lean"] = [L(N5M, "clk_high_exact", "exact", "(every port meets tClkR + tPWH <= tClkF) <-> tPWH <= dcLo + dsLoF"),
              L(N5M, "clk_high_tight", "sufficient", "on every port the high phase is at least dcLo + dsLoF"),
              L(N5M, "clk_low_exact", "context", "the clock-low twin, exact: tPWL <= dcLoF + dsLo (no row of its own; ConstraintsMore.clk_low_ok is cited on bd_mem.clk_high_width)"),
              L(N5M, "clk_high_not_necessary", "non_vacuity", "port p0 meets the exact form")]
cr["exactness"] = "exact"
cr["exact_scope"] = MEM_SCOPE
cr["exactness_note"] = ("Bnx5 (B-necessity5.md, Necessity5Mem): replacement of bd_mem.clk_high_width. The shipped condition is conservative by the "
                        "setup line's rise spread dsHi - dsLo.")
new_row(cr)
e = relabel("bd_mem.clk_high_width", "not_necessary",
            [L(N5M, "clk_high_not_necessary", "not_necessary", "dsLo = 1, dsHi = 3, dcLo = dsLoF = 1, tPWH = 2: the shipped form fails and every port meets tPWH"),
             L(N5M, "clk_high_tight", "lemma"),
             L(N5M, "clk_high_exact", "context", "the replacement's iff")],
            "Bnx5 (B-necessity5.md, Necessity5Mem): NOT necessary; replacement bd_mem.clk_high_width_exact (tPWH <= dcLo + dsLoF, exact).",
            old_ok=("sufficient",))
e["replacement"] = cr["id"]

# the reclassifications from existing Lean (B-necessity5.md table)
e = relabel("bd_merge.reset_first", "not_necessary", [],
            "Bj6 (B-necessity5.md table, reclassification from existing Lean, no new Lean): label follows the Bsx analysis above: not "
            "necessary AS WRITTEN; the H_RST_EARLY form (form 1) is replaced by H_NO_RETURN, cell level (early_request_ok, one bd_c2); "
            "the loop terms (form 0) stay required (necessary at the instance, NecessityReset.c2_box_exact); the wire terms are not "
            "analysed. A merge-level theorem with H_NO_RETURN in place of H_RST_EARLY is NOT proved (merge_timing_of_static takes "
            "H_RST_EARLY).", old_ok=("sufficient",))
e["replacement"] = "H_NO_RETURN"
e["replacement_scope"] = ("replaces form 1 (H_RST_EARLY) only; form 0 (loop terms H_RST_LONG, strict, and the wire terms) is still required: a "
                          "checker evaluates form 0 AND H_NO_RETURN")
e = relabel("gcd_rig.token_static", "structural", [],
            "Bj6 (B-necessity5.md table): 'structural': decided on the elaborated netlist, no inequality, nothing to weaken by 1.",
            old_ok=("sufficient",))

# ------------------------------------------------------------------ (3) KleeneWin (Bxw): the +1 is H_X_UNIFORM; per-edge windows; H_FB_WIN
KW = "KleeneWin"
XW_COMMON = ("Bxw (B-kleene-win.md, KleeneWin): this +1 is H_X_UNIFORM at w = a + c = 1 tick on every edge (steer_win_uniform recovers the "
             "uniform form); with per-edge windows (H_X_EDGE) the exact term is c(edge that must come first) + a(edge that must come after), "
             "and the uniform '+1, strict' is then neither necessary nor sufficient (steer_split_matters, steer_ct_split_x). Sufficient "
             "without the split: +W under H_W_BOUND (c_e + a_l <= W for every race pair). W is UNMEASURED (no prjxray/SDF transition data; "
             "board test XW-1 in B-kleene-win.md); 1 tick is the grid minimum.")
XW_FB = (" Own-feedback race: per-edge exact form cf + dlmax + dwmax + ar <= dlmin + E (cel_env_iff, any Facts cycle); with the feedback "
         "pin's own window wq (H_FB_WIN) it is cf + dlmax + dwmax + wq + ar <= dlmin + E (cel_env_win_iff, clean_iffW): the form here "
         "assumes wq = 0 (H_FB_PURE, loopW_of_loop). On the real bd_c2 INIT, CElemStrict's strict_clean point is a hazard at wq = 1 "
         "(c2_fbwin_hazard).")
XW_SEL = {"steer_strict_K": ("steer_win_exact", "steer_witness_W"), "join_strict_K": ("join_win_exact", "join_witness_W"),
          "muxn_edges_K at a + c = 1": ("muxn_win_exact", None)}
nxw = nfb = 0
for e in C:
    st = e.get("strict")
    if not (st and st.get("margin_added_ps")):
        continue
    src, back = st.get("source", ""), st.get("backing", "")
    refs = [L(KW, "steer_split_matters", "context", "with width-1 windows on every edge, binary equality can be safe and a 1-tick-strict margin unsafe: the +1 comes from H_X_UNIFORM, not from the cells"),
            L(KW, "steer_win_uniform", "reduction", "H_X_UNIFORM gives back the uniform +(a + c) form")]
    txt = XW_COMMON
    if src.startswith("Bkx"):
        w, wit = XW_SEL[back]
        refs.append(L(KW, w, "kleene", "per-edge windows (H_X_EDGE): exact with + c(first) + a(after)"))
        if wit:
            refs.append(L(KW, wit, "non_vacuity", "a different split on every edge, X on every window"))
        if w == "steer_win_exact":
            refs.append(L(KW, "steer_ct_split_x", "counter_trace", "1-tick-strict in binary-edge times, opposite split on the setup pair: the unselected O5 reads X at 1300"))
        txt += f" Per-edge iff for this row: {w}."
    elif e["id"].startswith("bd_latch["):
        refs += [L(KW, "latch_win_exact", "kleene", "per-edge windows: setup_pulse + (cOn + aOff), setup_data + (cD + aOff), hold + (cOff + aN); aOn drops out"),
                 L(KW, "latch_witness_W", "non_vacuity"),
                 L(KW, "latch_fbwin_iff", "exact_inner", "the odd bit's own loop with a feedback window wq: + wq")]
        txt += " Per-edge iff for this row: latch_win_exact; the latch loop with its own feedback window: latch_fbwin_iff (+wq)."
        add_hyp(e, ["H_FB_WIN: wq = 0 assumed (latch loop; = H_FB_PURE)"])
        nfb += 1
    else:
        refs += [L(KW, "cel_env_iff", "exact_inner", "per-edge X windows, any Facts cycle: cf + dlmax + dwmax + ar <= dlmin + E"),
                 L(KW, "cel_env_win_iff", "exact_inner", "with H_FB_WIN: + wq"),
                 L(KW, "clean_iffW", "exact_inner"),
                 L(KW, "c2_fbwin_hazard", "context", "bd_c2 real INIT: the strict_clean point (s = 421, D = 420) is a hazard at wq = 1 (clean at 422: c2_fbwin_clean)"),
                 L(KW, "loopW_exists", "non_vacuity")]
        txt += XW_FB
        add_hyp(e, ["H_FB_WIN: wq = 0 assumed (= H_FB_PURE)"])
        nfb += 1
    st["x_window"] = txt
    if not any(h.startswith("H_X_UNIFORM") for h in e.get("hypotheses", [])):
        add_hyp(e, ["H_X_UNIFORM (the +1: one X window of width 1 tick, same split, on every edge)"])
    add_lean(e, refs)
    if e["exactness"] == "exact":
        add_scope(e, "exact_scope", "Bxw: exact WITH the +1 only under H_X_UNIFORM at w = 1 (and wq = 0 on a feedback pin); with per-edge windows "
                  "the exact form is KleeneWin's (strict.x_window)")
    nxw += 1
LOG.append(f"KleeneWin: strict.x_window + H_X_UNIFORM hypothesis on {nxw} strict rows; H_FB_WIN (wq = 0) recorded on {nfb} own-feedback / latch-loop rows")

# ------------------------------------------------------------------ (4) KleenePess (Bpess): dependence on H_KLEENE_LUT being hazard-free
KP = "KleenePess"
PESS_HEAD = ("Bpess (B-kleene-pess.md, KleenePess): below H_KLEENE_LUT (the optimistic, hazard-free LUT model) a LUT output is definite v "
             "iff the Kleene closure is v AND every pin that reads X sits on a mux level that passes v (lutP_definite). ")
def kdep(e, needs, basis, refs, inferred=False):
    e["kleene_dependence"] = {"needs": needs, "basis": PESS_HEAD + basis, "inferred": inferred}
    add_lean(e, [L(KP, "lutP_definite", "context", "definite output v <-> closure v and every X pin passes v")] + refs)
nk = Counter()
for e in C:
    st = e.get("strict")
    kleene = any(h.startswith("H_KLEENE_LUT") or h.startswith("H_MUX_KLEENE") for h in e.get("hypotheses", [])) or \
        (st and st.get("margin_added_ps")) or e["id"] == "bd_link.stage"
    if not kleene:
        continue
    rid, back = e["id"], (st or {}).get("backing", "")
    if rid.startswith("bd_steer."):
        kdep(e, "pass0", "steer's +w iff survives weak1 verbatim (every definite spec value reached with an X pin is 0); under weak0 / strict it fails on steer_witness_K's own traces.",
             [L(KP, "steer_edges_weak1", "context", "the +w iff under weak1 (an NMOS-only tree)"),
              L(KP, "steer_fails_M", "counter_trace", "any policy without pass-0: the unselected O5 reads X at 1299"),
              L(KP, "steer_witness_weak1", "non_vacuity")])
    elif rid.startswith("bd_mux.bundled_s_"):
        kdep(e, "both", "the join's +w iff fails under every pessimistic model: weak1 (the selected join must restore 1 with its feedback reading X, C2(1,1,X)) and weak0 (the unselected join's 0).",
             [L(KP, "join_fails_weak1", "counter_trace"), L(KP, "join_fails_weak0", "counter_trace")])
    elif rid.startswith("bdc_muxn.s_"):
        kdep(e, "both", "bdc_muxn was NOT re-run; by lutP_definite the selected join's hold of 1 needs pass-1 and the unselected joins' 0 needs pass-0, as for bd_mux.",
             [], inferred=True)
    elif rid.startswith("bd_latch[") or rid == "bd_link.stage":
        kdep(e, "both", "latch box: the token whose value passes keeps the sufficient half (latch_pin_ok_M); the other token fails (latch_fails_M: q = X is a model run where Kleene's box is safe); strict loses both." +
             (" The stage's controller restores both values (c2nM_restore)." if rid == "bd_link.stage" else ""),
             [L(KP, "latch_pin_ok_M", "context", "sufficient half for a passing token value"),
              L(KP, "latch_fails_M", "counter_trace", "a non-passing token value: unsafe where Kleene is safe"),
              L(KP, "oddM_hold", "lemma", "ODD hold with X on d keeps q iff pass q (or d definite)")] +
             ([L(KP, "c2nM_restore", "lemma")] if rid == "bd_link.stage" else []))
    elif rid == "bd_latch_rst.reset":
        kdep(e, "pass(reset value)", "RST0 under an X pin needs pass-0, RST1 needs pass-1 (or no X pin).",
             [L(KP, "rstM_reset", "lemma")])
    elif rid.endswith(".reset_width") or rid == "design.rst_hold":
        kdep(e, "pass(reset value)", "a reset that forces 0 with an X pin needs pass-0 (c2M_rst for bd_c2); the other C-element variants follow the same (pin, value) rule.",
             [L(KP, "c2M_rst", "lemma")], inferred=not rid.startswith("bd_c2."))
    elif back.startswith("latch_facts"):
        kdep(e, "both", "the race's clean conclusion is a definite latch value held through its own loop; holding q with an X pin needs pass q, and the row covers both values.",
             [L(KP, "oddM_hold", "lemma"), L(KP, "oddM_transp", "lemma")], inferred=True)
    else:
        kdep(e, "both", "the own-feedback race's clean conclusion is a definite restore through the feedback pin while it reads X: c2M_restore (bd_c2: definite iff a = b != X and pass a; C2(1,1,X) = 1 iff p1), c2nM_restore (bd_c2n); the row's races cover both output values. The composed cells are not re-run under the models.",
             [L(KP, "c2M_restore", "lemma"), L(KP, "c2M_11x", "lemma"), L(KP, "c2nM_restore", "lemma")],
             inferred=not (rid.startswith("bd_c2.") or rid.startswith("bd_c2n.")))
    nk[e["kleene_dependence"]["needs"]] += 1
LOG.append(f"KleenePess: kleene_dependence on {sum(nk.values())} rows: {dict(nk)}")

hk = [h for h in doc["hypotheses_not_inequalities"] if h["id"] == KB_HYP_ID][0]
hk["statement"] += (" Bxw (KleeneWin): H_X_UNIFORM is an assumption; with per-edge windows (H_X_EDGE) each race gains c(first) + a(after) "
                    "exactly, and the feedback pin's own window (H_FB_WIN) adds wq. Bpess (KleenePess): H_KLEENE_LUT is the top of a bracket "
                    "strict <= any per-pin pass policy (weak1 = NMOS-only tree, weak0, retention) <= lutK (bracket); every safety / exclusion "
                    "result ('never a definite wrong or double value') survives every model below it (transfer, excl_M, arb_acks_safe); every "
                    "definite-output / hold / restore / reset result needs pass(v) at its X pins (lutP_definite). Per row: kleene_dependence.")
hk["check"] += ("; Bpess board test: the runt-flag pass matrix (6 pins x 2 values, FDCE async flag, B-kleene-pess.md section 5) decides which "
                "point of the bracket silicon sits at; XW-1 (B-kleene-win.md) bounds the window width")
add_lean(hk, [L(KW, "steer_win_exact", "kleene", "per-edge windows"), L(KW, "steer_split_matters", "counter_trace", "the uniform +1 is not a cell property"),
              L(KW, "cel_env_win_iff", "exact", "H_FB_WIN on any Facts cycle"),
              L(KP, "bracket", "bound", "strict <= any policy <= lutK, any tree order"),
              L(KP, "lutP_definite", "exact"), L(KP, "strict_iff", "exact"), L(KP, "transfer", "lemma"),
              L(KP, "excl_M", "context", "arbiter exclusion survives every model"),
              L(KP, "arb_run_le", "lemma"), L(KP, "arb_acks_safe", "context", "network ack exclusion survives every LUT semantics below Kleene"),
              L(KP, "bracket_strict_witness", "non_vacuity")])
hf = [h for h in doc["hypotheses_not_inequalities"] if h["id"] == "H_LUT_FIFO / H_PIN_FIFO / H_TREE_FIFO"][0]
hf["check"] += ("; Bpess: the NMOS-only tree is KleenePess's weak1 policy (pass-1 lost under an X select); the (pin, value) requirement list "
                "is lutP_definite")
add_lean(hf, [L(KP, "lutP_definite", "context"), L(KP, "lutP_eq_lutM", "lemma", "the model output does not depend on the tree or pin order")])

# ------------------------------------------------------------------ (5) OnGcdArbKappaTight (Bkx19): the binding row
GT, GTA = "OnGcdArbKappaTight", "OnGcdArbKappaTightA"
e = BY["bd_arbiter.rt1b"]
e["corner"]["kappa"]["results"].append(
    "Bkx19 (B-gcd-arb-kappa-tight.md, OnGcdArbKappaTight + the Mathlib bridge OnGcdArbKappaTightA): the binding row (seed 3 merge12.uarb1, "
    "RT1b server-free, lit, one whole-fs delay per arc) is SAFE for kappa <= 33176.932320/749546 ~ 0.0442627 (rt1b_safe, A_rt1b_safe) and "
    "has a violating realization for kappa >= 33176.932321/749546 (rt1b_unsafe, A_rt1b_unsafe): the threshold kappa_ex (irrational, "
    "kex_bracket; interior corner c ~ 5.1e-6) is bracketed to 1.3e-12. The whole kappa_ex - kappa* (~3.9e-6) is the 1 fs grid. Gate level "
    "(rt1b_gate_unsafe, rt1b_gate_safe, 7j's model, real INITs, all t): the same bracket, BUT the overlap needs smin = 0, wa0s = 0, qr = 0, "
    "cq = 0, i.e. zero server, zero A0 route to ustate and zero ustate O6 arc, which the server-free form allows. With those credited as "
    "corner-model arcs this arbiter is the RT1bs row (lit min 0.651) and the design's lit minimum is 0.0802 (seed 2 merge3.uarb1 h21, "
    "lit_srv_min): 0.0443 is the server-free form's number, not a gate-level threshold of the routed design. Lit safety carries "
    "H_SPREAD_CORRELATED (the prjxray within-corner spread is die-wide, carried by the shared corner; only the residual scatter is "
    "bounded by kappa: spread_correlated_safe); under H_SPREAD_INDEP (the cons arcs) the row fails at EVERY kappa, kappa = 0 included, "
    "by 46.8 ps (spread_indep_fails, spread_indep_not_safe). Every other row keeps OnGcdArbKappa's gap (<= 1.8e-5). Board test T_SPREAD "
    "in the note. Arc numbers: probe Bar's extraction (UNTRUSTED; routes not on disk).")
add_lean(e, [L(GT, "rt1b_safe", "corner"), L(GT, "rt1b_unsafe", "corner"), L(GT, "rt1b_not_allOK", "corner"),
             L(GT, "kex_bracket", "numbers"), L(GT, "kS_kU_inside", "numbers", "kappaS, kappaU lie inside OnGcdArbKappa's (kappa*, kappa_u)"),
             L(GT, "allOK_of_chk", "corner", "the finite certificate check is sound for every rational corner"),
             L(GT, "rt1b_gate_safe", "corner"), L(GT, "rt1b_gate_unsafe", "corner", "needs smin = wa0s = qr = cq = 0"),
             L(GT, "SU_overlap", "numbers", "g1 and g2 both high at 374043 fs"),
             L(GT, "H_SPREAD_CORRELATED", "definition"), L(GT, "H_SPREAD_INDEP", "definition"),
             L(GT, "spread_correlated_safe", "corner"), L(GT, "spread_indep_fails", "counter_trace"), L(GT, "spread_indep_not_safe", "counter_trace"),
             L(GT, "cons_rows_k0", "numbers", "the other four cons rows that fail at kappa = 0"),
             L(GT, "rt1b_safe_nonvacuous", "non_vacuity"), L(GT, "spread_nonvacuous", "non_vacuity"),
             L(GTA, "scat_iff", "reduction", "the restated Scat is CornerNat's"),
             L(GTA, "A_rt1b_safe", "corner", "on OnGcdArbKappa's own objects"), L(GTA, "A_rt1b_unsafe", "corner"),
             L(GTA, "A_gap_closed", "numbers"), L(GTA, "A_rt1b_gate_unsafe", "corner")])
add_hyp(e, ["H_SPREAD_CORRELATED (lit reading)", "server-free form (smin, A0 route to ustate, ustate O6 not credited)"])
LOG.append("bd_arbiter.rt1b: corner.kappa.results + OnGcdArbKappaTight (binding row bracketed to 1.3e-12; server-free caveat; H_SPREAD_CORRELATED)")
for rid in GK_ROWS:
    if rid == "bd_arbiter.rt1b":
        continue
    BY[rid]["corner"]["kappa"]["results"].append(
        "Bkx19: every lit verdict here carries H_SPREAD_CORRELATED (OnGcdArbKappaTight); only the design's binding row (bd_arbiter.rt1b) is "
        "bracketed to 1.3e-12, this row keeps OnGcdArbKappa's gap.")
    add_hyp(BY[rid], ["H_SPREAD_CORRELATED (lit reading)"])
hkap = [h for h in doc["hypotheses_not_inequalities"] if h["id"] == KAPPA_HYP_ID][0]
hkap["statement"] += (" Bkx19: a 'lit' reading (each arc's endpoints at prjxray FAST_MIN / SLOW_MAX) is safe at small kappa only under "
                      "H_SPREAD_CORRELATED (the within-corner min..max spread is die-wide and carried by the shared corner; kappa bounds the "
                      "residual); under H_SPREAD_INDEP (each arc anywhere in its own within-corner range) gcd_hw's binding arbiter row fails "
                      "at every kappa.")
hkap["check"] += "; T_SPREAD (B-gcd-arb-kappa-tight.md): fit one corner per die on >= 30 path pairs, residuals |rho| <= kappa decides lit vs cons"
add_lean(hkap, [L(GT, "H_SPREAD_CORRELATED", "definition"), L(GT, "H_SPREAD_INDEP", "definition"),
                L(GT, "spread_correlated_safe", "corner"), L(GT, "spread_indep_not_safe", "counter_trace")])

# ------------------------------------------------------------------ conventions, provenance
cv = doc["conventions"]
cv["exactness"] += (" Bj6: structural (a fact decided on the netlist or by construction, with no inequality to weaken: gcd_rig.token_static).")
cv["replacement"] += (" Bj6: optional replacement_rows lists every constraint id that together replaces the entry (bd_mux.uj_env_latency_req -> "
                      "one max-form row per join); optional replacement_scope says which forms the replacement replaces when the others stay "
                      "required (bd_merge.reset_first: H_NO_RETURN replaces the H_RST_EARLY form only).")
cv["strictness"] += (" Bj6 (KleeneWin, Bxw): every strict +1 is H_X_UNIFORM at w = 1 (strict.x_window and the row's hypotheses say so); "
                     "with per-edge windows the exact term is c(first) + a(after), and the own-feedback rows also assume wq = 0 (H_FB_WIN). "
                     "The +1 is not a cell property (steer_split_matters); W is unmeasured.")
cv["kleene_dependence"] = ("optional (Bj6, KleenePess): on every row whose theorems use a K3 LUT model (H_KLEENE_LUT, H_MUX_KLEENE, or a "
                           "strict +1): what its conclusion needs from the LUT below H_KLEENE_LUT. needs = pass0 | pass1 | both | "
                           "pass(reset value) | none: the (pin, value) pairs that must pass for the definite output the row concludes "
                           "(lutP_definite). Safety / exclusion results ('never a definite wrong or double value') need nothing "
                           "(transfer, excl_M, arb_acks_safe); the binary rows use no K3 model and carry no field. inferred = true: by "
                           "lutP_definite's rule, the cell not re-run under the pessimistic models.")
doc["produced_by"] = (doc["produced_by"].rstrip() +
    " Updated by probe Bj6 (2026-10-29) from B-necessity4.md (Necessity4Mux*: uj_env_latency_req rows not_necessary, max-form replacement "
    "rows, uj_env_latency_ctl boundary), B-necessity5.md (Necessity5*: grant_skew, settled_exclusion, bd_mem setup/hold/rdata exact, "
    "FASTRISE ack_flush and bd_mem.clk_high_width not_necessary with exact replacement rows, rst_lines / bd_link_dc / bd_flink boundary, "
    "bd_merge.reset_first and gcd_rig.token_static reclassified), B-kleene-win.md (strict.x_window, H_X_UNIFORM / H_FB_WIN), "
    "B-kleene-pess.md (kleene_dependence) and B-gcd-arb-kappa-tight.md (rt1b bracketed, H_SPREAD_CORRELATED); the 'probe Bj6' section "
    "of cell_constraints.bj5.py.")

json.dump(doc, open(OUT, "w"), indent=1)
for x in LOG:
    print(x)
