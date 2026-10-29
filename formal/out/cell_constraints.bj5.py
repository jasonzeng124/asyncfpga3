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

# ================================================================== probe Bj7 (2026-10-29)
# Third Bj pass of the day. Applies, from today's committed notes (and JOURNAL-B.md progress 12:10 / 12:50):
#   B-arb-kappa-exact.md (OnNetlistArbKappaExact), B-gcd-arb-kappa-srv.md (OnGcdArbKappaSrv),
#   B-self-audit4.md (SelfAuditB7: label / note fixes), B-contract-bridge.md (ContractBridge: H_ARB_EXCL),
#   B-lutfb-bridge2.md (LutFbBridge2: H_SEL_STABLE, H_PWR_SRC).
# Every name cited below is declared in the cited file (the validator greps each one).
LOG.append("---- probe Bj7")
KX, SRV, SA7, CB, FB2 = "OnNetlistArbKappaExact", "OnGcdArbKappaSrv", "SelfAuditB7", "ContractBridge", "LutFbBridge2"

# ------------------------------------------------------------------ (1) exact link_arb A0-fork thresholds (Bkx18)
KEX = {1: {("s1", "cons"): "0.2954922", ("s2", "cons"): "0.3356388", ("s3", "cons"): "0.3109273", ("s4", "cons"): "0.2080708",
           ("s1", "lit"): "0.4784366", ("s2", "lit"): "0.5481793", ("s3", "lit"): "0.5379863", ("s4", "lit"): "0.4148922"},
       2: {("s1", "cons"): "0.1806787", ("s2", "cons"): "94/325 = 0.2892308", ("s3", "cons"): "0.2440256", ("s4", "cons"): "0.2824745",
           ("s1", "lit"): "0.4011245", ("s2", "lit"): "0.4963581", ("s3", "lit"): "0.4593934", ("s4", "lit"): "0.4917064"}}
for k in (1, 2):
    e = BY[f"bd_arbiter.a0_fork_client{k}"]
    kap = e["corner"]["kappa"]
    assert kap["results"][0].startswith("link_arb (4 routed seeds), A0 fork"), k
    cases = [f"{s} {r} {KEX[k][(s, r)]}" for r in ("cons", "lit") for s in ("s1", "s2", "s3", "s4")]
    rat = (" s2 cons is rational (94/325), attained at the fast corner: kappa >= 94/325 is unsafe with one fixed fast-corner "
           "assignment; the other 7 are irrational (root of an explicit integer quadratic P_X, discriminant not a square), approached "
           "only at an interior corner that moves with kappa and never attained, so safe <-> kappa < kappa_ex <-> kappa <= kappa_ex."
           if k == 2 else
           " All 8 are irrational (root of an explicit integer quadratic P_X, discriminant not a square), approached only at an interior "
           "corner that moves with kappa and never attained, so safe <-> kappa < kappa_ex <-> kappa <= kappa_ex.")
    aud = (" Audit row 18 CONFIRMED and answered: OnNetlistArbKappa's kappa* = 197/1103 (s1c2 cons) is only the real relaxation's bound; "
           "at 200/1103 the auditor's own fast-corner assignment meets Scat and is not Safe (audit_s1c2_cons_200), and at 0.1807 every "
           "fast-corner assignment is safe while the case is unsafe at an interior corner (interior_s1c2_cons)."
           if k == 2 else " Audit row 18 answered (the s1c2 cons case is on bd_arbiter.a0_fork_client2).")
    kap["results"][0] = (
        f"link_arb (4 routed seeds), A0 fork, 7g's condition (no_early_ack_iff), client {k}, two endpoint readings (lit: FAST_MIN..SLOW_MAX "
        "for every arc; cons: early arcs FAST_MIN..SLOW_MIN, late arc FAST_MAX..SLOW_MAX + Elmore). Bkx18 (B-arb-kappa-exact.md, "
        "OnNetlistArbKappaExact): EXACT kappa threshold for each of this client's 8 seed x reading cases, in A's whole-ps CornerNat model "
        "(rational kappa, one rational corner for the die, every arc delay a whole number of ps within 1 +- kappa of its nominal at that "
        "corner, Scat; one fixed delay per arc per run), gate level on both sides (safe: Safe over every run; unsafe: a corner and an "
        f"assignment meeting Scat on all ten arcs on which every run acks early): exact_s1c{k}_cons ... exact_s4c{k}_lit state "
        "'(every corner, every assignment within kappa is Safe) <-> Below_X kappa', restated in A's and Bk1's types by Bridge.exact_*. "
        f"kappa_ex (float root extraction; Lean carries P_X < 0 with a rational cut u, bracketed to 1e-10 by bracket_*): {'; '.join(cases)}."
        + rat + " Safe kappas form an initial segment (safe_antitone: Scat bands grow with kappa). Each kappa_ex lies strictly inside "
        "OnNetlistArbKappa's old gap [kappa*, kappa* + 6/(E+L)). Verdicts: at rule A's 1/11 all 16 cases safe (verdict_κA); at kappaE = "
        "383/1927 15 of 16 safe, s1 client 2 cons unsafe (verdict_κE); s4 client 1 cons margin 0.2081 - 0.1988." + aud +
        " NOT covered: delays varying tick to tick, the A0 rise, arbitration (exclusion), Kleene X / metastability, kappa's value "
        "(unmeasured), the cons endpoints' provenance (Bt3's per-corner windows, not tied to a file).")
    cl = f"c{k}"
    refs = [L(KX, f"exact_s{s}{cl}_{r}", "exact", f"seed {s}, client {k}, {r}: all-corner, all-assignment safety iff Below (gate level)")
            for r in ("cons", "lit") for s in (1, 2, 3, 4)]
    refs += [L(KX, f"bracket_s{s}{cl}_{r}", "numbers") for r in ("cons", "lit") for s in (1, 2, 3, 4)]
    refs += [L(KX, "safe_antitone", "lemma", "Scat bands grow with kappa: the safe kappas are an initial segment"),
             L(KX, "not_safe1", "lemma"), L(KX, "not_safe2", "lemma"),
             L(KX, "verdict_κA", "corner", "kappa = 1/11: all 16 cases safe"),
             L(KX, "verdict_κE", "corner", "kappa = 383/1927: 15 of 16 safe")]
    if k == 2:
        refs += [L(KX, "audit_s1c2_cons_200", "counter_trace", "the auditor's assignment at 200/1103: Scat holds, not Safe"),
                 L(KX, "interior_s1c2_cons", "counter_trace", "kappa = 0.1807: every fast-corner assignment safe, an interior corner unsafe")]
    add_lean(e, refs)
    kap["exact_source"] = (f"OnNetlistArbKappaExact.exact_s1{cl}_cons .. exact_s4{cl}_lit (Bkx18): the one place where a kappa threshold "
                           "is called exact (audit row 18 answered); every other kappa result stays a bound / bracket")
    LOG.append(f"{e['id']}: corner.kappa.results[0] -> exact thresholds (OnNetlistArbKappaExact, 8 cases)")
cv["kappa"] = cv["kappa"].rstrip() + (
    " Bj7 (Bkx18, OnNetlistArbKappaExact): the 16 link_arb A0-fork cases (bd_arbiter.a0_fork_client1/2, 4 seeds x 2 clients x lit/cons) "
    "now have EXACT thresholds in the whole-ps CornerNat model, gate level on both sides (exact_*: safe iff Below_X kappa; corner.kappa."
    "exact_source); the validator allows the word 'exact' in corner.kappa.results on exactly those two rows. gcd_hw thresholds stay "
    "bracketed (Bkx19's rt1b, Bsrv's D1 / D2 to 1e-12) or within OnGcdArbKappa's gap: not exact.")

# ------------------------------------------------------------------ (2) gcd_hw arbiters, server credited, gate level (Bsrv)
SRV_TXT = ("Bsrv (B-gcd-arb-kappa-srv.md, OnGcdArbKappaSrv), lit reading (H_SPREAD_CORRELATED), whole fs, one delay per arc per run, "
           "server credited (the A0 branch to ustate, ustate's O6 arc, the q prefix and the server's graph path srv are delays of one "
           "corner-model realization; H_SERVER_GRAPH: the server answers no faster than srv). D1 = OnGcdArbKappa's 16 forms server-credited "
           "on all 36 arbiters, including ArbPin's BARE cell (A0 held low, H_A0_LOW): gate-level safe for kappa <= 0.080163500491 "
           "(design_gate_srv) and violated from kappa >= 0.080163500492 (design_srv_tight; binding seed 2 merge3.uarb1 h21, at the slow end, "
           "1.3e-6 above its kappa*). Its gate counterexample is the bare cell; as a run of 7j's gate relations (h21_7j_bare) it needs "
           "client 2 to withdraw an unacknowledged request: NOT a four-phase run. D2 = the 12 held-arbiter four-phase forms (7g forks, "
           "RT2/RT2b with srv, RT1s/RT1bs): gate-level safe for kappa <= 0.216552148868 (design_gate_held), violated from 0.216552148869 "
           "(design_held_tight; binding seed 4 merge12.uarb2 fork2, a 7g run through 7g's iff fork2_box_iff; the 7g model has no server). "
           "Which of D1 / D2 is gcd_hw's number depends on whether gcd_hw ever runs the bare race (H_SETTLED: open, not proved from the "
           "routes). Non-vacuity: design_nonvacuous. cons (H_SPREAD_INDEP): among the 16 server-credited forms the only rows failing at "
           "kappa = 0 are seed 2 merge3.uarb1 h21 and o1x (cons_srv_neg; pu = 0, so they fail at every kappa): under cons D1 has no safe "
           "kappa; D2's cons minimum 0.1288 (seed 4 merge12.uarb2 fork2) is the relaxation kappa* from the script, not decided. srv is from "
           "probe Bar's extraction (UNTRUSTED) and enters neither binding row. Not covered: the server's real latency, the non-binding rows' "
           "thresholds (certified safe at the design kappa, within 1.8e-5 by OnGcdArbKappa), per-edge scatter, X, metastability.")
srv_refs = [L(SRV, "design_gate_srv", "corner", "D1: every arbiter, gate level, kappa <= 0.080163500491"),
            L(SRV, "design_srv_tight", "corner", "D1 violated from 0.080163500492 (bare cell)"),
            L(SRV, "design_gate_held", "corner", "D2: held four-phase forms, gate level, kappa <= 0.216552148868"),
            L(SRV, "design_held_tight", "corner", "D2 violated from 0.216552148869 (7g fork2)"),
            L(SRV, "design_nonvacuous", "non_vacuity"),
            L(SRV, "cons_srv_neg", "corner", "cons: h21 and o1x of seed 2 merge3.uarb1 fail at kappa = 0")]
nsrv = 0
for e in C:
    k = e["corner"].get("kappa")
    if not k or not any(r.startswith("gcd_hw (36 routed arbiters") for r in k.get("results", [])):
        continue
    assert e["cell"] == "bd_arbiter", e["id"]
    k["results"].append(SRV_TXT)
    add_lean(e, srv_refs)
    nsrv += 1
assert nsrv == 12, nsrv
LOG.append(f"{nsrv} bd_arbiter rows: corner.kappa.results + OnGcdArbKappaSrv (D1 0.0802 bare cell, D2 0.2166 held four-phase)")
add_lean(BY["bd_arbiter.rt1b"], [L(SRV, "h21_gate_unsafe", "counter_trace", "D1's binding h21 (2 -> 1 handover, bare cell): both grants high"),
                                  L(SRV, "h21_7j_bare", "counter_trace", "the same race as a 7j run: A0 never rises, client 2 withdraws an unacknowledged request"),
                                  L(SRV, "g2m3_held_rt1bs", "corner", "the same arbiter's held r2 -> r1 handover (RT1bs) safe to kappa 0.769"),
                                  L(SRV, "h21_safe", "corner"), L(SRV, "h21_unsafe", "corner"), L(SRV, "h21_inside", "numbers")])
add_lean(BY["bd_arbiter.a0_fork_client2"], [L(SRV, "fork2_safe", "corner"), L(SRV, "fork2_unsafe", "corner"),
                                             L(SRV, "fork2_inside", "numbers"),
                                             L(SRV, "fork2_gate_unsafe", "counter_trace", "D2's binding row: a 7g run fires A2 spuriously")])

# ------------------------------------------------------------------ (3) self-audit 4 fixes (Bsa4, SelfAuditB7)
# (3a) bd_arbiter.rt1b: the row-level 'server-free' hypothesis contradicts the row's own inequality
e = BY["bd_arbiter.rt1b"]
SF = "server-free form (smin, A0 route to ustate, ustate O6 not credited)"
assert SF in e["hypotheses"] and "smin + wa0s + qr" in e["inequality"]
e["hypotheses"] = [h for h in e["hypotheses"] if h != SF] + [
    "H_SERVER_MIN (the server answers no faster than smin; the inequality credits smin, the A0 route to ustate wa0s and ustate's O6 arc qr)"]
e["corner"]["kappa"]["results"].append(
    "Bsa4 (B-self-audit4.md): the 'RT1b server-free' numbers in this row's kappa results (lit min 16587/374773 ~ 0.0443, Bkx19's "
    "bracket, rt1b_gate_unsafe) are for OnGcdArbKappa's server-free ARC FORM (smin = wa0s = qr = 0), NOT for this row's inequality, "
    "which credits smin + wa0s + qr (the server-credited RT1b of ArbHeldTimed2; under kappa that is OnGcdArbKappa's RT1bs, lit min 0.617, "
    "0.651 on seed 3 merge12.uarb1). Bkx19's kappa_ex - kappa* (~3.9e-6) is NOT proved to be the 1 fs grid.")
r1 = e["corner"]["kappa"]["results"]
i1 = [i for i, s in enumerate(r1) if "The whole kappa_ex - kappa* (~3.9e-6) is the 1 fs grid." in s]
assert len(i1) == 1
r1[i1[0]] = r1[i1[0]].replace("The whole kappa_ex - kappa* (~3.9e-6) is the 1 fs grid.",
                              "kappa_ex - kappa* is ~3.9e-6 (that it is the 1 fs grid is NOT proved: Bsa4).")
LOG.append("bd_arbiter.rt1b: row hypothesis 'server-free form' -> H_SERVER_MIN (matches its inequality); server-free caveat kept on the kappa sub-result")

# (3b) superseded sentences (B-self-audit4.md, JSON table: 'stale' / 'inconsistent' notes)
for rid, old in (("bd_mux.uj_env_latency_req", " No counter-run."),
                 ("bd_mux.uj_env_latency_ctl", " Sufficient; necessity not shown (negative controls only show the term is used)."),
                 ("bdc_muxn.uj_env_latency_req", ", not probed for muxn."),
                 ("bd_flink.qfb_first", "sufficient; no flink counter-trace.")):
    new = {"bdc_muxn.uj_env_latency_req": ".", "bd_flink.qfb_first": "sufficient."}.get(rid, "")
    sub(BY[rid], "exactness_note", old, new)
    LOG.append(f"{rid}: superseded sentence removed ({old.strip()!r})")

# (3c) boundary labels on +1 forms: the refuted point is the binary '<=' form, 2 ticks from the row's +1 form
BP = {"refuted_form": "binary '<=' (no strict +1)", "slack": 1, "ticks_from_row_form": 2,
      "row_form_necessity": "not shown: the row's +1 form is sufficient; its own boundary is not refuted"}
for rid, thm in (("bd_mux.uj0_env_latency_req_max", "Necessity4Mux.claimX1_false"),
                 ("bd_mux.uj_env_latency_ctl", "Necessity4MuxC.claimC1_false"),
                 ("bd_flink.qfb_first", "Necessity5Flink.q1_false")):
    e = BY[rid]
    assert e["exactness"] == "sufficient+necessary_at_boundary" and e["strict"]["margin_added_ps"] == 1, rid
    e["boundary_point"] = dict(BP, refuted_by=thm)
    add_scope(e, "necessity_scope", "BOUNDARY LABEL (Bsa4): 'necessary_at_boundary' refers to the binary '<=' form; the refuted point "
              "(slack 1 against '<=') is 2 ticks from this row's +1 form, whose own boundary is NOT refuted")
    LOG.append(f"{rid}: boundary_point (refuted point = '<=' form, 2 ticks from the +1 form)")
cv["boundary_point"] = ("optional (Bj7, Bsa4): on a sufficient+necessary_at_boundary row whose form carries the strict +1 but whose counter-run "
                        "refutes the binary '<=' form: refuted_form, slack, ticks_from_row_form (= slack + 1), refuted_by, and "
                        "row_form_necessity ('not shown'). Rows without it are not claimed either way (only the three rows Bsa4 checked "
                        "carry it).")

# (3d) H_SPREAD_CORRELATED is the lit model itself
hk = [h for h in doc["hypotheses_not_inequalities"] if h["id"] == "H_SHARED_CORNER / H_SCATTER (kappa)"][0]
hk["statement"] += (" Bsa4 (SelfAuditB7.spread_corr_iff: H_SPREAD_CORRELATED arc <-> arc = litArc): H_SPREAD_CORRELATED IS the lit model "
                    "itself, a renaming of the lit reading, not an independent hypothesis; spread_correlated_safe is rt1b_safe after subst. "
                    "Its only content beyond 'use lit' is the physical reading (the within-corner spread is die-wide), which T_SPREAD tests.")
add_lean(hk, [L(SA7, "spread_corr_iff", "relation", "H_SPREAD_CORRELATED <-> the lit arc model")])
LOG.append("hypothesis H_SHARED_CORNER / H_SCATTER (kappa): H_SPREAD_CORRELATED = lit model (spread_corr_iff)")

# (3e) '+W under H_W_BOUND' sufficient: proved for bd_steer only
WB = "Sufficient without the split: +W under H_W_BOUND (c_e + a_l <= W for every race pair)."
nwb = Counter()
for e in C:
    st = e.get("strict")
    if not st or WB not in st.get("x_window", ""):
        continue
    if e["cell"] == "bd_steer":
        st["x_window"] = st["x_window"].replace(WB, WB[:-1] + ": PROVED for bd_steer (SelfAuditB7.steer_win_bound; non-vacuity "
                                                "steer_win_bound_witness).")
        add_lean(e, [L(SA7, "steer_win_bound", "sufficient", "+W under H_W_BOUND (c_e + a_l <= W for every race pair) is sufficient for the steer box"),
                     L(SA7, "steer_win_bound_witness", "non_vacuity")])
        nwb["proved"] += 1
    else:
        st["x_window"] = st["x_window"].replace(WB, WB[:-1] + ": UNPROVED for this cell (stated by analogy; the only theorem is "
                                                "bd_steer's, SelfAuditB7.steer_win_bound).")
        nwb["unproved"] += 1
assert nwb["proved"] == 2 and nwb["unproved"] == 69, nwb
LOG.append(f"strict.x_window '+W under H_W_BOUND': proved on {nwb['proved']} bd_steer rows, labelled UNPROVED on {nwb['unproved']}")

# (3f) FASTRISE ack_flush: not necessary for every DACK >= 3
e = BY["bd_delay[FASTRISE].ack_flush"]
sub(e, "exactness_note", "NOT necessary for DACK >= 3 (flush_not_necessary, dack3_clean)",
    "NOT necessary for DACK = 3 (flush_not_necessary, dack3_clean) and for every DACK = m + 1 >= 3 (SelfAuditB7.flush_not_necessary_all: "
    "line delta k = m + 1 - k, w = 1, point delays; Bsa4 closed the gap from the single DACK = 3 instance)")
add_lean(e, [L(SA7, "flush_not_necessary_all", "not_necessary", "every DACK = m + 1 >= 3, point delays, line level")])
LOG.append("bd_delay[FASTRISE].ack_flush: not_necessary for every DACK >= 3 (flush_not_necessary_all)")

# ------------------------------------------------------------------ (4) C's H_ARB_EXCL is not derivable from B's per-pin arbiter (Bbr)
ARB_CC = {"field": "H_ARB_EXCL (C's AMergeC / IpowCells Contract: no tick with both grants high, every tick of the run)",
          "status": "not_derivable",
          "lean": ["ContractBridge.arb_excl_not_derivable", "ContractBridge.arb_excl_of_window"],
          "basis": ("arb_excl_not_derivable: B's bd_arbcell in its per-pin box (boxS), requests at 100 / 105 ps, has a behaviour with both "
                    "grants high at a tick, so H_ARB_EXCL as C states it does not follow from B's per-pin arbiter. arb_excl_of_window: "
                    "inside B's QUIET / COMMIT-without-overlap window it holds (forall n, g1 n && g2 n = false), for ONE arbitration with "
                    "single-step requests only; C's amerge_inv needs it at every tick, so C's proof does not go through with the window "
                    "form (a multi-token arbiter theorem, i.e. the board's open 8% overlap question, is missing).")}
for rid in ("bd_arbcell.settled_exclusion", "bd_arbcell.handover_overlap", "bd_arbiter.rt1", "bd_arbiter.rt1b"):
    e = BY[rid]
    e["c_contract"] = copy.deepcopy(ARB_CC)
    add_lean(e, [L(CB, "arb_excl_not_derivable", "counter_trace", "C's H_ARB_EXCL is not derivable from B's per-pin bd_arbcell (both grants high at a tick)"),
                 L(CB, "arb_excl_of_window", "partial", "the window-only form: one arbitration, single-step requests")])
    LOG.append(f"{rid}: c_contract H_ARB_EXCL not_derivable (arb_excl_not_derivable)")

# ------------------------------------------------------------------ (5) LutFbBridge2: H_SEL_STABLE (mux joins), H_PWR_SRC (bd_src)
SEL_CC = {"field": "C's LutFb / FbFirst for bd_mux uj0 / uj1 (mux_bound's h0, f0 / h1, f1)",
          "status": "needs_extra_hypothesis", "extra": "H_SEL_STABLE (select constant while ctl_req is high)",
          "lean": ["LutFbBridge2.muxJ0_lutFb", "LutFbBridge2.muxJ1_lutFb", "LutFbBridge2.sel_glitch_breaks_uj0", "LutFbBridge2.gated_phases"],
          "basis": ("muxJ0_lutFb / muxJ1_lutFb derive C's premises from B's physical model with EnvG on the effective pins "
                    "(x_req, ctl_req and not s); gated_phases gives those phases from the request protocol plus H_SEL_STABLE. "
                    "sel_glitch_breaks_uj0: real uj0 INIT, transport LUT delay 2, wire 1, every channel hypothesis, x_req = ctl_req = 1 "
                    "and a 1-tick select glitch: LutFb muxJ0F fails, so the request protocols alone are not enough. That this row's "
                    "pin-level setup / hold implies H_SEL_STABLE is NOT proved in Lean (ContractBridge's H_SETUP_PIN / H_HOLD_PIN route "
                    "gives C's H_SEL_PIN instead).")}
for rid in ("bd_mux.bundled_s_setup", "bd_mux.bundled_s_hold"):
    e = BY[rid]
    e["c_contract"] = copy.deepcopy(SEL_CC)
    add_lean(e, [L(FB2, "muxJ0_lutFb", "lemma", "C's LutFb / FbFirst for uj0 from B's model + EnvG"),
                 L(FB2, "muxJ1_lutFb", "lemma"),
                 L(FB2, "gated_phases", "lemma", "the gated request's phases from the request protocol + H_SEL_STABLE"),
                 L(FB2, "sel_glitch_breaks_uj0", "counter_trace", "1-tick select glitch: C's LutFb muxJ0F fails")])
    LOG.append(f"{rid}: c_contract LutFb needs H_SEL_STABLE (sel_glitch_breaks_uj0)")
new_h = {"id": "H_SEL_STABLE / H_PWR_SRC (C-bridge LUT premises)", "catalogue_row": "none (Bfb2, formal/notes/B-lutfb-bridge2.md)",
         "cells": ["bd_mux", "bd_src"],
         "statement": ("Two hypotheses the bridge from B's physical LUT model to C's LUT premises needs beyond Bfb's (LutFbBridge2). "
                       "H_SEL_STABLE: the mux select s is constant while ctl_req is high; needed for C's LutFb of the mux joins uj0 / uj1 "
                       "(sel_glitch_breaks_uj0: with it dropped, a 1-tick select glitch breaks LutFb muxJ0F under every channel hypothesis); "
                       "gated_phases uses it to give the gated request (r and s == b) its phases. H_PWR_SRC: during the power-up window "
                       "t < hi, where Win says nothing, bd_src's output may only rise; it replaces Bfb's H_PWR (output 0 until hi), which "
                       "the source cannot meet because its excitation not-ack is 1 from power-up (src_lutSI; src_witness rises at 1, inside "
                       "the window, so H_PWR_SRC is used). Neither is a timing inequality of this file; no row derives either. The bridge's "
                       "environment (Env1 per link) is still assumed network-wide (gcd_hw_safe_phys_links)."),
         "lean": [L(FB2, "sel_glitch_breaks_uj0", "counter_trace"), L(FB2, "gated_phases", "lemma"),
                  L(FB2, "muxJ0_lutFb", "lemma"), L(FB2, "muxJ1_lutFb", "lemma"),
                  L(FB2, "src_lutSI", "sufficient", "bd_src's LutSI premise under H_PWR_SRC"),
                  L(FB2, "src_witness", "non_vacuity"), L(FB2, "muxJ0_witness", "non_vacuity")],
         "check": "not statically checkable: H_SEL_STABLE is a property of the control sender's select trace; H_PWR_SRC of bd_src's power-up"}
assert new_h["id"] not in {h["id"] for h in doc["hypotheses_not_inequalities"]}
doc["hypotheses_not_inequalities"].append(new_h)
LOG.append(f"hypotheses_not_inequalities: NEW {new_h['id']}")
cv["c_contract"] = ("optional (Bj7): how a C-side contract field relates to the row (ContractBridge, LutFbBridge2): field, status = derived | "
                    "not_derivable | needs_extra_hypothesis, extra (the added hypothesis), lean (File.name, each also in the row's lean "
                    "list), basis.")

doc["produced_by"] = (doc["produced_by"].rstrip() +
    " Updated by probe Bj7 (2026-10-29) from B-arb-kappa-exact.md (OnNetlistArbKappaExact: exact thresholds of the 16 link_arb A0-fork "
    "cases), B-gcd-arb-kappa-srv.md (OnGcdArbKappaSrv: gate-level D1 0.0802 bare cell, D2 0.2166 held four-phase, cons failures), "
    "B-self-audit4.md (SelfAuditB7: rt1b hypothesis, superseded sentences, boundary_point, spread_corr_iff, steer_win_bound, "
    "flush_not_necessary_all), B-contract-bridge.md (c_contract H_ARB_EXCL) and B-lutfb-bridge2.md (c_contract H_SEL_STABLE, "
    "hypothesis H_SEL_STABLE / H_PWR_SRC); the 'probe Bj7' section of cell_constraints.bj5.py.")

# ================================================================== probe Bj8 (2026-10-29)
# Fourth Bj pass of the day. Applies, from today's committed notes (and JOURNAL-B.md progress 09:05 / 09:11 / 09:31 / 09:36):
#   B-necessity6.md (Necessity6Mux / Necessity6MuxN / Necessity6MuxJ / Necessity6PipeSel),
#   B-zero-delay-tok.md (ZeroDelayTok*: new row bd_link.stage_rearm, H_REARM),
#   B-arb-no-withdraw.md (ArbNoWithdraw: new row bd_arbiter.settled_rise, H_SETTLED; D2's no-withdrawal dependence;
#     7h/7j first-handover scope), B-arb-settled.md (ArbSettled: the row's sharp form H_PIN, lead's addition), B-arb-multi-token.md (ArbMultiToken: c_contract H_ARB_EXCL derivable for the held arbiter),
#   B-ipow-cells-t.md (IpowCellsT: Gap.gap_exact, the exact form of the RT_FB feedback contract).
# Every name cited below is declared in the cited file (the validator greps each one).
LOG.append("---- probe Bj8")
N6M, N6N, N6J, N6P = "Necessity6Mux", "Necessity6MuxN", "Necessity6MuxJ", "Necessity6PipeSel"
ZD, ZDC, ZDW, NW, MT, ICT = "ZeroDelayTok", "ZeroDelayTokChain", "ZeroDelayTokWit", "ArbNoWithdraw", "ArbMultiToken", "IpowCellsT"
BP8 = {"refuted_form": "binary '<=' (no strict +1)", "slack": 1, "ticks_from_row_form": 2,
       "row_form_necessity": "not shown: the row's +1 form is sufficient; its own boundary is not refuted"}
BP8_SCOPE = ("BOUNDARY LABEL (Bsa4 convention): 'necessary_at_boundary' refers to the binary '<=' form; the refuted point (slack 1 "
             "against '<=') is 2 ticks from this row's +1 form, whose own boundary is NOT refuted")

# ------------------------------------------------------------------ (1) Necessity6 (Bnx6)
e = relabel("bd_mux.uj1_env_latency_req_max", "sufficient+necessary_at_boundary",
            [L(N6M, "ClaimY", "definition", "MuxStaticN with S_J1_YR weakened by s, every other hypothesis verbatim"),
             L(N6M, "claimY0", "sufficient", "ClaimY 0 = mux_ok_staticN's hypothesis set"),
             L(N6M, "failY10", "counter_run", "N6.run 10 (uj0 net 1, uj1 net 10): every other MuxStaticN field holds, S_J1_YR off by exactly 1; the max is the z_ack branch"),
             L(N6M, "claimY1_false", "counter_trace", "not ClaimY 1: y_req's fall reaches uj1 at 57, j1 = 0 at 58 inside [48, 61), z_req = 0 at 61 inside [51, 64)"),
             L(N6M, "passY9", "non_vacuity", "the same family at 9 ticks passes with equality")],
            "Bnx6 (B-necessity6.md, Necessity6Mux): the uj1 boundary run is now built (claimY1_false, z_ack branch binding); "
            "the earlier 'uj1 boundary run NOT built' is superseded.", old_ok=("sufficient",))
sub(e, "exactness_note", "the uj1 boundary run is the symmetric statement, NOT built. ", "")
add_scope(e, "necessity_scope", "the z_ack branch (form 1), one parameter point (N6.run 10, unit delays, uj1 feedback net 10), binary "
          "'<=' at slack 1; form 0 (the j branch) has no boundary run of its own; " + BP8_SCOPE)
e["boundary_point"] = dict(BP8, refuted_by=f"{N6M}.claimY1_false")

e = relabel("bdc_muxn.uj_env_latency_req_max", "sufficient+necessary_at_boundary",
            [L(N6N, "ClaimN", "definition", "MN3StaticN with S_J_XR weakened by s, every other hypothesis verbatim"),
             L(N6N, "claimN0", "sufficient", "ClaimN 0 = muxn3_ok_staticN's hypothesis set"),
             L(N6N, "failN", "counter_run", "Mn6.run: unit delays, 10-tick feedback nets, Ec = 2 so S_J_C holds with equality while the max form is off by 1"),
             L(N6N, "claimN1_false", "counter_trace", "not ClaimN 1: in_0_req's fall reaches uj_0 at 41, j_0 = 0 at 42 inside [32, 43)")],
            "Bnx6 (B-necessity6.md, Necessity6MuxN): the boundary is now shown with a control sender one tick slower than Mn3Wit's "
            "(S_J_C holds with equality, the max form alone off by 1; claimN1_false); the earlier 'boundary NOT shown for muxn' is "
            "superseded. DELAY > 1 not covered.", old_ok=("sufficient",))
sub(e, "exactness_note", " Its boundary is NOT shown for muxn: in Mn3Wit's run S_J_C has the same right side (10), so violating the max form "
    "by 1 also breaks S_J_C; an isolated counter-run needs a slower control sender.", "")
add_scope(e, "necessity_scope", "one parameter point (Mn6.run, N = 1, DELAY = 1, input 0's join), binary '<=' at slack 1; " + BP8_SCOPE)
e["boundary_point"] = dict(BP8, refuted_by=f"{N6N}.claimN1_false")

e = relabel("bd_pipe.rst_lines", "sufficient+necessary_at_boundary",
            [L(N6P, "TimingS", "definition", "PipePerPin's TimingP with each of the four H_RST_SEL terms weakened separately"),
             L(N6P, "claim0", "sufficient", "Claim 0 0 0 0 = nodes_clean under TimingP"),
             L(N6P, "rst_sel_boundary", "counter_trace", "Claim 0 0 0 0 and not Claim (one term weakened by 1), for each of (a)-(d); N = 1, real bd_c2n INIT"),
             L(N6P, "a_false", "counter_trace", "(a) R0 + pr.hi <= R + ps.lo off by 1: power-up request garbage fires the node at 6, before tau 0 0 = 12"),
             L(N6P, "b_false", "counter_trace", "(b) out.hi + wh + pq.hi <= R + ps.lo off by 1: stale feedback fires the node at 6, before tau 0 0 = 9"),
             L(N6P, "c_false", "counter_trace", "(c) R + ps.hi <= rho0 + pr.lo off by 1: the node rises one tick late"),
             L(N6P, "d_false", "counter_trace", "(d) R0 + pa.hi <= rho0 + pr.lo off by 1: the node rises one tick early"),
             L(N6P, "a_viol", "numbers"), L(N6P, "b_viol", "numbers"), L(N6P, "c_viol", "numbers"), L(N6P, "d_viol", "numbers")],
            "Bnx6 (B-necessity6.md, Necessity6PipeSel): the four per-pin H_RST_SEL terms (the row's representative form) are now "
            "necessary at the boundary too (rst_sel_boundary), so every term of the row has a boundary run and the row is "
            "relabelled. (a), (b) guard real early fires from power-up garbage; (c), (d) only shift the first edge by one tick (data "
            "correctness under (c) / (d) violated not examined). N >= 2 and Kleene X at the selects not covered.", old_ok=("sufficient",))
sub(e, "exactness_note", " the row stays 'sufficient' because its representative per-pin H_RST_SEL form has no necessity result.",
    " (Bj8: superseded, see Bnx6 below.)")
sub(e, "exactness_note", "; the row stays 'sufficient' because the other terms are not.", " (Bj8: superseded, every term now has a boundary run).")
e["necessity_scope"] = e["necessity_scope"].replace(
    "The per-pin (6g) H_RST_SEL terms (PipePerPin; the row's representative form) have no necessity result",
    "The per-pin (6g) H_RST_SEL terms (PipePerPin; the row's representative form) are necessary at the boundary (Bnx6, "
    "Necessity6PipeSel.rst_sel_boundary: a_false .. d_false, one parameter point each, N = 1); for (a), (c), (d) the Lean form is the "
    "JSON form (no strict), for (b) the Lean '<=' form is 2 ticks from the JSON +1 form")
assert "rst_sel_boundary" in e["necessity_scope"]
add_scope(e, "necessity_scope", BP8_SCOPE + " (applies to the strict loop terms, among them (b), the representative form 0)")
e["boundary_point"] = dict(BP8, refuted_by=f"{N6P}.b_false")

e = BY["bd_mux.uxa_join_latency"]
assert e["exactness"] == "sufficient"
add_lean(e, [L(N6J, "ClaimJ", "definition", "MuxStatic with S_XA_J.2 weakened by s, every other field (S_XA_J.1, S_YA_J) verbatim"),
             L(N6J, "claimJ0", "sufficient", "ClaimJ 0 = mux_ok's hypothesis set"),
             L(N6J, "failJ", "counter_run", "J.run: unit delays, 12-tick j0 -> uxa wire, tight partners, reset to 14; S_XA_J.2 off by exactly 1 (14 = 13 + 1)"),
             L(N6J, "claimJ1_false", "counter_trace", "not ClaimJ 1: j0's fall reaches uxa at 57, z_ack's next rise at 58; x_ack = 1 at 60 inside [59, 67)")])
sub(e, "exactness_note", " Sufficient; necessity not shown (negative controls only show the term is used).",
    " Sufficient. Bnx6 (B-necessity6.md, Necessity6MuxJ): the second conjunct S_XA_J.2 (uxa, W0x.hi + Lxa.hi + wxah <= 2 Kz + Kc + "
    "Wzx.lo) is necessary at the boundary (claimJ1_false: a slow j0 -> uxa wire, x_ack oscillates through the next y transaction); "
    "S_XA_J.1 and the uya mirror have no result, so the row stays 'sufficient' (Bnx6's unproved analysis: S_XA_J.1 is probably not "
    "necessary as written).")
e["boundary_tight_terms"] = [{"term": "S_XA_J.2 (form 1, uxa)", "refuted_by": f"{N6J}.claimJ1_false", "form": "binary '<='",
                              "ticks_from_row_form": 2, "untouched": "S_XA_J.1 (form 0), uya forms 2 / 3"}]
LOG.append("bd_mux.uxa_join_latency: stays sufficient; boundary_tight_terms S_XA_J.2 (claimJ1_false)")
cv["boundary_tight_terms"] = ("optional (Bj8): on a row that stays 'sufficient', the terms (conjuncts) that ARE necessary at the boundary: term, "
                              "refuted_by (File.theorem, a NOT Claim(weakened by 1)), form refuted, ticks_from_row_form, and the terms untouched. "
                              "It does not change the row's label.")

# ------------------------------------------------------------------ (2) bd_link.stage_rearm (Bzd3, ZeroDelayTok)
st = BY["bd_link.stage"]
new_row({
    "id": "bd_link.stage_rearm",
    "cell": "bd_link",
    "catalogue_row": "none (Bzd3, formal/notes/B-zero-delay-tok.md)",
    "obligation": ("one bd_link stage carrying k >= 2 tokens (bd_c2n + one bd_latch bit, real INITs, open loop): between tokens j and j+1 "
                   "the controller surely reads the previous ack_out fall no later than it surely reads the next req_in rise"),
    "inequality": ("H_REARM Fb1_j + Bhi <= Ra1_{j+1} + Ahi (ack_out fall window end of token j plus the ack pin's slow read, against req_in "
                   "rise window end of token j+1 plus the req pin's slow read); together with bd_link.stage's six rows at every token. "
                   "Closed-loop form (ZeroDelayTokChain): V1_{i+1,j} + Bhi_i <= U1_{i,j+1}"),
    "forms": [],
    "refers_to": ["bd_link.stage", "bd_c2n.env_latency"],
    "informational": True,
    "lean": [L(ZD, "exact_rearm", "exact", "under WfK, GapK and bd_link.stage's six rows at every token: SafeK P <-> forall j, H_REARM j. The full "
               "iff SafeK <-> RowsK is NOT proved (the six rows' necessity inside a k-token env is open)"),
             L(ZD, "sufficientK", "sufficient", "WfK + six rows per token + H_REARM => SpecK for every behaviour (no GapK)"),
             L(ZD, "need_rearm", "necessary", "needs GapK j and token j+1's H_RACE_UP"),
             L(ZD, "rearm_breaks", "counter_trace", "P2 2979: 2 tokens, P0 box, H_REARM violated by exactly 1 ps (rearm_one_tick), all else met"),
             L(ZD, "rearm_one_tick", "numbers", "P2 2979 violates H_REARM by exactly 1 ps, every other row met"),
             L(ZD, "witness2", "non_vacuity", "P2 3500: all rows hold, SafeK, a simulated behaviour (data 1 then 0) meets SpecK"),
             L(ZD, "latch_tok_ok", "lemma", "multi-token latch capture per token window (no new latch row)"),
             L(ZD, "WfK", "definition"), L(ZD, "GapK", "definition", "necessity scope only: Fa1 j + Ahi <= U0 (j+1), V1 j + Qhi <= U0 (j+1)"),
             L(ZD, "RowsK", "definition"), L(ZD, "SpecK", "definition"), L(ZD, "SafeK", "definition"),
             L(ZDC, "chain_specK", "context", "closed N-stage chain, k tokens: every stage meets SpecK under H_LOOP_K, H_WIRE_POS, H_RST_SEEN, H_DATA_LOOP_K"),
             L(ZDC, "chain_rstK", "lemma"), L(ZDC, "chain_tokK", "lemma"),
             L(ZDW, "chain2_witness", "non_vacuity", "2 stages x 2 tokens, nonzero reads, coupled behaviour meets the 2-token spec")],
    "exactness": "exact",
    "exact_scope": ("iff for H_REARM ALONE: SafeK <-> forall j, H_REARM j, given WfK (LinkExact's Wf per token, k >= 1, H_NEXT ordered env "
                    "pulses), GapK (the necessity scope: the previous request fall and the node's own fall are surely read before the next "
                    "request can be read rising) and bd_link.stage's six rows at every token (exact_rearm). NOT the full k-token iff: the six "
                    "rows' necessity inside a k >= 2 environment is open (it must quantify over data sequences: with vs (j-1) = vs j, "
                    "setup_pulse of token j is not necessary). Sufficiency (sufficientK) needs no GapK. Binary '<=' in definite-window "
                    "times; no strict +1 claimed. NOT covered: rings with initial tokens (bd_c2n_set), C's k-token Link run, correlated "
                    "corners, a W-bit bus, zero-delay inter-stage reads."),
    "exactness_note": ("Bzd3 (B-zero-delay-tok.md, ZeroDelayTok): the only new cross-token row. If it fails, at U1 (j+1) the node reads request "
                       "1, acknowledge 1 (still token j's) and its own 0, and the real INIT holds 0 (c2nK 1 1 0 0 = 0) where the spec demands 1. "
                       "The rise of token j+1 has no new feedback race (c_follow1), the low phase of token j extends to U0 (j+1) from H_RACE_DN, "
                       "and the latch has no new row (latch_tok_ok). In the closed loop both sides are caused by stage i's own fall (through "
                       "the downstream request pin, and through the upstream ack pin and back), so it is a genuine race of the loop. "
                       "H_DATA_LOOP_K (cross-stage hold Tn_{i+1,j} <= U0_{i,j+1} + Elo_i) is a closed-loop hypothesis, sufficient only, not a "
                       "row of this file."),
    "hypotheses": ["H_CTL_READ / H_PIN_READ (non-monotone)", "H_KLEENE_LUT", "H_BOX", "EnvK (k four-phase tokens, open loop)",
                   "WfK: LinkExact's Wf per token + H_NEXT", "GapK (necessity of H_REARM only)"],
    "site_pins": {"needed": True, "roles": ["req pin hi (Ahi)", "ack pin hi (Bhi)"]},
    "rule": {"rule": "none", "verdict": "none", "detail": "UNCHECKED: no rule compares a link's ack-fall read with the next request-rise read"},
    "corner": {"mode": "n/a", "rule": "see refers_to (pins independent in the box, as in bd_link.stage)"},
    "check_scope": "route_plus_env",
    "evidence": "illustrative numbers only (P2 2979 breaks by 1 ps, P2 3500 passes); no route",
    "status": "proved",
    "combine": "all",
    "kleene_dependence": {"needs": st["kleene_dependence"]["needs"],
                          "basis": "same model as bd_link.stage (LinkExact's Kleene box, real bd_c2n INIT); " + st["kleene_dependence"]["basis"]
                                   + " ZeroDelayTok is not re-run under KleenePess.",
                          "inferred": True},
})
add_lean(st, [L(ZD, "exact_rearm", "context", "k >= 2 tokens: the one new cross-token row is bd_link.stage_rearm (H_REARM)")])
note_append(st, "Bj8 (Bzd3, ZeroDelayTok): with k >= 2 tokens the six rows apply per token (latch_tok_ok) plus ONE new row, "
            "bd_link.stage_rearm (H_REARM, exact_rearm); this row's iff stays the one-token one.")

# ------------------------------------------------------------------ (3) H_SETTLED (Bbare, ArbNoWithdraw) in its sharp form H_PIN (Bset, ArbSettled)
AS = "ArbSettled"
ref = BY["bd_arbiter.rt2_pulse"]
def settled_form(k):
    # client k: data side = A0 rise to ustate's hold pin I4; request side = A0 -> ua_k -> A_k -> client release loop -> r_k -> ustate's request pin
    upin = "ustate.I0" if k == 1 else "ustate.I1"
    return {"launch": f"A0 rise at the divergence point of ustate's and ua{k}'s branches of the A0 net (shared A0 prefix ac + dS_k cancels)",
            "data_paths": [[{"kind": "wire", "from": "A0@div", "to": "ustate.I4", "lean_sym": "dS2 + es" if k == 1 else "dS1 + es"},
                            {"kind": "site_pin", "from": "ustate.I4@pip", "to": "ustate.I4", "pin_role": "A0", "lean_sym": "ps"}]],
            "request_paths": [[{"kind": "wire", "from": "A0@div", "to": f"ua{k}.A0", "lean_sym": f"d12 + e{k}"},
                               {"kind": "site_pin", "from": f"ua{k}.A0@pip", "to": f"ua{k}.A0", "pin_role": "A0", "lean_sym": f"p{k}"},
                               {"kind": "lut_arc", "from": f"ua{k}.A0", "to": f"ua{k}.O6", "lean_sym": f"ac{k}"},
                               {"kind": "env", "name": f"L{k}", "spec": (f"client {k}'s release loop: A{k} driver -> client ack pin (wire + site pin, NOT "
                                "extracted) -> client cell -> r_k driver (H_CLIENT_LAT, min). link client: the controller's O6 arc x (H_ACK_READ, "
                                "H_LUT6_O6, LinkExact Conj); steer client: join C-element + uack OR + cond_br arcs (no model with arcs); R0 client: "
                                "the downstream arbiter's A0 C-join"), "lean_sym": "L"},
                               {"kind": "wire", "from": f"r{k} driver", "to": upin, "lean_sym": f"rs{k} (H_RK_ROUTE: rs{k} <= wr{k}s; the prefix before the branch is >= 0, dropped)"}]],
            "margin_ps": 0}
SET_RES = ("Bset (B-arb-settled.md, ArbSettled), lit reading (H_SPREAD_CORRELATED; Real7), Bar's UNTRUSTED extraction, sharp form H_ARC_P "
           "(fsh1 / fsh2): with setTbl2's per-client latency L, H_PIN holds for every realization at kappa <= kappaS2 = 0.216552148868 "
           "(OnGcdArbKappaSrv's D2 bound) on all 72 clients (settledP_safe; kernel certificate set2_cert). Largest L 502.361 ps (seed 2 "
           "merge12.uarb2 client 2, setTbl2_max), positive on 21 of 72 clients (setTbl2_pos: 3 link, 16 steer, 2 R0); for each positive entry "
           "and every kappa >= kappaS2 a realization violates the form at L - 10 fs (settledP_tight), so L = 0 fails on precisely those 21 "
           "(settledP_L0_fails). Link clients: discharged on 18 of 20 instances from LinkExact's controller model plus the controller's O6 arc "
           "at the same corner, no latency hypothesis (link_pin1 / link_pin2, design_link_discharged1 / 2); seed 3 and seed 4 merge2.uarb1 "
           "client 2 stay conditional (link_short; they need the unextracted ack wire, >= 37.6 / 89.7 ps). Steer and R0 clients: not "
           "discharged. Bbare's coarser H_SETTLED form (wa0s + qf <= wa0k + ckr + L) needed up to 1.59 ns and failed at L = 0 on 65 of 72 "
           "clients (settled_safe, settled_L0_fails).")
new_row({
    "id": "bd_arbiter.settled_rise",
    "cell": "bd_arbiter",
    "catalogue_row": "none (Bbare, formal/notes/B-arb-no-withdraw.md; sharp form Bset, formal/notes/B-arb-settled.md)",
    "obligation": ("H_SETTLED of 7h / 7j in its sharp pin form H_PIN (the rise-side twin of rule J): A0's rise reaches ustate's hold pin I4 no "
                   "later than the releasing client's r_k fall reaches ustate's request pin; the release starts from A0 -> ua_k -> A_k -> "
                   "client and returns to r_k"),
    "inequality": ("H_PIN (client k): ta + wa0s <= t0 + wr_ks (A0's rise at ustate.I4 vs r_k's fall at ustate's r_k pin). From causality "
                   "(settledP1_of_causal / settledP2_of_causal) it holds as soon as H_ARC_P: wa0s <= wa0k + ckr + L_k + wr_ks, L_k = client k's "
                   "release latency (A_k rise at ua_k's output -> r_k fall at its driver); on the routed data (Real7, H_RK_ROUTE rs_k <= wr_ks) "
                   "fsh_k: dS_other + es + ps <= d12 + e_k + p_k + ac_k + rs_k + L_k. H_PIN is implied by 7h / 7j's H_SETTLED (ta + wa0s + qf "
                   "<= t0 and ta + wa0k + ckf <= t0; H.ofScn, J.ofScn2) and strictly weaker (strict_witness); H_SETTLED's second conjunct is "
                   "used by no exclusion theorem"),
    "forms": [settled_form(1), settled_form(2)],
    "lean": [L(AS, "rt1_exclusion", "sufficient", "H.rt1_exclusion: 7h's grant exclusion re-proved on ScnP (H_SETTLED replaced by H_PIN)"),
             L(AS, "rt2_exclusion_arcs", "sufficient", "H.rt2_exclusion_arcs on ScnP"),
             L(AS, "rt1_exclusion2", "sufficient", "J.rt1_exclusion2 on Scn2P"),
             L(AS, "rt2_exclusion2_arcs", "sufficient", "J.rt2_exclusion2_arcs on Scn2P"),
             L(AS, "q_hi", "lemma", "H.q_hi: q stays 1 under H_PIN (FS_r1q / FS_hold on ustate's real INIT; the flat O6 arc cancels)"),
             L(AS, "q_lo2", "lemma", "J.q_lo2: the 7j mirror"),
             L(AS, "q_glitch2", "counter_trace", "J.q_glitch2, every record: t0 + wr2s < ta + wa0s (H_PIN violated) and A0 low there => q rises at "
               "t0 + wr2s + qr, before QBb (necessary for the q trace; that the early q edge breaks exclusion is NOT shown)"),
             L(AS, "q_glitch", "counter_trace", "H.q_glitch: q falls early when t0 + wr1s + qf < ta + wa0s + qr; with qr = qf (every Real7 record) "
               "this is exactly not H_PIN"),
             L(AS, "ScnP", "definition"), L(AS, "Scn2P", "definition"),
             L(AS, "ofScn", "lemma", "H.ofScn: H_SETTLED => H_PIN"), L(AS, "ofScn2", "lemma"),
             L(AS, "strict_witness", "non_vacuity", "W1p / W2p (7j's W1 / W2 with A0 rising at -50) meet ScnP / Scn2P while both conjuncts of "
               "H_SETTLED fail: H_PIN is strictly weaker (D0 corner-mixed: satisfiability only)"),
             L(AS, "settledP1_of_causal", "sufficient", "Caus1 + H_ARC_P => H_PIN"),
             L(AS, "settledP2_of_causal", "sufficient"),
             L(AS, "settledP1_nonvacuous", "non_vacuity", "on W1c at L = 0"),
             L(AS, "settledP_safe", "corner", "setTbl2's L: H_PIN for every realization at kappa <= kappaS2, 72 clients"),
             L(AS, "set2_cert", "numbers"), L(AS, "setTbl2_max", "numbers", "502361 fs"), L(AS, "setTbl2_pos", "numbers", "21 positive entries"),
             L(AS, "settledP_tight", "corner", "each positive entry violated at L - 10 fs for every kappa >= kappaS2"),
             L(AS, "settledP_L0_fails", "corner", "L = 0 fails on exactly the 21"),
             L(AS, "design_gate_held_sharp", "corner", "OnGcdArbKappaSrv's four handover conclusions on ScnP / Scn2P"),
             L(AS, "design_gate_held_sharp_causal", "corner", "the same with H_PIN from a causal run at latency >= setTbl2 + H_RK_ROUTE"),
             L(AS, "link_pin1", "sufficient", "link clients (merge10 client 1, 4 seeds): H_PIN for every kappa <= kappaS2, no latency hypothesis"),
             L(AS, "link_pin2", "sufficient", "link clients, client 2 (14 instances)"),
             L(AS, "design_link_discharged1", "corner", "A- and g-exclusion handover conclusions for the discharged link instances"),
             L(AS, "design_link_discharged2", "corner"),
             L(AS, "link_short", "counter_trace", "seed 3 / seed 4 merge2.uarb1 client 2: the O6 arc alone (zero ack route) violates the form at kappaS2"),
             L(AS, "link_caus1_nonvacuous", "non_vacuity", "LinkExact's P0 witness composed with W1c shifted by 5244 ps, latency 45"),
             L(NW, "settled1_of_causal", "sufficient", "Bbare's coarser form: Caus1 + H_ARC (wa0s + qf <= wa01 + c1r + L) + H_ARC2 => 7h's H_SETTLED"),
             L(NW, "settled2_of_causal", "sufficient"),
             L(NW, "A1_rise_after", "lemma", "from ua1's real INIT: A1's rise is >= ta + wa01 + c1r"),
             L(NW, "A2_rise_after", "lemma"),
             L(NW, "settled1_nonvacuous", "non_vacuity"),
             L(NW, "settled_safe", "corner", "coarse form: setTbl's L (max about 1.59 ns)"),
             L(NW, "setTbl_max", "numbers"),
             L(NW, "settled_L0_fails", "corner", "coarse form: L = 0 fails for 65 of 72 clients"),
             L(NW, "design_gate_held_causal", "context", "OnGcdArbKappaSrv's D2 with H_SETTLED discharged by L >= setTbl"),
             L(NW, "scn_excludes_caus", "context", "7h's Scn asserts its settled state on the whole past: the derivation uses a separate causal run")],
    "exactness": "sufficient",
    "necessity_scope": ("H_PIN is NECESSARY FOR THE q TRACE (J.q_glitch2, every record; H.q_glitch, exactly not H_PIN when qr = qf, i.e. on "
                        "every Real7 record): violated, q moves early in every run. That the early q edge goes on to break grant / ack "
                        "exclusion is NOT shown, so for the row's obligation (exclusion) H_PIN is sufficient only. 7h with qr < qf: the gap "
                        "between H_PIN and the necessary condition is not decided. The gcd_hw latency table is tight to 10 fs "
                        "(settledP_tight) as a statement about the form, not about exclusion."),
    "exactness_note": ("Bbare (ArbNoWithdraw) derived 7h / 7j's H_SETTLED from causality (H_ARC: wa0s + qf <= wa0k + ckr + L) and found it "
                       "NOT implied by the extracted arcs (L up to 1.59 ns, 65 / 72 clients at L = 0). Bset (ArbSettled) replaces it by the "
                       "sharp pin form H_PIN (exact for the q trace, strictly weaker, implied by H_SETTLED) and re-proves 7h / 7j's whole "
                       "exclusion chain on it: need at most 502.361 ps on 21 / 72 clients, discharged for 18 of 20 link instances. It is "
                       "one of the two conditions under which D2 (0.2166) rather than D1 (0.0802) is gcd_hw's threshold. Missing arcs: the "
                       "routed interconnect A_k driver -> client ack pin and its site pin (every client), H_LUT6_O6 (link), the steer "
                       "release loop (cond_br, join, uack OR, H_SRC_HOLD) and the R0 clients' A0 C-join (H_A0_CJOIN)."),
    "hypotheses": ["7h / 7j Run (gate relations, real ustate / ua_k INITs), H_SERVER_MIN", "H_A0_LOW_BEFORE (A0 low on ua_k's A0-view window before ta)",
                   "H_CLIENT_LAT (client releases at t0 >= T + L_k)", "H_RK_ROUTE (rs_k <= wr_ks)",
                   "links: LinkExact Wf / Conj, H_ACK_RB, H_ACK_READ, H_SAME_CORNER, H_LUT6_O6",
                   "lit reading (H_SPREAD_CORRELATED) for the kappa results"],
    "site_pins": {"needed": True, "roles": ["ustate.I4 (A0) hi", "ua_k A0 pin lo", "client ack pin lo", "ustate.I0 / I1 (r_k) lo"]},
    "rule": {"rule": "none", "verdict": "none",
             "detail": ("UNCHECKED by any project rule (cells/verify/arb_fork.py checks rule J, the A0 FALL fork, only). Proposed in "
                        "B-arb-settled.md as rule J+ (rise-side twin of J: one linear row per client, LOOP_k's arcs summed at their lower "
                        "bounds, setTbl2's L_k as the required latency for clients without a cell model); not a project rule")},
    "corner": {"mode": "1C", "rule": ref["corner"]["rule"], "note": "every arc, LOOP_k's included, at the SAME corner (H_SHARED_CORNER / H_SAME_CORNER)",
               "kappa": dict(copy.deepcopy({k: v for k, v in ref["corner"]["kappa"].items() if k != "results"}), results=[SET_RES])},
    "check_scope": "route_plus_env",
    "evidence": "setTbl2 (ps, kappaS2, seeds 2/3/4/d) in B-arb-settled.md section 2; Bar's extraction UNTRUSTED; no routed SDF / FASM of gcd_hw on this machine",
    "status": "proved",
    "combine": "all",
})

# D2's dependence on no-withdrawal (steer rows) and H_SETTLED, on the 12 rows carrying Bsrv's D1 / D2
D2_DEP = ("Bbare (B-arb-no-withdraw.md, ArbNoWithdraw): D2 (0.2166) is gcd_hw's threshold only CONDITIONALLY. (a) No client may withdraw an "
          "unacknowledged request: in C's network model none does (gcd_hw_arb_no_withdraw, a corollary of C's gcd_hw_protocol; one instant, "
          "one wire, so nothing about pin skew); at gate level links do not withdraw under LinkExact's Conj (link_no_withdraw), steers under "
          "bd_steer.bundled_s_setup / bundled_s_hold plus the named H_SRC_HOLD (steer_no_withdraw), R0 clients only if their own clients do; a "
          "violated steer select setup row produces precisely D1's withdrawn request (steer_withdraws, a 100 ps pulse). The steer rows' routed "
          "status is not re-checked. (b) H_SETTLED, sharp form H_PIN (bd_arbiter.settled_rise; ArbSettled): not implied by the extracted arcs "
          "(settledP_L0_fails: 21 of 72 clients need up to 502 ps), discharged for 18 of 20 link instances (design_link_discharged1 / 2). "
          "design_gate_held_sharp_causal is D2 with H_PIN discharged by L >= setTbl2. Neither (a) nor (b) is established on the routes.")
nd2 = 0
for e in C:
    k = e["corner"].get("kappa")
    if not k or not any(s.startswith("Bsrv (B-gcd-arb-kappa-srv.md") for s in k.get("results", [])):
        continue
    k["results"].append(D2_DEP)
    add_lean(e, [L(NW, "steer_withdraws", "counter_trace", "a violated steer setup row: a 100 ps unacknowledgeable request (D1's withdrawn r2)"),
                 L(NW, "steer_no_withdraw", "lemma", "steer branch held until TA + pr.lo under H_SETUP_PIN / H_HOLD_PIN / H_SRC_HOLD"),
                 L(NW, "link_no_withdraw", "lemma", "link ctl request held until ack_out's rise can be read, under LinkExact's Conj"),
                 L(NW, "gcd_hw_arb_no_withdraw", "context", "C's network model: no arbiter request withdraws"),
                 L(NW, "design_gate_held_causal", "corner", "D2 with H_SETTLED discharged by L >= setTbl"),
                 L(AS, "design_gate_held_sharp_causal", "corner", "D2 with the sharp H_PIN discharged by L >= setTbl2"),
                 L(AS, "settledP_L0_fails", "corner", "H_PIN at L = 0 fails on 21 of 72 clients"),
                 L(AS, "design_link_discharged1", "corner"), L(AS, "design_link_discharged2", "corner")])
    nd2 += 1
assert nd2 == 12, nd2
LOG.append(f"{nd2} bd_arbiter rows: corner.kappa.results + D2's no-withdrawal / H_SETTLED dependence (ArbNoWithdraw)")
for rid in ("bd_steer.bundled_s_setup", "bd_steer.bundled_s_hold"):
    e = BY[rid]
    add_lean(e, [L(NW, "steer_withdraws", "context", "gcd_hw: a violated steer setup row is exactly D1's withdrawn arbiter request (100 ps pulse)"),
                 L(NW, "steer_no_withdraw", "context", "with the per-pin rows and H_SRC_HOLD the selected branch never withdraws")])
    note_append(e, "Bj8 (Bbare, ArbNoWithdraw): in gcd_hw 9 steers drive arbiter requests; a violated select row makes the unselected "
                "branch a short request no arbiter can acknowledge (steer_withdraws), which is the race behind D1 = 0.0802; D2 = 0.2166 "
                "needs these rows on the routes (not re-checked).")
    LOG.append(f"{rid}: note + steer_withdraws / steer_no_withdraw (D2 dependence)")

# 7h / 7j first-handover scope on the held-arbiter rows
SCN = {"ArbHeldTimed.lean": ("scn_excludes_caus", "7h's Scn"), "ArbHeldTimed2.lean": ("scn2_excludes_caus", "7j's Scn2")}
nhs = 0
for e in C:
    if e["cell"] != "bd_arbiter":
        continue
    used = sorted({r["file"].split("/")[-1] for r in e["lean"]} & set(SCN))
    if not used:
        continue
    names = [SCN[f][0] for f in used]
    e["handover_scope"] = (
        "FIRST HANDOVER (Bbare, ArbNoWithdraw." + " / ".join(names) + "): " + " and ".join(SCN[f][1] for f in used) +
        " assert the settled initial state on the WHOLE past (e.g. A1 low for every t < t0), so no trace in which that client was ever "
        "acknowledged before t0 meets them: the theorems behind this row cover the first handover from reset, not repeated ones. "
        + ("Repeated handovers: ArbMultiToken (Barb2) splices a stylised settled past onto the run (splice_run) and gives windowed "
           "one-handover theorems (win1, win2) and grant exclusion over infinitely many alternating handovers (mt_exclusion), under H_M, "
           "H_SLOW_REREQ, H_HOLD and four-phase clients; early re-request, solo / idle / from-reset schedules open."
           if e["id"] in ("bd_arbiter.rt1", "bd_arbiter.rt1b") else
           "Not re-proved for repeated handovers (ArbMultiToken uses RT2 / A0 forks only internally, not packaged as a theorem)."))
    add_lean(e, [L(NW, n, "context", "the scenario's settled state is asserted on the whole past: first handover only") for n in names])
    nhs += 1
assert nhs >= 12, nhs
LOG.append(f"{nhs} bd_arbiter rows: handover_scope (7h / 7j first handover, scn_excludes_caus)")
cv["handover_scope"] = ("optional (Bj8): on rows backed by 7h / 7j (ArbHeldTimed / ArbHeldTimed2): which handovers the cited theorems cover. "
                        "Scn / Scn2 assert the settled state on the whole past (ArbNoWithdraw.scn_excludes_caus), so they cover the first "
                        "handover from reset; ArbMultiToken's windowed theorems extend grant exclusion (RT1 / RT1b) to alternating contention.")

# ------------------------------------------------------------------ (4) c_contract H_ARB_EXCL: held arbiter derivable (Barb2)
MT_REFS = [L(MT, "H_ARB_EXCL_of_mt", "sufficient", "C's H_ARB_EXCL verbatim on Nat traces n -> g(sigma n), any sampling sigma >= B0, held arbiter"),
           L(MT, "mt_exclusion", "sufficient", "(g1 t && g2 t) = false for every t >= B0, over infinitely many handovers"),
           L(MT, "H_ARB12_of_mt", "lemma", "C's H_ARB1, H_ARB2, H_ARB_EXCL at 1 ps ticks, under CX (strict RT1, one-tick causality, H_GRANT_IN_A0_LOW)"),
           L(MT, "win1", "lemma", "windowed one-handover theorem, client 1 releases"), L(MT, "win2", "lemma"),
           L(MT, "splice_run", "lemma"),
           L(MT, "mt_nonvacuous", "non_vacuity", "periodic 48 ps run over Z, every delay nonzero, two handovers per period, CX included")]
HELD_CC = {"field": "H_ARB_EXCL (C's AMergeC / IpowCells Contract: no tick with both grants high, every tick of the run)",
           "status": "needs_extra_hypothesis",
           "extra": ("MTRun (H_ORD, H_SLOW_REREQ TA2 + 4M <= u, H_HOLD u + 2M <= t0 (k+1), H_A0, four-phase clients without withdrawal "
                     "H_REQ1 / H_REQ2, settled H_INIT / H_R0_INIT) and H_M (M bounds every route + arc read offset), with RT1, RT2, RT1b, RT2b "
                     "in arc form"),
           "lean": ["ArbMultiToken.H_ARB_EXCL_of_mt", "ArbMultiToken.mt_exclusion", "ArbMultiToken.H_ARB12_of_mt",
                    "ArbMultiToken.mt_nonvacuous", "ContractBridge.arb_excl_not_derivable"],
           "basis": ("DERIVABLE as C states it for the HELD bd_arbiter (what gcd_hw instantiates): H_ARB_EXCL_of_mt, from mt_exclusion "
                     "(induction over handovers on windowed one-handover theorems), under the extra hypotheses; H_ARB1 / H_ARB2 also at 1 ps "
                     "ticks under CX (H_ARB12_of_mt). This does not contradict ContractBridge.arb_excl_not_derivable, which concerns the BARE "
                     "bd_arbcell (no hold) in B's per-pin box. H_SLOW_REREQ and H_HOLD use the coarse M: sufficient, not tight. NOT derived: "
                     "early re-request (three extra races named in B-arb-multi-token.md, not proved), solo / idle / from-reset schedules, "
                     "H_AMERGE_RTZ (B's model has no z_req), C's initial fields i1 / i2 / ix / iy: C's AMerge is still not instantiated.")}
for rid in ("bd_arbiter.rt1", "bd_arbiter.rt1b"):
    e = BY[rid]
    assert e["c_contract"]["status"] == "not_derivable", rid
    add_lean(e, MT_REFS)
    e["c_contract"] = copy.deepcopy(HELD_CC)
    LOG.append(f"{rid}: c_contract H_ARB_EXCL not_derivable -> needs_extra_hypothesis (derivable for the held arbiter, H_ARB_EXCL_of_mt)")
for rid in ("bd_arbcell.settled_exclusion", "bd_arbcell.handover_overlap"):
    e = BY[rid]
    cc = e["c_contract"]
    assert cc["status"] == "not_derivable", rid
    add_lean(e, [L(MT, "H_ARB_EXCL_of_mt", "context", "the HELD arbiter (bd_arbiter) does give C's H_ARB_EXCL under MTRun; the bare cell does not")])
    cc["lean"].append("ArbMultiToken.H_ARB_EXCL_of_mt")
    cc["basis"] = cc["basis"].replace(" (a multi-token arbiter theorem, i.e. the board's open 8% overlap question, is missing).",
                                      ".") + (" Bj8 (Barb2): this row is the BARE cell, for which H_ARB_EXCL stays NOT derivable "
                                              "(arb_excl_not_derivable). For the held bd_arbiter it IS derivable as C states it under "
                                              "multi-token hypotheses (ArbMultiToken.H_ARB_EXCL_of_mt; see bd_arbiter.rt1 / rt1b's "
                                              "c_contract). The bare cell's overlap question is out of that theorem's scope.")
    assert "Bj8 (Barb2)" in cc["basis"]
    LOG.append(f"{rid}: c_contract stays not_derivable (bare cell); basis points to H_ARB_EXCL_of_mt for the held arbiter")

# ------------------------------------------------------------------ (5) RT_FB: IpowCellsT's Gap.gap_exact (Bfc)
GAP = [L(ICT, "gap_exact", "exact_inner", "Gap.gap_exact: the exact form of C's timed feedback contract FbCelT (H_RT_FB on a pinned route): "
         "2-input C-element, environment answering g ticks after the output edge, transport feedback route of delay d >= 1: FbCelT <-> d <= g "
         "(tcheck Rc's fb_hi <= resp_lo), while the SI step and the old FbCel hold for every g"),
       L(ICT, "gap_reject", "counter_trace", "Gap.gap_reject: no route with hi > g meets FbCelT"),
       L(ICT, "si_not_fbCelT", "context", "Gap.si_not_fbCelT: at g = 0 the SI step holds but no route meets FbCelT")]
for rid in ("bd_c2.env_latency", "bd_c2n.env_latency", "bd_c3.env_latency", "bd_c4.env_latency"):
    e = BY[rid]
    assert "RT_FB" in e["rule"]["detail"], rid
    refs = copy.deepcopy(GAP)
    if rid != "bd_c2.env_latency":
        refs[0]["role"] = "context"
        refs[0]["note"] += " (proved for the 2-input cgate only; for this cell an analogy, not a theorem)"
    add_lean(e, refs)
    note_append(e, "Bj8 (Bfc, IpowCellsT): C-side RT_FB. IpowCells' FbCel had no timing content (ContractBridge.fbCel_iff_si); "
                "FbCelT pins the route, and Gap.gap_exact is its exact form (FbCelT <-> d <= g, fb_hi <= resp_lo) on the gap run"
                + ("." if rid == "bd_c2.env_latency" else ", proved for the 2-input C-element only."))
    LOG.append(f"{rid}: RT_FB exact form IpowCellsT.gap_exact ({refs[0]['role']})")

doc["produced_by"] = (doc["produced_by"].rstrip() +
    " Updated by probe Bj8 (2026-10-29) from B-necessity6.md (Necessity6*: uj1 / muxn max forms and rst_lines boundary-tight, S_XA_J.2), "
    "B-zero-delay-tok.md (new row bd_link.stage_rearm, H_REARM), B-arb-no-withdraw.md + B-arb-settled.md (new row bd_arbiter.settled_rise, H_SETTLED in its sharp form H_PIN; D2's "
    "no-withdrawal dependence; handover_scope), B-arb-multi-token.md (c_contract H_ARB_EXCL derivable for the held arbiter) and "
    "B-ipow-cells-t.md (RT_FB: gap_exact); the 'probe Bj8' section of cell_constraints.bj5.py.")

# ================================================================== probe Bj9 (2026-10-29)
# Fifth Bj pass of the day. Applies, from today's committed notes (and JOURNAL-B.md progress 10:05 / 10:12 / 10:18):
#   B-necessity7.md (Necessity7Mux / Necessity7MuxRuns / Necessity7MuxRunsN / Necessity7MuxN / Necessity7MuxNRuns: gate-aware H_DEP,
#     S_XA_FORK / S_XA_J.1 / S_A_FORK not necessary, replacement rows S_XA_SEQ, S_XA_R, S_A_SEQ, S_A_R),
#   B-kleene-win-bound.md (KleeneWinBound: '+W under H_W_BOUND' backed per row family; C-element rows +W + Wq),
#   B-self-audit5.md (SelfAuditB8, JSON items: a0_fork handover_scope basis, gap_exact role, rt1 / rt1b c_contract basis).
# Every name cited below is declared in the cited file (the validator greps each one).
LOG.append("---- probe Bj9")
N7, N7R, N7RN, N7N, N7NR, WB = ("Necessity7Mux", "Necessity7MuxRuns", "Necessity7MuxRunsN", "Necessity7MuxN", "Necessity7MuxNRuns",
                               "KleeneWinBound")
N7_BIN = ("Binary '<=' model (OpsTimedMux / MuxN3Timed: H_LUT_FIFO lumped LUT arcs, FIFO wires, line FIFO, port-level causal partners "
          "with minimum latencies, real INITs), with Lt5's gate-aware C-element run (cel_run_g: H_DEP asked only in gate-on tokens, an "
          "ORDER fact after a gate-off token). No strict +1 claimed (strict_pending). Every boundary is one parameter point, binary "
          "'<=' at slack 1; none is an iff.")
N7_PEND = ("input-against-input order / own-feedback race of a replacement form (Bnx7): the +1 of CElemStrict was NOT re-proved for "
           "these forms; Bnx7's pass runs sit at binary equality (passA5, passN5, passN7) and with a Kleene X window a same-tick "
           "hand-over is likely X. A checker may add +1 (sufficient, stronger than the '<=' form), not shown necessary.")
iso = BY["bd_mux.isochronic_forks"]
ujl = BY["bd_mux.uxa_join_latency"]
izk = BY["bdc_muxn.iso_zack"]
assert iso["exactness"] == ujl["exactness"] == izk["exactness"] == "sufficient"

def bin_form(f, note):
    g = copy.deepcopy(f)
    g["margin_ps"] = 0
    g["note"] = note
    return g

def seq_form(fork, ack, pin_note):
    g = copy.deepcopy(fork)
    g["data_paths"] = [g["data_paths"][0][:2]]
    assert g["data_paths"][0][0]["kind"] == "wire" and g["data_paths"][0][1]["kind"] == "site_pin", ack
    g["launch"] = "z_ack edge at its driver (the fall that ends the previous token of another input)"
    g["margin_ps"] = 0
    g["note"] = pin_note
    return g

def n_form(ack, lut_sym, fb_sym, ack_wire, client, env, envspec, req_wire, req_pin, join, jlut, jwire, jpin):
    lp = f"{ack}.{{I0|I1}}"
    return {"launch": f"the edge at {ack}'s inputs that moves its node (node-launched: the client loop)",
            "data_paths": [[{"kind": "lut_arc", "from": lp, "to": f"{ack}.O6", "lean_sym": f"{lut_sym}.hi"},
                            {"kind": "feedback_wire", "from": f"{ack}.O6", "to": f"{ack}.I2", "lean_sym": fb_sym},
                            {"kind": "site_pin", "from": f"{ack}.I2@pip", "to": f"{ack}.I2", "pin_role": "feedback"}]],
            "request_paths": [[{"kind": "lut_arc", "from": lp, "to": f"{ack}.O6", "lean_sym": f"{lut_sym}.lo"},
                               {"kind": "wire", "from": f"{ack}.O6", "to": client, "lean_sym": f"{ack_wire}.lo"},
                               {"kind": "env", "name": env, "spec": envspec, "lean_sym": env},
                               {"kind": "wire", "from": req_pin[0], "to": f"{join}.I0", "lean_sym": f"{req_wire}.lo"},
                               {"kind": "site_pin", "from": f"{join}.I0@pip", "to": f"{join}.I0", "pin_role": req_pin[1]},
                               {"kind": "lut_arc", "from": f"{join}.I0", "to": f"{join}.O6", "lean_sym": f"{jlut}.lo"},
                               {"kind": "wire", "from": jwire[0], "to": f"{ack}.I0", "lean_sym": f"{jwire[1]}.lo"},
                               {"kind": "site_pin", "from": f"{ack}.I0@pip", "to": f"{ack}.I0", "pin_role": jpin}]],
            "margin_ps": 0}

def n7_row(base, rid, obligation, inequality, forms, lean, exactness, note, scope=None, combine="all", groups=None, extra_hyp=()):
    r = {"id": rid, "cell": base["cell"], "catalogue_row": "none (Bnx7, formal/notes/B-necessity7.md)",
         "obligation": obligation, "inequality": inequality, "forms": forms, "lean": lean, "exactness": exactness,
         "exactness_note": note + " " + N7_BIN,
         "site_pins": copy.deepcopy(base["site_pins"]), "rule": {"rule": "none", "verdict": "none", "detail": "UNCHECKED"},
         "corner": copy.deepcopy(base["corner"]), "check_scope": "route_plus_env", "status": "proved", "combine": combine,
         "strict_pending": N7_PEND,
         "hypotheses": ["H_LUT_FIFO (lumped LUT arcs)", "port-level causal partners, minimum latencies (MuxCausal / MN3Causal)",
                        "real INITs", "server latency Es >= 1"] + list(extra_hyp)}
    if groups is not None:
        r["combine_groups"] = groups
    if scope:
        r["necessity_scope"] = scope
    if "also_applies_to" in base:
        r["also_applies_to"] = copy.deepcopy(base["also_applies_to"])
    return r

MUX_SUFF = [L(N7, "mux_ok_gs", "sufficient", "mux_ok's whole conclusion (MuxConcl: joins, z_req, both acks in both indexings, order) from "
              "MuxGates + MuxEnv + MuxCausal + 1 <= Es + MuxStaticG + MuxRstG"),
            L(N7, "mux_timing_g_of_static", "sufficient", "MuxTimingG from MuxCausal + MuxStaticG + reset"),
            L(N7, "mux_ok_g", "sufficient", "event form: H_DEP_XA / YA asked only in the owner's tokens, H_SEQ_XA / YA added"),
            L(N7, "MuxStaticG", "definition", "MuxStatic minus S_XA_FORK, S_XA_J.1, S_OR (and y mirrors), plus S_XA_SEQ, S_XA_R"),
            L(N7, "MuxTimingG", "definition"), L(N7, "MuxRstG", "definition", "reset sequencing: only z_ack's first edge must follow reset release at uxa / uya"),
            L(N7, "staticG_of_static", "lemma", "the shipped MuxStatic implies MuxStaticG"),
            L(N7, "MuxTiming.g", "lemma", "the old event form implies the gate-aware one"),
            {"file": "formal/lean/Formal/Cells/OpsTimedMux.lean", "name": "MuxCausal", "role": "definition"}]
MUXN_SUFF = [L(N7N, "muxn3_ok_gs", "sufficient", "MN3Concl (muxn3_ok's whole conclusion) from the gates, env, MN3Causal, MN3StaticG; FASTFALL line "
               "flush and 1 <= N taken as given"),
             L(N7N, "muxn3_timing_g_of_static", "sufficient"), L(N7N, "muxn3_ok_g", "sufficient", "event form, H_DEP_A only in input i's tokens, H_SEQ_A added"),
             L(N7N, "MN3StaticG", "definition", "MN3Static minus S_A_FORK, S_A_J.1, plus S_A_SEQ, S_A_R"), L(N7N, "MN3TimingG", "definition"),
             L(N7N, "staticG_of_static", "lemma", "the shipped MN3Static implies MN3StaticG"), L(N7N, "MN3Timing.g", "lemma"),
             {"file": "formal/lean/Formal/Cells/MuxN3Timed.lean", "name": "MN3Causal", "role": "definition"}]

# ---- bd_mux: S_XA_SEQ / S_XA_R (boundary), S_YA_SEQ / S_YA_R (sufficient)
KC = "Kc = Wzc.lo + Ec + wc + lj"
MUX_RST = ["MuxRstG (reset sequencing: only z_ack's first edge must follow reset release at uxa / uya)"]
KZ = "Kz = wo + Lor.lo + Dz.lo + Es"
mux_rows = {}
for a in ("x", "y"):
    A, ack, j, J = a.upper(), f"u{a}a", ("j0" if a == "x" else "j1"), ("uj0" if a == "x" else "uj1")
    Wz, La, wh, Wj, Wa, E, Wr, Lj = (("Wzx", "Lxa", "wxah", "W0x", "Wxa", "Ex", "Wx", "Lj0") if a == "x" else
                                     ("Wzy", "Lya", "wyah", "W1y", "Wya", "Ey", "Wy", "Lj1"))
    fk = iso["forms"][0 if a == "x" else 1]
    j1f = ujl["forms"][0 if a == "x" else 2]
    assert fk["note"] == f"S_{A}A_FORK" and j1f["note"].startswith(f"S_{A}A_J (1)"), (fk["note"], j1f["note"])
    other = "y" if a == "x" else "x"
    seq = n7_row(iso, f"bd_mux.u{a}a_seq",
                 f"S_{A}A_SEQ (Necessity7Mux.MuxStaticG): across a {other} -> {a} hand-over, z_ack's fall (end of the {other} token) reaches "
                 f"{ack} no later than the {a} token's {j} rise, launched by the same fall through the control sender (order only, no loop term)",
                 f"{Wz}.hi <= Kc + {Wj}.lo; {KC}",
                 [seq_form(fk, ack, f"S_{A}A_SEQ")], [], "sufficient", "", extra_hyp=MUX_RST)
    rr = n7_row(ujl, f"bd_mux.u{a}a_r",
                f"S_{A}A_R (Necessity7Mux.MuxStaticG): in a {a} token, {ack}'s loop settles before {j}'s next REAL edge reaches {ack}, "
                f"through the {a} client (S_{A}A_N, node-launched) or through the control sender (the shipped pair S_{A}A_FORK and "
                f"S_{A}A_J.1); the same edge is causally after BOTH paths because the join waits for ctl_req too",
                f"S_{A}A_N OR (S_{A}A_FORK AND S_{A}A_J.1): S_{A}A_N {La}.hi + {wh} <= {La}.lo + {Wa}.lo + {E} + {Wr}.lo + {Lj}.lo + {Wj}.lo; "
                f"S_{A}A_FORK {Wz}.hi + {La}.hi + {wh} <= Kc + {Wj}.lo; S_{A}A_J.1 {Wj}.hi + {La}.hi + {wh} <= Kz + Kc + {Wj}.lo; {KC}, {KZ}",
                [n_form(ack, La, wh, Wa, f"{a} client", E, f"{a} client: ack edge seen -> request edge (MuxCausal), min", Wr,
                        (f"{a}_req", f"{a}_req"), J, Lj, (j, Wj), j) | {"note": f"S_{A}A_N (group 0)"},
                 bin_form(fk, f"S_{A}A_FORK, binary (group 1, with form 2)"),
                 bin_form(j1f, f"S_{A}A_J.1, binary (group 1, with form 1)")],
                [], "sufficient", "", combine="any", groups=[[0], [1, 2]], extra_hyp=MUX_RST)
    mux_rows[a] = (seq, rr)

sx, rx = mux_rows["x"]
sx["lean"] = MUX_SUFF + [
    L(N7R, "ClaimSEQ", "definition", "mux_ok_gs with S_XA_SEQ weakened by s (MuxStaticW ... s 0), every other hypothesis verbatim"),
    L(N7R, "MuxStaticW", "definition"), L(N7R, "claimSEQ0", "sufficient", "ClaimSEQ 0 = mux_ok_gs's hypothesis set"),
    L(N7R, "failSEQ6", "counter_run", "RA.run 6 uW (z_ack -> uxa wire 6 ticks, every other LUT / wire 1, Ex = Ey = Ec = Es = 1, reset on [0, 12), "
      "x / y alternating, period 23): every field of MuxStaticW ... 1 0 holds, S_XA_SEQ off by exactly 1 (6 = 5 + 1)"),
    L(N7R, "claimSEQ1_false", "counter_trace", "not ClaimSEQ 1: z_ack (still high from y token 1) and j0 (x token 2) both high at uxa at 69; "
      "x_ack = 1 at 71 inside [XA 2, XA 3) = [57, 72)"),
    L(N7R, "passA5", "non_vacuity", "RA.run 5 uW meets MuxStaticG with S_XA_SEQ at equality (5 <= 5) and the whole conclusion")]
sx["exactness"] = "sufficient+necessary_at_boundary"
sx["necessity_scope"] = ("one parameter point (RA.run 6, unit delays elsewhere, open-loop periodic environment), binary '<=' at slack 1; no "
                         "strict +1 claimed (strict_pending)")
sx["exactness_note"] = ("Bnx7 (B-necessity7.md): replacement (with bd_mux.uxa_r) of bd_mux.isochronic_forks' S_XA_FORK. Sufficient "
                        "(mux_ok_gs) and necessary at the boundary (claimSEQ1_false). The hand-over order the shipped fork form implied "
                        "(staticG_of_static: S_XA_FORK implies S_XA_SEQ). " + N7_BIN)
rx["lean"] = MUX_SUFF + [
    L(N7R, "ClaimR", "definition", "mux_ok_gs with every inequality of S_XA_R weakened by s (MuxStaticW ... 0 s)"),
    L(N7R, "claimR0", "sufficient", "ClaimR 0 = mux_ok_gs's hypothesis set"),
    L(N7RN, "failR6", "counter_run", "RN.run 6 (uxa feedback net 6 ticks, tight clients): every field of MuxStaticW ... 0 1 holds; S_XA_R false "
      "(S_XA_N off by exactly 1, 7 = 6 + 1; S_XA_FORK off by 3)"),
    L(N7RN, "claimR1_false", "counter_trace", "not ClaimR 1: j0's fall reaches uxa at 33 before the feedback shows x_ack's rise (node at 28); "
      "x_ack = 0 at 35 inside [XA 0, XA 1) = [29, 44)"),
    L(N7RN, "passN5", "non_vacuity", "RN.run 5 meets S_XA_N with equality (6 <= 6) while S_XA_FORK fails (1 + 6 <= 5 false): passes"),
    L(N7RN, "passB", "non_vacuity", "RB.run (j0 -> uxa wire 1 tick on rises, 8 on falls): S_XA_J.1 fails, S_XA_N holds with 4 ticks of slack: passes")]
rx["exactness"] = "sufficient+necessary_at_boundary"
rx["necessity_scope"] = ("shown on the S_XA_N disjunct (group 0), at a point where the fork disjunct (group 1) also fails (failR6: S_XA_FORK off "
                         "by 3), so it refutes the weakened DISJUNCTION; one parameter point, binary '<=' at slack 1; whether a finer max "
                         "form (which input of uxa is late) is exact was not examined; no strict +1 claimed")
rx["exactness_note"] = ("Bnx7 (B-necessity7.md): replacement of bd_mux.isochronic_forks' S_XA_FORK and of bd_mux.uxa_join_latency's S_XA_J.1 "
                        "(which survive only as the conjunction inside this disjunction). Correction to Bnx6's unproved analysis: the client "
                        "loop alone is not the replacement, because in an x token j0's next edge is also causally after z_ack through the "
                        "control sender (the join waits for ctl_req's fall), so the shipped pair stays a valid sufficient branch. Sufficient "
                        "(mux_ok_gs), necessary at the boundary (claimR1_false). " + N7_BIN)
sy, ry = mux_rows["y"]
for r, nm in ((sy, "S_YA_SEQ"), (ry, "S_YA_R")):
    r["lean"] = MUX_SUFF + [L(N7R, "passA5", "non_vacuity", "MuxStaticG (both mirrors) holds on RA.run 5 uW")]
    r["exactness"] = "sufficient"
    r["exactness_note"] = (f"Bnx7 (B-necessity7.md): the uya mirror ({nm}), stated in MuxStaticG and covered by mux_ok_gs; NO run (no boundary, "
                           f"no pass run violating the shipped S_YA_FORK / S_YA_J.1): the uxa results apply by symmetry only. " + N7_BIN)
for r in (sx, rx, sy, ry):
    new_row(r)

e = relabel("bd_mux.isochronic_forks", "not_necessary",
            [L(N7R, "passA5", "not_necessary", "RA.run 5 uW: S_XA_FORK reads 5 + 2 <= 5 (false; by 3 in the strict form), MuxStaticG holds "
               "(S_XA_SEQ with equality) and mux_ok's whole conclusion follows (mux_ok_gs): every run at this point passes"),
             L(N7RN, "passN5", "not_necessary", "RN.run 5: S_XA_FORK 1 + 6 <= 5 false, S_XA_N with equality: passes"),
             L(N7, "mux_ok_gs", "sufficient", "the replacement's sufficiency"), L(N7, "staticG_of_static", "lemma", "the shipped form implies the replacement")],
            "Bnx7 (B-necessity7.md, Necessity7Mux*): NOT necessary, in the box sense: MuxStaticG (without S_XA_FORK / S_YA_FORK) is sufficient "
            "over every run (mux_ok_gs), and at passA5's / passN5's parameter points S_XA_FORK fails while every run passes. Replacement rows: "
            "bd_mux.uxa_seq (S_XA_SEQ, boundary, claimSEQ1_false), bd_mux.uxa_r (S_XA_R, boundary, claimR1_false) and the uya mirrors "
            "bd_mux.uya_seq / uya_r (sufficient, no run). S_YA_FORK's own non-necessity is by symmetry only. The untimed "
            "mux_needs_iso_* concern the isochronic-fork assumption of MergeMuxSI, not this timed inequality (re-roled context). "
            + N7_BIN, old_ok=("sufficient",))
e["replacement"] = "bd_mux.uxa_seq"
e["replacement_rows"] = ["bd_mux.uxa_seq", "bd_mux.uxa_r", "bd_mux.uya_seq", "bd_mux.uya_r"]
for r in e["lean"]:
    if r["name"].startswith("mux_needs_iso") and r["role"] == "necessary":
        r["role"] = "context"
        r["note"] = (r.get("note", "") + " (Bj9: untimed isochronic-fork assumption; the timed S_XA_FORK is not necessary, Bnx7)").strip()

e = relabel("bd_mux.uxa_join_latency", "not_necessary",
            [L(N7RN, "passB", "not_necessary", "RB.run (j0 -> uxa wire 1 on rises, 8 on falls): S_XA_J.1 reads 8 + 2 <= 4 + 4 + 1 (false; by 2 in "
               "the strict form), MuxStaticG holds (S_XA_N 4 ticks of slack, S_XA_J.2 10 <= 13): passes"),
             L(N7, "mux_ok_gs", "sufficient", "the replacement's sufficiency"), L(N7, "MuxStaticG", "definition", "S_XA_J.1 only inside S_XA_R")],
            "Bnx7 (B-necessity7.md): the first conjunct S_XA_J.1 is NOT necessary (passB with mux_ok_gs); it survives only inside the "
            "disjunct of bd_mux.uxa_r (S_XA_R). The second conjunct S_XA_J.2 is unchanged and still required (Bnx6: necessary at the "
            "boundary, claimJ1_false; boundary_tight_terms). The uya mirror S_YA_J.1 is replaced by bd_mux.uya_r (weaker, sufficient) by "
            "symmetry, no run; S_YA_J.2 still required. This supersedes Bnx6's 'S_XA_J.1 probably not necessary' (now proved). " + N7_BIN,
            old_ok=("sufficient",))
e["replacement"] = "bd_mux.uxa_r"
e["replacement_rows"] = ["bd_mux.uxa_r", "bd_mux.uya_r"]
e["replacement_scope"] = ("replaces forms 0 and 2 (S_XA_J.1, S_YA_J.1) only; forms 1 and 3 (S_XA_J.2, S_YA_J.2) are still required: a checker "
                          "evaluates forms 1 and 3 AND bd_mux.uxa_r / uya_r (with bd_mux.uxa_seq / uya_seq and the RTZ rows)")
btt = e["boundary_tight_terms"]
assert len(btt) == 1 and btt[0]["untouched"] == "S_XA_J.1 (form 0), uya forms 2 / 3"
btt[0]["untouched"] = ("uya forms 2 / 3 (S_YA_J.1 replaced by bd_mux.uya_r, S_YA_J.2 no run); S_XA_J.1 (form 0) is not necessary (Bnx7, "
                       "passB), replaced by bd_mux.uxa_r")

# ---- bdc_muxn: S_A_SEQ (boundary), S_A_R (sufficient)
fk, j1f = izk["forms"][0], izk["forms"][1]
assert fk["note"] == "S_A_FORK, per i" and j1f["note"].startswith("S_A_J (1)")
KCN = "Kc = Wzc.lo + Ec + (wc + ls + wsj + lj)"
sn = n7_row(izk, "bdc_muxn.ua_seq",
            "S_A_SEQ (Necessity7MuxN.MN3StaticG), per i: a token of input i after a token of another input: z_ack's fall reaches ua_i no "
            "later than j_i's rise, launched by the same fall through the control sender (order only)",
            f"Wza(i).hi <= Kc + Wja(i).lo; {KCN}", [seq_form(fk, "ua_i", "S_A_SEQ, per i")],
            MUXN_SUFF + [
                L(N7NR, "ClaimSEQn", "definition", "muxn3_ok_gs with S_A_SEQ weakened by s (MN3StaticW ... s 0), every other hypothesis verbatim"),
                L(N7NR, "MN3StaticW", "definition"), L(N7NR, "claimSEQn0", "sufficient", "ClaimSEQn 0 = muxn3_ok_gs's hypothesis set"),
                L(N7NR, "failSEQ8", "counter_run", "Mn7.run 8 (unit delays, DELAY = 1, all three z_ack -> ua_i wires 8 ticks, reset on [0, 9), token "
                  "k selects k % 3, period 27): every field of MN3StaticW ... 1 0 holds, S_A_SEQ off by exactly 1 (8 = 7 + 1)"),
                L(N7NR, "claimSEQn1_false", "counter_trace", "not ClaimSEQn 1: z_ack's fall of token 0 reaches ua_1 at 61, j_1's rise of token "
                  "1 at 60; in1_ack = 1 at 62 inside [XA 1 0, XA 1 1) = [46, 63)"),
                L(N7NR, "passN7", "non_vacuity", "Mn7.run 7: MN3StaticG with S_A_SEQ at equality and MN3Concl")],
            "sufficient+necessary_at_boundary",
            "Bnx7 (B-necessity7.md, Necessity7MuxN*): replacement (with bdc_muxn.ua_r) of bdc_muxn.iso_zack's S_A_FORK. Sufficient "
            "(muxn3_ok_gs), necessary at the boundary (claimSEQn1_false). DELAY > 1 not covered.",
            scope="one parameter point (Mn7.run 8, N = 1, DELAY = 1, input 1), binary '<=' at slack 1; no strict +1 claimed",
            extra_hyp=["FASTFALL line flush and 1 <= N taken as given"])
rn = n7_row(izk, "bdc_muxn.ua_r",
            "S_A_R (Necessity7MuxN.MN3StaticG), per i: in a token of input i, ua_i's loop settles before j_i's next real edge reaches ua_i, "
            "through client i (S_A_N, node-launched) or through the control sender (the shipped S_A_FORK and S_A_J.1)",
            "S_A_N OR (S_A_FORK AND S_A_J.1), per i: S_A_N La(i).hi + wah(i) <= La(i).lo + Wak(i).lo + Ex + Wx(i).lo + Lj(i).lo + Wja(i).lo; "
            "S_A_FORK Wza(i).hi + La(i).hi + wah(i) <= Kc + Wja(i).lo; S_A_J.1 Wja(i).hi + La(i).hi + wah(i) <= Kz + Kc + Wja(i).lo; "
            f"{KCN}, Kz = wo + Lo.lo + Dl + Es",
            [n_form("ua_i", "La", "wah", "Wak", "client i", "Ex", "client i: ack edge seen -> request edge (MN3Causal), min", "Wx",
                    ("in_i_req", "in_i_req"), "uj_i", "Lj", ("uj_i.O6", "Wja"), "j") | {"note": "S_A_N, per i (group 0)"},
             bin_form(fk, "S_A_FORK, per i, binary (group 1, with form 2)"),
             bin_form(j1f, "S_A_J.1, per i, binary (group 1, with form 1)")],
            MUXN_SUFF + [L(N7NR, "passN7", "non_vacuity", "MN3StaticG holds on Mn7.run 7 (S_A_FORK fails there, 7 + 2 <= 7, so S_A_R holds "
                                                          "through its S_A_N disjunct)")],
            "sufficient",
            "Bnx7 (B-necessity7.md): replacement of bdc_muxn.iso_zack's S_A_FORK and S_A_J.1 (now only a disjunct). Sufficient only: no "
            "muxn boundary run (it needs an environment with tight clients), and no pass run violating S_A_J.1 (it needs a spread Wja "
            "wire); neither was built.",
            combine="any", groups=[[0], [1, 2]], extra_hyp=["FASTFALL line flush and 1 <= N taken as given"])
new_row(sn); new_row(rn)
e = relabel("bdc_muxn.iso_zack", "not_necessary",
            [L(N7NR, "passN7", "not_necessary", "Mn7.run 7: S_A_FORK reads 7 + 2 <= 7 (false; by 3 in the strict form), MN3StaticG holds "
               "(S_A_SEQ with equality) and MN3Concl follows (muxn3_ok_gs): every run at this point passes"),
             L(N7N, "muxn3_ok_gs", "sufficient", "the replacement's sufficiency"), L(N7N, "staticG_of_static", "lemma", "the shipped form implies the replacement")],
            "Bnx7 (B-necessity7.md, Necessity7MuxN*): S_A_FORK is NOT necessary (passN7 with muxn3_ok_gs). Replacement rows: bdc_muxn.ua_seq "
            "(S_A_SEQ, boundary, claimSEQn1_false) and bdc_muxn.ua_r (S_A_R = S_A_N OR (S_A_FORK AND S_A_J.1), sufficient only). S_A_J.1 is "
            "now only a disjunct of S_A_R (its own non-necessity has no muxn run); S_A_J.2 unchanged (sufficient, no boundary run). The cited "
            "untimed mux_needs_iso_za is bd_mux's isochronic-fork assumption (re-roled context). " + N7_BIN, old_ok=("sufficient",))
e["replacement"] = "bdc_muxn.ua_seq"
e["replacement_rows"] = ["bdc_muxn.ua_seq", "bdc_muxn.ua_r"]
e["replacement_scope"] = ("replaces forms 0 and 1 (S_A_FORK, S_A_J.1) only; form 2 (S_A_J.2) is still required: a checker evaluates form 2 AND "
                          "bdc_muxn.ua_seq AND bdc_muxn.ua_r")
for r in e["lean"]:
    if r["name"] == "mux_needs_iso_za" and r["role"] == "necessary":
        r["role"] = "context"
        r["note"] = r.get("note", "") + " (Bj9: untimed isochronic-fork assumption; the timed S_A_FORK is not necessary, Bnx7)"
cv["combine"] = cv["combine"].rstrip() + (" Bj9: optional combine_groups (with 'any'): a list of groups of form indices; the obligation holds "
                                          "if EVERY form of ONE group holds (a disjunction of conjunctions: bd_mux.uxa_r = S_XA_N OR (S_XA_FORK "
                                          "AND S_XA_J.1)). Without it each form is its own group.")
cv["boundary_tight_terms"] = cv["boundary_tight_terms"].rstrip() + (" Bj9: also on a not_necessary row with replacement_scope, for the "
                                                                    "terms that stay required (bd_mux.uxa_join_latency: S_XA_J.2).")

# ------------------------------------------------------------------ (2) '+W under H_W_BOUND' per row family (Bwb, KleeneWinBound)
WB_OLD = ("Sufficient without the split: +W under H_W_BOUND (c_e + a_l <= W for every race pair): UNPROVED for this cell (stated by analogy; "
          "the only theorem is bd_steer's, SelfAuditB7.steer_win_bound).")
WB_STEER_OLD = ("Sufficient without the split: +W under H_W_BOUND (c_e + a_l <= W for every race pair): PROVED for bd_steer "
                "(SelfAuditB7.steer_win_bound; non-vacuity steer_win_bound_witness).")
WB_SRC = "Bwb, B-kleene-win-bound.md: KleeneWinBound"
WB_PAIR = ("pair reading: c_e + a_l <= W for every race pair, whatever the split")
WB_WIDTH_J = ("Width reading (H_W_EDGE: each edge's window contains its binary edge, 0 <= a_T, c_T, a_T + c_T <= W): a pair term can reach "
              "2W, so +2W is sufficient and needed (%s); with halves of free sign no finite margin suffices, even at width 0 "
              "(join_width_unbounded). So 'every window has width <= W' does NOT give +W.")
WB_GEN = [L(WB, "races_suff", "lemma", "generic: every race term <= W => binary-edge margins of +W are sufficient"),
          L(WB, "races_need", "lemma", "generic: a race term = W => a binary-edge margin below W on that race is unsafe (the iff's necessity half)")]
def wb_family(e):
    b, rid = e["strict"].get("backing", ""), e["id"]
    if "rst_dec" in b:
        return "rst"
    if rid.startswith("bd_steer."):
        return "steer"
    if rid.startswith("bd_mux.bundled_s_"):
        return "join"
    if rid.startswith("bdc_muxn.s_"):
        return "muxn"
    if rid.startswith("bd_latch[") and rid.split(".")[-1] in ("setup_pulse", "setup_data", "hold"):
        return "latch"
    assert b.startswith(("c2_all", "c2n_c8g", "c3_all", "c4_all", "latch_facts")), (rid, b)
    return "cel"
fam = Counter()
for e in C:
    st = e.get("strict")
    if not st or not st.get("margin_added_ps"):
        continue
    f = wb_family(e)
    fam[f] += 1
    xw = st["x_window"]
    if f == "steer":
        assert WB_STEER_OLD in xw, e["id"]
        k = "hold" if e["id"].endswith("hold") else "setup"
        new = (WB_STEER_OLD[:-1] + f"; {WB_SRC}.steer_win_bound'). Needed: a race pair whose term is exactly W makes a binary-edge "
               f"margin of W - 1 unsafe (steer_win_need_{k}; witness steer_bound_pair_witness, W = 2, non-uniform split). This is the "
               + WB_PAIR + ". " + (WB_WIDTH_J % "proved for the mux join and the latch: join_edge_bound / join_edge_need, latch_edge_bound / "
                                   "latch_edge_need; not stated for steer"))
        st["x_window"] = xw.replace(WB_STEER_OLD, new)
        add_lean(e, WB_GEN + [L(WB, "steer_win_bound'", "sufficient", "+W under the pair reading of H_W_BOUND (= SelfAuditB7.steer_win_bound)"),
                              L(WB, f"steer_win_need_{k}", "necessary", "a pair at exactly W: margin W - 1 unsafe"),
                              L(WB, "steer_bound_pair_witness", "non_vacuity", "W = 2, non-uniform split: safe at W, unsafe at W - 1"),
                              L(WB, "steer_races", "lemma", "steer's KleeneWin iff as a race list")])
        continue
    assert xw.count(WB_OLD) == 1, e["id"]
    if f == "rst":
        new = ("Sufficient without the split: +W under H_W_BOUND: UNPROVED for this row (Bwb, B-kleene-win-bound.md: the *_rst_dec backing is a Boolean "
               "reset-release decision, not a Facts cycle, and no per-edge reset iff exists, so races_suff does not apply; the earlier "
               "'by analogy' reading is not a theorem).")
    elif f == "join":
        k = "hold" if e["id"].endswith("hold") else "setup"
        new = ("Sufficient without the split: +W under H_W_BOUND (" + WB_PAIR + "): PROVED for the mux join (" + WB_SRC + ".join_win_bound); "
               f"needed: a pair at exactly W makes a binary-edge margin of W - 1 unsafe (join_win_need_{k}; witness join_bound_pair_witness, "
               "W = 2, non-uniform split). " + (WB_WIDTH_J % "join_edge_bound, join_edge_need: split c_e = a_l = W"))
        refs = [L(WB, "join_win_bound", "sufficient", "+W under the pair reading of H_W_BOUND"),
                L(WB, f"join_win_need_{k}", "necessary", "a pair at exactly W: margin W - 1 unsafe"),
                L(WB, "join_bound_pair_witness", "non_vacuity", "W = 2, non-uniform split: safe at W, unsafe at W - 1"),
                L(WB, "join_races", "lemma"),
                L(WB, "join_edge_bound", "context", "width reading: +2W sufficient"), L(WB, "join_edge_need", "context", "width reading: +2W needed"),
                L(WB, "join_width_unbounded", "context", "halves of free sign: no finite margin, even at width 0")]
    elif f == "muxn":
        new = ("Sufficient without the split: +W under H_W_BOUND (" + WB_PAIR + "): PROVED for the selected join (" + WB_SRC + ".muxn_win_bound, "
               "its 4 race pairs); needed: any of the 4 pairs at exactly W makes margin W - 1 unsafe (muxn_win_need; witness "
               "muxn_bound_witness, k = 1, W = 2). Unselected joins not covered. " + (WB_WIDTH_J % "proved for the mux join and the latch "
                                                                                      "only, not stated for bdc_muxn"))
        refs = [L(WB, "muxn_win_bound", "sufficient", "+W under the pair reading, 4 race pairs of the selected join"),
                L(WB, "muxn_win_need", "necessary", "any of the 4 pairs at exactly W: margin W - 1 unsafe"),
                L(WB, "muxn_bound_witness", "non_vacuity", "k = 1, W = 2"), L(WB, "muxn_races", "lemma")]
    elif f == "latch":
        k = {"setup_pulse": "pulse", "setup_data": "data", "hold": "hold"}[e["id"].split(".")[-1]]
        new = ("Sufficient without the split: +W under H_W_BOUND (" + WB_PAIR + "): PROVED for the latch (" + WB_SRC + ".latch_win_bound: "
               f"pulse, data, hold); needed: a pair at exactly W makes margin W - 1 unsafe (latch_win_need_{k}; witness "
               "latch_bound_pair_witness, W = 3, non-uniform split). " + (WB_WIDTH_J % "latch_edge_bound, latch_edge_need"))
        refs = [L(WB, "latch_win_bound", "sufficient", "+W under the pair reading (pulse, data, hold)"),
                L(WB, f"latch_win_need_{k}", "necessary", "a pair at exactly W: margin W - 1 unsafe"),
                L(WB, "latch_bound_pair_witness", "non_vacuity", "W = 3, non-uniform split"), L(WB, "latch_races", "lemma"),
                L(WB, "latch_edge_bound", "context", "width reading: +2W sufficient"), L(WB, "latch_edge_need", "context", "width reading: +2W needed")]
    else:
        new = ("Sufficient without the split: NOT +W. The own-feedback race's exact term is cf + wq + ar (cel_env_win_iff: the follow pin's "
               "trailing half, the feedback pin's own window wq, the release pin's leading half), and wq belongs to no race pair. Under "
               "H_W_BOUND (" + WB_PAIR + ") and H_FBW_BOUND (wq <= Wq) the bound is +W + Wq, sufficient and tight (" + WB_SRC +
               ".cel_env_win_bound: dlmax + dwmax + W + Wq <= dlmin + E; cel_env_win_need: for any split with cf + ar = W a margin below "
               "W + Wq is unsafe; explicit counter-run on any Facts cycle cel_win_ct; on the real bd_c2 INIT c2_win_ct / c2_win_clean: W = 2, "
               "wq = 1, clean at margin 3, hazard at 2). '+W' alone is sufficient only at wq = 0 (H_FB_PURE); +2W if Wq <= W is assumed "
               "(cel_env_win_bound_2W). Width reading (H_W_EDGE, 0 <= a_T, c_T, a_T + c_T <= W): +2W + Wq, i.e. +3W at Wq = W, sufficient and "
               "tight (cel_env_edge_bound, cel_env_edge_need). Caveat (not proved): that this row's inequality IS an instance of the Facts "
               "race (which edge is follow / release, what E is) is the row's existing strict.backing; composite rows carry it only as far "
               "as that mapping does.")
        refs = [L(WB, "cel_env_win_bound", "bound", "+W + Wq under the pair reading of H_W_BOUND and H_FBW_BOUND (wq <= Wq), any Facts cycle"),
                L(WB, "cel_env_win_need", "necessary", "of the window term: for any split with cf + ar = W, a margin below W + Wq is unsafe"),
                L(WB, "cel_env_win_bound_2W", "bound", "the special case Wq = W: +2W"),
                L(WB, "cel_env_edge_bound", "context", "width reading: +2W + Wq sufficient"),
                L(WB, "cel_env_edge_need", "context", "width reading: +2W + Wq needed"),
                L(WB, "cel_win_ct", "counter_trace", "every split, loop delay D = d + 1 and wq: margin cf + ar + wq - 1 wrong at the release window's start"),
                L(WB, "c2_win_ct", "counter_trace", "real bd_c2 INIT, W = 2, wq = 1, D = 420: hazard at margin 2"),
                L(WB, "c2_win_clean", "non_vacuity", "the same run clean at margin 3")]
        if e["id"] == "bd_fork.branch_data":
            refs.append(L(WB, "latch_win_bound", "context", "by the row's description (it is bd_latch.setup_data launched at the producer) the "
                          "latch bound applies too; that identification is the row's, not re-proved"))
    st["x_window"] = xw.replace(WB_OLD, new)
    if f != "rst":
        add_lean(e, WB_GEN + refs)
assert fam == Counter({"cel": 51, "latch": 9, "rst": 5, "steer": 2, "join": 2, "muxn": 2}), fam
LOG.append("strict.x_window '+W under H_W_BOUND' per family: " + ", ".join(f"{k} {v}" for k, v in sorted(fam.items())) +
           " (cel: +W + Wq; rst: stays UNPROVED)")
cv["strictness"] = cv["strictness"].rstrip() + (
    " Bj9 (Bwb, KleeneWinBound): '+W under H_W_BOUND' in strict.x_window is backed per row family under the PAIR reading (c_e + a_l <= W "
    "for every race pair): sufficient and needed for bd_steer (steer_win_bound', steer_win_need_*), the bd_mux join (join_win_bound, "
    "join_win_need_*), the bdc_muxn selected join (muxn_win_bound, muxn_win_need) and bd_latch (latch_win_bound, latch_win_need_*). The 51 "
    "C-element-backed (Facts own-feedback race) rows need +W + Wq (cel_env_win_bound / cel_env_win_need, Wq bounding the feedback pin's own "
    "window; '+W' only at wq = 0). Under the WIDTH reading (H_W_EDGE, halves non-negative) the bounds are +2W (join, latch: *_edge_bound / "
    "*_edge_need) and +2W + Wq = +3W at Wq = W (C-element); with halves of free sign no finite margin suffices (join_width_unbounded). The 5 "
    "rows backed by *_rst_dec keep 'UNPROVED' (not Facts cycles). W and Wq are unmeasured.")

# ------------------------------------------------------------------ (3) self-audit 5 (Bsa5) JSON items
A0F = "ArbA0Fork"
for k in (1, 2):
    e = BY[f"bd_arbiter.a0_fork_client{k}"]
    old_hs = e["handover_scope"]
    assert old_hs.startswith("FIRST HANDOVER (Bbare, ArbNoWithdraw.scn"), e["id"]
    other = ("7j's rt2_exclusion2_arcs (cited as 'uses', A0Fork2) runs on Scn2" if k == 1 else "7h's rt2_exclusion_arcs (cited as 'uses', A0Fork) runs on Scn")
    e["handover_scope"] = (
        f"ONE HANDOVER (7g, ArbA0Fork.Run; Bsa5 correction of Bj8's basis): this row's exact theorems (no_early_ack_iff, client{k}_iff, "
        "box_safe_iff) and counter-traces are about ArbA0Fork.Run: A0 high from t = 0 and falling ONCE at T0 > 0, kept low (H_A0_FALL), "
        "client k's ack low at t = 0 (H_A_INIT), ustate holding the previous winner (H_Q_INIT). One handover by construction of the run, "
        "not because of 7h / 7j's Scn / Scn2. " + other + ", which is also first-handover only (ArbNoWithdraw." +
        ("scn2_excludes_caus" if k == 1 else "scn_excludes_caus") + "). Not re-proved for repeated handovers (ArbMultiToken uses RT2 / A0 "
        "forks only internally, not packaged as a theorem).")
    add_lean(e, [L(A0F, "Run", "definition", "7g's run: A0 falls once (H_A0_FALL), A 0 = false (H_A_INIT): one handover")])
    LOG.append(f"{e['id']}: handover_scope basis -> 7g's ArbA0Fork.Run (Bsa5)")
cv["handover_scope"] = cv["handover_scope"].rstrip() + (" Bj9 (Bsa5): on bd_arbiter.a0_fork_client1 / 2 the basis is 7g's ArbA0Fork.Run "
                                                        "(A0 falls once, A 0 = false), not Scn / Scn2.")

e = BY["bd_c2.env_latency"]
g = [r for r in e["lean"] if r["name"] == "gap_exact" and r["file"].endswith("/IpowCellsT.lean")]
assert len(g) == 1 and g[0]["role"] == "exact_inner"
g[0]["role"] = "context"
g[0]["note"] += (" (Bj9, Bsa5: context, not exact_inner: it is one run family in which both C-element pins carry the SAME trace, so the "
                 "C-element acts as a buffer (cgate_dup), and it is about C's FbCelT, not an iff over this row's box)")
note_append(e, "Bj9 (Bsa5): IpowCellsT.gap_exact re-roled exact_inner -> context (one run family, identical C-element inputs, C's FbCelT).")
LOG.append("bd_c2.env_latency: IpowCellsT.gap_exact exact_inner -> context (Bsa5)")

MT_OLD = "DERIVABLE as C states it for the HELD bd_arbiter (what gcd_hw instantiates): H_ARB_EXCL_of_mt"
MT_NEW = ("DERIVABLE for the HELD bd_arbiter (what gcd_hw instantiates) FROM B0 ON, UNDER PERPETUAL ALTERNATING CONTENTION; RUNS FROM "
          "RESET EXCLUDED (Bsa5 correction of 'as C states it': C's field covers every tick of a run from reset, H_ARB_EXCL_of_mt covers the "
          "samples sigma n >= B0 of an MTRun, which starts settled with both clients requesting at B0 and holds H_HOLD for every k): "
          "H_ARB_EXCL_of_mt")
for rid in ("bd_arbiter.rt1", "bd_arbiter.rt1b"):
    cc = BY[rid]["c_contract"]
    assert cc["basis"].count(MT_OLD) == 1, rid
    cc["basis"] = cc["basis"].replace(MT_OLD, MT_NEW)
    LOG.append(f"{rid}: c_contract basis 'as C states it' -> from B0 on, perpetual alternating contention, runs from reset excluded (Bsa5)")
AC_OLD = "For the held bd_arbiter it IS derivable as C states it under multi-token hypotheses"
AC_NEW = ("For the held bd_arbiter it IS derivable from B0 on, under perpetual alternating contention (runs from reset excluded; Bj9, "
          "Bsa5), under multi-token hypotheses")
for rid in ("bd_arbcell.settled_exclusion", "bd_arbcell.handover_overlap"):
    cc = BY[rid]["c_contract"]
    assert cc["basis"].count(AC_OLD) == 1, rid
    cc["basis"] = cc["basis"].replace(AC_OLD, AC_NEW)
    LOG.append(f"{rid}: c_contract basis pointer to the held arbiter: same Bsa5 correction")

doc["produced_by"] = (doc["produced_by"].rstrip() +
    " Updated by probe Bj9 (2026-10-29) from B-necessity7.md (Necessity7*: bd_mux.isochronic_forks, bd_mux.uxa_join_latency (S_XA_J.1) and "
    "bdc_muxn.iso_zack not_necessary; new rows bd_mux.uxa_seq / uxa_r (boundary), uya_seq / uya_r, bdc_muxn.ua_seq (boundary), ua_r; "
    "combine_groups), B-kleene-win-bound.md (strict.x_window '+W under H_W_BOUND' backed per family; C-element rows +W + Wq; width reading "
    "+2W / +3W; *_rst_dec rows UNPROVED) and B-self-audit5.md (a0_fork handover_scope basis, gap_exact role, H_ARB_EXCL basis); the "
    "'probe Bj9' section of cell_constraints.bj5.py.")

json.dump(doc, open(OUT, "w"), indent=1)
for x in LOG:
    print(x)
