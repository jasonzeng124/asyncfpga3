#!/usr/bin/env python3
"""Generate formal/out/cell_constraints.json (probe P2, shard B, Phase 2 item B).

Every entry is transcribed from formal/notes/B-obligations.md and the B-*.md notes
it cites, checked against the Lean statements named in `lean`. Run with -I.
"""
import copy, json, sys

OUT = sys.argv[1]

# ---------------------------------------------------------------- arc helpers
def lut(u, pin, out="O6", sym=None, note=None):
    a = {"kind": "lut_arc", "from": f"{u}.{pin}", "to": f"{u}.{out}"}
    if sym: a["lean_sym"] = sym
    if note: a["note"] = note
    return a

def sp(u, pin, role, sym=None):
    a = {"kind": "site_pin", "from": f"{u}.{pin}@pip", "to": f"{u}.{pin}", "pin_role": role}
    if sym: a["lean_sym"] = sym
    return a

def wire(frm, to, sym=None, note=None):
    a = {"kind": "wire", "from": frm, "to": to}
    if sym: a["lean_sym"] = sym
    if note: a["note"] = note
    return a

def fbw(u, out, pin, sym=None):
    a = {"kind": "feedback_wire", "from": f"{u}.{out}", "to": f"{u}.{pin}"}
    if sym: a["lean_sym"] = sym
    return a

def env(name, spec, sym=None):
    a = {"kind": "env", "name": name, "spec": spec}
    if sym: a["lean_sym"] = sym
    return a

def line(name, edge, path, spec, sym=None):
    a = {"kind": "line", "name": name, "edge": edge, "path": path, "spec": spec}
    if sym: a["lean_sym"] = sym
    return a

def param(name, spec, sym=None):
    a = {"kind": "cell_param", "name": name, "spec": spec}
    if sym: a["lean_sym"] = sym
    return a

def L(file, name, role, **kw):
    d = {"file": f"formal/lean/Formal/{file}.lean", "name": name, "role": role}
    d.update(kw)
    return d

AUDIT = {"file": "audit/lean/B/W_CElem.lean", "name": "drop_env_latency_cex",
         "role": "necessary", "branch": "origin/claude/audit",
         "note": "audit counter-model (dl=1, dw=2, E=1): every hypothesis of c2_four_phase except H_ENV_LATENCY holds and O glitches inside the promised window"}

CORNER_1C = {"mode": "1C",
             "rule": "evaluate both sides in the SAME prjxray column, once at FAST_MIN and once at SLOW_MAX (H_ONE_CORNER), or as A's EndpointOK with kappa; box (every hi at SLOW_MAX, every lo at FAST_MIN) is always sound. A SLOW_MAX-only check must add the guard As - Af/k (ArbCorners.fast_neg_iff). Never rise=FAST / fall=SLOW."}
CORNER_BOTH = dict(CORNER_1C, mode="1C_both_corners_required")
CORNER_NA = {"mode": "n/a", "rule": "no static delay inequality"}

def form(data, req, margin=0, launch=None, note=None):
    f = {"launch": launch, "data_paths": data, "request_paths": req, "margin_ps": margin}
    if note: f["note"] = note
    return f

E = []
def add(**kw):
    kw.setdefault("status", "proved")
    kw.setdefault("check_scope", "static_route")
    kw.setdefault("combine", "all")
    E.append(kw)

# =============================================================== C-elements
CE = {
    "bd_c2":  dict(u="u", ins=["I0", "I1"], fb="I2", rst="I3", init="64'h00E8_00E8_00E8_00E8",
                   also=["bd_c2_set (reset polarity 1, INIT FFE8..)", "bd_c2_norst (no rst pin)",
                         "instances: bd_arbiter.ua1/ua2, bd_merge.uxa/uya, bd_mux.uxa/uya"],
                   fh=[L("Cells/CElemTiming", "c2_follow_hold", "sufficient"),
                       L("Cells/CElemCore", "c2_follow_hold", "sufficient", note="real-time port")],
                   rt=[L("Cells/CElemTiming", "runt_oscillates", "counter_trace"),
                       L("Cells/CElemCore", "runt_oscillatesR", "counter_trace")],
                   fp=[L("Cells/CElemTiming", "c2_four_phase", "sufficient"),
                       L("Cells/CElemCore", "c2_four_phase", "sufficient")],
                   rs=[L("Cells/CElemTiming", "c2_reset", "sufficient"),
                       L("Cells/CElemCore", "c2_reset", "sufficient")]),
    "bd_c2n": dict(u="u", ins=["I0", "I1"], fb="I2", rst="I3", init="64'h00B2_00B2_00B2_00B2",
                   also=["bd_c2n_set", "bd_link_ctl (req_in=I0, c_next=I1)", "bd_pipe stage controllers"],
                   fh=[L("Cells/OnNetlistTimed", "c2n_follow_hold", "sufficient", note="via c2n_as_c2 (b inverted)"),
                       L("Cells/OnNetlistTimed", "c_follow_hold_s1", "instance", note="routed link_arb s1..s4 instances c_follow_hold_s1..s4")],
                   rt=[L("Cells/CElemTiming", "runt_oscillates", "counter_trace", note="bd_c2 trace; bd_c2n = bd_c2 with b inverted (OnNetlistTimed.c2n_as_c2)")],
                   fp=[L("Cells/OnNetlistTimed", "c2n_four_phase", "sufficient"),
                       L("Cells/OnNetlistTimed", "c_four_phase_s1", "instance", note="s1..s4")],
                   rs=[L("Cells/ResetContract", "c2n_reset", "sufficient", note="general bd_c2n timed reset and hold through release, any power-up (B-reset-contract.md; P6)"),
                       L("Cells/ResetContract", "c2n_set_reset", "sufficient", note="bd_c2n_set"),
                       L("Cells/OnNetlistTimed2", "c_reset_s1", "instance", note="routed link_arb instances c_reset_s1..s4")]),
    "bd_c3":  dict(u="u", ins=["I0", "I1", "I2"], fb="I3", rst="I4", init="64'h0000_FE80_0000_FE80",
                   also=["bd_c3_norst", "bd_ctree nodes"],
                   fh=[L("Cells/CTreeTimed", "c3_follow_hold", "sufficient")],
                   rt=[L("Cells/CTreeTimed", "c3_runt", "counter_trace")],
                   fp=[L("Cells/CTreeTimed", "c3_four_phase", "sufficient")],
                   rs=[L("Cells/CTreeTimed", "c3_reset", "sufficient")]),
    "bd_c4":  dict(u="u", ins=["I0", "I1", "I2", "I3"], fb="I4", rst="I5", init="64'h0000_0000_FFFE_8000",
                   also=["bd_ctree nodes"],
                   fh=[L("Cells/CTreeTimed", "c4_follow_hold", "sufficient")],
                   rt=[L("Cells/CTreeTimed", "c4_runt", "counter_trace")],
                   fp=[L("Cells/CTreeTimed", "c4_four_phase", "sufficient")],
                   rs=[L("Cells/CTreeTimed", "c4_reset", "sufficient")]),
}
INV = [L("Cells/CElemInvolution", "c2_eternal", "context", note="runts never reliably die under involution delay: Dmax must be enforced"),
       L("Cells/CElemInvolution", "c2_slow_resolution", "context")]

for cell, c in CE.items():
    u, fb = c["u"], c["fb"]
    anyin = "|".join(c["ins"])
    loop_hi = [lut(u, f"{{{anyin}}}", "O6", "dlmax", note="max over the enabling pins; prjxray O6 flat over pins (45/124)"),
               fbw(u, "O6", fb, "dwmax"), sp(u, fb, "feedback", "part of dwmax in Lean")]
    add(id=f"{cell}.pulse_width", cell=cell, catalogue_row="C1", also_applies_to=c["also"],
        obligation="H_PULSE: minimum pulse width Dmax of the enabling input combination",
        inequality="enabling combination (all inputs = v, rst = 0) held at the LUT pins for >= dlmax + dwmax (Dmax)",
        forms=[form([loop_hi],
                    [[env("enabling_width", f"time from the last enabling input reaching {u}.{{{anyin}}} to the first withdrawal of any of them at the pins (min)")]],
                    launch=f"last enabling input edge at {u}'s pins")],
        lean=c["fh"] + c["rt"] + (INV if cell in ("bd_c2", "bd_c2n") else []),
        exactness="exact", exactness_note="exact for fixed transport delays: every runt 0 < w < dl+dw oscillates for ever (counter_trace).",
        site_pins={"needed": True, "roles": [f"{u}.{fb} (feedback), hi side"]},
        rule={"rule": "none", "verdict": "none", "detail": "UNCHECKED as such; inside a four-phase run it is implied by the env_latency entry (c2_four_phase derives c(k+1) >= c k + Dmax)."},
        corner=CORNER_1C, check_scope="route_plus_env",
        evidence="Bt c_follow_hold_s*: Dmax 569/838/960/590 ps (mean 739) on link_arb s1..s4, nextpnr 9c732bc6303458df")
    add(id=f"{cell}.env_latency", cell=cell, catalogue_row="C2", also_applies_to=c["also"],
        obligation="H_ENV_LATENCY (= H_FB_FAST, H_LAT, ctree H_ATOMIC_CELL 2): own feedback settles before the environment's answer",
        inequality="dlmax + dwmax <= dlmin + E; E = min over neighbours of (output -> neighbour wire + neighbour arc + wire back to one of this LUT's non-feedback pins)",
        forms=[form([loop_hi],
                    [[lut(u, f"{{{anyin}}}", "O6", "dlmin"),
                      env("E", f"{u}.O6 -> every reader of the output -> its response -> back to a non-feedback pin {u}.{{{anyin}}} (min over neighbours; routed when the neighbour is in the design, else the environment's latency)", "E")]],
                    launch=f"last enabling input edge at {u}'s pins (c k)")],
        lean=c["fp"] + [AUDIT, L("Cells/LinkHandshake", "fb_hazard", "necessary", note="untimed, N = 1"),
                        L("Timing/WinArrayB", "rtOne_exact", "checker_exactness", note="shard C: RT_FB check from the node edge is exact in the 10a model")],
        exactness="sufficient+necessary",
        exactness_note="sufficient (four_phase); necessary by the audit counter-model drop_env_latency_cex (an instance, not a general iff). Superseded by sel_order when per-pin delays are modelled.",
        site_pins={"needed": True, "roles": [f"{u}.{fb} (feedback) hi", "departing pins appear only in the sel_order form"]},
        rule={"rule": "none", "verdict": "none", "detail": "UNCHECKED: no rule compares a C-element's own feedback with its neighbours' answer. C-10d RT_FB (shard C, not a project rule) checks the node-edge form."},
        corner=CORNER_1C, check_scope="route_plus_env",
        evidence="Bt: required E >= 524-915 ps (mean 694); C-10d muller64 s1 RT_FB fails 12/64 slowE, 1/64 on nextpnr SDF (-7 ps); C-10f 8 seeds slowE 7.2 [4..12] of 64")
    sel_ok = cell == "bd_c2n"
    add(id=f"{cell}.sel_order", cell=cell, catalogue_row="C3", also_applies_to=c["also"],
        obligation="H_SEL_ORDER (per-pin form): own feedback reaches its mux select before the first departing input reaches its select",
        inequality="w_hi + SP[fb].hi <= E_tau + SP[departing pin].lo for each departing input; E_tau = earliest departure at its pin after the node edge",
        forms=[form([[fbw(u, "O6", fb, "wh"), sp(u, fb, "feedback", "pq.hi")]],
                    [[env(f"E_tau_{p}", f"node edge at {u}.O6 -> environment/neighbour -> earliest change of the input on {u}.{p} at the pin (ER/EA in PipePerPin)"),
                      sp(u, p, "departing input", "pr.lo/pa.lo")] for p in c["ins"]],
                    launch=f"node edge at {u}.O6 (tau)",
                    note="LUT arcs cancel: the reference instant is the actual node edge, so there is no LUT spread term (6g)")],
        lean=([L("Cells/FifoFidelity", "sel_phase", "sufficient"), L("Cells/FifoFidelity", "sel_order_of_lat", "sufficient"),
               L("Cells/PipePerPin", "selx_phase", "sufficient"),
               L("Cells/FifoFidelity", "sel_runt", "counter_trace"), L("Cells/FifoFidelity", "ce_not_fifo", "counter_trace", note="satisfies lumped C2 with equal-pin band, fails C3, oscillates"),
               L("Cells/PipePerPin", "ce_violates", "counter_trace"), L("Cells/FifoFidelity", "cj_clean", "twin", note="same run with fb on a fast pin is clean")]
              if sel_ok else
              [L("Cells/ConstraintsSel", "sel_phase_gen", "sufficient", note=f"H_SEL_ORDER (forall i, pq.fst kappa <= (p i).fst (alpha' i)) + H_SEL_KEEP on CPinLut n; applied with isC_{cell[3:]}"),
               L("Cells/ConstraintsSel", f"isC_{cell[3:]}", "relation", note="the real INIT is a C-element (IsCElem)" + ("" if cell == "bd_c2" else f"; INIT = ~rst*(all + q*any) by c{cell[4:]}_eq")),
               *([L("Cells/ConstraintsSel", f"c{cell[4:]}_eq", "function_equality")] if cell != "bd_c2" else []),
               L("Cells/ConstraintsSel", "sel_order_of_lat_gen", "sufficient", note="arithmetic form K + pq.hi <= D + (p i).lo for every departing pin, K = tau + w_hi, D = tau + E_tau >= 1; implies H_SEL_ORDER"),
               L("Cells/ConstraintsSel", "sel_runt_gen", "necessary", note="select level: an input gone at its select before the feedback arrived gives the old excitation"),
               L("Cells/ConstraintsSel", f"ce_c{cell[4:]}_sel_order_fails", "counter_trace", note="real INIT (other inputs high reduce it to a || q): fb site pin 6 ticks, departing pin 1 tick; H_SEL_ORDER fails (20 > 17), node rises 13, falls 19, rises 22"),
               L("Cells/ConstraintsSel", f"ce_c{cell[4:]}_not_fifo", "counter_trace", note="no FIFO read with hi <= 18 of the pin-level excitation reproduces it"),
               L("Cells/ConstraintsSel", "cjG_clean", "twin", note="same environment, every pin 1 tick: one clean edge")]),
        status="proved",
        exactness="sufficient+necessary_at_instance",
        exactness_note=("proved for the real bd_c2n INIT with per-pin FIFO site buffers (H_PIN_FIFO, H_TREE_FIFO); necessity shown by one oscillating counter-run, not a general iff."
                        if sel_ok else f"P3 (B-constraints-more.md): proved for the real {cell} INIT and pin map with per-pin FIFO site buffers (CPinLut: H_PIN_FIFO per pin, H_TREE_FIFO); the Lean arithmetic form (sel_order_of_lat_gen) is this entry's inequality. Necessity: select-level runt (sel_runt_gen) and one oscillating counter-run of the real INIT (ce_c{cell[4:]}_sel_order_fails), not a general iff."),
        site_pins={"needed": True, "roles": [f"{u}.{fb} (feedback) hi"] + [f"{u}.{p} (departing input) lo" for p in c["ins"]]},
        rule={"rule": "none", "verdict": "none", "detail": "UNCHECKED and invisible to every SDF rule (flat 25 ps site pip) and to the GLS (gls_lut_fifo: every GLS run satisfies H_LUT_FIFO by construction)."},
        corner=CORNER_1C, check_scope="route_plus_env",
        evidence="Bp: pin-1 feedback in 12/36 fixture feedback pins, 24/64 muller64 stages; per-pin term slow: link ctl +166 [-2,+245]; all 12 muller64 RT_FB failures have term > 0")
    add(id=f"{cell}.reset_width", cell=cell, catalogue_row="C5", also_applies_to=c["also"],
        obligation="H_RST_PULSE / H_RST_LONG: reset held >= Dmax at the pin, released before the first request",
        inequality=f"rst held at {u}.{c['rst']} for >= dlmax + dwmax; release before the first request reaches the pins",
        forms=[form([[lut(u, c["rst"], "O6", "dlmax"), fbw(u, "O6", fb, "dwmax"), sp(u, fb, "feedback")]],
                    [[env("rst_width", f"rst high at {u}.{c['rst']} (pin), min")]],
                    launch=f"rst rise at {u}.{c['rst']}")],
        lean=c["rs"], exactness="sufficient", exactness_note="necessity not shown separately (same loop as pulse_width).",
        site_pins={"needed": True, "roles": [f"{u}.{fb} hi", f"{u}.{c['rst']} (reset) hi"]},
        rule={"rule": "none", "verdict": "none", "detail": "UNCHECKED (testbench / top-level reset); harness resets are microsecond-scale."},
        corner=CORNER_1C, check_scope="environment")

# =============================================================== bd_ctree
add(id="bd_ctree.node_fork", cell="bd_ctree", catalogue_row="C7",
    obligation="lifted H_ENV_LATENCY (static form H_ENV_STATIC): every node's accumulated spread plus its feedback settles before the root's ack lets a leaf move",
    inequality="for every node n: Spread n + fmax n <= dist_min(n -> root) + E; Spread n = max over leaf->n paths of sum(hi - lo) (LUT and wire, port wire included)",
    forms=[form([[env("P_hi", "each leaf->n path P (port wire, child LUT arcs, child->parent wires), every element at hi", "Late/Spread"),
                  fbw("n", "O6", "fb", "fmax n"), sp("n", "fb", "feedback")]],
                [[env("P_lo", "the SAME leaf->n path P, every element at lo"),
                  env("dist_min", "n -> parent wires + parent LUT arcs up to the root, lo", "dist_min"),
                  env("E", "root ack -> earliest move of any leaf, lo", "E")]],
                launch="leaf edge at the port (per leaf->n path)",
                note="the same path on both sides: correlated; per-path rewrite of Spread, equivalent to the Lean static form")],
    provides={"bundling_latency": "root settles by c k + Lmax, Lmax = max over leaf->root paths of sum(lmax + wmax) (Late_le); for depth 2 (N = 5..16) Lmax = 2 lmax + wmax + imax (gen5_lat, gen8_lat)",
              "hold_side": "root cannot move before c k + MinD (Early_ge)"},
    lean=[L("Cells/CTreeTimed", "tree_four_phase", "sufficient", note="per-phase NodesOK form"),
          L("Cells/CTreeTimed", "tree_four_phase_static", "sufficient"), L("Cells/CTreeTimed", "static_ok", "lemma"),
          L("Cells/CTreeTimed", "ctree5_timed", "instance"), L("Cells/CTreeTimed", "ctree8_timed", "instance"),
          L("Cells/CTreeTimed", "gen5_static", "instance"), L("Cells/CTreeTimed", "gen8_static", "instance")],
    exactness="sufficient",
    exactness_note="tree-level necessity not shown; for one cell with zero port wires it reduces to bd_c2.env_latency, which is necessary (drop_env_latency_cex).",
    site_pins={"needed": True, "roles": ["each node's feedback pin hi (I2/I3/I4 by fan-in); not in the Lean model (lumped into fmax)"]},
    rule={"rule": "none", "verdict": "none", "detail": "UNCHECKED"},
    corner=CORNER_1C, check_scope="route_plus_env")
add(id="bd_ctree.ack_wait", cell="bd_ctree", catalogue_row="C6",
    obligation="four-phase with ack wait: the environment turns phase only after the ROOT output acknowledges",
    inequality="protocol (no delay inequality)", forms=[],
    lean=[L("Cells/CTree", "reachable_eq_flat", "exact", note="atomic-cell model: equal reachable-state sets"), L("Cells/CTree", "cex_noAck5", "necessary")],
    exactness="exact", exactness_note="structural, in an atomic-cell model (audit row 21 scope).",
    site_pins={"needed": False, "roles": []}, rule={"rule": "none", "verdict": "none", "detail": "protocol"},
    corner=CORNER_NA, check_scope="protocol")

# =============================================================== bd_latch
LBITS = {
    "bd_latch[odd]":      dict(cell="bd_latch", u="u", d="I0", en="I1", fb="I2", out="O6", arcnote="O6 45/124 flat"),
    "bd_latch[pair.O5]":  dict(cell="bd_latch", u="u", d="I0", en="I1", fb="I2", out="O5", arcnote="O5: I0/I1 44/152, I2 42/150"),
    "bd_latch[pair.O6]":  dict(cell="bd_latch", u="u", d="I3", en="I1", fb="I4", out="O6", arcnote="O6 45/124 flat"),
    "bd_latch_rst":       dict(cell="bd_latch_rst", u="u", d="I0", en="I1", fb="I2", out="O6", arcnote="O6; rst on I3"),
}
for key, b in LBITS.items():
    u, d, en, fb, o = b["u"], b["d"], b["en"], b["fb"], b["out"]
    rst = key == "bd_latch_rst"
    base_lean_setup = [L("Cells/Bundling", "capture", "sufficient"),
                       L("Cells/Bundling", "pair_o6_latch" if key == "bd_latch[pair.O6]" else "odd_latch", "relation", note="the INIT as a LatchRel"),
                       L("Cells/Latch", "holds_value", "sufficient"), L("Cells/LinkTimed", "stage_token", "instance", note="H_DATA_SETUP"),
                       L("Cells/Bundling", "counter_rule_I", "counter_trace", note="passes rule I at zero guard, corrupts (odd LUT6)"),
                       L("Cells/Latch", "ct3_setup_violation", "counter_trace"), L("Cells/LinkHandshake", "setup_needed", "necessary"),
                       L("Cells/RulesKL", "counter_K", "counter_trace", note="same missing arc in rule K")]
    status = "proved"
    RSTL = [L("Cells/ConstraintsLatchRst", "rst_latch_on", "relation", note="rst reading definitely 0 at its pin: the bit is LatchRel (the Kleene mux), both INITs RST0 00B8.., RST1 FFB8.."),
            L("Cells/Latch", "rst0_kleene", "function_equality")]
    fh = [fbw(u, o, fb, "fhi: loop wire"), sp(u, fb, "feedback", "in fhi"), lut(u, fb, o, "fhi: I2/I4 arc", note=b["arcnote"])]
    add(id=f"{key}.setup_data", cell=b["cell"], bit_kind=key, catalogue_row="L1",
        obligation="H_SETUP data part: the bit settles and goes once round its own loop before the enable fall arrives",
        inequality="Td + dhi + fhi <= Toff + elo; dhi = D wire + SP[d] + D arc (max); fhi = feedback wire + SP[fb] + feedback-pin arc (max); elo = enable wire + SP[en] + en arc (min)",
        forms=[form([[env("Td", "launch -> last data change at the D net driver", "Td"), wire("D.drv", f"{u}.{d}", "dhi"), sp(u, d, "data"), lut(u, d, o, "dhi")] + fh],
                    [[env("Toff", "launch -> enable fall at the en net driver (THIS bit's enable)", "Toff"), wire("en.drv", f"{u}.{en}", "elo"), sp(u, en, "enable"), lut(u, en, o, "elo")]],
                    launch="common upstream event (rule I: rise of the upstream stage whose latch feeds this one)")],
        lean=base_lean_setup if not rst else RSTL + [
              L("Cells/ConstraintsLatchRst", "capture_rst", "sufficient", note="Bundling.capture for the resettable bit, both polarities: H_SETUP, H_HOLD, H_RST_LOW from Rl, H_RST_DONE Rl + rhi <= max(Ton+ehi, Td+dhi)"),
              L("Cells/ConstraintsLatchRst", "counter_rule_I_rst", "counter_trace", note="Bundling's rule-I transport counter-trace is a run of both _rst INITs with rst tied low (rst0/rst1_bin_odd); H_SETUP misses the I2 arc, the bit ends wrong"),
              L("Cells/ConstraintsLatchRst", "counter_rules_rst0", "counter_trace"), L("Cells/ConstraintsLatchRst", "counter_rules_rst1", "counter_trace")],
        status=status, exactness="sufficient+necessary_at_boundary",
        exactness_note=("P3 (B-constraints-more.md): capture_rst, sufficient; boundary witness counter_rule_I_rst (rule I's counter-trace, a run of both _rst INITs with rst low). Extra hypothesis for this cell: H_RST_DONE, rst's fall reaches I3 (Rl + rhi) no later than max(Ton + ehi, Td + dhi); see bd_latch_rst.reset." if rst else
                        "sufficient (capture); tight at the boundary (counter_rule_I: one tick less passes); LinkHandshake.setup_iff is E for fixed transport as a worst-case-data condition only (audit row 20)."),
        site_pins={"needed": True, "roles": [f"{u}.{d} (data) hi", f"{u}.{fb} (feedback) hi", f"{u}.{en} (enable) lo"]},
        rule={"rule": "I (also K, L for bd_link_dc)", "source": "cells/verify/tighten.py l.1875-1878 (I), l.2096-2099 (K), l.2009-2012 (L)",
              "verdict": "missing_term",
              "missing": f"lut_arc {u}.{fb}->{o} (feedback-pin arc) and every SP term",
              "detail": "rule I's t_data = data at D pin + max D arc + loop_wire; no feedback-pin arc, no SP[fb]; uses min-over-bits elo (conservative); data from outside a link stage is 'not audited'. Guard max(0.2t,200) covers the 124 ps arc numerically, not arc + ~0.49 ns SP."},
        corner=CORNER_1C, check_scope="static_route",
        evidence="Bh P5b: transport control flips at 419 = wfb + arc; GLS flips at 296 (one arc short): a GLS pass cannot confirm this term. C-10e tcheck rule I (gcd_hw, 4 seeds): min fastG margin 213..366 ps")
    add(id=f"{key}.setup_pulse", cell=b["cell"], bit_kind=key, catalogue_row="L2",
        obligation="H_PW: enable high phase at the bit outlasts its own fanout spread plus one latch loop",
        inequality="Ton + ehi + fhi <= Toff + elo  (ehi + fhi <= Won + elo)",
        forms=[form([[wire("en.drv", f"{u}.{en}", "ehi"), sp(u, en, "enable"), lut(u, en, o, "ehi")] + fh],
                    [[env("Won", "enable rise -> enable fall at the en net driver (high width), min; in a pipe Won i = L_i.lo + max(ER i, EA i)", "Won"),
                      wire("en.drv", f"{u}.{en}", "elo"), sp(u, en, "enable"), lut(u, en, o, "elo")]],
                    launch="enable rise at the en net driver (Ton)",
                    note="the enable wire appears on both sides: its spread (hi - lo) is the term")],
        lean=([L("Cells/Bundling", "capture", "sufficient"), L("Cells/LinkTimed", "stage_token", "instance", note="H_PULSE_WIDTH"),
               L("Cells/PipeTimedN", "token", "instance", note="H_PW i"), L("Cells/LinkHandshake", "setup_iff", "exact_fixed_transport", note="j = i term")]
              if not rst else RSTL + [
                  L("Cells/ConstraintsLatchRst", "capture_rst_from_request", "sufficient", note="ehi + fhi <= W + elo together with the data part Td + dhi + fhi <= Tr + Rlo + W + elo (via Bundling.setup_from_request)"),
                  L("Cells/Bundling", "setup_from_request", "lemma")]),
        status=status, exactness="sufficient",
        exactness_note=("P3: capture_rst_from_request, sufficient (as the odd bit); no separate witness for the _rst INIT." if rst else
                        "sufficient; the j = i term of setup_iff (fixed transport, worst-case data)."),
        site_pins={"needed": True, "roles": [f"{u}.{en} (enable) hi and lo", f"{u}.{fb} (feedback) hi"]},
        rule={"rule": "none", "verdict": "none", "detail": "UNCHECKED: rule I's data path starts at the upstream latch, never at this bit's own enable rise. Rule L is the dc analogue (missing the feedback arc)."},
        corner=CORNER_1C, check_scope="route_plus_env",
        evidence="Bt2 stage_token_q*_s*: required E >= 1101-1953 ps, the binding environment constraint on those routes")
    add(id=f"{key}.hold", cell=b["cell"], bit_kind=key, catalogue_row="L3",
        obligation="H_HOLD / H_RULE_H: the enable fall reaches the bit before the next data value does",
        inequality="Toff + ehi <= Tnew + dlo; in control terms ehi_b <= aslow_b + L(b-1).lo + elo_(b-1) + dlo_b",
        forms=[form([[wire("en.drv", f"{u}.{en}", "ehi"), sp(u, en, "enable"), lut(u, en, o, "ehi")]],
                    [[env("Tnew", "enable fall at the driver -> first change of the D net driver (through the DACK credit aslow in a pipe)", "Tnew"),
                      wire("D.drv", f"{u}.{d}", "dlo"), sp(u, d, "data"), lut(u, d, o, "dlo")]],
                    launch="enable fall at the en net driver (Toff)")],
        lean=([L("Cells/Bundling", "capture", "sufficient"), L("Cells/Latch", "link_latch_holds", "sufficient"), L("Cells/Latch", "hold_of_dack", "sufficient", note="single-transaction arithmetic lemma"),
               L("Cells/OnNetlistTimed2", "latch_rule_h_net", "sufficient", note="windowed form"),
               L("Cells/Bundling", "counter_rule_H", "counter_trace"), L("Cells/Latch", "ct1_hold_violation", "counter_trace", note="silent wrong token"),
               L("Cells/Latch", "ct2_hold_violation_x", "counter_trace", note="X latched")] if not rst else RSTL + [
                  L("Cells/ConstraintsLatchRst", "capture_rst", "sufficient", note="H_HOLD Toff + ehi <= Tnew + dlo"),
                  L("Cells/ConstraintsLatchRst", "counter_rule_H_rst", "counter_trace", note="rule-H counter-trace as a run of both _rst INITs with rst low; H_HOLD fails, the bit ends wrong")]),
        status=status, exactness="sufficient+necessary_at_boundary",
        exactness_note=("P3: capture_rst, sufficient; boundary witness counter_rule_H_rst." if rst else "sufficient; boundary counter-traces."),
        site_pins={"needed": True, "roles": [f"{u}.{en} (enable) hi", f"{u}.{d} (data) lo"]},
        rule={"rule": "H", "source": "cells/verify/tighten.py rule H", "verdict": "conservative_arcs_missing_site_pins",
              "missing": f"SP[{u}.{en}].hi - SP[{u}.{d}].lo",
              "detail": "rule H omits the D-pin arc min (conservative) and adds guard, but has no site-pin term (Bp section 4: pair +258 [+123,+421], odd +324 [+172,+509] in the box). C-10e: 2/932 rows fail at fastG/slowG (-19..-207 ps) that tighten passes."},
        corner=CORNER_1C, check_scope="static_route",
        evidence="Bt2 rule H at pins: q2 required 135-929 ps; tighten.py l.148: H margins move 150-200 ps per seed")

# bd_latch_rst: the reset itself (new in P4, from B-constraints-more.md)
_rfb = [fbw("u", "O6", "I2", "fhi: loop wire"), sp("u", "I2", "feedback", "in fhi"), lut("u", "I2", "O6", "fhi: I2 arc")]
add(id="bd_latch_rst.reset", cell="bd_latch_rst", bit_kind="bd_latch_rst", catalogue_row="L5",
    obligation="H_RST_PW / H_EN_CLOSED_AT_RELEASE / H_RST_DONE: the reset pulse loads the initial value and fills the loop, the enable is closed when rst is released, and rst's release reaches the bit before the first capture",
    inequality="R0 + rhi + fhi <= R1 + rlo (rst high on [R0, R1) at the driver; rhi/rlo = rst wire + SP[I3] + I3 arc); E0 + ehi <= R1 + rlo (enable low from E0); Rl + rhi <= max(Ton + ehi, Td + dhi) for the first capture (H_RST_DONE of capture_rst)",
    forms=[form([[wire("rst.drv", "u.I3", "rhi"), sp("u", "I3", "reset"), lut("u", "I3", "O6", "rhi")] + _rfb],
                [[env("rst_width", "rst high at the driver: R1 - R0, min", "R1 - R0"), wire("rst.drv", "u.I3", "rlo"), sp("u", "I3", "reset"), lut("u", "I3", "O6", "rlo")]],
                launch="rst rise at the driver (R0)", note="H_RST_PW: the pulse fills the loop"),
           form([[env("E0", "enable fall at the en driver, relative to the rst fall (may be negative: closed before)", "E0"), wire("en.drv", "u.I1", "ehi"), sp("u", "I1", "enable"), lut("u", "I1", "O6", "ehi")]],
                [[wire("rst.drv", "u.I3", "rlo"), sp("u", "I3", "reset"), lut("u", "I3", "O6", "rlo")]],
                launch="rst fall at the driver (R1)", note="H_EN_CLOSED_AT_RELEASE; nothing is assumed about rst after R1 (the INIT's consensus makes rst a select between equal legs)"),
           form([[wire("rst.drv", "u.I3", "rhi"), sp("u", "I3", "reset"), lut("u", "I3", "O6", "rhi")]],
                [[env("first_capture", "rst fall -> first enable rise at the en driver (Ton - Rl), min", "Ton - Rl"), wire("en.drv", "u.I1", "ehi"), sp("u", "I1", "enable"), lut("u", "I1", "O6", "ehi")]],
                launch="rst fall at the driver (Rl)", note="H_RST_DONE, enable branch of the max; Lean has the enable at its hi bound, this form charges its lo bound (stronger, conservative); the data branch Td + dhi also suffices")],
    lean=[L("Cells/ConstraintsLatchRst", "reset_loads", "sufficient", note="rst high on [R0, R1) gives q = rv on [R0 + rhi, R1 + rlo)"),
          L("Cells/ConstraintsLatchRst", "reset_holds", "sufficient", note="initial token holds after release until the next enable rise reaches the bit; H_RST_PW, H_EN_CLOSED_AT_RELEASE"),
          L("Cells/ConstraintsLatchRst", "capture_rst", "sufficient", note="H_RST_DONE"),
          L("Cells/ConstraintsLatchRst", "rst0_isRst", "relation"), L("Cells/ConstraintsLatchRst", "rst1_isRst", "relation")],
    exactness="sufficient", exactness_note="P3 (B-constraints-more.md): sufficient; no counter-trace for the reset conditions.",
    site_pins={"needed": True, "roles": ["u.I3 (reset) hi and lo", "u.I2 (feedback) hi", "u.I1 (enable) hi"]},
    rule={"rule": "none", "verdict": "none", "detail": "UNCHECKED (top-level / testbench reset); bd_latch_rst is not emitted for gcd_hw (B-gcd-cells.md)"},
    corner=CORNER_1C, check_scope="route_plus_env")

add(id="bd_latch.loop_bound", cell="bd_latch", catalogue_row="L4",
    obligation="H_LOOP_MIN / H_LOOP_MAX: latch loop delay positive and bounded by L",
    inequality="1 <= loop <= L (L at SLOW_MAX suffices for every faster loop)", forms=[],
    lean=[L("Cells/Latch", "holds_value", "uses", note="LatchBit fields; LoopDelay.widen")],
    exactness="hypothesis", site_pins={"needed": True, "roles": ["feedback pin hi (in L)"]},
    rule={"rule": "none", "verdict": "none", "detail": "input data; O5 OUTMUX arc missing from prjxray SDF (Bt)"},
    corner=CORNER_1C, check_scope="static_route")

# =============================================================== bd_delay
hop = lambda e, p: line("udly", e, p, "one hop = wire + LUT1 (or LUT2 chain pin) arc")
add(id="bd_delay[sym].pulse_width", cell="bd_delay", variant="FASTFALL=0, FASTRISE=0", catalogue_row="D1",
    obligation="symmetric chain: an edge reaches z in [N lo, N hi]; a level survives iff it is wider than the chain's spread",
    inequality="T1 - T >= N (hi - lo)",
    forms=[form([[line("udly", "any", "chain", "N hops (wire + LUT1 arc each), hi", "N*hi")]],
                [[env("width", "level width at a: T1 - T, min"), line("udly", "any", "chain", "N hops, lo", "N*lo")]],
                launch="edge at a (T)")],
    provides={"edge_window": "z takes an edge of a within [N lo, N hi] (sym_edge); used as the matched delay by rules A/B/D/E"},
    lean=[L("Cells/Bundling", "sym_chain", "sufficient"), L("Cells/Bundling", "sym_edge", "sufficient"), L("Cells/Bundling", "buf_pulse_lost", "counter_trace")],
    exactness="sufficient+necessary_at_boundary", site_pins={"needed": True, "roles": ["each LUT1's I0 (hop), hi and lo"]},
    rule={"rule": "A/B/C/D/E (edge window via SDF)", "verdict": "none", "detail": "rules use the chain's routed delay (flat 124 arc); pulse width UNCHECKED (handshake pulses are wide)"},
    corner=CORNER_1C)
add(id="bd_delay[FASTFALL].flush_uniform", cell="bd_delay", variant="FASTFALL=1", catalogue_row="D2",
    obligation="H_FLUSH (uniform): the fast (low) phase at a is long enough that no stale 1 is in flight when the rise re-enters",
    inequality="2*hi + thi <= (T - F) + tlo",
    forms=[form([[line("udly", "fall", "chain", "2 chain hops, hi", "2*hi"), line("udly", "fall", "tap", "one tap hop (a -> stage i.I1 wire + LUT2 arc), hi", "thi")]],
                [[env("low_width", "a low on [F, T): T - F, min"), line("udly", "rise", "tap", "one tap hop, lo", "tlo")]],
                launch="a falls (F)")],
    lean=[L("Cells/Bundling", "slow_not_early", "sufficient"), L("Cells/Bundling", "fast_edge", "sufficient"), L("Cells/Bundling", "slow_arrives", "sufficient"),
          L("Cells/Bundling", "ff_counter", "counter_trace", note="glitch train"), L("Cells/Bundling", "ff_counter_ruleF", "counter_trace", note="passes rule F's premise, the rise skips the chain")],
    exactness="sufficient", exactness_note="uniform sufficient form; the exact per-stage form is the next entry (proved sufficient in P3, ConstraintsFastFall.slow_not_early_ps; flush_stage_of_uniform: this form implies it).",
    site_pins={"needed": True, "roles": ["chain pin I0 and tap pin I1 of each LUT2"]},
    rule={"rule": "F", "source": "cells/verify/tighten.py audit_fastfall", "verdict": "missing_term",
          "missing": "hop_hi(i -> i+1) - tap_lo(i+1): a value still in flight on the chain wire",
          "detail": "F checks latest stage-output fall <= earliest re-rise of the input + guard; covered only while the missing difference < guard"},
    corner=CORNER_1C)
add(id="bd_delay[FASTFALL].flush_per_stage", cell="bd_delay", variant="FASTFALL=1", catalogue_row="D2",
    obligation="exact per-stage FASTFALL flush (rule F + its in-flight term)",
    inequality="for every stage i: fall_i(latest, at stage-i OUTPUT) + hop_hi(i -> i+1) <= T + tap_lo(i+1)",
    forms=[form([[env("fall_i", "a fall -> stage i output fall, latest (Lean fallBound: min over tap and chain, per-stage windows)", "fallBound i"), wire("s[i].O", "u[i+1].I0", "hi i: chain wire"), sp("u[i+1]", "I0", "chain", "in hi i"), lut("u[i+1]", "I0", "O6", "in hi i")]],
                [[env("T", "a fall -> a re-rise (low width), min", "Tt - Fa"), wire("a", "u[i+1].I1", "tlo i: tap wire"), sp("u[i+1]", "I1", "tap", "in tlo i"), lut("u[i+1]", "I1", "O6", "in tlo i")]],
                launch="a falls", note="Lean H_FLUSH_STAGE i: fallBound i + hi i <= Tt + tlo i for every side stage 1 <= i < N (Lean's gate i reads s i and drives s (i+1), = this form's u[i+1]); each window includes its LUT2 pin arc, which cancel only with prjxray's flat O6 arc at one corner")],
    lean=[L("Cells/ConstraintsFastFall", "slow_not_early_ps", "sufficient", note="H_FLUSH_STAGE per side stage; every stage holds the fast value on [fallBound i, Ta + Lo i - 1], so z cannot rise before Ta + sum lo"),
          L("Cells/ConstraintsFastFall", "slow_arrives_ps", "sufficient"), L("Cells/ConstraintsFastFall", "fast_edge_ps", "sufficient"),
          L("Cells/ConstraintsFastFall", "fastfall_lineP", "relation", note="real INITs 2'h2, 4'h8 as a FastLineP"),
          L("Cells/ConstraintsFastFall", "flush_stage_of_uniform", "lemma", note="uniform H_FLUSH implies every H_FLUSH_STAGE"),
          L("Cells/ConstraintsFastFall", "flush_stage_strictly_weaker", "context", note="numeric case: every per-stage condition holds, H_FLUSH fails"),
          L("Cells/ConstraintsFastFall", "ruleF_counter_violates_stage", "counter_trace", note="Bundling.ff_counter_ruleF (rule F's premise holds, the rise skips) violates H_FLUSH_STAGE 1 (13+3 > 12+1)"),
          L("Cells/Bundling", "ff_counter_ruleF", "counter_trace", note="shows rule F without the in-flight term is insufficient")],
    exactness="sufficient",
    exactness_note="P3 (B-constraints-more.md): sufficient for every behaviour of the window model (per-hop, per-tap windows); strictly weaker than the uniform H_FLUSH. Necessity is shown only on rule F's witness (ruleF_counter_violates_stage), not in general (any violated stage => skip is open).",
    site_pins={"needed": True, "roles": ["u[i+1].I0 (chain) hi", "u[i+1].I1 (tap) lo"]},
    rule={"rule": "F", "verdict": "missing_term", "missing": "hop_hi(i -> i+1) - tap_lo(i+1)"},
    corner=CORNER_1C)
add(id="bd_delay[FASTRISE].ack_flush", cell="bd_delay", variant="FASTRISE=1 (DACK line in bd_link/bd_pipe)", catalogue_row="P3",
    obligation="H_ACK_FLUSH b: every copy of the OR line takes the rise before any takes the fall (stage b's high phase outlasts the line's path spread)",
    inequality="ahi_b <= Won_b + alo_b  (ahi = ripple path hi, alo = last tap path lo)",
    forms=[form([[line("dack", "rise", "ripple", "s0 -> LUT1 -> LUT2 chain ... -> s(n+1), every hop hi", "ahi")]],
                [[env("Won_b", "stage b node rise -> its fall, min; Won_b = L_b.lo + max(ER_b, EA_b) (per pin: out.lo + max(ER+pr.lo, EA+pa.lo))", "Won"),
                  line("dack", "fall", "tap", "fastest (last-tap) path, lo", "alo")]],
                launch="stage b node rise (line input)")],
    lean=[L("Cells/PipeTimedN", "fastrise_or", "sufficient", note="the real FASTRISE chain is an OR of FIFO copies"),
          L("Cells/PipeTimedN", "orn_hold_true", "sufficient"), L("Cells/PipeTimedN", "pipe_ctl", "uses"), L("Cells/PipePerPin", "pipe_ctl", "uses", note="per-pin Won")],
    exactness="sufficient", exactness_note="sufficient only; partly an artefact of the path-OR abstraction (6e), physically much weaker.",
    site_pins={"needed": True, "roles": ["chain/tap pins of the DACK LUTs (lumped FIFO pins in Lean)"]},
    rule={"rule": "none", "verdict": "none", "detail": "UNCHECKED (FASTRISE dual of rule F)"},
    corner=CORNER_1C, check_scope="route_plus_env")
add(id="bd_delay_gated.gate", cell="bd_delay_gated", catalogue_row="D5",
    obligation="gated FASTFALL line (H_FLUSH_STAGE with taps from `gate`, = GcdCells H_GFLUSH i): the gate's low phase flushes every stage before the gate's re-rise re-enables it, so z rises no earlier than the matched delay after the gate rises; z falls one tap hop after the gate",
    inequality="stage 1 (behind the ungated uor and g[0] LUT1s): F + r0.hi + r1.hi + (p 1).hi <= T + (q 1).lo; stage i >= 2: F + (q(i-1)).hi + (p i).hi <= T + (q i).lo (gate low on [F, T); r0 = gate -> uor, r1 = uor -> g[0], p i = chain pin, q i = tap pin of g[i], each route + site pin + arc)",
    forms=[form([[wire("gate", "uor.I0", "r0.hi"), sp("uor", "I0", "chain"), lut("uor", "I0", "O6", "r0.hi"), wire("uor.O6", "g[0].I0", "r1.hi"), sp("g[0]", "I0", "chain"), lut("g[0]", "I0", "O6", "r1.hi"),
                  wire("g[0].O6", "g[1].I0", "(p 1).hi"), sp("g[1]", "I0", "chain"), lut("g[1]", "I0", "O6", "(p 1).hi")]],
                [[env("low_width", "gate low on [F, T): T - F, min", "T - F"), wire("gate", "g[1].I1", "(q 1).lo"), sp("g[1]", "I1", "tap"), lut("g[1]", "I1", "O6", "(q 1).lo")]],
                launch="gate falls at its driver (F)", note="H_GFLUSH 1 (gflush1_of_lat): the two ungated hops are in flight"),
           form([[wire("gate", "g[i-1].I1", "(q (i-1)).hi"), sp("g[i-1]", "I1", "tap"), lut("g[i-1]", "I1", "O6", "(q (i-1)).hi"),
                  wire("g[i-1].O6", "g[i].I0", "(p i).hi"), sp("g[i]", "I0", "chain"), lut("g[i]", "I0", "O6", "(p i).hi")]],
                [[env("low_width", "gate low on [F, T): T - F, min", "T - F"), wire("gate", "g[i].I1", "(q i).lo"), sp("g[i]", "I1", "tap"), lut("g[i]", "I1", "O6", "(q i).lo")]],
                launch="gate falls at its driver (F)", note="H_GFLUSH i, 2 <= i < N (gflush_of_lat); ConstraintsFastFall states the same per stage as fallBound i + hi i <= Tg + tlo i")],
    lean=[L("Cells/ConstraintsFastFall", "gated_not_early", "sufficient", note="window model (house model, Kleene closure of the real INITs); H_FLUSH_STAGE against the gate's rise Tg; uses the header contract H_A_FOLLOWS_GATE as separate stability windows of a and gate"),
          L("Cells/ConstraintsFastFall", "gated_line", "relation"),
          L("Cells/ConstraintsFastFall", "gated_fast_edge", "sufficient", note="z falls one gate-tap hop after gate"),
          L("Cells/ConstraintsFastFall", "gated_dip_glitch", "sufficient", note="timed gated_dip_flushes: gate low on [F, F'] puts z low on [F + thi, F' + tlo] even while a stays high"),
          L("Cells/GcdCells", "no_early", "sufficient", note="per-pin FIFO read model (PipeTimed.Ret) as bdc instantiates the cell (gate -> uor -> g[0] -> AND stages); H_GFLUSH i"),
          L("Cells/GcdCells", "gflush1_of_lat", "sufficient", note="H_GFLUSH 1 from delays, with the uor hop"), L("Cells/GcdCells", "gflush_of_lat", "sufficient", note="H_GFLUSH i >= 2 from delays"),
          L("Cells/GcdCells", "fast_fall", "sufficient"), L("Cells/GcdCells", "rises", "sufficient"), L("Cells/GcdCells", "rise_by", "sufficient"),
          L("Cells/GcdCells", "flush_needed", "counter_trace", note="N = 2, gate dip [10, 12): H_GFLUSH 1 false (17 > 13), z high at 13 < 19 = T + L 2"),
          L("Cells/GcdCells", "long_dip_no_early", "non_vacuity"), L("Cells/GcdCells", "long_dip_rises", "non_vacuity"),
          L("Cells/LibEndMemMlink", "gated_gate_low", "kleene"), L("Cells/LibEndMemMlink", "gated_dip_flushes", "kleene")],
    exactness="sufficient",
    exactness_note="P3 (ConstraintsFastFall, window model) and Bg2 (GcdCells, per-pin FIFO model with the explicit uor anchor hop): two independent sufficient proofs; GcdCells.flush_needed is a failing counter-run with H_GFLUSH 1 violated (necessity at one instance, not tight, not general). Not shown: the AND gate's static-hazard freedom when chain and tap pins move together (H_TREE_FIFO folded into the per-pin maps); the bundling of the data z covers (rule A on the compute cone).",
    site_pins={"needed": True, "roles": ["g[i].I0 (chain) hi", "g[i].I1 (tap) lo and hi", "uor.I0, g[0].I0 hi (stage 1)"]},
    rule={"rule": "F", "source": "cells/verify/tighten.py audit_fastfall (covers bd_delay_gated: head input = uor output's late fall)", "verdict": "missing_term",
          "missing": "(p i).hi - (q i).lo: chain wire into g[i] against the tap wire into it (as row D2)"},
    corner=CORNER_1C, check_scope="route_plus_env",
    evidence="29 instances in gcd_hw (20 fused compute units, 8 control merges, 1 muxn3; N 12..94), B-gcd-cells.md; no route measured")

# =============================================================== bd_link / bd_pipe
add(id="bd_pipe.sel_order", cell="bd_pipe", also_applies_to=["bd_link (N = 1)"], catalogue_row="C3 (6g)",
    obligation="H_SELORD i: per stage, per-pin feedback-before-departure, with derived round trips",
    inequality="wh_i + pq_i.hi <= ER_i + pr_i.lo AND wh_i + pq_i.hi <= EA_i + pa_i.lo; ER_0 = Es, ER_(i+1) = alo(i+1) + pa_i.lo + out_i.lo + Rq(i+1).lo; EA_i = Rq(i+1).lo + pr_(i+1).lo + out_(i+1).lo + alo(i+1), EA_(N-1) = Er",
    forms=[form([[fbw("ctl[i].u", "O6", "I2", "wh_i"), sp("ctl[i].u", "I2", "feedback", "pq_i.hi")]],
                [[line("dack[i]", "any", "fastest", "stage i's ack out through DACK line to ctl[i-1].I1", "alo(i)"),
                  sp("ctl[i-1].u", "I1", "ack", "pa_(i-1).lo"), lut("ctl[i-1].u", "{I0|I1}", "O6", "out_(i-1).lo"),
                  line("rq[i]", "any", "request", "ctl[i-1].O6 -> SDELAY line -> ctl[i].I0", "Rq(i).lo"), sp("ctl[i].u", "I0", "req", "pr_i.lo")],
                 [line("rq[i+1]", "any", "request", "ctl[i].O6 -> ctl[i+1].I0", "Rq(i+1).lo"), sp("ctl[i+1].u", "I0", "req", "pr_(i+1).lo"),
                  lut("ctl[i+1].u", "{I0|I1}", "O6", "out_(i+1).lo"), line("dack[i+1]", "any", "fastest", "-> ctl[i].I1", "alo(i+1)"),
                  sp("ctl[i].u", "I1", "ack", "pa_i.lo")]],
                launch="node edge of ctl[i] (tau i j)",
                note="stage 0: first request path replaced by env Es + pr_0.lo; last stage: second path replaced by env Er + pa_(N-1).lo")],
    lean=[L("Cells/PipePerPin", "pipe_ctl", "sufficient"), L("Cells/PipePerPin", "selx_phase", "sufficient"), L("Cells/PipePerPin", "token", "sufficient"),
          L("Cells/PipePerPin", "pipe_forward", "sufficient"), L("Cells/PipePerPin", "ce_violates", "counter_trace"), L("Cells/PipePerPin", "ce_ctlp", "counter_trace"),
          L("Cells/FifoFidelity", "cj_clean", "twin")],
    exactness="sufficient+necessary_at_instance", exactness_note="replaces H_LUT_FIFO and H_LAT; residual hypotheses H_PIN_FIFO, H_TREE_FIFO.",
    site_pins={"needed": True, "roles": ["ctl[i].I2 (feedback) hi", "ctl[i].I0 (req) lo", "ctl[i].I1 (ack) lo", "neighbours' I0/I1 lo"]},
    rule={"rule": "none", "verdict": "none", "detail": "UNCHECKED; needs FASM pin assignment + prjxray site-pin bands"},
    corner=CORNER_1C, check_scope="static_route")
add(id="bd_pipe.lat_lumped", cell="bd_pipe", also_applies_to=["bd_link"], catalogue_row="C2 (6f)",
    obligation="H_LAT i (lumped, superseded by bd_pipe.sel_order when per-pin delays are modelled)",
    inequality="L_i.hi + wh_i <= L_i.lo + min(ER_i, EA_i)",
    forms=[form([[lut("ctl[i].u", "{I0|I1}", "O6", "L_i.hi"), fbw("ctl[i].u", "O6", "I2", "wh_i")]],
                [[lut("ctl[i].u", "{I0|I1}", "O6", "L_i.lo"), env("ER_i", "derived round trip through stage i-1 (see sel_order)")],
                 [lut("ctl[i].u", "{I0|I1}", "O6", "L_i.lo"), env("EA_i", "derived round trip through stage i+1")]],
                launch="ctl[i] phase start at its pins (c i j)")],
    lean=[L("Cells/PipeTimedN", "pipe_ctl", "sufficient"), L("Cells/PipeTimedN", "nodes_clean", "sufficient"), L("Cells/PipeTimedN", "live", "sufficient")],
    exactness="sufficient", exactness_note="assumes H_LUT_FIFO, which is false for a real LUT (FifoFidelity.ce_not_fifo); use sel_order.",
    site_pins={"needed": False, "roles": ["not in this form (that is why it is superseded)"]},
    rule={"rule": "none", "verdict": "none"}, corner=CORNER_1C, check_scope="static_route")
add(id="bd_pipe.boundary_I", cell="bd_pipe", also_applies_to=["bd_link"], catalogue_row="L1 (H_I b)",
    obligation="H_I b: data from stage b-1 captured by stage b's latch (rule I at boundary b)",
    inequality="Dl(b-1) + dhi_b + fhi_b <= Won(b-1) + Rq_b.lo + L_b.lo + elo_b  (in Z); Dl(i+1) = max(ehi_(i+1), Dl i - Rq(i+1).lo - L(i+1).lo + dhi(i+1))",
    forms=[form([[env("Dl(b-1)", "data lateness at stage b-1's latch outputs relative to its rise (depth recursion)", "Dl"),
                  wire("lat[b-1].q", "lat[b].u.Id", "dhi"), sp("lat[b].u", "Id", "data"), lut("lat[b].u", "Id", "O", "dhi"),
                  fbw("lat[b].u", "O", "Ifb", "fhi"), sp("lat[b].u", "Ifb", "feedback"), lut("lat[b].u", "Ifb", "O", "fhi")]],
                [[env("Won(b-1)", "stage b-1 high phase, min"), line("rq[b]", "rise", "request", "SDELAY line", "Rq_b.lo"),
                  sp("ctl[b].u", "I0", "req"), lut("ctl[b].u", "I0", "O6", "L_b.lo"), wire("ctl[b].O6", "lat[b].u.I1", "elo"),
                  sp("lat[b].u", "I1", "enable"), lut("lat[b].u", "I1", "O", "elo")]],
                launch="stage b-1 node rise (tau (b-1) (2k))", note="Id/Ifb/O per bit kind: odd/O5 I0/I2, pair O6 I3/I4")],
    lean=[L("Cells/PipeTimedN", "token", "sufficient"), L("Cells/PipePerPin", "token", "sufficient", note="per-pin credit Rq.lo + pr.lo + out.lo"),
          L("Cells/Bundling", "counter_rule_I", "counter_trace")],
    exactness="sufficient", site_pins={"needed": True, "roles": ["lat[b] data, feedback hi", "lat[b] enable lo", "ctl[b] req lo"]},
    rule={"rule": "I", "verdict": "missing_term", "missing": "feedback-pin arc and SP terms (see bd_latch[*].setup_data)"},
    corner=CORNER_1C, check_scope="static_route",
    evidence="C-10e tcheck: rule I agrees 75/75 rows on 4 gcd_hw seeds (nextpnr 9c732bc6303458df)")
add(id="bd_pipe.boundary_H", cell="bd_pipe", also_applies_to=["bd_link"], catalogue_row="L3 (H_H b)",
    obligation="H_H b: stage b's latch closes before stage b-1's next value reaches it (rule H, DACK credit = slowest path's lo)",
    inequality="ehi_b <= aslow_b + L(b-1).lo + elo_(b-1) + dlo_b",
    forms=[form([[wire("ctl[b].O6", "lat[b].u.I1", "ehi"), sp("lat[b].u", "I1", "enable"), lut("lat[b].u", "I1", "O", "ehi")]],
                [[line("dack[b]", "fall", "ripple", "slowest DACK path (ripple), lo", "aslow_b"), sp("ctl[b-1].u", "I1", "ack"),
                  lut("ctl[b-1].u", "I1", "O6", "L(b-1).lo"), wire("ctl[b-1].O6", "lat[b-1].u.I1", "elo_(b-1)"), sp("lat[b-1].u", "I1", "enable"),
                  lut("lat[b-1].u", "I1", "O", "elo_(b-1)"), wire("lat[b-1].q", "lat[b].u.Id", "dlo_b"), sp("lat[b].u", "Id", "data"), lut("lat[b].u", "Id", "O", "dlo_b")]],
                launch="ctl[b] node fall")],
    lean=[L("Cells/PipeTimedN", "token", "sufficient"), L("Cells/PipeTimedN", "back_odd", "lemma", note="rise after downstream fall comes through aslow"),
          L("Cells/OnNetlistTimed2", "latch_rule_h_net", "sufficient"), L("Cells/Latch", "ct1_hold_violation", "counter_trace")],
    exactness="sufficient", site_pins={"needed": True, "roles": ["lat[b].I1 hi", "lat[b] data pin lo", "ctl[b-1].I1, lat[b-1].I1 lo"]},
    rule={"rule": "H", "verdict": "conservative_arcs_missing_site_pins", "detail": "timing.early_fall to the tail is consistent with aslow; no SP term"},
    corner=CORNER_1C, check_scope="static_route",
    evidence="C-10e: H 157/158 or 158/158 rows agree; 2 rows fail at fastG/slowG only (enable path site pins ~800 ps at prjxray slow vs 419 in SDF)")
add(id="bd_pipe.rst_lines", cell="bd_pipe", also_applies_to=["bd_link"], catalogue_row="P4 / C5",
    obligation="startup: H_RST_LONG, H_RST_LINES b, H_RST_SEL i (reset released after lines and loops flushed, before the first request)",
    inequality="L_i.hi + wh_i <= R; L(b-1).hi + Rq_b.hi <= R; L_b.hi + ahi_b <= R; Ag_b <= R; per pin (6g): R0 + pr.hi <= R + ps.lo; out.hi + wh + pq.hi <= R + ps.lo; R + ps.hi <= rho0 + pr.lo; R0 + pa.hi <= rho0 + pr.lo",
    forms=[form([[lut("ctl[i].u", "I3", "O6"), fbw("ctl[i].u", "O6", "I2"), sp("ctl[i].u", "I2", "feedback")]],
                [[env("R", "reset release time at the reset driver (startup), min"), sp("ctl[i].u", "I3", "reset")]],
                launch="all pins hold their initial value (R0)", note="one representative form (6g H_RST_SEL (b)); the others have the same shape")],
    lean=[L("Cells/PipePerPin", "pipe_ctl", "sufficient", note="H_RST_SEL"), L("Cells/PipeTimedN", "pipe_ctl", "sufficient", note="H_RST_LONG, H_RST_LINES")],
    exactness="sufficient", site_pins={"needed": True, "roles": ["reset pin I3", "feedback I2", "req I0, ack I1"]},
    rule={"rule": "none", "verdict": "none", "detail": "UNCHECKED; true once at startup (reset polarity), resets are long in practice"},
    corner=CORNER_1C, check_scope="environment")
add(id="bd_pipe.data_lead", cell="bd_pipe", also_applies_to=["bd_link"], catalogue_row="P1",
    obligation="H_DATA_LEAD: data before request at the pipe input",
    inequality="dS k + Sdr <= rho(2k) + Lag  (classic request-after-data is sufficient, not necessary)",
    forms=[form([[env("dS", "sender: last data change at the input net driver"), env("Sdr", "data route to the first latch, hi")]],
                [[env("rho", "request rise at r[0]"), env("Lag", "request route + controller to the first enable, lo")]],
                launch="sender event")],
    lean=[L("Cells/Bundling", "classic_implies_setup", "sufficient"), L("Cells/Bundling", "setup_not_classic", "not_necessary"),
          L("Cells/PipeTimedN", "token", "uses")],
    exactness="sufficient", site_pins={"needed": True, "roles": ["first latch data / enable pins"]},
    rule={"rule": "A", "verdict": "conservative", "detail": "rule A (sender's request last, guard max(0.2t,200)) is a different, stronger condition"},
    corner=CORNER_1C, check_scope="route_plus_env")
add(id="bd_pipe.output", cell="bd_pipe", also_applies_to=["bd_link"], catalogue_row="P2",
    obligation="pipe_forward: last stage's data valid from the receiver's ack rise",
    inequality="Dl(N-1) b <= Er",
    forms=[form([[env("Dl(N-1)", "data lateness at the last latch output relative to its rise")]], [[env("Er", "receiver latency, min")]], launch="last stage node rise")],
    lean=[L("Cells/PipeTimedN", "pipe_forward", "sufficient"), L("Cells/LinkTimed", "stage_forward", "sufficient")],
    exactness="sufficient", site_pins={"needed": False, "roles": []},
    rule={"rule": "consumer's own rule (I at the next stage; B/D/E at an edge-sampling consumer)", "verdict": "different_condition"},
    corner=CORNER_1C, check_scope="route_plus_env")

# bd_link_dc
add(id="bd_link_dctl.lt_first", cell="bd_link_dctl", also_applies_to=["bd_link_dc"], catalogue_row="P6",
    obligation="H_LT_FIRST: lt settles before a neighbour can answer through b/a",
    inequality="max(bhi, ahi, ghi) + wlt_hi <= R - 1 + min(blo, alo, glo) + wlt_lo (ConstraintsMore H_LT_FIRST_T): b/a/gate stable at their drivers on [T, T + R - 1] (H_ROUND_TRIP, R = round trip back through b/a), each ult pin read over [lo, hi] (route + SP + arc), lt read by every consumer over [wlt_lo, wlt_hi]",
    forms=[form([[wire("{b|a|gate}.drv", "ult.{I0|I1|I2}", "bhi/ahi/ghi"), sp("ult", "{I0|I1|I2}", "input"), lut("ult", "{I0|I1|I2}", "O6", "bhi/ahi/ghi"), wire("ult.O6", "uld.I0", "wlt_hi"), sp("uld", "I0", "lt")]],
                [[env("R", "last b/a/gate change at its driver -> next change of any ult input at its driver (round trip through a neighbour), min, minus one tick", "R - 1"),
                  wire("{b|a|gate}.drv", "ult.{I0|I1|I2}", "min(blo, alo, glo)"), sp("ult", "{I0|I1|I2}", "input"), lut("ult", "{I0|I1|I2}", "O6", "min(blo, alo, glo)"),
                  wire("ult.O6", "uld.I0", "wlt_lo"), sp("uld", "I0", "lt")]],
                launch="last change of an ult input at its driver (T)", note="LUT-level form only (lt_first_window); its link to the untimed schedule ltFirst is not proved")],
    lean=[L("Cells/LinkHandshake", "dctl_ok0", "sufficient", note="interleaving schedule (untimed)"), L("Cells/LinkHandshake", "dctl_ok1", "sufficient"),
          L("Cells/LinkHandshake", "dctl_si_hazard", "counter_trace", note="9-step trace"),
          L("Cells/ConstraintsMore", "ult_kleene", "function_equality", note="INIT_DLT is the Kleene NOR"),
          L("Cells/ConstraintsMore", "lt_settles", "lemma"),
          L("Cells/ConstraintsMore", "lt_first_window", "partial", note="under H_ROUND_TRIP and H_LT_FIRST_T every consumer pin reads the settled lt before the next input change can arrive"),
          L("Cells/ConstraintsMore", "lt_opposite_x", "necessary", note="Kleene: opposite b/a edges inside the window give x; with one input high the other's edge is masked")],
    status="unproved", exactness="partial",
    exactness_note="P3 PARTIAL (LUT level only): lt_first_window proves the timed LUT-level statement; NOT proved that timed runs satisfying H_LT_FIRST_T obey the untimed schedule ltFirst that dctl_ok0/1 need (needs a timed model of the dctl controller and its two neighbours, est. 1 day). Status stays 'unproved' as an inequality => hazard-freedom theorem.",
    site_pins={"needed": True, "roles": ["uld.I0 hi", "return pins lo"]}, rule={"rule": "none", "verdict": "none", "detail": "decoupled_si.py --rt env assumes it, untimed"},
    corner=CORNER_1C, check_scope="route_plus_env")
for rk, which, ineq, ctr, cov in [
        ("K", "close caused by the request", "dWire + dArcMax + loopWire + fbArc + guard <= tReq + dCtl + dFan + enArcMin", "counter_K", "coded_K_covered"),
        ("L", "close caused by ld (request already up)", "max_p(lateWire + enArcMax + loopWire + fbArc) + guard <= tLd + tB + min_p(dCtl + dFan + enArcMin)", "counter_L", "coded_L_covered")]:
    data = ([wire("D.drv", "lat.u.Id", "dWire"), sp("lat.u", "Id", "data"), lut("lat.u", "Id", "O", "dArcMax")] if rk == "K"
            else [wire("ult.O6", "lat.u.I1", "lateWire"), sp("lat.u", "I1", "enable"), lut("lat.u", "I1", "O", "enArcMax")])
    data += [fbw("lat.u", "O", "Ifb", "loopWire"), sp("lat.u", "Ifb", "feedback"), lut("lat.u", "Ifb", "O", "fbArc")]
    req = ([env("tReq", "req_src -> ub.I0, early", "tReq")] if rk == "K" else [env("tLd+tB", "lt -> uld -> ld -> ub -> b, early", "tLd + tB")])
    req += [wire("b", "ult.I0", "dCtl"), lut("ult", "I0", "O6", "dCtl"), wire("ult.O6", "lat.u.I1", "dFan"), sp("lat.u", "I1", "enable"), lut("lat.u", "I1", "O", "enArcMin")]
    add(id=f"bd_link_dc.rule_{rk}_corrected", cell="bd_link_dc", catalogue_row="P7",
        obligation=f"dc latch close ({which}): corrected rule {rk}'",
        inequality=ineq,
        forms=[form([data], [req], launch="request leaves its source (K) / lt rise (L)")],
        lean=[L("Cells/RulesKL", "setup_of_KL", "sufficient", note="K' and L' imply H_SETUP under H_LAUNCH, H_LT_FALL_K/L (stated, not derived)"),
              L("Cells/RulesKL", "dc_capture", "sufficient"), L("Cells/RulesKL", ctr, "counter_trace", note=f"passes coded {rk} (and the other) at zero guard, corrupts"),
              L("Cells/RulesKL", cov, "rule_as_coded", note="coded rule implies corrected rule iff guard >= feedback arc")],
        exactness="sufficient", exactness_note="coded rule shown insufficient by a whole-stage transport trace; gap = exactly one feedback-pin arc.",
        site_pins={"needed": True, "roles": ["latch data/enable/feedback pins"]},
        rule={"rule": rk, "source": f"cells/verify/tighten.py rule {rk}", "verdict": "missing_term", "missing": "feedback-pin arc (and SP terms)",
              "detail": "200 ps guard floor covers the arc only by spending scatter guardband; bd_link_dc is not a production option"},
        corner=CORNER_1C, check_scope="static_route")

# =============================================================== bd_arbcell
add(id="bd_arbcell.req_separation", cell="bd_arbcell", also_applies_to=["bd_arbiter (ustate/ugrant)"], catalogue_row="R2",
    obligation="H_REQ_SEP: any two same-sense request edges more than L apart (L = state arc + q loop)",
    inequality="|t(r1 edge) - t(r2 edge)| > L for same-sense moves", forms=[],
    lean=[L("Cells/ArbBinary", "exclusion_transport", "sufficient"), L("Cells/ArbBinary", "exclusion_needs_sep", "necessary"),
          L("Cells/ArbBinary", "runt_overlap", "counter_trace"), L("Cells/ArbInvolution", "arb_grants_eternal", "context")],
    exactness="sufficient+necessary", exactness_note="an environment RATE, not a routable fact: request timing is free in an arbiter's use.",
    site_pins={"needed": False, "roles": []}, rule={"rule": "none", "verdict": "uncheckable_statically", "detail": "only probabilistic (metastability tier R3)"},
    corner=CORNER_NA, check_scope="not_static")
add(id="bd_arbcell.grant_skew", cell="bd_arbcell", catalogue_row="R2",
    obligation="H_GRANT_SKEW: O5/O6 grant arcs differ by at most the loop delay",
    inequality="|d6 - d5| <= L",
    forms=[form([[lut("ugrant", "I2", "O6", "d6")]], [[lut("ugrant", "I2", "O5", "d5"), env("L", "state arc + q loop, lo")]], launch="q edge at ugrant.I2"),
           form([[lut("ugrant", "I2", "O5", "d5")]], [[lut("ugrant", "I2", "O6", "d6"), env("L", "state arc + q loop, lo")]], launch="q edge at ugrant.I2")],
    lean=[L("Cells/ArbBinary", "exclusion_transport", "sufficient"), L("Cells/ArbBinary", "runt_overlap_needs_skew", "context", note="zero skew gives exclusion for every trace")],
    exactness="sufficient", site_pins={"needed": False, "roles": ["same pin (I2) feeds both outputs: SP cancels"]},
    rule={"rule": "none", "verdict": "none"}, corner=CORNER_1C, check_scope="static_route")
add(id="bd_arbcell.handover_overlap", cell="bd_arbcell", catalogue_row="R5",
    obligation="bare handover grant overlap (no obligation needed at a consistent corner)",
    inequality="overlap = max 0 (d6 - o5q - w) = 0 at every consistent corner and every w >= 0; box max 0 (37 - w)", forms=[],
    lean=[L("Cells/ArbHandover", "overlap_duration_r2_to_r1", "exact_formula", note="closed-form equality for the overlap count (not an iff)"), L("Cells/ArbCorners", "overlap_C", "exact_formula", note="closed form max 0 (d6 - o5q - w) at any corner (an equality, not an iff)"),
          L("Cells/ArbCorners", "corner_no_overlap", "sufficient", note="no overlap at every consistent corner, every w >= 0"), L("Cells/ArbCorners", "box_overlap_le", "bound"), L("Cells/ArbCorners", "prj_is_mix", "context", note="the old 16 ps was the corner mix"),
          L("Cells/ArbOverlapRace", "grant_cap", "bound", note="Bov: for EVERY digital trace (any request waveforms, fork skew, near ties, runts, q oscillation) every g1 & g2 interval is <= |b5 - b6| = |O5 - O6 arc of q's pin| (b_cancel, H_SHARED_Q_PIN)"),
          L("Cells/ArbOverlapRace", "cell_cap_consistent", "bound", note="<= 33 ps at a consistent corner"), L("Cells/ArbOverlapRace", "cell_cap_box", "bound", note="<= 112 ps in the independent box"),
          L("Cells/ArbOverlapRace", "cell_never_203", "bound", note="the cell cannot pass the board's >= 203 ps filter; the rig's detector site pins can (slow_trace_passes_203, 305 ps at SLOW_MAX with zero SDF skew)")],
    exactness="exact", site_pins={"needed": False, "roles": []}, rule={"rule": "none", "verdict": "none", "detail": "below any filter"},
    corner=dict(CORNER_1C, note="exact 0 holds only at a consistent corner; the corner-mixed arc model gives 16 ps"), check_scope="static_route")
add(id="bd_arbcell.bbm", cell="bd_arbcell", also_applies_to=["bd_arbiter.ugrant"], catalogue_row="R4",
    obligation="H_BBM1/H_BBM2: at a q edge the falling grant output beats the rising one (as involution delay functions)",
    inequality="not a static inequality (needs per-output pulse-shrink curves)", forms=[],
    lean=[L("Cells/ArbInvolution", "arb_grants_eternal", "sufficient"), L("Cells/ArbInvolution", "first_edge_overlap", "necessary"),
          L("Cells/ArbInvolution", "first_edge_iff", "exact_first_edge")],
    exactness="sufficient", exactness_note="necessary only at the first edge.",
    site_pins={"needed": False, "roles": []}, rule={"rule": "none", "verdict": "uncheckable_statically"}, corner=CORNER_NA, check_scope="not_static")
add(id="bd_arbcell.settled_exclusion", cell="bd_arbcell", also_applies_to=["bd_arbiter"], catalogue_row="R1",
    obligation="settled exclusion (structural: g1, g2 read the same q pin)", inequality="none", forms=[],
    lean=[L("Cells/ArbBinary", "settled_exclusion", "sufficient", note="unconditional Boolean identity g1 && g2 = false (not an iff)"), L("Cells/OnNetlist", "settled_exclusion_bits", "instance", note="on the bits")],
    exactness="exact", site_pins={"needed": False, "roles": []}, rule={"rule": "none", "verdict": "none"}, corner=CORNER_NA, check_scope="structural")

# =============================================================== bd_arbiter
def a0fork(k):
    g = "O6" if k == 2 else "O5"
    early = [wire("A0@div", "ustate.I4", "wSt"), sp("ustate", "I4", "A0", "pSt"), lut("ustate", "I4", "O6", "aSt", note=("q fall" if k == 2 else "q rise")),
             wire("ustate.O6", "ugrant.I2", "wQG"), sp("ugrant", "I2", "q", "pQG"), lut("ugrant", "I2", g, "aG", note=f"g{k} rise"),
             wire(f"ugrant.{g}", f"ua{k}.I0", "wGC"), sp(f"ua{k}", "I0", "grant", "pGC")]
    late = [wire("A0@div", f"ua{k}.I1", "wAC"), sp(f"ua{k}", "I1", "A0", "pAC")]
    held = (L("Cells/ArbHeldTimed", "rt2_exclusion_arcs", "uses", note="A0Fork (client 2)") if k == 2
            else L("Cells/ArbHeldTimed2", "rt2_exclusion2_arcs", "uses", note="A0Fork2 (client 1)"))
    add(id=f"bd_arbiter.a0_fork_client{k}", cell="bd_arbiter", catalogue_row="A1" if k == 2 else "A4",
        obligation=f"H_A0_FORK (client {k}): A0's fall reaches ua{k} before A0 -> q -> g{k} does",
        inequality="late <= early; late = wAC + SP[A0 pin of ua_k]; early = wSt + SP[ustate.I4] + aSt + wQG + SP[ugrant.I2] + aG + wGC + SP[g pin of ua_k]; shared prefix c and ua_k's arc cancel",
        forms=[form([late], [early], launch="A0 fall at the divergence point of the A0 net (after shared prefix c)",
                    note="crediting the shared prefix needs H_CLEAN_EDGE (C-10b prefix_credit_needs_clean_edge)")],
        lean=[L("Cells/ArbA0Fork", "no_early_ack_iff", "exact"), L("Cells/ArbA0Fork", f"client{k}_iff", "exact"),
              L("Cells/ArbA0Fork", "box_safe_iff", "exact", note="box version: hi.late <= lo.early"),
              L("Cells/ArbA0Fork", f"client{k}_counter", "counter_trace"), L("Cells/ArbA0Fork", "early_ack_latches", "counter_trace", note="latches for ever if overlap >= one ua loop"),
              L("Cells/TernaryPhases", "arb_a0_fall_ordered", "sufficient"), L("Cells/TernaryPhases", "arb_a0_fall_skewed_early_ack", "counter_trace"),
              held, L("Cells/ArbCorners", "A0Fork_iff" if k == 2 else "A0Fork2_iff", "reduction"),
              L("Cells/ArbCorners", "ruleJ_arcs", "rule_as_coded"), L("Cells/ArbCorners", "ruleJ_guard_covers_fast", "rule_as_coded"),
              L("Cells/ArbCorners", "ruleJ_guard_small_E", "rule_as_coded"), L("Cells/ArbCorners", "ruleJ_raw_window", "rule_as_coded"),
              L("Cells/ArbCorners", f"client{k}_corner_flip", "corner")],
        exactness="exact", exactness_note="iff, both directions, both clients (box version too).",
        site_pins={"needed": True, "roles": [f"ua{k}.I1 (A0) hi", "ustate.I4 (A0) lo", "ugrant.I2 (q) lo", f"ua{k}.I0 (grant) lo"]},
        rule={"rule": "J", "source": "cells/verify/arb_fork.py", "verdict": "exact_arcs_missing_site_pins",
              "missing": "(SP[ustate.I4] + SP[ugrant.I2] + SP[ua_k.I0] - SP[ua_k.I1]) - 2*25, up to -0.5 ns",
              "detail": f"rule J = box_safe_iff on nextpnr's SDF, guarded 0.772/1.155 past c; flat 2x124 arcs {'exact' if k == 2 else '26 ps conservative'} (ruleJ_arcs). Guarded J covers FAST_MIN given >= 114 ps early routing and k <= 1; raw J does not. Proposed rule J' in B-arb-a0fork.md (adds SP_lo/SP_hi per physical pin)."},
        corner=dict(CORNER_1C, note="box form is the Lean-exact one; at 1C the corner can flip within [-cellJ_slow, -cellJ_fast/k) (client*_corner_flip)"),
        check_scope="static_route",
        evidence="survey 168 routes: raw min +618, guarded min -103 (2 violations); Bp box site correction -13..-388 on 8/8 client-seeds")
a0fork(2); a0fork(1)

R1 = lambda: [wire("r1", "ugrant.I0", "wr1g"), sp("ugrant", "I0", "r1")]
add(id="bd_arbiter.rt1", cell="bd_arbiter", catalogue_row="A2", combine="any",
    obligation="RT1 grant exclusion across a 1 -> 2 handover (g1 falls before g2 rises)",
    inequality="wr1g + g1f1 <= wr1s + Rf1 + smin + wa0s + qf + wq + g2r  OR  g1fq <= g2r (w* include the physical pin's site delay)",
    forms=[form([R1() + [lut("ugrant", "I0", "O5", "g1f1")]],
                [[wire("r1", "ustate.I0", "wr1s"), sp("ustate", "I0", "r1"), lut("ustate", "I0", "O5", "Rf1"),
                  env("smin", "server minimum response R0 edge -> A0 edge (H_SERVER_MIN), incl. R0/A0 routes up to the A0 divergence", "smin"),
                  wire("A0", "ustate.I4", "wa0s"), sp("ustate", "I4", "A0"), lut("ustate", "I4", "O6", "qf"),
                  wire("ustate.O6", "ugrant.I2", "wq"), sp("ugrant", "I2", "q"), lut("ugrant", "I2", "O6", "g2r")]],
                launch="r1 fall at the client driver", note="race disjunct"),
           form([[lut("ugrant", "I2", "O5", "g1fq")]], [[lut("ugrant", "I2", "O6", "g2r")]], launch="q fall at ugrant.I2", note="structural disjunct (holds at FAST_MIN: rt1_fast_structural, +3 ps)")],
    lean=[L("Cells/ArbHeldTimed", "rt1_exclusion", "sufficient"), L("Cells/ArbHeldTimed", "rt1_counter", "counter_trace"),
          L("Cells/ArbHeldTimed", "rt1_counter_minserver", "necessary", note="for a server answering in exactly smin"),
          L("Cells/ArbCorners", "RT1_iff", "reduction"), L("Cells/ArbCorners", "rt1_fast_structural", "corner")],
    exactness="exact", exactness_note="exact with a min-response server.",
    site_pins={"needed": True, "roles": ["ugrant.I0 hi", "ustate.I0, ustate.I4, ugrant.I2 lo"]},
    rule={"rule": "none", "verdict": "none", "detail": "UNCHECKED"},
    corner=dict(CORNER_BOTH, note="RT1 as a whole cannot fail at FAST_MIN (structural); check the race disjunct at SLOW_MAX with guard As - Af/k"),
    check_scope="route_plus_env", evidence="arc-only: 496 SLOW_MAX / 180 FAST_MIN / 72 box (slow_arc_only etc.)")
add(id="bd_arbiter.rt1b", cell="bd_arbiter", catalogue_row="A4", combine="any",
    obligation="RT1b grant exclusion across a 2 -> 1 handover",
    inequality="wr2g + g2f <= wr2s + Rf2 + smin + wa0s + qr + wq + g1rq  OR  g2f <= g1rq",
    forms=[form([[wire("r2", "ugrant.I1", "wr2g"), sp("ugrant", "I1", "r2"), lut("ugrant", "I1", "O6", "g2f")]],
                [[wire("r2", "ustate.I1", "wr2s"), sp("ustate", "I1", "r2"), lut("ustate", "I1", "O5", "Rf2"), env("smin", "server minimum response", "smin"),
                  wire("A0", "ustate.I4", "wa0s"), sp("ustate", "I4", "A0"), lut("ustate", "I4", "O6", "qr"),
                  wire("ustate.O6", "ugrant.I2", "wq"), sp("ugrant", "I2", "q"), lut("ugrant", "I2", "O5", "g1rq")]],
                launch="r2 fall at the client driver", note="race disjunct"),
           form([[lut("ugrant", "I2", "O6", "g2f")]], [[lut("ugrant", "I2", "O5", "g1rq")]], launch="q rise at ugrant.I2", note="structural disjunct (holds at SLOW_MAX only)")],
    lean=[L("Cells/ArbHeldTimed2", "rt1_exclusion2", "sufficient"), L("Cells/ArbHeldTimed2", "rt1_counter2_minserver", "necessary"),
          L("Cells/ArbCorners", "RT1b_iff", "reduction"), L("Cells/ArbCorners", "rt1b_slow_structural", "corner"), L("Cells/ArbCorners", "rt1b_fast_race", "corner")],
    exactness="exact", site_pins={"needed": True, "roles": ["ugrant.I1 hi", "ustate.I1, ustate.I4, ugrant.I2 lo"]},
    rule={"rule": "none", "verdict": "none", "detail": "UNCHECKED"},
    corner=dict(CORNER_BOTH, note="a SLOW_MAX-only check of RT1b says nothing: structural at SLOW_MAX, can fail at FAST_MIN (rt1b_fast_race)"),
    check_scope="route_plus_env")

def rt2(k):
    o, j = k, 3 - k
    sfx = "" if k == 1 else "2"
    qe = "qf" if k == 1 else "qr"
    gname = f"g{k}"
    gf = "g1f1" if k == 1 else "g2f"
    gout = "O5" if k == 1 else "O6"
    rpin = "I0" if k == 1 else "I1"
    base_req = [wire("A0", "ustate.I4", "wa0s"), sp("ustate", "I4", "A0"), lut("ustate", "I4", "O6", qe),
                fbw("ustate", "O6", "I2", "wfb"), sp("ustate", "I2", "q fb"), lut("ustate", "I2", "O5", "Rrq"), env("smin", "server minimum response", "smin")]
    loop = [lut(f"ua{k}", "{I0|I1}", "O6", f"c{k}f"), fbw(f"ua{k}", "O6", "I2", f"wfa{k}"), sp(f"ua{k}", "I2", "feedback")]
    gpath = [wire(f"r{k}", f"ugrant.{rpin}", f"wr{k}g"), sp("ugrant", rpin, f"r{k}"), lut("ugrant", rpin, gout, f"g{k}f" + ("1" if k == 1 else "")),
             wire(f"ugrant.{gout}", f"ua{k}.I0", f"wg{k}"), sp(f"ua{k}", "I0", "grant")]
    rpath = [wire(f"r{k}", f"ustate.{rpin}", f"wr{k}s"), sp("ustate", rpin, f"r{k}"), lut("ustate", rpin, "O5", f"Rf{k}"), env("smin", "server minimum response (first)", "smin")]
    fork_other = [wire("A0", f"ua{j}.I1", f"wa0{j}"), sp(f"ua{j}", "I1", "A0"), lut(f"ua{j}", "I1", "O6", f"c{j}r")]
    rows = {
        "pulse": ("A0's low pulse at ua_k outlasts ua_k's fall loop",
                  f"c{k}f + wfa{k} <= wa0s + {qe} + wfb + Rrq + smin",
                  form([loop], [base_req], launch="A0 fall at ua_k / ustate divergence (A0 driver)")),
        gname: (f"{gname}'s fall reaches ua{k} and the loop closes before A0 rises again",
                f"wr{k}g + {gf} + wg{k} + c{k}f + wfa{k} <= wr{k}s + Rf{k} + 2 smin + wa0s + {qe} + wfb + Rrq + wa0{k}",
                form([gpath + loop], [rpath + base_req + [wire("A0", f"ua{k}.I1", f"wa0{k}"), sp(f"ua{k}", "I1", "A0")]], launch=f"r{k} fall at the client driver")),
        "forkA": (f"A{k} falls before A{j} can rise (A0 fork skew between ua{k} and ua{j})",
                  f"wa0{k} + c{k}f <= wa0s + {qe} + wfb + Rrq + smin + wa0{j} + c{j}r",
                  form([[wire("A0", f"ua{k}.I1", f"wa0{k}"), sp(f"ua{k}", "I1", "A0"), lut(f"ua{k}", "I1", "O6", f"c{k}f")]], [base_req + fork_other], launch="A0 fall at the A0 driver")),
        "forkG": (f"the same along {gname}'s path",
                  f"wr{k}g + {gf} + wg{k} + c{k}f <= wr{k}s + Rf{k} + 2 smin + wa0s + {qe} + wfb + Rrq + wa0{j} + c{j}r",
                  form([gpath + [lut(f"ua{k}", "I0", "O6", f"c{k}f")]], [rpath + base_req + fork_other], launch=f"r{k} fall at the client driver")),
    }
    for name, (what, ineq, f) in rows.items():
        nm = name if k == 1 else (name + "2" if name != gname else gname)
        lean = ([L("Cells/ArbHeldTimed", "rt2_exclusion_arcs", "sufficient"), L("Cells/ArbHeldTimed", "A1_low_after", "sufficient"),
                 L("Cells/ArbHeldTimed", "rt2_counter", "counter_trace"), L("Cells/ArbHeldTimed", "A1_stuck", "counter_trace"),
                 L("Cells/ArbCorners", "RT2_iff", "reduction")] if k == 1 else
                [L("Cells/ArbHeldTimed2", "rt2_exclusion2_arcs", "sufficient"), L("Cells/ArbHeldTimed2", "rt2_counter2", "counter_trace"),
                 L("Cells/ArbHeldTimed2", "A2_stuck2", "counter_trace"), L("Cells/ArbCorners", "RT2b_iff", "reduction")])
        ex, exn = "sufficient", "sufficient (arc form valid for every server); counter-traces when violated."
        if name == "pulse":
            lean += [L("Cells/ArbHeldTimed2", "A1_band", "necessary"), L("Cells/ArbHeldTimed2", "A1_band_overlap_matched", "necessary", note="matched fork: every shorter pulse overlaps")]
            if k == 2:
                lean += [L("Cells/ArbCorners", "pulse2_zero_routing", "corner", note="7j's wfa2+16 is a corner-mix artefact")]
            ex, exn = "sufficient+necessary_matched_fork", "pulse is also NECESSARY in the matched-fork case (A1_band_overlap_matched)."
        add(id=f"bd_arbiter.rt2{'' if k == 1 else 'b'}_{nm}", cell="bd_arbiter", catalogue_row="A3" if k == 1 else "A4",
            obligation=f"RT2{'' if k == 1 else 'b'} ack exclusion, field {name}: {what}",
            inequality=ineq, forms=[f], lean=lean, exactness=ex, exactness_note=exn,
            site_pins={"needed": True, "roles": ["every w* term includes the physical pin's site delay (7h notation)"]},
            rule={"rule": "none", "verdict": "none", "detail": "UNCHECKED"},
            corner=dict(CORNER_1C, note="arc parts per corner in ArbCorners (arcs_slowMax / arcs_fastMin / box_7h, box_7j); flip window 37-216 ps"),
            check_scope="route_plus_env")
rt2(1); rt2(2)
add(id="bd_arbiter.server_min", cell="bd_arbiter", catalogue_row="A5",
    obligation="H_SERVER_MIN, Scn.H_SETTLED, H_REQ_STEADY: server minimum response; A0 rise reached ustate/ua1 before r1 falls",
    inequality="smin = min R0-edge -> A0-edge (environment); A0 rise -> ustate (+qf), ua1 (+c1f) before r1 fall", forms=[],
    lean=[L("Cells/ArbHeldTimed", "rt1_exclusion", "uses", note="Server relation and Scn hypotheses")],
    status="proved", exactness="hypothesis", site_pins={"needed": False, "roles": []},
    rule={"rule": "none", "verdict": "none"}, corner=CORNER_1C, check_scope="environment")
add(id="bd_arbiter.alternation", cell="bd_arbiter", catalogue_row="A6",
    obligation="H_Q_BEFORE_REREQ (h2): a client does not re-raise its request while q is excited (fairness, not safety)",
    inequality="protocol", forms=[],
    lean=[L("Cells/ArbBinary", "arbiter_alternates", "sufficient"), L("Cells/ArbBinary", "need_h2", "necessary")],
    exactness="sufficient+necessary", site_pins={"needed": False, "roles": []}, rule={"rule": "none", "verdict": "none"},
    corner=CORNER_NA, check_scope="protocol")
add(id="bd_arbiter.ack_celements", cell="bd_arbiter", catalogue_row="A7",
    obligation="ua1/ua2 (bd_c2): C-element obligations pulse_width, env_latency, sel_order",
    inequality="see bd_c2.pulse_width, bd_c2.env_latency, bd_c2.sel_order with instance ua_k", forms=[], refers_to=["bd_c2.pulse_width", "bd_c2.env_latency", "bd_c2.sel_order"],
    lean=[L("Cells/CElemTiming", "c2_four_phase", "sufficient")], exactness="see_refers_to",
    site_pins={"needed": True, "roles": ["ua_k.I2 hi"]}, rule={"rule": "none", "verdict": "none"}, corner=CORNER_1C, check_scope="route_plus_env",
    evidence="Bp box E_need: ua1 +332 [+167,+600], ua2 +351 [+103,+598]")

# =============================================================== bd_mux
for xa, jn, other in [("uxa", "j0", "uj1"), ("uya", "j1", "uj0")]:
    add(id=f"bd_mux.{xa}_rtz", cell="bd_mux", also_applies_to=["bdc_muxn (generated)"], catalogue_row="X1",
        obligation=f"H_RTZ (cell level): z_ack's low pulse at {xa}'s pins outlasts {xa}'s LUT + own feedback",
        inequality=f"te + dlmax + dwmax <= tr (te: {jn} and z_ack both low at {xa}'s pins; tr: z_ack re-rise at the pin)",
        forms=[form([[lut(xa, "{I0|I1}", "O6", "dlmax"), fbw(xa, "O6", "I2", "dwmax"), sp(xa, "I2", "feedback")]],
                    [[env("zack_low", f"z_ack low at {xa}.I1 from te to the re-rise tr, min")]], launch=f"te at {xa}'s pins")],
        lean=[L("Cells/MuxRtzTimed", "rtz_safe", "sufficient"), L("Cells/MuxRtzTimed", "rtz_exact_safe", "sufficient", note="the safe half of the fixed-delay exactness (w >= dl + dw); the other half is rtz_counter"),
              L("Cells/MuxRtzTimed", "rtz_counter", "counter_trace", note="perpetual runt train, spurious ack"), L("Cells/MuxRtzTimed", "rtz_counter_loop", "counter_trace"),
              L("Cells/MuxRtzTimed", "rtz_inertial_lost", "counter_trace", note="inertial: wrong latch"), L("Cells/MergeMuxSI", "mux_needs_rtz", "necessary", note="untimed")],
        exactness="exact", exactness_note="exact for fixed delays (w >= dl+dw safe; 0 < w < dl+dw oscillates). rtz_safe is stated for any bd_c2 loop with a low j input, so it covers uya too.",
        site_pins={"needed": True, "roles": [f"{xa}.I2 (feedback) hi", f"{xa}.I1 (z_ack) in the env form"]},
        rule={"rule": "none", "verdict": "none", "detail": "UNCHECKED (no uxa/RTZ rule in tighten.py)"},
        corner=CORNER_1C, check_scope="route_plus_env")
    add(id=f"bd_mux.{xa}_rtz_env", cell="bd_mux", also_applies_to=["bdc_muxn (generated)"], catalogue_row="X1",
        obligation=f"H_RTZ_ENV: z_ack fall reaching {xa} plus its loop beats the control token's round trip back to z_ack's rise at {xa}",
        inequality=f"W{xa[1:]} + dlmax + dwmax <= wzc + dc + wcr + {'dl1' if xa == 'uxa' else 'dl0'} + wjo + dlo + dz + ds + w{xa[1:]} (all right terms min; Lean: te + dlmax + dwmax <= Tzf + (...) + w{xa[1:]}); conservative baseline W{xa[1:]} - w{xa[1:]} + dlmax + dwmax <= sum of (N+4) min arcs + (N+4) min hops",
        forms=[form([[wire("z_ack.drv", f"{xa}.I1", f"W{xa[1:]}"), sp(xa, "I1", "z_ack"), lut(xa, "I1", "O6", "dlmax"), fbw(xa, "O6", "I2", "dwmax"), sp(xa, "I2", "feedback")]],
                    [[wire("z_ack.drv", "ctl.sender", "wzc"), env("dc", "control sender: ctl_ack low seen -> ctl_req rise (bd_link sender: floop_causal)", "dc"),
                      wire("ctl_req", f"{other}.I1", "wcr"), sp(other, "I1", "ctl_req"), lut(other, "I1", "O6", "dl1" if xa == "uxa" else "dl0"),
                      wire(f"{other}.O6", "uor.I0|I1", "wjo"), lut("uor", "{I0|I1}", "O6", "dlo"), line("udly", "rise", "chain", "DELAY hops", "dz"),
                      env("ds", "server: z_req rise -> z_ack rise, min", "ds"), wire("z_ack.drv", f"{xa}.I1", f"w{xa[1:]}"), sp(xa, "I1", "z_ack")]],
                    launch="z_ack fall at its driver (Tzf)",
                    note="1C at each corner: loop at the corner's MIN, uxa at the same corner's MAX")],
        lean=[L("Cells/MuxRtzTimed", "mux_rtz_env_safe", "sufficient" if xa == "uxa" else "mirror"), L("Cells/MuxRtzTimed", "floop_causal", "lemma")]
             + ([] if xa == "uxa" else [L("Cells/ConstraintsMux", "mux_rtz_env_safe_uya", "sufficient", note="H_RTZ_ENV for uya: uj0's real INIT 0000AE08 (uj0_eq), uor pins swapped (H_J1_OR); y_ack low on [te+dlmax, t2+dlmin]"),
                                        L("Cells/ConstraintsMux", "uj0_eq", "function_equality"), L("Cells/ConstraintsMux", "uj0_blocked", "lemma", note="a low ctl_req pin holds uj0 at 0")]),
        status="proved",
        exactness="sufficient",
        exactness_note="env bound tightness argued, not proved." if xa == "uxa" else "P3 (B-constraints-more.md): mux_rtz_env_safe_uya, sufficient; env bound tightness argued, not proved (as uxa). Cell-level exactness: rtz_safe / rtz_counter are stated for any bd_c2 loop with a held-low j input, so they apply to uya verbatim (comment, no separate theorem).",
        site_pins={"needed": True, "roles": [f"{xa}.I1 (z_ack) hi and lo", f"{xa}.I2 hi", f"{other}.I1 lo"]},
        rule={"rule": "none", "verdict": "none", "detail": "UNCHECKED"},
        corner=CORNER_1C, check_scope="route_plus_env",
        evidence="fast_adv_N0_fails -7 raw; fast_adv N = 2: +405 raw / -6 guarded (fail); reachable in bdc loop-header mux")
add(id="bd_mux.bundled_s_setup", cell="bd_mux", also_applies_to=["bdc_muxn"], catalogue_row="X3",
    obligation="H_BUNDLED_S_PIN (setup half): s settled at each join pin before ctl_req rises there",
    inequality="t_req,min >= t_sel,max at uj0/uj1 pins, from a common launch",
    forms=[form([[env("s_path", "common launch -> s net driver", "Ts"), wire("s", f"{u}.I2", "shi"), sp(u, "I2", "select"), lut(u, "I2", "O6", "shi")] for u in ("uj0", "uj1")],
                [[env("req_path", "common launch -> ctl_req driver", "Tc"), wire("ctl_req", f"{u}.I1", "clo"), sp(u, "I1", "ctl_req"), lut(u, "I1", "O6", "clo")] for u in ("uj0", "uj1")],
                launch="control sender's latch/enable event (common launch)", note="Lean H_BUNDLED_S_SETUP_T: Ts + shi <= Tc + clo, per join")],
    lean=[L("Cells/MergeMuxSI", "mux_ok", "sufficient", note="untimed hypothesis"), L("Cells/MergeMuxSI", "mux_needs_bundled_s", "necessary"),
          L("Cells/MergeMuxSI", "mux_needs_bundled_s_hazard", "necessary"), L("Cells/MergeMuxSI", "mux_weak_broad_fails", "necessary")] + [L("Cells/ConstraintsMux", "uj0_unsel_low_timed", "sufficient", note="unselected join stays low until the next ctl_req rise; H_BUNDLED_S_SETUP_T Ts + shi <= Tc + clo, H_BUNDLED_S_HOLD_T Tcf + chi <= Ts' + slo, join low for one loop window"),
          L("Cells/ConstraintsMux", "uj1_unsel_low_timed", "sufficient"), L("Cells/ConstraintsMux", "unsel_low_timed", "sufficient", note="generic join form"),
          L("Cells/ConstraintsMux", "uj0_selected_c2", "sufficient", note="while s reads definitely at the selecting value, the join's gate IS bd_c2 on (req, ctl_req): every C-element theorem applies"),
          L("Cells/ConstraintsMux", "uj1_selected_c2", "sufficient"),
          L("Cells/ConstraintsMux", "j0_sel_is_c2", "function_equality", note="all 81 Kleene rows"), L("Cells/ConstraintsMux", "j1_sel_is_c2", "function_equality"),
          L("Cells/ConstraintsMux", "j0_s_x_hazard", "necessary", note="Kleene, at the select: s mid-edge while req and ctl_req are high gives x (per-pin form of mux_needs_bundled_s_hazard; not a full trace)")],
    exactness="sufficient", exactness_note="P3 (B-constraints-more.md): proved at the join pins (ConstraintsMux, Bundling window model, real INITs), sufficient; necessity at the select by Kleene (j0_s_x_hazard) and untimed (mux_needs_bundled_s*). NOT covered: the composition with the rest of the mux (mux_ok is still untimed). Each window (shi/slo, chi/clo) includes the route, the site pin and the uj pin arc.",
    site_pins={"needed": True, "roles": ["uj*.I2 (s) hi", "uj*.I1 (ctl_req) lo"]},
    rule={"rule": "E (skew.py), D (screen)", "verdict": "exact_structure_missing_site_pins", "detail": "common launch, 0.772/1.155; neither adds SP terms (C-10b ruleE_sitepin_fails_all)"},
    corner=CORNER_1C, check_scope="static_route")
add(id="bd_mux.bundled_s_hold", cell="bd_mux", also_applies_to=["bdc_muxn", "bd_steer (steer_s_x_while_req)"], catalogue_row="X3",
    obligation="H_BUNDLED_S_PIN (hold half): s moves at a join pin only while ctl_req is low there",
    inequality="ctl_req fall at the pin (hi) <= next s change at the pin (lo)",
    forms=[form([[env("req_fall", "common launch -> ctl_req fall at driver", "Tcf"), wire("ctl_req", f"{u}.I1", "chi"), sp(u, "I1", "ctl_req"), lut(u, "I1", "O6", "chi")] for u in ("uj0", "uj1")],
                [[env("s_change", "common launch -> next s change at driver", "Ts'"), wire("s", f"{u}.I2", "slo"), sp(u, "I2", "select"), lut(u, "I2", "O6", "slo")] for u in ("uj0", "uj1")],
                launch="sender event", note="Lean H_BUNDLED_S_HOLD_T: Tcf + chi <= Ts' + slo, per join")],
    lean=[L("Cells/MergeMuxSI", "mux_ok", "sufficient"), L("Cells/LibCtlMergeMux", "steer_s_x_while_req", "necessary", note="bd_steer")] + [L("Cells/ConstraintsMux", "uj0_unsel_low_timed", "sufficient", note="unselected join stays low until the next ctl_req rise; H_BUNDLED_S_SETUP_T Ts + shi <= Tc + clo, H_BUNDLED_S_HOLD_T Tcf + chi <= Ts' + slo, join low for one loop window"),
          L("Cells/ConstraintsMux", "uj1_unsel_low_timed", "sufficient"), L("Cells/ConstraintsMux", "unsel_low_timed", "sufficient", note="generic join form"),
          L("Cells/ConstraintsMux", "uj0_selected_c2", "sufficient", note="while s reads definitely at the selecting value, the join's gate IS bd_c2 on (req, ctl_req): every C-element theorem applies"),
          L("Cells/ConstraintsMux", "uj1_selected_c2", "sufficient"),
          L("Cells/ConstraintsMux", "j0_sel_is_c2", "function_equality", note="all 81 Kleene rows"), L("Cells/ConstraintsMux", "j1_sel_is_c2", "function_equality"),
          L("Cells/ConstraintsMux", "j0_s_x_hazard", "necessary", note="Kleene, at the select: s mid-edge while req and ctl_req are high gives x (per-pin form of mux_needs_bundled_s_hazard; not a full trace)")],
    exactness="sufficient", exactness_note="P3 (B-constraints-more.md): proved at the join pins (ConstraintsMux, Bundling window model, real INITs), sufficient; necessity at the select by Kleene (j0_s_x_hazard) and untimed (mux_needs_bundled_s*). NOT covered: the composition with the rest of the mux (mux_ok is still untimed). Each window (shi/slo, chi/clo) includes the route, the site pin and the uj pin arc.", site_pins={"needed": True, "roles": ["uj*.I1 hi", "uj*.I2 lo"]},
    rule={"rule": "none", "verdict": "none", "detail": "UNCHECKED"}, corner=CORNER_1C, check_scope="static_route")
add(id="bd_mux.bundled_z", cell="bd_mux", catalogue_row="X5",
    obligation="H_BUNDLED_Z: z_req after the datamux select has settled (matched DELAY)",
    inequality="select cone + datamux (hi) <= uor + udly rise (lo), from the join edge; Lean (consumer side) H_BUNDLED_Z_T Tz + zhi <= Ton + ehi with the consumer's H_PW and H_HOLD",
    forms=[form([[env("datamux", "s -> udat LUTs -> z_data, hi")]], [[lut("uor", "{I0|I1}", "O6"), line("udly", "rise", "chain", "DELAY hops")]], launch="join edge",
                note="this form bounds Tz + zhi by the request path's lower bound; with Ton >= join edge + uor + line + C-element it implies the Lean H_BUNDLED_Z_T (composition left to the reader with Bundling.sym_edge / slow_not_early_ps, not one theorem)")],
    lean=[L("Cells/MergeMuxSI", "mux_ok", "sufficient", note="untimed hypothesis"),
          L("Cells/ConstraintsMux", "bundled_z_capture", "sufficient", note="consumer bit captures the selected value: H_BUNDLED_Z_T Tz + zhi <= Ton + ehi (rule A's form), H_PW, H_HOLD"),
          L("Cells/ConstraintsMux", "dm_settles", "sufficient", note="z is the selected value from max(Ts + shi, Td + dhi)"),
          L("Cells/ConstraintsMux", "dm_odd_kleene", "function_equality", note="bd_datamux INIT E4"), L("Cells/ConstraintsMux", "dm_pair_o5_kleene", "function_equality"),
          L("Cells/ConstraintsMux", "dm_pair_o6_kleene", "function_equality", note="FFAA_5500_E4E4_E4E4"),
          L("Cells/Bundling", "setup_not_classic", "context", note="the exact condition is H_SETUP against the enable fall; the classic form is sufficient, not necessary")],
    exactness="sufficient", exactness_note="P3 (B-constraints-more.md): proved in the classic form (bundled_z_capture via Bundling.classic_implies_setup), sufficient, not necessary (the exact condition is the consumer's H_SETUP, Bundling.setup_not_classic). The request path lower bound is a composition, not a single theorem.",
    site_pins={"needed": True, "roles": ["udat select pin"]}, rule={"rule": "A", "verdict": "rule_is_the_check"}, corner=CORNER_1C)
# --------------------------------------------------------------- timed operator cells (probe P5: B-ops-timed.md, B-ops-timed2.md)
# OpsTimed* model: binary FIFO LUT arcs lumped over the pins (H_LUT_FIFO), one FIFO
# channel per fork branch (H_WIRE_FIFO, never isochronic by assumption), feedback
# nets as window channels [wl, wh]. Site pins are inside the Lean wire windows; they
# are listed as separate site_pin arcs so that the checker charges them.
OPS_X = "OpsTimed* (B-ops-timed.md, B-ops-timed2.md): every Ret window (W*, L*, Dz) is lo/hi of one routed arc incl. its site pin; LUT arcs are lumped over pins (per-pin LUT arcs not modelled: charge them as listed, hi on the data side, lo on the request side). Sufficient; necessity not shown (negative controls only show the term is used)."
CORNER_OPS = dict(CORNER_1C, note="Lean windows: take every lo and hi of one form from the same prjxray column (FAST_MIN, then SLOW_MAX); the lumped LUT arc is O6 45/124 (flat) or the per-pin O5 column")

# Probe Lt3 (B-ops-counter.md, Formal/Cells/OpsCounter.lean). OpsCounter.lean is
# git-tracked since e54d7ca (probe P6), so its theorems are cited as references.
OPSCOUNTER_TRACKED = True
def OC(name, role, note=None):
    return [L("Cells/OpsCounter", name, role, note=note)] if OPSCOUNTER_TRACKED else []
# Probe Lt4 (B-ops-exact.md, Formal/Cells/OpsExact.lean), probe P6.
def OX(name, role, note=None):
    return [L("Cells/OpsExact", name, role, note=note)]
LT4 = "Lt4 (B-ops-exact.md, OpsExact.lean)"

def Kz(src="{j0|j1}", pins="{I0|I1}"):
    """request/join edge -> z_ack edge at the server, min (Kz = wo + Lor.lo + Dz.lo + Es)."""
    return [wire(src, f"uor.{pins}", "wo"), sp("uor", pins, "join/request"), lut("uor", pins, "O6", "Lor.lo"),
            line("udly", "any", "chain", "uor.O6 -> bd_delay (FASTFALL=0, one FIFO channel) -> z_req at the server", "Dz.lo"),
            env("Es", "server: z_req edge at its pin -> z_ack edge (H_SRV), min", "Es")]

def Kc():
    """mux: z_ack edge -> next join node edge through the control sender, min (Kc = Wzc.lo + Ec + wc + lj)."""
    return [wire("z_ack.drv", "ctl.sender (ctl_ack = z_ack)", "Wzc.lo"),
            env("Ec", "control sender: ctl_ack edge seen -> next ctl_req edge (MuxCausal.H_CTL_C), min", "Ec"),
            wire("ctl_req", "{uj0|uj1}.I1", "wc"), sp("{uj0|uj1}", "I1", "ctl_req"), lut("{uj0|uj1}", "I1", "O6", "lj")]

def Ka():
    """merge: z_ack edge -> next request edge through an ack C-element and a client, min (Ka = wz + la + wa + Eo)."""
    return [wire("z_ack.drv", "{uxa|uya}.I1", "wz"), sp("{uxa|uya}", "I1", "z_ack"), lut("{uxa|uya}", "I1", "O6", "la"),
            wire("{uxa|uya}.O6", "{x|y} client", "wa"),
            env("Eo", "owner: ack edge seen -> request edge; the next requester raises only after the previous owner's ack fell (MergeCausal.H_OWN), min", "Eo")]

def cel(u, pin, src, wsym, lsym, role, fsym):
    return [wire(src, f"{u}.{pin}", wsym), sp(u, pin, role), lut(u, pin, "O6", lsym), fbw(u, "O6", "I2", fsym), sp(u, "I2", "feedback")]

MUX_T = [L("Cells/OpsTimedMux", "mux_timing_of_static", "sufficient", note="MuxTiming derived from MuxCausal + MuxStatic + reset (hRL, hRE)"),
         L("Cells/OpsTimedMux", "mux_ok", "sufficient", note="whole-cell timed handshake: one server transaction per control token, x/y acknowledged exactly in their tokens"),
         L("Cells/OpsTimedMux", "mux_ok_static", "sufficient"),
         L("Cells/OpsTimedMux", "MuxStatic", "definition"), L("Cells/OpsTimedMux", "MuxCausal", "definition"),
         L("Cells/OpsTimedWit", "static", "non_vacuity", note="MuxWit.static: MuxStatic holds on the unit-delay witness (decide)"),
         L("Cells/OpsTimedWit", "witness", "non_vacuity", note="MuxWit.witness: mux_ok applied, alternating selection, causal partners")]
MERGE_T = [L("Cells/OpsTimedMux", "merge_timing_of_static", "sufficient", note="MergeTiming derived from MergeCausal + MergeStatic + reset (hRL, hRE)"),
           L("Cells/OpsTimedMux", "merge_ok", "sufficient", note="whole-cell timed handshake: each server transaction acknowledges exactly its requester"),
           L("Cells/OpsTimedMux", "MergeStatic", "definition"), L("Cells/OpsTimedMux", "MergeCausal", "definition"),
           L("Cells/OpsTimedWit", "static", "non_vacuity", note="MergeWit.static"),
           L("Cells/OpsTimedWit", "witness", "non_vacuity", note="MergeWit.witness")] + \
          OX("merge_ok_noskew", "sufficient", "merge_ok's whole conclusion without H_OR_SKEW (MergeTimingNoSkew)") + \
          OX("merge_timing_ns_of_static", "sufficient", "MergeTimingNoSkew from MergeStaticNS (MergeStatic without S_OR)") + \
          OX("MergeStaticNS", "definition") + OX("MergeWit.noskew_witness", "non_vacuity")
STEER_T = [L("Cells/OpsTimed2", "steer_ok_static", "sufficient", note="steer_ok under SteerCausal + SteerStatic"),
           L("Cells/OpsTimed2", "steer_env_of_static", "sufficient", note="derives every SteerEnv field (H_S_PIN via steer_s_pin_of_wire, H_ACK_SKEW via steer_gap_causal + fst_order)"),
           L("Cells/OpsTimed2", "SteerStatic", "definition"), L("Cells/OpsTimed2", "SteerCausal", "definition"),
           L("Cells/OpsTimed", "steer_ok", "sufficient", note="each token reaches exactly its branch; one acknowledge per token"),
           L("Cells/OpsTimed2", "static_witness", "non_vacuity", note="SteerWit.static_witness: SteerStatic by decide on the unit-delay steer")]

add(id="bd_mux.isochronic_forks", cell="bd_mux", catalogue_row="X4",
    obligation="z_ack -> {uxa, uya, ctl sender} fork (S_XA_FORK / S_YA_FORK): z_ack's edge settles each ack C-element's loop before the next join edge, launched by the same z_ack edge through the control sender, reaches it; the ctl_req -> {uj0, uj1} fork needs no condition under FIFO branches (H_CTL_SEQ follows from causality)",
    inequality="Wzx.hi + Lxa.hi + wxah <= Kc + W0x.lo and Wzy.hi + Lya.hi + wyah <= Kc + W1y.lo; Kc = Wzc.lo + Ec + wc + lj",
    forms=[form([cel("uxa", "I1", "z_ack.drv", "Wzx.hi", "Lxa.hi", "z_ack", "wxah")], [Kc() + [wire("j0", "uxa.I0", "W0x.lo"), sp("uxa", "I0", "j0")]],
                launch="z_ack edge at its driver", note="S_XA_FORK"),
           form([cel("uya", "I1", "z_ack.drv", "Wzy.hi", "Lya.hi", "z_ack", "wyah")], [Kc() + [wire("j1", "uya.I0", "W1y.lo"), sp("uya", "I0", "j1")]],
                launch="z_ack edge at its driver", note="S_YA_FORK")],
    lean=MUX_T + [L("Cells/MergeMuxSI", "mux_ok", "sufficient", note="untimed, isochronic forks assumed"),
                  L("Cells/MergeMuxSI", "mux_needs_iso_za", "necessary", note="untimed"),
                  L("Cells/MergeMuxSI", "mux_needs_iso_cr", "necessary", note="untimed: two transitions in flight on one ctl_req branch, which a FIFO wire excludes by assumption")],
    status="proved", exactness="sufficient",
    exactness_note="Lt3 (OpsCounter.lean mux_ok_noskew): mux_ok's conclusions hold without H_OR_SKEW and without H_CTL_SEQ, confirming the ctl_req branch needs nothing. P5: timed sufficient form from mux_timing_of_static (S_XA_FORK, S_YA_FORK) + mux_ok, lumped LUT arcs, FIFO fork branches; with FIFO branches 'same transition seen consistently' is automatic, so the numeric condition is the z_ack branch only. Untimed necessity (mux_needs_iso_*) still cited; no timed counter-trace. " + OPS_X,
    site_pins={"needed": True, "roles": ["uxa.I1, uya.I1 (z_ack) hi", "uxa.I2, uya.I2 (feedback) hi", "uj*.I1 (ctl_req) lo", "uxa.I0, uya.I0 (join) lo"]},
    rule={"rule": "none", "verdict": "none", "detail": "UNCHECKED"}, corner=CORNER_OPS, check_scope="route_plus_env")
add(id="bd_mux.uj_env_latency_req", cell="bd_mux", catalogue_row="X (new, B-ops-timed)", also_applies_to=["bd_c2.env_latency (the join is a C-element while s reads its value: ConstraintsMux.uj0_selected_c2)"],
    obligation="H_DEP_J0/J1 through the client (S_J0_X / S_J1_Y): the join's own feedback settles before the client's answer (x_ack -> client -> x_req) returns to the join",
    inequality="Lj0.hi + wj0h <= Lj0.lo + W0x.lo + Lxa.lo + Wxa.lo + Ex + Wx.lo (uj1: Lj1, wj1h, W1y, Lya, Wya, Ey, Wy)",
    forms=[form([[lut(u, "{I0|I1}", "O6", f"{L_}.hi"), fbw(u, "O6", "I3", f"{wh}"), sp(u, "I3", "feedback")]],
                [[lut(u, "{I0|I1}", "O6", f"{L_}.lo"), wire(j, f"{a}.I0", f"{W}.lo"), sp(a, "I0", j), lut(a, "I0", "O6", f"{La}.lo"),
                  wire(f"{a}.O6", f"{c} client", f"{Wa}.lo"), env(E_, f"{c} client: ack edge seen -> request edge (MuxCausal.H_{c.upper()}C_*), min", E_),
                  wire(f"{c}_req", f"{u}.I0", f"{Wc}.lo"), sp(u, "I0", f"{c}_req")]],
                launch=f"phase start at {u}'s pins (c{u[-1]} j)", note=nm)
           for u, j, a, c, L_, wh, W, La, Wa, E_, Wc, nm in [("uj0", "j0", "uxa", "x", "Lj0", "wj0h", "W0x", "Lxa", "Wxa", "Ex", "Wx", "S_J0_X"),
                                                            ("uj1", "j1", "uya", "y", "Lj1", "wj1h", "W1y", "Lya", "Wya", "Ey", "Wy", "S_J1_Y")]],
    lean=MUX_T, exactness="sufficient", exactness_note="P5: field S_J0_X / S_J1_Y of MuxStatic, discharging MuxTiming.H_DEP_J0/J1. The bd_c2.env_latency form instantiated at the join (different INIT, same loop). " + LT4 + " section 5 (analysis, NOT proved): only sufficient as stated: the x return path also waits for z_ack (cx = max(A0, ZA0), ZA0 >= E + Kz + Wzx.lo), so W0x.lo could be replaced by max(W0x.lo, Kz + Wzx.lo); in a realistic netlist Kz dominates and this form has slack. No counter-run. " + OPS_X,
    site_pins={"needed": True, "roles": ["uj*.I3 (feedback) hi", "uj*.I0 (req) lo", "uxa/uya.I0 lo"]},
    rule={"rule": "none", "verdict": "none", "detail": "UNCHECKED"}, corner=CORNER_OPS, check_scope="route_plus_env")
add(id="bd_mux.uj_env_latency_ctl", cell="bd_mux", catalogue_row="X (new, B-ops-timed)",
    obligation="H_DEP_J0/J1 through the server and the control sender (S_J0_C / S_J1_C): the join's own feedback settles before z_req -> z_ack -> control sender -> ctl_req returns to the join",
    inequality="Lj0.hi + wj0h <= Lj0.lo + Kz + Wzc.lo + Ec + Wc0.lo (uj1: Wc1); Kz = wo + Lor.lo + Dz.lo + Es",
    forms=[form([[lut(u, "{I0|I1}", "O6", f"{L_}.hi"), fbw(u, "O6", "I3", wh), sp(u, "I3", "feedback")]],
                [[lut(u, "{I0|I1}", "O6", f"{L_}.lo")] + Kz(j, "I0" if u == "uj0" else "I1")
                 + [wire("z_ack.drv", "ctl.sender", "Wzc.lo"), env("Ec", "control sender latency, min", "Ec"), wire("ctl_req", f"{u}.I1", f"{Wc}.lo"), sp(u, "I1", "ctl_req")]],
                launch=f"phase start at {u}'s pins", note=nm)
           for u, j, L_, wh, Wc, nm in [("uj0", "j0", "Lj0", "wj0h", "Wc0", "S_J0_C"), ("uj1", "j1", "Lj1", "wj1h", "Wc1", "S_J1_C")]],
    lean=MUX_T, exactness="sufficient", exactness_note="P5: MuxStatic.S_J0_C / S_J1_C. " + OPS_X,
    site_pins={"needed": True, "roles": ["uj*.I3 hi", "uj*.I1 (ctl_req) lo", "uor.I0/I1 lo"]},
    rule={"rule": "none", "verdict": "none", "detail": "UNCHECKED"}, corner=CORNER_OPS, check_scope="route_plus_env")
add(id="bd_mux.uxa_join_latency", cell="bd_mux", catalogue_row="X (new, B-ops-timed)", also_applies_to=["bd_c2.env_latency at uxa/uya (join input)"],
    obligation="H_DEP_XA/YA against the join input (S_XA_J / S_YA_J): j's edge at uxa outlasts uxa's loop until the next j edge and until the next z_ack edge",
    inequality="W0x.hi + Lxa.hi + wxah <= Kz + Kc + W0x.lo and <= 2 Kz + Kc + Wzx.lo (uya: W1y, Lya, wyah, Wzy)",
    forms=[f for a, j, W, La, wh, Wz in [("uxa", "j0", "W0x", "Lxa", "wxah", "Wzx"), ("uya", "j1", "W1y", "Lya", "wyah", "Wzy")]
           for f in (form([cel(a, "I0", j, f"{W}.hi", f"{La}.hi", j, wh)], [Kz() + Kc() + [wire(j, f"{a}.I0", f"{W}.lo"), sp(a, "I0", j)]],
                          launch="join node edge (E j)", note=f"S_{a[1:].upper()}_J (1): next j edge"),
                     form([cel(a, "I0", j, f"{W}.hi", f"{La}.hi", j, wh)], [Kz() + Kc() + Kz() + [wire("z_ack.drv", f"{a}.I1", f"{Wz}.lo"), sp(a, "I1", "z_ack")]],
                          launch="join node edge (E j)", note=f"S_{a[1:].upper()}_J (2): next z_ack edge"))],
    lean=MUX_T, exactness="sufficient", exactness_note="P5: MuxStatic.S_XA_J / S_YA_J (arc-level instance of bd_c2.env_latency at the ack C-element's join input). " + OPS_X,
    site_pins={"needed": True, "roles": ["uxa/uya.I0 hi and lo", "uxa/uya.I2 hi", "uxa/uya.I1 lo"]},
    rule={"rule": "none", "verdict": "none", "detail": "UNCHECKED"}, corner=CORNER_OPS, check_scope="route_plus_env")
add(id="bd_mux.reset_first", cell="bd_mux", catalogue_row="X (new, B-ops-timed)",
    obligation="H_RST_LONG + H_RST_EARLY for the mux's C-elements (uj0, uj1, uxa, uya): reset outlasts every wire and loop, and is released before the first edge reaches each C-element",
    inequality="Wx.hi, Wy.hi, Wc0.hi, Wc1.hi, Lj*.hi + wj*h, Lj*.hi + W0x/W1y.hi, Wzx.hi, Wzy.hi, Lxa.hi + wxah, Lya.hi + wyah <= R; R <= first edge at each C-element pin (Xp 0, D0 0, Yp 0, D1 0, A0 0, ZA0 0, A1 0, ZA1 0)",
    forms=[form([[lut("{uj0|uj1|uxa|uya}", "{I0|I1}", "O6", "L*.hi"), fbw("{uj0|uj1|uxa|uya}", "O6", "{I3|I2}", "w*h")]],
                [[env("R", "reset release instant at the C-elements' rst pins (MuxTiming R), min")]], launch="reset assertion (time 0)", note="H_RST_LONG, loop terms; wire terms likewise (each wire hi <= R)"),
           form([[env("R", "reset release at the rst pins, max")]],
                [[env("first_edge", "first request / control / join / z_ack edge at each C-element input pin (Xp 0, D0 0, Yp 0, D1 0, A0 0, ZA0 0, A1 0, ZA1 0), min")]], launch="reset assertion (time 0)", note="H_RST_EARLY")],
    lean=[L("Cells/OpsTimedMux", "mux_timing_of_static", "sufficient", note="hypotheses hRL (H_RST_LONG) and hRE (H_RST_EARLY)"), L("Cells/OpsTimedMux", "MuxTiming", "definition", note="fields H_RST_LONG, H_RST_EARLY"),
          L("Cells/OpsTimedMux", "mux_ok", "sufficient")],
    exactness="sufficient", exactness_note="P5: the only MuxTiming fields not derived from MuxStatic; true once at startup (reset polarity). Necessity not shown.",
    site_pins={"needed": False, "roles": ["rst pins (I4 of uj*, I3 of uxa/uya) not modelled per pin"]},
    rule={"rule": "none", "verdict": "none", "detail": "UNCHECKED; harness resets are microsecond-scale"}, corner=CORNER_1C, check_scope="environment")
add(id="bd_mux.bundled_z_s", cell="bd_mux", catalogue_row="X5 (refined, B-ops-timed2)",
    obligation="S_Z_S0 / S_Z_S1: the select s, launched at the control sender's driver, settles at udat's output before z_req (launched by the same sender's ctl_req) reaches the server",
    inequality="shi + Mz <= Ls + Wc0.lo + Lj0.lo + wo + Lor.lo + Dz.lo (y selected: Wc1, Lj1); shi = s wire + site pin + udat select arc",
    forms=[form([[wire("s.drv", "udat.I0", "shi"), sp("udat", "I0", "select"), lut("udat", "I0", "O5|O6", "shi"), env("Mz", "consumer's margin before z_req reaches the server (0 if data is needed only at z_req's arrival)", "Mz")]],
                [[env("Ls", "control sender: s settled at its driver -> ctl_req rise at its port (MuxDataEnv.H_S_LEAD), min", "Ls"),
                  wire("ctl_req", f"{u}.I1", f"{Wc}.lo"), sp(u, "I1", "ctl_req"), lut(u, "I1", "O6", f"{Lj}.lo")] + Kz(j, p)[:4]],
                launch="s settled at the control sender's driver", note=nm)
           for u, j, p, Wc, Lj, nm in [("uj0", "j0", "I0", "Wc0", "Lj0", "S_Z_S0"), ("uj1", "j1", "I1", "Wc1", "Lj1", "S_Z_S1")]],
    lean=[L("Cells/OpsTimed2", "mux_data_ok", "sufficient", note="z = the selected input's bit from Z(2k) - Mz to zeta(2k) + holdM, every token; real datamux INIT via DmRel"),
          L("Cells/OpsTimed2", "mux_value_ok_static", "sufficient", note="mux_ok_static + mux_data_ok from causal partners and static obligations"),
          L("Cells/OpsTimed2", "MuxDataStatic", "definition"), L("Cells/OpsTimed2", "MuxDataEnv", "definition"),
          L("Cells/OpsTimed2", "value_witness", "non_vacuity", note="MuxWit.value_witness: real E4 INIT, inputs always disagree")]
         + OC("cex_S_Z_S", "counter_trace", "MuxCex: shi one tick past the boundary, stale select") + OC("bnd_S_Z", "instance", "MuxCex: boundary holds")
         + OX("cex_S_Z_S1", "counter_trace", "MuxA (Wc0 = 2): shi = 10 fails S_Z_S1 by one tick while S_Z_S0, S_Z_X, S_Z_Y hold; y's token reads x's bit; also proves no MuxDataStatic instance") + OX("bnd", "instance", "MuxA.bnd: shi = 9, mux_value_ok_static applies"),
    exactness="sufficient+necessary_at_boundary", exactness_note="P5: refines bd_mux.bundled_z (whose launch 'join edge' presumes s settled there). Lt3 (B-ops-counter.md, OpsCounter.lean MuxCex.bnd_S_Z / cex_S_Z_S): tight by one tick in MuxWit.run (shi = Ls + 5 holds, shi = Ls + 6 delivers the wrong bit for a y and an x token); In that run S_Z_S0 and S_Z_S1 fail together. P6 / Lt4 (OpsExact.lean MuxA.cex_S_Z_S1): S_Z_S1 is necessary ON ITS OWN (asymmetric run Wc0 = 2, one tick past with S_Z_S0 holding); S_Z_S0 alone holds by the cell's x/y mirror, which is not built. Keep both forms. Not a general iff. Hold half: no inequality under the bundled protocol (senders hold until they see their ack rise; margin holdM = sum of MIN delays). Negative control: Wx.lo -> Wx.hi in S_Z_X breaks the proof; no counter-trace. " + OPS_X,
    site_pins={"needed": True, "roles": ["udat.I0 (s) hi", "uj*.I1 (ctl_req) lo", "uor.I0/I1 lo"]},
    rule={"rule": "A", "verdict": "different_condition", "detail": "rule A audits the request after the data cone at the consumer; this launch is the sender's s driver"},
    corner=CORNER_OPS, check_scope="route_plus_env")
add(id="bd_mux.bundled_z_data", cell="bd_mux", catalogue_row="X5 (new, B-ops-timed2)",
    obligation="S_Z_X / S_Z_Y: the selected client's data, launched at its driver, settles at udat's output before its request reaches the server through the join",
    inequality="ahi + Mz <= Lx + Wx.lo + Lj0.lo + wo + Lor.lo + Dz.lo (y: bhi, Ly, Wy, Lj1)",
    forms=[form([[wire(f"{c}_data.drv", f"udat.{dp}", hi), sp("udat", dp, f"{c}_data"), lut("udat", dp, "O5|O6", hi), env("Mz", "consumer margin", "Mz")]],
                [[env(Ld, f"client {c}: data settled at its driver -> {c}_req rise (H_{c.upper()}_LEAD), min", Ld),
                  wire(f"{c}_req", f"{u}.I0", f"{Wq}.lo"), sp(u, "I0", f"{c}_req"), lut(u, "I0", "O6", f"{Lj}.lo")] + Kz(j, p)[:4]],
                launch=f"{c}_data settled at client {c}'s driver", note=nm)
           for c, dp, hi, Ld, u, Wq, Lj, j, p, nm in [("x", "{I1|I3}", "ahi", "Lx", "uj0", "Wx", "Lj0", "j0", "I0", "S_Z_X"),
                                                     ("y", "{I2|I4}", "bhi", "Ly", "uj1", "Wy", "Lj1", "j1", "I1", "S_Z_Y")]],
    lean=[L("Cells/OpsTimed2", "mux_data_ok", "sufficient"), L("Cells/OpsTimed2", "mux_value_ok_static", "sufficient"),
          L("Cells/OpsTimed2", "MuxDataStatic", "definition"), L("Cells/OpsTimed2", "value_witness", "non_vacuity", note="MuxWit.value_witness")]
         + OC("surv_S_Z_X", "not_necessary", "MuxCex: 4 ticks past the bound the value is still right (ctl_req is the join's late input)") + OC("cex_S_Z_X", "counter_trace", "5 ticks past") + OC("cex_S_Z_Y", "counter_trace")
         + OX("cex_S_Z_X", "counter_trace", "MuxA (x is the join's late input): ahi = 6 fails S_Z_X by one tick while S_Z_S0, S_Z_S1, S_Z_Y hold; x's token sees x's previous bit; also proves no MuxDataStatic instance") + OX("bnd", "instance", "MuxA.bnd: ahi = 5"),
    exactness="sufficient+necessary_at_boundary", exactness_note="P5: MuxDataStatic.S_Z_X / S_Z_Y; bundled_z covered only the select cone. Lt3 (OpsCounter.lean MuxCex.surv_S_Z_X, cex_S_Z_X, cex_S_Z_Y): when ctl_req is the join's late input the form has slack (MuxWit.run: the value survives 4 ticks past the bound, fails at 5); exact condition ahi + Mz <= Lx + (Z(2k) - xi(2m)) along the actually-late input. P6 / Lt4 (OpsExact.lean MuxA.cex_S_Z_X): when x IS the join's late input the static form is tight by one tick, and a routed netlist can produce that case, so the form is safe everywhere and exact when the client is late (not merely conservative). Tight on one run, not a general iff. S_Z_Y: by symmetry (late-y run not built; Lt3 cex_S_Z_Y is the ctl-late run). " + OPS_X,
    site_pins={"needed": True, "roles": ["udat data pins hi", "uj*.I0 (req) lo", "uor.I0/I1 lo"]},
    rule={"rule": "A", "verdict": "different_condition", "detail": "rule A's sender-request-last form is the classic version of this (sufficient for it only with the lead term)"},
    corner=CORNER_OPS, check_scope="route_plus_env")

# =============================================================== bd_steer (P4: B-gcd-cells.md gap 5, 38 instances in gcd_hw; P5: timed, B-ops-timed2.md section (d))
STEER_UNTIMED = [L("Cells/LibCtlMergeMux", "steer_req0", "function_equality", note="req0 = req . ~s (O5)"), L("Cells/LibCtlMergeMux", "steer_req1", "function_equality", note="req1 = req . s (O6)"),
                 L("Cells/LibCtlMergeMux", "steer_excl_K", "context", note="Kleene exclusion of the two branches (a universal fact, not an iff)"),
                 L("Cells/LibCtlMergeMux", "steer_s_x_while_req", "necessary", note="Kleene: s mid-edge while req is high gives x on both outputs"),
                 L("Cells/LibCtlMergeMux", "steer_req_s_together", "necessary", note="req and s moving together gives x"),
                 L("Net/OpsSteer", "steer_op", "sufficient", note="shard C, untimed operator refinement under Held")]
add(id="bd_steer.bundled_s_setup", cell="bd_steer", also_applies_to=["bd_bd2dr (same LUT6_2 INIT)"], catalogue_row="X3 (steer)",
    obligation="S_S_SETUP (H_BUNDLED_S_PIN, setup half): s, launched at its driver, reaches u.I1 before req's rise reaches u.I0",
    inequality="Ws.hi <= Ls + Wq.lo (Lean, lumped LUT arc); per-pin margin: + arc(u.I1 -> O5|O6).hi on the left, + arc(u.I0 -> O5|O6).lo on the right",
    forms=[form([[wire("s.drv", "u.I1", "Ws.hi"), sp("u", "I1", "select"), lut("u", "I1", "O5|O6", note="not in the Lean model (lumped L5/L6); per-pin margin")]],
                [[env("Ls", "sender: s settled at its driver -> req rise at the sender's port (SteerCausal.H_S_LEAD), min", "Ls"),
                  wire("req", "u.I0", "Wq.lo"), sp("u", "I0", "req"), lut("u", "I0", "O5|O6", note="not in the Lean model; per-pin margin")]],
                launch="s settled at its driver (the join(cond, data) node edge behind bdc's cond_br)")],
    lean=STEER_T + [L("Cells/OpsTimed", "steer_s_pin_of_wire", "sufficient", note="static form: sS + Ws.hi <= rho(2k) + Wq.lo, rho(2k+1) + Wq.hi <= sE + Ws.lo => H_S_PIN"),
                    L("Cells/OpsTimed", "steer_fwd", "sufficient", note="needs only the gates, a clean request and H_S_PIN")] + STEER_UNTIMED,
    status="proved", exactness="sufficient",
    exactness_note="P5 (B-ops-timed2.md (d)): proved sufficient with LUMPED LUT arcs (one FIFO arc per output after both pins); the u.I1-vs-u.I0 per-pin arc difference is not in the model and is charged here as margin. Kleene necessity at the select (steer_s_x_while_req) is not a timed counter-trace. " + OPS_X,
    site_pins={"needed": True, "roles": ["u.I1 (s) hi", "u.I0 (req) lo"]},
    rule={"rule": "E (skew.py)", "verdict": "exact_structure_missing_site_pins", "detail": "rule E checks the setup half without site pins (B-gcd-cells.md)"},
    corner=CORNER_OPS, check_scope="route_plus_env",
    evidence="38 instances in gcd_hw (every cond_br, behind bd_join(cond, data)), B-gcd-cells.md; no route measured")
add(id="bd_steer.bundled_s_hold", cell="bd_steer", also_applies_to=["bd_bd2dr"], catalogue_row="X3 (steer)",
    obligation="S_S_HOLD (H_BUNDLED_S_PIN, hold half): req's fall reaches u.I0 before s's next change reaches u.I1",
    inequality="Wq.hi <= Hs + Ws.lo; with the library contract (s held until ack fall seen) Hs = Wq.lo + Lm + Er + Wm + La.lo + Wk.lo (steer_hold_of_ackfall)",
    forms=[form([[wire("req", "u.I0", "Wq.hi"), sp("u", "I0", "req"), lut("u", "I0", "O5|O6", note="per-pin margin, not in Lean")]],
                [[env("Hs", "sender: req fall -> next s change at its driver (SteerCausal.H_S_HOLD); with bd_ctl's contract a whole round trip req -> u -> receiver -> uack -> sender", "Hs"),
                  wire("s.drv", "u.I1", "Ws.lo"), sp("u", "I1", "select"), lut("u", "I1", "O5|O6", note="per-pin margin, not in Lean")]],
                launch="req fall at the sender's port")],
    lean=STEER_T + [L("Cells/OpsTimed", "steer_s_pin_of_wire", "sufficient"),
                    L("Cells/OpsTimed2", "steer_hold_of_ackfall", "lemma", note="library contract gives Hs = a whole round trip")] + STEER_UNTIMED,
    status="proved", exactness="sufficient",
    exactness_note="P5: proved sufficient, lumped LUT arcs (as setup). With the library contract the margin is a whole round trip, so this cannot bind in practice unless the req wire is pathological. " + OPS_X,
    site_pins={"needed": True, "roles": ["u.I0 (req) hi", "u.I1 (s) lo"]},
    rule={"rule": "none", "verdict": "none", "detail": "UNCHECKED"}, corner=CORNER_OPS, check_scope="route_plus_env")

# =============================================================== bd_merge
add(id="bd_merge.seq", cell="bd_merge", catalogue_row="M1",
    obligation="H_MERGE_SEQ: a client raises req only when the other's req and ack are low (timed: the two requests are one sequence of four-phase transactions on common edges; causal form MergeCausal.H_OWN)", inequality="protocol", forms=[],
    lean=[L("Cells/MergeMuxSI", "merge_ok", "sufficient"), L("Cells/MergeMuxSI", "merge_needs_seq", "necessary"), L("Cells/LibCtlMergeMux", "merge_early_y_spurious_ack", "counter_trace"),
          L("Cells/OpsTimedMux", "merge_ok", "sufficient", note="timed: MergeEnv H_X/H_Y (the shape) + MergeTiming"), L("Cells/OpsTimedMux", "MergeCausal", "definition", note="H_OWN: the next requester raises only Eo after the previous owner's ack fell")],
    exactness="sufficient+necessary", site_pins={"needed": False, "roles": []}, rule={"rule": "none", "verdict": "none", "detail": "bdc emits bdc_amerge = bd_arbiter instead"},
    corner=CORNER_NA, check_scope="protocol")
add(id="bd_merge.bundled_z", cell="bd_merge", catalogue_row="M2",
    obligation="S_ZM_SEL_X (H_BUNDLED_Z): z_req after usel and the datamux select have settled (matched DELAY covers the select cone), launch x_req rise",
    inequality="hr + sh + Mz <= Wxo.lo + Lor.lo + Dz.lo; hr = x_req -> usel.I0 window (wire + site pin + arc), sh = sel -> udat select window",
    forms=[form([[wire("x_req", "usel.I0", "hr"), sp("usel", "I0", "x_req"), lut("usel", "I0", "O6", "hr"), wire("usel.O6", "udat.I0", "sh"), sp("udat", "I0", "sel"), lut("udat", "I0", "O5|O6", "sh"),
                  env("Mz", "consumer margin", "Mz")]],
                [Kz("x_req", "I0")[:4]], launch="x_req rise at the client")],
    lean=[L("Cells/OpsTimed2", "merge_data_ok", "sufficient", note="z = the requester's bit from Z(2k) - Mz to zeta(2k) + Hm, every token; real usel 4'hE and datamux E4 INITs"),
          L("Cells/OpsTimed2", "MergeDataStatic", "definition"), L("Cells/OpsTimed2", "value_witness", "non_vacuity", note="MergeWit.value_witness")]
         + OC("cex_S_ZM_SEL_X", "counter_trace", "MergeCex") + OC("cex_S_ZM_SEL_X_static", "counter_trace", "no MergeDataStatic instance for the failing windows")
         + OX("merge_data_ok_exact", "sufficient", "same conclusion as merge_data_ok under MergeDataExact (S_ZM_SEL_X, S_ZM_X/Y, S_SEL_XA_N, H_SEL_START; no S_SEL_XR, no S_OR); in a y token the x_req branch is launched by the LAST x token (last_x), so S_ZM_SEL_X covers it") + OX("MergeDataExact", "definition") + [
          L("Cells/MergeMuxSI", "merge_ok", "sufficient", note="untimed hypothesis"),
          L("Cells/ConstraintsMux", "usel_high", "lemma", note="usel = x_req | x_ack (4'hE)"), L("Cells/ConstraintsMux", "usel_low", "lemma"),
          L("Cells/ConstraintsMux", "usel_kleene", "function_equality"), L("Cells/ConstraintsMux", "dm_settles", "sufficient"),
          L("Cells/ConstraintsMux", "bundled_z_capture", "sufficient", note="H_BUNDLED_Z_T Tz + zhi <= Ton + ehi, H_PW, H_HOLD"),
          L("Cells/Bundling", "setup_not_classic", "context")],
    exactness="sufficient+necessary_at_boundary", exactness_note="Lt3 (OpsCounter.lean MergeCex.bnd_S_ZM_SEL_X, cex_S_ZM_SEL_X, cex_S_ZM_SEL_X_static): tight by one tick in MergeWit.run (usel x_req pin one tick late: select still low at Z 0, z = y's bit), and no MergeDataStatic instance exists for the failing windows. Not a general iff. P5: now the field S_ZM_SEL_X of a whole-cell timed theorem (merge_data_ok, early data protocol); same arcs as before. The y-token side needs sel LOW: its x_req branch is covered by THIS form (P6 / Lt4 merge_data_ok_exact: S_SEL_XR proved redundant, so bd_merge.sel_low_xreq is no longer an entry), its x_ack branch is S_SEL_XA_N in bd_merge.isochronic_forks. Negative control: Wzx.hi -> Wzx.lo in S_SEL_XA_Z breaks the proof; no counter-trace. " + OPS_X,
    site_pins={"needed": True, "roles": ["usel.I0, udat.I0 hi", "uor.I0 lo"]}, rule={"rule": "A", "verdict": "rule_is_the_check"}, corner=CORNER_OPS)
add(id="bd_merge.bundled_z_data", cell="bd_merge", catalogue_row="M2 (new, B-ops-timed2)",
    obligation="S_ZM_X / S_ZM_Y: the requesting client's data, launched at its driver, settles at udat's output before its request reaches the server",
    inequality="xh + Mz <= Lx + Wxo.lo + Lor.lo + Dz.lo (y: yh, Ly, Wyo)",
    forms=[form([[wire(f"{c}_data.drv", f"udat.{dp}", hi), sp("udat", dp, f"{c}_data"), lut("udat", dp, "O5|O6", hi), env("Mz", "consumer margin", "Mz")]],
                [[env(Ld, f"client {c}: data settled -> {c}_req rise (MergeDataEnv.H_{c.upper()}_LEAD), min", Ld)] + Kz(f"{c}_req", p)[:4]],
                launch=f"{c}_data settled at client {c}'s driver", note=nm)
           for c, dp, hi, Ld, p, nm in [("x", "{I2|I4}", "xh", "Lx", "I0", "S_ZM_X"), ("y", "{I1|I3}", "yh", "Ly", "I1", "S_ZM_Y")]],
    lean=[L("Cells/OpsTimed2", "merge_data_ok", "sufficient"), L("Cells/OpsTimed2", "MergeDataStatic", "definition"), L("Cells/OpsTimed2", "value_witness", "non_vacuity", note="MergeWit.value_witness")]
         + OC("cex_S_ZM_X", "counter_trace", "MergeCex") + OC("cex_S_ZM_Y", "counter_trace", "MergeCex") + OC("bnd_S_ZM_XY", "instance")
         + OX("merge_data_ok_exact", "sufficient", "S_ZM_X / S_ZM_Y are fields of MergeDataExact unchanged"),
    exactness="sufficient+necessary_at_boundary", exactness_note="Lt3 (OpsCounter.lean MergeCex.bnd_S_ZM_XY, cex_S_ZM_X, cex_S_ZM_Y and their _static forms): each tight by one tick in MergeWit.run (data pin one tick late: the server sees the client's previous bit). Not a general iff. P5: MergeDataStatic.S_ZM_X / S_ZM_Y (bd_merge's udat is .a(y_data), .b(x_data), .s(sel)). " + OPS_X,
    site_pins={"needed": True, "roles": ["udat data pins hi", "uor.I0/I1 lo"]},
    rule={"rule": "A", "verdict": "different_condition", "detail": "classic sender-request-last version"}, corner=CORNER_OPS, check_scope="route_plus_env")
# bd_merge.sel_low_xreq (S_SEL_XR) removed in P6: Lt4's merge_data_ok_exact does not assume it
# (redundant, proved); recorded in hypotheses_not_inequalities NOT_OBLIGATIONS.
add(id="bd_merge.isochronic_forks", cell="bd_merge", catalogue_row="M3",
    obligation="z_ack -> {uxa, uya} fork (S_XA_FORK / S_YA_FORK, H_MERGE_SEQ's 'fully completed') and the x_ack -> {usel, client} fork (S_SEL_XA_N: the fall of uxa's node crosses usel and the select before the next owner's request, launched by the same node fall through the x client, reaches the server)",
    inequality="Wzx.hi + Lxa.hi + wxah <= Ka + Wxc.lo; Wzy.hi + Lya.hi + wyah <= Ka + Wyc.lo; hq + sh + Mz <= Wxa.lo + Eo + Wyo.lo + Lor.lo + Dz.lo (S_SEL_XA_N, node-launched; replaces S_SEL_XA_Z and S_SEL_XA_R)",
    forms=[form([cel("uxa", "I1", "z_ack.drv", "Wzx.hi", "Lxa.hi", "z_ack", "wxah")], [Ka() + [wire("x_req", "uxa.I0", "Wxc.lo"), sp("uxa", "I0", "x_req")]],
                launch="z_ack edge at its driver", note="S_XA_FORK"),
           form([cel("uya", "I1", "z_ack.drv", "Wzy.hi", "Lya.hi", "z_ack", "wyah")], [Ka() + [wire("y_req", "uya.I0", "Wyc.lo"), sp("uya", "I0", "y_req")]],
                launch="z_ack edge at its driver", note="S_YA_FORK"),
           form([[wire("uxa.O6", "usel.I1", "hq"), sp("usel", "I1", "x_ack"), lut("usel", "I1", "O6", "hq"),
                  wire("usel.O6", "udat.I0", "sh"), sp("udat", "I0", "sel"), lut("udat", "I0", "O5|O6", "sh"), env("Mz", "consumer margin", "Mz")]],
                [[wire("uxa.O6", "x client", "Wxa.lo"), env("Eo", "owner x: x_ack fall seen -> next requester (y) raises (MergeCausal.H_OWN), min", "Eo")] + Kz("y_req", "I1")[:4]],
                launch="fall of uxa's node in the LAST x token before the y token (x_ack at uxa.O6; the later of the x_req fall and the z_ack fall at uxa)",
                note="S_SEL_XA_N (MergeDataExact.S_SEL_XA_N): the single exact x_ack-branch gate; the lumped forms S_SEL_XA_Z / S_SEL_XA_R are superseded (MergeDataStatic.exact: S_SEL_XA_Z implies S_SEL_XA_N) and are not checked")],
    lean=MERGE_T + OX("merge_data_ok_exact", "sufficient", "x_ack branch: S_SEL_XA_N alone (no S_SEL_XA_Z, S_SEL_XA_R, S_SEL_XR)") + OX("MergeDataExact", "definition")
                 + OX("MergeDataStatic.exact", "lemma", "the old static set implies the new one; merge_data_ok' (OpsExact) re-derives merge_data_ok as a corollary (not cited as a reference: the validator's name regex cannot match a primed name)")
                 + OX("bnd_S_SEL_XA_N", "instance", "MergeCex: hq = 4, theorem applies") + OX("cex_S_SEL_XA_N", "counter_trace", "MergeCex: hq = 5 fails only S_SEL_XA_N; y's token 1 delivers x's bit; also proves no MergeDataExact instance")
                 + [L("Cells/OpsTimed2", "merge_data_ok", "sufficient", note="earlier, lumped x_ack branch: S_SEL_XA_Z, S_SEL_XA_R"), L("Cells/OpsTimed2", "MergeDataStatic", "definition"),
                    *OC("cex_S_SEL_XA_Z", "counter_trace", "MergeCex: x_ack branch"), *OC("cex_S_SEL_XA_Z_static", "counter_trace"),
                    L("Cells/MergeMuxSI", "merge_ok", "sufficient", note="untimed, isochronic forks assumed"), L("Cells/MergeMuxSI", "merge_needs_iso_za", "necessary", note="untimed"),
                    L("Cells/MergeMuxSI", "merge_broad_needs_iso_xa", "necessary", note="untimed, broad data protocol")],
    status="proved", exactness="sufficient+necessary_at_boundary",
    exactness_note="P6 / " + LT4 + ": the x_ack branch gates on S_SEL_XA_N ALONE (merge_data_ok_exact, MergeDataExact); it is tight by one tick in MergeWit.run (bnd_S_SEL_XA_N at hq = 4, cex_S_SEL_XA_N at hq = 5 with every other MergeDataExact field holding). The launch is the uxa node fall of the last x token (last_x): every slot in between is a y slot. S_SEL_XA_Z and S_SEL_XA_R are dropped as separate checks (S_SEL_XA_Z implies S_SEL_XA_N; S_SEL_XA_R is no longer needed). Lt3 (OpsCounter cex_S_SEL_XA_Z) is the same boundary in the old form. Necessity is at that boundary in one run (not an iff); the z_ack branch (S_XA_FORK/S_YA_FORK) is only sufficient (not probed). EARLY data protocol only: the broad protocol (merge_broad_needs_iso_xa) is NOT covered. " + OPS_X,
    site_pins={"needed": True, "roles": ["uxa/uya.I1 hi", "uxa/uya.I2 hi", "usel.I1, udat.I0 hi", "uxa/uya.I0 lo", "x client pin of x_ack lo", "uor.I1 lo"]},
    rule={"rule": "none", "verdict": "none"}, corner=CORNER_OPS, check_scope="route_plus_env")
add(id="bd_merge.uxa_feedback", cell="bd_merge", catalogue_row="M4",
    obligation="S_XA_ZA / S_YA_ZA: z_ack's pulse at uxa/uya outlasts the C-element's loop (generic env latency; no mux-like race)",
    inequality="Wzx.hi + Lxa.hi + wxah <= Wzx.lo + Ka + Kz (uya: Wzy, Lya, wyah); dlmax + dwmax <= dlmin + E (bd_c2.env_latency)",
    forms=[form([cel(a, "I1", "z_ack.drv", f"{Wz}.hi", f"{La}.hi", "z_ack", wh)], [Ka() + Kz() + [wire("z_ack.drv", f"{a}.I1", f"{Wz}.lo"), sp(a, "I1", "z_ack")]],
                launch="z_ack edge at its driver", note=nm + f" (redundant when {Wz}.hi - {Wz}.lo <= {Wc}.hi - {Wc}.lo)")
           for a, Wz, La, wh, nm, Wc in [("uxa", "Wzx", "Lxa", "wxah", "S_XA_ZA", "Wxc"), ("uya", "Wzy", "Lya", "wyah", "S_YA_ZA", "Wyc")]],
    refers_to=["bd_c2.env_latency"],
    lean=[L("Cells/MuxRtzTimed", "merge_rtz_of_latency", "sufficient")] + MERGE_T
         + OX("merge_za_of_R", "redundancy", "S_XA_ZA follows from S_XA_R (1) (bd_merge.uxa_req_latency) whenever Wzx.hi - Wzx.lo <= Wxc.hi - Wxc.lo"), exactness="sufficient",
    exactness_note="P5: forms are MergeStatic.S_XA_ZA / S_YA_ZA inside the whole-cell theorem. P6 / " + LT4 + " merge_za_of_R: REDUNDANT, and the checker may skip it, when the z_ack wire's spread is at most the request wire's, (Wzx.hi - Wzx.lo) <= (Wxc.hi - Wxc.lo) at uxa (uya: Wzy vs Wyc, by symmetry; the y lemma is not written), given bd_merge.uxa_req_latency S_XA_R (1). Otherwise keep it. Probably NOT exact: the next edge of either uxa input is causally after node + Wxa + Eo, so a node-launched form like S_SEL_XA_N should replace it (Lxa.hi + wxah <= Lxa.lo + Wxa.lo + Eo + min(Wxc.lo, Kz + Wzx.lo), proposed, not proved). " + OPS_X,
    site_pins={"needed": True, "roles": ["uxa.I2 hi", "uxa/uya.I1 hi and lo"]}, rule={"rule": "none", "verdict": "none"}, corner=CORNER_OPS, check_scope="route_plus_env")
add(id="bd_merge.uxa_req_latency", cell="bd_merge", catalogue_row="M (new, B-ops-timed)", also_applies_to=["bd_c2.env_latency at uxa/uya (request input)"],
    obligation="S_XA_R / S_YA_R: a request edge at the ack C-element outlasts its loop until the next request edge and the next z_ack edge",
    inequality="Wxc.hi + Lxa.hi + wxah <= Kz + Ka + Wxc.lo and <= 2 Kz + Ka + Wzx.lo (uya: Wyc, Lya, wyah, Wzy)",
    forms=[f for a, c, W, La, wh, Wz in [("uxa", "x_req", "Wxc", "Lxa", "wxah", "Wzx"), ("uya", "y_req", "Wyc", "Lya", "wyah", "Wzy")]
           for f in (form([cel(a, "I0", c, f"{W}.hi", f"{La}.hi", c, wh)], [Kz("{x_req|y_req}") + Ka() + [wire(c, f"{a}.I0", f"{W}.lo"), sp(a, "I0", c)]],
                          launch="request edge at the client", note=f"S_{a[1:].upper()}_R (1)"),
                     form([cel(a, "I0", c, f"{W}.hi", f"{La}.hi", c, wh)], [Kz("{x_req|y_req}") + Ka() + Kz("{x_req|y_req}") + [wire("z_ack.drv", f"{a}.I1", f"{Wz}.lo"), sp(a, "I1", "z_ack")]],
                          launch="request edge at the client", note=f"S_{a[1:].upper()}_R (2)"))],
    lean=MERGE_T, exactness="sufficient", exactness_note="P5: arc-level instance of bd_c2.env_latency at uxa/uya's request input. " + OPS_X,
    site_pins={"needed": True, "roles": ["uxa/uya.I0 hi and lo", "uxa/uya.I2 hi", "uxa/uya.I1 lo"]},
    rule={"rule": "none", "verdict": "none", "detail": "UNCHECKED"}, corner=CORNER_OPS, check_scope="route_plus_env")
add(id="bd_merge.reset_first", cell="bd_merge", catalogue_row="M (new, B-ops-timed2)",
    obligation="H_RST_LONG + H_RST_EARLY (uxa, uya): reset outlasts wires and loops and is released before the first edge at each C-element (H_SEL_START moved to bd_merge.sel_start in P6)",
    inequality="Wxc.hi, Wyc.hi, Wzx.hi, Wzy.hi, Lxa.hi + wxah, Lya.hi + wyah <= R; R <= AX 0, ZA0 0, AY 0, ZA1 0",
    forms=[form([[lut("{uxa|uya}", "{I0|I1}", "O6", "L*a.hi"), fbw("{uxa|uya}", "O6", "I2", "w*ah")]], [[env("R", "reset release at the rst pins, min")]], launch="reset assertion (time 0)", note="H_RST_LONG (loop terms; each wire hi <= R likewise)"),
           form([[env("R", "reset release at the rst pins, max")]], [[env("first_edge", "first request / z_ack edge at uxa/uya input pins (AX 0, ZA0 0, AY 0, ZA1 0), min")]], launch="reset assertion (time 0)", note="H_RST_EARLY")],
    refers_to=["design.rst_hold", "design.rst_release_skew"],
    lean=[L("Cells/OpsTimedMux", "merge_timing_of_static", "sufficient", note="hypotheses hRL, hRE"), L("Cells/OpsTimedMux", "MergeTiming", "definition")],
    exactness="sufficient", exactness_note="P5: start-up only (reset polarity). Necessity not shown. P6: at design level these are design.rst_hold (per rst pin) and, for H_RST_EARLY, design.rst_release_skew / gcd_rig.token_static (B-reset-contract.md).",
    site_pins={"needed": False, "roles": ["rst pins not modelled per pin"]},
    rule={"rule": "none", "verdict": "none", "detail": "UNCHECKED; harness resets are microsecond-scale"}, corner=CORNER_1C, check_scope="environment")
add(id="bd_merge.sel_start", cell="bd_merge", catalogue_row="M (new, B-ops-timed2; split from reset_first in P6)",
    obligation="H_SEL_START: the first token's window starts after uxa's output (defined after its first evaluation) and usel are clean at the datamux select; a start-up condition about uxa's power-up level",
    inequality="max(hr, Lxa.hi + hq) + sh + Mz <= rho 0 + (Wyo.lo + Lor.lo + Dz.lo)",
    forms=[form([[lut("uxa", "{I0|I1}", "O6", "Lxa.hi"), wire("uxa.O6", "usel.I1", "hq"), sp("usel", "I1", "x_ack"), lut("usel", "I1", "O6", "hq"),
                  wire("usel.O6", "udat.I0", "sh"), sp("udat", "I0", "sel"), lut("udat", "I0", "O5|O6", "sh"), env("Mz", "consumer margin", "Mz")]],
                [[env("rho0", "first request edge at the client after reset (rho 0)", "rho 0")] + Kz("y_req", "I1")[:4]], launch="reset assertion (time 0)", note="H_SEL_START, uxa leg (shown exact)"),
           form([[wire("x_req", "usel.I0", "hr"), sp("usel", "I0", "x_req"), lut("usel", "I0", "O6", "hr"),
                  wire("usel.O6", "udat.I0", "sh"), sp("udat", "I0", "sel"), lut("udat", "I0", "O5|O6", "sh"), env("Mz", "consumer margin", "Mz")]],
                [[env("rho0", "first request edge at the client after reset (rho 0)", "rho 0")] + Kz("y_req", "I1")[:4]], launch="reset assertion (time 0)", note="H_SEL_START, x_req leg hr (not shown necessary: a transport run on N cannot exercise it)")],
    lean=[L("Cells/OpsTimed2", "merge_data_ok", "sufficient", note="MergeDataStatic.H_SEL_START"), L("Cells/OpsTimed2", "MergeDataStatic", "definition")]
         + OX("merge_data_ok_exact", "sufficient", "MergeDataExact.H_SEL_START, unchanged") + OX("bnd_H_SEL_START", "instance", "MergeY (y owns token 0): hq = 2, the theorem applies for either power-up level p")
         + OX("cex_H_SEL_START", "counter_trace", "MergeY: hq = 3, every other MergeDataExact field (incl. S_SEL_XA_N) holds; with uxa powering up high, usel reads it when y's token 0 reaches the server: z(4) = x's bit")
         + OX("surv_H_SEL_START_low", "not_necessary", "the same violation with uxa powering up low is harmless") + OX("witness", "non_vacuity", "MergeY.witness p: whole control side via merge_ok_noskew, both power-up levels"),
    exactness="sufficient+necessary_at_boundary",
    exactness_note="P6 / " + LT4 + " section 3 (MergeY): the Lxa.hi + hq leg is tight by one tick in a y-first run, but only against a uxa output that powers up HIGH (surv_H_SEL_START_low: harmless if it powers up low). Not a general iff. The hr leg is not shown necessary. A reset-polarity fact in the CLAUDE.md sense (true once at startup): uxa defined and seen by usel before the first request arrives. bdc emits bdc_amerge (bd_arbiter), not bd_merge, so gcd_hw has no instance. " + OPS_X,
    site_pins={"needed": True, "roles": ["usel.I0, usel.I1, udat.I0 hi", "uor.I1 lo"]},
    rule={"rule": "none", "verdict": "none", "detail": "UNCHECKED"}, corner=CORNER_OPS, check_scope="environment")

# =============================================================== bdc_amerge (generated control_merge; probes Cm, Cm2: B-amerge.md, B-amerge-timed.md)
# 7 x bdc_amerge2_0 + 1 x bdc_amerge3_0 in gcd_hw. The arbiters inside are bd_arbiter
# instances: their own entries (bd_arbiter.rt1*, rt2*, a0_fork*) apply per instance
# (9: 7 amerge2 uarb1, amerge3 uarb1 and uarb2); for amerge3's uarb1 the server is
# uarb2 + everything behind it (bdc_amerge3.rt2_cascade_*).
CORNER_ARBPIN = dict(CORNER_1C, mode="1C",
                     note="O5 arcs per ROUTED physical pin (ArbCornersPin.pinCol, B-arb-corners-pin.md): SLICEM A1-A4 -> O5 43-46 / 146-150 ps (FAST_MIN / SLOW_MAX), A5 -> O5 48 / 116; O6 45 / 124 flat over pins. Read Rrq (ustate.I2 -> O5) and every ugrant O5 arc from the pin the router chose; with DELAY = 0 the sign of race 1 flips with q's pin (pinA5_delay0: q on A5 fails at SLOW_MAX by 8 ps, passes at FAST_MIN; identity pins fail at FAST_MIN by 3 ps)")
ARBPIN = [L("Cells/ArbCornersPin", "pinCol", "corner", note="per-pin O5 column"), L("Cells/ArbCornersPin", "A5_vs_O6", "corner", note="A5 is the only pin with SLOW_MAX below O6 and FAST_MIN above it")]
AM_X = "Cm2 model (B-amerge-timed.md): Int ps, 7h's arbiter Run/Scn (real INITs, per-pin O5 arcs, flat O6, every route incl. site pin), the inferred index LUT (H_YOSYS_MAP) as 7h's rise-fast OR channel, consumer = transport wid + setup su, request path dz = R0 -> uor -> bd_delay_gated rise -> z_req -> consumer (min). Arc-only margins (routes 0) are in the note; no routed number."
UREQ = lambda pre="uarb.": [fbw(f"{pre}ustate", "O6", "I2", "wfb"), sp(f"{pre}ustate", "I2", "q fb"), lut(f"{pre}ustate", "I2", "O5", "Rrq", note="per physical pin (pinCol)")]
DZ = lambda src="R0": [wire(src, "uor.I0", "dz"), sp("uor", "I0", "R0"), lut("uor", "I0", "O6", "dz"),
                       line("udly", "rise", "chain", "bd_delay_gated rise (DELAY hops; 12 for amerge2, 24 for amerge3 in gcd_hw)", "dz"),
                       wire("z_req", "consumer capture", "dz")]
IDXOUT = lambda pin, sym: [sp("index_lut", pin, "index input"), lut("index_lut", pin, "O6", sym), env("wid", "index -> consumer capture point (transport, max)", "wid"), env("su", "consumer setup", "su")]
AM_SI = [L("Cells/AMerge2Proof", "amerge2_ok", "sufficient", note="untimed SI filter form (183 states, real and inferred INITs)")]

add(id="bdc_amerge.bundled_idx_grant", cell="bdc_amerge", also_applies_to=["bdc_amerge2_0 (7 instances in gcd_hw)"], catalogue_row="Cm H_BUNDLED_IDX race 1",
    obligation="H_BUNDLED_IDX, new owner (client 2 / in1): after q's fall the new grant g2 reaches the index LUT and the index reaches the consumer before the new token's z_req does",
    inequality="wq + g2r + wgi + xr + wid + su <= wfb + Rrq + dz (BidxA; the common part A0 fall -> q cancels)",
    forms=[form([[wire("uarb.ustate.O6", "uarb.ugrant.I2", "wq"), sp("uarb.ugrant", "I2", "q"), lut("uarb.ugrant", "I2", "O6", "g2r"),
                  wire("uarb.ugrant.O6", "index_lut.I0", "wgi")] + IDXOUT("I0", "xr")],
                [UREQ() + DZ()], launch="q fall at uarb.ustate.O6")],
    lean=[L("Cells/AMergeTimed", "bidx_new_owner", "sufficient"), L("Cells/AMergeTimed", "BidxA", "definition"),
          L("Cells/AMergeTimed", "bidx_new_owner_counter", "counter_trace", note="minimal capture Zr = RR + dz: the consumer sees the PREVIOUS owner's index (needs A0Fork, H_Z_IN_SRV dz <= smin)"),
          L("Cells/AMergeTimedW", "nonvacuous_slow", "non_vacuity"), L("Cells/AMergeTimedW", "nonvacuous_fast", "non_vacuity"),
          L("Cells/AMergeTimedW", "counter_fast_delay0", "instance", note="DELAY = 0 at FAST_MIN fails by 3 ps, counter-trace fires"),
          L("Cells/AMergeTimedW", "slow_delay0_passes", "instance"), L("Cells/AMergeTimedW", "pinA5_delay0", "corner", note="q on A5: fails at SLOW_MAX by 8 ps, passes at FAST_MIN by 3 ps")]
         + AM_SI + [L("Cells/AMerge2Proof", "amerge2_needs_bundled_idx", "necessary", note="untimed")] + ARBPIN,
    exactness="sufficient+necessary", exactness_note="Cm2: sufficient for every run of the real arbiter, every server and every capture allowed by H_REQ_PATH; necessary at the minimal request path (bidx_new_owner_counter, with A0Fork and H_Z_IN_SRV). " + AM_X + " Arc-only margin, DELAY = 12: 1514 (SLOW_MAX) / 537 (FAST_MIN) ps.",
    site_pins={"needed": True, "roles": ["ugrant.I2 (q), index_lut.I0 (g2) hi", "ustate.I2 (q feedback), uor.I0 lo"]},
    rule={"rule": "A", "source": "cells/verify/tighten.py (audits <cell>.uor)", "verdict": "different_condition",
          "detail": "rule A audits uor against the whole input cone, not the index LUT's grant pin against R0's O5 path; no per-pin O5 arc, no site pins"},
    corner=CORNER_ARBPIN, check_scope="route_plus_env")
add(id="bdc_amerge.bundled_idx_ack", cell="bdc_amerge", also_applies_to=["bdc_amerge2_0 (7)"], catalogue_row="Cm H_BUNDLED_IDX race 2 (ack leg)",
    obligation="H_BUNDLED_IDX, previous owner (client 2) leaves: A0's fall drops A2 = in1_ack at the index LUT before A0 -> q -> R0 -> z_req reaches the consumer",
    inequality="wa02 + c2f + wai + xf + wid + su <= wa0s + qr + wfb + Rrq + dz (BidxB.ack)",
    forms=[form([[wire("A0", "uarb.ua2.I1", "wa02"), sp("uarb.ua2", "I1", "A0"), lut("uarb.ua2", "I1", "O6", "c2f"), wire("uarb.ua2.O6", "index_lut.I1", "wai")] + IDXOUT("I1", "xf")],
                [[wire("A0", "uarb.ustate.I4", "wa0s"), sp("uarb.ustate", "I4", "A0"), lut("uarb.ustate", "I4", "O6", "qr")] + UREQ() + DZ()],
                launch="A0 (= z_ack) fall at its driver")],
    lean=[L("Cells/AMergeTimed", "bidx_old_owner", "sufficient", note="field ack; under the arbiter's own RT2b"), L("Cells/AMergeTimed", "BidxB", "definition"),
          L("Cells/AMergeTimed", "bidx_old_owner_counter", "counter_trace", note="ack leg fails at the minimal capture: consumer still sees index 1; TA cancels, every server")] + AM_SI + ARBPIN,
    exactness="sufficient+necessary", exactness_note="Cm2: necessary and sufficient at a consistent corner (xr = xf) at the minimal capture. " + AM_X + " Arc-only margin, DELAY = 12: 1638 / 582 ps.",
    site_pins={"needed": True, "roles": ["ua2.I1, index_lut.I1 hi", "ustate.I4, ustate.I2, uor.I0 lo"]},
    rule={"rule": "A", "verdict": "different_condition", "detail": "as bundled_idx_grant"}, corner=CORNER_ARBPIN, check_scope="route_plus_env")
G2FALL_R = [wire("r2", "uarb.ugrant.I1", "wr2g"), sp("uarb.ugrant", "I1", "r2"), lut("uarb.ugrant", "I1", "O6", "g2f")]
G2FALL_Q = [wire("uarb.ustate.O6", "uarb.ugrant.I2", "wq"), sp("uarb.ugrant", "I2", "q"), lut("uarb.ugrant", "I2", "O6", "g2f")]
REQ_R = [wire("r2", "uarb.ustate.I1", "wr2s"), sp("uarb.ustate", "I1", "r2"), lut("uarb.ustate", "I1", "O5", "Rf2", note="per physical pin"),
         env("smin", "server minimum response R0 fall -> A0 fall (H_SERVER_MIN)", "smin"),
         wire("A0", "uarb.ustate.I4", "wa0s"), sp("uarb.ustate", "I4", "A0"), lut("uarb.ustate", "I4", "O6", "qr")]
for nm, mid, cnt in [("bundled_idx_ack_g", [wire("uarb.ugrant.O6", "uarb.ua2.I0", "wg2"), sp("uarb.ua2", "I0", "g2"), lut("uarb.ua2", "I0", "O6", "c2f"), wire("uarb.ua2.O6", "index_lut.I1", "wai")], None),
                     ("bundled_idx_grant_fall", [wire("uarb.ugrant.O6", "index_lut.I0", "wgi")], "bidx_old_owner_counter_g")]:
    pin, xs = ("I1", "xf") if nm == "bundled_idx_ack_g" else ("I0", "xf")
    add(id=f"bdc_amerge.{nm}", cell="bdc_amerge", also_applies_to=["bdc_amerge2_0 (7)"], catalogue_row="Cm H_BUNDLED_IDX race 2 (" + ("gack" if cnt is None else "grant") + " leg)",
        obligation="H_BUNDLED_IDX, previous owner leaves: g2's fall reaches " + ("ua2 (when it is A2's later input) and A2's fall the index LUT" if cnt is None else "the index LUT directly") + " before the new token's z_req reaches the consumer; g2 falls by r2 (via ugrant.I1) or by q (via ugrant.I2): either form suffices",
        inequality=("BidxB.gack: wr2g + g2f + wg2 + c2f + wai + xf + wid + su <= wr2s + Rf2 + smin + wa0s + qr + wfb + Rrq + dz  OR  wq + g2f + wg2 + c2f + wai + xf + wid + su <= wfb + Rrq + dz" if cnt is None else
                    "BidxB.grant: wr2g + g2f + wgi + xf + wid + su <= wr2s + Rf2 + smin + wa0s + qr + wfb + Rrq + dz  OR  wq + g2f + wgi + xf + wid + su <= wfb + Rrq + dz"),
        combine="any",
        forms=[form([G2FALL_R + mid + IDXOUT(pin, xs)], [REQ_R + UREQ() + DZ()], launch="r2 (in1_req) fall at the client driver", note="r2 leg (contains a whole server response)"),
               form([G2FALL_Q + mid + IDXOUT(pin, xs)], [UREQ() + DZ()], launch="q rise at uarb.ustate.O6", note="q leg")],
        lean=[L("Cells/AMergeTimed", "bidx_old_owner", "sufficient", note="field " + ("gack" if cnt is None else "grant")), L("Cells/AMergeTimed", "BidxB", "definition")]
             + ([L("Cells/AMergeTimed", cnt, "counter_trace", note="the grant leg fails at the minimal capture: consumer still sees index 1")] if cnt else []) + AM_SI + ARBPIN,
        exactness="sufficient" if cnt is None else "sufficient+necessary",
        exactness_note=("Cm2: sufficient; no counter-trace for this leg. " if cnt is None else "Cm2: sufficient; necessary at the minimal capture through the grant leg (bidx_old_owner_counter_g). ") + AM_X,
        site_pins={"needed": True, "roles": ["ugrant.I1/I2, index_lut pins hi", "ustate.I1/I4/I2, uor.I0 lo"]},
        rule={"rule": "A", "verdict": "different_condition", "detail": "as bundled_idx_grant"}, corner=CORNER_ARBPIN, check_scope="route_plus_env")
add(id="bdc_amerge.idx_ack_fork", cell="bdc_amerge", also_applies_to=["bdc_amerge2_0 (7; pin in1_ack)", "bdc_amerge3_0 index LUTs, per ack pin (stated, NOT proved)"], catalogue_row="Cm H_IDX_ACK_FORK",
    obligation="H_IDX_ACK_FORK: in1_ack's branch into the index LUT is faster than its other branch through the client, in1_req's fall, ugrant and g2 back to the index LUT (else the index drops inside the consumer's hold window)",
    inequality="wai + xr <= cmin + wr2g + g2f + wgi + xf (IdxAckFork); at a consistent corner the index arcs cancel: wai <= cmin + wr2g + g2f + wgi",
    forms=[form([[wire("uarb.ua2.O6", "index_lut.I1", "wai"), sp("index_lut", "I1", "in1_ack"), lut("index_lut", "I1", "O6", "xr")]],
                [[env("cmin", "client: in1_ack at ua2.O6 -> in1_req fall at its driver (H_CLIENT_MIN), min", "cmin")] + G2FALL_R +
                 [wire("uarb.ugrant.O6", "index_lut.I0", "wgi"), sp("index_lut", "I0", "g2"), lut("index_lut", "I0", "O6", "xf")]],
                launch="in1_ack (A2) rise at uarb.ua2.O6")],
    lean=[L("Cells/AMergeTimed", "idx_ack_fork_hold", "sufficient"), L("Cells/AMergeTimed", "IdxAckFork", "definition"),
          L("Cells/AMergeTimed", "idx_ack_fork_counter_minclient", "counter_trace", note="with the minimal client, not IdxAckFork gives index 0 while in1_ack is high"),
          L("Cells/AMergeTimed", "idx_ack_fork_counter", "counter_trace"), L("Cells/AMergeTimed", "idx_ack_fork_in_window", "lemma", note="that instant precedes z_ack's fall: the consumer is still holding"),
          L("Cells/AMergeTimedW", "fork_nonvacuous_slow", "non_vacuity"), L("Cells/AMergeTimedW", "fork_counter_witness", "counter_trace", note="700 ps in1_ack route against a two-arc client: index 0 at t = 496")]
         + AM_SI + [L("Cells/AMerge2Proof", "amerge2_needs_idx_ack_fork", "necessary", note="untimed")],
    exactness="sufficient+necessary", exactness_note="Cm2: necessary and sufficient at the minimal client. Not proved for amerge3's LUT4 (stated per pin). " + AM_X + " Arc-only margin with a two-arc client: 372 / 135 ps; the real client of each gcd_hw control_merge input was not walked.",
    site_pins={"needed": True, "roles": ["index_lut.I1 hi", "ugrant.I1, index_lut.I0 lo"]},
    rule={"rule": "none", "verdict": "none", "detail": "UNCHECKED: a pure route-skew condition no rule states"}, corner=CORNER_1C, check_scope="route_plus_env")

def rt2c(k):
    """bdc_amerge3 uarb1: bd_arbiter.rt2*/rt2b* with smin -> sR (rise) and the first smin -> sF (fall), sF/sR derived from uarb2's gates (cascade_server)."""
    j = 3 - k
    qe = "qf" if k == 1 else "qr"
    gname = f"g{k}"
    gf = "g1f1" if k == 1 else "g2f"
    gout = "O5" if k == 1 else "O6"
    rpin = "I0" if k == 1 else "I1"
    u = "uarb1."
    def srv(edge):
        rf = "Rr1" if edge == "rise" else "Rf1"
        c1 = "c1r" if edge == "rise" else "c1f"
        return [wire("acc1_req (uarb1.R0)", "uarb2.ustate.I0", "D2.wr1s"), sp("uarb2.ustate", "I0", "r1"), lut("uarb2.ustate", "I0", "O5", f"D2.{rf}", note="per physical pin"),
                env("smin2", "uarb2's server: R0 -> uor -> bd_delay_gated (DELAY 24) -> consumer -> z_ack, min (H_SERVER_MIN of uarb2)", "D2.smin"),
                wire("z_ack", "uarb2.ua1.I1", "D2.wa01"), sp("uarb2.ua1", "I1", "A0"), lut("uarb2.ua1", "I1", "O6", f"D2.{c1}")]
    sR, sF = srv("rise"), srv("fall")
    base_req = [wire("acc1_ack (uarb1.A0)", f"{u}ustate.I4", "wa0s"), sp(f"{u}ustate", "I4", "A0"), lut(f"{u}ustate", "I4", "O6", qe),
                fbw(f"{u}ustate", "O6", "I2", "wfb"), sp(f"{u}ustate", "I2", "q fb"), lut(f"{u}ustate", "I2", "O5", "Rrq", note="per physical pin")] + sR
    loop = [lut(f"{u}ua{k}", "{I0|I1}", "O6", f"c{k}f"), fbw(f"{u}ua{k}", "O6", "I2", f"wfa{k}"), sp(f"{u}ua{k}", "I2", "feedback")]
    gpath = [wire(f"r{k}", f"{u}ugrant.{rpin}", f"wr{k}g"), sp(f"{u}ugrant", rpin, f"r{k}"), lut(f"{u}ugrant", rpin, gout, gf),
             wire(f"{u}ugrant.{gout}", f"{u}ua{k}.I0", f"wg{k}"), sp(f"{u}ua{k}", "I0", "grant")]
    rpath = [wire(f"r{k}", f"{u}ustate.{rpin}", f"wr{k}s"), sp(f"{u}ustate", rpin, f"r{k}"), lut(f"{u}ustate", rpin, "O5", f"Rf{k}", note="per physical pin")] + sF
    fork_other = [wire("acc1_ack", f"{u}ua{j}.I1", f"wa0{j}"), sp(f"{u}ua{j}", "I1", "A0"), lut(f"{u}ua{j}", "I1", "O6", f"c{j}r")]
    rows = {
        "pulse": ("acc1_ack's low pulse at ua_k outlasts ua_k's fall loop", f"c{k}f + wfa{k} <= wa0s + {qe} + wfb + Rrq + sR",
                  form([loop], [base_req], launch="acc1_ack fall at its driver (uarb2.ua1.O6)")),
        gname: (f"{gname}'s fall reaches ua{k} and its loop closes before acc1_ack rises again",
                f"wr{k}g + {gf} + wg{k} + c{k}f + wfa{k} <= wr{k}s + Rf{k} + sF + sR + wa0s + {qe} + wfb + Rrq + wa0{k}",
                form([gpath + loop], [rpath + base_req + [wire("acc1_ack", f"{u}ua{k}.I1", f"wa0{k}"), sp(f"{u}ua{k}", "I1", "A0")]], launch=f"r{k} fall at the client driver")),
        "forkA": (f"A{k} falls before A{j} can rise (acc1_ack fork skew)", f"wa0{k} + c{k}f <= wa0s + {qe} + wfb + Rrq + sR + wa0{j} + c{j}r",
                  form([[wire("acc1_ack", f"{u}ua{k}.I1", f"wa0{k}"), sp(f"{u}ua{k}", "I1", "A0"), lut(f"{u}ua{k}", "I1", "O6", f"c{k}f")]], [base_req + fork_other], launch="acc1_ack fall at its driver")),
        "forkG": (f"the same along {gname}'s path", f"wr{k}g + {gf} + wg{k} + c{k}f <= wr{k}s + Rf{k} + sF + sR + wa0s + {qe} + wfb + Rrq + wa0{j} + c{j}r",
                  form([gpath + [lut(f"{u}ua{k}", "I0", "O6", f"c{k}f")]], [rpath + base_req + fork_other], launch=f"r{k} fall at the client driver")),
    }
    for name, (what, ineq, f) in rows.items():
        nm = name if k == 1 else (name + "2" if name != gname else gname)
        lean = ([L("Cells/AMergeTimedC", "rt2_cascade", "sufficient", note=f"field {name} of RT2C"), L("Cells/AMergeTimedC", "RT2C", "definition"),
                 L("Cells/AMergeTimedC", "rt2_cascade_counter", "counter_trace", note="cascade at its minimum (TA = TR + sF, TA2 = RR + sR): A1 and A2 of uarb1 both high (7h rt2_counter instantiated; no run exhibited)")]
                if k == 1 else
                [L("Cells/AMergeTimedC", "rt2_cascade2", "sufficient", note=f"field {name} of RT2Cb"), L("Cells/AMergeTimedC", "RT2Cb", "definition")])
        lean += [L("Cells/AMergeTimedC", "cascade_server", "reduction", note="uarb2 + its server is a server for uarb1 with responses sF (fall) / sR (rise); tight"),
                 L("Cells/AMergeTimedC", "cascade_nonvacuous", "non_vacuity", note="explicit runs of both arbiters, wired by rfl; sF, sR attained"),
                 L("Cells/AMergeTimedC", "cascade_corners", "corner", note="DELAY = 24: sR = 3376 / 1214 ps (SLOW_MAX / FAST_MIN)"),
                 L("Cells/AMerge3Proof", "amerge3_ok", "sufficient", note="untimed SI form (5630 states)"),
                 L("Cells/AMerge3Proof", "amerge3_needs_rt2_cascade", "necessary", note="untimed: runt on uarb1's previous ack")] + ARBPIN
        add(id=f"bdc_amerge3.rt2_cascade_{nm}", cell="bdc_amerge3", also_applies_to=["bdc_amerge3_0 uarb1 (1 instance in gcd_hw)", f"bd_arbiter.rt2{'' if k == 1 else 'b'}_{nm} with smin made explicit"],
            catalogue_row="Cm H_RT2_CASCADE",
            obligation=f"H_RT2_CASCADE (RT2{'' if k == 1 else 'b'} of uarb1, field {name}): {what}; uarb1's server is uarb2.ua1 + uarb2's server",
            inequality=ineq + "; sR = wr1s + Rr1 + smin2 + wa01 + c1r, sF = wr1s + Rf1 + smin2 + wa01 + c1f (uarb2's fields)",
            forms=[f], lean=lean, exactness="sufficient",
            exactness_note="Cm2: sufficient for every run of both arbiters and every server of uarb2, in scope H_IN2_IDLE (uarb2's own in2 idle during uarb1's handover; the in2-handover case is not proved). Side obligation H_ACK1_PULSE = bd_c2.pulse_width at uarb2.ua1. " + AM_X + " Arc-only margin of pulse, DELAY = 24: 3526 / 1256 ps.",
            site_pins={"needed": True, "roles": ["every w* term includes the physical pin's site delay (7h notation)"]},
            rule={"rule": "none", "verdict": "none", "detail": "UNCHECKED"}, corner=CORNER_ARBPIN, check_scope="route_plus_env")
rt2c(1); rt2c(2)
add(id="bdc_amerge3.bundled_idx0_grant", cell="bdc_amerge3", also_applies_to=["bdc_amerge3_0 (1)"], catalogue_row="Cm H_BUNDLED_IDX (amerge3 index[0], race 1)",
    obligation="H_BUNDLED_IDX for index[0] (LUT4 16'h000E, pins in1_ack, g2(arb1), g2(arb2), in2_ack): uarb1's new grant reaches index[0] and the consumer before the request, which now runs through uarb2's ustate O5, does",
    inequality="wq1 + g2r1 + wgi + xr + wid + su <= wfb1 + Rrq1 + wr1s2 + Rr1_2 + dz (BidxA3)",
    forms=[form([[wire("uarb1.ustate.O6", "uarb1.ugrant.I2", "wq1"), sp("uarb1.ugrant", "I2", "q"), lut("uarb1.ugrant", "I2", "O6", "g2r1"),
                  wire("uarb1.ugrant.O6", "index_lut.I1", "wgi")] + IDXOUT("I1", "xr")],
                [UREQ("uarb1.") + [wire("acc1_req (uarb1.R0)", "uarb2.ustate.I0", "wr1s2"), sp("uarb2.ustate", "I0", "r1"), lut("uarb2.ustate", "I0", "O5", "Rr1_2", note="per physical pin")] + DZ("uarb2.R0")],
                launch="q fall at uarb1.ustate.O6")],
    lean=[L("Cells/AMergeTimedC", "bidx3_new_owner", "sufficient", note="scope H_IN2_IDLE"), L("Cells/AMergeTimedC", "BidxA3", "definition"),
          L("Cells/AMergeTimedC", "bidx3_new_owner_counter", "counter_trace", note="minimal request path"), L("Cells/AMergeTimedC", "bidx3_nonvacuous_slow", "non_vacuity"),
          L("Cells/AMerge3Proof", "amerge3_ok", "sufficient", note="untimed SI form"), L("Cells/AMerge3Proof", "amerge3_needs_bundled_idx", "necessary", note="untimed")] + ARBPIN,
    exactness="sufficient+necessary", exactness_note="Cm2: necessary at the minimal request path. Not proved: index[1] (amerge2's theorems apply to uarb2's own handovers, the joint case is not modelled), race 2 for amerge3. " + AM_X + " Arc-only margin, DELAY = 24: 3154 ps (SLOW_MAX).",
    site_pins={"needed": True, "roles": ["uarb1.ugrant.I2, index_lut.I1 hi", "uarb1.ustate.I2, uarb2.ustate.I0, uor.I0 lo"]},
    rule={"rule": "A", "verdict": "different_condition", "detail": "as bdc_amerge.bundled_idx_grant"}, corner=CORNER_ARBPIN, check_scope="route_plus_env")

# =============================================================== bdc_muxn (generated N-way mux; probe Cm: B-amerge.md; probe Mn: B-muxn3-timed.md; 1 x bdc_muxn3_32 in gcd_hw)
MN_SI = [L("Cells/MuxN3Proof", "muxn3_ok", "sufficient", note="untimed SI (1728 states): one output transaction per control token, only the selected input acknowledged, no hazard on any gate incl. the inferred decode LUT3s"),
         L("Cells/MuxN3Proof", "muxn3_serves", "non_vacuity")]
MNT = "Cells/MuxN3Timed"
MN_T = [L(MNT, "muxn3_ok", "sufficient", note="timed whole-cell theorem (event form): join i fires exactly in the tokens selecting i, |j and z_req one clean transaction per control token, only the selected input acknowledged"),
        L(MNT, "muxn3_timing_of_static", "sufficient", note="MN3Timing (except reset sequencing and the line flush) derived from MN3Causal + MN3Static"),
        L(MNT, "muxn3_ok_static", "sufficient"), L(MNT, "MN3Static", "definition"), L(MNT, "MN3Causal", "definition"),
        L(MNT, "E_step", "lemma", note="selected-join edges increase from causality alone: no H_CTL_SEQ, no OR skew over the three j -> |j wires"),
        L(MNT, "static", "non_vacuity", note="Mn3Wit.static: every MN3Static field on the unit-delay witness (k-th token selects k % 3)"),
        L(MNT, "witness", "non_vacuity", note="Mn3Wit.witness = muxn3_ok applied; witness_values checks the acks and z_req")]
MN_X = ("Mn (B-muxn3-timed.md, MuxN3Timed.lean): real inferred INITs (decode LUT3 10/40/40, |j LUT3 FE, data LUT5 F0AA_CCF0), bd_c2 joins/acks, Lt2's FASTFALL line (bd_delay_gated as emitted); LUT arcs LUMPED over pins (H_LUT_FIFO): "
        "the decode's s-pin vs ctl-pin arc difference and the LUT5's per-pin arcs are charged as extra arcs; FIFO wire per fork branch, none isochronic. "
        "Kz = wo + Lo.lo + Dl + Es (selected join node -> z_ack at the server); Kj = wc + ls + wsj + lj (ctl_req -> decode -> join); Kc = Wzc.lo + Ec + Kj. "
        "Reset sequencing (H_RST_LONG, H_RST_EARLY) and the line's H_FLUSH_STAGE (bd_delay[FASTFALL].flush_per_stage) are taken in event form. Necessity of a form is shown only where stated.")

def MKj(m="m"):
    return [wire("ctl_req", f"sel_{m}.I2", "wc"), sp(f"sel_{m}", "I2", "ctl_req"), lut(f"sel_{m}", "I2", "O6", "ls"),
            wire(f"sel_{m}.O6", f"uj_{m}.I1", "wsj"), sp(f"uj_{m}", "I1", "sel"), lut(f"uj_{m}", "I1", "O6", "lj")]
def MKz(m="m", srv=True):
    a = [wire(f"uj_{m}.O6", "or3.{I0|I1|I2}", "wo"), sp("or3", "{I0|I1|I2}", "j"), lut("or3", "{I0|I1|I2}", "O6", "Lo.lo"),
         line("udly", "any", "stage-0 composite path or3 -> uor (LUT1) -> wire -> LUT1, then the taps", "bd_delay_gated (FASTFALL = 1) to z_req at the server, min over H 0 and Tp i (ffE_ge)", "Dl")]
    return a + ([env("Es", "server: z_req edge at its pin -> z_ack edge, min", "Es")] if srv else [])
def MKc(m="m"):
    return [wire("z_ack.drv", "ctl.sender (ctl_ack = z_ack)", "Wzc.lo"), env("Ec", "control sender: ctl_ack edge seen -> next ctl_req edge (MN3Causal), min", "Ec")] + MKj(m)
def uacel(i, pin, src, W, role):
    return [wire(src, f"ua_{i}.{pin}", f"{W}.hi"), sp(f"ua_{i}", pin, role), lut(f"ua_{i}", pin, "O6", "La.hi"), fbw(f"ua_{i}", "O6", "I2", "wah"), sp(f"ua_{i}", "I2", "feedback")]
MN_ALSO = ["bdc_muxn3_32 (1 instance in gcd_hw)"]

add(id="bdc_muxn.rtz", cell="bdc_muxn", also_applies_to=MN_ALSO, catalogue_row="Cm H_MUX_RTZ",
    obligation="S_A_RTZ (H_MUX_RTZ): z_ack's pulse at ua_k (either polarity) outlasts ua_k's arc + feedback loop plus the z_ack wire's spread, against the round trip z_ack -> control sender -> ctl_req -> decode -> next join -> |j -> line -> server",
    inequality="Wza.hi + La.hi + wah <= Wza.lo + Kc + Kz (per k; m = the next token's selected input, any)",
    forms=[form([uacel("k", "I1", "z_ack.drv", "Wza", "z_ack")],
                [[wire("z_ack.drv", "ua_k.I1", "Wza.lo"), sp("ua_k", "I1", "z_ack")] + MKc("m") + MKz("m")],
                launch="z_ack edge at its driver", note="MN3Static.S_A_RTZ; redundant when Wza.hi - Wza.lo <= Wja.hi - Wja.lo (rtz_of_fork_j, given bdc_muxn.iso_zack)")],
    lean=MN_T + [L(MNT, "rtz_of_fork_j", "redundancy", note="S_A_RTZ follows from S_A_FORK and S_A_J's second half whenever the z_ack branch's spread is at most the j branch's (any fixed-delay run)"),
                 L("Cells/MuxN3Proof", "muxn3_needs_rtz", "necessary", note="untimed: runt on in0_ack, as bd_mux"),
                 L("Cells/MuxRtzTimed", "rtz_safe", "context", note="cell-level H_RTZ for any bd_c2 loop with a low j input: applies to ua_k verbatim")] + MN_SI,
    status="proved", exactness="sufficient+necessary_untimed",
    exactness_note="P6 / Mn: MN3Static.S_A_RTZ, proved sufficient inside muxn3_timing_of_static + muxn3_ok (the JSON's old arc set, with the Lean's composite stage-0 line path in place of |j -> uor -> udly). REDUNDANT, and the checker may skip it, when the z_ack wire's spread at ua_k is at most the j wire's, (Wza.hi - Wza.lo) <= (Wja.hi - Wja.lo), given bdc_muxn.iso_zack (S_A_FORK and S_A_J (2)); so no transport run in the static family violates it alone. Necessity untimed only (muxn3_needs_rtz); an event-form counter-run (asymmetric Ec) is designed, not built. " + MN_X,
    site_pins={"needed": True, "roles": ["ua_k.I1 hi and lo", "ua_k.I2 hi", "sel_m.I2, uj_m.I1, or3 pin lo"]},
    rule={"rule": "none", "verdict": "none", "detail": "UNCHECKED"}, corner=CORNER_OPS, check_scope="route_plus_env")
add(id="bdc_muxn.s_setup", cell="bdc_muxn", also_applies_to=MN_ALSO, catalogue_row="Cm H_S_PIN (setup)",
    obligation="S_S_SETUP / S_Z_S: the index bits, settled at the control sender's driver Lsd before its ctl_req rise, reach each decode LUT3 before ctl_req does, and each data LUT5 bit before z_req reaches the server",
    inequality="decode i, per bit b: Ws_b(i).hi <= Lsd + Wc(i).lo (+ per-pin arc margin sel_i.I{0,1} vs sel_i.I2); data LUT5, per bit: sh_b + Mz <= Lsd + Kj + wo + Lo.lo + Dl",
    forms=[form([[wire("s{0|1}.drv", "sel_i.{I0|I1}", "Ws0/Ws1.hi"), sp("sel_i", "{I0|I1}", "s"), lut("sel_i", "{I0|I1}", "O6", note="not in the Lean model (lumped decode arc); per-pin margin")]],
                [[env("Lsd", "control sender: index settled at its driver -> ctl_req rise at its port (MN3DataEnv.H_S_LEAD; the link n_index_97 latching the amerge3 index), min", "Lsd"),
                  wire("ctl_req", "sel_i.I2", "Wc.lo"), sp("sel_i", "I2", "ctl_req"), lut("sel_i", "I2", "O6", note="not in the Lean model; per-pin margin")]],
                launch="index settled at the control sender's driver", note="S_S_SETUP (muxn3_s_pin_of_static), per decode i and bit; exact (Mn3Cex)"),
           form([[wire("s{0|1}.drv", "zdat.{I3|I4}", "sh0/sh1"), sp("zdat", "{I3|I4}", "s"), lut("zdat", "{I3|I4}", "O6", "sh0/sh1"), env("Mz", "consumer margin before z_req reaches the server", "Mz")]],
                [[env("Lsd", "control sender: index settled -> ctl_req rise, min", "Lsd")] + MKj("m") + MKz("m", srv=False)],
                launch="index settled at the control sender's driver", note="MN3DataStatic.S_Z_S, data LUT5 F0AA_CCF0, per bit (32)")],
    lean=[L(MNT, "muxn3_s_pin_of_static", "sufficient", note="H_S_PIN at every decode from S_S_SETUP and S_S_HOLD and the sender's contract"),
          L(MNT, "muxn3_data_ok", "sufficient", note="LUT5 output = the selected input's bit from Mz before z_req until Hm after z_ack, under MN3DataStatic (S_Z_S)"),
          L(MNT, "MN3DataStatic", "definition"), L(MNT, "MN3DataEnv", "definition"),
          L(MNT, "dm5_sel", "lemma", note="kernel-checked on the INIT: with definite index bits of v < 3 the LUT5 output is the selected pin whatever the other two read, x included"),
          L(MNT, "bnd_ok", "instance", note="Mn3Cex: s wires 1 tick, S_S_SETUP with equality, muxn3_ok_static applies"),
          L(MNT, "cex_setup_violated", "counter_trace", note="Mn3Cex: s wires 2 ticks, S_S_SETUP fails by one tick, S_S_HOLD holds, every other hypothesis the same proof term"),
          L(MNT, "cex_fails", "counter_trace", note="decode 0 emits a one-tick runt in token 1; join 0 high at 52 in [E 2, E 3): muxn3_ok's conclusion (1) is false; in0_ack high at 59"),
          L(MNT, "s_pin_static", "non_vacuity", note="Mn3Wit: H_S_PIN from muxn3_s_pin_of_static, S_S_SETUP tight"),
          L(MNT, "data_witness", "non_vacuity", note="Mn3Wit: muxn3_data_ok applied; data_values: non-degenerate bits")] + MN_T
         + [L("Cells/AMergeGates", "sel_needs_setup", "necessary", note="Kleene: a moving s pin under a high ctl_req gives x"),
            L("Cells/AMergeGates", "sel_idle", "context", note="decodes ignore s while ctl_req is low"), L("Cells/AMergeGates", "dm5_eq", "function_equality")] + MN_SI,
    status="proved", exactness="sufficient+necessary_at_boundary",
    exactness_note="P6 / Mn: decode form (S_S_SETUP) proved sufficient and EXACT in the counter-run family Mn3Cex (boundary holds, boundary + 1 corrupts the token: one-tick counter-run with every other hypothesis unchanged). Tight on one run, not a general iff. Data LUT5 form (S_Z_S): proved sufficient (muxn3_data_ok, non-vacuous data_witness), no counter-run. " + MN_X,
    site_pins={"needed": True, "roles": ["sel_i.I0/I1, zdat.I3/I4 (s) hi", "sel_i.I2 (ctl_req) lo", "uj_m.I1, or3 pin lo"]},
    rule={"rule": "E (skew.py)", "verdict": "exact_structure_missing_site_pins", "detail": "rule E's common-launch setup form, if it is applied to these LUTs; no SP terms"},
    corner=CORNER_OPS, check_scope="route_plus_env")
add(id="bdc_muxn.s_hold", cell="bdc_muxn", also_applies_to=MN_ALSO, catalogue_row="Cm H_CTL_HOLD / H_S_PIN (hold)",
    obligation="S_S_HOLD: ctl_req's fall reaches each decode LUT3 before the next index change does, under the header's contract (index held until the sender has SEEN ctl_ack fall)",
    inequality="Wc(i).hi <= Kj + Kz + Wzc.lo + Ws_b(i).lo (per decode i, per bit b); the data LUT5 hold needs no inequality (S_HM are sums of MIN delays)",
    forms=[form([[wire("ctl_req", "sel_i.I2", "Wc.hi"), sp("sel_i", "I2", "ctl_req"), lut("sel_i", "I2", "O6", note="per-pin margin, not in Lean")]],
                [MKj("m") + MKz("m") + [wire("z_ack.drv", "ctl.sender (ctl_ack = z_ack)", "Wzc.lo"), env("hold", "sender: ctl_ack fall seen -> next index change at its driver, >= 0 (MN3DataEnv.H_S_HOLD)"),
                                        wire("s{0|1}.drv", "sel_i.{I0|I1}", "Ws0/Ws1.lo"), sp("sel_i", "{I0|I1}", "s"), lut("sel_i", "{I0|I1}", "O6", note="per-pin margin, not in Lean")]],
                launch="ctl_req fall at the control sender", note="S_S_HOLD (muxn3_s_pin_of_static)")],
    lean=[L(MNT, "muxn3_s_pin_of_static", "sufficient"), L(MNT, "MN3DataEnv", "definition", note="H_S_HOLD: index held until the sender has seen ctl_ack fall"),
          L(MNT, "muxn3_data_ok", "sufficient", note="data LUT5 hold: S_HM only")] + MN_T
         + [L("Cells/MuxN3Proof", "muxn3_needs_hold", "necessary", note="untimed: s moves under a high ctl_req, sel[0] runt"),
            L("Cells/AMergeGates", "sel_needs_setup", "necessary", note="Kleene")] + MN_SI,
    status="proved", exactness="sufficient",
    exactness_note="P6 / Mn: proved sufficient under the header's hold contract; the margin is a whole round trip, so it binds only for a pathological ctl_req wire. Timed necessity not probed (untimed: muxn3_needs_hold). " + MN_X,
    site_pins={"needed": True, "roles": ["sel_i.I2 hi", "sel_i.I0/I1 lo", "uj_m.I1, or3 pin lo"]},
    rule={"rule": "none", "verdict": "none", "detail": "UNCHECKED"}, corner=CORNER_OPS, check_scope="route_plus_env")
add(id="bdc_muxn.iso_ctl", cell="bdc_muxn", also_applies_to=MN_ALSO, catalogue_row="Cm isochrony",
    obligation="ctl_req -> {sel_0, sel_1, sel_2} fork: NO skew bound under FIFO branches (selected-edge order from causality, E_step; unselected decodes stay low by H_S_PIN + selF_off). Its only timed content is S_J_C per branch: join i's own feedback settles before z_req -> z_ack -> control sender -> ctl_req -> decode i returns to the join",
    inequality="Lj(i).hi + wjh(i) <= Lj(i).lo + Kz + Wzc.lo + Ec + Wc(i).lo + Ls(i).lo + Wsj(i).lo (per i)",
    forms=[form([[lut("uj_i", "{I0|I1}", "O6", "Lj.hi"), fbw("uj_i", "O6", "I2", "wjh"), sp("uj_i", "I2", "feedback")]],
                [[lut("uj_i", "{I0|I1}", "O6", "Lj.lo")] + MKz("i") + [wire("z_ack.drv", "ctl.sender (ctl_ack = z_ack)", "Wzc.lo"), env("Ec", "control sender latency, min", "Ec")] + MKj("i")],
                launch="join i's node edge", note="MN3Static.S_J_C, per branch i")],
    lean=MN_T + [L(MNT, "selF_off", "lemma", note="sel_i = 0 while ctl_req is low"), L(MNT, "selF_idx", "lemma", note="sel_i = ctl_req . (v = i) for v < 3 (from the INITs)"),
                 L("Cells/MergeMuxSI", "mux_needs_iso_cr", "necessary", note="bd_mux analogue, untimed: two transitions in flight on one branch, which a FIFO wire excludes by assumption")] + MN_SI,
    status="proved", exactness="sufficient",
    exactness_note="P6 / Mn: refines 'branch skew < half a handshake' (as bd_mux.isochronic_forks' ctl branch): no skew condition, only the per-branch join env latency S_J_C. Not shown necessary. " + MN_X,
    site_pins={"needed": True, "roles": ["uj_i.I2 (feedback) hi", "sel_i.I2, uj_i.I1, or3 pin lo"]},
    rule={"rule": "none", "verdict": "none", "detail": "UNCHECKED"}, corner=CORNER_OPS, check_scope="route_plus_env")
add(id="bdc_muxn.iso_zack", cell="bdc_muxn", also_applies_to=MN_ALSO, catalogue_row="Cm isochrony",
    obligation="z_ack -> {ua_0, ua_1, ua_2, ctl sender} fork (S_A_FORK) and ua_i's env latency at its j input (S_A_J): z_ack's edge settles ua_i's loop before the next join edge, launched by the same z_ack edge through the control sender, reaches ua_i; j_i's edge outlasts ua_i's loop until the next j edge and the next z_ack edge",
    inequality="Wza(i).hi + La(i).hi + wah(i) <= Kc + Wja(i).lo; Wja(i).hi + La(i).hi + wah(i) <= Kz + Kc + Wja(i).lo and <= 2 Kz + Kc + Wza(i).lo",
    forms=[form([uacel("i", "I1", "z_ack.drv", "Wza", "z_ack")], [MKc("m") + [wire("uj_i.O6", "ua_i.I0", "Wja.lo"), sp("ua_i", "I0", "j")]],
                launch="z_ack edge at its driver", note="S_A_FORK, per i"),
           form([uacel("i", "I0", "uj_i.O6", "Wja", "j")], [MKz("m") + MKc("m") + [wire("uj_i.O6", "ua_i.I0", "Wja.lo"), sp("ua_i", "I0", "j")]],
                launch="join i's node edge", note="S_A_J (1): next j edge"),
           form([uacel("i", "I0", "uj_i.O6", "Wja", "j")], [MKz("m") + MKc("m") + MKz("m") + [wire("z_ack.drv", "ua_i.I1", "Wza.lo"), sp("ua_i", "I1", "z_ack")]],
                launch="join i's node edge", note="S_A_J (2): next z_ack edge")],
    lean=MN_T + [L("Cells/MergeMuxSI", "mux_needs_iso_za", "necessary", note="bd_mux analogue (untimed); no muxn3-specific counter-run")] + MN_SI,
    status="proved", exactness="sufficient",
    exactness_note="P6 / Mn: MN3Static.S_A_FORK and S_A_J, proved sufficient. For an input the next token does not select, S_A_FORK constrains a bookkeeping edge (j_i does not move); like Lt3's skew results it may be a proof artefact there. Not shown necessary. " + MN_X,
    site_pins={"needed": True, "roles": ["ua_i.I1, ua_i.I0 hi and lo", "ua_i.I2 hi", "sel_m.I2, uj_m.I1, or3 pin lo"]},
    rule={"rule": "none", "verdict": "none", "detail": "UNCHECKED"}, corner=CORNER_OPS, check_scope="route_plus_env")
add(id="bdc_muxn.bundled_z_data", cell="bdc_muxn", also_applies_to=MN_ALSO, catalogue_row="Cm (new, B-muxn3-timed.md)",
    obligation="S_Z_D: input i's data, settled at its driver Ld before in_i_req rises, settles at the data LUT5 output before z_req (through join i) reaches the server",
    inequality="dh(i) + Mz <= Ld + Wx(i).lo + Lj(i).lo + wo + Lo.lo + Dl (per i, per bit)",
    forms=[form([[wire("in_i_data.drv", "zdat.I{2-i}", "dh"), sp("zdat", "I{2-i}", "in_i data"), lut("zdat", "I{2-i}", "O6", "dh"), env("Mz", "consumer margin", "Mz")]],
                [[env("Ld", "client i: data settled at its driver -> in_i_req rise (MN3DataEnv.H_D_LEAD), min", "Ld"),
                  wire("in_i_req", "uj_i.I0", "Wx.lo"), sp("uj_i", "I0", "in_i_req"), lut("uj_i", "I0", "O6", "Lj.lo")] + MKz("i", srv=False)],
                launch="in_i data settled at client i's driver", note="MN3DataStatic.S_Z_D, per i")],
    lean=[L(MNT, "muxn3_data_ok", "sufficient"), L(MNT, "MN3DataStatic", "definition"), L(MNT, "MN3DataEnv", "definition"),
          L(MNT, "dm5_sel", "lemma"), L(MNT, "data_witness", "non_vacuity", note="Mn3Wit.data_witness; data_values: 1,0,1,0,1,0 over inputs 0,1,2,0,1,2, an unselected input carrying the opposite bit")],
    exactness="sufficient",
    exactness_note="P6 / Mn: new entry (was missing). Proved sufficient; as Lt3 found for bd_mux's S_Z_X, probably only sufficient when the decode is the join's late input (exact when in_i_req is late, by analogy with Lt4's MuxA; not built for muxn). " + MN_X,
    site_pins={"needed": True, "roles": ["zdat.I0/I1/I2 (data) hi", "uj_i.I0 (req) lo", "or3 pin lo"]},
    rule={"rule": "A", "verdict": "different_condition", "detail": "rule A's sender-request-last form is the classic version (sufficient for it only with the lead term)"},
    corner=CORNER_OPS, check_scope="route_plus_env")
add(id="bdc_muxn.uj_env_latency_req", cell="bdc_muxn", also_applies_to=MN_ALSO + ["bd_c2.env_latency at uj_i"], catalogue_row="Cm (new, B-muxn3-timed.md)",
    obligation="S_J_X: join i's own feedback settles before its answer (j_i -> ua_i -> in_i_ack -> client i -> in_i_req) returns to the join",
    inequality="Lj(i).hi + wjh(i) <= Lj(i).lo + Wja(i).lo + La(i).lo + Wak(i).lo + Ex + Wx(i).lo (per i)",
    forms=[form([[lut("uj_i", "{I0|I1}", "O6", "Lj.hi"), fbw("uj_i", "O6", "I2", "wjh"), sp("uj_i", "I2", "feedback")]],
                [[lut("uj_i", "{I0|I1}", "O6", "Lj.lo"), wire("uj_i.O6", "ua_i.I0", "Wja.lo"), sp("ua_i", "I0", "j"), lut("ua_i", "I0", "O6", "La.lo"),
                  wire("ua_i.O6", "client i", "Wak.lo"), env("Ex", "client i: ack edge seen -> request edge (MN3Causal), min", "Ex"),
                  wire("in_i_req", "uj_i.I0", "Wx.lo"), sp("uj_i", "I0", "in_i_req")]],
                launch="join i's node edge", note="MN3Static.S_J_X, per i")],
    lean=MN_T, exactness="sufficient",
    exactness_note="P6 / Mn: new entry (bd_mux analogue bd_mux.uj_env_latency_req). Proved sufficient; only sufficient by Lt4's bd_mux analysis (the return path also waits for z_ack), not probed for muxn. " + MN_X,
    site_pins={"needed": True, "roles": ["uj_i.I2 (feedback) hi", "uj_i.I0 (req) lo", "ua_i.I0 lo"]},
    rule={"rule": "none", "verdict": "none", "detail": "UNCHECKED"}, corner=CORNER_OPS, check_scope="route_plus_env")

# =============================================================== mlink / flink
for cell, ctl, en, enpins in [("bd_mlink", "ux", "en", "I0"), ("bd_flink", "uck", "ck", "I0")]:
    uq = "ctl.uq" if cell == "bd_mlink" else "ctl.uq"
    add(id=f"{cell}.qfb_first", cell=cell, catalogue_row="ML1",
        obligation=f"H_QFB_FIRST: the request latch's own feedback (done -> uq.I2) settles before {ctl} reacts through {en}",
        inequality=f"fhi <= wlo + elo: done -> uq.I2 wire + SP + I2 arc (max) <= done -> {ctl}.I0 wire + SP + {ctl} arc (min) + {en} -> uq.I1 wire + SP + I1 arc (min) (qfb_clean_form, when done makes one clean edge); general Lean form H_QFB_FIRST_T max(max(A+whi, B+ahi) + ehi, Td + dhi) + fhi <= Tq + wlo + elo",
        forms=[form([[fbw(uq, "O6", "I2", "fhi"), sp(uq, "I2", "feedback", "in fhi"), lut(uq, "I2", "O6", "in fhi")]],
                    [[wire(f"{uq}.O6", f"ctl.{ctl}.I0", "wlo"), sp(f"ctl.{ctl}", "I0", "done", "in wlo"), lut(f"ctl.{ctl}", "I0", "O6", "in wlo"),
                      wire(f"ctl.{ctl}.O6", f"{uq}.I1", "elo"), sp(uq, "I1", en, "in elo"), lut(uq, "I1", "O6", "in elo")]],
                    margin=0, launch="done edge at uq.O6", note="P3: the JSON's former strict '<' (margin 1) relaxes to '<=' in the discrete model (qfb_counter: one tick more oscillates; qfb_clean: equality is clean). In the window model uq's I2 and I1 arcs are inside fhi and elo; they cancel only with prjxray's flat O6 arc at one corner")],
        lean=[L("Cells/LibEndMemMlink", f"{'mlink' if cell == 'bd_mlink' else 'flink'}_req_bit_H", "sufficient", note="interleaving schedule allowH"),
              L("Cells/LibEndMemMlink", f"{'mlink' if cell == 'bd_mlink' else 'flink'}_runt", "counter_trace"),
              L("Cells/LibEndMemMlink", f"{'mlink' if cell == 'bd_mlink' else 'flink'}_cycle", "counter_trace"),
              L("Cells/LibEndMemMlink", "masks_fail_without_H", "necessary"),
              L("Cells/ConstraintsMore", f"{'mlink' if cell == 'bd_mlink' else 'flink'}_qfb_first_timed", "sufficient", note="H_QFB_FIRST_T, H_ACK_STABLE, H_GAP, H_HOLD: done captures and holds the new token, no runt"),
              L("Cells/ConstraintsMore", "qfb_clean_form", "lemma", note="S <= Tq (one clean done edge): H_QFB_FIRST_T reduces to fhi <= wlo + elo"),
              L("Cells/ConstraintsMore", "capture_gap", "lemma")]
             + ([L("Cells/ConstraintsMore", "mlink_uq_latch", "relation"), L("Cells/ConstraintsMore", "ux_open", "lemma", note="ux F9 keeps the latch open until wlo after done shows the new value"),
                 L("Cells/ConstraintsMore", "qfb_counter", "counter_trace", note="closed-form transport run of the whole request-bit loop (real INITs, ack = 0), fhi = 3 > wlo + elo = 2: done rises 6, falls 8, oscillates with period 3"),
                 L("Cells/ConstraintsMore", "qfb_clean", "twin", note="same environment, fhi = 2 = wlo + elo: one clean edge")]
                if cell == "bd_mlink" else
                [L("Cells/ConstraintsMore", "flink_uq_latch", "relation", note="E2 is LatchRel with enable !ck (winK_not)"), L("Cells/ConstraintsMore", "uck_open", "lemma")]),
        status="proved", exactness="sufficient+necessary_at_boundary" if cell == "bd_mlink" else "sufficient",
        exactness_note=("P3 (B-constraints-more.md): mlink_qfb_first_timed, sufficient; tight by one tick on a witness (qfb_counter oscillates at fhi = wlo + elo + 1, qfb_clean is clean at equality), not a general iff. Untimed S/N (mlink_req_bit_H, masks_fail_without_H) still cited. NOPEN > 1 (uz path) not modelled."
                        if cell == "bd_mlink" else
                        "P3 (B-constraints-more.md): flink_qfb_first_timed, sufficient; no flink counter-trace. NOPEN > 1 (uz path) not modelled."),
        site_pins={"needed": True, "roles": ["uq.I2 hi", f"{ctl}.I0 lo", "uq.I1 lo"]},
        rule={"rule": "none", "verdict": "none", "detail": "UNCHECKED; not emitted by bdc"}, corner=CORNER_1C, check_scope="static_route")

# =============================================================== bd_mem
MEMSRC = [L("Cells/LibEndMemMlink", "setup_ok", "sufficient")]
add(id="bd_mem.setup", cell="bd_mem", catalogue_row="ME1",
    obligation="RAM setup: addr/wdata/we settled tSU before CLKARDCLK rise",
    inequality="tSU <= dsLo (DSETUP line + ubuf + clock net, MIN); payload settled at the RAM pins by req rise (H_FOUR_PHASE_ENV)",
    forms=[form([[param("tSU", "RAMB18E1 setup to CLKARDCLK (prjxray BRAM_L max corner: 566/737/532 ps by pin class)")]],
                [[line("usetup", "rise", "chain", "DSETUP sym line", "dsLo"), lut("ubuf", "I0", "O6", "dsLo"), wire("ubuf.O6", "ram.CLKARDCLK", "dsLo")]],
                launch="req rise at bd_mem (payload already at the RAM pins)")],
    lean=MEMSRC, exactness="sufficient", exactness_note="payload route skew is the requester's bundling (tPay at the RAM pins is an environment hypothesis).",
    site_pins={"needed": True, "roles": ["ubuf.I0"]}, rule={"rule": "B", "verdict": "conservative_partial", "detail": "only when clock and payload share a source; else 'caller's to meet'"},
    corner=CORNER_1C, check_scope="static_route")
add(id="bd_mem.hold", cell="bd_mem", catalogue_row="ME2", obligation="RAM hold: payload held tHD after CLKARDCLK rise",
    inequality="tHD <= dcLo + dsLoF + dcLoF (ack round trip)",
    forms=[form([[param("tHD", "RAMB18E1 hold")]], [[line("uco", "rise", "chain", "DCO line + ack wire", "dcLo"), env("req_fall", "requester: ack rise -> req fall >= 0"),
                 line("usetup", "fall", "chain", "DSETUP fall + ubuf + clock net", "dsLoF"), line("uco", "fall", "chain", "DCO fall", "dcLoF"), env("pay_next", "ack fall -> next payload >= 0")]],
                launch="CLKARDCLK rise")],
    lean=[L("Cells/LibEndMemMlink", "hold_ok", "sufficient")], exactness="sufficient", site_pins={"needed": False, "roles": []},
    rule={"rule": "none", "verdict": "none", "detail": "not a separate gate (tighten.py l.177-180 reports HOLD arcs)"}, corner=CORNER_1C)
add(id="bd_mem.rdata_before_ack", cell="bd_mem", catalogue_row="ME3", obligation="read data valid before ack (DOA_REG = 0)",
    inequality="tCO <= dcLo, PLUS the consumer's rdata-vs-ack route skew (H_RDATA_ROUTE, named in the Lean doc, NOT in the theorem)",
    forms=[form([[param("tCO", "RAMB18E1 clock-to-out (2454 ps used by rule C)"), env("rdata_route", "DOADO -> consumer, hi (NOT in the Lean theorem)")]],
                [[line("uco", "rise", "chain", "DCO line", "dcLo"), env("ack_route", "ack -> consumer, lo (NOT in the Lean theorem)")]], launch="CLKARDCLK rise")],
    lean=[L("Cells/LibEndMemMlink", "rdata_before_ack", "sufficient", note="without H_RDATA_ROUTE")],
    exactness="sufficient", exactness_note="the route-skew terms are added here; the Lean theorem covers tCO <= dcLo only.",
    site_pins={"needed": True, "roles": ["consumer pins"]}, rule={"rule": "C", "verdict": "missing_term", "missing": "consumer rdata-vs-ack route skew"}, corner=CORNER_1C)
add(id="bd_mem.clk_high_width", cell="bd_mem", catalogue_row="ME4", obligation="RAM clock high width vs tPWH",
    inequality="tPWH <= dsLo + dcLo + dsLoF - dsHi (clk_high_width gives width >= the right side; ConstraintsMore.MemPort.clk_high_ok makes the comparison a theorem)",
    forms=[form([[param("tPWH", "RAMB18E1 min clock high pulse"), line("usetup", "rise", "chain", "DSETUP + ubuf + clk, hi", "dsHi")]],
                [[line("usetup", "rise", "chain", "lo", "dsLo"), line("uco", "rise", "chain", "lo", "dcLo"), line("usetup", "fall", "chain", "lo", "dsLoF")]], launch="req rise")],
    lean=[L("Cells/LibEndMemMlink", "clk_high_width", "bound"), L("Cells/LibEndMemMlink", "rtz_serialised", "bound"),
          L("Cells/ConstraintsMore", "clk_high_ok", "sufficient", note="MemPort.clk_high_ok: tPWH + dsHi <= dsLo + dcLo + dsLoF implies tClkR + tPWH <= tClkF"),
          L("Cells/ConstraintsMore", "clk_low_ok", "sufficient", note="MemPort.clk_low_ok: tPWL <= dcLoF + dsLo implies tClkF + tPWL <= tClkR2 (companion low-width bound)")],
    exactness="sufficient", exactness_note="P3: MemPort.clk_high_ok, sufficient (arithmetic on clk_high_width with the MemPort hypotheses H_SETUP_LINE, H_CO_LINE, H_FOUR_PHASE_ENV). Datasheet parameters only; BRAM is not a gate model.",
    site_pins={"needed": False, "roles": []}, rule={"rule": "none", "verdict": "none"}, corner=CORNER_1C)


# =============================================================== design-level reset (probes Rst, Rst2: B-reset-contract.md, B-reset-gcd.md)
# rst_src = gcd_hw.v's rig_rst LUT output (~por_done | rst_sr[15]); w_rst(X) = the routed rst net to pin X.
RC = "Cells/ResetContract"
RG = "Cells/ResetGcd"
RST_X = ("Rst/Rst2: no route, so no form is evaluated. ResetGcd's results are about the ELABORATED RTL control netlist of gcd_hw (bdc default DELAY_* sizes, gcd_rig CMPD = 16; "
         "3322 nodes, real INITs and pin lists, Verilog -> Lean by an unverified generator cross-checked against yosys by WL colour refinement), not the synthesized or routed netlist. "
         "The GMW network theorems are in model steps (D = LUT bound, W = wire bound); the per-cell timed lemmas are window channels; the two are not one theorem.")
RST_CELLS = ["185 bd_c2n (link/pipe controllers, uenv0)", "1 bd_c2n_set (uenv1)", "153 bd_c2 (incl. 18 arbiter acks, 42 mux acks, 6 muxn3 C-elements)",
             "10 bd_c3", "14 bd_c4", "21 + 21 bd_mux uj0/uj1", "9 bd_arbiter ustate O6 (+ 9 O5 read rst: 423 rst pins)"]
add(id="design.rst_hold", cell="design", also_applies_to=["per reset-carrying LUT G of gcd_hw (414): " + "; ".join(RST_CELLS), "generalises bd_c2.reset_width, bd_c2n.reset_width, bd_c3.reset_width, bd_c4.reset_width"],
    catalogue_row="Rst section 3.1 (C16)",
    obligation="rst held at every reset pin for the cell's loop bound: each reset-carrying LUT reaches its reset value from ANY power-up state (binary and all-X)",
    inequality="w_rst(G.I_rst).hi + SP + G arc I_rst -> O (dlmax) + feedback wire (dwmax) + feedback SP <= rst_width + w_rst(G.I_rst).lo, per G",
    forms=[form([[wire("rst_src", "G.I_rst", "w_rst(G).hi"), sp("G", "I_rst", "rst"), lut("G", "I_rst", "O6", "dlmax"), fbw("G", "O6", "I_fb", "dwmax"), sp("G", "I_fb", "feedback")]],
                [[env("rst_width", "rst_src high, min (gcd_hw: 16 hk cycles from rst_sr; 24 more at POR)", "rst_width"), wire("rst_src", "G.I_rst", "w_rst(G).lo"), sp("G", "I_rst", "rst")]],
                launch="rst_src rise", note="per reset-carrying LUT G")],
    lean=[L(RC, "c2n_reset", "sufficient", note="timed reset and hold through release, any power-up (LoopG window channels)"), L(RC, "c2n_set_reset", "sufficient"),
          L("Cells/CElemTiming", "c2_reset", "sufficient"), L("Cells/CTreeTimed", "c3_reset", "sufficient"), L("Cells/CTreeTimed", "c4_reset", "sufficient")]
         + [L(RC, f"{c}_rstB", "function_equality", note="rst = 1 forces the reset value for every Boolean value of every other pin") for c in ("c2", "c2n", "c2n_set", "c3", "c4", "uj0", "uj1", "arb")]
         + [L(RC, f"{c}_rstK", "lemma", note="the same for every K3 value (all-X power-up)") for c in ("c2", "c2n", "c2n_set", "c3", "c4", "uj0", "uj1", "arb")]
         + [L(RG, "gcd_census", "instance", note="414 reset cells, 423 rst pins, by kind"), L(RG, "gcd_spec", "instance", note="ResetSpec on the whole gcd_hw control network (decide +kernel)"),
            L(RG, "neg_norst", "counter_trace", note="negative control: ulink_n1__1's rst pin tied to 0 fails the check")],
    exactness="sufficient",
    exactness_note="P6 / Rst: sufficient; the per-cell form of bd_c*.reset_width, now with a general bd_c2n theorem. Necessity not shown separately (same loop as pulse_width). " + RST_X,
    site_pins={"needed": True, "roles": ["G.I_rst hi and lo", "G feedback pin hi"]},
    rule={"rule": "none", "verdict": "none", "detail": "UNCHECKED; rst is a general-routed net with fanout 414 (skew unknown)"}, corner=CORNER_1C, check_scope="route_plus_env")
add(id="design.rst_flush", cell="design", also_applies_to=["per reset cell G and per non-rst control pin p of G driven, through stateless LUTs and delay lines, by reset cell H"], catalogue_row="Rst section 3.2 (C16)",
    obligation="rst held long enough for every stateless control LUT and delay line to flush to its reset value (rank by rank) before release",
    inequality="w_rst(H.I_rst).hi + SP + H arc (hi) + longest control path H.O -> G.p (hi, every LUT arc, wire and delay-line hop) <= rst_width + w_rst(G.I_rst).lo; model units: rst held >= 23 (D + W + 1) + W steps on gcd_hw (maxRank = 21)",
    forms=[form([[wire("rst_src", "H.I_rst", "w_rst(H).hi"), sp("H", "I_rst", "rst"), lut("H", "I_rst", "O6"),
                  line("ctl_path", "any", "longest", "H.O6 -> stateless control LUTs / delay lines -> G.p, every hop (hi)", "rank"), sp("G", "p", "control")]],
                [[env("rst_width", "rst_src high, min", "rst_width"), wire("rst_src", "G.I_rst", "w_rst(G).lo"), sp("G", "I_rst", "rst")]],
                launch="rst_src rise", note="per (H, G.p); gcd_hw's longest path is uselect1's 94-element bd_delay_gated (+ uor, fork wire, join pin)")],
    refers_to=["bd_pipe.rst_lines"],
    lean=[L(RC, "reset_binary", "sufficient", note="every bounded GMW run, any power-up, rst held on (0, E]: control nodes of rank < m at reset values on [(m+1)(D+W+1), E]"),
          L(RC, "reset_ternary", "sufficient", note="Kleene from all-X"), L(RC, "ResetSpec", "definition", note="H_IN, H_LOCAL"),
          L(RG, "gcd_reset_binary", "sufficient", note="gcd_hw instance: reset values on [23(D+W+1), E]"), L(RG, "gcd_reset_ternary", "sufficient"),
          L(RG, "gcd_reset_release", "sufficient", note="composition: rst = 1 on (0, E] with E >= 23(D+W+1) + W, anything after: reset values hold until a frontier controller moves"),
          L(RC, "rig_reset_binary", "instance", note="35-node rig skeleton"), L(RG, "neg_unguarded", "counter_trace", note="negative control: an OR steer lets the never-reset latch's X into control")],
    exactness="sufficient",
    exactness_note="P6 / Rst, Rst2: sufficient (the GMW bound by rank). Rst2's whole-network ranks count delay elements one LUT at a time (maxRank = 21, 23 Jacobi steps; Rst's scan reported 4 with lines collapsed). A tightened GCD_DUT_PARAMS build changes chain lengths and needs a regeneration. " + RST_X,
    site_pins={"needed": True, "roles": ["H.I_rst hi", "G.p hi", "G.I_rst lo"]},
    rule={"rule": "none", "verdict": "none", "detail": "UNCHECKED"}, corner=CORNER_1C, check_scope="route_plus_env")
add(id="design.rst_release_skew", cell="design", also_applies_to=["per frontier F (gcd_hw: ulink_n1__1, ulink_n36__0/1/2, ulink_n68__0/1, ulink_n94__0/1, ulink_n155__0/1) and per reset cell G with a pin reachable from F; evaluate only for G in the first wave (ucond_br9/10/11_j)"],
    catalogue_row="Rst section 3.3 (H_RST_SKEW)",
    obligation="H_RST_SKEW: each reset cell's rst pin releases before the earliest frontier event can reach any of its pins (sufficient against H_NO_RETURN, the lost-event hazard after a frontier fires)",
    inequality="w_rst(G.I_rst).hi + SP <= w_rst(F.I_rst).lo + SP + F arc I3 -> O6 (lo) + shortest path F.O -> G.p (lo)",
    forms=[form([[wire("rst_src", "G.I_rst", "w_rst(G).hi"), sp("G", "I_rst", "rst")]],
                [[wire("rst_src", "F.I3", "w_rst(F).lo"), sp("F", "I3", "rst"), lut("F", "I3", "O6"),
                  line("ctl_path", "rise", "shortest", "F.O6 -> G.p, every hop (lo); first wave: ulink_n1__1.O -> ucmpi0.uor -> 30-hop gated line -> ufork2 -> join pins"), sp("G", "p", "control")]],
                launch="rst_src fall", note="H_RST_SKEW, per (F, G)")],
    lean=[L(RC, "first_change", "sufficient", note="min-delay potentials bound the first event (H_CAUSAL per node, from loop_causal / win_causal; not assembled for a network)"),
          L(RC, "released_quiet", "sufficient", note="H_RST_SKEW gives the simultaneous-release state"),
          L(RG, "gcd_release_quiet", "not_necessary", note="whole network, any per-pin release skew: no control node moves before a frontier controller does"),
          L(RC, "c2n_race_holdK", "lemma"), L(RC, "c2_race_holdK", "lemma"), L(RC, "uj_race_holdK", "lemma"), L(RC, "race_movesK", "lemma", note="a first-wave cell goes x during the race; its forced excitation erases the transient")],
    exactness="sufficient",
    exactness_note="P6 / Rst2: gcd_release_quiet (kernel-checked on the imported gcd_hw network) makes release skew UNNECESSARY for 'nothing moves before a frontier link fires': it holds for every skew. What H_RST_SKEW still buys is the step after: a frontier fires while some cell's rst is still high, and that cell could miss a complete input pulse (H_NO_RETURN, argued, not proved). So this form is only sufficient, and a checker need evaluate it only for first-wave cells; for the 1-LUT paths to fork ack trees (likely to fail) the race lemmas make it harmless. " + RST_X,
    site_pins={"needed": True, "roles": ["G.I_rst hi", "F.I3 lo", "G.p lo"]},
    rule={"rule": "none", "verdict": "none", "detail": "UNCHECKED"}, corner=CORNER_1C, check_scope="route_plus_env")
add(id="gcd_rig.token_static", cell="gcd_rig", also_applies_to=["the 10 frontier link controllers of gcd_hw: ulink_n1__1 (rig token, uenv1), ulink_n155__0/1 (usource13), ulink_n36__0/1/2 (usource3), ulink_n68__0/1 (usource5), ulink_n94__0/1 (usource7)", "replaces PipePerPin H_RST_SEL(c) / PipeTimedN H_RST_EARLY for these stages"],
    catalogue_row="Rst section 3.4",
    obligation="the request pin of each frontier controller F carries 1 from before rst_src falls (minus w_rst(F).lo) until F's first rise plus its loop bound; then F fires once, within dlmax of its own release, with no ordering between its rst and request selects",
    inequality="structural: holds by construction (env_c forced 1 during reset and held by bd_c2n_set; bd_src req = ~ack with ack = 0)", forms=[],
    lean=[L(RC, "c2n_frontier", "sufficient", note="H_TOKEN, H_STAY: 0 while rst is high at its pin, 1 from r + dlmax, fires once"),
          L(RC, "c2n_set_reset", "lemma", note="uenv1 holds the token through release"),
          L(RG, "gcd_frontier", "instance", note="exactly these 10 control nodes are excited at the simultaneous-release state"),
          L(RG, "gcd_frontier_fire", "instance", note="each is a bd_c2n with its request at 1 during reset (uenv1 or a usource)"),
          L(RG, "gcd_reset_ones", "instance", note="the 17 reset-1 nodes: rst, 9 arbiter q, 4 bd_src requests, uenv1, both upsnk elements (p_end consumed during reset)"),
          L(RG, "gcd_links_empty", "instance", note="every bd_c2n resets to 0: all links empty"), L(RC, "rig_frontier", "instance", note="35-node rig")],
    exactness="sufficient",
    exactness_note="P6 / Rst, Rst2: a property of the netlist, decided on the imported elaborated netlist. PipePerPin's H_RST_SEL(c) with rho 0 = R would demand ps.hi <= pr.lo, a spurious per-pin band requirement when the request has been static since power-up; c2n_frontier is the right statement for frontier stages. The kernel at release holds the rig token on a/b/start plus the four sources' standing tokens. " + RST_X,
    site_pins={"needed": False, "roles": []}, rule={"rule": "none", "verdict": "none", "detail": "structural"}, corner=CORNER_NA, check_scope="structural")
add(id="gcd_rig.idx_setup", cell="gcd_rig", also_applies_to=["per bit of a_v, b_v (and g_v at the compare): the frontier latch of ulink_n1__1 and the direct a_data / b_data readers"], catalogue_row="Rst section 3.5",
    obligation="the vector index, moved by an hk clock edge before reset, has settled at the frontier latch's d pin and the direct readers before the frontier controller's first rise opens the latch",
    inequality="tCO + vector decode LUTs + route to latch d / readers (hi) + setup <= rst_width + w_rst(F).lo + F arc I3 -> O6 (lo), from the hk edge that moves idx",
    forms=[form([[param("tCO", "FDRE clock-to-out (idx register)", "tCO"), env("vec_path", "vector decode LUTs + route to ulink_n1__1's latch d pin and the a_data/b_data readers, hi", "vec"), env("su", "latch / reader setup", "su")]],
                [[env("rst_width", "rst_src high after the idx edge, min (16 hk cycles)", "rst_width"), wire("rst_src", "F.I3", "w_rst(F).lo"), sp("F", "I3", "rst"), lut("F", "I3", "O6")]],
                launch="the hk-clock edge that moves idx")],
    lean=[L(RC, "c2n_frontier", "context", note="F rises within dlmax of its own release"), L(RC, "latch_write", "context", note="a transparent latch with definite d is definite whatever its X feedback"),
          L("Cells/Bundling", "capture", "context", note="the phase-0 capture (Ton = the first enable rise)")],
    status="unproved", exactness="unproved",
    exactness_note="P6 / Rst: stated in EndpointOK form, not composed as one theorem (the clocked idx register is outside every Lean model). Trivially met: 16 hk cycles of reset. Note B-reset-contract.md section 7.3: the stale ok+err pairs are more consistent with the ASSERTION edge (idx and rst_sr load on the same win_edge_d edge) than with a result in flight after release; a hypothesis from reading the RTL, not a measurement. " + RST_X,
    site_pins={"needed": True, "roles": ["F.I3 lo"]}, rule={"rule": "none", "verdict": "none", "detail": "UNCHECKED"}, corner=CORNER_1C, check_scope="environment")

# --------------------------------------------------------------- probe P5: references added to existing entries
BYID = {e["id"]: e for e in E}
def more(i, refs=(), note=None, also=None, evidence=None):
    e = BYID[i]
    e["lean"] = e["lean"] + list(refs)
    if note:
        e["exactness_note"] = (e.get("exactness_note", "") + " " + note).strip()
    if also:
        e["also_applies_to"] = e.get("also_applies_to", []) + also
    if evidence:
        e["evidence"] = (e.get("evidence", "") + "; " + evidence).strip("; ")

for i in ("bd_mux.bundled_s_setup", "bd_mux.bundled_s_hold"):
    BYID[i]["exactness_note"] = BYID[i]["exactness_note"].replace(
        "NOT covered: the composition with the rest of the mux (mux_ok is still untimed).",
        "P5: now also a premise (pin form, MuxEnv.H_S_PIN0/1) of the timed whole-cell theorem OpsTimedMux.mux_ok; its static FIFO-wire form is the steer's (OpsTimed.steer_s_pin_of_wire).")
    more(i, [L("Cells/OpsTimedMux", "mux_ok", "uses", note="MuxEnv.H_S_PIN0/1"), L("Cells/OpsTimedMux", "MuxEnv", "definition")])
for i, fld in (("bd_mux.uxa_rtz_env", "S_XA_RTZ"), ("bd_mux.uya_rtz_env", "S_YA_RTZ")):
    more(i, [L("Cells/OpsTimedMux", "mux_timing_of_static", "sufficient", note=f"MuxStatic.{fld}: Wz?.hi + L?a.hi + w?ah <= Wz?.lo + Kc + Kz, the same arc set, inside the whole-cell theorem (mux_ok)"),
             L("Cells/OpsTimedMux", "MuxStatic", "definition")],
         note=f"P5 (B-ops-timed.md): {fld} of OpsTimedMux.MuxStatic is this entry with exactly MuxRtzTimed's arc set, now discharging H_DEP_XA/YA of the whole-cell theorem.")
more("bd_mux.bundled_z", [L("Cells/OpsTimed2", "mux_data_ok", "sufficient", note="whole-cell value theorem; its static obligations are bd_mux.bundled_z_s and bd_mux.bundled_z_data"),
                          L("Cells/OpsTimed2", "mux_value_ok_static", "sufficient")],
     note="P5 (B-ops-timed2.md): refined by bd_mux.bundled_z_s (launch at the s driver; this form presumes s settled at the join edge) and bd_mux.bundled_z_data (client data, missing before). Hold half: no inequality beyond the sender protocol.")
more("bd_delay[FASTFALL].flush_per_stage",
     [L("Cells/OpsTimed2", "ff_tok", "sufficient", note="FIFO-arc version: every stage of an FFLine is a clean four-phase trace under H_FLUSH_STAGE (event form)"),
      L("Cells/OpsTimed2", "flush_stage_static", "sufficient", note="one-step static form f + H.hi <= e(2k+2) + Tp.lo"),
      L("Cells/OpsTimed2", "mux_ok_fastfall", "sufficient", note="composed with bd_mux: z_req one clean transaction per control token through a FASTFALL line")],
     note="P5 (B-ops-timed2.md (c)): restated for FIFO arcs and composed with the mux; no witness for ff_tok / mux_ok_fastfall, fall bound unrolled one step only.")
PW = "Cells/PipeWitness"
more("bd_pipe.sel_order", [L(PW, "witness", "non_vacuity", note="W3.witness: GatesP/EnvP/TimingP/DataP jointly, every N >= 1, feedback on the SLOWEST site pin (3 vs 1/2), H_SELORD margin 5"),
                           L(PW, "sel_lead", "non_vacuity", note="W3.sel_lead: ack select leads the request select by 5 / 2 ticks"),
                           L(PW, "hold_rise", "non_vacuity", note="W2/W3.hold_rise: the C-element holds through its feedback (flipping the feedback select flips the excitation)"),
                           L(PW, "hold_fall", "non_vacuity")],
     evidence="B-pipe-witness.md W3: mutation feedback pin 9 breaks H_SELORD and the witness's gate relation together (scratch mutation, not a theorem)")
more("bd_pipe.lat_lumped", [L(PW, "witness", "non_vacuity", note="W1.witness / W2.witness: non-tie runs (Ain leads Rin by 4 ticks), W2 with DACK = 2 and distinct rise/fall latencies"),
                            L(PW, "no_tie", "non_vacuity", note="W1.no_tie"), L(PW, "hold", "non_vacuity", note="W1.hold: feedback decides the output"),
                            L(PW, "ack_latency", "non_vacuity", note="W2.ack_latency")])
more("bd_pipe.boundary_I", [L(PW, "witness", "non_vacuity", note="W1.witness: non-unit data path (D pin 3 ticks in [2,4], enable 2 in [1,3], own output 2 in [1,2]) jointly with the control"),
                            L(PW, "latch_hold", "non_vacuity", note="W1/W3.latch_hold: enable closed, D already shows token k+1, output still token k"),
                            L(PW, "latchT", "lemma", note="real ODD INIT as a transport LUT inside the Kleene windows")])
more("bd_pipe.boundary_H", [L(PW, "witness", "non_vacuity", note="W2.witness: H_H with the DACK credit aslow = 4 (real FASTRISE chain)"),
                            L(PW, "chain2", "lemma", note="the DACK = 2 FASTRISE chain is the OR of its FIFO paths (fastrise_or), discharging GatesN.H_ACK_LINE")])
more("bd_pipe.rst_lines", [L(PW, "witness", "non_vacuity", note="W3.witness: H_RST_SEL and H_FLUSH tight (equalities)")],
     evidence="B-pipe-witness.md W3 mutation M3 (feedback site pin 7): only H_RST_SEL (b) fails, so that startup obligation is genuine (scratch mutation, not a theorem)")
more("bd_pipe.output", [L(PW, "witness", "non_vacuity", note="W1/W2/W3.witness apply pipe_forward: every token delivered")])
more("bd_delay[FASTRISE].ack_flush", [L(PW, "chain2", "non_vacuity", note="real FASTRISE chain (BUF 2'h2, FR_SIDE 4'hE) with DACK = 2 in a joint pipe witness (W2, W3)")])
# --------------------------------------------------------------- probe P6: Lt4, Mn, Rst, Rst2 references added to existing entries
for cell, pre in (("bd_c2", "c2"), ("bd_c2n", "c2n"), ("bd_c3", "c3"), ("bd_c4", "c4")):
    more(f"{cell}.reset_width", [L(RC, f"{pre}_rstB", "function_equality", note="rst = 1 forces the reset value for every Boolean value of every other pin"),
                                 L(RC, f"{pre}_rstK", "lemma", note="the same in Kleene semantics: holds from all-X power-up")],
         note="P6 (B-reset-contract.md): the per-instance form of design.rst_hold (which adds w_rst and the rst site pin); forcing lemmas on the real INIT." + (" bd_c2n now has a general theorem (ResetContract.c2n_reset); c_reset_s1 is an instance." if cell == "bd_c2n" else ""))
for i, lem, Wz, Wj, ent in (("bd_mux.uxa_rtz_env", "mux_rtz_of_J", "Wzx", "W0x", "S_XA_J (1)"), ("bd_mux.uya_rtz_env", "mux_rtz_y_of_J", "Wzy", "W1y", "S_YA_J (1)")):
    more(i, OX(lem, "redundancy", f"MuxStatic.S_*_RTZ follows from {ent} (bd_mux.uxa_join_latency) whenever {Wz}.hi - {Wz}.lo <= {Wj}.hi - {Wj}.lo"),
         note=f"P6 / {LT4} {lem}: REDUNDANT, and the checker may skip it, when the z_ack wire's spread is at most the join wire's, ({Wz}.hi - {Wz}.lo) <= ({Wj}.hi - {Wj}.lo), given bd_mux.uxa_join_latency {ent}; it can bind only through the z_ack wire's rise/fall delay spread. Otherwise keep it: plausibly exact (the next token's z_ack rise is not causally after x_ack's fall); counter-run designed (time-varying Wzx), not built.")
FW = [L(RC, "latch_stays_x", "context", note="bd_latch is not reset: opaque with X feedback it stays X"), L(RC, "latch_holdB", "lemma", note="binary: holds its old value (the previous window's data on silicon)"),
      L(RC, "latch_write", "lemma", note="the first write: transparent with definite d is definite whatever its X feedback"),
      L(RC, "latch2_write_lo", "lemma"), L(RC, "latch2_write_hi", "lemma")]
FWN = "P6 / Rst (B-reset-contract.md section 4, 'bd_latch.first_write', no separate id): the never-reset latch's first write after release is the PHASE-0 instance of this entry (NRBW (b): every guard's first rise after c_L's first rise plus d -> q and the cone's settle). Reset adds no inequality; NRBW (a), the guard, is the hypotheses_not_inequalities row NRBW."
for key in ("bd_latch[odd]", "bd_latch[pair.O5]", "bd_latch[pair.O6]"):
    more(f"{key}.setup_data", FW, note=FWN)
more("bd_pipe.boundary_I", FW, note=FWN)
more("bd_pipe.data_lead", [], note=FWN)
more("bd_pipe.rst_lines", [L(RC, "c2n_frontier", "sufficient", note="frontier stages: no select ordering needed")],
     note="P6 / Rst: at a FRONTIER stage (request 1 throughout reset: the 10 gcd_hw links in gcd_rig.token_static) H_RST_SEL(c) with rho 0 = R becomes ps.hi <= pr.lo, a spurious requirement; gcd_rig.token_static (c2n_frontier) replaces it there. Design level: design.rst_flush.")
for e in E:
    if e["cell"] == "bd_arbiter" and (e["id"].startswith("bd_arbiter.rt") or e["id"].startswith("bd_arbiter.a0_fork")):
        e["also_applies_to"] = e.get("also_applies_to", []) + ["bdc_amerge2_0.uarb (7 in gcd_hw), bdc_amerge3_0.uarb2 (1); bdc_amerge3_0.uarb1 with smin made explicit: bdc_amerge3.rt2_cascade_* (B-amerge.md, B-amerge-timed.md)"]

# --------------------------------------------------------------- probe Blt: bd_steer exact per-pin rows; bd_fork / bd_join delegation
LGS = "Cells/LibGapSteer"
for side in ("setup", "hold"):
    e = BYID[f"bd_steer.bundled_s_{side}"]
    f0 = e["forms"][0]
    if side == "setup":
        e["obligation"] = ("S_S_SETUP_PIN (LibGapSteer H_SETUP_PIN, per output O5 and O6): s, settled at its driver at S0, "
                           "is read by output O_b no later than req's rise at its driver (R) is read by O_b")
        e["inequality"] = "per output b in {O5, O6}: S0 + ps_b.hi <= R + pr_b.lo; ps_b = s.drv -> u.I1 wire + SP[I1] + arc(I1 -> O_b); pr_b = req -> u.I0 wire + SP[I0] + arc(I0 -> O_b)"
        f0["data_paths"][0][2]["note"] = "per-pin arc I1 -> O5 resp. O6 (in the Lean model: part of ps_b)"
        f0["data_paths"][0][0]["lean_sym"] = "ps_b.hi"
        f0["request_paths"][0][1]["lean_sym"] = "pr_b.lo"
        f0["request_paths"][0][3]["note"] = "per-pin arc I0 -> O5 resp. O6 (in the Lean model: part of pr_b)"
    else:
        e["obligation"] = ("S_S_HOLD_PIN (LibGapSteer H_HOLD_PIN, per output O5 and O6): req's fall at its driver (F) is read by "
                           "O_b no later than s's next change at its driver (S1) is read by O_b")
        e["inequality"] = "per output b in {O5, O6}: F + pr_b.hi <= S1 + ps_b.lo (with bd_ctl's contract S1 - F = Hs, a round trip: OpsTimed2.steer_hold_of_ackfall)"
        f0["data_paths"][0][2]["note"] = "per-pin arc I0 -> O5 resp. O6 (in the Lean model: part of pr_b)"
        f0["data_paths"][0][0]["lean_sym"] = "pr_b.hi"
        f0["request_paths"][0][1]["lean_sym"] = "ps_b.lo"
        f0["request_paths"][0][3]["note"] = "per-pin arc I1 -> O5 resp. O6 (in the Lean model: part of ps_b)"
    e["lean"] = [
        L(LGS, "steer_box_exact", "exact", note="iff over the delay box, for every read-map pair inside it and every s stable on [S0,S1) (arbitrary outside): SpecOK <-> setup AND hold"),
        L(LGS, "steer_pin_exact", "exact", note="iff for fixed per-pin delays (apply per corner realisation)"),
        L(LGS, "steer_pin_ok", "sufficient", note="any (non-monotone) per-pin read maps"),
        L(LGS, "steer_both", "sufficient", note="both outputs, four inequalities"),
        L(LGS, "steer_tokens", "sufficient", note="any number of tokens, per-token windows"),
        L(LGS, "steer_pin_ok_K", "sufficient", note="Kleene: s may be X outside its window; outputs stay definite"),
        L(LGS, "setup_needed", "necessary", note="violated setup: SpecOK fails at R + dr on either output"),
        L(LGS, "hold_needed", "necessary", note="violated hold: SpecOK fails at F - 1 + dr"),
        L(LGS, "spurious_token", "counter_trace", note="setup short by 100 ps: the UNSELECTED branch O5 rises (spurious token)"),
        L(LGS, "late_hold_glitch", "counter_trace", note="hold violated: unselected branch high at the end of the pulse"),
        L(LGS, "witness_run", "non_vacuity", note="selected O6 rises and falls, O5 stays low"),
        L(LGS, "witness_hyps", "non_vacuity"),
        L(LGS, "Rd", "definition", note="H_PIN_READ"),
        L(LGS, "SpecOK", "definition", note="= OpsSteer's lut field for one token"),
    ] + [r for r in e["lean"] if r["name"] in ("steer_req0", "steer_req1", "steer_ok", "steer_op", "steer_hold_of_ackfall", "steer_excl_K")]
    e["exactness"] = "exact"
    e["exactness_note"] = ("Blt (formal/notes/B-lib-gap.md): exact (iff) over the delay box with PER-PIN LUT arcs (H_PIN_READ: each output reads each pin "
        "through its own window; read maps need not be monotone), the select adversarial outside [S0,S1). Supersedes the lumped-arc sufficient "
        "form of OpsTimed2 for this obligation; necessity is per output (either output fails: unselected = spurious token, selected = late/runt). "
        "Box necessity assumes the two pins' delays independent; under a correlated corner model use steer_pin_exact per realisation. "
        "Not covered: mid-rail select inside the mux tree (H_KLEENE_LUT), the uack OR (steer_back, H_ACK_SKEW).")
    e["status"] = "proved"

FD = "Cells/ForkData"
FORK_ALSO = ["bd_fork N=2..6 in gcd_hw (52 instances incl. the 8 control_merge `_f` forks; 139 branches): 53 branches end at bd_link/bd_pipe (bd_fork.branch_data), 59 at bd_join (data obligation moves to the join's consumer: bd_steer.bundled_s_setup / compute rule A), 12 at a nested bd_fork (pass through to the leaf), 6 at bd_snk and 9 control-only (no data)"]
for cell, n, what, refs in (
        ("bd_fork", 52, "request broadcast as wires, acks joined by bd_ctree",
         ["bd_fork.branch_data", "bd_c2.env_latency", "bd_c3.env_latency", "bd_c4.env_latency", "bd_ctree.node_fork", "bd_ctree.ack_wait"]),
        ("bd_join", 38, "requests joined by bd_ctree, ack broadcast as wires",
         ["bd_c2.env_latency", "bd_c3.env_latency", "bd_c4.env_latency", "bd_ctree.node_fork", "bd_ctree.ack_wait",
          "bd_latch[odd].setup_data", "bd_latch[pair.O5].setup_data", "bd_latch[pair.O6].setup_data", "bd_steer.bundled_s_setup"])):
    fwd = ("its forward data obligation is bd_fork.branch_data (per branch, at the consumer latch; Bfd); its ack side is the C-tree rows"
           if cell == "bd_fork" else
           "its data passes through unchanged, so the data obligation is the consumer's (bd_steer.bundled_s_setup, a latch setup_data with the join's wires on both paths, or the compute unit's rule A)")
    add(id=f"{cell}.delegated", cell=cell, catalogue_row="none (Blt coverage audit)",
        obligation=f"{cell} has no LUT of its own ({what}); {fwd}",
        inequality="see refers_to, with the fork/join wires on the consumer's data and request paths",
        forms=[], refers_to=refs,
        lean=[L("Cells/CTreeTimed", "tree_four_phase", "sufficient")] + ([L(FD, "fork_capture", "sufficient", note="data side, every branch (bd_fork.branch_data)")] if cell == "bd_fork" else []),
        exactness="see_refers_to",
        site_pins={"needed": True, "roles": ["consumer pins, as in the referred rows"]},
        rule={"rule": "none", "verdict": "none", "detail": "covered by the referred rows' rules (A/I/E) when they walk through the fork/join wires"},
        corner=CORNER_1C, check_scope="route_plus_env",
        evidence=f"{n} instances in gcd_hw (B-gcd-cells.md); no route measured")

# --------------------------------------------------------------- probe Bfd: bd_fork branch data (C14), bdc_amerge index conjunction (C11)
FDATA = [env("Td", "launch -> last change of the shared data net at its driver (producer: its latch Q / amerge index LUT / compute output), max", "Td"),
         wire("x_data.drv", "consumer.lat.u.I0", "dhi", note="THIS branch's route of the shared bus (per bit)"),
         sp("consumer.lat.u", "I0", "data"), lut("consumer.lat.u", "I0", "O6|O5", "dhi"),
         fbw("consumer.lat.u", "O6|O5", "I2|I4", "fhi"), sp("consumer.lat.u", "I2|I4", "feedback", "in fhi"),
         lut("consumer.lat.u", "I2|I4", "O6|O5", "fhi", note="the arc rule I omits (bd_latch[*].setup_data missing_term)")]
FREQ_EDGE = [env("Tr", "launch -> producer request edge at its driver, min", "Tr"),
             wire("x_req.drv", "consumer.ctl.u.u.I0", "rlo", note="the fork's req fan-out wire to THIS branch"),
             sp("consumer.ctl.u.u", "I0", "req_in"), lut("consumer.ctl.u.u", "I0", "O6", "rlo"),
             wire("consumer.ctl.u.u.O6", "consumer.lat.u.I1", "elo"), sp("consumer.lat.u", "I1", "enable"), lut("consumer.lat.u", "I1", "O6|O5", "elo")]
FREQ_W = FREQ_EDGE[:4] + [env("wlo", "consumer node rise -> node fall, min: node -> DACK (FASTRISE rise) -> fork C-tree -> producer ack pin -> producer req fall -> fork wire -> node fall (rule I's t_ack + t_fall)", "wlo")] + FREQ_EDGE[4:]
FD_EV = "none: no routed number (Bfd; gcd_hw re-emitted, consumer census in Bfd's scratch, B-fork-data.md section 1)"
add(id="bd_fork.branch_data", cell="bd_fork", also_applies_to=FORK_ALSO, catalogue_row="C14 (H_FORK_DATA, C-8f)",
    obligation="H_FORK_DATA_W: per branch, the shared data bus is through the branch's latch and once round its loop before the branch's enable FALL can arrive (bd_latch.setup_data with the launch at the fork's producer)",
    inequality="Td + dhi + fhi <= Tr + rlo + wlo + elo; side conditions H_FORK_PULSE ehi + fhi <= wlo + elo (= bd_latch.setup_pulse) and H_FORK_HOLD ehi <= alo + dlo (= bd_latch.hold with the fork C-tree on the ack path)",
    forms=[form([FDATA], [FREQ_W], launch="producer node rise (the event that launches both the data and the request)")],
    lean=[L(FD, "branch_capture", "sufficient"), L(FD, "fork_capture", "sufficient", note="all branches, one shared data net"),
          L(FD, "H_FORK_DATA_W", "definition"), L(FD, "BrRun", "definition"),
          L(FD, "fork_data_needed", "counter_trace", note="parametric: every branch with point windows violating by exactly 1 ps at the minimal environment latches the stale value (real odd-bit INIT), q = !v at Toff + elo and every loop period after"),
          L(FD, "fork_data_needed_num", "instance", note="the counter-trace hypotheses are satisfiable"),
          L(FD, "fork_data_good", "non_vacuity", note="parametric witness run of every hypothesis"),
          L("Cells/Bundling", "capture", "lemma")],
    exactness="sufficient+necessary",
    exactness_note="Bfd (B-fork-data.md): sufficient for every trace of the window gate relation; necessary by one ps at the minimal environment (node rises at Tr + rlo, falls wlo later), point windows. Odd-bit LUT6 only; the LUT6_2 pair bits use pair_o5_latch/pair_o6_latch in branch_capture (sufficiency) but the counter-trace is not built for them. No routed number.",
    site_pins={"needed": True, "roles": ["consumer.lat.u.I0 (data), I2/I4 (feedback) hi", "consumer.ctl req_in pin, consumer.lat.u.I1 (enable) lo"]},
    rule={"rule": "I", "source": "cells/verify/tighten.py rule I (reading the code, not a run)", "verdict": "missing_term",
          "detail": "rule I audits every controller whose data enters from a link stage that also requests it, through any combinational path, so a link->fork->link branch is covered, with the closing path t_rise + t_ack + t_fall (the wlo credit). It omits the latch's feedback-pin arc (as for bd_latch.setup_data). Branches whose producer is not a bd_link stage (amerge index, compute outputs, steer/mux outputs, environment) print 'not audited'; for those, rule A (uor-audited cells) covers the producer's own cone but not the fork branch's route skew. UNCONFIRMED on a routed tighten log."},
    corner=CORNER_1C, check_scope="route_plus_env", evidence=FD_EV)
add(id="bd_fork.branch_data_edge", cell="bd_fork", also_applies_to=FORK_ALSO + ["edge-sampling consumers (bd_link_dc, BRAM clock) where it is the relevant form"], catalogue_row="C14 (H_FORK_DATA, C-8f, as written)",
    obligation="H_FORK_DATA as C-8f states it: per branch, data_hi at the consumer's latch (through D and once round the loop) <= req_lo (earliest the branch's request can open the latch)",
    inequality="Td + dhi + fhi <= Tr + rlo + elo",
    forms=[form([FDATA], [FREQ_EDGE], launch="producer node rise")],
    lean=[L(FD, "H_FORK_DATA", "definition"), L(FD, "edge_implies_W", "sufficient", note="implies bd_fork.branch_data"),
          L(FD, "edge_form_not_needed", "not_necessary", note="violated by 850 ps, H_FORK_DATA_W holds, the latch captures")],
    exactness="sufficient",
    exactness_note="Bfd: sufficient (implies H_FORK_DATA_W), NOT necessary at a Muller bd_link/bd_pipe consumer (every latch consumer in gcd_hw: BD_LINK_DC not defined). A route checker should check bd_fork.branch_data instead; this form is the conservative screen.",
    site_pins={"needed": True, "roles": ["as bd_fork.branch_data"]},
    rule={"rule": "none", "verdict": "none", "detail": "no rule states it; rule I checks the weaker exact form"},
    corner=CORNER_1C, check_scope="route_plus_env", evidence=FD_EV)
AMT = "Cells/AMergeTimed"
AM_CAVEAT = ("CAVEAT (Bfd, B-fork-data.md section 3): Cm2's consumer is edge-sampling (index settled su before Zr), and the necessity above holds only at such a consumer. "
             "Every index consumer in gcd_hw is a Muller bd_link/bd_pipe behind the _f fork, which closes a whole handshake after Zr: the counter-traces show a stale index at the request edge, not a stale latched value. "
             "At those consumers the exact condition is bd_fork.branch_data (H_FORK_DATA_W, with Td = the index settle time), and this entry is sufficient only.")
add(id="bdc_amerge.idx_bundle", cell="bdc_amerge", also_applies_to=["bdc_amerge2_0 (7 in gcd_hw)", "the per-race entries bdc_amerge.bundled_idx_grant, .bundled_idx_ack, .bundled_idx_ack_g, .bundled_idx_grant_fall, .idx_ack_fork (this entry is their conjunction)"],
    catalogue_row="C11 (H_AMERGE_IDX)",
    obligation="H_AMERGE_IDX: index = g2 | in1_ack names the token's owner at the consumer su before that token's request (R0 -> uor -> bd_delay_gated -> z_req -> fork _f -> consumer) does, in all three races (new owner's grant; previous owner's ack and grant fall; the in1_ack fork into the index LUT). The data-mux leg is empty in gcd_hw (width 0: in_k_data = 1'b0, z_data unconnected)",
    inequality="BidxA /\\ BidxB (ack, gack, grant) /\\ IdxAckFork, see the per-race entries; wid = index LUT O6 -> fork _f data wire -> consumer latch D -> loop (max), dz = R0 -> uor -> udly rise -> z_req -> fork _f req wire -> consumer node -> latch EN (min)",
    forms=[form([[env("per_race", "see bdc_amerge.bundled_idx_grant / bundled_idx_ack / bundled_idx_ack_g / bundled_idx_grant_fall / idx_ack_fork")]], [[env("per_race", "as data side")]], launch="per race")],
    refers_to=["bdc_amerge.bundled_idx_grant", "bdc_amerge.bundled_idx_ack", "bdc_amerge.bundled_idx_ack_g", "bdc_amerge.bundled_idx_grant_fall", "bdc_amerge.idx_ack_fork", "bd_fork.branch_data"],
    lean=[L(FD, "H_AMERGE_IDX", "definition", note="namespace Formal.Cells.ForkData.AMerge"), L(FD, "amerge_idx_sufficient", "sufficient", note="needs the arbiter's RT2b"),
          L(FD, "amerge_idx_necessary", "counter_trace", note="exact legs at an edge-sampling consumer: BidxA (with A0Fork, H_Z_IN_SRV), BidxB.ack (xr = xf), IdxAckFork (minimal client)"),
          L(FD, "amerge_idx_nonvacuous", "non_vacuity", note="SLOW_MAX DELAY = 12, cmin = 248; runs in AMergeTimedW.nonvacuous_slow"),
          L(FD, "amerge_data_const", "lemma", note="data-mux leg constant in gcd_hw"),
          L(AMT, "bidx_new_owner", "sufficient"), L(AMT, "bidx_old_owner", "sufficient"), L(AMT, "idx_ack_fork_hold", "sufficient")],
    exactness="sufficient+necessary_at_boundary",
    exactness_note="Bfd: the conjunction of Cm2's legs; necessary leg by leg at the minimal request path / minimal client EXCEPT BidxB.gack (sufficient only) and BidxB.grant (own counter-trace). " + AM_CAVEAT,
    site_pins={"needed": True, "roles": ["as the per-race entries"]},
    rule={"rule": "A", "verdict": "different_condition", "detail": "as bdc_amerge.bundled_idx_grant; the consumer side (fork _f branch to a link) is rule I's when the producer is a link, which the amerge is not: 'not audited'"},
    corner=CORNER_1C, check_scope="route_plus_env", evidence=FD_EV)
BYID = {e["id"]: e for e in E}
for i in ("bdc_amerge.bundled_idx_grant", "bdc_amerge.bundled_idx_ack", "bdc_amerge.bundled_idx_ack_g", "bdc_amerge.bundled_idx_grant_fall", "bdc_amerge.idx_ack_fork", "bdc_amerge3.bundled_idx0_grant"):
    if i in BYID:
        more(i, [L(FD, "amerge_idx_sufficient", "sufficient", note="the conjunction bdc_amerge.idx_bundle")] if i.startswith("bdc_amerge.") else [], note=AM_CAVEAT)
        BYID[i]["necessity_scope"] = "edge_sampling_consumer_only"

# --------------------------------------------------------------- probe Bmx: bd_mux select setup/hold exact per join (LibGapMux)
LGM = "Cells/LibGapMux"
MUX_KEEP = ("mux_needs_bundled_s", "mux_needs_bundled_s_hazard", "mux_weak_broad_fails", "steer_s_x_while_req",
            "uj0_unsel_low_timed", "uj1_unsel_low_timed", "j0_sel_is_c2", "j1_sel_is_c2", "j0_s_x_hazard", "mux_ok", "MuxEnv")
for side in ("setup", "hold"):
    e = BYID[f"bd_mux.bundled_s_{side}"]
    e["also_applies_to"] = []   # bdc_muxn has other join INITs: NOT covered by LibGapMux (its own rows are bdc_muxn.s_setup / s_hold)
    fm = e["forms"][0]
    if side == "setup":
        e["obligation"] = ("S_MUX_S_SETUP_PIN (LibGapMux H_SETUP_PIN, per join uj0 and uj1): s, settled at its driver at S0, "
                           "is read by the join (pin I2 -> O6) no later than ctl_req's rise at its driver (Cr) is read by it (pin I1 -> O6)")
        e["inequality"] = ("per join k in {uj0, uj1}: S0 + ps_k.hi <= Cr + pc_k.lo; ps_k = s.drv -> uk.I2 wire + SP[I2] + arc(I2 -> O6); "
                           "pc_k = ctl_req.drv -> uk.I1 wire + SP[I1] + arc(I1 -> O6). The request pin I0 and the feedback pin I3 do NOT enter.")
        for p in fm["data_paths"]: p[0]["lean_sym"] = "S0"; p[1]["lean_sym"] = "ps_k.hi"; p[3]["lean_sym"] = "ps_k.hi"
        for p in fm["request_paths"]: p[0]["lean_sym"] = "Cr"; p[1]["lean_sym"] = "pc_k.lo"; p[3]["lean_sym"] = "pc_k.lo"
        fm["note"] = "Lean LibGapMux.join_box_exact: S0 + Shi <= Cr + Clo (per join); same shape as the old H_BUNDLED_S_SETUP_T Ts + shi <= Tc + clo"
    else:
        e["obligation"] = ("S_MUX_S_HOLD_PIN (LibGapMux H_HOLD_PIN, per join uj0 and uj1): ctl_req's fall at its driver (Cf) is read by the "
                           "join (I1 -> O6) no later than s's next change at its driver (S1) is read by it (I2 -> O6)")
        e["inequality"] = ("per join k in {uj0, uj1}: Cf + pc_k.hi <= S1 + ps_k.lo (S1 from the control channel's contract: s held to "
                           "ctl_ack fall = z_ack fall). The request pin I0 and the feedback pin I3 do NOT enter.")
        for p in fm["data_paths"]: p[0]["lean_sym"] = "Cf"; p[1]["lean_sym"] = "pc_k.hi"; p[3]["lean_sym"] = "pc_k.hi"
        for p in fm["request_paths"]: p[0]["lean_sym"] = "S1"; p[1]["lean_sym"] = "ps_k.lo"; p[3]["lean_sym"] = "ps_k.lo"
        fm["note"] = "Lean LibGapMux.join_box_exact: Cf + Chi <= S1 + Slo (per join); same shape as the old H_BUNDLED_S_HOLD_T Tcf + chi <= Ts' + slo"
    e["lean"] = [
        L(LGM, "join_box_exact", "exact", note="iff over the delay box (request, ctl_req, s AND feedback pin windows, Qlo >= 1), for every request trace, every s stable on [S0,S1) (arbitrary outside) and every join trace obeying H_PIN_READ + H_RESET: JSpec <-> setup AND hold"),
        L(LGM, "join_pin_exact", "exact", note="iff for fixed per-pin delays (apply per corner realisation)"),
        L(LGM, "join_pin_ok", "sufficient", note="any (non-monotone) read maps; no hypothesis on the request pin, feedback pin, reset or loop"),
        L(LGM, "mux_joins", "sufficient", note="both joins, four inequalities, own ctl_req/s read maps per join"),
        L(LGM, "join_pin_ok_K", "sufficient", note="Kleene reads: s, request and feedback may be X; s anything outside its window"),
        L(LGM, "dev_iff", "function_equality", note="pointwise, real INITs: LUT != spec iff ctl_req reads 1, s reads !v, request read != feedback read"),
        L(LGM, "unsel_low", "sufficient", note="JSpec + H_RESET + positive loop: the unselected join is 0 for ever (no wrong-branch token)"),
        L(LGM, "join_needed", "necessary", note="every violation has a real trace (constructed by run) on which JSpec fails"),
        L(LGM, "caseA", "necessary"), L(LGM, "caseB_unsel", "necessary"), L(LGM, "caseB_sel_short", "necessary"), L(LGM, "caseB_sel_long", "necessary"),
        L(LGM, "wrong_branch_latched", "counter_trace", note="setup short by 100 ps, loop 50 ps: unselected uj0 latches 1 with x_req waiting (x's token taken for y's control token)"),
        L(LGM, "wrong_branch_runt", "counter_trace", note="same, loop 200 ps: 100 ps runt on j0, recirculated every 200 ps"),
        L(LGM, "selected_early_fall", "counter_trace", note="hold violated: selected uj1 falls 500 ps early (y_req already low)"),
        L(LGM, "witness_hyps", "non_vacuity"), L(LGM, "witness_run", "non_vacuity", note="uj1 fires, uj0 stays 0 with both requests waiting"),
        L(LGM, "LutEq", "definition", note="H_PIN_READ per pin incl. feedback I3"), L(LGM, "JSpec", "definition", note="C-element law with the token's decode"),
    ] + [r for r in e["lean"] if r["name"] in MUX_KEEP]
    e["exactness"] = "exact"
    e["exactness_note"] = ("Bmx (formal/notes/B-lib-gap-mux.md): exact (iff) per join over the delay box with PER-PIN reads of all four live pins "
        "(x/y_req I0, ctl_req I1, s I2, own feedback I3; read maps need not be monotone), s adversarial outside [S0,S1), the client request arbitrary. "
        "The request and feedback windows drop out of the condition (they only shape the failure: latched wrong-branch token if the bad window "
        "outlasts the loop, else a recirculating runt). Necessity per join: unselected join with the other client's request waiting; selected join "
        "with its request waiting (setup) or already fallen (hold). Box necessity assumes pin delays independent; under a correlated corner model "
        "use join_pin_exact per realisation. O6 LUT arcs are flat over pins in prjxray, so the per-pin content is the site pins SP[I1], SP[I2]. "
        "Supersedes the window-model sufficient form (ConstraintsMux.*_unsel_low_timed) for this obligation. Not covered: bdc_muxn (other INITs; "
        "its rows are bdc_muxn.s_setup / s_hold), the ctl_req fork as a C rule K obligation, the source of S0/S1, mid-rail select (H_KLEENE_LUT).")
    e["status"] = "proved"

# --------------------------------------------------------------- probe Bri: gcd_rig.idx_setup proved exact (RigIdx)
RI = "Cells/RigIdx"
e = BYID["gcd_rig.idx_setup"]
e["obligation"] = ("H_IDX_SETUP: the operand word vector(idx), moved by the hk load edge n0 that also raises rig_rst, has settled at the frontier latch's d pins "
                   "(ulink_n1__1, and any direct a_data/b_data reader whose request is a delayed copy of F, e.g. ucmpi0) su before the frontier controller F opens the latch (RigIdx.SetupOK)")
e["inequality"] = ("vhi + su <= 16*Tlo + rlo + dlmin + enlo; vhi = idx tCO + vector decode + route to d (PathOK band hi), Tlo = min hk period, "
                   "rlo = rig_rst tCO + OR + route + SP[F.I3] (band lo), dlmin = F's LUT arc (min), enlo = F.O6 -> latch enable / reader request (min). "
                   "Side condition H_RST_LONG: rhi + dlmax + dwmax <= 16*Tlo + rlo (and H_RST_LONG_EN with + enhi for the iff)")
e["forms"] = [form([[param("tCO", "FDRE clock-to-out (idx register)", "vhi"),
                     env("vec_path", "vector decode LUTs + route to ulink_n1__1's latch d pin and the a_data/b_data readers, hi (with tCO: the band hi vhi)", "vhi"),
                     env("su", "latch / reader setup", "su")]],
                   [[env("16Tlo", "16 hk periods from the load edge n0 to the rst fall edge (min period Tlo)", "16*Tlo"),
                     param("tCO_rst", "FDRE clock-to-out (rig_rst register), lo", "rlo"),
                     wire("rst_src", "F.I3", "rlo", note="incl. the OR stage"), sp("F", "I3", "rst", "rlo"), lut("F", "I3", "O6", "dlmin"),
                     wire("F.O6", "lat.u.I1", "enlo", note="or the direct reader's request path"), sp("lat.u", "I1", "enable", "enlo"),
                     lut("lat.u", "I1", "O6", "enlo")]],
                   launch="the hk load edge n0 (moves idx and raises rig_rst)")]
e["lean"] = [L(RI, "idx_setup_suff", "sufficient", note="Rig + H_RST_LONG + H_IDX_SETUP: SetupOK, operands = the window's vector on [e n0 + vhi, e(n0+65536) + vlo), F low until r + dlmin"),
             L(RI, "idx_setup_iff", "exact", note="SetupOK for every run satisfying Rig <-> H_IDX_SETUP, under Tlo > 0, ordered bands at most one hk period wide, H_RST_LONG_EN, H_SHORT"),
             L(RI, "cex_rig", "counter_trace", note="explicit run satisfying every Rig field with no setup assumed; with H_IDX_SETUP false the d pin shows the previous vector su before the opening (cex_open, idx_before)"),
             L(RI, "idx_nonvacuous", "non_vacuity", note="7.6 ns hk period instance (illustrative bands, not routed)"),
             L(RI, "idx_fire", "context", note="the opening exists given H_TOKEN_FIRST; the token is needed only until F's first rise plus its loop bound (gcd_rig.token_static)")] + e["lean"]
e["status"] = "proved"
e["exactness"] = "exact"
e["exactness_note"] = ("Bri (formal/notes/B-rig-idx.md, RigIdx.lean): exact (idx_setup_iff) over every run satisfying Rig (H_HK_PERIOD, H_LOOP, H_PATH_RST, H_PATH_IDX, "
                       "H_RST_ONE_FALL, H_EN), every edge timing and window; no token hypothesis is needed for the setup half (the reset alone holds F low until r + dlmin). "
                       "Side conditions of the iff: Tlo > 0, bands ordered and at most one hk period wide, H_RST_LONG_EN, H_SHORT. Non-vacuity at 7.6 ns with illustrative, "
                       "not routed, bands. The previous P6 note (stale ok+err pairs, B-reset-contract.md 7.3) is a hypothesis from reading the RTL, not a measurement. " + RST_X)
e["check_scope"] = "route_plus_env"
more("gcd_rig.token_static", [L(RI, "idx_fire", "context", note="aF = 1, bF = 0 needed only on [e n0 + rhi, r + dlmax + dwmax]")],
     note="Bri (RigIdx.idx_fire): the static token is needed only until F's first rise plus its loop bound, not for the whole run.")

# --------------------------------------------------------------- probe Bdg: bd_delay_gated.gate per-pin box-exact (LibGapDelay)
LGD = "Cells/LibGapDelay"
e = BYID["bd_delay_gated.gate"]
e["obligation"] = ("H_GFLUSH i (LibGapDelay.GF, per stage 1 <= i < N, per pin): the stale stage value is gone from g[i]'s chain pin "
                   "before the gate's re-rise reaches its tap pin. Spec: from the fast-fall point F + (q(N-1)).hi on, z equals the "
                   "line's response to the new token alone (Flushed: no stale pulse), hence z rises no earlier than T + Llo N "
                   "(NoEarly: the full matched length, chain LOWER bounds, after the gate rose); z falls one tap hop after the gate")
e["lean"] = [
    L(LGD, "box_exact_flushed", "exact", note="iff over the per-pin delay box (every read-map tuple inside it, non-monotone allowed): Flushed <-> H_GFLUSH i for all 1 <= i < N, under H_BAL_HI, H_LO_ORDER, H_START (all stages), gate pulse F < T"),
    L(LGD, "box_exact_no_early", "exact", note="same, for NoEarly, with H_SHORT added"),
    L(LGD, "flush_of_gflush", "sufficient", note="any read maps in the box, no side condition"),
    L(LGD, "no_early_of_gflush", "sufficient"),
    L(LGD, "stale_pulse", "necessary", note="per stage: GF i false by any amount -> at the box corner (constant delays: stages <= i slow, tap i and later fast) z high at T + (q i).lo + Pl i (N-1) while the new-token response is low"),
    L(LGD, "stale_pulse_early", "necessary", note="with H_SHORT the stale pulse is before T + Llo N"),
    L(LGD, "rescue_flushed", "counter_trace", note="boundary: without H_LO_ORDER per-stage GF is NOT necessary (N=3, GF 1 false, slow tap 2 covers the hole; Flushed holds for every map)"),
    L(LGD, "rescue_no_early", "counter_trace"),
    L(LGD, "rescue_hyps", "counter_trace"),
    L(LGD, "real_ok", "non_vacuity", note="SLOW corner, N=12, low phase 900 ps (stage-1 slack 0): every hypothesis of both iff theorems holds; Flushed and NoEarly for every map"),
    L(LGD, "real_rises", "non_vacuity", note="slow corner: z out at 623, falls at 624, rises at 6180"),
    L(LGD, "real_bad", "counter_trace", note="899 ps (GF 1 short by 1 ps): z high at 4499 < 5119 = T + Llo 12, new-token response low (stale pulse, early by 620 ps)"),
    L(LGD, "fresh_late", "relation", note="the new token's response is never early"),
    L(LGD, "line_unique", "relation", note="every trace of the per-pin line is run"),
    L(LGD, "Flushed", "definition", note="spec: no stale pulse after the fast-fall point"),
    L(LGD, "NoEarly", "definition", note="spec: no request before the full matched length"),
    L(LGD, "GF", "definition", note="H_GFLUSH i, = this row's inequality"),
] + e["lean"]
e["exactness"] = "exact"
e["exact_under"] = ["H_BAL_HI", "H_LO_ORDER", "H_START", "H_SHORT (NoEarly only)"]
e["exactness_note"] = (
    "Bdg (formal/notes/B-lib-gap-delay.md): exact (iff) over the per-pin delay box (H_PIN_READ, read maps need not be monotone), "
    "for both specs, ONLY under four per-route side conditions (field exact_under) that delimit where per-stage necessity holds; outside them the row is sufficient only "
    "(flush_of_gflush / no_early_of_gflush need no side condition). "
    "H_BAL_HI (stages k+1 < N: Vd(k+1) <= Vd k + (p k).hi, i.e. (q 1).hi <= r0.hi + r1.hi + (p 1).hi and (q k).hi <= (q(k-1)).hi + (p k).hi), "
    "H_LO_ORDER ((q k).lo <= (q i).lo + sum_{j=i+1..k} (p j).lo for i < k), H_START (F + (q(N-1)).hi <= T + (q i).lo + sum_{j>i} (p j).lo), "
    "and for NoEarly H_SHORT ((q i).lo < Llo(i+1)). Necessity is FALSE without H_LO_ORDER (rescue_*: a slow later tap "
    "covers the hole). Necessity uses independent per-pin corners (box); under a correlated corner model it is the box corner, always sound "
    "for sufficiency. Supersedes GcdCells/ConstraintsFastFall's sufficient forms for this obligation. Not covered: glitch-freedom of the "
    "new token's rising edge itself under non-monotone maps (FIFO: GcdCells.rises), the data bundled (rule A), the gate waveform (H_GATE_PULSE), "
    "and mid-rail X inside the LUT2 mux (H_KLEENE_LUT), hence strict_pending stays.")
e["evidence"] = e["evidence"] + "; LibGapDelay real_*: illustrative SLOW-corner numbers (LUT arc prjxray 100..124, wires assumed), no route measured"
e["status"] = "proved"

# --------------------------------------------------------------- probe Bj: strict own-feedback race (Bs, B-celem-strict.md, CElemStrict.lean)
CS = "Cells/CElemStrict"
STRICT_EXACT = [L(CS, "env_latency_iff", "exact", note="per-pin Kleene mux-tree model (H_TREE, H_MUX_KLEENE, H_FB_PURE): clean <-> dlmax + dwmax + wa <= dlmin + E, wa = X window of the departing select"),
                L(CS, "env_latency_strict", "exact", note="wa = 1 tick (the grid minimum): clean <-> dlmax + dwmax < dlmin + E"),
                L(CS, "box_iff", "exact", note="over the delay box D in [Dlo, Dhi]: safe for all <-> tb + Dhi + wb <= slo (slo = release X start)"),
                L(CS, "clean_iff", "exact"),
                L(CS, "env_latency_atomic", "context", note="wa = 0 (instantaneous selects, H_ATOMIC_LUT): the old '<=' form; the cited <= theorems are proved in that model and stay sufficient for the strict form")]
STRICT_C2 = STRICT_EXACT + [L(CS, "c2_all", "instance", note="the Facts hold on the real bd_c2 INIT, all 8 cycles"),
                            L(CS, "boundary_x", "counter_trace", note="at equality (D = 420): bd_c2 reads 1 at tick 419 and X at tick 420"),
                            L(CS, "binary_glitch", "counter_trace", note="release before the feedback moved: full binary glitch back to 0"),
                            L(CS, "strict_clean", "non_vacuity", note="the strict side is clean")]
STRICT_C2N = STRICT_EXACT + [L(CS, "c2n_c8g", "instance", note="the Facts hold on bd_c2n for C-8g's transition (1,0,0)->(1,1,1) only"),
                             L(CS, "boundary_x_c2n", "counter_trace", note="X at equality on C-8g's transition"),
                             L(CS, "strict_clean", "non_vacuity")]
STRICT_LATCH = STRICT_EXACT + [L(CS, "latch_facts", "instance", note="the Facts hold on the bd_latch odd bit (data edge while en = 1, then the en fall); pair O5/O6 are the same mux (Latch.pair_o5_kleene / pair_o6_kleene)")]
STRICT_MECH = [L(CS, "clean_iff", "exact", note="generic theorem (any Facts); the Facts for this cell/race are NOT decided: strict by the same mechanism"),
               L(CS, "env_latency_strict", "exact", note="generic"), L(CS, "box_iff", "exact", note="generic"), L(CS, "boundary_x", "counter_trace", note="bd_c2 instance of the mechanism")]
STRICT_INST = [L(CS, "env_latency_strict", "exact", note="for the bd_c2 / bd_c2n own-feedback race inside this entry; the composed entry's exactness is unchanged"),
               L(CS, "box_iff", "exact", note="same race"), L(CS, "c2_all", "instance"), L(CS, "boundary_x", "counter_trace", note="the race at equality reads X")]

def strict(i, refs, forms=None, ineq=None, backing=None, what=None):
    """L <= R becomes L + 1 <= R on the given forms (default all); held widths become >= Dmax + 1."""
    e = BYID[i]
    idx = list(range(len(e["forms"]))) if forms is None else forms
    for k in idx:
        e["forms"][k]["margin_ps"] += 1
    if ineq is None:
        ineq = e["inequality"].replace(" <= ", " + 1 <= ").replace(">= dlmax + dwmax", ">= dlmax + dwmax + 1")
    e["inequality"] = ineq
    e["lean"] = e["lean"] + refs
    e["strict"] = {"source": "Bs (formal/notes/B-celem-strict.md, Formal/Cells/CElemStrict.lean)", "backing": backing, "forms": idx,
                   "terms": what or "every form", "margin_added_ps": 1}
    e["exactness_note"] = (e.get("exactness_note", "") + " STRICT (Bs): own-feedback race, L <= R is now L + 1 <= R (margin_ps + 1 on forms " + str(idx) + (", " + what if what else "") +
                           "); the cited '<=' theorems are proved with instantaneous selects (H_ATOMIC_LUT / zero-width windows) and stay sufficient for the strict form. See conventions.strictness.").strip()

for c in ("bd_c2", "bd_c2n"):
    R = STRICT_C2 if c == "bd_c2" else STRICT_C2N
    b = "c2_all" if c == "bd_c2" else "c2n_c8g"
    strict(f"{c}.env_latency", R, backing=b)
    strict(f"{c}.sel_order", R, backing=b)
    strict(f"{c}.pulse_width", R, backing=b, what="held width >= Dmax + 1")
for c in ("bd_c2", "bd_c2n", "bd_c3", "bd_c4"):
    strict(f"{c}.reset_width", STRICT_MECH, backing="mechanism (Facts not decided)", what="rst held >= Dmax + 1")
for c in ("bd_c3", "bd_c4"):
    for o in ("env_latency", "sel_order"):
        strict(f"{c}.{o}", STRICT_MECH, backing="mechanism (Facts not decided)")
    strict(f"{c}.pulse_width", STRICT_MECH, backing="mechanism (Facts not decided)", what="held width >= Dmax + 1")
strict("design.rst_hold", STRICT_MECH, backing="mechanism (Facts not decided)")
for key in ("bd_latch[odd]", "bd_latch[pair.O5]", "bd_latch[pair.O6]", "bd_latch_rst"):
    strict(f"{key}.setup_data", STRICT_LATCH, backing="latch_facts")
    strict(f"{key}.setup_pulse", STRICT_LATCH, backing="latch_facts")
strict("bd_latch_rst.reset", STRICT_LATCH, forms=[0], backing="latch_facts", what="first part H_RST_PW only",
       ineq="R0 + rhi + fhi + 1 <= R1 + rlo (rst high on [R0, R1) at the driver; rhi/rlo = rst wire + SP[I3] + I3 arc); E0 + ehi <= R1 + rlo (enable low from E0); Rl + rhi <= max(Ton + ehi, Td + dhi) for the first capture (H_RST_DONE of capture_rst)")
strict("bd_ctree.node_fork", STRICT_INST, backing="c2_all (bd_c3/bd_c4 nodes: mechanism)")
strict("bd_pipe.sel_order", STRICT_INST, backing="c2n_c8g / c2_all", what="both halves")
strict("bd_pipe.lat_lumped", STRICT_INST, backing="c2n_c8g / c2_all")
strict("bd_pipe.rst_lines", STRICT_INST, backing="c2n_c8g / c2_all", what="loop terms only (the representative form is the loop term out.hi + wh + pq.hi)",
       ineq="L_i.hi + wh_i + 1 <= R; L(b-1).hi + Rq_b.hi <= R; L_b.hi + ahi_b <= R; Ag_b <= R; per pin (6g): R0 + pr.hi <= R + ps.lo; out.hi + wh + pq.hi + 1 <= R + ps.lo; R + ps.hi <= rho0 + pr.lo; R0 + pa.hi <= rho0 + pr.lo (the two loop terms strict, Bs)")
for i in ("bd_mux.uxa_rtz", "bd_mux.uya_rtz", "bd_mux.uxa_rtz_env", "bd_mux.uya_rtz_env", "bd_mux.uj_env_latency_req", "bd_mux.uj_env_latency_ctl"):
    strict(i, STRICT_INST, backing="c2_all")
strict("bd_mux.isochronic_forks", STRICT_INST, backing="c2_all", what="both")
strict("bd_mux.uxa_join_latency", STRICT_INST, backing="c2_all", what="both, uxa and uya",
       ineq="W0x.hi + Lxa.hi + wxah + 1 <= Kz + Kc + W0x.lo and W0x.hi + Lxa.hi + wxah + 1 <= 2 Kz + Kc + Wzx.lo (uya: W1y, Lya, wyah, Wzy)")
strict("bd_mux.reset_first", STRICT_INST, forms=[0], backing="c2_all", what="loop terms (H_RST_LONG) only",
       ineq="Lj*.hi + wj*h + 1 <= R, Lxa.hi + wxah + 1 <= R, Lya.hi + wyah + 1 <= R (loop terms, strict, Bs); Wx.hi, Wy.hi, Wc0.hi, Wc1.hi, Lj*.hi + W0x/W1y.hi, Wzx.hi, Wzy.hi <= R; R <= first edge at each C-element pin (Xp 0, D0 0, Yp 0, D1 0, A0 0, ZA0 0, A1 0, ZA1 0)")
strict("bd_merge.isochronic_forks", STRICT_INST, forms=[0, 1], backing="c2_all", what="S_XA_FORK and S_YA_FORK; the S_SEL_XA_N part is bundling and stays '<='",
       ineq="Wzx.hi + Lxa.hi + wxah + 1 <= Ka + Wxc.lo; Wzy.hi + Lya.hi + wyah + 1 <= Ka + Wyc.lo; hq + sh + Mz <= Wxa.lo + Eo + Wyo.lo + Lor.lo + Dz.lo (S_SEL_XA_N, node-launched; replaces S_SEL_XA_Z and S_SEL_XA_R)")
strict("bd_merge.uxa_feedback", STRICT_INST, backing="c2_all", what="both")
strict("bd_merge.uxa_req_latency", STRICT_INST, backing="c2_all", what="both, uxa and uya",
       ineq="Wxc.hi + Lxa.hi + wxah + 1 <= Kz + Ka + Wxc.lo and Wxc.hi + Lxa.hi + wxah + 1 <= 2 Kz + Ka + Wzx.lo (uya: Wyc, Lya, wyah, Wzy)")
strict("bd_merge.reset_first", STRICT_INST, forms=[0], backing="c2_all", what="loop terms (H_RST_LONG) only",
       ineq="Lxa.hi + wxah + 1 <= R, Lya.hi + wyah + 1 <= R (loop terms, strict, Bs); Wxc.hi, Wyc.hi, Wzx.hi, Wzy.hi <= R; R <= AX 0, ZA0 0, AY 0, ZA1 0")
for i in ("bdc_muxn.rtz", "bdc_muxn.iso_ctl", "bdc_muxn.uj_env_latency_req"):
    strict(i, STRICT_INST, backing="c2_all")
strict("bdc_muxn.iso_zack", STRICT_INST, backing="c2_all", what="all three",
       ineq="Wza(i).hi + La(i).hi + wah(i) + 1 <= Kc + Wja(i).lo; Wja(i).hi + La(i).hi + wah(i) + 1 <= Kz + Kc + Wja(i).lo and Wja(i).hi + La(i).hi + wah(i) + 1 <= 2 Kz + Kc + Wza(i).lo")
for i in ("bd_arbiter.rt2_pulse", "bd_arbiter.rt2_g1", "bd_arbiter.rt2b_pulse2", "bd_arbiter.rt2b_g2",
          "bdc_amerge3.rt2_cascade_pulse", "bdc_amerge3.rt2_cascade_g1", "bdc_amerge3.rt2_cascade_pulse2", "bdc_amerge3.rt2_cascade_g2"):
    strict(i, STRICT_INST, backing="c2_all", what="the ua_k C-element's loop against the A0 re-rise")
more("bd_arbiter.ack_celements", note="STRICT (Bs): inherits the strict bd_c2 entries it refers to.")
for i in ("bd_mlink.qfb_first", "bd_flink.qfb_first"):
    strict(i, STRICT_LATCH, backing="latch_facts (uq is a latch-shaped LUT3 loop)",
           ineq=BYID[i]["inequality"].replace("fhi <= wlo + elo:", "fhi + 1 <= wlo + elo:").replace("+ fhi <= Tq + wlo + elo", "+ fhi + 1 <= Tq + wlo + elo"))
    BYID[i]["exactness_note"] += " P3's relaxation to '<=' (qfb_clean: equality is clean) holds only with zero-width selects; in the per-pin Kleene model equality reads X, so the margin is 1 again (the pre-P3 strict form)."
# branch_data is bd_latch.setup_data with the launch at the producer: strict for the same reason (latch_facts); not in Bs's list (the entry is new)
strict("bd_fork.branch_data", STRICT_LATCH, backing="latch_facts (it is bd_latch.setup_data launched at the producer)", what="H_FORK_DATA_W and H_FORK_PULSE; H_FORK_HOLD is input-against-input and stays '<='",
       ineq="Td + dhi + fhi + 1 <= Tr + rlo + wlo + elo; side conditions H_FORK_PULSE ehi + fhi + 1 <= wlo + elo (= bd_latch.setup_pulse) and H_FORK_HOLD ehi <= alo + dlo (= bd_latch.hold with the fork C-tree on the ack path; input-against-input, not made strict)")
strict("bd_fork.branch_data_edge", STRICT_LATCH, backing="latch_facts")
for i, why in (("bd_link_dctl.lt_first", "already strict (R - 1)"), ("bd_arbcell.req_separation", "already strict ('>')"),
               ("bd_link_dc.rule_K_corrected", "strict when guard >= 1"), ("bd_link_dc.rule_L_corrected", "strict when guard >= 1")):
    BYID[i]["strict"] = {"source": "Bs (formal/notes/B-celem-strict.md)", "status": why, "margin_added_ps": 0}
# input-against-input orders: NOT made strict; need their own check (B-celem-strict.md)
PEND = ("input-against-input order (B-celem-strict.md): at equality the same X-window mechanism applies whenever the function is not constant across the two "
        "moving selects; NOT made strict here, needs its own check before it is")
for i in ("bd_latch[odd].hold", "bd_latch[pair.O5].hold", "bd_latch[pair.O6].hold", "bd_latch_rst.hold",
          "bd_steer.bundled_s_hold", "bd_mux.bundled_s_hold",
          "bd_delay[FASTFALL].flush_uniform", "bd_delay[FASTFALL].flush_per_stage", "bd_delay[FASTRISE].ack_flush", "bd_delay_gated.gate",
          "bd_arbiter.a0_fork_client1", "bd_arbiter.a0_fork_client2",
          "bd_arbiter.rt2_forkA", "bd_arbiter.rt2_forkG", "bd_arbiter.rt2b_forkA2", "bd_arbiter.rt2b_forkG2",
          "bdc_amerge3.rt2_cascade_forkA", "bdc_amerge3.rt2_cascade_forkG", "bdc_amerge3.rt2_cascade_forkA2", "bdc_amerge3.rt2_cascade_forkG2"):
    BYID[i]["strict_pending"] = PEND + ("; Latch.ct2_hold_violation_x already shows the X" if ".hold" in i and "latch" in i else "")

# --------------------------------------------------------------- probe Bj2: Bmn (LibGapMuxN), Blp (LibGapLatch), Bsx (NecessityReset, NecessityMuxRtz), H_NO_RETURN (ResetGcdWave)
def LN(f, n, role, note=None):
    return L(f, n, role, **({"note": note} if note else {}))

# ---- Bmn (formal/notes/B-lib-gap-muxn.md): bdc_muxn select setup/hold exact per decode and index bit; new bdc_muxn.no_third_branch
LMN = "Cells/LibGapMuxN"
MN_COMMON = [
    LN(LMN, "join_exact_fixed", "exact", "fixed per-pin delays, ANY index-bit traces: NSpec for every request trace and every trace obeying H_PIN_READ (decode LUT3 + bd_c2 join) + H_RESET iff no instant where ctl_req reads 1 at the decode and the per-bit code reading disagrees with the token about k. Request pin, decode->join wire and join feedback drop out"),
    LN(LMN, "decode_exact_all_tokens", "exact", "M1 box: join k correct for EVERY token value v < 3 iff decode k's two index pins meet per-bit setup AND hold (decode pins only)"),
    LN(LMN, "sel_box_exact", "exact", "M1 box, selected join (v = k): iff per-bit setup and hold, both bits"),
    LN(LMN, "unsel_box_exact", "exact", "M1 box, unselected join: iff Cover (every instant ctl_req may read 1 lies in the read-stable window of a bit where k and v differ); implied by the per-bit form (sel_cond_cover)"),
    LN(LMN, "join_ok_of_reads", "sufficient", "any (non-monotone) read maps"),
    LN(LMN, "maps_ok", "sufficient", "per-instant box form"),
    LN(LMN, "maps_needed", "necessary", "constant-delay bad instant inside the box refutes the box statement"),
    LN(LMN, "join_needed", "necessary", "every bad instant has a real trace (run) on which NSpec fails: unselected join rises with its request waiting; selected join fails to rise or falls early"),
    LN(LMN, "dec_eq", "function_equality", "decode LUT3 INITs 10/40/40 (H_YOSYS_MAP pin orders) = ctl_req & (s == k)"),
    LN(LMN, "c2_dev", "function_equality", "bd_c2 00E8: output differs between two decode values iff they differ and request read != feedback read"),
    LN(LMN, "third_branch_latched", "counter_trace", "index 1 -> 2 with s1 (rising) read 600 ps late: decode 0 reads 00 on [1300,1500), join 0 with in0_req waiting latches 1 from 1400 for ever: input 0's token consumed by a control token for input 2"),
    LN(LMN, "selcond_witness", "non_vacuity"), LN(LMN, "witness_third", "non_vacuity", "join 0 is 0 at every instant, join 2 fires at 1400, good timing, both requests waiting"),
]
_mn_orig_setup = copy.deepcopy(BYID["bdc_muxn.s_setup"])
for side in ("setup", "hold"):
    e = BYID[f"bdc_muxn.s_{side}"]
    fm = e["forms"][0]
    if side == "setup":
        e["obligation"] = ("S_MUXN_S_SETUP_PIN (LibGapMuxN, per decode k, per index bit b): bit b, settled at its driver at S0_b, is read by "
                           "decode k (pin s_b -> O6) no later than ctl_req's rise (Cr) is read by it (pin ctl_req -> O6); and S_Z_S for the data LUT5 (unchanged)")
        e["inequality"] = ("decode k, per bit b: S0_b + ps_b(k).hi <= Cr + pc(k).lo; ps_b(k) = s_b.drv -> sel_k.I{0|1} wire + SP + arc(I -> O6); "
                           "pc(k) = ctl_req.drv -> sel_k.I2 wire + SP + arc(I2 -> O6). The sel_k -> uj_k wire, uj_k's request pin and its feedback do NOT enter. "
                           "Old form: Ws_b(i).hi <= Lsd + Wc(i).lo with S0_b = Cr - Lsd. Data LUT5 form unchanged: sh_b + Mz <= Lsd + Kj + wo + Lo.lo + Dl")
        for p in fm["data_paths"]:
            for st in p:
                if st.get("kind") == "lut_arc": st["lean_sym"] = "ps_b(k).hi (arc part)"; st.pop("note", None)
                if st.get("kind") == "wire": st["lean_sym"] = "ps_b(k).hi (wire part)"
        for p in fm["request_paths"]:
            for st in p:
                if st.get("kind") == "lut_arc": st["lean_sym"] = "pc(k).lo (arc part)"; st.pop("note", None)
                if st.get("kind") == "wire": st["lean_sym"] = "pc(k).lo (wire part)"
        fm["note"] = "Lean LibGapMuxN.decode_exact_all_tokens / sel_box_exact: S0_b + Shi_b <= Cr + Clo per decode, per bit; EXACT (iff over the box, every token value)"
    else:
        e["obligation"] = ("S_MUXN_S_HOLD_PIN (LibGapMuxN, per decode k, per index bit b): ctl_req's fall (Cf) is read by decode k (I2 -> O6) "
                           "no later than bit b's next change at its driver (S1_b) is read by it (s_b pin -> O6)")
        e["inequality"] = ("decode k, per bit b: Cf + pc(k).hi <= S1_b + ps_b(k).lo (S1_b from the control sender's contract: index held until ctl_ack fall "
                           "seen; the old sufficient form Wc(i).hi <= Kj + Kz + Wzc.lo + Ws_b(i).lo is this with S1_b - Cf >= Kj + Kz + Wzc.lo). "
                           "The sel_k -> uj_k wire, uj_k's request pin and its feedback do NOT enter.")
        fm["note"] = ("Lean LibGapMuxN.decode_exact_all_tokens / sel_box_exact: Cf + Chi <= S1_b + Slo_b per decode, per bit; EXACT given S1_b. "
                      "The composed form via the sender contract (S1_b >= Cf + Kj + Kz + Wzc.lo) stays sufficient (MuxN3Timed)")
    e["lean"] = MN_COMMON + e["lean"]
    e["exactness"] = "exact"
    e["exact_scope"] = ("decode form (forms[0]) exact per decode k and per index bit; data LUT5 form (forms[1], S_Z_S) sufficient only" if side == "setup" else
                        "the inequality text is exact given S1_b; forms[0] bounds S1_b - Cf by the sender's round-trip contract (Kj + Kz + Wzc.lo), which is sufficient only")
    e["exactness_note"] = ("Bmn (formal/notes/B-lib-gap-muxn.md, LibGapMuxN.lean): the DECODE form is exact (iff) per decode k and per index bit over the "
        "delay box, with PER-PIN reads of the decode LUT3 (s0, s1, ctl_req) and of the bd_c2 join (request, sel_k, own feedback), read maps not "
        "necessarily monotone, each index bit stable on its own window and arbitrary outside (M1), the client request arbitrary, quantified over every "
        "token value v < 3. For one fixed token the unselected joins need only Cover (weaker; unsel_box_exact); the per-bit form is what makes every "
        "join right for every token. The decode->join wire and the join's request/feedback pins drop out. Box necessity takes pin delays "
        "independent; under a correlated corner model use join_exact_fixed per realisation. "
        + ("The data LUT5 form (S_Z_S) stays SUFFICIENT (MuxN3Timed.muxn3_data_ok). " if side == "setup" else
           "S1_b itself comes from the sender's contract; the composed round-trip form stays sufficient. ")
        + "Old Mn content: " + e["exactness_note"])
    e["status"] = "proved"
# same reason as bd_mux.bundled_s_hold / bd_steer.bundled_s_hold: Bmn's model has no X on the index bits (H_KLEENE_LUT not covered)
BYID["bdc_muxn.s_hold"]["strict_pending"] = PEND + "; LibGapMuxN has no Kleene version (no X on the index bits)"
t = {k: v for k, v in _mn_orig_setup.items() if k in ("cell", "also_applies_to", "check_scope", "combine", "corner")}
t.update(id="bdc_muxn.no_third_branch", catalogue_row="Bmn (new, B-lib-gap-muxn.md)",
    obligation=("H_NO_THIRD (LibGapMuxN.third_box_exact): when the index changes 1 -> 2 or 2 -> 1 (both bits change) across a control token's "
                "ctl_req window, decode 0 never reads the intermediate code 00 while ctl_req reads 1 (11 selects nothing)"),
    inequality=("r = the bit going 0 -> 1, f = the bit going 1 -> 0, T = their change times at the driver, decode 0's pins: "
                "Cf + pc(0).hi <= T_f + ps_f(0).lo  OR  T_r + ps_r(0).hi <= Cr + pc(0).lo  OR  T_r + ps_r(0).hi <= T_f + ps_f(0).lo. "
                "Setup side (token = the new code) and hold side (token = the old code, T = the next change) alike."),
    forms=[{"launch": "the index change (both bits) at the control sender's driver",
            "data_paths": [[{"kind": "wire", "from": "s_r.drv", "to": "sel_0.I{0|1}", "lean_sym": "Bhi (rising bit, wire part)"},
                            {"kind": "site_pin", "from": "sel_0.I{0|1}@pip", "to": "sel_0.I{0|1}", "pin_role": "s (rising bit)"},
                            {"kind": "lut_arc", "from": "sel_0.I{0|1}", "to": "sel_0.O6", "lean_sym": "Bhi (arc part)"}]],
            "request_paths": [[{"kind": "wire", "from": "s_f.drv", "to": "sel_0.I{0|1}", "lean_sym": "Alo (falling bit, wire part)"},
                               {"kind": "site_pin", "from": "sel_0.I{0|1}@pip", "to": "sel_0.I{0|1}", "pin_role": "s (falling bit)"},
                               {"kind": "lut_arc", "from": "sel_0.I{0|1}", "to": "sel_0.O6", "lean_sym": "Alo (arc part)"}]],
            "margin_ps": 0,
            "note": "third disjunct (rise-first) only; the other two are s_setup's rising-bit form and s_hold's falling-bit form at decode 0. A checker may take the OR of the three"}],
    lean=[LN(LMN, "third_box_exact", "exact", "iff over the box, index 1 -> 2 (s0 falls, s1 rises), any token v in {1,2}"),
          LN(LMN, "third_fixed_exact", "exact", "fixed delays, 1 -> 2"), LN(LMN, "third_fixed_exact_21", "exact", "fixed delays, 2 -> 1"),
          LN(LMN, "third_implied_by_setup", "sufficient", "the selected join's correctness implies join 0's: the third branch is never the only failure"),
          LN(LMN, "step_sel_exact", "exact", "selected join after a clean step: iff both changed bits read changed by ctl_req's read rise"),
          LN(LMN, "step_old_exact", "exact", "old branch: excluded once ONE changed bit is read changed"),
          LN(LMN, "rise_first_example", "instance", "rise-first: join 0 correct, selected join 2 fires late (NSpec deviation, not a wrong token)"),
          LN(LMN, "third_branch_latched", "counter_trace"), LN(LMN, "witness_third", "non_vacuity"),
          LN(LMN, "code12_zero", "lemma"), LN(LMN, "dec_eq", "function_equality")],
    exactness="exact",
    exactness_note=("Bmn: exact per join 0 over the box under H_S_STEP (each bit changes once, cleanly). Implied by bdc_muxn.s_setup's rising-bit "
                    "form (setup side) and bdc_muxn.s_hold's falling-bit form (hold side), so it adds no obligation to a design that meets those; it is the "
                    "exact condition for the third-branch hazard alone (a weaker per-join form). n = 3 only (2 index bits). INFORMATIONAL: a checker that "
                    "evaluates s_setup and s_hold need not evaluate this row."),
    informational=True, refers_to=["bdc_muxn.s_setup", "bdc_muxn.s_hold"],
    status="proved",
    site_pins={"needed": True, "roles": ["sel_0.I{0|1} (rising bit) hi", "sel_0.I{0|1} (falling bit) lo", "sel_0.I2 (ctl_req) lo/hi"]},
    rule={"rule": "none", "verdict": "none", "detail": "UNCHECKED (implied by rule-E-shaped per-bit setup + the unchecked hold)"})
E.insert(E.index(BYID["bdc_muxn.s_hold"]) + 1, t)
BYID[t["id"]] = t

# ---- Blp (formal/notes/B-lib-gap-latch.md): the nine bd_latch rows exact per pin; hold strict (clears strict_pending)
LGL = "Cells/LibGapLatch"
LBITS_P = {"odd": ("odd_box_exact", "I0", "I2", "O6"), "pair.O5": ("o5_box_exact", "I0", "I2", "O5"), "pair.O6": ("o6_box_exact", "I3", "I4", "O6")}
L_MODEL = ("LibGapLatch model: H_PIN_READ (each of d, en, own q read through its own window [t-hi, t-lo]: wire + SP + that pin's arc "
           "to THIS output; read maps need not be monotone), H_KLEENE_LUT on the real INIT (Latch.*_kleene: the pair's neighbour pins never "
           "matter, X included), H_EN_TOKEN (en definite 1 on [Ton, Toff-we), ARBITRARY on the closing window [Toff-we, Toff), 0 from Toff; "
           "arbitrary before Ton), H_D_STABLE (d definite v on [Td, Tnew-wd), arbitrary elsewhere), power-up arbitrary (no reset). "
           "Spec Capt: q = v (definite) whenever en reads the closing window or later. ")
L_NOTES = ("Exactness: box_exact (iff over the per-pin box, three inequalities together; each one has its own counter-trace "
           "family: need_pulse_two / need_data / need_hold). Strictness: with H_MUX_KLEENE's one tick of X on the moving select "
           "(we = wd = 1) all three rows are strict (strict_edges); with instantaneous selects (we = wd = 0) all three are '<=' "
           "(atomic_edges). The 1 ps is the model's minimum, not a measured slew. Box necessity takes the three pins independent; "
           "under H_RF_SYM (one delay per arc for both edges) use sym_exact / cells_sym_exact (setup_pulse loses the enable's spread). "
           "Not covered: multi-token packaging (per token), the sources of Ton/Toff/Td/Tnew (LinkTimed, ForkData), mid-rail selects beyond H_KLEENE_LUT.")
for bit, (thm, dp, fp, o) in LBITS_P.items():
    common_lean = [
        LN(LGL, thm, "exact", f"real INIT ({bit}), iff over the per-pin box: setup_pulse AND setup_data AND hold"),
        LN(LGL, "box_exact", "exact", "engine form on latM"),
        LN(LGL, "box_exact_edges", "exact", "binary-edge form with X windows we (enable fall) and wd (next datum)"),
        LN(LGL, "strict_edges", "exact", "we = wd = 1: all three strict"),
        LN(LGL, "atomic_edges", "context", "we = wd = 0: all three '<='"),
        LN(LGL, "sym_exact", "exact_fixed_transport", "H_RF_SYM: fixed per-pin delays anywhere in the box"),
        LN(LGL, "cells_sym_exact", "exact_fixed_transport", "the same on the three real INITs"),
        LN(LGL, "latch_pin_ok", "sufficient", "any read maps"),
        LN(LGL, "witness_run", "non_vacuity", "a run at the boundary writes 0 -> 1 and holds 1"),
    ]
    for row in ("setup_data", "setup_pulse", "hold"):
        e = BYID[f"bd_latch[{bit}].{row}"]
        e["exactness"] = "exact"
        e["status"] = "proved"
        e.pop("strict_pending", None)
        if row == "setup_data":
            e["obligation"] = ("L_SETUP_DATA (LibGapLatch, per pin): the datum, settled at its driver at Td, read through the D pin (slowest), "
                               "then once round the bit's OWN feedback pin (slowest), is in before the enable's closing window starts as read (fastest)")
            e["inequality"] = (f"Td + dhi + fhi + we <= Toff + elo (we = 1: strict); dhi = D wire + SP[u.{dp}] + arc u.{dp}->{o} (max); "
                               f"fhi = feedback wire (incl. any LUT->xMUX output hop) + SP[u.{fp}] + arc u.{fp}->{o} (max); "
                               f"elo = en wire + SP[u.I1] + arc u.I1->{o} (min)")
            e["lean"] = common_lean + [LN(LGL, "need_data", "necessary", "violated: X (window) or the old value captured"),
                                       LN(LGL, "ct_data_x", "counter_trace", "1 ps short: X captured"),
                                       LN(LGL, "ct_data_wrong", "counter_trace", "1 ps short, instantaneous select: old value 0 captured")] + \
                [r for r in e["lean"] if r["name"] in ("capture", "odd_latch", "pair_o6_latch", "counter_rule_I", "latch_facts", "env_latency_strict", "clean_iff")]
            e["exactness_note"] = L_MODEL + "setup_data: exact (iff). Consistent with CElemStrict.latch_facts/clean_iff (c = Td + dhi, D = fhi, s = Toff - we + elo). " + L_NOTES
            e["rule"]["detail"] = (e["rule"]["detail"] + " Blp: every missing term APPEARS in the exact form: the feedback-pin arc and SP[fb] (in fhi, max), "
                                   "SP[d] (in dhi, max), and the +1 strictness; SP[en] and the en arc appear on the right at min (omitting them is conservative); "
                                   "the enable's hi does not appear.")
        elif row == "setup_pulse":
            e["obligation"] = ("L_SETUP_PULSE (LibGapLatch, per pin): the enable's rise as read (slowest) plus once round the bit's own feedback "
                               "pin (slowest) lands before its closing window starts as read (fastest); the data pin drops out")
            e["inequality"] = (f"Ton + ehi + fhi + we <= Toff + elo (we = 1: strict), i.e. Won >= (ehi - elo) + fhi + 1; ehi/elo = en wire + "
                               f"SP[u.I1] + arc u.I1->{o} (max/min), fhi as setup_data. Under H_RF_SYM (one delay per arc): Won >= fhi + 1. "
                               "prjxray, ONE corner c in {FAST, SLOW}: Won >= (w_en.c_max - w_en.c_min) + (SP[en].c_max - SP[en].c_min) + "
                               f"(arc_I1->{o}.c_max - c_min) + w_fb.c_max + SP[fb].c_max + arc_fb->{o}.c_max + 1")
            e["lean"] = common_lean + [LN(LGL, "need_pulse_two", "necessary", "box: rise read at ehi, fall at elo; the bit keeps its power-up value"),
                                       LN(LGL, "need_pulse_sym", "necessary", "fixed delays: Ton + fhi > Toff - we"),
                                       LN(LGL, "ct_pulse_x", "counter_trace", "1 ps short: X captured"),
                                       LN(LGL, "ct_pulse_wrong", "counter_trace", "1 ps short, instantaneous select: power-up value 0 kept")] + \
                [r for r in e["lean"] if r["name"] in ("capture", "stage_token", "setup_iff", "latch_facts")]
            e["exactness_note"] = L_MODEL + "setup_pulse: exact (iff); previously sufficient only. " + L_NOTES
            e["rule"] = {"rule": "none", "verdict": "none",
                         "detail": "UNCHECKED by any rule (rule I starts at the upstream latch). Blp proposes rule P: per latch bit, per corner, "
                                   "Won(en driver, min over the route's enable pulse) >= (en spread at the bit) + fhi + 1 with SP from the FASM pin. "
                                   "Binding on the Bt2 routes (required E >= 1101-1953 ps)."}
            e["evidence"] = (e["evidence"] + "; prjxray SLOW, odd bit (O6 100::124), en on A2 (SP 409::507), fb on A1 (SP 516): "
                             "Won >= 763 ps + en wire spread + fb wire (box) or >= 641 ps + fb wire (H_RF_SYM); FAST: 324 / 271 ps + wires")
            e["site_pins"]["roles"] = ["u.I1 (enable) hi and lo", f"u.{fp} (feedback) hi"]
        else:
            e["obligation"] = ("L_HOLD (LibGapLatch, per pin): the end of the enable's closing window as read (slowest) comes no later than "
                               "the start of the next datum's X window as read through the D pin (fastest); the feedback pin drops out")
            e["inequality"] = (f"Toff + ehi + wd <= Tnew + dlo (wd = 1: strict); ehi = en wire + SP[u.I1] + arc u.I1->{o} (max); "
                               f"dlo = D wire + SP[u.{dp}] + arc u.{dp}->{o} (min)")
            for f_ in e["forms"]:
                f_["margin_ps"] = 1
            e["strict"] = {"source": "Blp (formal/notes/B-lib-gap-latch.md, Formal/Cells/LibGapLatch.lean)", "backing": "strict_edges",
                           "forms": [0], "terms": "every form", "margin_added_ps": 1}
            e["lean"] = common_lean + [LN(LGL, "need_hold", "necessary", "violated: X (window) or the next datum captured and fed back"),
                                       LN(LGL, "ct_hold_x", "counter_trace", "1 ps short: X captured"),
                                       LN(LGL, "ct_hold_wrong", "counter_trace", "1 ps short, instantaneous select: new datum 0 captured")] + \
                [r for r in e["lean"] if r["name"] in ("capture", "latch_rule_h_net", "counter_rule_H", "ct2_hold_violation_x")] + \
                [LN(CS, "env_latency_strict", "context", "the same H_MUX_KLEENE mechanism (X on a moving select); here the moving select is the next datum's")]
            e["exactness_note"] = L_MODEL + ("hold: exact (iff). strict_pending RESOLVED: strict by the next datum's X window (wd), "
                                             "margin_ps raised to 1. ") + L_NOTES
            e["rule"]["detail"] = (e["rule"]["detail"] + f" Blp: the exact form contains SP[u.I1].hi and SP[u.{dp}].lo (the missing site-pin term), the "
                                   "D-pin arc at min (rule H omits it: conservative) and the +1 strictness (missing); no feedback term.")

# ---- Bsx (formal/notes/B-necessity.md): exactness of 12 sufficient-only rows; reset-width forms made box-exact
NR = "Cells/NecessityReset"
NMR = "Cells/NecessityMuxRtz"
RGW = "Cells/ResetGcdWave"
def bsx(i, exactness, note, refs, **extra):
    e = BYID[i]
    e["exactness"] = exactness
    e["exactness_note"] = (note + " Earlier: " + e.get("exactness_note", "")).strip()
    e["lean"] = e["lean"] + [LN(f, n, r, nt) for f, n, r, nt in refs]
    e.update(extra)
    return e
CORNER_RST = dict(CORNER_1C, note=("Bsx: the reset-width form charges the I_rst arc hi on the data side and lo on the request side, so box mode is exact "
                                   "(NecessityReset.reset_box_exact); the earlier form (I_rst arc on the data side only) was short by arc.hi - arc.lo - 1 "
                                   "in box mode (json_box_gap_fails) and exact (+1) only in 1C with flat O6 arcs"))
RST_FORM_NOTE = ("Bsx (NecessityReset.reset_box_exact): Rhi + Qhi + 1 <= W + Rlo, Rhi/Rlo = rst read window (wire + SP[I_rst] + arc I_rst -> O), "
                 "Qhi = loop (feedback-pin arc + feedback wire + SP[fb]); same shape as bd_latch_rst.reset form 0. The +1 is the rst rise X window "
                 "(kleene_rise_x; the fall is harmless, kleene_release_harmless)")
for c in ("bd_c2", "bd_c2n", "bd_c3", "bd_c4"):
    rp, fp = CE[c]["rst"], CE[c]["fb"]
    e = BYID[f"{c}.reset_width"]
    m = e["forms"][0]["margin_ps"]
    e["forms"] = [form([[lut("u", rp, "O6", "Rhi: I_rst arc (hi)"), fbw("u", "O6", fp, "Qhi: loop wire"), sp("u", fp, "feedback", "in Qhi"), lut("u", fp, "O6", "Qhi: feedback-pin arc")]],
                       [[env("rst_width", f"rst high at u.{rp} (pin), min", "W"), lut("u", rp, "O6", "Rlo: I_rst arc (lo)")]],
                       margin=m, launch=f"rst rise at u.{rp} (pin)", note=RST_FORM_NOTE)]
    e["inequality"] = (f"width (exact, strict): arc(u.{rp} -> O6).hi + Qhi + 1 <= rst_width(at u.{rp}) + arc(u.{rp} -> O6).lo, Qhi = arc(u.{fp} -> O6) + feedback wire + SP[u.{fp}] "
                       "(1C, flat O6: rst held >= dlmax + dwmax + 1); release before the first request reaches the pins: sufficient, NOT necessary "
                       "(the exact cell-level condition is H_NO_RETURN)")
    e["corner"] = CORNER_RST
    e["site_pins"]["roles"] = [f"u.{fp} (feedback) hi", f"u.{rp} (reset) arc hi and lo"]
bsx("bd_c2.reset_width", "sufficient+necessary",
    "Bsx: width clause exact in the per-pin model (NecessityReset.reset_box_exact / c2_box_exact): box iff Rhi + Qhi <= W + Rlo, 1C (fixed delays) iff loop <= W (rst path drops out). The form now charges the I_rst arc on both sides (hi data, lo request), so it is box-exact plus its strict +1; the earlier form omitted the arc's spread in box mode (json_box_gap). The 'released before the first request' clause is NOT necessary (early_request_ok); the needed condition is H_NO_RETURN (returned_pulse_lost).",
    [(NR, "reset_box_exact", "exact", None), (NR, "reset_pin_exact", "exact", None), (NR, "c2_box_exact", "exact", None),
     (NR, "c2_short_reset", "counter_trace", "loop 400 ps, rst path 500 ps, rst held 399 ps: bd_c2 is 0 at 600 and 1 again at 899"),
     (NR, "c2_ok_reset", "non_vacuity", "rst held 400 ps: 0 for ever"), (NR, "c2_traces_exist", "non_vacuity", None),
     (NR, "json_box_gap_fails", "counter_trace", "the earlier form passes at W = 917; the exact box needs 995"),
     (NR, "early_request_ok", "not_necessary", None), (NR, "early_request_numbers", "not_necessary", None),
     (NR, "returned_pulse_lost", "counter_trace", None), (NR, "kleene_rise_x", "context", None)])
bsx("bd_c2n.reset_width", "sufficient+necessary",
    "Bsx: as bd_c2.reset_width; c2n HOLDS with every input at its reset value (c2n_resetstate_holds), so the width is needed in gcd_hw's actual reset state, not only for a power-up input value.",
    [(NR, "c2n_box_exact", "exact", None), (NR, "c2n_resetstate_holds", "instance", None), (NR, "reset_pin_exact", "exact", None),
     (NR, "early_request_ok", "not_necessary", None), (NR, "returned_pulse_lost", "counter_trace", None)])
for c, v in (("bd_c3", "(1,0,0)"), ("bd_c4", "(1,0,0,0)")):
    bsx(f"{c}.reset_width", "sufficient+necessary",
        f"Bsx: as bd_c2.reset_width (inputs held at {v}); with all inputs 0 the cell resets itself (inputs0_force).",
        [(NR, f"{c[3:]}_box_exact", "exact", None), (NR, "inputs0_force", "context", None)])
e = BYID["design.rst_hold"]
m = e["forms"][0]["margin_ps"]
e["forms"] = [form([[wire("rst_src", "G.I_rst", "Rhi: w_rst(G).hi"), sp("G", "I_rst", "rst", "in Rhi"), lut("G", "I_rst", "O6", "Rhi: I_rst arc (hi)"),
                     fbw("G", "O6", "I_fb", "Qhi: loop wire"), sp("G", "I_fb", "feedback", "in Qhi"), lut("G", "I_fb", "O6", "Qhi: feedback-pin arc")]],
                   [[env("rst_width", "rst_src high, min (gcd_hw: 16 hk cycles from rst_sr; 24 more at POR)", "W"), wire("rst_src", "G.I_rst", "Rlo: w_rst(G).lo"),
                     sp("G", "I_rst", "rst", "in Rlo"), lut("G", "I_rst", "O6", "Rlo: I_rst arc (lo)")]],
                   margin=m, launch="rst_src rise", note="per reset-carrying LUT G. " + RST_FORM_NOTE)]
e["inequality"] = ("per G: w_rst(G.I_rst).hi + SP[I_rst].hi + arc(I_rst -> O).hi + arc(I_fb -> O).hi + feedback wire.hi + SP[I_fb].hi + 1 "
                   "<= rst_width + w_rst(G.I_rst).lo + SP[I_rst].lo + arc(I_rst -> O).lo (Rhi + Qhi + 1 <= W + Rlo)")
e["corner"] = CORNER_RST
e["site_pins"]["roles"] = ["G.I_rst hi and lo (wire, SP and arc)", "G feedback pin hi"]
bsx("design.rst_hold", "sufficient+necessary_at_instance",
    "Bsx: per G exact (reset_box_exact on the real INIT of c2, c2n, c2n_set, c3, c4, uj0, uj1). Needed for c2n/c2n_set even with inputs at reset values; for c2/c3/c4/uj0/uj1 NOT needed once every input reads 0 (c2_inputs0_selfreset). FORM FIXED (Bj2): the earlier form charged the I_rst arc only on the data side, so in BOX mode it was short by (arc hi - arc lo - 1) per pin (json_box_gap, json_box_gap_fails: W = 917 passed the form, the exact box needs 995); it was sound only in 1C. The form now has the I_rst arc lo on the request side and the feedback-pin arc hi on the data side, as bd_latch_rst.reset form 0, which is the exact box condition plus the strict +1. Arbiter ustate not covered.",
    [(NR, "reset_box_exact", "exact", None), (NR, "cells", "instance", None), (NR, "c2ns_box_exact", "exact", None),
     (NR, "uj0_box_exact", "exact", None), (NR, "uj1_box_exact", "exact", None),
     (NR, "c2_inputs0_selfreset", "not_necessary_at_instance", None), (NR, "json_box_gap", "counter_trace", "numbers: the earlier form at W = 917 vs the exact box at 995"),
     (NR, "json_box_gap_fails", "counter_trace", None)])
bsx("bd_latch_rst.reset", "sufficient+necessary",
    "Bsx: form 0 (H_RST_PW: R0 + rhi + fhi + 1 <= R1 + rlo) is exactly the per-pin box condition (+1 strict) for both RESET_VALUEs, en held low (latch_rst0_box_exact, latch_rst1_box_exact). Unlike the earlier design.rst_hold form this form is box-sound (rlo includes the I3 arc). Forms 1-2 (H_EN_CLOSED_AT_RELEASE, H_RST_DONE) untouched (sufficient).",
    [(NR, "latch_rst0_box_exact", "exact", None), (NR, "latch_rst1_box_exact", "exact", None)],
    necessity_scope="forms[0] (H_RST_PW) only; forms 1-2 sufficient")
bsx("bd_merge.reset_first", "sufficient",
    "Bsx: NOT necessary as a whole. Loop terms (Lxa.hi + wxah + 1 <= R, uya) necessary at the instance (c2_box_exact, uxa with x_req up and z_ack 0). H_RST_EARLY (R <= AX 0, ZA0 0, ...) is NOT necessary at the cell: an early edge that stays is processed as if it arrived at release (early_request_ok); the needed condition is H_NO_RETURN (returned_pulse_lost). Wire terms (W*.hi <= R) not analysed (FIFO start-time artifact).",
    [(NR, "c2_box_exact", "necessary_loop_terms", None), (NR, "early_request_ok", "not_necessary", None), (NR, "returned_pulse_lost", "counter_trace", None)])
bsx("bd_mux.reset_first", "sufficient",
    "Bsx: as bd_merge.reset_first; loop terms necessary at uj0/uj1 (uj0_box_exact, uj1_box_exact: join held with its request up, ctl_req 0) and uxa/uya (c2_box_exact); H_RST_EARLY not necessary (early_request_ok).",
    [(NR, "uj0_box_exact", "necessary_loop_terms", None), (NR, "uj1_box_exact", "necessary_loop_terms", None),
     (NR, "c2_box_exact", "necessary_loop_terms", None), (NR, "early_request_ok", "not_necessary", None)])
bsx("bd_pipe.rst_lines", "sufficient",
    "Bsx: the loop term L_i.hi + wh_i + 1 <= R is necessary for the bd_c2n stage controller in the actual reset state (inputs at reset values hold: c2n_box_exact, c2n_resetstate_holds). The line/flush and per-pin (6g) terms are untouched.",
    [(NR, "c2n_box_exact", "necessary_loop_term", None), (NR, "c2n_resetstate_holds", "instance", None)])
bsx("design.rst_release_skew", "not_necessary",
    "Bsx + Rst3: NOT necessary. Cell level: an input edge that reaches a reset cell while its rst is still read high and then stays is processed exactly as if it arrived at release (early_request_ok, numbers early_request_numbers). The exact cell-level requirement is H_NO_RETURN: an input pulse that completes while rst is read high is lost (returned_pulse_lost). Design level: ResetGcdWave.gcd_wave_settled proves H_NO_RETURN for the reset-release window on gcd_hw's control network for EVERY rst waveform (any skew, glitches, re-assertion), so this skew bound is not needed there; the residual is H_RST_BEFORE_LOOP (rst final W < 34 GMW steps before the loop is first requested: gcd_loop_late, rst_reads_low). Kept as a sufficient form only; see hypotheses_not_inequalities H_NO_RETURN.",
    [(NR, "early_request_ok", "not_necessary", None), (NR, "early_request_numbers", "not_necessary", None),
     (NR, "returned_pulse_lost", "exact_replacement_counter_trace", None),
     (RGW, "gcd_wave_settled", "not_necessary", "whole gcd_hw control network: from F + 34(D+W+1) every control node is at sigB for every rst waveform in (S, F]"),
     (RGW, "gcd_first_wave", "not_necessary", "the covering statement gcd_wave_settled specialises")],
    replacement="H_NO_RETURN")
bsx("bd_mux.uxa_rtz_env", "sufficient+necessary_at_boundary",
    "Bsx: in mux_rtz_env_safe's own hypothesis set, H_RTZ_ENV cannot be weakened by 1 ps: claim1_false (box run: z_ack wire fall 4 / rise 1) and claim1_false_1C (every stage one fixed delay) satisfy every other hypothesis, violate H_RTZ_ENV by exactly 1 tick, and x_ack returns to 1 inside the window (real uj1 and bd_c2 INITs). claim0 = the sufficient half. One parameter point per form; mux_ok's other hypotheses not re-checked on the run.",
    [(NMR, "claim0", "sufficient", None), (NMR, "claim1_false", "counter_trace", None), (NMR, "claim1_false_1C", "counter_trace", None)])
bsx("bd_mux.uya_rtz_env", "sufficient+necessary_at_boundary",
    "Bsx: mirror of uxa_rtz_env with the real uj0 INIT (x_req waiting, s = 0).",
    [(NMR, "claimY0", "sufficient", None), (NMR, "claimY1_false", "counter_trace", None), (NMR, "claimY1_false_1C", "counter_trace", None)])

# --------------------------------------------------------------- probe Bj3: Bmg (NecessityMerge), CElemStrict2 backing, honest `exact` roles (B-self-audit2.md)
NM = "Cells/NecessityMerge"
CS2 = "Cells/CElemStrict2"
BMG = "Bmg (formal/notes/B-necessity-merge.md, NecessityMerge.lean)"

# (1) bd_merge.uxa_loop: H_XA_LOOP / H_YA_LOOP, launched at the ack C-element's own output edge
def xa_loop(a, c, Wa, Wc, Wz, wh):
    q = [fbw(a, "O6", "I2", f"{wh}: in Qhi"), sp(a, "I2", "feedback", "in Qhi"), lut(a, "I2", "O6", "Qhi: I2 (feedback) arc, hi")]
    head = [wire(f"{a}.O6", f"{c[0]} client", f"{Wa}.lo (Xlo)"),
            env("Eo", f"client {c[0]}: {c[0]}_ack edge seen -> its next {c} edge, min (H_CLIENT)", "Eo")]
    return [form([q], [head + [wire(c, f"{a}.I0", f"{Wc}.lo"), sp(a, "I0", c), lut(a, "I0", "O6", "Alo: I0 arc, lo")]],
                 margin=1, launch=f"{a}.O6 edge", note=f"{c} branch: Qhi + 1 <= Xlo + Eo + Alo"),
            form([q], [head + Kz(c, "I0" if c == "x_req" else "I1") + [wire("z_ack.drv", f"{a}.I1", f"{Wz}.lo"), sp(a, "I1", "z_ack"), lut(a, "I1", "O6", "Blo: I1 arc, lo")]],
                 margin=1, launch=f"{a}.O6 edge", note="z_ack branch: Qhi + 1 <= Xlo + Eo + K + Blo, K = Kz (min request edge -> z_ack edge)")]
old = BYID["bd_merge.uxa_feedback"]
loop = dict(
    id="bd_merge.uxa_loop", cell="bd_merge", catalogue_row="M4 (Bmg; replaces uxa_feedback and uxa_req_latency)",
    obligation="H_XA_LOOP / H_YA_LOOP: an ack C-element's own feedback settles before the first next-phase input edge it causes reaches any of its pins; launched at the C-element's OUTPUT edge, so the input wires' spreads cancel",
    inequality=("wxah + SP(uxa.I2).hi + arc(uxa.I2 -> O6).hi + 1 <= Wxa.lo + Eo + (Wxc.lo + SP(uxa.I0).lo + arc(uxa.I0 -> O6).lo) and "
                "<= Wxa.lo + Eo + Kz + (Wzx.lo + SP(uxa.I1).lo + arc(uxa.I1 -> O6).lo) (Qhi + 1 <= Xlo + Eo + Alo, Qhi + 1 <= Xlo + Eo + K + Blo); "
                "uya: wyah, Wya, Wyc, Wzy; Kz = wo + Lor.lo + Dz.lo + Es"),
    forms=xa_loop("uxa", "x_req", "Wxa", "Wxc", "Wzx", "wxah") + xa_loop("uya", "y_req", "Wya", "Wyc", "Wzy", "wyah"),
    refers_to=["bd_merge.uxa_feedback", "bd_merge.uxa_req_latency", "bd_merge.isochronic_forks"],
    lean=[L(NM, "uxa_box_exact", "exact", note="per-pin box (input read maps monotone and independent, feedback map arbitrary, real bd_c2 INIT), env H_CLIENT / H_SERVER: every run is the zero-delay C-element of its reads iff the two inequalities hold with '<='"),
          L(NM, "uxa_ok", "sufficient"), L(NM, "merge_hhold", "lemma"),
          L(NM, "cel_box_exact", "exact_inner", note="generic pointwise HHold, any pin count"), L(NM, "uxa_init", "function_equality", note="real bd_c2 INIT = cSpec"),
          L(NM, "glitch", "counter_trace", note="loop 451 against 450 available: x_ack 1 at 949, 0 at 950"),
          L(NM, "nonvacuous", "non_vacuity", note="loop 450 (equality): hypotheses hold, a trace exists"),
          L(NM, "old_imply_new", "redundancy", note="old S_XA_ZA + S_XA_FORK imply H_XA_LOOP: nothing that passed before fails now")] + STRICT_INST,
    exactness="exact",
    exact_scope=("binary per-pin box: the exact condition is '<=' (uxa_box_exact); the +1 is Bs's Kleene X window of the release select (CElemStrict), kept on top and not re-proved here. "
                 "Protocol (which edges the zero-delay C-element has) not covered: bd_merge.seq / isochronic_forks. The uor / delay / server path is one lower bound K. Box necessity takes pins independent."),
    exactness_note=(BMG + ": exact (uxa_box_exact). Every next input edge at uxa is caused by uxa's own output edge, through the client (x_req) or the client and the server (z_ack); "
                    "both bounds are measured from that edge, so how late the following input arrived only moves the edge and its spread cancels. The data side is the I2 (feedback) "
                    "wire, site pin and arc hi; the old forms charged the I1/I0 arc (equal only for flat O6 arcs). Witness: one x token, z_ack K after x_req, client exactly Eo (wit_*)."),
    site_pins={"needed": True, "roles": ["uxa/uya.I2 hi (feedback)", "uxa/uya.I0 lo", "uxa/uya.I1 lo"]},
    rule={"rule": "none", "verdict": "none", "detail": "UNCHECKED"},
    corner=dict(CORNER_1C, note="a box theorem (always sound); per corner realisation it holds with each window collapsed"),
    check_scope="route_plus_env", status="proved", combine="all",
    strict={"source": "Bs (formal/notes/B-celem-strict.md, Formal/Cells/CElemStrict.lean)", "backing": "c2_all", "forms": [0, 1, 2, 3], "terms": "all four", "margin_added_ps": 1})
E.insert(E.index(BYID["bd_merge.uxa_req_latency"]) + 1, loop)
BYID["bd_merge.uxa_loop"] = loop
for i, nm, refs in (("bd_merge.uxa_feedback", "S_XA_ZA / S_YA_ZA", [L(NM, "old_not_necessary", "not_necessary", note="box numbers: old S_XA_ZA fails (2948 > 2735), H_XA_LOOP holds (941 <= 1081), uxa_ok makes every run correct")]),
                    ("bd_merge.uxa_req_latency", "S_XA_R (1), (2)", [L(NM, "old_not_necessary_R", "not_necessary", note="x_req wire [200, 2000]: old S_XA_R (1) fails (3225 > 2551), H_XA_LOOP unchanged, every run correct")])):
    e = BYID[i]
    e["exactness"] = "not_necessary"
    e["replacement"] = "bd_merge.uxa_loop"
    e["lean"] = e["lean"] + refs + [L(NM, "old_imply_new", "redundancy", note="old S_XA_ZA + old S_XA_FORK imply the replacement")]
    e["exactness_note"] = (BMG + f": NOT necessary; replaced by bd_merge.uxa_loop (H_XA_LOOP), which is exact (uxa_box_exact). {nm} charge the input wire's spread, which cancels when "
                           "the race is launched at uxa's output edge. Kept for traceability; a checker evaluates bd_merge.uxa_loop instead. Earlier: " + e["exactness_note"])
    e.setdefault("refers_to", [])
    e["refers_to"] = e["refers_to"] + ["bd_merge.uxa_loop"]
BYID["bd_merge.isochronic_forks"]["exactness_note"] += (" " + BMG + " (argued, NOT proved): the loop term of forms 0/1 (Lxa.hi + wxah) is not needed in y-owned phases (uxa holds 0; the race is the z_ack fall at I1 against the next x_req rise at I0); "
                                                          "in x phases the loop part is bd_merge.uxa_loop's x_req branch.")
e = BYID["bd_ctree.node_fork"]
e["lean"] = e["lean"] + [L(NM, "ctree1_box_exact", "exact_inner", note="one-node tree only (bd_c2 root, two port wires): exact iff Qhi <= E + min(port read lo)"),
                         L(NM, "cel_box_exact", "exact_inner", note="node level, pointwise"), L(NM, "c2_cspec", "function_equality"), L(NM, "c3_cspec", "function_equality"), L(NM, "c4_cspec", "function_equality")]
e["exactness_note"] += (" " + BMG + ": NOT necessary for a one-node tree: the row charges the port wires' spread, which cancels, and omits the port read lo on the right; the exact one-node "
                        "condition is Qhi <= E + min(read_lo(port_i)) (ctree1_box_exact). Depth >= 2 OPEN (proposed, NOT proved: Qhi_n <= dist_min(n -> root) + E + min over children c of "
                        "(MaxMin(c) + read_lo(c -> n)), MaxMin(leaf) = 0, MaxMin(m) = max_j (MaxMin(j) + read_lo(j -> m))).")

# (2a) CElemStrict2 decides the Facts that were "mechanism (Facts not decided)" (11 rows)
MECH = {id(r) for r in STRICT_MECH}
def decided(i, refs, backing):
    e = BYID[i]
    e["lean"] = [r for r in e["lean"] if id(r) not in MECH] + refs
    e["strict"] = dict(e["strict"], backing=backing)
    e["exactness_note"] = e["exactness_note"].replace("Facts not decided", "Facts decided in CElemStrict2")
GEN = [L(CS, "env_latency_iff", "exact", note="generic; the Facts for this cell are decided in CElemStrict2"), L(CS, "env_latency_strict", "exact", note="generic, wa = 1"),
       L(CS, "box_iff", "exact", note="generic, over the delay box"), L(CS, "clean_iff", "exact", note="generic")]
for c, n, cyc in (("bd_c3", "c3_all", 18), ("bd_c4", "c4_all", 32)):
    inst = [L(CS2, n, "instance", note=f"AllCycles: the Facts hold on every one of the {cyc} cycles of the real INIT (decide +kernel)"),
            ] + ([L(CS2, "c4_clean_iff", "exact", note="usage form for every bd_c4 cycle")] if c == "bd_c4" else []) + \
           [L(CS, "boundary_x", "counter_trace", note="bd_c2 instance of the same mechanism (no c3/c4 trace)")]
    for o in ("env_latency", "sel_order", "pulse_width"):
        decided(f"{c}.{o}", GEN + inst, f"{n} (CElemStrict2, all {cyc} cycles)")
RST2 = [L(CS2, "reset_width_iff", "exact", note="rst as the release pin: safe over D in [Dlo, Dhi] iff Dhi + wa <= P"), L(CS2, "reset_width_strict", "exact", note="wa = 1: Dhi < P"),
        L(CS2, "reset_width_atomic", "context", note="wa = 0: the old '<=' form"), L(CS2, "rst_boundary_x", "counter_trace", note="bd_c2, P = D: 0 at 419, X at 420"),
        L(CS2, "rst_strict_clean", "non_vacuity", note="P = D + 1: clean"), L(CS2, "rst_glitch", "counter_trace", note="binary release before the feedback moved: reset lost"),
        L(CS2, "rst_powerup_x", "counter_trace", note="power-up X start"), L(CS2, "rst_powerup_strict_clean", "non_vacuity")]
RST_DEC = {"bd_c2": [L(CS2, "c2_rst_dec", "instance"), L(CS2, "c2_rst_race", "lemma"), L(CS2, "c2_rst_forced", "lemma"), L(CS2, "c2_rst_classes", "context")],
           "bd_c2n": [L(CS2, "c2n_rst_dec", "instance"), L(CS2, "c2n_rst_race", "lemma"), L(CS2, "c2n_rst_classes", "context"), L(CS2, "rst_boundary_x_c2n", "counter_trace")],
           "bd_c3": [L(CS2, "c3_rst_dec", "instance")], "bd_c4": [L(CS2, "c4_rst_dec", "instance")]}
for c, refs in RST_DEC.items():
    decided(f"{c}.reset_width", RST2 + refs, f"{refs[0]['name']} (CElemStrict2: rst-release Facts decided at every hold vector, start values not equal to the reset value incl. X)")
decided("design.rst_hold", RST2 + RST_DEC["bd_c2"][:1] + RST_DEC["bd_c2n"][:1] + RST_DEC["bd_c3"] + RST_DEC["bd_c4"] +
        [L(CS2, "c2set_rst_dec", "instance"), L(CS2, "c2nset_rst_dec", "instance"), L(CS2, "latrst0_rst_dec", "instance"), L(CS2, "latrst1_rst_dec", "instance")],
        "*_rst_dec (CElemStrict2) for c2, c2_set, c2n, c2n_set, c3, c4, latch_rst; uj0 / uj1: mechanism (their rst Facts are not decided)")

# (2b) an iff for the strictness race INSIDE an entry is `exact_inner`, not `exact`; keep `exact` only where the race is the entry
OWN_RACE = {f"{c}.{o}" for c in ("bd_c2", "bd_c2n", "bd_c3", "bd_c4") for o in ("env_latency", "pulse_width", "reset_width")} | {"design.rst_hold"}
n_inner = 0
for e in E:
    if e["id"] in OWN_RACE:
        continue
    new = []
    for r in e["lean"]:
        if r["role"] == "exact" and r["file"].endswith(("/CElemStrict.lean", "/CElemStrict2.lean")):
            r = dict(r, role="exact_inner"); n_inner += 1
        new.append(r)
    e["lean"] = new

# (2c) older non-iff theorems relabelled at their definitions above; rows that relied on them
e = BYID["bd_arbcell.settled_exclusion"]
e["exactness"] = "sufficient"
e["exactness_note"] = ("Bj3: unconditional structural fact (g1 && g2 = false for every input and q; no timing condition, so nothing to be necessary). "
                       "Earlier labelled exact, but settled_exclusion is a Boolean identity, not an iff.")
BYID["bd_arbcell.handover_overlap"]["exact_scope"] = ("closed form, not an iff: overlap = max 0 (d6 - o5q - w) (overlap_duration_r2_to_r1, overlap_C), so zero overlap iff d6 <= o5q + w; "
                                                      "at every consistent corner and every w >= 0 that holds (corner_no_overlap)")
for i, sf, nc in (("bd_arbiter.rt1", "rt1_exclusion", "rt1_counter_minserver"), ("bd_arbiter.rt1b", "rt1_exclusion2", "rt1_counter2_minserver")):
    BYID[i]["exact_scope"] = f"with a server answering in exactly smin, from two theorems (no single iff): {sf} (sufficient) and {nc} (necessary); the *_iff theorems cited are reductions of the rule form"
for i in ("bd_mux.uxa_rtz", "bd_mux.uya_rtz"):
    BYID[i]["exact_scope"] = "fixed delays, from two theorems (no single iff): rtz_exact_safe (w >= dl + dw: safe) and rtz_counter (0 < w < dl + dw: oscillates)"

# =============================================================== global hypotheses (not inequalities)
HYP = [
    {"id": "H_LUT_FIFO / H_PIN_FIFO / H_TREE_FIFO", "catalogue_row": "C4", "cells": ["every handshake LUT"],
     "statement": "one pin edge that leaves the function unchanged gives no output edge (single 2:1 mux with equal legs; H_KLEENE_LUT per mux)",
     "lean": [L("Cells/MuxTree", "muxTree_eq_lutK", "reduction"), L("Cells/FifoFidelity", "gls_lut_fifo", "context", note="every GLS run satisfies it by construction")],
     "check": "none on this silicon; fidelity grade B (NMOS-only tree, mid-rail select while equal legs rise)"},
    {"id": "metastability (no deadline)", "catalogue_row": "C8/R3", "cells": ["bd_c*", "bd_arbcell", "bd_arbiter"],
     "statement": "a runt width that never resolves always exists under an involution channel; no fixed read time is safe",
     "lean": [L("Cells/CElemInvolution", "c2_eternal", "counter_trace", note="existence of a runt width whose every solution oscillates for ever (an existential, not an iff)"), L("Cells/ArbInvolution", "arb_grants_eternal", "context")],
     "check": "not static; MTBF needs tau_r, T0 measured (analog tier frozen by the north star)"},
    {"id": "H_LUT62_SHARED_READ", "catalogue_row": "11", "cells": ["every LUT6_2 with O5 and O6 used (bd_arbiter.ugrant/ustate, bd_latch pair, bd_steer, bd_datamux pair)"],
     "statement": "O5 and O6 of one LUT6_2 read each shared physical pin A1..A5 at the same time (one input buffer per pin; residual skew inside the mux tree ignored); grant/overlap results that cancel q's route and site pin rely on it",
     "lean": [L("Cells/TernaryOnBits2", "SiteSync", "definition", note="restriction of the run class; universal theorems unchanged, witnesses rebuilt"),
              L("Cells/ArbOverlapRace", "Decomp", "definition", note="field H_SHARED_Q_PIN"), L("Cells/ArbOverlapRace", "b_cancel", "lemma")],
     "check": "GLS or board: drive one pin of a fractured LUT and measure O5 vs O6; must stay below one model step. Unmeasured."},
    {"id": "NOT_OBLIGATIONS: H_OR_SKEW / S_OR (bd_mux, bd_merge), H_ACK_SKEW / S_ACK (bd_steer), S_XA_PW / S_YA_PW (bd_mux, bd_merge), S_SEL_XR (bd_merge.sel_low_xreq), S_SEL_XA_Z / S_SEL_XA_R as separate checks", "catalogue_row": "Lt3, Lt4",
     "cells": ["bd_mux", "bd_merge", "bd_steer"],
     "statement": "premises of OpsTimed*'s proof route that are NOT cell obligations. B-ops-counter.md proves the conclusions without the skew and pulse-width premises (OpsCounter.lean: mux_ok_noskew, Tok.retime, or_tok_mono, mux_or_step; merge_or_step; steer_back_noskew; mux_ack_pulses_noPW, mux_XA_real_step, mux_YA_real_step, merge_XA_real_step, merge_YA_real_step; MuxWit.noskew_witness, MuxWit.ack_pulses_noPW_witness), from causality alone (1 <= Es, 1 <= Ex/Ey/Eo). B-ops-exact.md (P6) finishes the merge: merge_ok_noskew / merge_timing_ns_of_static remove the merge's H_OR_SKEW / S_OR by a theorem, and merge_data_ok_exact proves the value path under MergeDataExact, which has no S_SEL_XR (the x_req branch of a y token is launched by the LAST x token and covered by S_ZM_SEL_X, bd_merge.bundled_z) and replaces S_SEL_XA_Z / S_SEL_XA_R by the single node-launched S_SEL_XA_N (bd_merge.isochronic_forks; MergeDataStatic.exact: the old set implies the new). They are deliberately NOT entries in `constraints`: no routed netlist can fail them in the model (S_SEL_XA_Z / S_SEL_XA_R are sufficient lumpings of S_SEL_XA_N, so checking them is merely conservative).",
     "lean": OC("mux_ok_noskew", "sufficient") + OC("merge_or_step", "lemma") + OC("steer_back_noskew", "sufficient") + OC("mux_ack_pulses_noPW", "sufficient") + OC("merge_XA_real_step", "sufficient")
             + OX("merge_ok_noskew", "sufficient") + OX("merge_timing_ns_of_static", "sufficient") + OX("merge_data_ok_exact", "sufficient", "no S_SEL_XR, S_SEL_XA_N in place of S_SEL_XA_Z / S_SEL_XA_R")
             + OX("last_x", "lemma") + OX("MergeDataStatic.exact", "lemma"),
     "check": "none needed"},
    {"id": "NRBW (no read before first write): bd_latch is not reset", "catalogue_row": "Rst section 4",
     "cells": ["bd_latch (every data latch)", "bd_steer, bd_mux uj0/uj1, gcd_rig samplers (the guards)"],
     "statement": "(a) GUARD: every LUT that reads q_L or a net in its X cone is either a guard whose Kleene value, with its guarding request at reset value 0 and every data pin x, is definite (steer req0/req1, mux joins' select pin, gcd_rig uerr_d/uok_d/uabsn_d/ucmpb_d), or the next latch with en = 0. (b) WRITE BEFORE READ: the phase-0 instance of the latch/bundling entries (bd_latch[*].setup_data, bd_pipe.boundary_I, bd_pipe.data_lead). Rst2 decides (a) on the whole imported gcd_hw control network with every data net (incl. the muxn3 decode outputs) a FREE input, so H_GUARD_MAP (yosys keeping ctl_req in the decode LUT) is NOT needed for reset or release.",
     "lean": [L(RC, "steer_guardK", "lemma"), L(RC, "uj0_guardK", "lemma"), L(RC, "uj1_guardK", "lemma"), L(RC, "rig_cmp_guardK", "lemma"),
              L(RG, "gcd_post_definite", "instance", note="every control excitation at release is definite with all 64 data nets X"),
              L(RG, "neg_unguarded", "counter_trace", note="an OR steer fails the check"), L(RC, "rig_post_definite", "instance")],
     "check": "structural; decided on the elaborated RTL control netlist (ResetGcd), not yet on a synthesized / routed netlist (C-11c import)"},
    {"id": "H_NO_RETURN", "catalogue_row": "Rst section 2", "cells": ["every reset cell whose rst is still high when a frontier link fires"],
     "statement": "no input of a cell still held in reset rises AND returns before the cell's rst releases (a lost event). Cell level (Bsx, NecessityReset): this is the exact requirement: a pulse that completes while rst is read high is lost (returned_pulse_lost), while an edge that arrives early and stays is processed as if it arrived at release (early_request_ok), so 'released before the first request' (H_RST_EARLY, design.rst_release_skew) is sufficient, not necessary. Design level (Rst3, ResetGcdWave): PROVED for the reset-release window on gcd_hw's elaborated control network: for every rst waveform on (S, F] (any per-pin skew, glitches, re-assertion) every control node is at the same state sigB from F + 34(D+W+1) until the first loop request (gcd_wave_settled, from gcd_first_wave; model steps D = LUT bound, W = wire bound). Residual: H_RST_BEFORE_LOOP, rst final before the loop is first requested, which holds with a clean rst edge when W < 34 steps (gcd_clean_release, gcd_loop_late, rst_reads_low). The loop phases (after the first steer request) are not covered.",
     "lean": [L(RG, "gcd_release_quiet", "context", note="nothing moves before a frontier controller, for any release skew"),
              L(RGW, "gcd_first_wave", "sufficient", note="every bounded run from the reset state, rst anything on (S, F] and 0 on (F, E], steers 0 on (S, E]: sA covers [S, E], sB m covers [F + m(D+W+1), E]"),
              L(RGW, "gcd_wave_settled", "sufficient", note="H_NO_RETURN for the reset-release window: from F + 34(D+W+1) to E every control node is at sigB, whatever rst did"),
              L(RGW, "gcd_clean_release", "sufficient", note="with a clean rst edge at F, from power-up; steer-hold needed only after F + 34"),
              L(RGW, "gcd_loop_late", "lemma", note="no steer leaves 0 until 34 steps after rst was last 1 (a causal chain of 34 real LUTs)"),
              L(RGW, "rst_reads_low", "lemma", note="H_RST_BEFORE_LOOP: every rst pin reads 0 once F + W < k"),
              L(NR, "returned_pulse_lost", "necessary", note="cell level: a returned pulse while rst is read high is lost (bd_c2 stays 0)"),
              L(NR, "early_request_ok", "context", note="cell level: an early edge that stays gets exactly the clean response")],
     "check": "H_RST_BEFORE_LOOP on a routed netlist: max rst-pin delay (slow) < 34 fast-min LUT+wire steps on the path ulink_n1__1 -> ucmpi0 -> join -> steer, guardbanded (GUARD_LO/GUARD_HI); design.rst_release_skew need not be evaluated"},
    {"id": "H_RF_ASYM", "catalogue_row": "11", "statement": "rise = fall within a corner column; asymmetry unmeasured", "lean": [], "check": "unmeasured"},
    {"id": "H_WIRE_RATIO", "catalogue_row": "11", "statement": "one fast/slow ratio k per margin; per-wire scatter p10 0.37 .. p90 0.82 not modelled",
     "lean": [L("Cells/ArbCorners", "fast_neg_iff", "corner"), L("Cells/ArbCorners", "guard_universal", "corner")], "check": "guard As - Af/k on SLOW_MAX-only checks"},
]

# --------------------------------------------------------------- top level
doc = {
    "schema": "cell_constraints/1",
    "produced_by": "probe P2 (shard B, Phase 2 item B), 2026-10-27; transcribed from formal/notes/B-obligations.md and the B-*.md notes; no new Lean, no route. Updated by probe P4 (2026-10-27) from B-constraints-more.md (P3 Constraints{Sel,LatchRst,FastFall,Mux,More}.lean: 16 of the 19 unproved entries proved, lt_first partial, isochronic_forks x2 unproved; new bd_latch_rst.reset), B-gcd-cells.md (GcdCells.lean for bd_delay_gated; new bd_steer entries, unproved) and B-arb-overlap-race.md / B-ternary-on-bits2.md (grant overlap cap, H_LUT62_SHARED_READ). Updated by probe P5 (2026-10-27) from B-ops-timed.md / B-ops-timed2.md (OpsTimed, OpsTimedMux, OpsTimedWit, OpsTimed2: timed bd_steer/bd_mux/bd_merge; steer select setup/hold and both isochronic_forks now proved; new env-latency instances, reset_first, value path) and B-ops-counter.md (OpsCounter: one-tick counter-runs for the value path; or_skew / ack_or_skew / ack_pulse_width shown NOT necessary and therefore not entries), B-amerge.md / B-amerge-timed.md (AMerge*, MuxN3*: new cells bdc_amerge, bdc_amerge3, bdc_muxn), B-arb-corners-pin.md (per-pin O5 corner rule for the arbiter-based entries) and B-pipe-witness.md (non-degenerate witnesses cited on the bd_pipe entries); no new Lean, no route. Updated by probe P6 (2026-10-27) from B-ops-counter.md (OpsCounter.lean now tracked: OPSCOUNTER_TRACKED = True), B-ops-exact.md (OpsExact: merge x_ack branch on S_SEL_XA_N alone, S_SEL_XR redundant -> bd_merge.sel_low_xreq removed, H_SEL_START split out as bd_merge.sel_start and shown exact against uxa powering up high, mux S_Z_S1 exact alone, S_Z_X exact when x is the join's late input, S_*_RTZ / S_XA_ZA redundant under a wire-spread condition), B-muxn3-timed.md (MuxN3Timed: the 5 bdc_muxn entries proved, new bdc_muxn.bundled_z_data and .uj_env_latency_req, s_setup exact by the one-tick Mn3Cex), B-reset-contract.md and B-reset-gcd.md (ResetContract, ResetGcd: new design.rst_hold, design.rst_flush, design.rst_release_skew, gcd_rig.token_static, gcd_rig.idx_setup; bd_latch first write as the phase-0 instance of the latch entries; hypotheses NRBW and H_NO_RETURN); no new Lean, no route",
    "routed_numbers_provenance": "every 'evidence' number is quoted from B/C notes: link_arb/ce_pair s1..s4 and gcd_hw d/2/3/4 routed by nextpnr sha256 9c732bc6303458df (toolchain.sh ok); muller64 s1 is one route",
    "conventions": {
        "time_unit": "ps",
        "form": "EndpointOK (formal/lean/Formal/Core/Substrate/CornerNat.lean): for every data path P and every request path Q of a form, sum over P of each arc's upper delay + margin_ps <= sum over Q of each arc's lower delay, both measured from the form's common `launch` event. With a corner model this is EndpointOK kappa (path P) (path Q) (margin + |P| + |Q|) (bundle_band, one ps of rounding per arc); with fixed intervals it is shard C's 10a race check.",
        "combine": "'all': every form must hold (default). 'any': the obligation holds if one form holds (RT1, RT1b: race OR structural).",
        "names": "cell-relative: `<lut instance>.<logical pin>` (I0..I5, O5, O6); `<u>.<pin>@pip` is the site-pin input of that LUT pin. The checker maps logical pins to the physical A1..A6 the router chose (routed JSON X_ORIG_PORT_A<k> / ROUTING sitewire, or FASM). `{I0|I1}` = max (data side) or min (request side) over those pins. Bracketed indices (ctl[i], lat[b]) are pipe stages.",
        "arc_kinds": {
            "lut_arc": "cell IOPATH from a logical input pin to an output (prjxray per pin/output: O6 45/124 flat over pins; O5 from I0/I1 44/152, from I2 42/150; FAST_MIN/SLOW_MAX ps). nextpnr SDF: flat 124.",
            "site_pin": "input site-pin buffer of the physical LUT pin, SP[pin]; prjxray tile_type_CLBL{L,M}_{L,R}.json (fast_min, fast_max, slow_min, slow_max) ps: A1 (172,214,416,516), A2 (170,212,409,507), A3 (107,133,278,344), A4 (86,107,229,284), A5 (33,42,91,112), A6 (2,2,4,5); SLICEM A1 up to 531, D1 540. nextpnr SDF: flat 25 ps (then subtract 25 from INTERCONNECT if it includes the site pip; check on one SDF).",
            "wire": "routed INTERCONNECT from a driver output to a sink pin, excluding the site pin (prjxray pips + Elmore RC, or SDF band).",
            "feedback_wire": "routed wire from a LUT's output back to its own input pin (the loop wire; tighten.loop_wire).",
            "line": "traversal of a bd_delay line (or request/DACK line) for one edge along a named path (chain/ripple/tap/fastest); expands to wire + LUT arcs per hop.",
            "env": "a segment outside the cell (neighbour response, server, sender, protocol latency); resolved by the checker by walking the routed netlist when it is inside the design, else an environment hypothesis.",
            "cell_param": "datasheet / chipdb constant (BRAM tSU, tHD, tCO, tPWH)."},
        "lean_sym": "the symbol the arc instantiates in the cited Lean statement (dlmax, dwmax, wfa1, ...).",
        "site_pins": "`needed` = the obligation's exact form contains per-pin site delays; `roles` = which logical pin roles and on which side. The SDF cannot see them (flat 25 ps).",
        "corner_rule": "prjxray's two IOPATH triples are FAST and SLOW corners, NOT rise and fall (ArbCorners.prj_is_mix; prjxray makesdf.py:63). NEVER take a rise arc from FAST and a fall arc from SLOW. Modes: '1C' = both sides from one column, checked at FAST_MIN and at SLOW_MAX (or EndpointOK with kappa over a shared corner); 'box' = every hi at SLOW_MAX and every lo at FAST_MIN independently (always sound, pessimistic); '1C_both_corners_required' = a SLOW_MAX-only check is NOT enough (RT1b). A SLOW_MAX-only margin needs the guard As - Af/k (fast_neg_iff; As - Af if k <= 1, guard_universal). Rise = fall within a column (H_RF_ASYM unmeasured).",
        "status": "'proved' = every cited sufficient theorem exists in a tracked file; 'unproved' = the inequality is not a Lean statement (extrapolated, physical reading of an untimed result, or no theorem).",
        "exactness": "sufficient | sufficient+necessary (a counter-trace shows the condition cannot be dropped) | sufficient+necessary_at_boundary/instance (tight on a concrete trace, not a general iff) | exact (iff; see exact_scope / exact_under when present) | not_necessary (sufficient, but a theorem shows the condition is not needed; see `replacement`) | sufficient+necessary_untimed (S/N in an untimed model; the delay inequality is its physical reading) | untimed_schedule | hypothesis (a named assumption the cell theorems use, not derived) | sufficient_by_arithmetic | see_refers_to | partial (status stays 'unproved': a weaker statement than the entry is proved; exactness_note says what is missing) | unproved.",
        "rule_verdicts": "exact | conservative | missing_term (rule weaker; `missing` names the term) | exact_arcs_missing_site_pins | conservative_arcs_missing_site_pins | rule_is_the_check | different_condition | none (no rule checks it) | uncheckable_statically.",
        "check_scope": "static_route (route + prjxray only) | route_plus_env (needs a neighbour or environment latency; static when the neighbour is in the design) | environment | protocol | structural | not_static.",
        "exact_scope": "optional text: which forms or parts of an 'exact' entry are exact; the rest of the entry is sufficient only (e.g. bdc_muxn.s_setup: decode form exact, data LUT5 form sufficient).",
        "necessity_scope": "optional text: where the necessity half of an entry's exactness holds (a consumer kind, or a subset of its forms).",
        "informational": "true: the entry is implied by the entries in refers_to; a checker that evaluates those need not evaluate it.",
        "replacement": "for exactness 'not_necessary': the named hypothesis (hypotheses_not_inequalities) or the constraint id that is the needed condition in its place (bd_merge.uxa_feedback / uxa_req_latency -> bd_merge.uxa_loop; kept for traceability, a checker evaluates the replacement).",
        "lean_roles": "role of each citation. 'exact': the theorem's statement is an iff (contains '↔'; the validator checks this) for the entry's inequality or a named part of it (see exact_scope). 'exact_inner': an iff for a race, sub-case or special case INSIDE the entry (e.g. CElemStrict's own-feedback race behind the strict +1 of a composed entry, or the one-node bd_ctree case); it does not make the entry exact. 'exact_formula': a closed-form equality for a quantity (e.g. an overlap duration), not an iff. Other roles: sufficient, necessary, counter_trace, non_vacuity, instance, lemma, definition, context, not_necessary*, redundancy, ... (as named).",
        "exact_under": "optional list of named side conditions: the entry's 'exact' holds only under them; outside them it is sufficient only.",
        "strictness": "Bs (formal/notes/B-celem-strict.md, Formal/Cells/CElemStrict.lean): in the per-pin Kleene mux-tree model (H_TREE, H_MUX_KLEENE: a moving select reads X on [s, s + wa), wa >= 1 tick; H_FB_PURE) the own-feedback race is clean iff dlmax + dwmax + wa <= dlmin + E (env_latency_iff), so with the grid minimum wa = 1 ps every own-feedback race entry reads L + 1 <= R (env_latency_strict; at equality bd_c2 reads X, boundary_x) and every held width >= Dmax + 1. Entries carrying `strict` have margin_ps raised by 1 on the forms it lists; their earlier '<=' theorems are proved with instantaneous selects (wa = 0, env_latency_atomic) and remain sufficient. The 1 ps is the model's minimum, NOT a measured slew: the physical margin is the departing select's X width (with SDF 50% arrival times about half the sum of the two select slews), which nothing here measures. `strict_pending` marks input-against-input orders where the same mechanism may apply but has not been checked; they stay '<='.",
        "guards_in_rules": "tighten.py A, D, F, H, I, K, L add req_guard = max(0.2 t, 200 ps); skew.py (E) and arb_fork.py (J) use 0.772 early / 1.155 late (GUARD_LO/GUARD_HI).",
        "tcheck_mapping": "for one form: node 0 = launch; each path is a chain of 10a arcs [lo, hi] from node 0; data = the end nodes of the data paths; req = one node joined by the request paths' ends (the earliest change of any); setup = margin_ps. tcheck's PASS is then `verdict_sound` (every data change precedes every request change by setup). A shared arc on both sides (same element, as in setup_pulse) is CPPR-pessimistic under FixedRun (C-10a corr)."},
    "cells_pin_maps": {
        "bd_c2": "u LUT6 00E8..: I0 a, I1 b, I2 q (feedback), I3 rst", "bd_c2n": "u LUT6 00B2..: I0 a (req), I1 b (ack, inverted), I2 q, I3 rst",
        "bd_c3": "u LUT6 0000_FE80..: I0..I2 inputs, I3 q, I4 rst", "bd_c4": "u LUT6 0000_0000_FFFE_8000: I0..I3 inputs, I4 q, I5 rst",
        "bd_latch": "odd LUT6 B8B8..: I0 d, I1 en, I2 q; pair LUT6_2 FF33_CC00_B8B8_B8B8: O5 (I0 d[i], I1 en, I2 q[i]), O6 (I3 d[i+1], I1 en, I4 q[i+1])",
        "bd_latch_rst": "LUT6 00B8../FFB8..: I0 d, I1 en, I2 q, I3 rst",
        "bd_delay": "LUT1 2'h2 chain (I0); FASTFALL/FASTRISE: stage 0 LUT1, stages 1..N-1 LUT2 (I0 chain, I1 tap from a) 4'h8 / 4'hE",
        "bd_arbiter": "ustate LUT6_2 FFF0_FFB2_ACAC_ACAC: I0 r1, I1 r2, I2 q, I3 rst, I4 A0 -> O6 q, O5 R0; ugrant LUT6_2 0C0C_0C0C_A0A0_A0A0: I0 r1, I1 r2, I2 q -> O5 g1, O6 g2; ua1/ua2 bd_c2: I0 g_k, I1 A0, I2 A_k",
        "bd_mux": "uj0 LUT6 0000_AE08..: I0 x_req, I1 ctl_req, I2 s, I3 j0, I4 rst; uj1 0000_EA80..: I0 y_req; uor LUT2 E; uxa/uya bd_c2 (I0 j0/j1, I1 z_ack)",
        "bd_merge": "uor LUT2 E (x_req, y_req); uxa/uya bd_c2 (I0 x_req/y_req, I1 z_ack); usel LUT2 E (x_req, x_ack)",
        "bd_mlink": "ctl.ux LUT3 F9: I0 done, I1 ack, I2 rst -> en; ctl.uq bd_latch W=1: I0 req_in, I1 en, I2 done",
        "bd_flink": "ctl.uck LUT3 06: I0 done, I1 ack, I2 rst -> ck; ctl.uq LUT3 E2: I0 req_in, I1 ck, I2 done",
        "bd_mem": "ubuf LUT1 2'h2: strobe -> ram_clk (USE_BUFG = 0)",
        "bd_steer": "u LUT6_2 8888_8888_2222_2222: I0 req, I1 s, I2..I4 0, I5 1 -> O5 req0 (req.~s), O6 req1 (req.s); uack LUT2 E (ack0, ack1)",
        "bd_delay_gated": "as bdc instantiates it: uor LUT1 (gate) -> g[0] LUT1 -> g[i] LUT2 4'h8 (I0 chain s[i], I1 tap gate), 1 <= i < N; z = s[N]",
        "bd_datamux": "udat odd LUT3 E4: I0 s, I1 a, I2 b (s ? b : a); pair LUT6_2 FFAA_5500_E4E4_E4E4: I0 s, O5 (I1 a0, I2 b0), O6 (I3 a1, I4 b1). bd_mux: a = x_data, b = y_data; bd_merge: a = y_data, b = x_data, s = sel",
        "bdc_amerge": "bdc_amerge2_0 (bdc/emit.py emit_amerge): uarb bd_arbiter (pin map above), index_lut inferred LUT2 4'hE: I0 g2 (ugrant.O6), I1 in1_ack (ua2.O6) (H_YOSYS_MAP); uor LUT1 + bd_delay_gated on R0",
        "bdc_amerge3": "bdc_amerge3_0: cascade uarb1 -> uarb2 (uarb2.r1 = uarb1.R0 = acc1_req, uarb2.A1 = uarb1.A0 = acc1_ack); index[0] inferred LUT4 16'h000E: I0 in1_ack, I1 g2(uarb1), I2 g2(uarb2), I3 in2_ack; index[1] LUT2 4'hE: I0 g2(uarb2), I1 in2_ack",
        "bdc_muxn": "bdc_muxn3_32 (emit_muxn): sel_k inferred LUT3 (sel0 10: I0 s0, I1 s1, I2 ctl_req; sel1 40: I0 s1, I1 s0, I2 ctl_req; sel2 40: I0 s0, I1 s1, I2 ctl_req); uj_k bd_c2 (I0 in_k_req, I1 sel_k); or3 LUT3 FE (j2, j1, j0) -> uor -> bd_delay_gated; ua_k bd_c2 (I0 j_k, I1 z_ack); zdat LUT5 F0AA_CCF0 per bit (I0 in2, I1 in1, I2 in0, I3 s0, I4 s1)"},
    "constraints": E,
    "hypotheses_not_inequalities": HYP,
}
doc["produced_by"] += ". Updated by probe Bj (2026-10-27) from B-celem-strict.md (CElemStrict: own-feedback race entries strict, L + 1 <= R, field `strict`; input-against-input orders marked `strict_pending`), B-lib-gap.md (LibGapSteer: bd_steer select setup/hold exact per pin; bd_fork/bd_join delegation rows) B-fork-data.md (ForkData: bd_fork.branch_data, bd_fork.branch_data_edge, bdc_amerge.idx_bundle; edge-sampling caveat on the amerge index races), B-lib-gap-mux.md (LibGapMux: bd_mux select setup/hold exact per join), B-lib-gap-delay.md (LibGapDelay: bd_delay_gated.gate exact under side conditions) and B-rig-idx.md (RigIdx: gcd_rig.idx_setup proved exact); no new Lean, no route"
doc["produced_by"] += ". Updated by probe Bj2 (2026-10-27) from B-lib-gap-muxn.md (LibGapMuxN: bdc_muxn.s_setup decode form and s_hold exact per decode and index bit, field exact_scope; new informational bdc_muxn.no_third_branch), B-lib-gap-latch.md (LibGapLatch: the nine bd_latch setup_data / setup_pulse / hold rows exact per pin; hold strict), B-necessity.md (NecessityReset, NecessityMuxRtz: reset-width rows necessary, reset-width forms of bd_c*.reset_width and design.rst_hold made box-exact with the I_rst arc on both sides, design.rst_release_skew not necessary, bd_mux rtz_env tight at the boundary) and B-reset-gcd-wave.md (ResetGcdWave: H_NO_RETURN proved for the reset-release window); no new Lean, no route"
doc["produced_by"] += ". Updated by probe Bj3 (2026-10-27) from B-necessity-merge.md (NecessityMerge: new exact bd_merge.uxa_loop (H_XA_LOOP, launched at the ack C-element's output); uxa_feedback and uxa_req_latency not_necessary with replacement bd_merge.uxa_loop; bd_ctree.node_fork not necessary for a one-node tree, depth >= 2 open), B-celem-strict2.md (CElemStrict2: the 11 'mechanism (Facts not decided)' strict rows now cite the decided Facts c3_all, c4_all, *_rst_dec, reset_width_iff) and B-self-audit2.md (citation roles: exact only for an iff; exact_inner, exact_formula; non-iff theorems relabelled); no new Lean, no route"
json.dump(doc, open(OUT, "w"), indent=1)
print(len(E), "constraints")

# optional: python3 -I cell_constraints.gen.py cell_constraints.json cell_constraints.md re-renders the md's entry table
if len(sys.argv) > 2:
    rows = []
    for e in E:
        r = e["rule"]
        rv = "none" if r["rule"] == "none" else f'{r["rule"]}: {r["verdict"]}'
        tag = " (strict +1)" if e.get("strict", {}).get("margin_added_ps") else (" (strict pending)" if "strict_pending" in e else "")
        rows.append(f'| `{e["id"]}` | {e["status"]} | {e["exactness"]}{tag} | {"yes" if e["site_pins"]["needed"] else "no"} | {rv} |')
    md = open(sys.argv[2]).read().split("\n")
    h = md.index("| id | status | exactness | site pins | rule: verdict |")
    st = en = h + 2
    while en < len(md) and md[en].startswith("| `"):
        en += 1
    md[st:en] = rows
    open(sys.argv[2], "w").write("\n".join(md))
    print("table:", len(rows), "rows ->", sys.argv[2])
