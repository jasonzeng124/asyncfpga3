#!/usr/bin/env python3
"""Generate formal/out/cell_constraints.json (probe P2, shard B, Phase 2 item B).

Every entry is transcribed from formal/notes/B-obligations.md and the B-*.md notes
it cites, checked against the Lean statements named in `lean`. Run with -I.
"""
import json, sys

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
                   rs=[L("Cells/OnNetlistTimed2", "c_reset_s1", "sufficient", note="routed link_arb instances c_reset_s1..s4 (instance-level; no general bd_c2n reset theorem)")]),
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
              if sel_ok else []),
        status="proved" if sel_ok else "unproved",
        exactness="sufficient+necessary_at_instance" if sel_ok else "unproved",
        exactness_note=("proved for the real bd_c2n INIT with per-pin FIFO site buffers (H_PIN_FIFO, H_TREE_FIFO); necessity shown by one oscillating counter-run, not a general iff."
                        if sel_ok else "extrapolated from bd_c2n's proof (FifoFidelity/PipePerPin use INIT_c2n only); no Lean theorem for this INIT/pin map."),
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
    status = "unproved" if rst else "proved"
    rstnote = ("timing theorem not stated for the _rst INIT; Latch.rst0_kleene/rst1_kleene show it is the odd latch mux when rst = 0, so Bundling.capture should apply, but no Lean theorem composes them" if rst else None)
    fh = [fbw(u, o, fb, "fhi: loop wire"), sp(u, fb, "feedback", "in fhi"), lut(u, fb, o, "fhi: I2/I4 arc", note=b["arcnote"])]
    add(id=f"{key}.setup_data", cell=b["cell"], bit_kind=key, catalogue_row="L1",
        obligation="H_SETUP data part: the bit settles and goes once round its own loop before the enable fall arrives",
        inequality="Td + dhi + fhi <= Toff + elo; dhi = D wire + SP[d] + D arc (max); fhi = feedback wire + SP[fb] + feedback-pin arc (max); elo = enable wire + SP[en] + en arc (min)",
        forms=[form([[env("Td", "launch -> last data change at the D net driver", "Td"), wire("D.drv", f"{u}.{d}", "dhi"), sp(u, d, "data"), lut(u, d, o, "dhi")] + fh],
                    [[env("Toff", "launch -> enable fall at the en net driver (THIS bit's enable)", "Toff"), wire("en.drv", f"{u}.{en}", "elo"), sp(u, en, "enable"), lut(u, en, o, "elo")]],
                    launch="common upstream event (rule I: rise of the upstream stage whose latch feeds this one)")],
        lean=base_lean_setup if not rst else [L("Cells/Latch", "rst0_kleene", "function_equality"), L("Cells/Bundling", "capture", "sufficient", note="for the rst=0 relation, by reduction (not composed in Lean)")],
        status=status, exactness="unproved" if rst else "sufficient+necessary_at_boundary",
        exactness_note=rstnote or "sufficient (capture); tight at the boundary (counter_rule_I: one tick less passes); LinkHandshake.setup_iff is E for fixed transport as a worst-case-data condition only (audit row 20).",
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
              if not rst else []),
        status=status, exactness="unproved" if rst else "sufficient",
        exactness_note=rstnote or "sufficient; the j = i term of setup_iff (fixed transport, worst-case data).",
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
               L("Cells/Latch", "ct2_hold_violation_x", "counter_trace", note="X latched")] if not rst else []),
        status=status, exactness="unproved" if rst else "sufficient+necessary_at_boundary",
        exactness_note=rstnote or "sufficient; boundary counter-traces.",
        site_pins={"needed": True, "roles": [f"{u}.{en} (enable) hi", f"{u}.{d} (data) lo"]},
        rule={"rule": "H", "source": "cells/verify/tighten.py rule H", "verdict": "conservative_arcs_missing_site_pins",
              "missing": f"SP[{u}.{en}].hi - SP[{u}.{d}].lo",
              "detail": "rule H omits the D-pin arc min (conservative) and adds guard, but has no site-pin term (Bp section 4: pair +258 [+123,+421], odd +324 [+172,+509] in the box). C-10e: 2/932 rows fail at fastG/slowG (-19..-207 ps) that tighten passes."},
        corner=CORNER_1C, check_scope="static_route",
        evidence="Bt2 rule H at pins: q2 required 135-929 ps; tighten.py l.148: H margins move 150-200 ps per seed")

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
    exactness="sufficient", exactness_note="uniform sufficient form; the exact per-stage form is the next entry (unproved).",
    site_pins={"needed": True, "roles": ["chain pin I0 and tap pin I1 of each LUT2"]},
    rule={"rule": "F", "source": "cells/verify/tighten.py audit_fastfall", "verdict": "missing_term",
          "missing": "hop_hi(i -> i+1) - tap_lo(i+1): a value still in flight on the chain wire",
          "detail": "F checks latest stage-output fall <= earliest re-rise of the input + guard; covered only while the missing difference < guard"},
    corner=CORNER_1C)
add(id="bd_delay[FASTFALL].flush_per_stage", cell="bd_delay", variant="FASTFALL=1", catalogue_row="D2",
    obligation="exact per-stage FASTFALL flush (rule F + its in-flight term)",
    inequality="for every stage i: fall_i(latest, at stage-i OUTPUT) + hop_hi(i -> i+1) <= T + tap_lo(i+1)",
    forms=[form([[env("fall_i", "a fall -> stage i output fall, latest"), wire("s[i].O", "u[i+1].I0", "hop_hi: chain wire"), sp("u[i+1]", "I0", "chain")]],
                [[env("T", "a fall -> a re-rise (low width), min"), wire("a", "u[i+1].I1", "tap_lo"), sp("u[i+1]", "I1", "tap")]],
                launch="a falls", note="LUT2 arc of u[i+1] is common to both arrivals and cancels at select level")],
    lean=[L("Cells/Bundling", "ff_counter_ruleF", "counter_trace", note="shows rule F without the in-flight term is insufficient")],
    status="unproved", exactness="unproved",
    exactness_note="stated in B-bundling.md as the exact requirement; no Lean theorem proves it sufficient or necessary per stage (H_FLUSH is its uniform sufficient form).",
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
    obligation="gated FASTFALL line: gate low forces 0 down the chain",
    inequality="none proved (Kleene only)", forms=[],
    lean=[L("Cells/LibEndMemMlink", "gated_gate_low", "kleene"), L("Cells/LibEndMemMlink", "gated_dip_flushes", "kleene")],
    status="unproved", exactness="unproved", exactness_note="no timing theorem; expect the FASTFALL per-stage form with taps from `gate`.",
    site_pins={"needed": False, "roles": []}, rule={"rule": "F", "verdict": "none"}, corner=CORNER_1C)

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
    inequality="ult arc + lt wire (hi) <= wire + LUTs + wire back through b/a (lo)",
    forms=[form([[lut("ult", "{I0|I1}", "O6"), wire("ult.O6", "uld.I0")]],
                [[env("answer", "b or a edge -> neighbour -> back to ub/ua pins, lo")]], launch="b or a edge at ult's pins")],
    lean=[L("Cells/LinkHandshake", "dctl_ok0", "sufficient", note="interleaving schedule (untimed)"), L("Cells/LinkHandshake", "dctl_ok1", "sufficient"),
          L("Cells/LinkHandshake", "dctl_si_hazard", "counter_trace", note="9-step trace")],
    status="unproved", exactness="untimed_schedule",
    exactness_note="proved as an untimed schedule restriction; the delay inequality is its physical reading, not a Lean statement.",
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
    lean=[L("Cells/ArbHandover", "overlap_duration_r2_to_r1", "exact"), L("Cells/ArbCorners", "overlap_C", "exact"),
          L("Cells/ArbCorners", "corner_no_overlap", "exact"), L("Cells/ArbCorners", "box_overlap_le", "bound"), L("Cells/ArbCorners", "prj_is_mix", "context", note="the old 16 ps was the corner mix")],
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
    lean=[L("Cells/ArbBinary", "settled_exclusion", "exact"), L("Cells/OnNetlist", "settled_exclusion_bits", "instance", note="on the bits")],
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
        lean=[L("Cells/MuxRtzTimed", "rtz_safe", "sufficient"), L("Cells/MuxRtzTimed", "rtz_exact_safe", "exact"),
              L("Cells/MuxRtzTimed", "rtz_counter", "counter_trace", note="perpetual runt train, spurious ack"), L("Cells/MuxRtzTimed", "rtz_counter_loop", "counter_trace"),
              L("Cells/MuxRtzTimed", "rtz_inertial_lost", "counter_trace", note="inertial: wrong latch"), L("Cells/MergeMuxSI", "mux_needs_rtz", "necessary", note="untimed")],
        exactness="exact", exactness_note="exact for fixed delays (w >= dl+dw safe; 0 < w < dl+dw oscillates). rtz_safe is stated for any bd_c2 loop with a low j input, so it covers uya too.",
        site_pins={"needed": True, "roles": [f"{xa}.I2 (feedback) hi", f"{xa}.I1 (z_ack) in the env form"]},
        rule={"rule": "none", "verdict": "none", "detail": "UNCHECKED (no uxa/RTZ rule in tighten.py)"},
        corner=CORNER_1C, check_scope="route_plus_env")
    add(id=f"bd_mux.{xa}_rtz_env", cell="bd_mux", also_applies_to=["bdc_muxn (generated)"], catalogue_row="X1",
        obligation=f"H_RTZ_ENV: z_ack fall reaching {xa} plus its loop beats the control token's round trip back to z_ack's rise at {xa}",
        inequality="Wux + dlmax + dwmax <= wzc + dc + wcr + dl1 + wjo + dlo + dz + ds + wux (all right terms min); conservative baseline Wux - wux + dlmax + dwmax <= sum of (N+4) min arcs + (N+4) min hops",
        forms=[form([[wire("z_ack.drv", f"{xa}.I1", "Wux"), sp(xa, "I1", "z_ack"), lut(xa, "I1", "O6", "dlmax"), fbw(xa, "O6", "I2", "dwmax"), sp(xa, "I2", "feedback")]],
                    [[wire("z_ack.drv", "ctl.sender", "wzc"), env("dc", "control sender: ctl_ack low seen -> ctl_req rise (bd_link sender: floop_causal)", "dc"),
                      wire("ctl_req", f"{other}.I1", "wcr"), sp(other, "I1", "ctl_req"), lut(other, "I1", "O6", "dl1"),
                      wire(f"{other}.O6", "uor.I0|I1", "wjo"), lut("uor", "{I0|I1}", "O6", "dlo"), line("udly", "rise", "chain", "DELAY hops", "dz"),
                      env("ds", "server: z_req rise -> z_ack rise, min", "ds"), wire("z_ack.drv", f"{xa}.I1", "wux"), sp(xa, "I1", "z_ack")]],
                    launch="z_ack fall at its driver (Tzf)",
                    note="1C at each corner: loop at the corner's MIN, uxa at the same corner's MAX")],
        lean=[L("Cells/MuxRtzTimed", "mux_rtz_env_safe", "sufficient" if xa == "uxa" else "mirror"), L("Cells/MuxRtzTimed", "floop_causal", "lemma")],
        status="proved" if xa == "uxa" else "unproved",
        exactness="sufficient" if xa == "uxa" else "unproved",
        exactness_note="env bound tightness argued, not proved." if xa == "uxa" else "mirror of the uxa theorem (uj0 in place of uj1); not stated in Lean.",
        site_pins={"needed": True, "roles": [f"{xa}.I1 (z_ack) hi and lo", f"{xa}.I2 hi", f"{other}.I1 lo"]},
        rule={"rule": "none", "verdict": "none", "detail": "UNCHECKED"},
        corner=CORNER_1C, check_scope="route_plus_env",
        evidence="fast_adv_N0_fails -7 raw; fast_adv N = 2: +405 raw / -6 guarded (fail); reachable in bdc loop-header mux")
add(id="bd_mux.bundled_s_setup", cell="bd_mux", also_applies_to=["bdc_muxn"], catalogue_row="X3",
    obligation="H_BUNDLED_S_PIN (setup half): s settled at each join pin before ctl_req rises there",
    inequality="t_req,min >= t_sel,max at uj0/uj1 pins, from a common launch",
    forms=[form([[env("s_path", "common launch -> s net driver"), wire("s", f"{u}.I2"), sp(u, "I2", "select")] for u in ("uj0", "uj1")],
                [[env("req_path", "common launch -> ctl_req driver"), wire("ctl_req", f"{u}.I1"), sp(u, "I1", "ctl_req")] for u in ("uj0", "uj1")],
                launch="control sender's latch/enable event (common launch)")],
    lean=[L("Cells/MergeMuxSI", "mux_ok", "sufficient", note="untimed hypothesis"), L("Cells/MergeMuxSI", "mux_needs_bundled_s", "necessary"),
          L("Cells/MergeMuxSI", "mux_needs_bundled_s_hazard", "necessary"), L("Cells/MergeMuxSI", "mux_weak_broad_fails", "necessary")],
    status="unproved", exactness="sufficient+necessary_untimed", exactness_note="untimed S/N (mux_ok hypothesis); the delay inequality is its physical reading, not a timed Lean statement.",
    site_pins={"needed": True, "roles": ["uj*.I2 (s) hi", "uj*.I1 (ctl_req) lo"]},
    rule={"rule": "E (skew.py), D (screen)", "verdict": "exact_structure_missing_site_pins", "detail": "common launch, 0.772/1.155; neither adds SP terms (C-10b ruleE_sitepin_fails_all)"},
    corner=CORNER_1C, check_scope="static_route")
add(id="bd_mux.bundled_s_hold", cell="bd_mux", also_applies_to=["bdc_muxn", "bd_steer (steer_s_x_while_req)"], catalogue_row="X3",
    obligation="H_BUNDLED_S_PIN (hold half): s moves at a join pin only while ctl_req is low there",
    inequality="ctl_req fall at the pin (hi) <= next s change at the pin (lo)",
    forms=[form([[env("req_fall", "common launch -> ctl_req fall at driver"), wire("ctl_req", f"{u}.I1"), sp(u, "I1", "ctl_req")] for u in ("uj0", "uj1")],
                [[env("s_change", "common launch -> next s change at driver"), wire("s", f"{u}.I2"), sp(u, "I2", "select")] for u in ("uj0", "uj1")],
                launch="sender event")],
    lean=[L("Cells/MergeMuxSI", "mux_ok", "sufficient"), L("Cells/LibCtlMergeMux", "steer_s_x_while_req", "necessary", note="bd_steer")],
    status="unproved", exactness="sufficient+necessary_untimed", site_pins={"needed": True, "roles": ["uj*.I1 hi", "uj*.I2 lo"]},
    rule={"rule": "none", "verdict": "none", "detail": "UNCHECKED"}, corner=CORNER_1C, check_scope="static_route")
add(id="bd_mux.bundled_z", cell="bd_mux", catalogue_row="X5",
    obligation="H_BUNDLED_Z: z_req after the datamux select has settled (matched DELAY)",
    inequality="select cone + datamux (hi) <= uor + udly rise (lo), from the join edge",
    forms=[form([[env("datamux", "s -> udat LUTs -> z_data, hi")]], [[lut("uor", "{I0|I1}", "O6"), line("udly", "rise", "chain", "DELAY hops")]], launch="join edge")],
    lean=[L("Cells/MergeMuxSI", "mux_ok", "sufficient", note="untimed hypothesis")],
    status="unproved", exactness="hypothesis", exactness_note="a hypothesis of an untimed proof; the inequality is rule A's, no timed Lean theorem.",
    site_pins={"needed": True, "roles": ["udat select pin"]}, rule={"rule": "A", "verdict": "rule_is_the_check"}, corner=CORNER_1C)
add(id="bd_mux.isochronic_forks", cell="bd_mux", catalogue_row="X4",
    obligation="weak isochrony: z_ack -> {uxa, uya, ctl}; ctl_req -> {uj0, uj1}",
    inequality="branch skew < half a handshake (reading of the untimed result)", forms=[],
    lean=[L("Cells/MergeMuxSI", "mux_ok", "sufficient"), L("Cells/MergeMuxSI", "mux_needs_iso_za", "necessary"), L("Cells/MergeMuxSI", "mux_needs_iso_cr", "necessary")],
    status="unproved", exactness="sufficient+necessary_untimed", exactness_note="isochrony needed (N theorems); the numeric skew bound is not a Lean statement.",
    site_pins={"needed": True, "roles": []}, rule={"rule": "none", "verdict": "none"}, corner=CORNER_1C, check_scope="route_plus_env")

# =============================================================== bd_merge
add(id="bd_merge.seq", cell="bd_merge", catalogue_row="M1",
    obligation="H_MERGE_SEQ: a client raises req only when the other's req and ack are low", inequality="protocol", forms=[],
    lean=[L("Cells/MergeMuxSI", "merge_ok", "sufficient"), L("Cells/MergeMuxSI", "merge_needs_seq", "necessary"), L("Cells/LibCtlMergeMux", "merge_early_y_spurious_ack", "counter_trace")],
    exactness="sufficient+necessary", site_pins={"needed": False, "roles": []}, rule={"rule": "none", "verdict": "none", "detail": "bdc emits bdc_amerge = bd_arbiter instead"},
    corner=CORNER_NA, check_scope="protocol")
add(id="bd_merge.bundled_z", cell="bd_merge", catalogue_row="M2",
    obligation="H_BUNDLED_Z: z_req after usel and both its inputs settled (matched DELAY covers the select cone)",
    inequality="usel + datamux (hi) <= uor + udly rise (lo)",
    forms=[form([[wire("x_req", "usel.I0"), lut("usel", "{I0|I1}", "O6"), env("datamux", "sel -> udat -> z_data, hi")]],
                [[wire("x_req", "uor.I0"), lut("uor", "I0", "O6"), line("udly", "rise", "chain", "DELAY hops")]], launch="x_req rise")],
    lean=[L("Cells/MergeMuxSI", "merge_ok", "sufficient", note="untimed hypothesis")], status="unproved", exactness="hypothesis",
    site_pins={"needed": True, "roles": []}, rule={"rule": "A", "verdict": "rule_is_the_check"}, corner=CORNER_1C)
add(id="bd_merge.isochronic_forks", cell="bd_merge", catalogue_row="M3",
    obligation="weak isochrony z_ack -> {uxa, uya}; x_ack -> {usel, client} (broad window)", inequality="branch skew < one environment round trip", forms=[],
    lean=[L("Cells/MergeMuxSI", "merge_ok", "sufficient"), L("Cells/MergeMuxSI", "merge_needs_iso_za", "necessary"), L("Cells/MergeMuxSI", "merge_broad_needs_iso_xa", "necessary")],
    status="unproved", exactness="sufficient+necessary_untimed", site_pins={"needed": True, "roles": []}, rule={"rule": "none", "verdict": "none"}, corner=CORNER_1C, check_scope="route_plus_env")
add(id="bd_merge.uxa_feedback", cell="bd_merge", catalogue_row="M4",
    obligation="uxa/uya: generic C-element env latency implies H_RTZ (no mux-like race)",
    inequality="dlmax + dwmax <= dlmin + E (see bd_c2.env_latency)", forms=[], refers_to=["bd_c2.env_latency"],
    lean=[L("Cells/MuxRtzTimed", "merge_rtz_of_latency", "sufficient")], exactness="sufficient",
    site_pins={"needed": True, "roles": ["uxa.I2 hi"]}, rule={"rule": "none", "verdict": "none"}, corner=CORNER_1C, check_scope="route_plus_env")

# =============================================================== mlink / flink
for cell, ctl, en, enpins in [("bd_mlink", "ux", "en", "I0"), ("bd_flink", "uck", "ck", "I0")]:
    uq = "ctl.uq" if cell == "bd_mlink" else "ctl.uq"
    add(id=f"{cell}.qfb_first", cell=cell, catalogue_row="ML1",
        obligation=f"H_QFB_FIRST: the request latch's own feedback (done -> uq.I2) settles before {ctl} reacts through {en}",
        inequality=f"done -> uq.I2 wire (max) [+ SP] < done -> {ctl}.I0 wire (min) + {ctl} arc (min) + {en} -> uq.I1 wire (min)",
        forms=[form([[fbw(uq, "O6", "I2"), sp(uq, "I2", "feedback")]],
                    [[wire(f"{uq}.O6", f"ctl.{ctl}.I0"), sp(f"ctl.{ctl}", "I0", "done"), lut(f"ctl.{ctl}", "I0", "O6"),
                      wire(f"ctl.{ctl}.O6", f"{uq}.I1"), sp(uq, "I1", en)]],
                    margin=1, launch="done edge at uq.O6", note="strict '<' => margin 1 ps; uq's own arc cancels at select level")],
        lean=[L("Cells/LibEndMemMlink", f"{'mlink' if cell == 'bd_mlink' else 'flink'}_req_bit_H", "sufficient", note="interleaving schedule allowH"),
              L("Cells/LibEndMemMlink", f"{'mlink' if cell == 'bd_mlink' else 'flink'}_runt", "counter_trace"),
              L("Cells/LibEndMemMlink", f"{'mlink' if cell == 'bd_mlink' else 'flink'}_cycle", "counter_trace"),
              L("Cells/LibEndMemMlink", "masks_fail_without_H", "necessary")],
        status="unproved", exactness="untimed_schedule",
        exactness_note="proved as an untimed schedule restriction (S and N); the delay inequality is the Lean doc's physical reading, not a timed theorem. NOPEN > 1 (uz path) not modelled.",
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
    inequality="tPWH <= dsLo + dcLo + dsLoF - dsHi (clk_high_width gives width >= the right side; the comparison is arithmetic)",
    forms=[form([[param("tPWH", "RAMB18E1 min clock high pulse"), line("usetup", "rise", "chain", "DSETUP + ubuf + clk, hi", "dsHi")]],
                [[line("usetup", "rise", "chain", "lo", "dsLo"), line("uco", "rise", "chain", "lo", "dcLo"), line("usetup", "fall", "chain", "lo", "dsLoF")]], launch="req rise")],
    lean=[L("Cells/LibEndMemMlink", "clk_high_width", "bound"), L("Cells/LibEndMemMlink", "rtz_serialised", "bound")],
    status="unproved", exactness="sufficient_by_arithmetic", exactness_note="the width bound is proved; comparing with tPWH is not a Lean statement.",
    site_pins={"needed": False, "roles": []}, rule={"rule": "none", "verdict": "none"}, corner=CORNER_1C)

# =============================================================== global hypotheses (not inequalities)
HYP = [
    {"id": "H_LUT_FIFO / H_PIN_FIFO / H_TREE_FIFO", "catalogue_row": "C4", "cells": ["every handshake LUT"],
     "statement": "one pin edge that leaves the function unchanged gives no output edge (single 2:1 mux with equal legs; H_KLEENE_LUT per mux)",
     "lean": [L("Cells/MuxTree", "muxTree_eq_lutK", "reduction"), L("Cells/FifoFidelity", "gls_lut_fifo", "context", note="every GLS run satisfies it by construction")],
     "check": "none on this silicon; fidelity grade B (NMOS-only tree, mid-rail select while equal legs rise)"},
    {"id": "metastability (no deadline)", "catalogue_row": "C8/R3", "cells": ["bd_c*", "bd_arbcell", "bd_arbiter"],
     "statement": "a runt width that never resolves always exists under an involution channel; no fixed read time is safe",
     "lean": [L("Cells/CElemInvolution", "c2_eternal", "exact"), L("Cells/ArbInvolution", "arb_grants_eternal", "context")],
     "check": "not static; MTBF needs tau_r, T0 measured (analog tier frozen by the north star)"},
    {"id": "H_RF_ASYM", "catalogue_row": "11", "statement": "rise = fall within a corner column; asymmetry unmeasured", "lean": [], "check": "unmeasured"},
    {"id": "H_WIRE_RATIO", "catalogue_row": "11", "statement": "one fast/slow ratio k per margin; per-wire scatter p10 0.37 .. p90 0.82 not modelled",
     "lean": [L("Cells/ArbCorners", "fast_neg_iff", "corner"), L("Cells/ArbCorners", "guard_universal", "corner")], "check": "guard As - Af/k on SLOW_MAX-only checks"},
]

# --------------------------------------------------------------- top level
doc = {
    "schema": "cell_constraints/1",
    "produced_by": "probe P2 (shard B, Phase 2 item B), 2026-10-27; transcribed from formal/notes/B-obligations.md and the B-*.md notes; no new Lean, no route",
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
        "exactness": "sufficient | sufficient+necessary (a counter-trace shows the condition cannot be dropped) | sufficient+necessary_at_boundary/instance (tight on a concrete trace, not a general iff) | exact (iff) | sufficient+necessary_untimed (S/N in an untimed model; the delay inequality is its physical reading) | untimed_schedule | hypothesis (a named assumption the cell theorems use, not derived) | sufficient_by_arithmetic | see_refers_to | unproved.",
        "rule_verdicts": "exact | conservative | missing_term (rule weaker; `missing` names the term) | exact_arcs_missing_site_pins | conservative_arcs_missing_site_pins | rule_is_the_check | different_condition | none (no rule checks it) | uncheckable_statically.",
        "check_scope": "static_route (route + prjxray only) | route_plus_env (needs a neighbour or environment latency; static when the neighbour is in the design) | environment | protocol | structural | not_static.",
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
        "bd_mem": "ubuf LUT1 2'h2: strobe -> ram_clk (USE_BUFG = 0)"},
    "constraints": E,
    "hypotheses_not_inequalities": HYP,
}
json.dump(doc, open(OUT, "w"), indent=1)
print(len(E), "constraints")
