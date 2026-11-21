#!/usr/bin/env python3
"""Sweep driver: writes RESULTS.md next to this file.  See explore.py."""
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from explore import (analyse, build_forkjoin, build_ring, fmt_state, gate_trace,  # noqa: E402
                     make_completion, make_reset, project, stage_modes)

QUICK = os.environ.get("QUICK") == "1"
MAXS = 9 if QUICK else 13


def jobs():
    for N in range(1, 9):
        yield ("ring", "fixed", False, f"N={N}", lambda N=N: build_ring(N))
    for LR in range(1, 4):
        for LP in range(0, 5):
            for LQ in range(LP, 5):
                if LP + LQ + LR <= MAXS:
                    yield ("fork-join", "fixed", False, f"LP={LP} LQ={LQ} LR={LR}",
                           lambda a=LP, b=LQ, c=LR: build_forkjoin("join", [a, b], c))
    for kind, nm in (("mux", "fork-mux"), ("steer", "fork-condbr")):
        for LR in range(1, 4):
            for LP in range(0, 5):
                for LQ in range(0, 5):
                    if LP + LQ + LR <= MAXS:
                        yield (nm, "fixed", False, f"LP={LP} LQ={LQ} LR={LR}",
                               lambda k=kind, a=LP, b=LQ, c=LR: build_forkjoin(k, [a, b], c))
    for LR in range(1, 3):
        for a in range(0, 4):
            for b in range(a, 4):
                for c in range(b, 4):
                    if a + b + c + LR <= MAXS - 1:
                        yield ("fork3-join3", "fixed", False, f"L1={a} L2={b} L3={c} LR={LR}",
                               lambda a=a, b=b, c=c, r=LR: build_forkjoin("join", [a, b, c], r))
    for kind, nm in (("join", "fork-join"), ("mux", "fork-mux"), ("steer", "fork-condbr")):
        for LR in range(1, 3):
            for LP in range(0, 3):
                for LQ in range(0, 3):
                    if kind == "join" and LQ < LP:
                        continue
                    yield (nm, "fixed", True, f"LP={LP} LQ={LQ} LR={LR}",
                           lambda k=kind, a=LP, b=LQ, c=LR: build_forkjoin(k, [a, b], c, delays=True))
    for kind, nm in (("mux", "fork-mux"), ("steer", "fork-condbr")):
        for LR in range(1, 3):
            for LP in range(0, 3):
                for LQ in range(0, 3):
                    yield (nm, "free", False, f"LP={LP} LQ={LQ} LR={LR}",
                           lambda k=kind, a=LP, b=LQ, c=LR: build_forkjoin(k, [a, b], c, mode="free"))


NOTES = """## Reading the results

**Fixed mode, comp starts (the collapse claim).**  For every topology and every initial stage
vector the gate model's reachable stage vectors equal the stage model's, its deadlocks project
exactly onto the stage model's reachable deadlocks, every link firing is a stage-model step, no
gate is ever disabled (semi-modular), and 'Z(x) has a cycle' and 'the full 2S-transition marked
graph has a token-free cycle' each predict a reachable deadlock exactly.  On rest markings the
ringfloor.md arithmetic (S >= 2T+1 with T >= 1 per cycle, L_Q >= 2K per fork/join pair, applied
pairwise for the 3-way fork) is right on every one.  The same holds with one LUT1 buffer per
bd_delay (link req_out / ack_in, the mux's request delay).  A few 'inv' counts on bd_mux topologies
with L_Q = 0 (y_ack feeds the fork's C-element directly) mean the completion heuristic picks a
different (equivalent) value for a hold gate there; every agreement column is still full.

**reset starts are a different question**: the physical power-up with bd_c2n_set on the links that
are 1 and every other cell as emit.py emits it (fork / join / mux C-elements come up 0).  They agree
with the stage model only where that power-up equals the consistent completion (column
reset==comp); elsewhere the internal C-elements contradict the marking (e.g. a token placed in the
first link of both fork branches, with the fork's acknowledge C-element at 0: the fork 'forgets' it
was acknowledged), which produces hazards, non-stage steps and deadlocks the stage model does not
have.  emit.py never places initial tokens this way (loops fill from their entry), so this does not
bear on the claim; it does say that a hand-placed initial token next to a fork / join needs the
set variant of that cell too.

**Free mode** (select / condition an environment bit that may change only while the select /
condition channel's req and ack are both 0; mux x from a bd_src, steer branch 0 into a bd_snk;
starts with the choice point idle).  All starts deadlock (a loop with an entry and no exit fills; one
with an exit and no entry drains), so the deadlock column is not informative.  cond_br: full
agreement.  mux: a real gate-level hazard (see the worked example): after an x handshake, x_ack =
C(j0, z_ack) is excited to fall once z_ack has fallen, but the select may already change and the next
y handshake raise z_ack again first, disabling x_ack's fall (it then falls a whole handshake late).
That is a timing assumption (one LUT against a round trip through the loop), not speed-independence,
and it is exactly the loop-entry to first-iteration switch of a header mux.  The remaining free-mode
mux mismatches come from this explorer's stage-level rule for an unselected input (the stage model
has no state for 'that input's acknowledge has returned'), not from the cells.

## Not covered

Timing / bundling constraints and matched delays (delay chains are wires, or one buffer with
--delays; FASTRISE / FASTFALL side LUTs not modelled); glitches inside a LUT (a LUT is one atomic
gate with its own feedback; hazards are reported, not simulated as pulses); Kleene X / power-up
before reset; the arbiter (bd_arbiter, bdc_amerge, control_merge) and bd_merge; bdc_muxn (N > 2);
fused compute units and bd_join over operands beyond the 2/3-way joins here; bd_ctree with N > 4;
the decoupled link (BD_LINK_DC); data values (only req / ack / select / condition wires); select and
condition values tied to the data that computes them (free mode makes them independent);
topologies beyond one fork-join loop (nested loops, several back edges in series, the
mode-switching walk rules of ringfloor.md).  Sizes: paths L_P, L_Q <= 4, L_R <= 3 (S <= 11; QUICK: S <= 9); 3-way fork paths <= 3, L_R <= 2; --delays and free mode paths <= 2, L_R <= 2; rings N <= 8.
"""


def kind_of(nm):
    return {"ring": "ring", "fork-join": "join", "fork3-join3": "join",
            "fork-mux": "mux", "fork-condbr": "steer"}[nm]


def main():
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)), "RESULTS.md")
    t0 = time.time()
    rows, details, examples = [], [], []
    for nm, mode, delays, params, mk in jobs():
        net, meta = mk()
        sk = ("comp",) if (delays or mode == "free") else ("comp", "reset")
        rs, det, _ = analyse(nm, params, net, meta, kind_of(nm), starts_kind=sk,
                             check_inv=not delays)
        for r in rs:
            r["mode"] = mode
            r["delays"] = delays
            rows.append(r)
            # one worked example per kind of discrepancy
            want = None
            if r["hz"] and not any(e[0] == ("hz", nm, mode, r["start"]) for e in examples):
                want = ("hz", r["hz"][0])
            elif r["sim_ex"] and not any(e[0] == ("sim", nm, mode, r["start"]) for e in examples):
                want = ("sim", r["sim_ex"][0])
            if want:
                f = make_completion(net)[0] if r["start"] == "comp" else make_reset(net)
                S, E = net.S, len(net.env)
                guards = stage_modes(net)[3] if E else []
                best = None
                for x in range(1 << (S + E)):
                    if not all(((x >> l) & 1) == 0 for gl in guards for l in gl):
                        continue
                    g0 = f(x)
                    if g0 is None:
                        continue
                    tr = gate_trace(net, g0, lambda s, t=want[1]: s == t)
                    if tr is not None and (best is None or len(tr) < len(best[1])):
                        best = (g0, tr)
                if best:
                    st = want[1]
                    if want[0] == "hz":
                        _, gi, gj = r["hz"]
                        what = (f"in {fmt_state(net, st)}, firing {net.gates[gi]['name']} "
                                f"disables excited {net.gates[gj]['name']}")
                    else:
                        _, gi = r["sim_ex"]
                        what = (f"in {fmt_state(net, st)} (stage vector "
                                f"{project(net, st):0{S + E}b}), link {net.gates[gi]['name']} "
                                f"fires: not a step of the stage model")
                    examples.append(((want[0], nm, mode, r["start"]),
                                     f"{nm} {params} mode={mode}{' delays' if delays else ''} "
                                     f"start={r['start']}: {what}; shortest trace from "
                                     f"{fmt_state(net, best[0])}: {' '.join(best[1])}"))
        details += det
    el = time.time() - t0

    def agg(sel):
        a = dict(n=0, starts=0, dead=0, agree_dead=0, agree_reach=0, hazards=0, sim_bad=0,
                 inv=0, z_bad=0, rest=0, rest_ok=0, gmax=0)
        for r in sel:
            a["n"] += 1
            for k in ("starts", "dead", "agree_dead", "agree_reach", "hazards", "sim_bad",
                      "rest", "rest_ok"):
                a[k] += r[k]
            a["inv"] += r["inv"] or 0
            a["z_bad"] += r["z_bad"] or 0
            a["gmax"] = max(a["gmax"], r["gstates"])
        return a

    L = []
    L.append("# Gate-level vs stage-level liveness on the real cells (shard C)\n")
    L.append(f"Generated by `formal/tools/live/cells/run.sh` ({'QUICK ' if QUICK else ''}"
             f"{len(rows)} runs, {el:.0f} s).  Model and method: `explore.py` docstring; "
             "summary of what is and is not covered at the end.\n")
    L.append("## Summary by family\n")
    L.append("| family | mode | delays | start | runs | starts | starts w/ reachable deadlock | "
             "deadlock sets agree | reach sets agree | hazards | non-stage steps | inv viol | "
             "Z-cycle wrong | rest markings | ringfloor cond. right | max gate states |")
    L.append("|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|")
    keys = []
    for r in rows:
        k = (r["topo"], r["mode"], r["delays"], r["start"])
        if k not in keys:
            keys.append(k)
    for k in keys:
        a = agg([r for r in rows if (r["topo"], r["mode"], r["delays"], r["start"]) == k])
        fixed = k[1] == "fixed"
        L.append(f"| {k[0]} | {k[1]} | {'buf' if k[2] else '-'} | {k[3]} | {a['n']} | {a['starts']} | "
                 f"{a['dead']} | {a['agree_dead']}/{a['starts']} | {a['agree_reach']}/{a['starts']} | "
                 f"{a['hazards']} | {a['sim_bad']} | "
                 f"{'n/a' if (k[2] or k[3] == 'reset') else a['inv']} | "
                 f"{a['z_bad'] if fixed else 'n/a'} | {a['rest'] if fixed else 'n/a'} | "
                 f"{str(a['rest_ok']) + '/' + str(a['rest']) if fixed else 'n/a'} | {a['gmax']} |")
    L.append("")
    L.append("Columns: *starts* = initial stage vectors (fixed mode: all 2^S; free mode: all "
             "(x, s) with the choice point idle).  *deadlock sets agree* = starts for which the set of "
             "stage vectors of reachable gate deadlocks equals the set of reachable stage deadlocks "
             "(so in particular 'deadlock reachable' agrees).  *reach sets agree* = starts for which "
             "the projection of the reachable gate states equals the stage model's reachable set. "
             "*hazards* = (state, firing, disabled gate) triples violating semi-modularity. "
             "*non-stage steps* = (state, link firing) pairs where the projected step is not a step "
             "of the stage model.  *inv viol* = reachable gate states with a stable internal hold "
             "gate differing from the completion of its projection.  *Z-cycle wrong* = starts where "
             "'Z(x) has a cycle' differs from 'gate deadlock reachable'.  *rest markings* = starts in "
             "which every high stage has all its neighbours low (one token per high stage), where "
             "ringfloor.md's arithmetic (cycle: S >= 2T+1 and T >= 1; fork-join: L_Q >= 2K) is "
             "evaluated against the gate model.\n")
    if details:
        L.append("## Rest markings where the ringfloor arithmetic and the gate model differ\n")
        comp_det = [d for d in details if "start=comp" in d]
        L.append(f"comp starts: {len(comp_det)}; reset starts: {len(details) - len(comp_det)} "
                 "(first 20 shown)\n")
        for d in (comp_det + [d for d in details if d not in comp_det])[:20]:
            L.append(f"- {d}")
        L.append("")
    L.append("## Worked examples of each discrepancy kind\n")
    for _, e in examples:
        L.append(f"- {e}")
    L.append("")
    L.append("## All runs\n")
    L.append("| topology | params | mode | delays | start | S | E | gates | gate states | stage states | "
             "starts | deadlock starts | dead agree | reach agree | gate reach subset | hazards | "
             "non-stage steps | inv | Z wrong | MG wrong | rest | ringfloor right | reset==comp |")
    L.append("|" + "---|" * 23)
    for r in rows:
        L.append(f"| {r['topo']} | {r['params']} | {r['mode']} | {'buf' if r['delays'] else '-'} | "
                 f"{r['start']} | {r['S']} | {r['E']} | {r['gates']} | {r['gstates']} | {r['sstates']} | "
                 f"{r['starts']} | {r['dead']} | {r['agree_dead']} | {r['agree_reach']} | {r['subset']} | "
                 f"{r['hazards']} | {r['sim_bad']} | {'' if r['inv'] is None else r['inv']} | "
                 f"{'' if r['z_bad'] is None else r['z_bad']} | {'' if r['mg_bad'] is None else r['mg_bad']} | "
                 f"{r['rest']} | {r['rest_ok']} | {'' if r['same_as_comp'] is None else r['same_as_comp']} |")
    L.append("")
    L.append(NOTES)
    with open(out, "w") as fh:
        fh.write("\n".join(L) + "\n")
    print(f"wrote {out}: {len(rows)} runs in {el:.0f} s")
    bad = [r for r in rows if r["mode"] == "fixed" and r["start"] == "comp" and
           (r["agree_dead"] != r["starts"] or r["agree_reach"] != r["starts"] or r["hazards"]
            or r["sim_bad"] or (r["z_bad"] or 0) or r["rest_ok"] != r["rest"])]
    print(f"fixed-mode comp runs with any disagreement: {len(bad)}")
    for r in bad[:10]:
        print("  ", r["topo"], r["params"], r["delays"])


if __name__ == "__main__":
    main()
