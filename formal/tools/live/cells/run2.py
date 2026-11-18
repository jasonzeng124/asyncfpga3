#!/usr/bin/env python3
"""Follow-up sweep (explore2.py): writes RESULTS2.md next to this file."""
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from explore import (analyse, chain, mg_tokenfree_cycle, project, scc_dp,  # noqa: E402
                     stage_graph, make_completion)
from explore2 import (Net2, build_loop, explore_from, fmt_state, hazards, monitors,  # noqa: E402
                      reset_state, terminal_dead, trace_to)

HERE = os.path.dirname(os.path.abspath(__file__))
QUICK = os.environ.get("QUICK") == "1"
LIMIT = int(os.environ.get("LIMIT", "150000"))


# ------------------------------------------------------------- (2), (3) ------

def fj(Ls, LR, kind="join", k=0, ff=0):
    n = Net2(fastfall=ff)
    idx = [0]
    segs = {}
    segs["R"] = chain(n, "R", LR, "jz_r", "jz_a", "f_r", "f_a", False, idx)
    pr, pa = [], []
    for i, L in enumerate(Ls):
        nm = "PQXYZW"[i]
        segs[nm] = chain(n, nm, L, f"fo{i}_r", f"fo{i}_a", f"ji{i}_r", f"ji{i}_a", False, idx)
        pr.append(f"fo{i}_r")
        pa.append(f"fo{i}_a")
    n.fork("F", "f_r", "f_a", pr, pa)
    if kind == "join":
        n.join("J", [f"ji{i}_r" for i in range(len(Ls))], [f"ji{i}_a" for i in range(len(Ls))],
               "jz_r", "jz_a")
    else:   # bdc_muxn N = 3: path 0 = index (ctl), path 1 = selected input k
        ins = [("1'b0", f"unused{j}_a") for j in range(3)]
        ins[k] = ("ji1_r", "ji1_a")
        bits = ["1'b1" if (k >> b) & 1 else "1'b0" for b in range(2)]
        n.muxn("MN", ins, "ji0_r", "ji0_a", bits, "jz_r", "jz_a")
    return n.finalize(), {"segments": segs}


def ring_ff(N, ff):
    n = Net2(fastfall=ff)
    for i in range(N):
        n.link(f"L{i}", f"r{i}", f"a{i}", f"r{(i + 1) % N}", f"a{(i + 1) % N}")
    return n.finalize(), {"segments": {"ring": list(range(N))}}


def part23():
    jobs = []
    for N in (5, 6):
        rng = (0, 1) if QUICK else (0, 1, 2)
        import itertools
        for Ls in itertools.combinations_with_replacement(rng, N):
            for LR in (1, 2):
                if sum(Ls) + LR <= (9 if QUICK else 11):
                    jobs.append((f"fork{N}-join{N} (bd_ctree {N})", f"L={''.join(map(str, Ls))} LR={LR}",
                                 lambda Ls=Ls, LR=LR: fj(list(Ls), LR)))
    for k in range(3):
        for LP in range(0, 4):
            for LQ in range(0, 4):
                for LR in (1, 2, 3):
                    if LP + LQ + LR <= 9:
                        jobs.append((f"fork-bdc_muxn3 (s={k})", f"LP={LP} LQ={LQ} LR={LR}",
                                     lambda k=k, a=LP, b=LQ, c=LR: fj([a, b], c, "muxn", k)))
    for ff in (1, 2, 3):
        for N in range(3, 7):
            jobs.append((f"ring, RFAST DELAY={ff}", f"N={N}", lambda N=N, ff=ff: ring_ff(N, ff)))
        for LP in range(0, 3):
            for LQ in range(LP, 3):
                for LR in (1, 2):
                    if ff == 1 or LP + LQ + LR <= 5:
                        jobs.append((f"fork-join, RFAST DELAY={ff}", f"LP={LP} LQ={LQ} LR={LR}",
                                     lambda a=LP, b=LQ, c=LR, ff=ff: fj([a, b], c, "join", 0, ff)))
    rows, examples = [], {}
    for fam, params, mk in jobs:
        if os.environ.get("VERBOSE"):
            print("part23", fam, params, flush=True)
        net, meta = mk()
        rs, det, _ = analyse(fam, params, net, meta, "ring" if fam.startswith("ring") else "join",
                             starts_kind=("comp",), check_inv=False)
        r = rs[0]
        comp = make_completion(net)[0]
        starts = [comp(x) for x in range(1 << net.S)]
        adj = explore_from(net, [s for s in starts if s is not None])
        mon = monitors(net, adj)
        hz, _, _ = hazards(net, adj)
        r["mon"] = len(mon)
        r["fam"] = fam
        rows.append(r)
        if hz and fam not in examples:
            st, gi, gj = hz[0]
            best = None
            for s0 in starts:
                if s0 is None:
                    continue
                tr = trace_to(net, s0, st)
                if tr is not None and (best is None or len(tr) < len(best[1])):
                    best = (s0, tr)
            examples[fam] = (f"{fam} {params}: in {fmt_state(net, st)} firing "
                             f"{net.gates[gi]['name']} disables {net.gates[gj]['name']}; from "
                             f"{fmt_state(net, best[0])}: {' '.join(best[1])}")
        if mon and (fam + "/mon") not in examples:
            examples[fam + "/mon"] = f"{fam} {params}: {mon[0][0]} on {mon[0][1]}"
    return rows, examples


# ------------------------------------------------------------------ (1) ------

def part1():
    rows, examples = [], []
    grid = []
    for merge in ("amerge", "merge"):
        for mode in ("fixed", "free"):
            for k in (1, 2):
                for LC in (0, 1, 2):
                    for LB in (0, 1, 2):
                        for LD in (1, 2):
                            for LB2 in (0, 1, 2):
                                LK = 1
                                if QUICK and (LC == 2 or LB2 == 2):
                                    continue
                                grid.append((merge, mode, k, LC, LB, LD, LK, LB2))
    for gi_, (merge, mode, k, LC, LB, LD, LK, LB2) in enumerate(grid):
        if os.environ.get("VERBOSE"):
            print("part1", gi_, len(grid), merge, mode, k, LC, LB, LD, LK, LB2, flush=True)
        net, segs = build_loop(k=k, merge=merge, mode=mode, LC=LC, LB=LB, LD=LD, LK=LK, LB2=LB2)
        x0 = sum(1 << (2 * i + 1) for i in range(k))
        g0 = reset_state(net, x0)
        try:
            adj = explore_from(net, [g0], limit=LIMIT)
        except RuntimeError:
            rows.append(dict(merge=merge, mode=mode, k=k, LC=LC, LB=LB, LD=LD, LK=LK, LB2=LB2,
                             gates=len(net.gates), states=f">{LIMIT}", good="", bad=0, hz=0, arb=0,
                             mon=0, steady=0, agree_dead=None, agree_reach=None, zbad=None,
                             skipped=True))
            continue
        dead, _, _ = terminal_dead(net, adj)
        linkmask = sum(1 << gi for gi in net.link_bit)
        good = [d for d in dead if d & linkmask == 0]
        bad = [d for d in dead if d & linkmask]
        hz, arb, exc = hazards(net, adj, exclude=set(net.arb_q) | set(net.env))
        mon = monitors(net, adj)
        row = dict(merge=merge, mode=mode, k=k, LC=LC, LB=LB, LD=LD, LK=LK, LB2=LB2,
                   gates=len(net.gates), states=len(adj), good=len(good), bad=len(bad),
                   hz=len(hz), arb=len(arb), mon=len(mon))
        # stage model of the iterating loop (entry exhausted, condition 1,
        # back edges selected), from every reachable steady gate state
        loop = [i for i in range(net.S) if i not in segs["E"]]
        sig = lambda nm: net.find(net.sig(nm))  # noqa: E731
        zero = [sig(s) for s in ("enc_r", "end_r", "enc_a", "end_a")]
        assume = {sig("enc_r"): 0, sig("end_r"): 0, sig("index"): 1}
        if "cond" in net.names:
            assume[sig("cond")] = 1
        feeders, fed, _ = stage_graph(net, assume)
        pos = {s: j for j, s in enumerate(loop)}
        F = [[pos[p] for p in feeders[s] if p in pos] for s in loop]
        D = [[pos[u] for u in fed[s] if u in pos] for s in loop]
        L = len(loop)

        def lproj(st):
            x = 0
            for j, s in enumerate(loop):
                if (st >> net.link_bit[s]) & 1:
                    x |= 1 << j
            return x

        def val(st, s):
            return net.const[s] if s in net.const else (st >> net.bit[s]) & 1

        def steady(st):
            if any((st >> net.link_bit[s]) & 1 for s in segs["E"]):
                return False
            if any(val(st, s) for s in zero):
                return False
            return mode == "fixed" or val(st, sig("cond")) == 1
        sadj, snenv = {}, {}
        for x in range(1 << L):
            succ = []
            for t in range(L):
                v = (x >> t) & 1
                if all(((x >> p) & 1) != v for p in F[t]) and all(((x >> u) & 1) == v for u in D[t]):
                    succ.append(x ^ (1 << t))
            sadj[x], snenv[x] = succ, len(succ)
        sres = scc_dp(sadj, lambda v: v, snenv)
        steady_states = [st for st in adj if steady(st)]
        if mode == "fixed":
            gnenv = {st: len(adj[st]) for st in adj}
            gres = scc_dp(adj, lproj, gnenv)
            agree_dead = agree_reach = 0
            zbad = 0
            for st in steady_states:
                gr, gd = gres[st]
                sr, sd = sres[lproj(st)]
                agree_dead += (gd != 0) == (sd != 0) and gd == sd
                agree_reach += gr == sr
                zbad += mg_tokenfree_cycle(L, F, lproj(st)) != (gd != 0)
            row.update(steady=len(steady_states), agree_dead=agree_dead,
                       agree_reach=agree_reach, zbad=zbad)
        else:
            row.update(steady=len(steady_states), agree_dead=None, agree_reach=None, zbad=None)
            # free mode: does every stuck terminal state have a token-free
            # cycle in the iterating loop's stage graph (Z(x)), i.e. would the
            # fixed-mode stage model have predicted it?
            pred = sum(1 for d in bad if mg_tokenfree_cycle(L, F, lproj(d)))
            row["bad_pred"] = pred
        # does the fixed-mode loop deadlock at all (from reset)?
        rows.append(row)
        for kind, lst in (("hazard", hz), ("monitor", mon), ("stuck", bad)):
            if lst and not any(e[0] == (kind, merge, mode) for e in examples):
                tgt = {"hazard": lambda: lst[0][0], "monitor": lambda: lst[0][2],
                       "stuck": lambda: lst[0]}[kind]()
                tr = trace_to(net, g0, tgt)
                if kind == "hazard":
                    what = (f"firing {net.gates[lst[0][1]]['name']} disables "
                            f"{net.gates[lst[0][2]]['name']}")
                elif kind == "monitor":
                    what = f"{lst[0][0]} on {lst[0][1]} (gate {net.gates[lst[0][3]]['name']})"
                else:
                    what = "stuck terminal state"
                examples.append(((kind, merge, mode),
                                 f"{merge} {mode} k={k} LC={LC} LB={LB} LD={LD} LK={LK} LB2={LB2}: "
                                 f"{what} in {fmt_state(net, tgt)}; trace from reset ({len(tr)} "
                                 f"firings): {' '.join(tr)}"))
    return rows, examples


def main():
    t0 = time.time()
    r1, e1 = part1()
    t1 = time.time()
    r23, e23 = part23()
    t2 = time.time()
    L = ["# Follow-up: arbitrated loop header, bdc_muxn, wide bd_ctree, FASTFALL (shard C)\n",
         f"Generated by `formal/tools/live/cells/run.sh` via run2.py ({'QUICK, ' if QUICK else ''}"
         f"part 1: {len(r1)} loops in {t1 - t0:.0f} s; parts 2-3: {len(r23)} runs in {t2 - t1:.0f} s). "
         "Model: explore2.py docstring.\n"]
    L.append("## (1) Loop header: control_merge (bdc_amerge2 or bd_merge) + bd_mux + two cond_brs\n")
    L.append("Start: physical reset with k tokens in a 2k-link entry reservoir (bd_c2n_set on its odd "
             "links, every other cell at its reset value; the arbiter's q comes up 1).  "
             "*good* = terminal states with every link 0 (all tokens left by the exit); *stuck* = "
             "terminal states with a link still 1.  *steady* = reachable states with the entry exhausted "
             "(fixed mode); there the gate model is compared with the stage model of the iterating loop "
             "(feeders traced with entry req = 0, index = 1, condition = 1).\n")
    hdr = ("| merge | mode | k | LC | LB | LD | LK | LB2 | gates | gate states | good end | stuck | "
           "hazards | arb. races | protocol/bundling viol. | steady states | dead agree | reach agree | "
           "Z wrong | stuck predicted by Z |")
    L.append(hdr)
    L.append("|" + "---|" * 20)
    for r in r1:
        L.append(f"| {r['merge']} | {r['mode']} | {r['k']} | {r['LC']} | {r['LB']} | {r['LD']} | {r['LK']} | "
                 f"{r['LB2']} | {r['gates']} | {r['states']} | {r['good']} | {r['bad']} | {r['hz']} | "
                 f"{r['arb']} | {r['mon']} | {r['steady']} | "
                 f"{'' if r['agree_dead'] is None else str(r['agree_dead']) + '/' + str(r['steady'])} | "
                 f"{'' if r['agree_reach'] is None else str(r['agree_reach']) + '/' + str(r['steady'])} | "
                 f"{'' if r['zbad'] is None else r['zbad']} | "
                 f"{str(r.get('bad_pred')) + '/' + str(r['bad']) if 'bad_pred' in r else ''} |")
    L.append("\n### Summary (part 1)\n")
    for merge in ("amerge", "merge"):
        for mode in ("fixed", "free"):
            sel = [r for r in r1 if r["merge"] == merge and r["mode"] == mode]
            if not sel:
                continue
            s = lambda k: sum(r[k] or 0 for r in sel)  # noqa: E731
            sk = sum(1 for r in sel if r.get("skipped"))
            sel = [r for r in sel if not r.get("skipped")]
            line = (f"- {merge} {mode}: {len(sel)} loops explored ({sk} skipped at the state limit {LIMIT}); loops with a stuck state "
                    f"{sum(1 for r in sel if r['bad'])}; hazards {s('hz')} (in "
                    f"{sum(1 for r in sel if r['hz'])} loops); protocol/bundling violations {s('mon')} "
                    f"(in {sum(1 for r in sel if r['mon'])} loops); arbitration races {s('arb')}")
            if mode == "fixed":
                line += (f"; steady states {s('steady')}, dead agree {s('agree_dead')}, reach agree "
                         f"{s('agree_reach')}, Z wrong {s('zbad')}")
            else:
                line += f"; stuck states predicted by Z(x) of the iterating loop {s('bad_pred')}/{s('bad')}"
            L.append(line)
    L.append("\n### Worked examples (part 1)\n")
    for _, e in e1:
        L.append(f"- {e}")
    L.append("\n## (2) bdc_muxn N = 3, bd_ctree N = 5 / 6; (3) FASTFALL request lines\n")
    L.append("Same method as RESULTS.md (fixed mode, every stage vector, consistent completion), plus "
             "the protocol monitor.\n")
    L.append("| family | runs | starts | deadlock starts | dead agree | reach agree | hazards | non-stage steps "
             "| protocol viol. | Z wrong | rest | ringfloor right |")
    L.append("|---|---|---|---|---|---|---|---|---|---|---|---|")
    fams = []
    for r in r23:
        if r["fam"] not in fams:
            fams.append(r["fam"])
    for f in fams:
        sel = [r for r in r23 if r["fam"] == f]
        s = lambda k: sum(r[k] or 0 for r in sel)  # noqa: E731
        L.append(f"| {f} | {len(sel)} | {s('starts')} | {s('dead')} | {s('agree_dead')} | {s('agree_reach')} | "
                 f"{s('hazards')} | {s('sim_bad')} | {s('mon')} | {s('z_bad')} | {s('rest')} | {s('rest_ok')} |")
    L.append("\n### Worked examples (parts 2-3)\n")
    for e in e23.values():
        L.append(f"- {e}")
    L.append("")
    with open(os.path.join(HERE, "RESULTS2.md"), "w") as fh:
        fh.write("\n".join(L) + "\n")
    print(f"wrote RESULTS2.md: part 1 {len(r1)} loops ({t1 - t0:.0f} s), parts 2-3 {len(r23)} runs "
          f"({t2 - t1:.0f} s)")


if __name__ == "__main__":
    main()
