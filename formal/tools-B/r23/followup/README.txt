bsub1 (shard B subagent, 2026-11-09; UNTRUSTED Python). Latch-chain truncations in C's datal.py, pair (12,18), g=1, kappa=0.
Working copy of formal/tools/tocc in tocc/ (paths patched /tmp/claude-0/tocc -> /tmp/claude-0/bsub1/tocc).
Inputs: tools/cview/lean2json.py on Formal/Target/NetPS -> net.json (deleted, 39 MB; regenerate) + tocc/bnd.json.
Pipeline: build.py -> sim.py c 12 18 (R=40000) -> data.py c -> datal.py c (defaults, HOLDX 20000, NPASS 4).
 tocc/datal_c{0,1}.log      reproduction: 82 / 46 failing guards of 264 (= C's 15:21 numbers exactly)
 tocc/datal_t.py            instrumented datal (made by mkpatch.py): records every truncation (TRUNC), claim end
                            binding pins; env NOTRUNC=<kinds>, NOTRUNCQ=<latches> suppress truncation (counterfactual)
 trunc_c*.json/.txt         (ana.py) every distinct truncation event: latch, kind, enable, D pins, close, D-claim end,
                            D's next change in the run (gap), guards on its claim-end chain
 trunc3_c*.json             (ana3.py) union margin by Sep / Up(c1.B->c2.A) / Up-Sep via common ancestor / run
 trunc4_c*.json/.txt        (ana4.py) root vs inherited truncation; for roots, why the bound fails (Up blocker event)
 table_c*.tsv               (merge.py) one row per truncation event incl. B670 kappa
 chains_c*.txt, roots_c*.txt (ana2.py) claim-end binding chain of every failing guard; guards grouped by root
 guards_c*.txt              failing-guard sets under counterfactuals (dt_nouh, dt_noall, cf_* pickles in tocc/)
 adv_summary.txt            adversarial sims (simx.py; ADV specs tocc/adv_*.json from advplan.py) + hazchk + holdchk.py
 latch_enables.json         enable source -> latches (from classify.LATCH)

Follow-up (relative Up clause + chain joins):
 tocc/ao.py        my copy, env UPREL=1: UpOKA relative clause (relbound: bases = 8 latest common ancestors of p and e0,
                   Up0 without the clause, Sep by forms ii/iii), Up allowed for events ranked up to UPPRE=3000 before e0,
                   min over applicable disjuncts; sep23 tables cached per source (results identical in base mode).
                   ao_orig.py = previous copy.
 tocc/datal_t.py   env UPJOIN=1 (ChainUpOK Up join, 1 <= c2.a), JOINANC=1 (JoinAnc via 10 latest common ancestors).
 tocc/g_{rel,relup,relupanc}_c{0,1}.{log,pkl}   (12,18) runs, NPASS=1; base = tocc/datal_t_c*.pkl (NPASS=4; NPASS=1 identical counts)
 gsum_c{0,1}.txt   (fsum.py) failing guards, truncations by kind and class (A/B/C/O), joins by form
 tocc/dbgup.py, dbgj.py   Up diagnostics (X34Y92.C5 link; why the Up join never fires)
 tocc175/          same tools for pair (17,5): g_base_c*, g_relupanc_c* (.log/.pkl), gsum175_c*.txt
 (f_*.pkl in tocc/ are from an earlier, buggy relative-clause version: ignore)
