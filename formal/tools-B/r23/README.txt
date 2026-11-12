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
