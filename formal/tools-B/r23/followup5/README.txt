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

Follow-up 2 (re-anchoring; 2026-11-09):
 tocc/datal_t.py  env REANCH=1: at a re-open (chain[-1] = H) the latch's D claim is requested from the start of D's
                  own simulated stable value (comb claims split into segment chains, joined by ChainOK comb segments);
                  env LGTOPOFF=1: the guard-optimal end choice (GTOP) is not applied to a latch's internal phase windows.
 tocc/h_ra_c*.{log,pkl}   UPREL+UPJOIN+JOINANC+REANCH (12,18); tocc/h_rag_c*  + LGTOPOFF (12,18)
 tocc/trU.py, trU_c0.txt  U->H trace of X36Y63.B6/X36Y68.B6; probe.py, probe2.py; dbgA2.py (U' start anchoring)
 tocc/advplan2.py, advplan3.py, adv2/, adv3/   setup-race and concurrent-branch adversarial sims
 tocc175/h_rag_c*.{log,pkl}, ana2_rag_c*.log, chains175_*   (17,5) with the same configuration, roots

Follow-up 3 (soundness fix + bank re-open; 2026-11-09):
 tocc/ao.py       SEPIV1=1 (default): sepAny drops form-(iv) separations with d < 1 (SepOKA).
 tocc/datal_t.py  ANEG=1: a claim's start offset a may be negative (Lean Claim.a : Int); window() no longer clamps
                  max(0, reqs). XFIRST=1 (cover-drop order by recency) tried, worse, not used.
 tocc/s_best_c*   UPREL+UPJOIN+JOINANC+REANCH+LGTOPOFF, sound Seps: 48/48 failing
 tocc/s_an_c*     same + ANEG: 0/0;  tocc/s_an2_c*  UPREL+UPJOIN+JOINANC+LGTOPOFF+ANEG (no REANCH): 0/0
 tocc/s_xf_c*     XFIRST experiment (78/78)
 bank_c{0,1}.json (tocc/bank.py)  bank latches at each X30Y76.A6 opening: Q old/new, D at the open, D flips
 tocc/tern.py     ternary (Kleene) check of the bank D cones with the changing / all bank latches X
 tocc/leaves.py   D-cone leaves changing near each opening; tocc/multi.py, probe3.py (why the D claim anchors at the open)
 tocc/advplan4.py, adv4/   bank-open adversary (enable path fast, everything else at max delay)

Follow-up 4 (CovTimeU; ANEG withdrawn as unsound — Lean needs 0 <= c.a):
 tocc/datal_t.py  COVUP=1: when no cover start event is a Sep-common anchor, try the COVUPN (6) latest common causal
                  ancestors e0 of the cover start events; each cover's start by Sep (hi+w.a-d) or by CovTimeU
                  (hi+w.a+Up(e0->w.A), needs hi+w.a >= 1); c.a = max(0, ...). COVUPSCORE=1 (consumer-aware choice) tried.
 tocc/cu_c*   UPREL+UPJOIN+JOINANC+LGTOPOFF+COVUP: 42/30;  tocc/cu0_c*  same without COVUP: 60/48
 tocc/cus_c*  + COVUPSCORE, COVUPN=12: 42/30;  tocc/cur_c*  COVUP + REANCH: 18/18
 tocc/ana2_cu_c*.log   roots; tocc175/cur_c*  (17,5) with COVUP+REANCH: 156/126

Follow-up 5 (failing claim obligations):
 tocc/datal_t.py  now also records per-claim failing obligations (FAILS), every loop-cover CovTime check against FINAL
                  windows (LOOPC: pending covers and previous-pass covers, incl. the CovTimeU form), DEPSMAP, PASSLOG.
 tocc/obl.py      counts failing items by kind, guards blocked per kind (dependency closure), loop-cover classes.
 tocc/o_p1_c*     COVUP config NPASS=1; o_p10_c*  NPASS=10 (converges: c0 pass 4, c1 pass 2); o_rp10_c*  + REANCH NPASS=10
