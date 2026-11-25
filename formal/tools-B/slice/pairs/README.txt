Uniform K = 16 corner slices for pairs (17,5) and (8,12) (shard B subagent, 2026-11-10; UNTRUSTED Python measurements).
Same pipeline and configuration as ../README.txt (pair (12,18)), only the simulated pair changes.
Question: does the uniform 16-slice cover [i/16,(i+1)/16] that passed for (12,18) also pass for (17,5) and (8,12)?

SHORT ANSWER (g = 1, kappa = 0, one midpoint run per slice):
  (8,12):  ALL 16 slices pass. Control 0 local-check failures, data layer 0/284 guards, 0 failing claim items,
           lchk 0/0. Simulated output 4 = gcd on every slice.
  (17,5):  control passes on all 16 slices (0 LCheckXA failures). The DATA LAYER FAILS on the 6 slices covering
           [0, 3/8] (78 or 60 of 406 guards). The 10 slices covering [3/8, 1] pass everything (0/406, 0 items, lchk 0/0).
           So uniform K = 16 is NOT a passing cover for (17,5); finer slices near c = 0 were not tried.
  (1071,462): NOT run. Two slices had started, but per the coordinator they were stopped before any data layer finished.

------------------------------------------------------------------------------------------------------------------------
COMMANDS (scratch /tmp/claude-0/slice2; reuses /tmp/claude-0/slice/src and /tmp/claude-0/slice/base from ../README.txt)
 mk2.sh NAME II     copy slice/src/*.py into slice2/NAME with the /tmp paths patched, and copy model.pkl + build.log from
                    /tmp/claude-0/slice/k16_II. The slice model is pair-independent: build.py reads only net.json, bnd.json
                    and C1/C2. The (17,5) [0,0] sanity slice s175_00 was built fresh with C1=0 C2=0 build.py.
 run3.sh NAME A B   sim.py 0 A B (R=40000) -> data.py 0 -> ao.py 0 (control, C's default flags, 3 rounds) -> rundt.py 0
                    with B's final env (CRELUP=1 REL=1 RELD=99 RELK=16 RELTRY=64 UPJOIN=1 JOINANC=1 LGTOPOFF=1 COVUP=1
                    COVMEET=1 MUXX=1 XOPT=1 ESPLIT=1 ENDFIX=2 LCHK=1 NPASS=10) -> obl.py, ana2.py, gsum.py.
                    Before each heavy step it waits for >= 6 GB MemAvailable and >= 4 GB free disk. It redoes data.py if
                    data.py did not finish and retries the data layer up to 3x. After the diagnostics it deletes
                    data_c0.pkl (1.5-1.9 GB per slice), plus the ao and dl pickles of slices that pass fully.
 run2.sh            the first version, without disk hygiene; it ran p175_00..09.
 q3.sh A B PFX      the 16 slices of one pair, at most 2 at once (xargs -P 2), skipping slices that have DONE.
 chain*.sh          the queues actually used. q2.sh is the first queue script.
 tab2.py DIRS       one table row per slice. Columns as in ../tab.py, plus total guards per pair and data-layer minutes.
 logs/NAME/         build, sim, data, ao, datal, obl, ana2 and gsum logs of every reported slice.
                    Every reported datal.log ends with its [lchk] lines and "relative-clause stats".

INCIDENTS
 - At about 13:30 the session disk filled up (data_c0.pkl at about 1.8 GB per slice). p175_10's data.py died with ENOSPC.
   The coordinator deleted data_c0.pkl in p175_00..05; those runs had already finished, so nothing was lost.
   Slices p175_00..09 all finished before 13:30 with complete logs.
 - p175_10's next attempt (about 13:55) left data_c0.pkl short (1.48 GB). The data layer then hit EOFError at the
   pickle load, 3 times, so that run has no lchk lines. Its logs are kept in /tmp/claude-0/slice2/p175_10/bad1.
   p175_10 was rerun from scratch at 17:47 (rerun: 0/406, lchk 0/0); its row is from the rerun.
 - No OOM kills among the reported runs. The two (1071,462) runs that started were killed by me and are not reported.

------------------------------------------------------------------------------------------------------------------------
RESULTS (columns as in ../README.txt: final-round LCheckXA failures with no justified RT edge; failing guards / total;
 failing claim items = obl.py count incl. latch-phase audit + loop covers; latch-claim truncations; lchk upFormB/sepFormB
 failures; data passes (< 10 = fixpoint reached); data-layer wall minutes. sim out = simulated output (want = gcd))

PAIR (17,5)
| slice [c1,c2] | dir | sim out (want) | control LCheckXA fails | guards failing | failing claim items | truncations | lchk up/sep | data passes | data min |
|---|---|---|---|---|---|---|---|---|---|
| [0/1, 0/1] | s175_00 (sanity) | 1 (1) | 0 | 0 / 406 | 0 | 0 | 0/0 | 4 | 17 |
| [0/1, 1/16] | p175_00 | 1 (1) | 0 | 78 / 406 | 0 | 2123 | 0/0 | 5 | 17 |
| [1/16, 1/8] | p175_01 | 1 (1) | 0 | 78 / 406 | 0 | 2098 | 0/0 | 5 | 17 |
| [1/8, 3/16] | p175_02 | 1 (1) | 0 | 78 / 406 | 0 | 2001 | 0/0 | 6 | 19 |
| [3/16, 1/4] | p175_03 | 1 (1) | 0 | 60 / 406 | 0 | 1821 | 0/0 | 6 | 19 |
| [1/4, 5/16] | p175_04 | 1 (1) | 0 | 60 / 406 | 0 | 1773 | 0/0 | 6 | 19 |
| [5/16, 3/8] | p175_05 | 1 (1) | 0 | 60 / 406 | 0 | 1417 | 0/0 | 10 (NOT converged) | 25 |
| [3/8, 7/16] | p175_06 | 1 (1) | 0 | 0 / 406 | 0 | 0 | 0/0 | 3 | 14 |
| [7/16, 1/2] | p175_07 | 1 (1) | 0 | 0 / 406 | 0 | 0 | 0/0 | 3 | 14 |
| [1/2, 9/16] | p175_08 | 1 (1) | 0 | 0 / 406 | 0 | 0 | 0/0 | 3 | 14 |
| [9/16, 5/8] | p175_09 | 1 (1) | 0 | 0 / 406 | 0 | 0 | 0/0 | 3 | 14 |
| [5/8, 11/16] | p175_10 (rerun) | 1 (1) | 0 | 0 / 406 | 0 | 0 | 0/0 | 3 | 13 |
| [11/16, 3/4] | p175_11 | 1 (1) | 0 | 0 / 406 | 0 | 0 | 0/0 | 3 | 14 |
| [3/4, 13/16] | p175_12 | 1 (1) | 0 | 0 / 406 | 0 | 0 | 0/0 | 3 | 15 |
| [13/16, 7/8] | p175_13 | 1 (1) | 0 | 0 / 406 | 0 | 0 | 0/0 | 3 | 15 |
| [7/8, 15/16] | p175_14 | 1 (1) | 0 | 0 / 406 | 0 | 0 | 0/0 | 3 | 15 |
| [15/16, 1/1] | p175_15 | 1 (1) | 0 | 0 / 406 | 0 | 0 | 0/0 | 3 | 15 |
 Sanity: s175_00's datal.log is identical to tools-B/r23/final/175_c0.log (corner 0, (17,5)) except for one line, the
 [audit] line that the later audited config adds (audit failing 0). Its control result is 0 failures.

PAIR (8,12)
| slice [c1,c2] | dir | sim out (want) | control LCheckXA fails | guards failing | failing claim items | truncations | lchk up/sep | data passes | data min |
|---|---|---|---|---|---|---|---|---|---|
| [0/1, 1/16] | p812_00 | 4 (4) | 0 | 0 / 284 | 0 | 0 | 0/0 | 3 | 6 |
| [1/16, 1/8] | p812_01 | 4 (4) | 0 | 0 / 284 | 0 | 0 | 0/0 | 4 | 8 |
| [1/8, 3/16] | p812_02 | 4 (4) | 0 | 0 / 284 | 0 | 0 | 0/0 | 4 | 8 |
| [3/16, 1/4] | p812_03 | 4 (4) | 0 | 0 / 284 | 0 | 0 | 0/0 | 3 | 6 |
| [1/4, 5/16] | p812_04 | 4 (4) | 0 | 0 / 284 | 0 | 0 | 0/0 | 4 | 8 |
| [5/16, 3/8] | p812_05 | 4 (4) | 0 | 0 / 284 | 0 | 0 | 0/0 | 3 | 7 |
| [3/8, 7/16] | p812_06 | 4 (4) | 0 | 0 / 284 | 0 | 0 | 0/0 | 3 | 6 |
| [7/16, 1/2] | p812_07 | 4 (4) | 0 | 0 / 284 | 0 | 0 | 0/0 | 3 | 6 |
| [1/2, 9/16] | p812_08 | 4 (4) | 0 | 0 / 284 | 0 | 0 | 0/0 | 3 | 6 |
| [9/16, 5/8] | p812_09 | 4 (4) | 0 | 0 / 284 | 0 | 0 | 0/0 | 3 | 6 |
| [5/8, 11/16] | p812_10 | 4 (4) | 0 | 0 / 284 | 0 | 0 | 0/0 | 3 | 6 |
| [11/16, 3/4] | p812_11 | 4 (4) | 0 | 0 / 284 | 0 | 0 | 0/0 | 3 | 6 |
| [3/4, 13/16] | p812_12 | 4 (4) | 0 | 0 / 284 | 0 | 0 | 0/0 | 3 | 6 |
| [13/16, 7/8] | p812_13 | 4 (4) | 0 | 0 / 284 | 0 | 0 | 0/0 | 3 | 6 |
| [7/8, 15/16] | p812_14 | 4 (4) | 0 | 0 / 284 | 0 | 0 | 0/0 | 3 | 6 |
| [15/16, 1/1] | p812_15 | 4 (4) | 0 | 0 / 284 | 0 | 0 | 0/0 | 3 | 6 |

------------------------------------------------------------------------------------------------------------------------
ROOTS OF THE (17,5) FAILURES (data layer only; ana2.py = deepest truncation on each failing guard's claim-end chain;
 tuple = (latch node, link, c1.B event, c2.A event, margin ps); "None" = no bound found)
 Every failing guard is an END failure ("no Sep E -> claim.B", margin -inf in gsum) on data nodes SLICE_X38Y78.A6
 (54 / 36 guards) and SLICE_X37Y68.B6 (24). No failing claim item is a finite-margin CovTime/ChainOK miss: obl.py
 counts 0 items and 0 failing loop covers, and the latch-phase audit fails 0. The failures are latch-claim truncations,
 mostly at U'->T (e.g. p175_00: H->U' 360, U'->T 1705, T->U 58).
  p175_00 [0,1/16]:    H->U' at X30Y76.D6 -927 (36 guards), X30Y75.A6 -792 (18), X31Y76.A5 -510 (12), X31Y76.B6 -789 (12)
  p175_01 [1/16,1/8]:  same links: -621, -477, -172, -470
  p175_02 [1/8,3/16]:  X30Y76.D6 -430, X30Y75.A6 -276, X31Y76.A6 -76, X31Y76.B6 -267
  p175_03 [3/16,1/4]:  X30Y76.D6 -141 (48), X30Y76.B6 -60 (12)
  p175_04 [1/4,5/16]:  X30Y76.D6 -66 (48), X30Y75.D5 -108 (12)
   On all of 00-04: c1.B = SLICE_X30Y76.A6(4) (the register-bank enable, re-open) and c2.A = SLICE_X38Y15.C6(4).
   The H->U' link (re-latch: new D valid before the re-open read) misses by an amount that shrinks steadily toward
   c = 3/8. These are the same bank-enable latches as the (12,18) K=8 roots (c1.B = X30Y76.A6), here in the H->U' phase.
  p175_05 [5/16,3/8]:  different root: U'->T at X34Y92.B5 (30 guards; c1.B = X30Y76.A6(4), c2.A = X34Y92.A6(6)) and
   X22Y86.B5 (30; c2.A = X22Y87.A6(4)), margin None (no Sep/Up bound found). The window fixpoint was NOT reached in
   10 passes: 18407 windows changed on every pass from pass 2 to pass 9, which looks like a 2-cycle or a stall, not
   checked. The roots were measured at non-final windows.
 The slices are equal-width, and the (17,5) corner-0 run itself passes (sanity slice). So the failures look like
 width effects near c = 0, as for (12,18) at K <= 8. Narrower slices on [0,3/8] were NOT run. Whether, for example,
 K = 32 there passes is open.

WHAT IS NOT SHOWN
 - Nothing is Lean-checked. The checks are B's and C's untrusted Python models of the Lean rules; lchk re-checks only the
   emitted Sep/Up entries. The slice nets are not emitted.
 - One midpoint run per slice, one simulation per pair (R = 40000); g = 1, kappa = 0.
 - (1071,462) was not run. A finer cover for (17,5) on [0,3/8] was not run. A [0,0] sanity slice was run only for (17,5).
 - That the slice windows cover every corner c in the slice is the build.py arithmetic (exact Fractions, ceil/floor)
   plus the Lean side's claim (Formal/Cells/CornerSlice.lean), not checked here.
 - Root attributions (ana2 deepest truncation) are a heuristic link, not proven causes. p175_05's roots come from
   non-converged windows.
 - All pickles over 1 MB in /tmp/claude-0/slice2 (data, ao, dl, model) were deleted after the runs (disk limit),
   so only the logs remain (here under logs/, and in /tmp/claude-0/slice2/*/). Further probes of the (17,5) roots
   (dsep.py, sepchk.py) would need those slices rerun.
