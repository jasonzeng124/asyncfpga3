K = 32 slices of [0, 3/8] for pair (17,5) (shard B subagent, 2026-11-10; UNTRUSTED Python measurements).
Same pipeline and configuration as ../pairs/README.txt (run3.sh), only the slice width changes (1/32 instead of 1/16).
Question: do the 12 slices [i/32,(i+1)/32], i = 0..11, which cover [0,3/8] where the (17,5) K = 16 data layer failed, pass?

SHORT ANSWER (g = 1, kappa = 0, one midpoint run per slice): YES, all 12 pass.
  Control: 0 final-round LCheckXA failures on every slice. Data layer: 0 / 406 guards failing, 0 failing claim items
  (obl.py, incl. the latch-phase audit (failing 0) and loop covers (0 failing)), 0 latch-claim truncations, lchk
  upFormB/sepFormB 0/0, fixpoint reached (3-4 passes). Simulated output 1 = gcd(17,5) on every slice.
  Combined with ../pairs (K = 16 slices [3/8,1] pass), the cover {12 slices of width 1/32 on [0,3/8]} + {10 slices of
  width 1/16 on [3/8,1]} passes for (17,5) in this untrusted measurement. No failing slice, so there are no binding roots to report.
  The K=16 H->U' bank-latch roots (X30Y76.D6 etc., -927..-108 ps) and p175_05's U'->T roots no longer appear.

COMMANDS (scratch /tmp/claude-0/slice3; reuses /tmp/claude-0/slice/src and /tmp/claude-0/slice/base)
 mk3.sh NAME C1 C2  copy slice/src/*.py into slice3/NAME with the /tmp paths patched, then BUILD a fresh slice model:
                    C1=.. C2=.. python3 build.py base/net.json base/bnd.json model.pkl (all 12: "mid clamped arcs 0").
 run3.sh NAME A B   = ../pairs/run3.sh with two changes: the scratch dir is slice3, and the disk wait is >= 6 GB (was 4);
                    and after the diagnostics it deletes data_c*.pkl and every other pickle > 50 MB unconditionally.
                    Memory wait >= 6 GB as before. Same sim/data/ao/rundt env (B's final config, NPASS=10).
 q32.sh             builds the 12 models serially, then runs the 12 slices with xargs -P 2 (at most 2 at once).
 tab3.py DIRS       = ../pairs/tab2.py reading /tmp/claude-0/slice3. table.md is its output.
 logs/NAME/         build, sim, data, ao, datal, obl, ana2, gsum logs of each slice. Every datal.log ends with its
                    [lchk] lines and "relative-clause stats".

RUN NOTES
 - Queue ran 19:07-22:15 UTC. No retries: no datal_killed*.log, no FAILED, no Traceback in any log.
 - Shard B main reported a container restart at ~20:06 UTC. In this container the queue processes (started 19:07)
   were still running at 20:07 (p32_02/03 in rundt.py); only one of my wait commands was killed (exit 137). So no
   slice was rerun; p32_02 and p32_03 completed in the original run with complete logs.
 - Scratch peaked at ~3.4 GB (two data_c0.pkl of ~1.6-1.7 GB). Now ~120 MB (no pickle > 50 MB remains).
 - The "guards failing 30" lines in datal.log are pass 0 (initial windows), and "failures 7886" in ao.log is round 0.
   The final pass and round are 0.

RESULTS (columns as in ../pairs/README.txt)
| slice [c1,c2] | dir | sim out (want) | control LCheckXA fails | guards failing | failing claim items | truncations | lchk up/sep | data passes | data min |
|---|---|---|---|---|---|---|---|---|---|
| [0/1, 1/32] | p32_00 | 1 (1) | 0 | 0 / 406 | 0 | 0 | 0/0 | 4 | 15 |
| [1/32, 1/16] | p32_01 | 1 (1) | 0 | 0 / 406 | 0 | 0 | 0/0 | 4 | 15 |
| [1/16, 3/32] | p32_02 | 1 (1) | 0 | 0 / 406 | 0 | 0 | 0/0 | 4 | 15 |
| [3/32, 1/8] | p32_03 | 1 (1) | 0 | 0 / 406 | 0 | 0 | 0/0 | 4 | 15 |
| [1/8, 5/32] | p32_04 | 1 (1) | 0 | 0 / 406 | 0 | 0 | 0/0 | 4 | 15 |
| [5/32, 3/16] | p32_05 | 1 (1) | 0 | 0 / 406 | 0 | 0 | 0/0 | 4 | 15 |
| [3/16, 7/32] | p32_06 | 1 (1) | 0 | 0 / 406 | 0 | 0 | 0/0 | 4 | 14 |
| [7/32, 1/4] | p32_07 | 1 (1) | 0 | 0 / 406 | 0 | 0 | 0/0 | 4 | 14 |
| [1/4, 9/32] | p32_08 | 1 (1) | 0 | 0 / 406 | 0 | 0 | 0/0 | 4 | 15 |
| [9/32, 5/16] | p32_09 | 1 (1) | 0 | 0 / 406 | 0 | 0 | 0/0 | 4 | 15 |
| [5/16, 11/32] | p32_10 | 1 (1) | 0 | 0 / 406 | 0 | 0 | 0/0 | 3 | 13 |
| [11/32, 3/8] | p32_11 | 1 (1) | 0 | 0 / 406 | 0 | 0 | 0/0 | 3 | 13 |

WHAT IS NOT SHOWN
 - Nothing is Lean-checked; these are B's/C's untrusted Python models of the Lean rules. lchk only re-checks emitted Sep/Up.
 - One midpoint run per slice, one simulation per slice (R = 40000); g = 1, kappa = 0; pair (17,5) only.
 - Slices [3/8,1] were not rerun here; the claim of a full cover relies on ../pairs (K = 16) results.
 - That the slice windows cover every corner in the slice is build.py's exact-Fraction arithmetic plus the Lean-side
   claim (Formal/Cells/CornerSlice.lean), not checked here. Whether width 1/16 would pass on parts of [0,3/8] with a
   different split (e.g. only near c = 0) was not tested.
 - Pickles were deleted, so further probes would need reruns.
