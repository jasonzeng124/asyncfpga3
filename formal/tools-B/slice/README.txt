Corner slices for the (12,18) one-pair certificate (shard B subagent, 2026-11-10; UNTRUSTED Python measurements).
Question: split the corner range [0,1] into slices [c1,c2]; per slice ONE integer net (per arc lo = ceil(lerp(fmin,smin,c1)),
hi = floor(lerp(fmax,smax,c2)), summed per composite pin route) and ONE midpoint run. For which K do both C's control
certificate (ao.py local checks) and B's final data-layer builder (datal_t.py, final config) pass on every slice?

SHORT ANSWER (pair (12,18), g = 1, kappa = 0; one midpoint run per slice):
  K = 1, 2, 4: FAIL on every slice.  K = 8: FAIL on [0,1/8], [1/8,1/4] (control + data) and [1/4,3/8] (control only);
  the 5 slices from 3/8 to 1 pass.  K = 16: ALL 16 slices pass (control 0 local-check failures; data layer 0/264
  guards, 0 failing claim items incl. the latch-phase audit and loop covers, lchk 0/0, fixpoint reached).
  COVER: the 11 slices [i/16,(i+1)/16] for i = 0..5 plus [3/8,1/2],[1/2,5/8],[5/8,3/4],[3/4,7/8],[7/8,1] were each
  measured to pass everything (subset of the K=16 and K=8 runs). Uniform K = 12 was not run.

------------------------------------------------------------------------------------------------------------------------
PIPELINE (scratch /tmp/claude-0/slice; nothing under formal/tools or formal/lean edited)
 inputs   python3 formal/tools/cview/lean2json.py formal/lean/Formal/Target/NetPS base/net.json base/bnd.json
          (187258 nodes, 186873 gates; every arc has fmin<=smin, fmax<=smax, so loC/hiC grow with c)
 copies   src/: formal/tools/tocc/{build,classify,sim,data,cert,lcheck,timing}.py, ao.py = tools-B/r23/x4/ao.py
          (B's copy; SEP23TAB fix, SEPIV1), datal_t.py = tools-B/r23/final/datal_t.py, rundt.py = tools-B/r23/x4/rundt.py.
          relup.py / lchk.py are exec'd read-only from formal/tools/tocc/r1b (as datal_t.py does).
 mkslice.sh NAME C1 C2   copy src/*.py into /tmp/claude-0/slice/NAME with the hard-coded /tmp paths patched, then
          C1=.. C2=.. python3 build.py net.json bnd.json model.pkl   (slice mode, diff: slice_build.diff)
 runslice3.sh NAME  sim.py 0 12 18 (R=40000) -> data.py 0 -> ao.py 0 (control; default flags = C's final
          --cyc --causeanc --prevanc + dcp, 3 rounds) -> rundt.py 0 with B's final env
          CRELUP=1 REL=1 RELD=99 RELK=16 RELTRY=64 UPJOIN=1 JOINANC=1 LGTOPOFF=1 COVUP=1 COVMEET=1 MUXX=1 XOPT=1
          ESPLIT=1 ENDFIX=2 LCHK=1 NPASS=10   (= tools-B/r23/final/queue12.sh config, incl. the audit of 16:5x)
          -> diag.sh (obl.py, ana2.py from tools-B/r23 copied with paths patched; gsum.py).  It waits for 6 GB free
          memory and retries the data layer if it was OOM-killed (4 runs were killed once by concurrent Lean builds
          and rerun; every reported log ends with the lchk lines). queue3.sh: at most 2 slices at once.
 ctrlonly.sh  sim + data + ao only (control prescan of K=8 and K=16).
 summ.py / tab.py   log summaries; ctrlroots.py: TO rows lowered at the reader of each remaining control failure.
 pinarcs.py: per-arc route of a pin and need(c1,c2) of a TO row.  dsep.py: datal_t's own sep/upq + JoinAnc terms.
 latchcmp.py, claimat.py, sepchk.py: claim / Sep probes used for the roots below.
 Every slice is run with corner argument c = 0; in slice mode build.py stores the slice window under BOTH keys 0
 and 1, so the corner argument only labels files/logs.

SLICE MODE (build.py; full diff in slice_build.diff)
 per arc:  lo = ceil(lerp(fmin,smin,C1)),  hi = floor(lerp(fmax,smax,C2)),
           mid = floor((lerp(fmin,smin,CM) + lerp(fmax,smax,CM)) / 2) clamped to [lo,hi], CM = (C1+C2)/2,
 exact Fractions; pin window = (sum lo, sum hi, sum mid) over the composite route (copy chain), as in build.py.
 DEVIATION from the brief: mid uses floor, not round, so that [0,0] and [1,1] reproduce build.py's corner midpoints
 ((fmin+fmax)//2) exactly. The clamp never fired (0 clamped arcs on every slice).

SANITY
 [0,0] (s00): model windows identical to build.py corner 0 on all pins; ao.log identical to C's ao3_c0.txt (minus
   timings); datal.log byte-identical to tools-B/r23/final/1218_au_c0.log.
 [1,1] (s11): windows identical to corner 1; datal.log identical to 1218_au_c1.log except the "[c=0]" label (2 lines).
 numpy 2.4.6 had to be pip-installed (the fresh container had none).

------------------------------------------------------------------------------------------------------------------------
RESULTS (columns: final-round LCheckXA local-check failures with no justified RT edge; failing guards of 264;
 failing claim items = obl.py count of failing ChainOK/JoinAnc/comb-segment links + latch-phase CovTime audit + loop
 covers at the final windows; latch-claim truncations; lchk upFormB/sepFormB failures; data passes; every run's
 simulated output = 6 = gcd(12,18))
| slice [c1,c2] | dir | sim out | control LCheckXA fails | guards failing | failing claim items | truncations | lchk up/sep | data passes |
|---|---|---|---|---|---|---|---|---|
| [0/1, 0/1] | s00 | 6 | 0 | 0 / 264 | 0 | 0 | 0/0 | 3 |
| [1/1, 1/1] | s11 | 6 | 0 | 0 / 264 | 0 | 0 | 0/0 | 3 |
| [1/2, 1/2] | s05 | 6 | 0 | 0 / 264 | 0 | 0 | 0/0 | 3 |
| [0/1, 1/1] | k1a | 6 | 8 | 112 / 264 | 4 | 2064 | 0/0 | 3 |
| [0/1, 1/2] | k2a | 6 | 2 | 47 / 264 | 516 | 1140 | 0/0 | 10 |
| [1/2, 1/1] | k2b | 6 | 1 | 42 / 264 | 0 | 1050 | 0/0 | 3 |
| [0/1, 1/4] | k4a | 6 | 1 | 42 / 264 | 0 | 1163 | 0/0 | 5 |
| [1/4, 1/2] | k4b | 6 | 1 | 42 / 264 | 0 | 1104 | 0/0 | 3 |
| [1/2, 3/4] | k4c | 6 | 1 | 42 / 264 | 0 | 1021 | 0/0 | 3 |
| [3/4, 1/1] | k4d | 6 | 1 | 30 / 264 | 0 | 852 | 0/0 | 3 |
| [0/1, 1/8] | k8a | 6 | 1 | 42 / 264 | 0 | 1023 | 0/0 | 4 |
| [1/8, 1/4] | k8b | 6 | 1 | 30 / 264 | 0 | 817 | 0/0 | 4 |
| [1/4, 3/8] | k8c | 6 | 1 | 0 / 264 | 0 | 0 | 0/0 | 4 |
| [3/8, 1/2] | k8d | 6 | 0 | 0 / 264 | 0 | 0 | 0/0 | 3 |
| [1/2, 5/8] | k8e | 6 | 0 | 0 / 264 | 0 | 0 | 0/0 | 3 |
| [5/8, 3/4] | k8f | 6 | 0 | 0 / 264 | 0 | 0 | 0/0 | 3 |
| [3/4, 7/8] | k8g | 6 | 0 | 0 / 264 | 0 | 0 | 0/0 | 3 |
| [7/8, 1/1] | k8h | 6 | 0 | 0 / 264 | 0 | 0 | 0/0 | 3 |
| [0/1, 1/16] | k16_00 | 6 | 0 | 0 / 264 | 0 | 0 | 0/0 | 3 |
| [1/16, 1/8] | k16_01 | 6 | 0 | 0 / 264 | 0 | 0 | 0/0 | 3 |
| [1/8, 3/16] | k16_02 | 6 | 0 | 0 / 264 | 0 | 0 | 0/0 | 4 |
| [3/16, 1/4] | k16_03 | 6 | 0 | 0 / 264 | 0 | 0 | 0/0 | 3 |
| [1/4, 5/16] | k16_04 | 6 | 0 | 0 / 264 | 0 | 0 | 0/0 | 4 |
| [5/16, 3/8] | k16_05 | 6 | 0 | 0 / 264 | 0 | 0 | 0/0 | 3 |
| [3/8, 7/16] | k16_06 | 6 | 0 | 0 / 264 | 0 | 0 | 0/0 | 3 |
| [7/16, 1/2] | k16_07 | 6 | 0 | 0 / 264 | 0 | 0 | 0/0 | 3 |
| [1/2, 9/16] | k16_08 | 6 | 0 | 0 / 264 | 0 | 0 | 0/0 | 3 |
| [9/16, 5/8] | k16_09 | 6 | 0 | 0 / 264 | 0 | 0 | 0/0 | 3 |
| [5/8, 11/16] | k16_10 | 6 | 0 | 0 / 264 | 0 | 0 | 0/0 | 3 |
| [11/16, 3/4] | k16_11 | 6 | 0 | 0 / 264 | 0 | 0 | 0/0 | 3 |
| [3/4, 13/16] | k16_12 | 6 | 0 | 0 / 264 | 0 | 0 | 0/0 | 3 |
| [13/16, 7/8] | k16_13 | 6 | 0 | 0 / 264 | 0 | 0 | 0/0 | 3 |
| [7/8, 15/16] | k16_14 | 6 | 0 | 0 / 264 | 0 | 0 | 0/0 | 3 |
| [15/16, 1/1] | k16_15 | 6 | 0 | 0 / 264 | 0 | 0 | 0/0 | 3 |
(data passes = window-fixpoint passes printed; < 10 means converged; k2a did not converge in NPASS=10.)

ROOTS OF THE FAILURES
Control (ao.py). Every remaining failure is an LCheckXA failure for which no RT edge is proposable ("no candidate
 edge"), at a reader whose TO row failed and whose L entry was therefore lowered. The rows pass at the corners (need
 = hi'(v,b) - lo'(v,a) <= 0 there) and fail because a slice's window width (hi from c2, lo from c1) adds to need.
 - SLICE_X3Y22.B6 (NxE, D = X5Y24.B6, X2Y29.DQ, X2Y21.B6): row a = X2Y21.B6(1), b = X3Y22.B6(0) (own feedback),
   Sep = 2 ps; need = hiC(c2)(v,v) - loC(c1)(v,X2Y21.B6). need per slice (pinarcs.py): K=1 308; K=2 140,124;
   K=4 56,48,40,32; K=8 15,9,7,1,-3,..; K=16 all <= -6. Margin (Sep - need): K=8 slices a,b,c: -13, -7, -5 ps;
   passes from [3/8,1/2] on. Widest passing slice (this row only): c2 - c1 ~0.087 at c1=0, ~0.11 at 0.25,
   ~0.14 at 0.5, ~0.16 at 0.75. This is the only control root for K >= 2 except k2a.
 - k2a [0,1/2] adds SLICE_X38Y21.C6 EnE (row a = X38Y21.A6(0), b = X39Y41.D6(1), margin -208).
 - k1a [0,1] has 8 failures at 7 readers: X3Y22.B6 (-306/-490), X38Y21.C6 (-671), X16Y21.A6 (-240), X25Y82.D6
   (-112), X32Y45.A6 (-9), X38Y51.B6 (-186/-68), X38Y84.D6 (best RT edge X38Y85.A6(3)->X39Y82.D6(4): margin -270).
 All are width effects of a fixed run ordering; smaller slices fix them (K=16 control: 0 failures on all 16 slices).

Data layer (datal_t.py). No failing obligation is a finite-margin CovTime/ChainOK miss; the failures are latch-claim
 truncations (a ChainOK link that neither Sep, the Up join nor JoinAnc can justify), which cut the claim of a data
 node, so a guard's claim ends too early ("end: no Sep E -> claim.B") or the guard's start fails. Failing guards are
 always on the data nodes SLICE_X38Y78.A6 (18 guards; 54 at K=1) and SLICE_X37Y68.B6 (12-24), plus at K<=2 a few
 latch-start shortfalls (X36Y63.B6 -6 .. -411, X12Y33.B6 -150/-715, ...) and at K=1 X21Y61.B6.
 Deepest truncation on each failing guard's claim-end chain (ana2.py; "margin None" = no bound found):
  k1a  T->U at X13Y87.D5 / X13Y86.B6, c1.B = X12Y87.A6(1), c2.A = X12Y87.A6(0), margins -8798 / -8157;
       + 4 failing comb-segment links (MUXX no bridge)
  k2a  T->U at X22Y87.D6, X23Y87.D5 and U'->T at X30Y75.B6, all with c1.B = SLICE_X27Y80.A6(2) (mux-select branch,
       cf. r23 follow-up 7); window fixpoint NOT reached in 10 passes (17k windows change per pass) and 516 loop-cover
       end checks fail (prev-pass windows, -2 .. -5.2 ns)
  k2b, k4a: T->U at X22Y87.D6 / X22Y87.C5 (c1.B = X27Y80.A6(2), c2.A = X22Y87.A6(0) the latch open), U'->T X31Y76.A5,
       U->H X34Y65.A5 (c1.B = X30Y76.A6(2), the register-bank enable)
  k4b, k4c, k4d, k8a, k8b: U->H at X30Y64.C6 / X30Y65.A6 / X34Y65.A5 / X34Y66.C6/D6 / X37Y70.D6, all with
       c1.B = SLICE_X30Y76.A6(2) (bank open) and c2.A = the latch's own close event (X30Y64.A6(1), X34Y66.A6(1), ...)
 Measured for the X30Y64.C6 U->H link (dsep.py, datal_t's own sep/upq): the close X30Y64.A6(1) and the bank open
  X30Y76.A6(2) are not causally ordered; Sep comes only from form (iv) through the common ancestor
  SLICE_X27Y80.A6(2): Sep23(anc -> bank open) - Up(anc -> close).
    k16_00 [0,1/16]:  23602 - 20755 = +2847  -> link holds, no truncation, slice passes
    k8b    [1/8,1/4]: 28235 - 29991 = -1756  (form iv needs >= 1); JoinAnc margin 1065 + 28235 - 633 - 29991 = -1324
  i.e. the Up - Sep gap of two concurrent branches grows with the slice width; at width 1/16 it has ~2.8 ns slack at
  c ~ 0, at width 1/8 it is ~1.3-1.8 ns short. Smaller slices fix it (K=16 data results in the table); a builder
  change would need a tighter Up for this concurrent-branch pair (the same R1-type root B saw at the corners before
  C's relative Up clause), not a new rule.
 Zero-width check: [1/2,1/2] (s05, mid run at c = 1/2) passes everything (0/264, 0 items, lchk 0/0), so intermediate
 corners per se are fine; the failures above are width effects.

WHAT IS NOT SHOWN
 - Nothing is Lean-checked: the slice nets are not emitted, the ceil/floor arithmetic is Python (exact Fractions), and
   all checks are B's/C's untrusted Python models of the Lean rules (lchk re-checks only the emitted Sep/Up entries).
 - One pair (12,18) only; one midpoint run per slice (not every behaviour in the slice); g = 1, kappa = 0.
 - Each slice net's windows contain the corner-c windows for c in the slice per arc (monotone lerp, ceil/floor of
   the endpoints); that this suffices in Lean (GateFact with N.lo <= sumLoC(c), sumHiC(c) <= N.hi) is the Lean side's
   claim (Formal/Cells/CornerSlice.lean, not checked here).
 - The control check is C's ao.py as C/B ran it (local checks after RT-edge rounds); TO-row failures are handled by
   lowering L, which is part of that procedure, not counted as failures.
 - Root attributions for control failures (TO rows lowered at the same reader) are a heuristic link, not proven causes.
 - mid uses floor instead of round (see above).
 - Uniform K = 12 and other non-uniform covers were not run.
