# joinaware: rule A' at the data's captures, with the join credit (`CA_JOINAWARE=1`)

PROGRAM.md "General first" item 2 (one rule, every kernel) and formal FOR-RESEARCH B2 / B3 ("the static rule sizes an
operator's delay for its own worst carry, as if its result were captured when its request arrives"). Subagent
`joinrule` of research, 2026-11-17 22:48 - 2026-11-18 02:45 UTC. nextpnr 9c732bc6303458df (`cells/verify/toolchain.sh` OK
before the builds). Changed: `research/tools/corner_audit.py` only (additions, all behind the flag); added: this
directory's files and two small preload vector sets (section 5). cells/rtl, bdc, dynamatic, circt untouched.

**Headline.** `CA_JOINAWARE=1` checks each sized operator's data where it is captured (the next latch's opening,
or the steer / mux request that samples it), with C-elements waiting for their last input and a join credit for a
sibling whose request shares the operator's launch; unset, corner_audit is byte-identical (checked on the final code).
It reproduces formal B3 on xorshift statically on all four x55a10 routes: with UADDI0's chain removed the current rule
fails uaddi0 by 1.5-2.1 ns, the joined rule passes it by +275 .. +1734 ps on ucmpi1's credited request; on the four
rebuilt routes with UADDI0 = 1 it passes all four (+239 .. +1509 ps; the current rule: -1559 .. -2121). UCMPI1 is not
relaxed (A'j within 0.4 ns of A'; short under both rules at this corner). Seed 21's full proposal: UADDI0 12 -> 1,
UXORI2 -> 1, UXORI1 -> 4; 100 -> 66 kernel links against 76 without the flag. The negative controls are flagged: +5 /
+20 ns on the adder's carry into bit 16 (A'j -1566 / -17016), +3 ns on the compare's chain (ucmpi1 -3439), UCMPI1 at
1 (uaddi0 -867: the credit shrinks with its sibling). collatz's uaddi1 / ucmpi2 join is NOT credited (no common launch
within one crossing; the counters meet only through the loop's control), so collatz gains the downstream arcs only
(full proposal on a relaxed route: UADDI1 3, against 11 without the flag). The automatic flow's routes: with the flag the it-0 proposals sum to 119 / 90 / 103 / 130 delay
links (xorshift / collatz / collatz64 / ipow) against 131 / 97 / 110 / 135 without, no line longer (xorshift UADDI0 8 -> 1
on ucmpi1's credit; collatz and collatz64 USELECT0 -> 1 on ucmpi2's); on the suite's it-1 routes 91 / 93 / 129 against
105 / 106 / 147 (collatz it 1 keeps UADDI1 at 3 where the current rule pads it to 11).
Draws (the default model) on the relaxed builds: xorshift (UADDI0 = 1) passes 12 / 12 xor19 draws on its four routes (three each, all EQUIVALENT, CARRY / F7 / FF from
0.27 to 0.97) and the preloaded counter's 12 / 12 on route 21; collatz (UADDI1 = 1, below what the joined rule
proposes) passes 7 / 7 col18 draws on four routes (4 / 4 on the two EQUIVALENT routes); the preload harness's negative
control fails as it must (with power-up states, a wrong value on the call that crosses 2^30; the clean route passes the
same rows), and the u1c1 build that both static rules flag passes its one draw (the static flag there is pessimistic).

## 1. The rule change (one switch, every kernel)

`CA_JOINAWARE=1` in `research/tools/corner_audit.py`, on top of whatever else is set (the automatic flow runs
`BD_SKEW_AND_JOIN=1 CA_SIZERULE=1`). Unset, every output is byte-identical (section 3.1).

For every cell that has an A' row (a generated operator whose data comes only from its upstream links: the fused
compute cells; muxes keep their A / A'm rows), the A' comparison -- the cell's data at its own outputs against its own
request at its own chain tail -- is replaced by a comparison **at every capture of the data**:

1. **Captures.** The data's forward combinational cone (from the cell's data outputs, through any logic, steers' data
   wires, mux data LUTs, other operators' logic) is followed to every storage input it reaches. Two kinds are
   captures:
   - a `bd_latch` data pin: the event is that latch's **enable**, and the two are compared at the latch output
     (data via D->Q against the enable via EN->Q). This is the latch-OPEN contract, not the latch close: every other
     rule measures the next stage from the enable -- A' launches the next cell's data at the link's C node through
     the latch's EN, rule E crosses a latch on its enable, rule I composes a pipe stage from the sender's enable. Data
     that is only in before the close would make each of those margins too large by exactly its lateness;
   - a `bd_steer` / `bd_mux` select pin: the event is the request pin on the same LUT (rule E's pairing).

   Anything else the cone reaches (a storage input that is not a latch's data or a select, an input of a
   non-combinational cell with no timing arc -- an FF's D, the PS7, an IO --, a capture with no event, or one this
   cell's request does not lead to) means the rule does not apply: the cell keeps its A' row and gets an unsized `j` row
   that says why.
2. **Launch and walks.** From each upstream link's C node (A''s launches): the data side on the longest walk (through
   the link's latch, at the first crossing level), the capture side on the earliest walk with **every positive
   C-element waiting for its last input reached** (skew.py's AND seeding, always on here), and every link C node
   `C(req_in, ~c_next)` seeded from its request pin only: its latch cannot open before its request arrives, and an
   acknowledge arriving on c_next at the same crossing count is a lap (on collatz, ulink_n13's walk reached the capture
   link through umux1's acknowledge and the pipe's next stage before its request did). The earliest path to the event
   must pass through this cell's request (its chain tail), else the capture is not one its request leads to.
3. **Join credit** (formal B3: "the later request must cover every input's data"). When the cell's request reaches
   exactly one storage node, a join J (so the cell's acknowledge is J's), J's other inputs are credited with a lower
   bound on their arrival relative to the launch S (the cell's input link's C node, `C(req_in, ~c_next)`):

       credit(i) = min over L in anc(S) U ack(S) of  s(L -> i) - l(L -> S)

   `anc(S)`: the handshake nodes (storage, not latches) driving S's request pin (I0); `ack(S)`: those driving its
   acknowledge pin (I1). `s` is the earliest walk (AND seeding), `l` the longest. A credit path must be the sibling's
   own handshake: from L it crosses at most one link C node (entered by its request pin from an `anc` launch, by its
   acknowledge pin from an `ack` launch) and otherwise only C-tree joins, never a latch and never S; S must be reached
   from L without a crossing. J's firing on the capture walk is then max(own input, credit + the input's arc).
4. **Guard**: A''s, max(a_frac x data, a_min), when no credit binds (A'j is then A' moved to the capture, with the
   rule's own guard). When the credit binds, both legs: max(a_frac x (data + capture + 2 l(L -> S)), a_min), as rule
   E's 0.97 / 1.03 do, because the capture leg then runs through another cell's request (fast) while l(L -> S) is
   subtracted (slow). A first version guarded both legs always; on the automatic flow's collatz64 route that made
   the proposal one link LONGER than without the flag (uaddi0 4 -> 7, ucmpi0 / ucmpi2 +1), a guard-policy effect
   that has nothing to do with captures, so it was dropped (commit 920aa08aa; every number here is from that rule).
5. **Rows and sizing.** Row `A'j <cell>` (rule A, sized); the cell's `A'` row becomes rule `a` (reported, not sized);
   `A'j` names the race: launch, worst capture, the data path and the capture path (storage nodes crossed), the credit
   (sibling, binding launch, its path) and the own-request bound (the same capture without the credit). A line that no
   measured constraint depends on, and whose cell has a sized A'j row, may go to `--floor` (it is measured free: its
   capture's last input is another cell's request); every other line on no constraint is kept, as before. (In every
   proposal below the freed lines got there through the ordinary greedy shrink instead: their A'j row drops by less
   than its margin when the chain is removed, because the credit holds the rest. The branch is a guard for the case
   where the credit dominates by more than the line's own delay.)

### Why the credit is a lower bound in every interleaving

S fires at max(a, k) + arc, a = its request rising, k = its acknowledge falling. In every token, a <= t_A + l(A -> S)
for the forward ancestor A that fired, and k <= t_K + l(K -> S) for the acknowledge source K that released it. The
sibling's request at J rises only after its own source S_i fired, which needs S_i's request (the same A's request: the
credit path from A enters S_i by its request pin) **and** its acknowledge: S_i's acknowledge waits for J's acknowledge
(every input of a join is acknowledged by it, possibly through a fork's C-tree), which is the cell's acknowledge
(precondition: the cell's request reaches only J), so whenever S is held by K, S_i is held by K too. Hence
t_i >= max(t_A + s(A -> i), t_K + s(K -> i)), and t_i - t_S >= min(s(A -> i) - l(A -> S), s(K -> i) - l(K -> S))
(max(x1, y1) - max(x2, y2) >= min(x1 - x2, y1 - y2)). Without the acknowledge term the bound fails when S is
back-pressured and the sibling is not; with the precondition that cannot happen.

## 2. The races it keeps

Every A'j row is one race, printed in report.txt as: launch (the input link's C node), worst capture (latch or select
pin), the data path and its time (storage nodes crossed, e.g. `ulink_n7f__0.ctl.u.u > ulink_n7f__0.lat.pair[2]`), the
capture path and its time (e.g. `ulink_n7f__0.ctl.u.u > ucond_br6_j > ulink_n_trueResult_6.many.stage[0].u.ctl.u.u`),
the credit when one exists (sibling, binding launch, its path) and the own-request bound. Three kinds remain:

1. **Latch capture behind the cell's own request** (no join, or the credit does not bind): data through the input
   link's latch and the cell's logic (and a steer's data wire) to the next link's latch D, against the request through
   the cell's chain, the join, the steer gate and that link's C node to the latch enable. Versus A', the capture side
   gains the join + steer + C-node + enable arcs and the data side the wire to the latch: 0.3-1.3 ns on these routes
   (x55a10 seed 21: uxori2 -4 -> +1324, uxori1 -499 -> -162, uaddi0 +2511 -> +3584).
2. **Latch capture behind a sibling's request** (the credit binds): the same, but the join waits for the sibling (formal
   B3's case). Named: `uaddi0 ... [join ucond_br6_j: sibling from ucmpi1.udly.chain.g[4] credited +3576 ps (worst of 4
   launches: umux0.uj0 > ulink_n7f__1.ctl.u.u > ucmpi1.ujoin)]`. The four launches are umux0's two joins (uj0, uj1:
   whichever fired the counter's fork) and the two acknowledge sources of ulink_n7f__0 (ulink_n_trueResult_6's stage-0
   C node and ucond_br6_j itself, through the sink branch).
3. **Select capture**: a compare's result at a steer / mux select against the request pin on the same LUT (the
   pairing rule E makes, with rule A's launch). ucmpi0 / ucmpi1: worst at ucond_br2 / ucond_br6. Barely relaxed: the
   compare's request reaches the steer only through its own chain, and the select's wire to the steer offsets the
   join + steer arcs (seed 21: ucmpi1 A' -880, A'j -800; ucmpi0 +1319 / +1296).

Kept on A' (row `j`): a cell whose data also reaches an untimed sink. On every kernel here that is the output mux
(xorshift / ipow umux3, collatz / collatz64 umux2): its data goes to the bench's 64 output FFs
(`$auto$ff.cc:337:slice$8001/D` ...), which no rule here times.

Races on x55a10 seed 21 (sdf 42b4fb4c, CA_SIZERULE corner, ps):

| operator | A' (own request) | A'j (captures) | worst capture | credit | own-request bound |
|---|---|---|---|---|---|
| uaddi0 | +2511 | +3584 | latch ulink_n_trueResult_6.many.stage[0].u: data 3749 ps (1x) vs enable 7445 ps (2x) | ucmpi1 +3576 (via umux0.uj0) | 3584 |
| uaddidec0 | +7554 | +9304 | latch ulink_n_trueResult_2.many.stage[0].u: data 3918 ps (1x) vs enable 13339 ps (2x) | - | 9304 |
| ucmpi0 | +1319 | +1296 | select ucond_br2: data 4563 ps (1x) vs request 5995 ps (2x) | - | 1296 |
| ucmpi1 | -880 | -800 | select ucond_br6: data 4731 ps (1x) vs request 4072 ps (2x) | - | -800 |
| umux3 | +1095 | not applied (its data reaches 64 input(s) that are not a latch's data or a select ($auto$ff.cc:337:slic) | | | |
| uxori1 | -499 | -162 | latch ulink_n25: data 2555 ps (1x) vs enable 2469 ps (1x) | - | -162 |
| uxori2 | -4 | +1324 | latch ulink_n_falseResult_9.many.stage[0].u: data 2188 ps (1x) vs enable 3577 ps (2x) | - | 1324 |

## 3. Checks

### 3.1 Unset: byte-identical

Checked on the automatic flow's xorshift it-0 route (`/tmp/bot/runs/ca/au_xorshift_1_0/seed1`, inputs copied):
`BD_SKEW_AND_JOIN=1 CA_SIZERULE=1 CA_JOBS=2 PYTHONHASHSEED=0`, the same `--out` path, the original corner_audit
(bb7b783ab) against the new one with `CA_JOINAWARE` unset, twice: at 05becdcf9 and at the final 920aa08aa. Both
times report.txt, lines.tsv, sizes.vh, verify.txt, negative_sized.tsv, soak.sdf, tighten.log, skew.log, arb_fork.log
and stdout are byte-identical (47 lines changed, kernel links 511 -> 131, as the bot's own `rule_and` run of that
route).

Why PYTHONHASHSEED: without it two runs of the SAME code differ (the bot's `au_xorshift_1_0/rule_and` and
`su_xorshift_1_0/rule`, same route and flags, differ in the order of tied rows in lines.tsv): tighten.find_chains and
other set iterations follow Python's per-process string hash. The proposals were equal; the byte order of ties is not.

### 3.2 Formal B3, statically (x55a10 routes, seeds 1 / 2 / 4 / 21, cand3b's command)

Routes rebuilt with cand3b's command (`637fe5514:research/cluster/requests/cand3b.sh`: x55a10 sizes,
`MLIR_OVERRIDE=research/data/fifteen/xorshift_predec.mlir`, its six BDC knobs, `BD_SKEW_AND_JOIN=1`), `lane2.sh` with
`LANE_NORUN=1`: bench sdf md5 21 -> 42b4fb4c (the brief's), 1 / 2 / 4 -> 8f165305 / f1da196a / 05a84ea0 (= formal C41's
x55a10 routes, which B3 used). Rule: `BD_SKEW_AND_JOIN=1 CA_SIZERULE=1` (the automatic flow's) with and without
`CA_JOINAWARE=1`; margins in ps at the CA_SIZERULE corner. "Zeroed" = the same audit worker with that line's chain arcs
set to 0 (what corner_audit's sensitivity run does), i.e. the line at 0 links on the same route. The relaxed builds
are x55a10 with UADDI0 = 1 (`research/data/sizerule/xorshift_sizes_x55a10_ja_bench.vh`, the joined proposal's value at
`--floor 1`), same command.

| seed | x55a10 sdf | as built (UADDI0 12): A' / A'j uaddi0 [credit] | UADDI0 chain zeroed: A' / A'j uaddi0 [own-request bound] | ucmpi1 A' / A'j (as built; UCMPI1 zeroed) | relaxed build (UADDI0 1) sdf: A' / A'j uaddi0 [own-request bound] |
|---|---|---|---|---|---|
| 21 | 42b4fb4c | +2511 / **+3584** [+3576] | -1977 / **+1060** [-904] | -880 / -800; -2585 / -2505 | 57fee21d: -1559 / **+1058** [credit +3383, own -510] |
| 2 | f1da196a | +2280 / **+3592** [+4074] | -1537 / **+1734** [-225] | -76 / -94; -1840 / -1858 | 5b49b9b7: -2121 / **+239** [credit +3283, own -1581] |
| 4 | 05a84ea0 | +2483 / **+3547** [+3204] | -2084 / **+275** [-1020] | -1173 / -785; -2549 / -2161 | 3881aa40: -1639 / **+1509** [credit +3897, own -607] |
| 1 | 8f165305 | +3057 / **+3829** [+3758] | -1575 / **+1082** [-803] | -737 / -446; -2475 / -2184 | bf472488: -1901 / **+896** [credit +3148, own -691] |

- **UADDI0 is free under the joined rule on all four routes, and only under it.** With its chain removed the base rule
  flags uaddi0 by 1.5-2.1 ns (A'), the joined rule keeps it positive (+275 .. +1734) because its capture
  (ulink_n_trueResult_6 stage 0's enable) waits at ucond_br6_j for ucmpi1's request, which the credit places
  3.2-4.1 ns after uaddi0's input link fired. The own-request bound (the same capture without the credit: A' plus the
  downstream join + steer + C-node + enable arcs, +0.8-1.3 ns) is still negative in every zeroed case: the join credit
  is what frees the line. On the four relaxed builds, as built (last column), the same picture: the base rule fails
  uaddi0 by 1.6-2.1 ns, the joined rule passes it by +239 .. +1509 ps, every time on the credit.
- **UCMPI1 is not relaxed.** Its captures are the select pins of ucond_br6..9, reached only through its own chain, so
  A'j stays within -20 .. +390 ps of A'; zeroing its chain is flagged by both rules (A'j -1858 .. -2505). At this
  corner ucmpi1 is short as built on all four routes under both rules (A'j -94 .. -800; rule E at ucond_br6 -923 on
  seed 21), so both proposals pad it (seed 21: 5 -> 11 under both): the joined rule changes nothing there.
- **The full proposal on seed 21** (sensitivity, greedy shrink, verify; 412 s): UADDI0 12 -> 1 "floor 1" (removing
  its whole chain costs its A'j row 2524 ps of the row's 3584: the credit holds the rest, so the greedy shrink reaches
  the floor and verify agrees), UCMPI1 5 -> 11 (padded for rule E at ucond_br6, -923 ps), kernel links 100 -> 66 (100
  -> 76 without the flag). Against the same audit without the flag, the lines that differ:

| line | x55a10 | proposal, flag unset | proposal, CA_JOINAWARE=1 | why (with the flag) |
|---|---|---|---|---|
| UADDI0 | 12 | 6 | 1 | floor 1 |
| UXORI1 | 3 | 6 | 4 | PAD 3->4 for A'j bridge_i.udut.uxori1 (-162 ps) |
| UXORI2 | 3 | 4 | 1 | floor 1 |

Every other line is proposed the same way by both. Sum of all proposed lines: 76 unset, 66 with the flag.

At the nominal corner (`--uniform 0.288`, eval_task's second static check; CARRY4 at 0.288 too), report only, seed 21:

| route | A' uaddi0 | A'j uaddi0 [credit; own-request bound] | A' / A'j ucmpi1 |
|---|---|---|---|
| x55a10 (UADDI0 12) | +3653 | +4818 [+3945; 4818] | -429 / -337 |
| relaxed (UADDI0 1) | -948 | **+1870** [+3718; +148] | -391 / +67 |

**collatz (B3's other join, uaddi1 / ucmpi2 at ucond_br5) is NOT reproduced: no credit.** On the four relaxed collatz
builds (x0.70 with UADDI1 1, cand4's knobs, seeds 27 / 2 / 3 / 4: sdf f66e0c02 / 63fb4fd1 / 5c5f8e31 / 5f876e69)
uaddi1's A'j is -331 / -1254 / -589 / -744 (A' -1699 / -2117 / -1825 / -1843), own-request bound = margin; ucmpi2 has
+1788 .. +2418. The join is found (uaddi1's request reaches only ucond_br5_j), but its sibling's
request does not descend from a launch one crossing behind uaddi1's input links: ulink_n13 is fed by the steps mux
umux1, ulink_n19__1 by the constant's source (whose request is the inverse of ufork5's acknowledge), ucmpi2's
ulink_n10__4 by n's fork. The walks reach the sibling only through acknowledge laps (umux1.uya -> ulink_n_falseResult_5
-> ufork8's acknowledge tree -> ulink_n10__4 by its c_next), which the credit's structure check rejects. The two
counters are synchronised by the loop's control merge several crossings back; crediting that needs the forward-firing
and acknowledge argument carried through more than one crossing, which this rule does not do. So on collatz the joined
rule only gains the downstream arcs (A' -> A'j: +0.9 .. +1.4 ns). Full proposals on relaxed route 27 (as built with
UADDI1 1), with and without the flag: UADDI1 1 -> **3** (padded for A'j -331 ps) against 1 -> **11** (A' -1699);
USELECT0 5 -> 1 (on ucmpi2's credit) against 3; UADDI0 7 -> 4 against 5; kernel links 109 -> 63 against 74. The
collatz draws at UADDI1 1 (3.5) test a point below what the joined rule allows.

### 3.3 Negative controls

A check earns its place by failing. Injections are `research/tools/fifteen/sdf_inject.py` on the route's prjxray SDF:
`uaddi0 ... slice[3].carry4/CO3 -> slice[4].carry4/CIN` is the carry into bit 16 of i + 1 (a routed 0 ps arc), so the
lateness lands on bits 16-31 at ulink_n_trueResult_6's stage-0 latch, where A'j measures. corner_audit `--no-size`,
CA_SIZERULE corner, ps.

| route (UADDI0) | injection | A' uaddi0 (own request) | A'j uaddi0 (captures) | flagged by the joined rule |
|---|---|---|---|---|
| x55a10 seed 21 (12) | none | +2511 | +3584 (own request binds; credit +3576) | no |
| x55a10 seed 21 (12) | +5 ns on the carry into bit 16 | -2639 | **-1566** | yes |
| x55a10 seed 21 (12) | +20 ns | -18089 | **-17016** | yes |
| relaxed seed 21 (1) | none | -1559 | +1058 (credit +3383 binds; own -510) | no |
| relaxed seed 21 (1) | +20 ns | -22159 | **-19542** | yes |
| x55a10 seed 21, UCMPI1's chain zeroed | (the sibling short) | +2511 | +3584 (own; credit falls +3576 -> +1871) | ucmpi1: A'j **-2505** |
| relaxed seed 21 (1) | +3 ns on ucmpi1's carry (slice[0] -> [1]) | -1559 | +1058 (unchanged: the compare's data does not move its request) | ucmpi1: A'j -379 -> **-3439** (rule E -2777) |

The +5 ns row is the calibration: A'j moves by the injected 5000 ps plus the guard's growth on the longer data leg
(+150), i.e. the injected arc is on the measured data path to the capture. The UCMPI1-zeroed row is the credit's own
control: the sibling's request is earlier by its chain (credit -1705 ps), and ucmpi1's own capture (the select at
ucond_br6) is flagged by both rules (A' -2585, A'j -2505).

**The preloaded counter's harness, under the same defect** (the brief: its harness lacked a negative control). Relaxed
route seed 21 (UADDI0 1, sdf 57fee21d), +20 ns on the carry into bit 16, `preload_gate.sh ... draw:2101` (CARRY / F7 /
FF at 0.97 in that draw):

| vectors (expected values from the C, preload_oracle.sh) | GLS power-up | +20 ns route | clean route |
|---|---|---|---|
| pre1 (12 rows) | X (default) | FAIL 0/12: every batch HANGs from its first call, odata X, the bench FSM X | **PASS 12/12** |
| xor19 vector 5 alone (x0 92d68ca2, rounds 3: an ordinary call) | X (default) | FAIL 0/1 (HANG) | (PASS in the 19/19 draws) |
| pre1m: control i0 0 / carry into bit 8 / carry into bit 16 (pre1 rows 1, 3, 5) | `+META_INIT=0` | PASS 3/3 | - |
| pre1n: control i0 0 / i0 2^30 - 3 / i0 2^30 - 2 (pre1 rows 1, 7, 12) | `+META_INIT=0` | **FAIL 2/3**: the i0 = 2^30 - 2 call returns d4976114 (C: 01649a8e) in both runs | **PASS 3/3** |

The default rows are an artifact of the simulator, not the defect: with the X power-up of GLS, slice 4's carry-in is
X for 20 ns after the adder's operands first become defined (its input latch has no reset), the capture latch closes
inside that window, and the X is held by the loop's C-elements for good (cells/gls/fid_core.vh's `+META_INIT` exists
for exactly this: "a hang the device cannot have"). With power-up states (META_INIT=0) the harness behaves as formal
B2 reported for its own simulator: ordinary calls and the carries into bits 8 / 16 pass, a call that crosses
0x40000000 is wrong. So the preloaded vectors can fail where xor19 cannot reach (its counter stays below 2^12). Not run:
META_INIT=1, the full pre1 with META_INIT on either route, xor19 with META_INIT on the +20 ns route.

**A build whose operator data is late at its consumer by the static measure** (the brief's "UCMPI1 at 1"):
`xorshift_sizes_x55a10_negu1c1_bench.vh` = x55a10 with UADDI0 1 and UCMPI1 1, seed 21, same command (sdf f5295dc4,
ffmux-clean). Report-only audits, ps:

| row | flag unset | CA_JOINAWARE=1 |
|---|---|---|
| uaddi0 (own request / captures) | A' -2215 | A'j **-867** (credit +2011, was +3383 with UCMPI1 5; own-request bound -1535) |
| ucmpi1 | A' -2347 | A'j **-2074** (select at ucond_br6: data 4254 vs request 2307) |
| rule E ucond_br6 (unchanged by the flag) | -2143 | -2143 |

The relaxed rule fails it on both cells, and uaddi0 fails *because* its sibling got shorter: the credit is a measured
property of the route, not a licence for the line. (Under a draw this build passes, 3.5: a static control, not a
demonstrated failure.)

### 3.4 The automatic flow's own routes (AUTO it 0 = suite su_*_1_0 routes)

The automatic flow's it-0 routes (`/tmp/bot/runs/ca/au_*_1_0/seed1`, copied; emit.py's estimates; identical SDF and
sizes to the suite's `su_*_1_0`, whose audits by the bot -- `BD_SKEW_AND_JOIN=1 CA_SIZERULE=1`, flag unset -- are the
baselines here), and the suite's it-1 routes (`su_*_1_1`: the loop's second iteration, sizes = it 0's proposal; the
bot's audits again the baselines). The joined audits: same flags plus `CA_JOINAWARE=1`, CA_JOBS=2, rule 920aa08aa.
Per kernel: A' vs A'j per operator, then every line whose proposal differs.

#### xorshift, it 0 (route su_xorshift_1_0 = au_xorshift_1_0, emit.py's estimates)
| operator | A' | A'j | credit / note |
|---|---|---|---|
| uaddi0 | +5999 | +8380 | ucmpi1 +12030; own 7154 |
| uaddidec0 | +7855 | +9341 |  |
| ucmpi0 | +10861 | +10844 |  |
| ucmpi1 | +8097 | +8127 |  |
| umux3 | +3393 | (A') | not applied: its data reaches 64 input(s) that are not a latch's data or a select ( |
| uxori1 | +34742 | +35103 |  |
| uxori2 | +17025 | +18557 |  |

| line | size as built | proposal, flag unset | proposal, CA_JOINAWARE=1 | why (with the flag) |
|---|---|---|---|---|
| UADDI0 | 24 | 8 | 1 | floor 1 |
| UXORI1 | 96 | 6 | 5 | bound by A'j bridge_i.udut.uxori1 (340 ps left) |
| UXORI2 | 48 | 5 | 1 | floor 1 |

3 line(s) differ; proposed kernel links (sum of lines.tsv proposals): 131 unset, 119 with the flag

#### collatz, it 0 (route su_collatz_1_0 = au_collatz_1_0, emit.py's estimates)
| operator | A' | A'j | credit / note |
|---|---|---|---|
| uaddi0 | +28835 | +29563 |  |
| uaddi1 | +8373 | +9760 |  |
| ucmpi0 | +9051 | +9052 |  |
| ucmpi2 | +10561 | +10991 |  |
| umux2 | +2899 | (A') | not applied: its data reaches 64 input(s) that are not a latch's data or a select ( |
| uselect0 | +32824 | +35146 | ucmpi2 +12601; own 35146 |

| line | size as built | proposal, flag unset | proposal, CA_JOINAWARE=1 | why (with the flag) |
|---|---|---|---|---|
| UADDI0 | 80 | 4 | 2 | bound by A'j bridge_i.udut.uaddi0 (76 ps left) |
| UADDI1 | 24 | 3 | 1 | floor 1 |
| UCMPI2 | 30 | 5 | 4 | bound by E bridge_i.udut.ucond_br5.u$LUT5/A4 (17 ps left) |
| USELECT0 | 86 | 3 | 1 | floor 1 |

4 line(s) differ; proposed kernel links (sum of lines.tsv proposals): 97 unset, 90 with the flag

#### collatz64, it 0 (route su_collatz64_1_0 = au_collatz64_1_0, emit.py's estimates)
| operator | A' | A'j | credit / note |
|---|---|---|---|
| uaddi0 | +62337 | +63215 |  |
| uaddi1 | +5611 | +6837 |  |
| ucmpi0 | +17760 | +17374 |  |
| ucmpi2 | +18221 | +18414 |  |
| umux2 | +3768 | (A') | not applied: its data reaches 64 input(s) that are not a latch's data or a select ( |
| uselect0 | +43988 | +45752 | ucmpi2 +21491; own 45752 |

| line | size as built | proposal, flag unset | proposal, CA_JOINAWARE=1 | why (with the flag) |
|---|---|---|---|---|
| UADDI0 | 160 | 4 | 2 | bound by A'j bridge_i.udut.uaddi0 (287 ps left) |
| UADDI1 | 24 | 10 | 7 | bound by A'j bridge_i.udut.uaddi1 (355 ps left) |
| USELECT0 | 118 | 3 | 1 | floor 1 |

3 line(s) differ; proposed kernel links (sum of lines.tsv proposals): 110 unset, 103 with the flag

#### ipow, it 0 (route su_ipow_1_0 = au_ipow_1_0, emit.py's estimates)
| operator | A' | A'j | credit / note |
|---|---|---|---|
| ucmpi0 | +9377 | +9536 |  |
| ucmpi2 | +9851 | +10128 |  |
| umuli1 | +18435 | +19515 |  |
| umux3 | +3832 | (A') | not applied: its data reaches 64 input(s) that are not a latch's data or a select ( |
| uselect0 | +38014 | +39454 |  |

| line | size as built | proposal, flag unset | proposal, CA_JOINAWARE=1 | why (with the flag) |
|---|---|---|---|---|
| UMULI1 | 64 | 17 | 15 | bound by A'j bridge_i.udut.umuli1 (377 ps left) |
| USELECT0 | 118 | 18 | 15 | bound by A'j bridge_i.udut.uselect0 (345 ps left) |

2 line(s) differ; proposed kernel links (sum of lines.tsv proposals): 135 unset, 130 with the flag

#### xorshift, it 1 (route su_xorshift_1_1: the loop's second iteration, sizes = it 0's proposal)
| operator | A' | A'j | credit / note |
|---|---|---|---|
| uaddi0 | +828 | +8280 | ucmpi1 +11500; own 1798 |
| uaddidec0 | +7029 | +8314 |  |
| ucmpi0 | -202 | +152 |  |
| ucmpi1 | +6899 | +6946 |  |
| umux3 | +205 | (A') | not applied: its data reaches 64 input(s) that are not a latch's data or a select ( |
| uxori1 | +978 | +1495 |  |
| uxori2 | +807 | +1998 |  |

| line | size as built | proposal, flag unset | proposal, CA_JOINAWARE=1 | why (with the flag) |
|---|---|---|---|---|
| UADDI0 | 8 | 6 | 1 | floor 1 |
| UADDIDEC0 | 22 | 6 | 3 | bound by A'j bridge_i.udut.uaddidec0 (176 ps left) |
| UCMPI0 | 4 | 6 | 4 | bound by E bridge_i.udut.ucond_br4.u$LUT5/A2 (52 ps left) |
| UXORI1 | 6 | 4 | 2 | bound by A'j bridge_i.udut.uxori1 (15 ps left) |
| UXORI2 | 5 | 3 | 1 | floor 1 |

5 line(s) differ; proposed kernel links (sum of lines.tsv proposals): 105 unset, 91 with the flag

#### collatz, it 1 (route su_collatz_1_1: the loop's second iteration, sizes = it 0's proposal)
| operator | A' | A'j | credit / note |
|---|---|---|---|
| uaddi0 | +104 | +490 |  |
| uaddi1 | -1302 | +30 |  |
| ucmpi0 | -370 | +106 |  |
| ucmpi2 | -207 | -362 |  |
| umux2 | +272 | (A') | not applied: its data reaches 64 input(s) that are not a latch's data or a select ( |
| uselect0 | +233 | +1821 | ucmpi2 +3202; own 1869 |

| line | size as built | proposal, flag unset | proposal, CA_JOINAWARE=1 | why (with the flag) |
|---|---|---|---|---|
| UADDI0 | 4 | 4 | 3 | bound by A'j bridge_i.udut.uaddi0 (75 ps left) |
| UADDI1 | 3 | 11 | 3 | bound by A'j bridge_i.udut.uaddi1 (30 ps left) |
| UCMPI0 | 6 | 9 | 7 | PAD 6->7 for E bridge_i.udut.ucond_br2.u$LUT5/A1 (-20 ps) |
| USELECT0 | 3 | 3 | 1 | floor 1 |

4 line(s) differ; proposed kernel links (sum of lines.tsv proposals): 106 unset, 93 with the flag

#### collatz64, it 1 (route su_collatz64_1_1: the loop's second iteration, sizes = it 0's proposal)
| operator | A' | A'j | credit / note |
|---|---|---|---|
| uaddi0 | -2809 | -1782 |  |
| uaddi1 | +1110 | +1958 |  |
| ucmpi0 | +706 | +1035 |  |
| ucmpi2 | -1169 | -1266 |  |
| umux2 | +8 | (A') | not applied: its data reaches 64 input(s) that are not a latch's data or a select ( |
| uselect0 | -1026 | +1122 | ucmpi2 +3175; own 835 |

| line | size as built | proposal, flag unset | proposal, CA_JOINAWARE=1 | why (with the flag) |
|---|---|---|---|---|
| UADDI0 | 4 | 20 | 14 | PAD 4->14 for A'j bridge_i.udut.uaddi0 (-1782 ps) |
| UADDI1 | 10 | 8 | 5 | bound by A'j bridge_i.udut.uaddi1 (45 ps left) |
| UCMPI0 | 10 | 9 | 8 | bound by E bridge_i.udut.ucond_br4.u$LUT5/A3 (23 ps left) |
| USELECT0 | 3 | 9 | 1 | floor 1 |

4 line(s) differ; proposed kernel links (sum of lines.tsv proposals): 147 unset, 129 with the flag

### 3.5 The draws

Builds: the relaxed sizes on four seeds each, same commands as the parents (xorshift: cand3b's; collatz: cand4b's
collatz x0.70: `MLIR_OVERRIDE=research/data/fifteen/collatz_preeq2.mlir BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0
BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BD_SKEW_AND_JOIN=1`), `LANE_NORUN=1`. Every route ffmux-clean.
xorshift x55a10 + UADDI0 1: seeds 21 / 2 / 4 / 1 -> 57fee21d / 5b49b9b7 / 3881aa40 / bf472488; collatz x0.70 + UADDI1 1:
seeds 27 / 2 / 3 / 4 -> f66e0c02 / 63fb4fd1 / 5c5f8e31 / 5f876e69. Draws: `bench_gate.sh ... draw:K` (the default model:
chains and rest U[0.20, 0.31] independently, CARRY4 / F7F8 / FF U[0.20, 1.0], setting M scatter; netlist decoded from
the bits, fasm_equiv verdict), K = 100 S + j as the farm's cand3b; gate vectors xor19 / col18 (expected values from the C,
`research/data/eventgraph/gate`). Preloaded counter: `research/tools/preload/preload_gate.sh ... pre1 draw:K`
(`research/data/preload/pre1`: carries into bits 8 / 12 / 16 / 24 / 30 / 31, the 32-bit wrap, 81 iterations across
2^30; expected values from the C started at the preloaded state). The parent sizes' record: cand3b (x55a10) 200 / 200
draws on 28 EQUIVALENT routes; cand4 collatz x0.70 96 / 96 on 24.

The node was shared (load 40-80 on 16 cores, two machine-wide GLS compile slots): a draw took 14-25 min including a
5-15 min wait for a compile slot, so the counts below are what fitted in the time box, not the brief's 4 x 4.

| route | kind | draw / vectors | verdict |
|---|---|---|---|
| ja_c70u1_27 | draw | 2701 chains 0.2835 rest 0.2625 carry/f7f8/ff 0.4062 region 0.02 wire 0.126 seed 2701 | PASS 17/17 cycles 5481 VERDICT: EQUIVALENT  (1744s) |
| ja_c70u1_27 | draw | 2702 chains 0.2615 rest 0.2302 carry/f7f8/ff 0.9124 region 0.02 wire 0.126 seed 2702 | PASS 17/17 cycles 5288 VERDICT: EQUIVALENT  (580s) |
| ja_c70u1_2 | draw | 201 chains 0.2521 rest 0.2781 carry/f7f8/ff 0.7417 region 0.02 wire 0.126 seed 201 | PASS 17/17 cycles 5718 VERDICT: NOT EQUIVALENT (792s) |
| ja_c70u1_3 | draw | 301 chains 0.2734 rest 0.3011 carry/f7f8/ff 0.6149 region 0.02 wire 0.126 seed 301 | PASS 17/17 cycles 6270 VERDICT: EQUIVALENT (verdict recomputed from run.log with bench_gate's rule; the wrapper's echo failed) |
| ja_c70u1_3 | draw | 302 chains 0.2024 rest 0.2325 carry/f7f8/ff 0.8762 region 0.02 wire 0.126 seed 302 | PASS 17/17 cycles 5782 VERDICT: EQUIVALENT  (569s) |
| ja_c70u1_4 | draw | 401 chains 0.3020 rest 0.2765 carry/f7f8/ff 0.9457 region 0.02 wire 0.126 seed 401 | PASS 17/17 cycles 6056 VERDICT: NOT EQUIVALENT (811s) |
| ja_c70u1_4 | draw | 402 chains 0.2014 rest 0.2611 carry/f7f8/ff 0.8909 region 0.02 wire 0.126 seed 402 | PASS 17/17 cycles 5613 VERDICT: NOT EQUIVALENT (504s) |
| ja_x55a10u1_1 | draw | 101 chains 0.2548 rest 0.2819 carry/f7f8/ff 0.3701 region 0.02 wire 0.126 seed 101 | PASS 19/19 cycles 5382 VERDICT: EQUIVALENT  (587s) |
| ja_x55a10u1_1 | draw | 102 chains 0.2132 rest 0.2450 carry/f7f8/ff 0.2739 region 0.02 wire 0.126 seed 102 | PASS 19/19 cycles 5156 VERDICT: EQUIVALENT  (562s) |
| ja_x55a10u1_1 | draw | 103 chains 0.2423 rest 0.2628 carry/f7f8/ff 0.9369 region 0.02 wire 0.126 seed 103 | PASS 19/19 cycles 5324 VERDICT: EQUIVALENT  (598s) |
| ja_x55a10u1_21 | draw | 2101 chains 0.2928 rest 0.2673 carry/f7f8/ff 0.9737 region 0.02 wire 0.126 seed 2101 | PASS 19/19 cycles 5656 VERDICT: EQUIVALENT  (837s) |
| ja_x55a10u1_21 | draw | 2101 [SDF ja21_carry16_20ns.sdf; xor19 vector 5 only (x0 92d68ca2, rounds 3, expected 7b0859a0), 120 us batch cap, no META_INIT] chains 0.2928 rest 0.2673 carry/f7f8/ff 0.9737 region 0.02 wire 0.126 seed 2101 | FAIL 0/1 cycles 9970 VERDICT: EQUIVALENT  (444s) |
| ja_x55a10u1_21 | draw | 2102 chains 0.2217 rest 0.2812 carry/f7f8/ff 0.3078 region 0.02 wire 0.126 seed 2102 | PASS 19/19 cycles 5558 VERDICT: EQUIVALENT  (564s) |
| ja_x55a10u1_21 | draw | 2103 chains 0.2988 rest 0.2094 carry/f7f8/ff 0.9524 region 0.02 wire 0.126 seed 2103 | PASS 19/19 cycles 5510 VERDICT: EQUIVALENT  (534s) |
| ja_x55a10u1_2 | draw | 201 chains 0.2521 rest 0.2781 carry/f7f8/ff 0.7417 region 0.02 wire 0.126 seed 201 | PASS 19/19 cycles 5267 VERDICT: EQUIVALENT  (728s) |
| ja_x55a10u1_2 | draw | 202 chains 0.2571 rest 0.2883 carry/f7f8/ff 0.8171 region 0.02 wire 0.126 seed 202 | PASS 19/19 cycles 5362 VERDICT: EQUIVALENT  (553s) |
| ja_x55a10u1_2 | draw | 203 chains 0.2385 rest 0.2682 carry/f7f8/ff 0.6837 region 0.02 wire 0.126 seed 203 | PASS 19/19 cycles 5178 VERDICT: EQUIVALENT  (565s) |
| ja_x55a10u1_4 | draw | 401 chains 0.3020 rest 0.2765 carry/f7f8/ff 0.9457 region 0.02 wire 0.126 seed 401 | PASS 19/19 cycles 5863 VERDICT: EQUIVALENT  (652s) |
| ja_x55a10u1_4 | draw | 402 chains 0.2014 rest 0.2611 carry/f7f8/ff 0.8909 region 0.02 wire 0.126 seed 402 | PASS 19/19 cycles 5352 VERDICT: EQUIVALENT  (527s) |
| ja_x55a10u1_4 | draw | 403 chains 0.2172 rest 0.2152 carry/f7f8/ff 0.3860 region 0.02 wire 0.126 seed 403 | PASS 19/19 cycles 5262 VERDICT: EQUIVALENT  (606s) |
| neg_u1c1_21 | draw | 2101 chains 0.2928 rest 0.2673 carry/f7f8/ff 0.9737 region 0.02 wire 0.126 seed 2101 | PASS 19/19 cycles 5312 VERDICT: EQUIVALENT  (555s) |
| ja_x55a10u1_21 | preload | pre1 draw:2101 carry16_20ns chains 0.2928 rest 0.2673 carry/f7f8/ff 0.9737 region 0.02 wire 0.126 seed 2101 | FAIL 0/12 cycles 119640 VERDICT: EQUIVALENT  (5753s) |
| ja_x55a10u1_21 | preload | pre1 draw:2101 chains 0.2928 rest 0.2673 carry/f7f8/ff 0.9737 region 0.02 wire 0.126 seed 2101 | PASS 12/12 cycles 794 VERDICT: EQUIVALENT  (242s) |
| ja_x55a10u1_21 | preload | pre1m draw:2101 carry16_20ns_mi0 chains 0.2928 rest 0.2673 carry/f7f8/ff 0.9737 region 0.02 wire 0.126 seed 2101 | PASS 3/3 cycles 104 VERDICT: EQUIVALENT  (136s) |
| ja_x55a10u1_21 | preload | pre1n draw:2101 carry16_20ns_mi0 chains 0.2928 rest 0.2673 carry/f7f8/ff 0.9737 region 0.02 wire 0.126 seed 2101 | FAIL 2/3 cycles 98 VERDICT: EQUIVALENT  (136s) |
| ja_x55a10u1_21 | preload | pre1n draw:2101 clean_mi0 chains 0.2928 rest 0.2673 carry/f7f8/ff 0.9737 region 0.02 wire 0.126 seed 2101 | PASS 3/3 cycles 94 VERDICT: EQUIVALENT  (192s) |

Reading: every draw on a relaxed route passes; the injected defect fails the preloaded harness (with power-up states)
while the clean route passes the same rows. xorshift with UADDI0 = 1: 12 / 12
xor19 draws on the four routes, all EQUIVALENT, at draw points including CARRY / F7 / FF 0.95-0.97 (2101, 401); the
preloaded counter on route 21 at CARRY 0.97 passes 12/12 (carries into bits 16 / 24 / 30 / 31 and the 32-bit wrap).
collatz with UADDI1 = 1: 7 / 7 col18 draws on four routes (27 and 3 EQUIVALENT; 2 and 4 NOT EQUIVALENT by the known
F7BMUX / GND-LUT driver class, excluded from counts as the farm does, though the decoded bits passed). The u1c1 control build (UADDI0 1 and UCMPI1 1), flagged by
both rules statically (3.3), passes its one draw (2101, 19/19): at that draw point the lateness the rules flag does not
corrupt a result, so u1c1 is a static control only, not a demonstrated failure (the static rule's pessimism on
xorshift's compares is the sizerule README's finding; with UCMPI1 at 1 it is still there).

What the draws say about the rule: on xorshift they agree with the static result -- UADDI0 = 1 survives where the
joined rule says it does (all four routes pass A'j), and where the current rule says it does not. On collatz the
joined rule is conservative: it flags UADDI1 = 1 on all four routes (no credit), and the draws pass it, as formal B3
found (UADDI1 "was never on the cycle"). Neither kernel produced a draw failure, so these draws cannot show that the
rule's margin is tight; the injected controls (3.3) are what show that it fails when it should.

## 4. What this does not show

- **Not the latch close.** Formal's B2 reading ("held by transparent latches for a whole iteration", >= 8 ns of carry
  slack) is NOT credited: A'j stops at the latch OPEN, the contract every downstream rule measures from. A rule that
  lets data arrive up to the close has to carry the lateness into the next stage's A', rule E's select walks and rule
  I, which this change does not do. What is credited is the join only.
- **The credit's precondition is checked, its corner is not modelled.** The bound holds when the cell's request reaches
  exactly one storage node (checked) and the sibling's acknowledge waits for that join's (true of every bd_join input);
  the walks do not track rising vs falling edges (this SDF's arcs are polarity-free apart from the fast-fall / fast-rise
  side taps, which the earliest walk keeps, so `s` is short, the safe side). Only the FIRST join after the cell's
  request is credited; later joins on the capture path get AND seeding of what the launch reaches, nothing more.
- **The guard is a choice.** A''s data-leg guard without a binding credit; 3 % on each leg (+ the credit's ancestor leg
  twice) with one, mirroring rule E's 0.97 / 1.03. Neither is a new measurement.
- **Static numbers are mostly one corner.** 3.2-3.4 are the CA_SIZERULE corner (chains and LUT / wire 0.21, CARRY4 /
  F7F8 / FF 1.0); the nominal corner (`--uniform 0.288`) only on seed 21 (x55a10 and relaxed), report only.
- **The draws are few** (3.5: xorshift 12 xor19 draws on four routes, one preloaded run; collatz 7 col18 draws on four routes), on the default delay model only (two of the xorshift draws happen to sit at
  CARRY / F7 / FF 0.95-0.97); no DRAW_CARRY slow-carry blocks, no board. The preloaded counter ran on one relaxed
  route; its negative control on three pre1 rows with `+META_INIT=0` only (not META_INIT=1, not the full pre1).
  formal B3's 8 / 8 + 4 / 4 slow-carry + preloaded draws per route on UADDI0 = 0 are the larger sample, in another
  simulator.
- **No draw failed, so the draws do not measure the rule's margin**; they say the relaxation it licenses on xorshift
  is safe on these routes and draw points.
- **Speed is not measured here.** The builds are LANE_NORUN (route + prjxray SDF only): no event-graph P. formal B3
  measured -5.9 % period on UADDI0 0 (3 clean routes); collatz's UADDI1 buys nothing (it was never on the cycle).
- **The automatic loop with the flag was not run end to end**: 3.4 is one proposal on each of the loop's it-0 and
  it-1 routes (the bot's suite routes), not a loop. In the loop the sibling shrinks too on later iterations; the A'j
  row then moves the freed line back up through the ratchet (a line the rule ever asks to lengthen is pinned), which is
  the intended coupling but is not measured here.
- **collatz's join is not credited** (3.2): a sibling whose request meets the operator's only through the loop's
  control, several crossings back, gets no credit; the rule is conservative there.
- **Select captures add nothing new.** Rule E already measures a compare's select race (with the select's own launch);
  A'j's select rows are the same race with A's launch and guard.

## 5. Files

| file | what |
|---|---|
| `research/tools/corner_audit.py` | `CA_JOINAWARE=1`: `walk_floor()` (skew.walk + the credit floor), `rule_a_joined()` (captures, credit, rows `A'j` / `j`), the worker hook, the free-line rule in the shrink, one report line. Unset: unchanged (3.1) |
| `research/data/sizerule/joinaware.md` | this file |
| `research/data/sizerule/xorshift_sizes_x55a10_ja_bench.vh` | x55a10 with UADDI0 12 -> 1 (the relaxed xorshift candidate built and drawn in 3.5) |
| `research/data/sizerule/collatz_sizes_x70_ja_bench.vh` | collatz x0.70 (cand4) with UADDI1 7 -> 1 |
| `research/data/sizerule/xorshift_sizes_x55a10_negu1c1_bench.vh` | NEGATIVE CONTROL, not a candidate: x55a10 with UADDI0 1 and UCMPI1 1 |
| `research/data/preload/pre1m.{hex,pre,exp,rows,notes}`, `pre1n.*` | pre1's rows 1 / 3 / 5 and 1 / 7 / 12 (the preload harness's negative control in 3.3); expected values = those lines of pre1.exp, re-checked against `preload_oracle.sh` (the C) |

Commands (the subagent's scripts were thin wrappers of these):

```
# a route (cand3b's knobs), route + prjxray SDF only
BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/xorshift_predec.mlir LANE_NORUN=1 research/tools/fifteen/lane2.sh \
  L NAME xorshift SIZES SEED research/data/fifteen/vec_xorshift.hex BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 \
  BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_FORK_OUT_LINK=n11__0 BDC_MERGE_OUT_LINK=ucontrol_merge0
# the rule (as auto_size.sh, plus the flag); --no-size for the report only
BD_SKEW_AND_JOIN=1 CA_SIZERULE=1 CA_JOINAWARE=1 CA_JOBS=2 python3 research/tools/corner_audit.py CA/seed1 --prefix bridge_i.udut. --out CA/join
# a line at 0 on the same route: the worker with that chain's arcs scaled to 0
python3 research/tools/corner_audit.py --_worker CA/join/soak.sdf '{"a_frac": 0.03, "a_min": 50, "glo": 0.97, "ghi": 1.03,
  "drop_const": true, "rule_a_link": true, "osc": [], "cut": [], "drop": [], "scale": {"bridge_i.udut.uaddi0.udly": 0.0}}'
# the carry into bit 16 of i + 1, late
python3 research/tools/fifteen/sdf_inject.py xray.sdf inj.sdf 'uaddi0\..*slice\[3\]\.genblk1\.carry4/CO3$' \
  'uaddi0\..*slice\[4\]\.genblk1\.carry4/CIN$' 20000
# draws and the preloaded counter (GATE_PLUSARGS=+META_INIT=0 for the negative control's power-up states)
research/tools/eventgraph/bench_gate.sh HW xorshift_bench_gen W research/data/eventgraph/gate/xor19.hex .../xor19.exp draw:K
research/tools/preload/preload_gate.sh HW W XRAY_SDF pre1 draw:K
```
