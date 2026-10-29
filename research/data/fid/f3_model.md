# F3: silicon-like primitives for the routed GLS (opt-in `GLS_MODEL=fid`)

Date 2026-10-27. Worktree on claude/research @ 818e90e. iverilog 12.0.
nextpnr 9c732bc6303458df (toolchain.sh passed) for the two routes used:
`arb_mtbf` (BD_NO_TIGHTEN=1, default seed; routed.json md5 43e15fb7,
sdf 814299ac) and `ro_many_top` (BD_RLOC=none; json 0f22d385, sdf 28248a69,
the same md5s as F1's rebuild).

## What was built

| mechanism | where | switch |
|---|---|---|
| LUT6/LUT5 and MUXF7/8: transport delay per input pin, output = mux tree of the delayed pins | `cells/gls/fid_core.vh` (`FID_LUT6`, `FID_MUX2`), used by `prims.v` | `-DGLS_FID` (build.sh: `GLS_MODEL=fid`) |
| metastability on a LUT state node (output routed back into its own pin) | `FID_RESOLVE`; gen.py finds the self-loops and passes `META6/5`, `TLOOP6/5` (feedback wire + arc), `FB6/5` (the feedback pin mask, since 055edd7), `SEED` | same |
| flop aperture: random old/new choice plus extra clock-to-Q | `prims.v` `SLICE_FFX` under `GLS_FID` | same |
| within-die variation: per-region correlated factor | `gen.py` `GLS_SCATTER_REGION`, `GLS_REGION_SLICES` | env |
| board position in the corner band | `gen.py` `GLS_SDF_FIELD=band`, `GLS_SDF_BAND` (default 0.38) | env |
| the same LUT model for the cell testbenches | **not in the tree**: a `BD_FID` path in `cells/sim/bd_prims_sim.v` was used for section 5's runs from an uncommitted copy and never landed (`git log -S BD_FID` on that file is empty; audit r18 #10). The cell benches cannot run fid from a checkout. | - |
| single-corner cell arcs (the refuted rise/fall row) | `cells/sim/bd_prims_sim.v` | default slow max, `-DBD_FAST_MIN` |

### The default build is unchanged
- gen.py on arb_mtbf: netlist.v, netlist_baked.v, annot.sdf, names.map and
  nets.map have the same md5 as the unmodified gen.py's output. With
  GLS_SCATTER=0.1 in arc mode and in wire mode (seed 3), the files are
  byte-identical to the old gen.py's. With GLS_MODEL=fid, netlist.v (the
  annotation-gate netlist) is still identical.
- Routed GLS of arb_mtbf over 3 us with the old and the new prims.v (default
  defines): all 124240 wire/reg signals have identical value-change histories,
  7,576,074 changes in total (`fid/f3/vcd_norm.py`; header and parameter
  lines ignored). The testbench logs are identical too.
- Gate (tb_gate, new prims.v): `ANNOTATE_DONE`, 0 SDF WARNING/ERROR lines.
- Not shown: byte-identity on gcd_hw or any other route (none was built).

## 1. Transport per pin, and the audit's examples (`fid/f3/tb_f3_lut.v`)

Each pin Ak is copied through `ak <= #(arc_k - 1) Ak` (a nonblocking
transport, every edge kept). The output is the zero-time mux tree of the
copies, and a 1 ps sampler (`FID_SAMPLE`) puts back the 1 ps. The sampler
absorbs zero-width glitches between two copies that land in the same time
step. Before it existed, one of those glitches reached the resolver as a
0 ps "runt" and broke tb_arb's exclusion check. Consequence: an edge can be
up to 1 ps early when two pins land on exactly the same picosecond. Per-pin
arcs come from the SDF. In prjxray's CLBLL/CLBLM sdf, every A1..A6->O6 arc is
the same (0.045::0.056)(0.100::0.124). The O5 arcs differ per pin
(A5 0.118, A1..A4 0.150-0.152 slow max). The large per-pin differences sit in
the site-pin wires, which F1's xray SDF puts in the interconnect (already
transport).

| check (arc 124 ps) | default model | fid model | transport expectation |
|---|---|---|---|
| T1 buffer, pulse 1000-1120, rise 1130 | 1 edge, at 1244 | 1124, 1244, 1254 | 1124, 1244, 1254 |
| T2 XOR3, inputs at 1000/1040/1100 | 1 edge at 1124 | 1124, 1164, 1224 | settles 1224 |
| T2 value at a request at 1200 | 1 (apparent margin **+76 ps**) | 0 (margin **-24 ps**) | 0, -24 ps |
| T3 isolated 50 ps pulse | swallowed | passes (2124-2174) | passes |
| T4 XOR2, A1 3000 / A2 3030 | no edge | 30 ps glitch 3124-3154 | function hazard |
| T5 change on an unread pin | no edge | no edge | no edge |
| T6 MUXF7 data pin, 50 ps pulse | swallowed | passes | passes |

`run_f3.sh` requires tb_f3_lut to FAIL on the default model. It fails 5 of 6
checks there, and that failure is the negative control. X semantics do not
change: for 3000 random vectors with x on 30% of inputs (4 INITs plus a MUXF7),
the settled outputs are identical under the two models (`tb_f3_kleene.v`).

**Hazard and pulse literature.** No datasheet or app note was found. The
only source is P. Alfke (Xilinx) on comp.arch.fpga: a single-input change does
not glitch the LUT, because the pass-transistor mux holds its value during
non-overlapped switching. A multi-input change can glitch, and he would not
guarantee glitch-freedom at every PVT corner
(fpgarelated.com/showthread/comp.arch.fpga/32950-1.php). The model agrees
with that: a single-pin change gives at most one edge, and a multi-pin change
gives the hazard its arrival order implies. Internal mux-tree skew beyond the
characterised arcs is unknown. `+FID_LEVEL_PS=s` adds (3.5-k)*s ps to pin Ak,
with A6 at the root and fastest. The default is 0, which is an assumption.
**Pulse filtering:** no 7-series figure was found, so every pulse of 1 ps or
more passes (pessimistic for async).

## 2. Metastability

**LUT state node** (`FID_RESOLVE`). A runt is an output reversal less than
TLOOP after the node's last edge, where TLOOP = feedback wire + the feedback
pin's arc. For such a runt, the model computes an offset
delta = p - (TLOOP - WIN/2) + N(0, WIN/4) (p = runt width). Then:
- If delta <= -WIN/2, the runt is rejected.
- Otherwise the node resolves to the runt value (delta > 0) or back, after
  t_r = TAU ln(WIN / 2|delta|), clipped at 40 TAU. For a uniformly distributed
  offset this gives P(t_r > t) = exp(-t/TAU).
- Since 055edd7 the feedback pin is evaluated from the node's committed state
  (FB6/FB5), so a runt has no echo and no input change is ignored; a drive
  away from the held value during a resolution ends it as an ordinary edge.
  Before that, the echo was masked by ignoring every change for TLOOP after
  the runt, which lost genuine follow pulses (audit r16 follow_lost; the
  regression is fid/f3/tb_f3_follow.v). Every fid result before 055edd7 used
  the old resolver.
- `+META_X=1` makes the node x while it resolves.

TAU = WIN = 150 ps for a LUT loop is an **assumption**: no figure was found.
The tail is longer than every flop tau below, which is the pessimistic side.
Pure transport without the resolver is not an option. On routed arb_mtbf with
`+META_OFF=1`, the decision nodes make 3330-3451 q edges in 20 us, against
1730-1741 with the resolver. Runts circulate in the hold state, the digital
picture of a loop that never resolves.

**Flop** (`SLICE_FFX` under GLS_FID). The aperture is [-TSU, +THD] from the
SDF SETUPHOLD, or `+META_FFW` (50 ps) centred when there is none. A change in
the aperture picks old or new by offset from the centre plus N(0, ap/4) noise,
and adds TAU_FF ln(ap / 2|delta|) to CK->Q. TAU_FF defaults to 75 ps. That is
at or above every FPGA flop tau in Beer et al., "The devolution of
synchronizers", ASYNC 2010 (57/51/73 ps at 130/90/65 nm). No 28 nm 7-series
value was found. The flop's CK->Q became an explicit transport delay. The
specify path made it max(TCKQ, t_r) instead of TCKQ + t_r, which hid every
resolution shorter than TCKQ: the first run measured a slowest CK->Q of
300 ps, the bare TCKQ.

**Testbench `tb_f3_meta.v`** (prims.v, the routed-GLS primitives):

| | default model | fid model |
|---|---|---|
| A. bd_arbcell from SLICE_LUTX: 200 identical races, r2 360 ps after r1, loop 424 ps | r1 wins 200/200 | r1 125, r2 75; X 0; settled double grant 0 |
| A. transient g1&g2 | 0 | 194 overlaps, widest 26 ps (the O5/O6 arc difference is 28 ps) |
| B. flop, D 20 ps before CK, window -60/+40 | X 200/200 | 1: 116, 0: 84, X 0; slowest CK->Q 593 ps (TCKQ 300) |

Mutual exclusion holds for the settled grants. During a resolution, both
grants are briefly high for no longer than the fractured site's O5/O6 arc
difference, which is the structural decode skew tb_arb_overlap is about.
run_f3.sh requires tb_f3_meta to FAIL under the default model, and it does:
one side always wins, and the flop goes X.

**Routed GLS of hw/arb_mtbf** (`tb_f3_arbm.v`, 20 us, nextpnr SDF min
column):
- gen.py found 644 self-loop state LUTs, with loop delay min/median/max
  419/419/773 ps.
- The six `ch[*].ustate` decision elements on the two free-running rings made
  99 metastable events (50 commit, 49 back) with META_SEED=1, and 94 (50/44)
  with seed 2. Median t_r was 86/98 ps, max 647.
- No x on the grants. Transient overlaps per channel were at most 28 ps wide;
  ring periods were 15930/23740 ps under both models.
- With the xray SDF at band 0.38 plus region 0.16 and wire 0.126 scatter, a
  10 us run gave rings of 14388/20312 ps and 80 ch[*] events (30 commit,
  50 back), with no x.
- The default model on the same route shows overlaps up to 148 ps wide on
  channels 0, 2 and 5. The fid model never exceeds 28 ps there. These are
  default-model artefacts, not seen with transport.
- The sync1/sync2 flops never saw an aperture event, because win_hit stays
  quiet. The flop path is covered by tb_f3_meta only.

## 3. Within-die variation (`fid/f3/ring_scatter.py`, `test_variation.sh`)

The existing GLS_SCATTER (per arc, or per pip with MODE=wire) is the
per-wire random term. `GLS_SCATTER_REGION=sigma_r` multiplies every arc by a
factor drawn per GLS_REGION_SLICES x GLS_REGION_SLICES block of slice sites,
using a stable hash of (seed, region). Cell arcs take their own site's region
and interconnect its sink's. Sizing was done against the one number on
record, the 8.5% median ring scatter. On ro_many_top's 128 rings (lengths 7 to
63), each draw's period ratio was divided by the draw's median (a corner is
not scatter). Results, median |dev|:

| perturbation (8 draws unless noted) | all | L7 | L63 |
|---|---|---|---|
| wire 0.126 alone | 0.65% | | |
| arc 0.126 alone (4 draws) | 1.44% | 2.17% | 0.99% |
| region 0.10, 10-slice regions (4 draws) | 5.34% | 5.79% | 4.60% |
| region 0.16, 10-slice regions | 8.04% | 9.55% | 6.42% |
| **region 0.16 + wire 0.126 (recommended)** | **8.33%** | 10.0% | 6.52% |

Per-wire scatter of any plausible size averages out over a ring. The board's
8.5% therefore has to be correlated, if it is variation at all. test_variation
checks two things: the recommended setting must land in 6.5-10.5%, and wire
scatter alone must fall below 3% (the negative control). It passes.
`GLS_SDF_FIELD=band` interpolates fast_min + b*(slow_max - fast_min) within
one arc. On arb_mtbf's xray SDF, a LUT arc of (45:100:124) becomes 75 ps at
b = 0.38. On nextpnr's SDF (all columns equal) it is a no-op.

What this does not show:
- The region size and the region/wire split are not identifiable from the
  repo. The board's per-ring periods are not archived, and the 8.5% includes
  nextpnr's model error (F1: the xray model spread is about half the measured
  scatter). On the xray SDF the right sigma_r is probably smaller.
- Nothing here says which rings are slow on this die.

## 4. Library: does any state cell depend on a LUT not glitching?

`fid/f3/lut_hazards.py` enumerates every state LUT in cells/rtl (read only).
For each stable state, it checks every multi-pin change and every arrival
order. Every hazard it finds falls into one of three classes:
- **C-elements** (bd_c2/_set/c3/c4/_norst): only on inputs moving in
  OPPOSITE senses, e.g. a 0->1 while b 1->0. Four-phase handshakes never do
  that between output transitions.
- **bd_c2n / bd_c2n_set and the bd_arbiter state** (q = C(r1, ~r2)): r1 and
  r2 moving the same way together. That is the arbitration race itself,
  handled by the resolver. With r1/A0 together, the protocol orders A0 after
  the grant.
- **bd_latch, bd_link_dctl, bd_mux joins, bd_flink_ctl, bd_dr2bd**: the
  enable or ld moving together with data. That is the latch setup/hold, i.e.
  the bundling constraint that tighten.py and the rules already own, not a LUT
  property.

No library cell's correctness rests on glitch-freedom beyond its protocol and
bundling obligations. That is a judgement per class, not a proof per instance.

Empirical check (from an uncommitted BD_FID copy of bd_prims_sim.v, see the
table at the top; not reproducible from the tree): run_sim.sh in a copy of cells/ with `-DBD_FID` (the cell
netlists have direct feedback, so state nodes are detected at run time: a
pin that followed 3 consecutive output edges and never missed one). With
`+FID_LIST`, tb_arb lists exactly ua1, ua2, ustate and ucell.ustate. An
earlier detector also took the grant LUT, a false positive, and that is
fixed. Results: see the table in section 5.

## 5. The refuted rise/fall row, and every cell testbench

`bd_prims_sim.v` read 56/124 (O6) and 55/152 (O5) as rise/fall. Those pairs
are fast-corner and slow-corner bounds of one arc. Both edges now take slow
max (O6 124; O5 152 152 150 150 118), or fast min with `-DBD_FAST_MIN` (45;
44 44 42 46 48). BD_T_RISE/BD_T_FALL are kept as names and are now equal.
tb_end's expected period was written as the constant 56+124. It now uses
the macros (the only testbench edit).

Results: 27 testbenches, all build/gen artefacts generated from
cloud/fixtures. old = HEAD's bd_prims_sim (rise/fall).

| config | pass | fails |
|---|---|---|
| old, route 0 | 27/27 | - |
| old, route 354 | 26/27 | tb_smoke_xorshift_gen TIMEOUT at 300 s under load (passed at route 0; not rerun) |
| new slow, route 0 | 24/27 | tb_arb_overlap (no overlap arc-only), tb_end (stale 180 ps constant, fixed since), tb_ctl (timeout) |
| new slow, route 354 | 26/27 | tb_ctl (timeout) |
| new fast min (-DBD_FAST_MIN), route 0 | 26/27 | tb_arb_overlap (no overlap arc-only); tb_ctl PASSES at this corner |
| **fid** slow, route 0 | 25/27 (26 with the long rerun) | tb_ctl (decoupled ATTEMPT: PROTO); tb_smoke_xorshift_gen hit the 900 s wall limit and PASSED when rerun alone (1439 s; runs_done=8, lat 220..8936, same as the default model) |
| **fid** fast min, route 0 | 25/27 | tb_ctl (decoupled attempt PROTO); tb_smoke_xorshift_gen 900 s wall limit (not rerun) |
| **fid** slow, route 354 | 24/26 run (tb_smoke_xorshift_gen not run: too slow under load) | tb_arb_overlap: **11 overlaps, 19-26 ps, with routing** (all removed by the 1-link filter); tb_ctl (decoupled attempt PROTO) |

Metastability census, fid, route 0, +META_VERBOSE=2. In tb_arb, tb_arb_prot,
tb_link, tb_merge, tb_mux, tb_ring, tb_steer, tb_forkjoin, tb_conv, tb_prims
and tb_gcd_rig, no library state node ever reversed inside its loop delay:
0 resolver events, 0 rejected runts. So the library cells, as those benches
drive them, never present a LUT state node with a race or a glitch. The
detector can fire, as two benches show:
- tb_arb_overlap: 6 events on udut.ustate, all four outcome combinations.
- tb_ctl: 2020 events plus 219 rejected runts, all in the decoupled
  attempt's `ur`/`ulf` state LUTs. That attempt is hazard-dependent, and only
  the transport model shows it.

Which earlier conclusions change:
- **tb_arb_overlap.** With the old split there were 89 overlaps, 8-16 ps wide,
  at route 0, and none at 354. The "falling grant lags the rising one by 2.5x"
  premise was the corner mix. With one corner, the default model shows NO
  overlap arc-only, so the bench's "the hazard must appear" check fails. The
  transport model shows the real one: O5 is 26-28 ps slower than O6 in the
  same site. With fid it appears at route 0 (4 overlaps, 5-26 ps, all removed
  by a one-link filter). It also appears in routed arb_mtbf (at most 28 ps).
- **bd_arb.v header.** The "with zero routing the rising grant wins by 16 ps"
  arithmetic (56+52 vs 124) used fast rises. tb_arb's own handover count goes
  from 1 instant (old, route 0) to 0 (new). The header's claim is unproven
  either way under one corner.
- **tb_ctl.** The decoupled ATTEMPT (verify/attempts/bd_deco_attempt.v, not
  a library cell) now deadlocks under the default model at slow max, at both
  route 0 and 354 (its four completion flags stay 0000, and the bench waits
  forever). It completes at fast min. Before, it completed and lost data, as
  the bench asserts. Under fid it completes at every corner and route and
  fails PROTO: its output request glitches out of phase from 8980 ps on, with
  2020 resolver events in its state LUTs. The simple controller and bd_link_dc
  pass their rows in every configuration.
- **tb_arb_overlap, routed regime.** Under fid the bench FAILS at route 354:
  11 overlaps, 19-26 ps. BD_ROUTE_PS adds the same delay to O5 and O6, so the
  28 ps O5-O6 difference survives routing. The old conclusion "routing removes
  the overlap" came from inertial paths plus the corner mix. Every overlap is
  still removed by the 1-link filter, and bd_arbiter (q held on A0) shows none
  in tb_arb. The routed arb_mtbf GLS agrees: overlaps of at most 28 ps on all
  six channels.
- **tb_mem / tb_bdc_mem sizing.** These size chains from BD_T_RISE: DSETUP=5,
  DCO=20 at 124 ps per link. Before it was "one rise arc = 56". Both pass.
- **tb_null_gcd_gen / tb_null_isprime_gen.** Unchanged: PASS,
  runs_done=50, lat 5..5 under old and new at route 0.
- **arb_mtbf.** No simulation of hw/arb_mtbf.v uses bd_prims_sim.v (grep),
  so this fix does not touch it. Its routed GLS is in section 2.


## 6. CARRY4 and SLICE_LATX transport (S5, 2026-10-28)

Under `GLS_FID` only, `prims.v` now has transport variants of CARRY4 and
SLICE_LATX. Without GLS_FID the preprocessed prims.v is identical to the old
one, so the default model is unchanged (evidence below).

- **CARRY4.** Each output has its own copy of every pin it depends on. Each
  copy is delayed by that pin's arc to that output (`T<pin><out>`, the names
  the SDF and gen.py's baked netlist already use; 52 arcs), minus the 1 ps
  that `FID_SAMPLE` adds back. Each output is the carry/xor expression of the
  default model, evaluated on its own copies. The code is mechanical (one
  copy per arc).
- **SLICE_LATX.** CK, D, CE and SR are each delayed by their own arc. nextpnr's
  SDF has only CK->Q, so D/CE/SR take TCKQ unless `TDQ/TCEQ/TSRQ` (fid-only
  parameters, default -1 = TCKQ) are given. That is the same stated
  assumption as before. The latch function runs on the delayed pins once per
  time step, 1 ps after the first copy moves, so that two copies landing in
  the same step cannot leave a zero-width x in the state (x is sticky in a
  latch). There is NO metastability model for a D change at the gate's
  closing edge: the result is whatever order the arcs give.
- **Power-up difference:** fid Q equals INIT from t = 0, while the default
  model's Q is x for the first TCKQ. On the die the configured INIT is
  present at start-up.

| check | default model | fid model | transport expectation |
|---|---|---|---|
| C1 S0 and S1 rise together, O1 = S1 ^ (S0 ? 1 : 0), TS1O1 205 / TS0O1 400 | pulse 1205-1340 | pulse 1205-1400 | 1205-1400 |
| C2 50 ps pulse on S2 -> O2 (228) | swallowed | 2228-2278 | passes |
| C3 S3 pulse 3000-3120, rise 3130 -> O3 (233) | 1 edge, at 3233 | 3233, 3353, 3363 | last edge 3363 |
| C4 CIN -> CO3 (114) on a propagate chain, plus a 40 ps CIN pulse | edges at 4271, 4871; pulse lost | 4114, 4714, 5114, 5154 | 4114, 4714, 5114, 5154 |
| C5 one CIN edge -> CO0 (271), O2 (239) | wrong times | 4871, 4839 | 4871, 4839 |
| L1 open latch, 50 ps D pulse, TCKQ 300 | swallowed | 1300-1350 | passes |
| L2 D falls at 2120 and rises at 2130, latch open | the 10 ps dip is lost | 2420, 2430 | both edges |
| L3 D 40 ps before the gate closes | captured at 3300 | captured at 3300 | captured |
| L4 40 ps async clear while closed | Q 0 at 4300, held | the same | the same |
| L5 D pulse while closed | no edge | no edge | no edge |

`run_f3.sh` now also runs `tb_f3_carry` (the default model fails 5 of 5) and
`tb_f3_latch` (the default model fails 2 of 5). Each must FAIL under the default model
and PASS under fid, and both do. `tb_f3_kleene_c4` checks that x semantics do
not change: 3000 random vectors with x on 15% of the carry pins (latch pins
x 2%, SR mostly 0, latch state carried over from one vector to the next)
give identical settled O/CO/Q under the two models. That check can fail. A
mutated fid model (`|` -> `&` in CO2's carry-in) differs on 278 lines, and
one with the latch's x-on-unknown-gate rule removed differs on 288. The x
draw takes the low 31 bits of $random. (The older tb_f3_kleene uses a signed
`r % 10 < 3`, so its x rate is about 65%, not 30%. Not changed.)

**The default model's CARRY4 is not its SDF arcs (found here).** Internally,
CO1..CO3 and O1..O3 read the CO nets, and those nets are the module's own
path-delayed outputs. So each output moves at max(its own arc, the time the
CO net it reads moves). For a propagate chain, the default model's CIN->CO3
is 271 ps (CIN->CO0), not the annotated 114, and that cost is paid on every
CARRY4 of a ripple chain. S0->CO3 becomes 514 (S0->CO2) instead of 489.
(Probe: one CIN edge gives CO0..CO3 all at +271, O2 at +271 instead of +239.)
prjxray's own table has CIN->CO3 (0.114 slow max) shorter than CIN->CO0
(0.271), which is not causal for a ripple through CO0. It looks like a fitting
artefact, and nextpnr's STA uses the same numbers. The fid model follows the
arcs as given, so **on a carry chain fid is FASTER than the default model,
and it agrees with the SDF and STA rather than with the default GLS.** If the
real CIN->CO3 is at least CIN->CO0, the default GLS was the closer one and
fid (and the STA) are optimistic on carry-ripple data. Under the "take the
longer number" rule, an arc-monotone floor (each CO_k at least CO_(k-1)) would
be the safe choice. It was NOT added, because it departs from the
characterised arcs and this is the main thread's decision.

**Library dependence.** No cells/rtl cell uses CARRY4 or a slice latch.
bd_latch keeps its storage on LUTs (its header gives the reason: the
LDCE.G clock-pin routing), and no current design instantiates LDCE (journal,
fasm2net entry). CARRY4 appears only where yosys infers it, in bdc compute
units (addi/subi/cmpi via alumacc, cmpi as `xa > xb`) and in clocked counters
in rigs. Those are datapath cones under a bd_delay bundle (or synchronous), so
correctness depends on the settled value at the request, not on glitch
freedom. What the model changes is the GLS settle time of those cones. The
carry-ripple point above is the one that could move a GLS bundling margin,
in the optimistic direction under fid.

**Default build unchanged.** `iverilog -E` of the old and the new prims.v,
with no defines and with `-DGLS_TRANSPORT_IC`, gives identical text (blank
lines and `line markers ignored). A small netlist (16 ICBUFs, 8 LUTs, a
2-CARRY4 8-bit chain, 8 SLICE_LATX with mixed GHIGH/INIT/SR, 3000 random
stimulus events) simulated with old and new prims.v under default defines
gives byte-identical VCD bodies: 123,918 value changes plain and 125,704 with
GLS_TRANSPORT_IC. `vcd_norm.py` agrees (0 differ). The same bench under fid
differs, so the bench can tell the models apart.

Not done:
- No routed GLS with the new CARRY4/latch under fid, and no kernel GLS (no
  route on disk in this worktree, and nextpnr was not allowed).
- No latch aperture/metastability.
- DSP, BUFG and flop CK/SR pins are still sample-at-fire (BUFG and the flop
  pins: transport since S6, section 7).
- The carry arc-monotonicity question is open.

## 7. SLICE_FFX pins and BUFGCTRL transport (S6, 2026-10-29)

Under `GLS_FID` only. Without it the preprocessed prims.v is identical to
HEAD's (evidence below).

What the fid flop was before S6: Q was already a transport CK->Q (S1; section
2), so a Q pulse narrower than TCKQ was kept, but CK/D/CE/SR were read at the
CK event with no arc, any CK pulse however narrow clocked the flop, and SR
was outside the aperture. BUFGCTRL was the default specify path (a pulse
narrower than TI0O swallowed).

- **Pin arcs.** CK, D, CE, SR each reach the capture node through their own
  transport arc (`TCKI`, `TDI`, `TCEI`, `TSRI`, fid-only parameters), and Q
  leaves it TCKQ - TCKI later through a token queue (so a capture undone by a
  runt decision is cancelled before Q moves). The SDF has only CK->Q plus a
  SETUPHOLD per pin, so the pin->node arcs are not characterised: TCKI
  defaults to 1 ps and the others to TCKI. External CK->Q stays exactly TCKQ
  and the SDF aperture stays where the SDF puts it. Data copies land 1 ps
  before their arc so that a copy and the CK copy never share a time step;
  an input moving at the same instant as CK is a 1 ps-setup aperture event.
  This shifts tb_f3_meta B by 1 ps (116/84 -> 119/81 captures of 1/0).
- **SR in the aperture.** SR changes are now aperture events like D and CE
  (the SDF has `SETUPHOLD SR 100/100` on the flops that use SR). The resolve
  chooses between the old and new next state `SR ? SRVAL : CE ? D : Q`;
  when they are the same 0/1 value, nothing is resolved.
- **Minimum pulse width.** A clean CK high pulse (or a low gap before a
  rise) of width p is judged with FID_RESOLVE's runt law:
  delta = p - TMPW + N(0, WMPW/4). If delta <= -WMPW/2 there is no capture
  (high runt: the flop keeps its pre-edge state; low runt: the edge
  re-captures the state the master held). Otherwise the result is new if
  delta > 0, else old, after TAU_FF ln(WMPW/2|delta|). **Source: none.**
  prjxray-db's `timings/*.sdf` have no WIDTH or PERIOD check for any cell,
  and the 7-series data sheet (DS187) could not be fetched from this session.
  TMPW = 70, WMPW = 40 ps (`+FF_MPW=`, `+FF_MPW_WIN=`, 0 = off) is an
  assumption, chosen so that the band [50, 90] ends below the fastest CK->Q
  in the SDFs here (99 ps), so the decision comes before Q moves. If a user
  sets TMPW + WMPW/2 > TCKQ - TCKI, a high runt judged after Q moved gives a
  Q glitch back to the outcome (pessimistic, stated).
- **BUFGCTRL.** I0->O is a transport delay (`TI0O`, the baked name),
  like ICBUF under GLS_TRANSPORT_IC. It has no pulse filter: no BUFG minimum
  pulse width is in prjxray-db, and the sink flop's TMPW judges a runt.
- Parameter names the baked netlist uses (`INIT, SRVAL, TCKQ, TSU, THD,
  SEED`; `TI0O`) are unchanged. The new parameters exist only under GLS_FID,
  so a testbench that sets them wraps them in `ifdef GLS_FID` (tb_f3_ff).

**tb_f3_ff** (TCKQ 300; run_f3.sh requires FAIL default, PASS fid):

| check | default | fid HEAD (pre-S6) | fid S6 |
|---|---|---|---|
| F1 120 ps CK runt, next rise 240 ps later: Q 1300 / 1540 | no Q edge (both swallowed) | ok | ok |
| F2 30 ps CK runt (below the band): no capture | captures | captures | ok |
| F3 70 ps runt x200: both outcomes, no X | 1 every time | 1 every time | 97 / 103, X 0 |
| F4 arcs 100: 40 ps SR pulse at a rise, then two rises 200 ps apart: 1300->0, 1500->1, 1800->0 | 1 edge (1800) | ok | ok |
| F5 arcs 100: CE dips 1990-2010 around a rise (CE edge 20 ps after CE edge): hold, then 2500->1, 2700->0 | no edge | ok | ok |
| F6 SR rises 10 ps before CK (window +-40) x200: both outcomes | 0 every time | 0 every time | 59 / 141, X 0 |
| F7 TSRI 200 vs TCKI 1: SR 50 ps before CK misses that edge | SR seen | n/a (no arcs) | ok |
| G1 120 ps pulse into a 200 ps BUFG clocks the flop behind it | swallowed, no clock | swallowed | ok (O 1200/1320, Q 1500) |

The "fid HEAD" column ran with a copy of tb_f3_ff that has the
`ifdef GLS_FID` parameter overrides deleted. F1, F4 and F5 already passed
there, because the pre-S6 Q path was transport. What S6 adds is shown by F2,
F3, F6, F7 and G1.

**tb_f3_kleene_ff:** 3000 random vectors, x on D 15%, CE 10%, SR 4%, CK x
on 3% of pulses, four flops (one behind a BUFGCTRL), state carried across
vectors. The settled Q is identical under default and fid. A mutated fid
flop (x on CE loads D, made by a sed in run_f3.sh) differs on 318 lines, so
the check can fail.

**Default build unchanged.** `iverilog -E` of HEAD's and the new prims.v,
with no defines and with `-DGLS_TRANSPORT_IC`, are identical (blank lines and
`line markers ignored, as in section 6). A small netlist (12 ICBUFs, a
BUFGCTRL, 8 LUTs feeding 8 SLICE_FFX with mixed INIT/SRVAL, SR/CE driven,
TSU 60 / THD 40, 4000 random events, 152 violation lines) gives
byte-identical VCDs (all but `$date`) with the old and the new prims.v:
65,107 value-change lines plain and 66,503 with GLS_TRANSPORT_IC. The logs
are identical apart from the dumpfile path. Under fid the same bench
differs.

**Found here: gen.py drops negative SETUPHOLD values.** `RE_SH` matches
`\((\d+):...`, so `(SETUPHOLD (posedge D) (posedge CK) (-60:...) (241:...))`
and CE's `(109) (-5)` never match. On the bq3 seed-3 route (min column), 42
of 326 baked flops have TSU/THD, and they are exactly the 42 with an SR
SETUPHOLD (100/100). The other 284 flops get no aperture: the default model
checks nothing, and fid uses the 50 ps `+META_FFW` default. The 42 get the
SR window, not D's (-60/+241). It was NOT fixed: the fix changes the default
baked netlist and the gate's numbers, so it is the main thread's decision.
The model already treats TSU/THD <= 0 as "use the default", which would also
need a decision for a genuinely negative setup.

**Library and rig dependence.**
- `bd_flink` (`cells/rtl/bd_mlink.v`, not integrated) clocks an FDRE bank
  from a LUT, `ck = ~rst & (done ^ ack_out)`. A done/ack_out race there is
  exactly a CK runt. Under default the LUT path swallowed it. Under fid HEAD
  any runt clocked the bank. Under S6 the TMPW law decides, so its GLS
  verdict depends on the assumed TMPW.
- `bd_mem` (USE_BUFG=1) puts a BUFG between the strobe and RAMB18 CLK. prims.v
  has no RAMB model, so the BUFG change does not reach it in GLS.
- Rigs with synchronisers or async-fed flops (arb_mtbf `sync1/sync2`, the
  FDSE `rst_sr` chains in gcd_hw and other `*_ps` rigs, BUFG-clocked counters)
  see behaviour change only on an aperture or runt event. The SR-in-aperture
  rule is new for the reset synchronisers.
- No other cells/rtl cell has a flop or a BUFG (bd_latch keeps its storage in
  LUTs).

Not done (S6): no routed GLS under fid with the new flop and BUFG (nextpnr was
not allowed, and the machine is nearly full); no per-pin skew derived from
the per-pin SETUPHOLD centres (TDI/TCEI/TSRI default to TCKI); no async
SR (FDCE/FDPE are not emitted by this flow; gen.py would need a mode); no
BUFG minimum pulse width or CE/S glitchless-mux model (I1 is permanently
deselected here); the cell-simulation stand-ins (`cells/sim/bd_prims_sim.v`,
its BUFG; it has no flop model) were not touched; DSP left alone.

## Files
- added (S6): `cells/gls/fid/f3/{tb_f3_ff.v, tb_f3_kleene_ff.v}`; changed (S6):
  `prims.v` (GLS_FID SLICE_FFX and BUFGCTRL), `run_f3.sh`
- added (S5): `cells/gls/fid/f3/{tb_f3_carry.v, tb_f3_latch.v, tb_f3_kleene_c4.v}`;
  changed (S5): `prims.v` (GLS_FID CARRY4 and SLICE_LATX), `run_f3.sh`
- added: `cells/gls/fid_core.vh`, `cells/gls/fid/f3/{run_f3.sh, tb_f3_lut.v,
  tb_f3_meta.v, tb_f3_kleene.v, tb_f3_arbm.v, gen_arbm_sig.py,
  meta_summary.py, vcd_norm.py, ring_scatter.py, test_variation.sh,
  lut_hazards.py}`, this file
- changed: `cells/gls/prims.v` (GLS_FID variants of SLICE_LUTX, SELMUX2_1,
  SLICE_FFX. The default modules only gain unused META*/TLOOP*/SEED
  parameters so one testbench elaborates on both), `cells/gls/gen.py`
  (GLS_MODEL=fid state-node and seed parameters, GLS_SCATTER_REGION,
  GLS_SDF_FIELD=band), `cells/gls/build.sh` (GLS_MODEL=fid compile and
  provenance line), `cells/sim/bd_prims_sim.v` (single corner, BD_FID),
  `cells/tb/tb_end.v` (expected period from the macros)

## Open
- TAU/WIN for a LUT loop and the flop tau at 28 nm are not measured.
  hw/arb_mtbf on the board is the instrument. Until then the defaults are
  stated assumptions, chosen to be long.
- Loops through more than one cell (for example a LUT plus MUXF7, or two
  LUTs) get no resolver. gen.py only detects self-loops.
- DSP keeps iverilog module paths (sample at fire). CARRY4 and the
  latch-mode FF are transport since S5 (section 6); SLICE_FFX pins and
  BUFGCTRL since S6 (section 7). The flop minimum pulse width (70 +- 20 ps)
  is an assumption, not a measurement.
- gen.py drops every SETUPHOLD with a negative number (section 7), so most
  flops get no SDF aperture. Fixing it changes the default baked netlist.
- With fid, a full gcd_hw / kernel routed GLS has not been run (no such
  route in this worktree). The next step is GLS_MODEL=fid on BQ#3's route
  with the 16 vectors.
- The decoupled attempt's new deadlock under one corner was not root-caused.
  It is not a library cell.
