# Where one iteration's time goes (PROGRAM.md, FIRST item)

A measurement. It changes no design and no sizes.

## Method

**Stack.** Each build is a board bench top (`*_bench_gen`, the route the board list names) on the full stack:
- the netlist is decoded from the `.bit` (`fasm2net --ps7`, fasm_equiv VERDICT in each `provenance.txt`);
- prjxray SDF (`xray_delay.py`), `GLS_MODEL=fid`;
- the calibrated bands with no scatter: delay chains at 0.21, CARRY4/F7/FF at 1, everything else at 0.288. These are the `worst` column's bands; the scatter is left out so the run is deterministic.

**Run.** `ps7_bench.v` runs one vector with 256 rounds twice, at `+FCLK_PS=12000`. The answer is checked against the C source. Every net of the decoded netlist is dumped to a VCD (`cells/gls/` is unchanged; `dump.v` is a separate top).

Tools are in `research/tools/itercost/`:
- `trace.py`: causal back-trace.
- `categorize.py`: categories.
- `analyze.py`: the cycle, the tables and the sum check.
- `lengthen.sh`: the lengthening check.

**1. Critical cycle.** In the fid model every primitive is a transport delay per (pin, output) arc. So an output edge at `t` has exactly one cause: an input-net edge at `t_src` with `t_src + wire + arc = t`. `cause()` finds that edge and reports the slack, which is zero on an exact hop.

The walk starts from a steady-state rise of a loop marker (`n8_u_req`, the output of umux1, in run 2 of the vector). It steps back cause by cause until it reaches the previous rise. It must close on the marker itself, and every hop must be exact; otherwise nothing is reported. This is the actual chain of events read from the trace, not a netlist or delay-total inference.

**2. Categories.** Each hop's cell is named from the routed JSON (BEL to nextpnr cell). The categories partition the period:

| category | what it is |
|---|---|
| rtz | every hop whose output is a FALLING edge of a control net (4-phase phases 3-4), wire and arc, whatever the cell |
| routing | wire part of a rising hop into or out of a handshake cell: the req/ack wires between cells |
| handshake | arc part of a rising hop through a handshake cell: C-elements, joins, forks, steers, acks, arbiter, LUT latches |
| delay | rising hops through matched-delay elements (`udly`/`rdly`/`uack` chains and the `uor` link), wire and arc |
| logic | rising hops through datapath cells, plus the part of each delay that its bundled data really needed |
| excess | the rest of each delay |

The delay split works per delay instance on the cycle. Let `t_a` be the event entering the instance and `d` its time on the cycle. Then:
- **settle** is the last arrival (edge time plus wire) of the data that instance bundles, at any of the data's loads:
  - a fused region's or mux's `z_data`;
  - a merge's `index`;
  - a link's `data_out`;
  - a pipe stage's output.
- **logic** = `clamp(settle - t_a, 0, d)`.
- **excess** = `d - logic`.

`delays.tsv` also gives each delay's worst `settle - entry` over all 512 iterations of the run. That includes loop entry and exit, the only iterations where the loop-control data changes. It is input-dependent, so it is not a static bound.

**3. Self-check.**
- The categories add up to the measured period to the picosecond (gate: 1%).
- Lengthening one delay element on the cycle raises the iteration time by the predicted amount. Lengthening one off the cycle does not (`lengthen.tsv`).

## xorshift (bench top, NEXTPNR_SEED=1, the board list's routes)

Routes:
- T3: sdf `e3024283`, bit `52c48942`.
- x0.5: sdf `c5b8ca02`, bit `c6f26526`.

Both are nextpnr `9c732bc6303458df`. The T3 decode is NOT_EQUIVALENT of the known benign kind only (a GND-buffer LUT on a CARRY4 DI). Both runs return `cd3132bf`, the C reference for seed 0x92d68ca2 with 256 rounds.

The period is constant in steady state: 508 of 511 marker intervals are identical, to the picosecond.

| ns per iteration | x0.5 | T3 |
|---|---:|---:|
| measured period (marker to marker) | **39.06** | **57.03** |
| hops on the cycle (all exact) / stages | 86 / 13 | 123 / 13 |
| logic | 1.03 (2.6%) | 1.01 (1.8%) |
| excess delay | 11.79 (30.2%) | 21.77 (38.2%) |
| handshake (cell arcs) | 1.23 (3.1%) | 1.23 (2.2%) |
| routing (req/ack wires) | 7.85 (20.1%) | 9.10 (16.0%) |
| return-to-zero | 17.15 (43.9%) | 23.92 (41.9%) |
| of RTZ: delay chains falling | 8.07 | 13.59 |
| of RTZ: handshake cells falling | 9.08 | 10.33 |
| sum - period | 0 ps | 0 ps |
| **bound logic + handshake** | **2.26** | **2.24** |
| bound + all req/ack routing | 10.1 | 11.3 |
| Dynamatic (same kernel, clock margin included) | 12.73 | 12.73 |

Wire against cell arc, x0.5: wires are 33.5 ns of 39.06 (86%) and cell arcs 5.6 ns. A delay chain is mostly routing: its rising part is 12.8 ns, of which 10.9 ns is wire between the chain's LUTs. Its arcs are 62 ps per element.

### The critical cycle is the loop-control ring, not the xorshift datapath

The 13 stages on the cycle, in order:
1. umux1 (x's loop mux)
2. ulink_n8
3. ucond_br7 (x's steer, through its acknowledge only)
4. ulink_n_trueResult_8
5. ulink_n11__1
6. ucmpi1 (`i+1 < rounds`)
7. ufork9
8. ucond_br9_j and ucond_br9 (the control token's steer)
9. ulink_n_trueResult_12
10. ucontrol_merge0 (the arbitrated loop-header merge)
11. ucontrol_merge0_f
12. ulink_n12__1 (umux1's select, a 2-stage pipe)
13. back to umux1

The cycle runs once on rising edges and once on falling edges. None of the xorshift arithmetic is on it: uxori1, uxori2, uaddi0, umux0, umux2 and their links are off it.

Check: +500 ps on one element of uxori1's delay leaves the period unchanged (836 cycles before and after). +500 ps on one ucmpi1 delay element raises it by 11 cycles, predicted 10.7: that delay is on the rising pass only, because its fall takes the gated fast path. +500 ps on one element of the n12__1 pipe's rdly raises it by 22 cycles, predicted 21.3: that delay is on both passes.

In steady state, no data on the cycle changes, except the merge's index bit, which returns to zero with its grant:
- **ulink_n11__1** carries `rounds`, which is loop-invariant.
- **ucmpi1's** result is 1 until the exit iteration.
- **umux1's** select is 1 until the exit iteration.

So the delays on the cycle bundle data that does not move. Their per-iteration logic is 0. Over the whole run, the worst settle each delay saw is below its length:

| delay on the cycle | x0.5: on cycle / worst settle seen (ns) | T3: on cycle / worst settle seen (ns) |
|---|---|---|
| ucmpi1.udly (compare) | 4.01 / 2.64 | 7.92 / 0.83 |
| ulink_n12__1 stage[1] rdly (select bit) | 3.12 / 1.31 | 5.77 / 1.32 |
| ulink_n11__1 rdly (rounds) | 2.13 / 1.74 | 3.90 / 2.02 |
| ucontrol_merge0.udly (index) | 1.89 / 1.43 | 2.46 / 1.01 |
| umux1.udly (x mux) | 1.26 / < 0 | 1.86 / < 0 |
| ulink_n12__1 stage[0] rdly | 0.42 / 0.76 | 0.88 / 1.00 |

For umux1, x arrives before the mux's delay starts. For stage[0], the data reaches stage[1]'s latch, which opens only after stage[1]'s own handshake, so this is not a bundling failure.

Why each stage on the cycle exists, from bdc's `link_sites()` on this kernel:
- ulink_n11__1, ulink_n12__1, ulink_n8 and ulink_n_trueResult_8 are **rule-1 measurability sites**: storage in front of a delay-bearing cell, so that `tighten.py` has a start point.
- ulink_n12__1's second stage is the **+1 throughput slack stage** (`BDC_SLACK_STAGES`).
- ulink_n_trueResult_12 is the only **rule-2 ring-storage** link on the cycle (ring floor 3).
- Stages carrying no logic in steady state: every link (5 instances, 6 latch stages); the forks; the steers, which only pass acknowledges here; and ucmpi1 and umux1, whose outputs are constant until exit.

Per stage (x0.5; T3 in `T3_seed1/stages.tsv`):

| stage | ns on the cycle | of which RTZ | of which excess delay |
|---|---:|---:|---:|
| ulink_n12__1 (2-stage pipe, select bit) | 9.17 | 4.58 | 3.53 |
| ulink_n11__1 (rounds) | 5.49 | 2.75 | 2.13 |
| ucmpi1 | 5.27 | 0.94 | 4.01 |
| umux1 | 4.48 | 1.71 | 1.26 |
| ucontrol_merge0 | 3.99 | 1.31 | 0.86 |
| ulink_n_trueResult_12 | 2.25 | 1.13 | 0 |
| ucond_br9 + ucond_br9_j | 2.94 | 1.47 | 0 |
| ucond_br7 | 1.46 | 0.73 | 0 |
| ulink_n8 | 1.24 | 0.62 | 0 |
| ulink_n_trueResult_8 | 1.08 | 0.54 | 0 |
| ucontrol_merge0_f | 1.03 | 0.52 | 0 |
| ufork9 | 0.65 | 0.32 | 0 |

### Levers, ranked by the time each could recover (x0.5; T3)

These are upper bounds read off this cycle. Shortening the cycle moves the critical cycle elsewhere (the xor ring has at least 0.5 ns of slack, and how much more is not measured). None of these was built.

1. **Two-phase signalling** removes the falling pass: 17.2 ns (44%); T3 23.9 ns. It is the largest lever on both builds.
2. **Fewer stages on the control ring.** The four rule-1 links on it hold 17.0 ns of the cycle; T3 27.5 ns. ulink_n12__1 alone is 9.2 ns (23%), and its slack stage is part of that. They are measurability sites for data that does not change inside the loop. The ring floor (3 stages per cycle) still needs storage somewhere.
3. **Delay chains bundling loop-invariant data.** The rising excess is 11.8 ns; T3 21.8 ns. Sizing each delay to the worst settle seen in this run would recover about 5.3 ns; T3 about 16.7 ns. That is not safe, because the settle depends on the inputs and the guard must be kept. Structurally, `rounds` and the loop-exit compare need bundling only at loop entry and exit.
4. **Fast fall on the chains that still fall at full cost:**
   - x0.5: ulink_n11__1 rdly, the n12__1 pipe rdlys and umux1's udly, 6.9 ns;
   - T3: 12.4 ns.

   ucmpi1's and the merge's gated chains already fall fast (0.5-0.6 ns).
5. **Routing.** Wires are 86% of the period: 7.9 ns of req/ack routing between control cells, plus most of every delay chain. Placement (keeping each control ring and chain local) is a lever on all of the above, not measured here.
6. **Smaller guard.** This is inside the excess in item 3; the excess is far larger than any guard.
7. **Delay chains overcovering their block** (for example a constant shift built as a barrel shifter): not on this cycle. The xor regions' delays are off the critical cycle, so shortening them recovers nothing on this route.

### Explanations retired or confirmed

- **"The xorshift's datapath matched delays are the cost": ruled out on these routes.** The xor regions are not on the critical cycle, and lengthening one by 0.5 ns changes nothing. The matched delays that ARE on the cycle are 54% (x0.5) and 64% (T3) of the period, rising plus falling. But they bundle the loop-control channels, whose data does not change inside the loop.
- **"Paid on both edges"** is half right. Falling edges are 42-44% of the period, but only 21-24% are delay chains falling. The rest is the handshake cells' and wires' own return to zero, which fast fall cannot touch. Link fast fall's measured 6-12% gain fits the 14-18% of the period that ulink_n11__1's and ulink_n12__1's rdlys spend falling.
- **logic + handshake = 2.2 ns per iteration** against Dynamatic's 12.73 ns. Even with all request/acknowledge routing added, it is 10-11 ns. What the async build pays is protocol (RTZ), routing, and delay chains on a control ring that carries no changing data.

## collatz (bench top, NEXTPNR_SEED=1, the board list's routes, item #9)

Routes:
- T3: sdf `6134880a`, bit `e6b7bdf7`.
- per-cell "cs": sdf `1ab39716`, bit `07b0fbef`.

Both decode EQUIVALENT (benign kinds only). The vector is n=6171, 261 steps, run twice; both builds return 261. The bench masks collatz's n to 16 bits (`loop_cost.sh`), so 2^30 becomes n=1, 0 steps; that is correct and was not used.

umux1's output is NOT on the critical cycle: the back-walk passes its previous rise without touching it. So the marker is `n26_u_req`, the output of uaddi0, found as a net that repeats at exactly one period on a 4-period walk.

All 518 steady-state iterations are traced (`iterations.tsv`), and every one closes exactly with categories summing to its period. **Even and odd steps take the identical period, to the ps.** Both branches are computed every iteration and a select picks one, so the cycle does not depend on the branch.

| ns per iteration | cs (per-cell) | T3 |
|---|---:|---:|
| measured period | **67.82** | **77.56** |
| hops / stages | 150 / 13 | 180 / 13 |
| logic | 9.34 (13.8%) | 9.50 (12.3%) |
| excess delay | 30.99 (45.7%) | 37.73 (48.6%) |
| handshake | 1.10 (1.6%) | 1.10 (1.4%) |
| routing | 8.84 (13.0%) | 7.57 (9.8%) |
| return-to-zero | 17.56 (25.9%) | 21.66 (27.9%) |
| of RTZ: delay chains / handshake cells | 7.62 / 9.93 | 12.99 / 8.67 |
| sum - period | 0 ps | 0 ps |
| **bound logic + handshake** | **10.44** | **10.60** |
| bound + all req/ack routing | 19.3 | 18.2 |
| Dynamatic (README.md) | 14.05 | 14.05 |

Mean over the 518 iterations, by parity of n (cs): even logic 8.31 / excess 32.03 ns, odd 8.19 / 32.15. The table above is one representative iteration.

Wires are 85-86% of the period, as for xorshift.

**Self-check** (`lengthen.tsv`):
- +500 ps on one uselect0 delay element raises the cycle count 1479 to 1490 (predicted 1489.9).
- +500 ps on uaddi1's (the step counter, off the cycle) leaves it at 1479.

### Here the cycle is the n datapath

The cycle runs:
1. uaddi0: 3n+1, as `(n << e1) + n + 1`
2. ulink_n26
3. uselect0: `n & 1 ? 3n+1 : n >>> e3`
4. ulink_n28__1
5. ucmpi2: `n != 1`
6. ucond_br6_j and ucond_br6 (n's steer)
7. ulink_n_falseResult_7
8. ucontrol_merge0
9. ulink_n14__0 (umux0's select)
10. umux0
11. ulink_n10__1 (or ulink_n10__2 on the T3 route)
12. back to uaddi0

As for xorshift, it runs once on rising edges and once on falling edges.

Two of the regions on the cycle compute something every iteration:
- **uaddi0:** logic 5.2-5.9 ns of an 11.2-11.9 ns delay.
- **uselect0:** logic 2.8-2.9 ns of a 12.2-12.4 ns delay.

Both shift by a constant 1 that reaches the region as a **data channel**: handshake `constant4`, fired once per iteration and forked five ways, so it is not folded into the region. yosys therefore builds two 32-bit barrel shifters. The delays are sized to the barrel shifters' static paths, while the trace sees the shift-by-one paths. That is PROGRAM's "a constant shift synthesised as a barrel shifter", measured: 16.3 ns (cs) and 14.6 ns (T3) of excess delay on the cycle, in these two regions alone.

The rest of the cycle again bundles data that does not change in steady state:
- ucmpi2's result is 1 until exit (8.0-8.4 ns of delay, logic 0, worst seen 3.1-3.3 ns).
- ulink_n14__0 carries umux0's select (4.1-7.1 ns of rdly on the rise and again on the fall).

Links on the cycle: ulink_n26, ulink_n28__1, ulink_n10__x and ulink_n14__0 are rule-1 measurability sites. ulink_n_falseResult_7 is the rule-2 ring-storage link (floor 3).

| stage (cs) | ns on the cycle | RTZ | excess | logic |
|---|---:|---:|---:|---:|
| uselect0 (select, barrel shift) | 14.57 | 1.47 | 9.58 | 2.82 |
| uaddi0 (3n+1, barrel shift) | 14.09 | 1.30 | 6.68 | 5.23 |
| ulink_n14__0 (umux0 select) | 9.78 | 4.89 | 4.11 | 0 |
| ucmpi2 (n != 1) | 9.66 | 1.17 | 7.95 | 0 |
| ucontrol_merge0 | 5.99 | 1.86 | 1.72 | 1.29 |
| umux0 | 3.06 | 1.53 | 0.95 | 0 |
| ulink_n_falseResult_7 | 2.24 | 1.12 | 0 | 0 |
| ucond_br6 + ucond_br6_j | 3.01 | 1.51 | 0 | 0 |
| ulink_n10__1 / ulink_n28__1 / ulink_n26 | 1.43 / 1.42 / 1.31 | 0.72 / 0.71 / 0.65 | 0 | 0 |
| ucontrol_merge0_f | 1.26 | 0.63 | 0 | 0 |

### Levers, ranked (cs; T3)

1. **Delays overcovering their block:**
   - The excess is 31.0 ns (46%); T3 37.7 ns.
   - Sizing every delay on the cycle to the worst settle seen in this run would recover 24.4 ns; T3 31.4 ns. That is not safe as it stands: it is input-dependent and the guard must be kept.
   - The structural part is folding the shift-by-one constant into uaddi0 and uselect0, which removes the barrel shifters: up to 16.3 ns; T3 14.6 ns.
2. **Two-phase:** 17.6 ns (26%); T3 21.7 ns.
3. **Fewer stages:** the four rule-1 links hold 13.9 ns; T3 19.1 ns. ulink_n14__0, a 1-bit select, holds 9.8 and 15.1 ns of that.
4. **Routing:** 8.8 ns of req/ack wires, plus most of every chain.
5. **Fast fall** on the chains that still fall at full cost (ulink_n14__0's rdly and umux0's udly): 5.1 ns; T3 9.9 ns.

### Across the two kernels

- logic + handshake is 2.2 ns per iteration (xorshift) and 10.4-10.6 ns (collatz). Dynamatic's closed clock period is 12.73 ns and 14.05 ns.
- The async builds are 3.1-4.5x (xorshift) and 4.8-5.5x (collatz) slower. The difference is excess delay (30-49%), RTZ (26-44%) and routing (10-20%). It is not logic.
- RTZ costs E = P / (P - RTZ) = 1.78x on xorshift and 1.35x on collatz, against the x1.5 that README.md's model assumes.
- The "matched delays are the cost" claim holds on collatz, where its datapath delays are on the cycle. It does not hold on xorshift, where the datapath is off the cycle and the delays that cost are on the loop-control ring.

## Not shown

- One route per build, at the calibrated bands (no scatter, no PVT corner), on the simulator, not silicon.
- Settle times depend on the inputs (one value per kernel), so the "worst settle seen" is not a bound.
- A bound by idealisation failed (`research/tools/itercost/zero_delays.py`, a negative result).
  - The six delay instances on x0.5 xorshift's control ring were set to 1 ps arcs and 1 ps input wires.
  - The kernel deadlocked after its first iteration: umux1's output rose once and never again.
  - Meanwhile some net kept switching for 155 µs of sim time, after which the run was stopped.
  - So "remove the ring's delays" is not a measurable what-if on this route. Those delays order the first token's handshakes, not only its data. Levers 2-4 above are therefore read off the cycle, not simulated.
- Only the first critical cycle. Once a lever shortens it, another ring becomes critical. For xorshift, the xor ring has at least 0.5 ns of slack (`lengthen.tsv`); how much more is not measured.

## Every delay line on collatz's loop (owner's second lead, 2026-11-15) -- item 25 on one route, then on 28 routes

Tool: `research/tools/itercost/line_account.py` (corner_audit's own worker and the audits' path functions; per line:
the constraint that sets it, the covered data path split into logic / latch / enable spread / wire, the request path,
guard, margin, elements needed as routed and for the logic alone). Route ceb_24 (sdf e001dc27, nextpnr
9c732bc6303458df), worst corner; nominal and the arc-by-arc paths in `collatz/line_account_ceb_24/`. The >= 8 route
table follows once the farm runs it.

On this route the critical cycle is NOT the datapath: it is umux1's select ring (ulink_n13 -> ulink_n14__1), 35.92 ns,
of which the 36-element select line ulink_n14__1 stage[1].rdly is 13.7 ns rising + 13.7 ns falling. The datapath loop
(ulink_n14__0, umux0, uaddi0, uselect0, ulink_n10__4's ack fall) is next, 34.32 ns.

| line | n | ps at worst | on cycle R/F | set by | margin | covered data: logic/latch/enable/wire (total) | n need (as routed) | n logic only |
|---|---|---|---|---|---|---|---|---|
| ulink_n14__1 st1 rdly (select) | 36 | 13291 | 13698/13698 | select rule only (rule E +13.2 ns) | +13212 | 0/68/184/313 (565) | 1 | 0 |
| ulink_n14__0 rdly (select) | 18 | 6962 | 7684/0 | select rule only (rule E +7.1 ns) | +7116 | 0/68/482/313 (863) | 1 | 0 |
| uselect0 udly | 16 | 5473 | 5804/0 | rule A, bundled pairing (+1455 ps lag borrowed from ulink_n26) | +3230 | 204/0/0/2070 (3729) | 8 | 1 |
| uaddi0 udly | 12 | 4360 | 4775/0 | rule A' (3n+1 carry chain) | +2944 | 1489/73/957/561 (3080) | 5 | 4 |
| ulink_n10__4 uack | 6 | 2161 | 0/2720 | rule H; NOT in sizes.vh (RTL default 6) | +2978 | -- | 0 | -- |
| umux0 udly | 6 | 1813 | 2153/0 | rule A (ack path only; datamux unpaired) | +1926 | wire 657 + ctl 68 | 1 | 0 |
| umux1 udly | 5 | 1696 | 2020/565 | rule A (as umux0) | +1772 | wire 465 + ctl 68 | 1 | 0 |

Findings on this route (diagnosis; nothing is shortened from this table alone):
- The two select lines (27 of the 54 elements on the loop) sit on no constraint but the withdrawn select rule. Farm
  fcsel0 tests them at 0 on 32 routes with every check.
- uselect0 (`n & 1 ? 3n+1 : n >> 1`) is 204 ps of logic and 2070 ps of wire: a kept LUT1 (uz_n29) drives a 32-bit
  fanout net, 279-1250 ps across the bits -- the wire the owner asked about. Its 16 elements come from tighten's
  bundled pairing, which adds 1455 ps of controller-to-latch lag from ulink_n26, the worst upstream link; the data's own
  link (n11) has 0. A' (from the upstream C nodes) would give +5419 ps / 2 elements, but corner_audit refuses A' here
  because two "foreign" sources reach the data: the reset flop (static in operation: a false-path candidate) and the
  request of the folded constant operand n12 = 1 (usource2), joined although its data is folded. Fix the cause: do not
  join a folded constant's request (as compute fusion already does), and exclude the reset flop as a launch.
- Links that carry only constants (ulink_n19__1..4: the shift amount and the constants joined into uaddi0 / uselect0)
  are 32-bit latch banks whose D pins are tie-offs; their ack lines are built at the RTL default 6 because sizes.vh has
  no macro for them; ULINK_N10__4_UACK too (6, on the datapath cycle's falling edge, rule H says 0).
- uaddi0 is a real carry path; 0.78 ns of its 0.96 ns enable term is the enable net's spread over 32 latch bits.

### Item 25 on 28 routes (farm fceq_la, worst corner; 2026-11-16)

`research/tools/itercost/la_aggregate.py fceq_la worst` over line_account's per-route tables (31 routes built, 28 with
an event graph; period median 35.92 ns, 33.38-38.51). A line is listed on a route only when it is on that route's
critical or near-critical cycle, so "8/8" means: present on 8 routes, on the cycle on all 8. Medians, (range).

| line | routes on cycle | n | ps | on cycle (R+F, ps, median of those) | set by (routes) | margin ps | data logic / latch / enable / wire | n_need | n_logic |
|---|---|---|---|---|---|---|---|---|---|
| ulink_n14__1.many.stage[1].u.rdly | 28/28 | 36 | 13494 (12357..14591) | 27805 (25770..30040) | E depends 28 | 13350 (12059..14443) | 0 / 68 / 183 (160..482) / 322 (273..733) | 1 (1..2) | 0 |
| umux1.udly | 28/28 | 5 | 1491 (1111..1821) | 2388 (1888..3114) | A own 28 | 1815 (1233..2248) | 0 / 0 / 0 / 464 (281..654) | 1 (0..1) | 0 |
| ulink_n13.uack | 28/28 | 1 | 62 | 1163 (642..1682) | H own 28 | 1161 (446..2062) | -- / -- / -- / -- | 0 | -- |
| ulink_n14__0.rdly | 8/8 | 18 | 6902 (6178..7193) | 7630 (6835..7920) | E depends 8 | 7043 (6679..7791) | 0 / 68 / 178 (172..482) / 318 (279..601) | 1 (0..1) | 0 |
| uselect0.udly | 8/8 | 16 | 5546 (5211..6672) | 5812 (5628..7009) | A own 8 | 3167 (2690..4478) | 204 / -- / 0 / 2030 (1672..2330) | 8 (6..9) | 1 |
| uaddi0.udly | 8/8 | 12 | 4256 (3667..4455) | 4580 (3968..4849) | A' own 8 | 2765 (2326..3243) | 1484 (1330..1500) / 75 (68..76) / 933 (726..1315) / 648 (557..889) | 5 (4..6) | 4 (4..5) |
| ulink_n10__4.uack | 8/8 | 6 | 1962 (1645..2434) | 2626 (2317..3595) | H own 8 | 2984 (2845..3734) | -- / -- / -- / -- | 0 | -- |
| umux0.udly | 8/8 | 6 | 1850 (1630..2105) | 2356 (2153..2652) | A own 8 | 2240 (1926..2528) | 0 / 0 / 0 / 500 (329..657) | 1 | 0 |
| ulink_n_falseResult_9.many.stage[0].u.uack | 8/8 | 3 | 742 (618..856) | 595 (419..703) | H own 8 | 1007 (859..1339) | -- / -- / -- / -- | 0 (0..1) | -- |

Reading, over 28 routes (it confirms the one-route table and makes it general):
- On every route the critical cycle is umux1's select ring (ulink_n13 -> ulink_n14__1), and ulink_n14__1's 36-element
  select line is 27.8 ns of it (25.8-30.0, rise + fall). Its rule E margin is +13.4 ns (12.1-14.4): the data it bundles
  is 0.6 ns (latch 68 + enable spread 183 + wire 322 ps). It needs 1 element as routed (at most 2). Item 28 (select
  links at 3, fcsel3m) took this: 35.9 -> 25.8 ns.
- On 8 routes the datapath loop is near-critical. uselect0's 16 elements cover 204 ps of logic and 2.0 ns of wire
  (1.7-2.3) and need 8 (6-9) as routed, 1 for the logic alone: the 32-bit fanout of the kept LUT1, and the 1.45 ns
  of borrowed lag from the bundled pairing, as on seed 24. uaddi0 (the 3n+1 carry chain) is real logic (1.48 ns) and
  needs 5 of its 12. ulink_n10__4's ack (6, no macro in sizes.vh) sits on the datapath cycle's fall with +3.0 ns of
  rule H margin (fcsel1m: dropping it bought -0.32 ns median).
- The same table on item 28's own routes (fcsel3m_la), on collatz64 item 26 (fc64eq_la) and ipow item 19 (fipowrh_la)
  is on the farm.
