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

## Not shown

- One route per build, at the calibrated bands (no scatter, no PVT corner), on the simulator, not silicon.
- Settle times depend on the inputs (one seed value, 256 rounds), so the "worst settle seen" is not a bound.
- Collatz: next (PROGRAM: "xorshift first, then collatz").
