# Probe Bh: the B-gls-compare predictions, run in iverilog

Probe: run the cheapest predictions of `B-gls-compare.md` §5 (P6, P3, P4b, P5b, P1b, plus
P6b) in iverilog on the real models, and say for each whether it matches the formal
prediction. Every run has a negative control that can fail, and the control did fail.

Nothing routed was produced, so the toolchain/seed rules do not apply: no nextpnr, no SDF
and no placement were involved. Every number below comes from **unrouted cells with
hand-set wire delays**. These are cell-level GLS runs, not a design-level GLS, and they say
nothing about any particular route.

Nothing in the repo was changed except this file.

## Setup

- **Simulator.** iverilog 12.0 (Ubuntu package `12.0-2build2`). I installed it in this
  container with `apt-get install -y iverilog`, for local use only. `-gspecify` is passed
  everywhere.
- **Cells.** These are the frozen `cells/rtl/bd_ce.v`, `bd_arb.v` and `bd_latch.v`, copied
  byte for byte into the scratch dir (`SOURCES.sha256` records the hashes). Two prims sets
  were used:
  - **cells/sim:** `cells/sim/bd_prims_sim.v`, with rise 56 / fall 124 and the O5 per-pin
    pairs.
  - **research GLS:** `git show origin/claude/research:cells/gls/prims.v` at `7e90c4f`
    (`SLICE_LUTX`, `ICBUF`), read-only. There are two builds:
    - **gate**: the default, with the specify-path ICBUF. This is the annotated acceptance
      build.
    - **baked**: `-DGLS_TRANSPORT_IC`, the transport ICBUF that `build.sh`'s
      `run_baked.vvp` uses.
- **Shim.** The cells instantiate `LUT6` / `LUT6_2`, but the research prims are bel models.
  `rshim.v` (full text in the appendix) maps each LUT onto one `SLICE_LUTX`, using the
  identity pin map (I0→A1 … I5→A6, INIT unchanged). It puts one ICBUF on each input pin, with
  a per-instance `W0..W5` delay (set by `defparam`), as gen.py does per sink. `ARC` / `ARC5`
  set the O6/O5 arcs (default 124 = SLOW_MAX, rise = fall, as in the research GLS).
  `-DLUT_TRANSPORT` replaces the SAF specify channel with a pure transport delay. That is the
  formal side's channel, and it serves as the negative control for the loop predictions.
- **Location.** All benches, scripts and logs are in
  `/tmp/claude-0/-home-user-asyncfpga3/7f52a4bc-3f11-5919-b34a-537c5f812fdf/scratchpad/glsruns/`
  (`tb_p*.v`, `sweep_p*.sh`, `logs/`). The standard compile line, run from that directory, is

  ```
  iverilog -g2012 -gspecify -Wno-timescale [-DGLS_TRANSPORT_IC] [-D...] -s tb -o build/x.vvp \
      research/prims.v rshim.v rtl/bd_ce.v rtl/bd_arb.v tb_pN.v && vvp -n build/x.vvp
  ```

  For cells/sim, `research/prims.v rshim.v` is replaced by `bd_prims_sim.v -DBD_ROUTE_PS=R`.

## 0. An iverilog artefact found on the way (it affects hierarchical benches, not the flat research GLS)

**What happens.** In the **gate** build, an ICBUF loses its delay (0 ps instead of D)
under one condition. Its input net is a net that some module instance has bound to **both an
input port and its output port**. That is every C-element and latch in the library:
`.I2(q) … .O(q)`.

**Minimal reproducer.** `probe/tb_ic5.v` is a module `L` with `.I2(q), .O(q)`, plus an
external `ICBUF #(.D(100))` reading `q`. The ICBUF output moves at q+0, not at q+100.

**What it does not affect.**
- The baked (transport) build is unaffected.
- Without the self-bound port the delay is correct (`probe/tb_ic.v`, `tb_ic2.v`, `tb_ic4.v`).
- gen.py's netlist is flat: each sink gets a private net driven by an ICBUF, and no instance
  has an input on its own output net. So **the research GLS proper should not be exposed**.
  I did not run gen.py, so this is argued from its source, not tested.

**Who is exposed.** Any bench that drives `cells/rtl` hierarchically through the research
prims in the gate build (as A-gls-compare's `tb_c2` variants did). It silently drops every
wire delay on a C-element's or latch's output fanout.

**Fix in the shim.** One extra continuous assignment or `buf` in front of the ICBUF restores
the delay (`rshim.v`'s `rpin`).

**Runs affected.** My first P3 and P6 gate-build runs had this bug. Their logs are kept as
`logs/*_SHIMBUG.log`, and everything below was rerun after the fix.
- The bug was visible in P3: the gate-build BOX overlap stayed at 37 ps for every R, while
  the baked build tracked 37 − R.
- Check after the fix: for single-edge stimuli the gate and baked builds must agree, and in
  P3 they now agree on all 45 rows.

## P6: 7i `arb_runt_held`, holds in every run

**Prediction.** A0 = 1 on both branches, with q = 1, g2 = 0, A1 = 1, A2 = 0. Then q, g2, A1
and A2 never move, whatever r1 and r2 do. **SYM** is the mirror case: q = 0, g1 = 0, A2 = 1,
A1 = 0.

**Bench: `tb_p6.v`.**
- Setup: reset, r1↑, A0↑, so A1 = 1. The bench checks the setup state.
- Stimulus: N random request edges.
  - In 40% of edges the gap is 0–3 ps; otherwise it is 0–1499 ps.
  - Edge kinds: r1 only, r2 only, r1 then r2 1 ps later, or both in one timestep.
  - `+XPCT=10`: 10% of request values are `x`.
- Check: it counts *events* on q, g2, A1 and A2 (on g1 in SYM), and checks the final values.
  It also counts g1/R0 events (g2/R0 in SYM), to show the stimulus reached the cell. That
  count is in the thousands in every run.
- `sweep_p6.sh` runs it on the research prims:
  - 40 random configurations, each with a random arc per LUT (20–600 ps) and a random wire
    per live pin (0, 1–30 or 1–2500 ps), from `genwires.py <cfg>`;
  - both builds, base and SYM, x off and on;
  - N = 5000.
- `run_p6.sh sim` runs it on cells/sim at BD_ROUTE_PS = 0, 8, 16 and 354, with 3 seeds each,
  N = 20000, base and SYM, x off and on.

**Commands.**
```
NCFG=40 N=5000 ./sweep_p6.sh > logs/p6_sweep.log
R=$R SEEDS="1 2 3" XPCT=$x N=20000 ./run_p6.sh sim [-DSYM] [-DNC_UNHELD]
```

**Result.**
- Research GLS: **320 of 320 library runs HOLD** (40 cfg × 2 builds × 2 start states ×
  2 x-modes; `logs/p6_sweep.log`).
- cells/sim: **48 of 48 HOLD** (`logs/p6_sim.log`).
- Zero events on the held nodes in every run, including 1 ps near-ties, same-timestep ties
  and x on the requests.

**Matches the prediction:** yes, exactly.

**Negative control (`-DNC_UNHELD`).** A scratch copy of `bd_arbiter` whose state LUT ignores
A0 (INIT `64'hFFB2_FFB2_ACAC_ACAC`, the pre-hold cell; `nc/bd_arb_unheld.v`). Same harness.
- **320 of 320 and 48 of 48 VIOLATED.**
- Typical run: hundreds of q and g2 events, A2 rises, and the run ends with **A1 = A2 = 1**.

**What this shows.** Every GLS run is inside 7i's unbounded-delay theorem, as argued in
B-gls-compare §3 ("SAF is a GMW gate").

**What it does not show.** The analog case: q at a mid-rail level. The binary and Kleene
models cannot produce that.

## P6b: 7i `arb_tie_acked` with q forced to x, holds

**Prediction.** Both requests rise from idle. While q is x, or wanders between x, 0 and 1,
R0 stays 1 and A1 = A2 = 0 as long as A0 = 0.

**Bench: `tb_p6b.v`.** It applies `force dut.q` 41 times (x, 0 or 1, holding each for
29–300 ps) and then leaves q at x. It counts any instant where R0 ≠ 1, A1 ≠ 0 or A2 ≠ 0.

**Result** (cells/sim, research gate and research baked): **0 violations**, and R0 = 1 when
the window ends. After A0 rises, A1 and A2 go to x and R0 stays 1. The theorem makes no claim
about A1/A2 after the ack, and that is what was observed.

**Negative control (`-DNC_NOTIE`).** Only r1 asks, so R0 = r1·q must follow q's x. The
result: **14, 18 and 18 violations**, R0 = x.

**Matches the prediction:** yes.

## P3: 7e `tb_arb` overlap vs uniform R

**Prediction.** Under the old 56/124 arcs the bare-cell r2→r1 handover overlap is
max(0, 16 − R) ps. The 16 ps is `124 − 56 − 52`:
- 124 is the falling O6 arc at SLOW_MAX;
- 56 is the rising state LUT and 52 the rising O5 I2 arc, both at FAST_MAX.

So 16 ps is a **corner mix**: no single die at one corner produces it (B-gls-compare §1).
At a consistent corner (rise = fall = d) the overlap is 0 for every R ≥ 0. The full box
(falling O6 at SLOW_MAX 124, state LUT at FAST_MIN 45, O5 at FAST_MIN 42) gives
max(0, 37 − R).

**Run 1: tb_arb itself, unmodified** (copied to scratch, `run_sim.sh`'s compile line).
```
iverilog -g2012 -gspecify -Wall -Wno-timescale -DBD_ROUTE_PS=$R -o build/tb_arb_$R.vvp \
    bd_prims_sim.v bd_env.v rtl/*.v attempts/*.v tb/tb_arb.v && vvp -n build/tb_arb_$R.vvp
```
- The overlap count is 1 instant for R = 0, 4, 8, 12 and 15, and 0 for R = 16, 17, 20, 56
  and 354.
- **tb_arb PASS** at every R.
- Caveat (ii) of B-gls-compare (a zero-length coincidence still counting one instant at
  R = 16) **did not happen**: at R = 16 the count is 0.

**Run 2: the overlap measured in ps, `tb_p3.v`.**
- The stimulus is the same shape as tb_arb's directed tie/handover, in both directions. It
  records `$realtime` at g1&g2 rise and fall, and prints the g1, g2 and q edge times.
- `-DGLS` puts W = R on every live pin of both LUTs. `-DBOX` sets the box arcs.
- `logs/p3_sweep.log`, 51 rows, compared against the prediction by script. **0 mismatches**:

| model | R swept | measured overlap (ps) | prediction |
|---|---|---|---|
| cells/sim 56/124 (+R per arc) | 0, 1, 2, 4, 8, 12, 14, 15, 16, 17, 20, 56, 354 | 16, 15, 14, 12, 8, 4, 2, 1, 0, 0, 0, 0, 0 | max(0, 16 − R): exact |
| research GLS, flat 124, gate and baked (+R per pin) | 0, 1, 8, 16, 37, 100, 354 | 0 everywhere | 0: exact |
| research GLS, flat 45 (FAST_MIN), both builds | 0, 8, 16 | 0 | 0: exact |
| research GLS, BOX 45/42/124, both builds | 0, 1, 8, 16, 30, 36, 37, 38, 100 | 37, 36, 29, 21, 7, 1, 0, 0, 0 | max(0, 37 − R): exact |

- The r1→r2 direction gives 0 in every model, as predicted. The falling O5 arc (152 in
  cells/sim) is shorter than the q-fall + O6-rise path.
- Edge times at R = 0 in cells/sim: q↑ 80057, g1↑ 80109, g2↓ 80125, measured from r2↓ at
  80001. These are exactly 56, 56 + 52 and 124 ps.

**Matches the prediction:** yes, to the ps.

**Negative control.** The BOX arm, the same harness with different arcs, predicts a nonzero
37 − R and measures it. Under cells/sim, R < 16 must give a nonzero overlap, and it does. So
the harness can see an overlap, and the zeros elsewhere are not vacuous.

**What it does not show.** Whether silicon has any rise/fall asymmetry (`H_RF_ASYM`,
unmeasured). The box figure is a worst case across corners, and nothing places one die there.

## P4b: bd_c2 set runt with a 295 ps feedback wire

**Prediction.** Set-runt widths S (a and b both high for S ps), feedback wire 295, arc 124,
loop D = 419. B-gls-compare's proxy predicted:
- the baked build rings for S in 125–294 (5d's band [ρ, D − ρ]);
- the gate build does not ring;
- with wfb = 60 < arc the band is empty.

**Bench: `tb_p4.v`.** `bd_c2` with W2 = WFB, starting from q = 0 with a = 0 and b = 1. Then
a rises, and b falls S ps later. The outcome is classified as HOLD, RINGS (q still moving in
the last 5 loop periods) or LATCH.

**Command.** `./sweep_p4.sh <wfb> 0 500 [-DGLS_TRANSPORT_IC] [-DLUT_TRANSPORT]`, at 1 ps
steps (`logs/p4b.log`).

**Result:**

| WFB | build | HOLD (q = 0) | RINGS | LATCH |
|---|---|---|---|---|
| 295 | baked (SAF LUT) | 0–123 | **124–295** | ≥ 296 |
| 295 | gate (SAF LUT) | 0–294 (124–294: **one runt pulse on q**, then 0) | none | ≥ 295 (295: runt, then latch) |
| 295 | baked + LUT_TRANSPORT (control) | 0 | 1–418 | ≥ 419 |
| 60 | baked / gate (SAF LUT) | 0–123 | none | ≥ 124 |
| 60 | baked + LUT_TRANSPORT | 0 | 1–183 | ≥ 184 |

- The baked ring band is **[124, 295] = [ρ, D − ρ] inclusive**. That is exactly 5d's
  theorem with ties in the band, and it matches A-gls-compare's earlier 124–300 for D = 424.
- The Python proxy's 125–294 is off by one at each end. That is its pulse-end convention:
  iverilog rings at the ties and the proxy does not.
- With wfb = 60 the band is empty (2ρ > D), as 5d says.
- The transport control rings for every 0 < S < D. That is 5b's `runt_oscillatesR`, which
  the formal side uses.

**Matches the prediction:** yes, with the boundaries corrected by one ps to the tie-inclusive
form.

**New detail.** The gate build "does not ring", but it is **not clean**. For 124 ≤ S ≤ 294
it emits **one output runt of width S** and then holds 0. At S = 295 it emits a runt, drops,
then latches (3 edges). The gate build's specify-path wire swallows the returning pulse, so
the runt never re-enters the loop. It still leaves the LUT output.

**Negative control.** The LUT_TRANSPORT arm, same harness. It rings across the window where
SAF holds, so the harness can classify a ring.

## P5b: bd_latch setup boundary

**Prediction.** d leads the enable fall at the pins by w. Feedback wire 295, arc 124.
- `w ≤ arc`: both builds keep the OLD value silently.
- `arc < w < wfb`: the baked build rings (period arc + wfb) and the gate build keeps OLD.
- Beyond that: NEW.
- 6c's H_SETUP, on the transport channel, needs `w ≥ wfb + arc = 419`.

**Bench: `tb_p5.v`.**
- Two shapes:
  - W = 1: the odd `LUT6`, INIT B8B8, feedback on I2;
  - W = 2: the `LUT6_2` pair, bit 0 on O5 with feedback on I2 and bit 1 on O6 with feedback
    on I4; both feedback pins carry WFB.
- Stimulus: en = 1 and d = 0 give q = 0. Then d rises at T − w and en falls at T.

**Command.** `./sweep_p5.sh <wfb> <W> 0 500 [-DGLS_TRANSPORT_IC] [-DLUT_TRANSPORT] [-DPAIR]`
(`logs/p5b.log`).

**Result** (W = 1 and the W = 2 pair are identical, with both bits moving together):

| WFB | build | OLD | RINGS | NEW |
|---|---|---|---|---|
| 295 | baked (SAF LUT) | 0–123 | **124–295** | ≥ 296 |
| 295 | gate (SAF LUT) | 0–294 (124–294: **one runt on q**, then OLD) | none | ≥ 295 |
| 295 | baked + LUT_TRANSPORT (6c's channel) | 0 | 1–418 | **≥ 419** |
| 60 | baked / gate | 0–123 | none | ≥ 124 |
| 60 | baked + LUT_TRANSPORT | 0 | 1–183 | ≥ 184 |

**Matches the prediction:** yes, with the same one-ps tie correction as P4b.
- GLS threshold: OLD for w < 124, i.e. silent corruption. The GLS latches correctly only
  from 296 ps (baked) or 295 ps (gate).
- That is ≈ `wfb`, which is rule I without its guard. 6c's `wfb + arc = 419` is reproduced
  **exactly** by the transport control.
- So the conclusion of B-gls-compare §2(a) stands, now on the real prims: **a GLS pass cannot
  confirm 6c's missing I2-arc term**, since the GLS threshold is 124 ps short of it.

**Correction to B-gls-compare §2(a).** "Gate build: OLD value" is true of the final state
only. On the way, q emits **one runt of width w** for 124 ≤ w ≤ 294. A downstream reader can
latch that runt.

**Negative control.** The transport arm. It also gives exactly 6c's predicted threshold, 419.

## P1b: the A0-fork early ack in the full arbiter

**Prediction.** δ = late − early at ua2's pins. The GLS (SAF) hides 0 < δ ≤ arc(ua2): no
ack. Beyond that:
- in the baked build, A2 rings with period arc + wfb = 419 for arc < δ < wfb, and latches an
  early ack after that;
- the transport model (7g) acks or rings for every δ > 0.

**Bench: `tb_p1.v`.**
- The frozen `bd_arbiter`, all arcs 124. Feedback wires of 295 on ua1.I2 and ua2.I2. Only the
  A0 branch into ua2 (`ua2.u.W1 = WA`) carries extra wire; every other wire is 0.
- Sequence: client 1 is served and returns to zero, and client 2 waits. The setup state is
  checked: A1 = 1, A2 = 0, R0 = 0, q = 1.
- At T0 the server drops A0 and **never raises it again**, so any A2 ≠ 0 is an
  acknowledgement for a transaction the server never began.
- g2 reaches ua2.I0 at T0 + 248 (measured, printed), so δ = WA − 248.

**Command.** `./sweep_p1.sh 295 -50 450 [-DGLS_TRANSPORT_IC] [-DLUT_TRANSPORT]`, at 1 ps
steps, one compile per δ (`logs/p1b*.log`).

**Result:**

| build | no ack | rings | early ack (latched) |
|---|---|---|---|
| baked (SAF LUT) | δ ≤ 123 (0 edges on A2) | **124–295**, period 419 (A2 edges at +372, +791, +1210, …) | ≥ 296 |
| gate (SAF LUT) | δ ≤ 123 clean; **124–294: one A2 runt of width δ**, then 0 | none | ≥ 295 (295: runt, then latch) |
| baked + LUT_TRANSPORT (7g's channel, control) | δ ≤ 0 | 1–418 | ≥ 419 |

**Matches the prediction:** yes.
- The one-arc blind spot is real on the real prims. For 1 ≤ δ ≤ 123, A2 does not move in
  either build, while 7g's transport model rings from δ = 1.
- Rule J's raw sign (δ ≤ 0) is the transport boundary exactly. The GLS boundary is δ ≤ 123.
- B-gls-compare's step list (0, 60 → no ack; 125, 200 → ring; 295 → latch; 420 → latch)
  holds in the baked build, with δ = 124 now ringing (tie) and δ = 295 still ringing.

**Correction.** In the gate build the "no ack" region 124–294 is **not clean**: A2 pulses
once, for δ ps. A client waiting on `A2 === 1` would take that pulse as an acknowledge. So
the gate build hides less than "no ack" suggests, but it reports it as a runt, not as a
latched ack.

**Negative control.** The transport arm acks or rings for every δ ≥ 1, the same harness
classifies EARLY_ACK for δ ≥ 296, and δ ≤ 0 gives NO_ACK. Both outcomes are reachable, so the
harness can fail.

## Summary

| # | prediction | result | matches |
|---|---|---|---|
| P6 | runt-held: q/g2/A1/A2 never move with A0 = 1 | 368 of 368 runs hold (research gate/baked, random arcs and wires, x, ties; cells/sim). Unheld-INIT control: 368 of 368 violated | yes |
| P6b | tie with q = x: R0 = 1, A1 = A2 = 0 until A0 | 0 violations in 3 models. Non-tie control: 14–18 violations | yes |
| P3 | overlap max(0, 16 − R) (cells/sim); 0 at a consistent corner; box 37 − R | 51 of 51 rows exact to the ps. tb_arb: 1 instant for R ≤ 15, 0 from R = 16 | yes (16 ps confirmed to be a corner-mix artefact of the arcs) |
| P4b | baked rings in [arc, wfb]; gate does not ring; empty when wfb < arc | baked rings 124–295; gate holds with one runt; empty at wfb = 60 | yes (ties included; gate build leaks one runt) |
| P5b | latch: OLD ≤ arc, ring (baked) up to wfb, NEW after; 6c needs wfb + arc | 0–123 OLD, 124–295 ring, ≥ 296 NEW; transport control flips at exactly 419 | yes (gate build leaks one runt) |
| P1b | GLS hides 0 < δ ≤ arc; baked rings period 419 up to wfb, then early ack | no ack ≤ 123; ring 124–295 at period 419; early ack ≥ 296; transport acks/rings from δ = 1 | yes (gate build leaks one A2 runt for 124–294) |

**Main points for the two branches:**

1. The formal side's one-arc disagreement with the GLS (B-gls-compare §2) is confirmed on the
   real prims, in both builds. The transport controls reproduce the formal thresholds
   exactly:
   - 6c: 419;
   - 7g: δ > 0;
   - 5b: rings for 0 < S < D.

   The GLS thresholds sit one arc (124 ps) later. The formal numbers stay the gates.
2. The gate (annotated) build differs from the baked build in a way neither proxy captured.
   It does not ring, and it **emits one runt of the runt's width** and then reverts. So in
   the gate build a bundling-window violation shows up as a glitch on the latch or ack
   output, not as a silent OLD value. Which build to trust on loops: the baked one (transport
   wire). B-gls-compare §4 already says so.
3. The iverilog gate-build ICBUF artefact (§0) matters for anyone running `cells/rtl`
   hierarchically on the research prims. The flat gen.py netlist should be immune, but that
   was argued from its source, not run.

**What was not done:**
- P8 (O5/O6 sharing a site pin in the xray SDF) needs a routed SDF; none is on disk.
- P2b needs the research toolchain.
- P5 and P10 need the board.
- No design-level GLS was run.

## Appendix: `rshim.v` (scratch copy is authoritative)

```verilog
`timescale 1ps/1ps
`ifndef RARC
 `define RARC 124
`endif
module rpin #(parameter integer D = 0) (input wire I, output wire O);
    generate if (D == 0) begin : direct
        assign O = I;
    end else begin : ic
        wire Ib;              // private input net: avoids the section-0 artefact
`ifndef NO_BUF_FIX
        buf (Ib, I);
`else
        assign Ib = I;
`endif
        ICBUF #(.D(D)) b (.I(Ib), .O(O));
    end endgenerate
endmodule
module rlut #(parameter [63:0] INIT = 64'h0, parameter integer ARC = `RARC, parameter integer ARC5 = ARC,
              parameter integer W0 = 0, W1 = 0, W2 = 0, W3 = 0, W4 = 0, W5 = 0)
    (input wire I0, I1, I2, I3, I4, I5, output wire O5, output wire O6);
    wire a1, a2, a3, a4, a5, a6;
    rpin #(W0) p0 (I0, a1); rpin #(W1) p1 (I1, a2); rpin #(W2) p2 (I2, a3);
    rpin #(W3) p3 (I3, a4); rpin #(W4) p4 (I4, a5); rpin #(W5) p5 (I5, a6);
`ifdef LUT_TRANSPORT      // negative control: the formal transport channel
    wire f5, f6;
    SLICE_LUTX #(.INIT(INIT), .TA1O6(0), .TA2O6(0), .TA3O6(0), .TA4O6(0), .TA5O6(0), .TA6O6(0),
        .TA1O5(0), .TA2O5(0), .TA3O5(0), .TA4O5(0), .TA5O5(0))
        l (.A1(a1), .A2(a2), .A3(a3), .A4(a4), .A5(a5), .A6(a6), .O5(f5), .O6(f6));
    reg o5 = 1'bx, o6 = 1'bx;
    always @(f5) o5 <= #ARC5 f5;
    always @(f6) o6 <= #ARC f6;
    assign O5 = o5; assign O6 = o6;
`else
    SLICE_LUTX #(.INIT(INIT), .TA1O6(ARC), .TA2O6(ARC), .TA3O6(ARC), .TA4O6(ARC), .TA5O6(ARC), .TA6O6(ARC),
        .TA1O5(ARC5), .TA2O5(ARC5), .TA3O5(ARC5), .TA4O5(ARC5), .TA5O5(ARC5))
        l (.A1(a1), .A2(a2), .A3(a3), .A4(a4), .A5(a5), .A6(a6), .O5(O5), .O6(O6));
`endif
endmodule
// LUT6 (O = rlut.O6) and LUT6_2 wrap rlut with the same INIT/ARC/ARC5/W0..W5 parameters.
```

## Verdict

**Works.**
- All six predictions run match on the real models, with 1 ps boundary resolution.
- Every arm has a negative control that failed when it should have.
- Two refinements came out of the runs:
  - band edges are tie-inclusive, [arc, wfb];
  - the gate build leaks one runt, where B-gls-compare said it gives a clean OLD value.
- One tooling hazard turned up: the iverilog gate-build ICBUF drops its delay on self-bound
  nets, which affects hierarchical benches only.
- Effort spent was about 1.5 h. To finish P8 and P2b, the research owner needs about ½ day
  with a routed xray SDF.
