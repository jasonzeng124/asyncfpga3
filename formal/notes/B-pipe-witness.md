# B probe 6h: non-degenerate joint witnesses for the timed pipe (answers audit P3 row 3)

File: `formal/lean/Formal/Cells/PipeWitness.lean` (core Lean, about 900 lines).
It imports `Formal.Cells.PipeTimedN` and `Formal.Cells.PipePerPin` read-only.
The `PipePerPin` olean was missing, so I compiled it with `-o` into
`.lake/build/lib/lean/Formal/Cells/PipePerPin.olean`. The source is unchanged.
This file adds no shared definitions. Its helpers (`latchT`, `chs`, `chain2`,
`fst_comp_shift`, `sq12`, `sq16`, the `bw` tactic macro) live in it.

Check command (clean: no errors, no warnings, about 25 s):

    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/PipeWitness.lean

**Axioms.** I ran `#print axioms` on a scratch copy.
- `latchT` and `chain2` use only {propext, Quot.sound}.
- These use {propext, Classical.choice, Quot.sound}: `W1.witness`,
  `W1.no_tie`, `W1.hold`, `W1.latch_hold`, `W2.witness`, `W2.ack_latency`,
  `W2.hold_rise`, `W2.hold_fall`, `W3.witness`, `W3.sel_lead`,
  `W3.hold_rise`, `W3.hold_fall` and `W3.latch_hold`.

The file contains no `sorry`, `admit`, `axiom` or `native_decide`. No routed
numbers are reported, and nothing here depends on a nextpnr build.

The audit branch was not imported. W1's control part re-derives
`audit/lean/P3/PipeNWit.lean`'s `Aud.Pg` in this file, using a different
proof method (`bw`, described below).

## The question (audit P3 row 3)

`PipeTimedN.Wit.witness` is a tie run. `Rin = Ain` at every stage, so
`bd_c2n = C(req, !ack)` never holds through its feedback. The auditor
repaired the control side for every N (`Aud.witness_g`). Two things were
still UNVERIFIED:
- a data-side witness with non-unit delays;
- a joint witness with `DACK >= 2`.

The task also asked for the same for `PipePerPin`, with the feedback on the
slowest pin.

## What is proved: all three, for EVERY N >= 1

### W1: the auditor's control realisation, plus a non-unit data path

**Delays.**
- Control: LUT 2, request line 3, DACK 1, feedback wire 1, reset 6,
  half-period 12, `Es = Er = 6`.
- Data, per latch bit (the real ODD INIT through
  `Bundling.transport_gate`): the D pin is read 3 ticks back, in window
  [2,4]; the enable 2 ticks back, in window [1,3]; its own output 2 ticks
  back, in window [1,2]. All windows have `lo < hi`.
- Sender: token k on `[2+24k, 26+24k)`, values alternating.

| theorem | statement |
|---|---|
| `W1.τ_e` | The derived event times, solved from the recursion: `τ i j = 8 + 5i + 12j`. |
| `W1.no_tie` | Inside the pipe, `Ain i (j+1) = 14+5i+12j` and `Rin i (j+1) = 18+5i+12j`. The acknowledge leads the request by 4 ticks. |
| `W1.hold` | **hold_exercised**, for every stage and every phase j, at `s = 15+5i+12j`. Request, acknowledge and feedback all read `Vph j`, so C(req,!ack) sees disagreeing inputs. The real INIT outputs `Vph j`. With the feedback pin flipped it outputs `!Vph j`, so the output is decided by the feedback pin alone. |
| `W1.latch_hold` | Every stage and every token k, at `t = 33+5i+24k`: the enable reads closed, the D pin already reads token k+1, and the output still shows token k (≠ token k+1). The latch holds through its own loop. |
| `W1.witness` | `GatesN ∧ EnvN ∧ TimingN ∧ DataN` hold jointly. `pipe_forward` is applied: on `[γ(2k), γ(2k+1))` the last stage outputs `k even`. Also the C-element hold and the latch hold at every stage `i < N`. |

### W2: DACK = 2, the real FASTRISE chain, rise and fall latencies differ

**The chain, gate by gate.** `s1 = LUT1 2'h2 (s0)` with arc 2. Then
`s2 = LUT2 4'hE (I0 = s1 via arc 2, I1 = s0 via arc 1)`.

`chain2` applies `PipeTimedN.fastrise_or` to these transport nets. It shows
that `chs x 2` is exactly the OR of the two FIFO copies `cpath … 1 0` (the
ripple, 4) and `cpath … 1 1` (the tap, 1). `GatesN.H_ACK_LINE` is discharged
by `chain2`. It is not assumed.

`alo = 1`, `ahi = aslow = 4`, `m = 1`. The receiver behaves as a virtual
stage N behind the same chain: `γ j = 9 + 5N + 12j + 3(j mod 2)`.

| theorem | statement |
|---|---|
| `W2.ack_latency` | Inside the pipe, the acknowledge pin follows stage `i+1`'s rise by **1** and its fall by **4**. It still leads the request by 4 ticks after a rise and by 1 tick after a fall. |
| `W2.hold_rise`, `W2.hold_fall` | The C-element holds through its feedback after every acknowledge rise (all inputs 1 at `15+5i+24k`) and after every fall (all inputs 0 at `29+5i+24k`). In both cases the flipped feedback would flip the output. |
| `W2.witness` | `GatesN ∧ EnvN ∧ TimingN ∧ DataN` hold jointly. `m = 1`, `alo = 1`, `aslow = 4`. `pipe_forward` delivers every token. Both holds are shown at every stage. The data path is W1's, and `H_H` now uses the DACK credit `aslow = 4`. |

### W3: the per-pin model (`PipePerPin`), feedback on the SLOWEST pin

**Delays.**
- Site pins: request 1, acknowledge 2, **feedback 3**, reset 1.
- Tree and output 2, feedback wire 1, request line 3.
- The DACK = 2 chain of W2.
- Reset at its pin at 8, pins flushed from 6, half-period 16, `Es = 8`,
  `Er = 7`.
- The same non-unit latch arcs as W1.

**Obligation margins.** `H_SELORD` has margin 5 (`1+3 ≤ 8+1`) and 5
(`1+3 ≤ 7+2`). `H_FLUSH`'s `out.hi + ahi ≤ R0` and `H_RST_SEL` (c) are tight
(equalities).

| theorem | statement |
|---|---|
| `W3.τ_e` | `τ i j = 11 + 6i + 16j`, solved from `PP.tt`. |
| `W3.ctl` | Every controller is a `CtlP`: the real `bd_c2n` INIT at the selects (`exSel`) at every instant. |
| `W3.sel_lead` | Inside the pipe, the acknowledge pin follows the next node by 1 after a rise and 4 after a fall. At the selects it leads the request select by **5** ticks after a rise and **2** after a fall. The acknowledge select arrives at `20+6i+32k` and `39+6i+32k`. |
| `W3.hold_rise`, `W3.hold_fall` | Select-level hold at `u = 21+6i+32k` (all three selects 1) and at `u = 39+6i+32k` (all 0). The excitation equals the feedback select, which is the slowest pin. Flipping that select flips the excitation. |
| `W3.latch_hold` | As W1, at `t = 44+6i+32k`. |
| `W3.witness` | `GatesP ∧ EnvP ∧ TimingP ∧ DataP` hold jointly. Pin delays are ordered `pr < pa < pq` and `ps < pq`. `m = 1`, `alo = 1`, `aslow = 4`. `PipePerPin.pipe_forward` delivers every token. Both select-level holds and the latch hold are shown at every stage. |

## Method

The traces are closed-form square waves (`decide (o ≤ t ∧ (t-o) % p < h)`).

Every pointwise gate relation is closed by the `bw` macro. This covers the
real INIT through `c2n_eq`, the chain OR and the latch recursion. `bw` turns
the Boolean equation into an iff with `Bool.eq_iff_iff`, then `simp`, then
`omega`. Each takes well under a second.

The event times are not stated. They are solved from `PN.cc`/`PP.tt` by
induction, exactly as in 6f/6g.

## Negative controls (mutations, on scratch copies)

- **M1.** DACK chain arc `C` 2 → 6, which makes the fall latency 8. It is
  killed (17 errors). The kill is WEAK: the first errors are the `rfl`
  lemmas `cp0`/`ackT_e`, which pin the chain's arcs.
- **M3.** W3 feedback site pin 3 → 7, applied consistently: `P.pq`, `ctl`,
  the feedback offset in `H_OUT`, `exS`, and the obligations restated.
  - The gate relation `ctl` and all hold lemmas still check.
    `H_SELORD` still holds (`1+7 ≤ 8+1`, margin 0).
  - Only `H_RST_SEL (b)` fails: `2+1+7 ≤ 8+1` is false, so the loop is not
    flushed when reset releases. That startup obligation is genuine.
  - The pin-order `show` also fails, which is structural.
- **M4.** The same with feedback pin 9. Now `H_SELORD` FAILS
  (`1+9 > 8+1`), and so does the gate relation itself: the `bw`/omega in
  `ctl.H_OUT` finds a counterexample instant. The closed-form node is no
  longer the select-level excitation, because the feedback select arrives
  after the acknowledge select and the C-element briefly sees the stale
  feedback.

  This is the per-pin obligation biting on a concrete run. The witness
  breaks exactly when `H_SELORD` is violated. With feedback pin 7 it
  survives at margin 0.

## What is NOT shown / limits

- These are witnesses (non-vacuity). They are not measurements. All delays
  are fixed transport delays inside their windows. FIFO maps are the
  shift maps, so no witness exercises `σ` jitter inside `[lo, hi]` on the
  control side. On the data side the windows are wider than the actual
  delays, but each pin's delay is still fixed.
- One data bit (`W = 1`), not a multi-bit pair (`pair_o5/o6` latches are not
  instantiated).
- DACK = 2 only (`m = 1`). `DACK ≥ 3` is not instantiated. `chain_w` in 6f
  covers general length with unit arcs only.
- The runs are environment-paced: the sender's period is the bottleneck.
  No witness is ring-limited or pipeline-full.
- The tick values are illustrative. They are not prjxray numbers.

## Verdict

**Works.** Audit row 3's two UNVERIFIED items are now proved for every
`N ≥ 1`:
- a non-unit, unequal-delay data-side witness, jointly with the control;
- a DACK = 2 joint witness with distinct rise and fall latencies.

The per-pin model has the same, with the feedback on the slowest pin. In all
three, the C-element demonstrably holds through its feedback, in both phase
kinds for W2 and W3, and the latches hold through their loops.

Remaining effort if wanted:
- about 1–2 h for a parametric DACK = n+1 witness (`cpath` with general n
  and non-unit arcs);
- about 1 h for a W = 2 pair-latch data path.

What it buys: `pipe_ctl`, `pipe_forward` and their per-pin versions are no
longer only known to be satisfiable by a tie run. Their hypotheses are
jointly satisfiable by runs that exercise every hold state the theorems
reason about.

## Fidelity per primitive

| primitive | how it is modelled |
|---|---|
| Controller LUT (`bd_c2n`, INIT `0x00B2…`) | Real INIT through `CElemTiming.exc`/`lutB`. W1/W2: lumped FIFO LUT (`Ctl.H_LUT_FIFO`, shift 2). W3: per-pin (`CtlP`), each site pin its own shift, then a shift-2 tree/output. |
| Feedback | A routed wire, transport 1 inside the window `[1,1]` (`H_FB` via `transport_winDelay`). In W3 it is followed by the slowest site pin (3). |
| DACK line | W1: one LUT1 buffer arc (shift 1). W2/W3: the real FASTRISE chain (`BUF 2'h2`, `FR_SIDE 4'hE` through `lutB`), each LUT pin a transport arc, proved to be the OR of FIFO copies by `fastrise_or`. |
| Request line | One FIFO shift of 3, standing for wire + SDELAY + wire. |
| Latch bit | Real ODD INIT `B8B8…` as a transport LUT with pin delays 3/2/2 inside the Kleene windows [2,4]/[1,3]/[1,2] (`latchT` → `odd_latch`). |
| Environment | Square-wave sender and receiver. W2/W3's receiver is shaped as a virtual stage N behind the same DACK chain. |
