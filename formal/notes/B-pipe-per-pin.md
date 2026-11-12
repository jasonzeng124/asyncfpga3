# B probe 6g: the N-stage timed pipe with per-pin controller LUTs

File: `formal/lean/Formal/Cells/PipePerPin.lean` (core Lean, about 1300
lines). It imports `Formal.Cells.FifoFidelity` (Bq) and
`Formal.Cells.PipeTimedN` (6f), both read-only. The `FifoFidelity` olean was
missing; it was compiled with the brief's command (plain `lean`, about 2 s,
no `lake env` needed). This file adds no shared definitions. Its own
definitions (`CtlP`, `PP`, `GatesP`, `EnvP`, `TimingP`, `DataP`, `Dl`,
`Wit.sq8`, …) live in namespace `Formal.Cells.PipePerPin`.

Check command:

    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/PipePerPin.lean

Status: **checks clean** in about 10 s, with no errors and no warnings. It
contains no `sorry`, `admit`, `axiom` or `native_decide`. `#print axioms` was
run on a scratch copy:
- {propext, Classical.choice, Quot.sound}: `selx_phase`, `selx_pre`,
  `pipe_ctl`, `nodes_clean`, `pins_clean`, `live`, `token`, `pipe_forward`,
  `ctl_lut_fifo`, `Wit.witness`, `Wit.witness_data`;
- {propext, Quot.sound}: `ce_violates`, `ce_ctlp`.

No routed numbers are reported, and no nextpnr build was run.

## The question

6f proved the `N`-stage `bd_pipe` (clean control, every token delivered,
live) under `H_LUT_FIFO`: each controller's output is a FIFO read of its
pin-level excitation. Bq showed that this is false for a real LUT, whose pins
reach the mux tree through different site-pin buffers (`ce_not_fifo`). Bq
gave the per-pin model `PinLut` and a one-phase result (`sel_phase`).

This probe replaces `H_LUT_FIFO` in the N-stage theorem by:
- the per-pin model;
- a per-stage, per-phase ordering condition, stated as an inequality over
  routed delays.

## The model (`CtlP`, `GatesP`)

Each controller `i` is described by the following relations.
- **`H_OUT`**: `O t = exSel pr pa pq ps req ack qp rst (out.σ t)`. This is
  Bq's `PinLut` relation exactly (`CtlP.pinLut` builds the `PinLut`). It has
  two parts:
  - each pin (I0 req, I1 ack, I2 feedback, I3 rst) reaches its select through
    its own FIFO site-pin map (**H_PIN_FIFO**);
  - the real `bd_c2n` INIT (`0x00B2…`, via `CElemTiming.exc`/`lutB`) is
    evaluated at the selects, then passes through one FIFO tree and output
    map `out` (**H_TREE_FIFO**).
- **`H_FB`**: the feedback wire is 5b's window channel. Non-FIFO behaviour is
  allowed.
- **`H_LOOP_POS`**: `1 ≤ out.lo + wl + pq.lo`.

The lines, the DACK OR line (`fastrise_or`) and the environment are as in 6f.
The pipe realisation `PP` carries per-stage maps `pr pa pq ps out`.

**Event times are derived, not assumed** (`PP.tt`). The recursion is 6f's
`2j + i` recursion, with the node edge computed through the selects:
- `S i j = max (pr_i.fst (Rin i j)) (pa_i.fst (Ain i j))` is the phase start
  at the selects;
- `τ i j = out_i.fst (S i j)` is the node edge (`τ_eq`).

## What is proved

| theorem | statement |
|---|---|
| `selx_phase` | One stage, one phase, at the selects. Let the pins be clean on `[ρ,ρ')` and `[α,α')`. Assume reset is low at its select and **H_SEL_ORDER** holds: `τ + wh + pq.hi ≤ min (pr.fst ρ') (pa.fst α')`. Then the select-level excitation is `v` on `[S, max (pr.fst ρ') (pa.fst α'))`. This is Bq's `sel_phase` with its `hqp`/`H_SEL_KEEP` premises removed. Those premises assume the result, since the feedback is the node itself; here they are discharged by strong induction on time. The case split is `sel_phase`'s (`c2n_set`, `c2n_hold`). |
| `selx_pre` | Before the first request reaches its select, the select-level excitation is 0. This needs the request select and the loop to be flushed when reset releases at **its** select. |
| `depR`, `depA`, `gap`, `fwd`, `back_odd`, `rho_le`, `gam_le`, `S0_eq`, `rst_sel` | Causality at every boundary, derived with per-pin credits. |
| `pipe_ctl` | **(1) For all N ≥ 1, all phases j, all stages i:** the select-level excitation of the real INIT equals `Vph j` on `[S i j, S i (j+1))`. No `H_LUT_FIFO` is used. |
| `nodes_clean`, `pins_clean` | Every node and every internal pin is a clean one-edge-per-phase signal. |
| `live` | `τ i j < τ i (j+1)`. It needs **no extra hypothesis**: `H_SELORD` and `H_LOOP_POS` give `Won ≥ 1`. |
| `token`, `pipe_forward` | **(2), (3)** Every stage latches every token and the last stage delivers it. This is 6f's data path, with per-pin credits. |
| `ctl_lut_fifo` | **Corollary.** It assumes an extra **pin-level** ordering, `wh ≤ ER ∧ wh ≤ EA` and `out.hi + wh ≤ R`. Under it, each controller satisfies 6e's `Ctl.H_LUT_FIFO`, with band `[out.lo, max(pr.hi,pa.hi) + out.hi]`. Proof: the pin-level and select-level phase sequences are matched edge by edge and fed to Bq's `pinlut_fifo_of_edges`. |
| `Wit.witness`, `Wit.witness_data` | Non-vacuity for every N ≥ 1 with **unequal** pin delays. |
| `ce_ctlp`, `ce_violates` | The Bq counterexample is a behaviour of this model and violates `H_SELORD`. Its fast-feedback twin satisfies `H_SELORD` and is clean. |

## The per-stage per-pin obligation, final form (`TimingP.H_SELORD`)

For every stage `i`:

    wh_i + pq_i.hi ≤ ER_i + pr_i.lo     and     wh_i + pq_i.hi ≤ EA_i + pa_i.lo

where `ER` and `EA` are derived round trips (`PP.ER`, `PP.EA`) with `alo` the
fastest DACK path's `lo`:

    ER_0     = Es                                         (sender)
    ER_(i+1) = alo(i+1) + pa_i.lo + out_i.lo + Rq(i+1).lo
    EA_i     = Rq(i+1).lo + pr_(i+1).lo + out_(i+1).lo + alo(i+1)   (i+1 < N)
    EA_(N-1) = Er                                         (receiver)

Reading the inequality:
- **Left side**: the feedback's latest arrival at its select, counted from
  the node edge (feedback wire, then the feedback site pin).
- **Right side**: each departure's earliest arrival at its own select,
  counted from the node edge.

Every term is a routed delay:
- site-pin bands of the physical pins chosen by the router (prjxray);
- LUT tree arcs;
- wire and line bands;
- the environment's `Es` and `Er`.

So this is a checkable inequality over routed pin delays. It replaces 6f's
`H_LAT` and the assumption `H_LUT_FIFO`, both.

Compared with Bq's `w_hi + pq.hi ≤ E_τ + min(pr.lo, pa.lo)`, it is split per
departure: each departure is credited with its **own** pin's `lo`. Compared
with 6f's lumped `H_LAT` (`L.hi + wh ≤ L.lo + min(ER, EA)`), it has no LUT
spread term `out.hi − out.lo`, because the reference instant is the actual
node edge.

**The rest of the contract** (`TimingP`):
- **`H_RST_SEL i`**: startup per stage. It replaces `H_RST_LONG`, and it is
  new: reset now has its own pin delay. It has four parts:
  - (a) `R0 + pr.hi ≤ R + ps.lo`;
  - (b) `out.hi + wh + pq.hi ≤ R + ps.lo`;
  - (c) `R + ps.hi ≤ ρ0 + pr.lo`;
  - (d) `R0 + pa.hi ≤ ρ0 + pr.lo`.

  Parts (a) and (b): when reset releases at its select, the request select
  and the loop already read flushed values. Part (c): reset reaches its
  select before the first request does. Part (d): the acknowledge select is
  flushed by then too. `R0 ≤ R` is the time from which every pin holds its
  initial value.
- **`H_FLUSH b`**: 6f's `H_RST_LINES`, stated against `R0`.
- **`H_ACK_FLUSH b`**: as 6f, with the per-pin
  `Won i = out_i.lo + max(ER_i + pr_i.lo, EA_i + pa_i.lo)`.
- **Data side** (`DataP`): 6f's obligations, with the credit
  `Rq.lo + L.lo` replaced by `Rq.lo + pr.lo + out.lo` (`H_I`, `H_SETUP0`,
  `Dl`), and the DACK credit followed by `pa_i.lo + out_i.lo` (`H_H`).

## Witness (`Wit`)

Delays, per stage:

| element | ticks |
|---|---|
| request pin | 1 |
| acknowledge pin | 2 |
| **feedback pin** (slowest: Bq's unfavourable placement) | **3** |
| reset pin | 1 |
| tree | 1 |
| feedback wire | 1 |
| request line | 1 |
| DACK line (DACK = 1) | 1 |

The environment and reset: `R = 4`, `R0 = 2`, `Es = 6`, `Er = 4`.

Derived event times:
- `τ i j = 9 + 3i + 8j` (`tt_w`, solved from the recursion);
- every net is a half-period-8 square wave.

What the run exercises:
- At the selects, the acknowledge arrives and departs one tick before the
  request. So for one tick per half-phase, the excitation is held by the
  feedback alone (`key8`, cases `(s−o)%16 = 7` and `15`).
- `H_SELORD` holds with margin 2: inner `4 ≤ 6`, `4 ≤ 6`; at the ends `4 ≤ 7`
  and `4 ≤ 6`.
- Data: one bit, alternating tokens, real `ODD` latch INIT. `pipe_forward`
  applies, and the output is true at `γ 0` and false at `γ 2`.

## Counterexample (`ce_ctlp`, `ce_violates`)

Bq's run uses these delays:
- request, acknowledge and reset pins 1, **feedback pin 6**;
- tree 2, wire 1;
- the request is withdrawn 3 ticks after the node edge, so `ER = 3`.

Results:
- **It is a `CtlP` behaviour** (`ce_ctlp`). Every gate relation of this
  file's model holds at every instant.
- **It violates `H_SELORD`**: `1 + 6 > 3 + 1`. The node rises at 13, drops at
  19 and rises at 22 (`ce_node`), then oscillates.
- **The twin satisfies it.** The same environment with a 1-tick feedback pin
  gives `1 + 1 ≤ 3 + 1`, and the node makes one edge (`cj_clean`).

## Findings

1. **`H_LUT_FIFO` is not needed and is strictly stronger than what the
   circuit needs.**
   - The pipe theorem holds under `H_SELORD`, which is a select-level
     condition.
   - Recovering `H_LUT_FIFO` (`ctl_lut_fifo`) needs, in addition, the
     pin-level ordering `wh ≤ ER`, `wh ≤ EA`. `H_SELORD` does not imply it
     when the feedback pin is faster than the departing pin
     (`pq.hi < pr.lo`).
   - Example (arithmetic only, not a Lean theorem): `wh = 2`, `pq.hi = 0`,
     `pr.lo = 2`, `ER = 1`. Then `H_SELORD` holds (`2 ≤ 3`) and the pin-level
     ordering fails (`2 > 1`).
   - So, by `pipe_ctl`, such a route is clean even though the 6e/6f premise
     is not available for it. No Lean witness of an actual `H_LUT_FIFO`
     failure in a clean pipe was built.
   - Neither direction is a vacuity problem. Both are now explicit.
2. **The pin-level lower bound is lost in `ctl_lut_fifo`.** Bq's
   `pinlut_fifo_of_edges` anchors both edge sequences at 0 (`c 0 = e 0 = 0`
   with `c j + lo ≤ e j`), which forces `lo = 0`. The recovered band is
   therefore `[out.lo, max(pr.hi, pa.hi) + out.hi]`, not
   `[min(pr.lo, pa.lo) + out.lo, …]`. A variant of `ret_of_edges` with a
   pre-phase exemption would restore it (about 30 min). The pipe theorem
   itself does not use this band.
3. **Reset now has its own pin delay**, and that adds startup obligations
   (`H_RST_SEL`) that 6f did not have. All of them are startup facts, true
   once at power-up. Parts (c) and (d) say that the environment's first
   request must come after reset has released at every rst select. They are
   per stage, but the first request `ρ0` is the bound for all stages.

## What did not work / not done

- **Bq's `sel_phase` is not applied verbatim.** Its feedback premise covers
  the whole phase, and that is the result being proved. `selx_phase` uses the
  same case analysis with the premise discharged by strong induction. This is
  a restatement, not a new idea.
- **Not checked by any rule.**
  - No `tighten.py` rule checks `H_SELORD`, `H_RST_SEL` or `H_ACK_FLUSH`.
  - The SDF flattens site pins to 25 ps (C-10c), so `pq.hi` and `pr.lo` are
    invisible to every current gate.
  - The check needs FASM pin assignments (C-11b's fasm2lean) plus prjxray
    site-pin bands.
- **No real routed numbers.** The witness uses unit ticks, not prjxray
  delays.
- **No joint witness with `DACK ≥ 2`**, as in 6f.
- **Residual assumptions are unchanged from Bq**:
  - H_TREE_FIFO, which includes the single-select static-hazard assumption
    of B-muxtree-fidelity;
  - H_PIN_FIFO.

## Verdict

**Works.** 6f's general-N pipe theorem (clean nodes and pins, every token
delivered, live) now holds for controllers modelled as `PinLut`s with per-pin
site delays. The assumption `H_LUT_FIFO` is gone. In its place is one
per-stage inequality over routed pin delays:
- `H_SELORD`, in the final form above;
- plus startup and line-flush inequalities.

A unit-delay witness with unequal pin delays satisfies everything for every
N, and Bq's counterexample is shown to violate exactly `H_SELORD`.

Effort was about 1.5 h, against the half-day estimate in the Bq notes. 6f's
structure carried over almost line for line.

**What it buys.**
- The physical assumption under the timed pipe shrinks to:
  - FIFO site-pin buffers;
  - a FIFO tree;
  - one inequality per stage that a FASM + prjxray tool can check.
- It also says exactly which pin-placement fact matters: the feedback's site
  pin against each departing input's site pin.
- The proposed audit gate is this inequality per `bd_c2*`, with the
  guardband applied. The alternative is `LOCK_PINS` on the feedback to A6 or
  A5, which changes a frozen cell and needs a routed-GLS result.

**To finish.**
- A FASM-driven checker for `H_SELORD` (about 1 day, on fasm2lean).
- Instantiating the contract with prjxray numbers for one routed pipe.

## Fidelity per primitive

- **Controller LUT (`bd_c2n`).**
  - Real INIT via `lutB`, binary values.
  - Per-pin FIFO site-pin maps, then a zero-time function at the selects,
    then a FIFO tree/output map. This is the prjxray split (site-pin delay
    per pin, then one cell arc).
  - Not modelled: per-level mux delays inside the tree (lumped in `out`),
    charge-sharing runts, X and metastability. The pins are clean protocol
    signals here.
- **Feedback wire.** 5b's window channel. Non-FIFO behaviour is allowed.
- **Request line, DACK line, latches, environment.** As 6f:
  - the request line is FIFO;
  - the DACK line is an OR of FIFO copies, which is a theorem for the real
    FASTRISE chain;
  - each latch is 6c's Kleene `LatchRel`, and in the witness the real `ODD`
    INIT as a transport LUT.

  The DACK LUTs still use lumped FIFO pins. Their own per-pin refinement is
  not done. FASTRISE is an OR of monotone inputs, so it is likely
  order-free, but this is not proved.
- **Time.** ℕ ticks. The data lateness `Dl` is in ℤ.
