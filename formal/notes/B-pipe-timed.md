# B probe 6e: a timed N-stage `bd_pipe` (N = 2 in full)

File: `formal/lean/Formal/Cells/PipeTimed.lean` (core Lean, about 1180 lines).
It imports `Formal.Cells.LinkTimed`, and through it `CElemTiming`, `Bundling`
and `LinkHandshake`, all read-only through their oleans. It adds no shared
definitions. The `LinkTimed` olean was missing; it was compiled with the
command given in the brief. The file checks clean, with no errors and no
warnings, in about 10 s. It contains no `sorry`, `admit`, `axiom` or
`native_decide`.

Check command:

    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/PipeTimed.lean

`#print axioms` was run on a scratch copy, for `pipe_ctl`, `nodes_clean`,
`pins_clean`, `token0`, `token1`, `pipe_forward`, `exc_phase`, `Wit.witness`
and `Wit.witness_data`. Each uses only {propext, Classical.choice,
Quot.sound}; `ctl_loop` uses only {propext, Quot.sound}.

No routed numbers are reported here. Nothing in this probe depends on a
nextpnr build.

## The gap, and how it is closed

6d left this gap open. Its node, under 5b's non-FIFO window channel
(`WinDelay`), may glitch inside each transition window of width
`dlmax - dlmin`. The next stage's environment model (`CtlEnv`), however,
needs a clean request shape.

This probe closes it by **route (a)**: a FIFO bounded-delay channel, under
which every controller output makes exactly one transition per phase.
Route (b), relaxing the shape hypotheses, was not attempted. The reason is
given below.

1. **FIFO channel, ℕ-time** (`Ret`, `fifo_hold`, `fifo_comp`, `fifo_win`).
   - This is shard A's `Core/Delay/Pure.lean` `Retime`/`Chan` with ℕ ticks
     in place of ℝ. The output at `t` is the input at `σ t`, with
     `t - hi ≤ σ t ≤ t - lo` (truncated subtraction) and `σ`
     nondecreasing. The relation is only required from `t ≥ hi` on: before
     that is power-up.
   - `fst c` is the first output instant that reads at or after `c`. It is
     defined by a bounded search `lfind` (no `Nat.find` in core).
   - `fifo_hold`: an input stretch `[a, b)` at value `v` becomes the output
     stretch `[fst a, fst b)` at `v`.
   - `fifo_comp`: two FIFO channels in series are one FIFO channel. A wire,
     each LUT1 of the SDELAY chain and another wire therefore make one
     request line.
   - `fifo_win`: a FIFO channel is a `WinDelay`, so every 5b/6d result
     applies to it. `ctl_loop` uses this: a FIFO controller is a 5b `Loop`.
2. **The controller's excitation is hazard-free for a whole phase**
   (`exc_phase`, `exc_pre`). The excitation is the LUT's Boolean function of
   its pins for the real `bd_c2n` INIT, via `c2n_eq`.
   - **Hypotheses.** The request holds `v` on `[ρ, ρ')`. The acknowledge
     holds `!v` on `[α, α')`. Both departures `ρ'` and `α'` come at least
     `L.lo + E` after the phase start `max ρ α`. Finally,
     `L.hi + wh ≤ L.lo + E` (5b's `H_ENV_LATENCY`).
   - **Conclusion.** The excitation is exactly `v` on
     `[max ρ α, max ρ' α')`, whatever the inputs do after they depart.
   - **Proof.** Strong induction on time, inside the phase only. Once an
     input has left, the feedback pin already shows `v`, read back through
     the LUT's FIFO map into the same phase. No earlier phase is used.
   - `exc_pre` is the reset phase: reset high on `[0, R)` from any power-up
     state, then the request low.
3. **One node edge per phase** (`node_phase`). The LUT output is the
   excitation read through a FIFO map (`H_LUT_FIFO`). So the node is `v`
   exactly on `[fst c, fst c')`, and its single edge lands at
   `τ = fst c ∈ [c + L.lo, c + L.hi]`.
4. **The pins between stages are clean.**
   - The request line is FIFO, so `fifo_hold` applies.
   - The DACK FASTRISE line is modelled as the OR of a fast FIFO copy (the
     side taps) and a slow FIFO copy (the ripple) of the node.
     `or_hold_false` gives the low stretch, which is automatic.
     `or_hold_true` gives the high stretch, which needs the two copies to
     overlap.
   - So stage `i`'s node, seen through its line, is a clean four-phase
     signal at stage `i ± 1`'s pin. This is exactly 6d's row 4.

## The two-stage pipe (`bd_pipe #(.N(2))`)

**Delay realisation and event times.**
- `P2` holds reset release `R`, the read-time maps of the two controller
  LUTs (`L0`, `L1`), the request line `Rq`, the two acknowledge-line paths
  (`Ar` fast, `Af` slow), and the environment's edge times `ρ` (at `r[0]`)
  and `γ` (at `a[2]`).
- `cc` defines all phase starts by recursion on the phase index:
  - `c0 j = max (ρ j) (A0 j)`;
  - `c1 j = max (R1 j) (A1 j)`;
  - `τ0 j = L0.fst (c0 j)`, `τ1 j = L1.fst (c1 j)`;
  - `R1 j = Rq.fst (τ0 j)`, `A0 (j+1) = ackT j (τ1 j)`, `A1 (j+1) = γ j`.
- `ackT` takes a rise through the earlier path and a fall through the later
  one.

**Theorems (all proved).**

| theorem | statement |
|---|---|
| `ge_R`, `tau*_lo`, `R1_lo`, `A0_lo` | Bookkeeping: every phase starts after reset; each derived time is at least its cause plus the channel's `lo`. |
| `dep0a`, `dep1r` | **Causality across the internal boundary is derived, not assumed.** Stage 0's acknowledge pin departs at least `L0.lo + RT0` after stage 0's phase start, with `RT0 = Rq.lo + L1.lo + alo`. Stage 1's request pin departs at least `L1.lo + RT1` after its phase start, with `RT1 = alo + L0.lo + Rq.lo`. These follow from the `max` structure of the definitions alone. (`dep0r` and `dep1a` are the environment's, from `H_SND` and `H_RCV`.) |
| `gap0`, `gap1`, `fwd`, `back_odd`, `rho_le`, `gam_le` | Edge-spacing bounds used by the data path. `back_odd` is where DACK's slow-path credit, `max Ar.lo Af.lo`, enters. |
| `pipe_ctl` | **(1) Main control theorem.** For every phase `j`, both excitations equal `Vph j` on `[c_i j, c_i (j+1))`. Induction on `j`: stage 0's phase `j+1` uses stage 1's phase `j` through the DACK line (`ack0_succ`), and stage 1's phase `j` uses stage 0's phase `j` through the request line (`phase1_of`). This is how the circularity (each stage is the other's environment) is broken. |
| `nodes_clean` | Both nodes are clean step signals: low from `L.hi` to the first edge, then `Vph j` on `[τ_i j, τ_i (j+1))`, for all `j`. |
| `pins_clean` | Stage 1's request pin is `Vph j` on `[R1 j, R1 (j+1))`. Stage 0's acknowledge pin is `!Vph j` on `[A0 j, A0 (j+1))`. These are clean environments in 6d's sense. |
| `live` | The edges strictly increase (given the environment's events), so every phase interval is non-empty and the pipe really moves. |
| `token0`, `token1` | **(2) Every token, every bit, both stages.** 6c's `Bundling.capture` is applied unchanged, with `Ton/Toff/Tnext = τ_i(2k)/τ_i(2k+1)/τ_i(2k+2)` derived from `nodes_clean`. Stage 1's data is stage 0's latch output, with its validity window from `token0`. |
| `pipe_forward` | **(3) Delivery.** The output bit holds token `k`'s value until the receiver's acknowledge falls (`γ(2k+1)`). Under three output-bundling inequalities, it holds from the acknowledge rise `γ(2k)`. |
| `Wit.witness`, `Wit.witness_data` | **Non-vacuity**, described in its own section below. |

Because the nodes are proved clean, the latch enable is exactly 6c's clean
pulse. Bundling's `H_EN_CLEAN` is discharged for a genuine delay interval,
not only for fixed delays as in 6d's `stage_token_clean`. 6d's
`capture_win` is no longer needed.

## Non-vacuity

`Wit.witness` and `Wit.witness_data` give one run that satisfies every
field of `Gates2`, `Env2`, `Timing2` and `Data2` at every instant `t`.

- **Delays.** Every read-time map is a fixed delay of 1 tick; feedback wires
  are 1; reset is released at 4; `Es = Er = 3`.
- **Traces.** Every net is a closed-form square wave `sq o`, so the gate
  relations are checked for all `t` (`key`, `x0_rel`, `x1_rel`).
- **Derived times.** They are computed from the recursion, not stated:
  `τ0 j = 5 + 4j`, `τ1 j = 7 + 4j` (`cc_w`).
- **Data.** One bit whose token values alternate (`val k = (k even)`), so a
  stuck or reset-valued latch cannot pass. Both latch bits are the real
  `ODD` INIT (`B8B8…`) as transport LUTs, made into a `LatchRel` through
  6c's `odd_latch`/`transport_gate`.
- `witness_data` also applies `pipe_forward` to this run. The output bit is
  token `k`'s value from `γ(2k)` to `γ(2k+1)`, for every `k`.
- **Non-degeneracy checks.** The nodes are not constant: `sq 5 5 = true`,
  `sq 5 9 = false`. The output alternates: `x1W 10 = true`,
  `x1W 18 = false`.

## The two-stage contract, with rules

**Notation.**
- `RT0 = Rq.lo + L1.lo + alo` and `RT1 = alo + L0.lo + Rq.lo` are the
  minimum round trips through the neighbour.
- `alo = min Ar.lo Af.lo`, `ahi = max Ar.hi Af.hi`.
- `V0` and `V1` are the per-bit latch windows (data `[dlo, dhi]`, enable
  branch `[elo, ehi]`, latch loop `[flo, fhi]`).

**"Rule" column.** H, I, F and A are rules in `cells/verify/tighten.py`.

| # | field | inequality / statement | meaning | rule |
|---|---|---|---|---|
| 1 | `Gates2.H_CTL*.H_LUT_FIFO` | ctl LUT = excitation read through a FIFO map `[L.lo, L.hi]` | **NEW and load-bearing**: one function edge gives one output edge; no static-hazard glitch on a pin change that leaves the function unchanged | not a rule; input data (prjxray arc min/max) plus the FIFO assumption, see "Fidelity" |
| 2 | `H_FB`, `H_LOOP_POS` | feedback wire window; loop ≥ 1 | as 6d | SDF; trivially true |
| 3 | `Gates2.H_REQ_LINE` | `r[1] = O0 ∘ Rq.σ`, FIFO | SDELAY chain + wires (`fifo_comp`) | `Rq.lo` is rule I's knob (rows 13, 14) |
| 4 | `Gates2.H_ACK_LINE` | `a[1] = O1∘Ar.σ ∨ O1∘Af.σ` | DACK FASTRISE: rise via tap, fall via ripple | `Af.lo` is rule H's knob (row 15); `alo` is the "FASTRISE, the fast side" term of rule I |
| 5 | `Gates2.H_RST`, `Timing2.H_RST_LONG` | reset high on `[0, R)`, `R ≥ L.hi + wh` | 5b `c2_reset` per stage | **unchecked** (6d row 8) |
| 6 | `Timing2.H_RST_LINES` | `R ≥ L0.hi + Rq.hi`, `R ≥ L1.hi + ahi` | power-up values flushed out of the lines by release | **unchecked**; new |
| 7 | `Env2.H_REQ*`, `H_ACK*`, `H_RST_EARLY` | clean shapes at the pipe's two external pins | environment | the environment's own cells (for an upstream link: this theorem) |
| 8 | `Env2.H_SND`, `H_RCV` | next edge ≥ `Es` / `Er` after the node edge it answers | four-phase partners | structural |
| 9 | `Timing2.H_LAT0` | `L0.hi + w0h ≤ L0.lo + min Es RT0` | stage 0's neighbours answer slower than its feedback wire plus its LUT spread | **unchecked** (6d row 7), now per stage; the internal term is DERIVED from `RT0` |
| 10 | `Timing2.H_LAT1` | `L1.hi + w1h ≤ L1.lo + min Er RT1` | same at stage 1 | **unchecked** |
| 11 | `Timing2.H_ACK_FLUSH` | `ahi ≤ L1.lo + max Er RT1 + alo` | node 1's high phase outlasts the DACK line's path spread | **unchecked**. A FASTRISE dual of rule F (rule F checks only FASTFALL request lines, which `bd_pipe` does not use: `RFAST = 0`). Partly an artefact of the two-path abstraction (in the real chain every element rises one hop after its input); see below |
| 12 | `Data2.H_DATA_LEAD` | `dS k + Sdr ≤ ρ(2k) + Lag` | data before the request at the pipe input | **rule A** (sender's request last, `Lag = 0`) |
| 13 | `Data2.H_SETUP0`, `H_PW0` | `dhi0 + fhi0 + Lag ≤ Sdr + 2·L0.lo + max Es RT0 + elo0`; `ehi0 + fhi0 ≤ L0.lo + max Es RT0 + elo0` | input data, and the enable pulse, outlast one latch loop before stage 0 closes | setup: rule I at the input ("not audited" for data from a pin); pulse: **unchecked** (6d row 14) |
| 14 | `Data2.H_I1`, `H_I1_SRC` | `ehi0 + dhi1 + fhi1 ≤ L0.lo + max Es RT0 + Rq.lo + L1.lo + elo1` (and the source-data variant) | stage 1 closes no earlier than stage 0's latched value arrives | **rule I** at boundary 1, word for word. The closing path is upstream rise → req line → L1 → ack fast side → L0 (fall) → req line → L1 → enable branch, which is `τ0(2k) + L0.lo + RT0 + Rq.lo + L1.lo + elo1`. The request line appears twice and the data path not at all; this is why SDELAY is the knob. The `fhi1` term is the latch-loop arc 6c's `counter_rule_I` says rule I omits. `max Es RT0 ≥ RT0`, so rule I's successor-only path is a sufficient instance |
| 15 | `Data2.H_H1` | `ehi1 ≤ max Ar.lo Af.lo + L0.lo + elo0 + dlo1` | stage 1's latest enable fall precedes stage 0's next value (DACK fall → stage-0 LUT → stage-0 enable → stage-1 D pin) | **rule H** at boundary 1. The DACK credit enters as the SLOW path's `lo` (a fall leaves the FASTRISE line late) |
| 16 | `Data2.H_DATA_REL`, `H_HOLD0` | `τ0(2k+1) + Erel ≤ dE k`; `ehi0 ≤ Erel + dlo0` | rule H at the input boundary (stage 0's DACK is folded into `Erel`) | **rule H**. Unlike 6d row 16 there is no `dlmax - dlmin` term: `Erel` is measured from the node's actual edge, which is proved unique |
| 17 | `Data2.H_PW1` | `ehi1 + fhi1 ≤ L1.lo + max Er RT1 + elo1` | stage 1's enable pulse | **unchecked** |
| 18 | `pipe_forward` hypotheses | `ehi1 ≤ Er`, `ehi0 + dhi1 ≤ Rq.lo + L1.lo + Er`, `dhi0 + dhi1 + Lag ≤ Sdr + L0.lo + Rq.lo + L1.lo + Er` | output valid by the receiver's acknowledge rise | the consumer's own rule (next stage's I; B, D or E at an edge-sampling consumer). The request's lead over the data, which grows with depth, is exactly `ehi0 + dhi1` against `Rq.lo + L1.lo` |
| 19 | `Data2.H_LATCH*`, `H_WIN*` | 6c `LatchRel`, windows well formed | Kleene latch from the real INITs | not timing rules |

## General N: the skeleton

Everything in sections 2–3 of the file is independent of `N`: `fifo_hold`,
`fifo_comp`, `or_hold_*`, `exc_phase`, `exc_pre`, `node_phase` and
`ctl_loop`. For `N` stages (`i < N`), boundary `b ∈ [1, N)` carries:
- a request line `Rq_b` (`O_{b-1}` → I0 of stage `b`; SDELAY);
- an acknowledge line `(Ar_b, Af_b)` (`O_b` → I1 of stage `b-1`; stage
  `b`'s DACK).

**Times.**
- `ρ_0 = ρ` (environment); `ρ_i j = Rq_i.fst (τ_{i-1} j)` for `i ≥ 1`.
- `α_i 0 = R`; `α_i (j+1) = ackT_{i+1} j (τ_{i+1} j)` for `i < N-1`;
  `α_{N-1} (j+1) = γ j`.
- `c_i j = max (ρ_i j) (α_i j)` and `τ_i j = L_i.fst (c_i j)`.
- `c_i j` depends on `c_{i-1} j` and `c_{i+1} (j-1)`, so the recursion is
  well founded on `2j + i`. In Lean: recursion on `j` with an inner
  recursion on ascending `i`.

**Induction.** Same order: phase `(i, j)` uses `(i-1, j)` through the
request line (`fifo_hold`) and `(i+1, j-1)` through the DACK line
(`or_hold_*`). The step lemma is `exc_phase` unchanged.

**Derived departures.** These are the `dep0a`/`dep1r` pattern:
- `ρ_i(j+1) ≥ c_i j + L_i.lo + (alo_i + L_{i-1}.lo + Rq_i.lo)`;
- `α_i(j+1) ≥ c_i j + L_i.lo + (Rq_{i+1}.lo + L_{i+1}.lo + alo_{i+1})`.

**Obligations per stage `i`.** `H_LAT_i` and `H_PW_i`.

**Obligations per boundary `b`.**
- `H_I_b`: rule I with `Rq_b.lo` counted twice on the closing path.
- `H_H_b`: rule H with `max Ar_b.lo Af_b.lo`.
- `H_ACK_FLUSH_b`: the FASTRISE dual of F.
- `H_RST_LINES_b`.

**Source term.** The data that rippled through transparent stages
(`H_I_SRC`) becomes a recursion over `Td_b = max (τ_{b-1}(2k) + ehi_{b-1},
Td_{b-1} + dhi_{b-1})`. This is where the request's lead over the data,
which grows with depth (`bd_link.v` header; 441 ps measured at N = 4),
enters the proof.

**Estimate.** About 1 day to write the general-`N` recursion and induction
in Lean. No new idea is needed; the work is index bookkeeping and the two
boundary stages.

## What did not work / not done

- **General N is not in Lean.** It is the skeleton above. N = 2 is complete
  (control, data and witness).
- **Route (b) was not pursued.** Under the non-FIFO window channel, a node
  can show the NEW value for one tick early in its window and then fall
  back: a runt.
  - At the next stage that runt is a request with `¬ack = 1`, so the
    excitation there is `req ∨ qp`. This is the configuration of 5b's
    `runt_oscillates`, whose oscillation stops only when the real request
    edge forces the loop.
  - The downstream node therefore glitches over a wider window, and so on
    down the pipe.
  - "Clean outside a window" is thus not preserved with a fixed window
    width. It would need a bound on the cascade. This is not proved either
    way; it is an informal argument.
- **The FIFO hypothesis (`H_LUT_FIFO`, `H_REQ_LINE`, `H_ACK_LINE`) is
  assumed, not derived.**
  - It cannot be derived from 6a/6c's Kleene/window LUT models, which
    allow in-window glitches by design.
  - It is the one new physical assumption that makes composition work.
  - Testing it needs GLS or the board: a single function edge must never
    give more than one output edge. Nominal-delay simulation cannot show
    this.
- **The DACK line is a two-path abstraction.** It is the OR of a fast and a
  slow FIFO copy, not a gate-by-gate FIFO model of 6c's `fastrise_line`
  chain. Iterating `or_hold_*` and `fifo_hold` along the chain would remove
  this (estimate: half a day).
  - `H_ACK_FLUSH` asks the slow path to have taken the RISE before the node
    falls again. In the real chain every element rises one hop after the
    input (the taps), so the physical requirement is much weaker than the
    row as stated.
- **Not instantiated through 6d.** The pipe theorem does not instantiate
  6d's `CtlEnv` for each stage. `ctl_loop` shows that a FIFO controller is
  a 5b `Loop`, so 6d's lemmas apply. `pipe_ctl` re-proves what is needed
  per phase, because `CtlEnv` takes all phases' hypotheses at once, which
  is circular in a pipe.
- **Environment causality is stated against the node's edge `τ`**
  (`H_SND`, `H_RCV`, `H_DATA_REL`), not as 6d's "observed at some `u`".
  The two are equivalent once the node is proved clean, since `τ` is the
  first instant the new value is visible. The pipe-internal causality is
  not assumed at all.
- **The witness uses unit delays**, not ps-scale prjxray numbers. It shows
  the hypotheses are jointly satisfiable at every instant; it is not a
  model of a route.

## Verdict

**Works.** For N = 2, the composition gap 6d left is closed under genuine
delay intervals:
- every controller output and every internal pin is proved to be a clean
  four-phase signal;
- the cross-boundary causality is derived;
- every token's value is proved to pass through both stages and be
  delivered, for all tokens and all bits;
- a fixed-delay witness satisfies every hypothesis, control and data, at
  every instant.

The general-N version is a mechanical extension of the same lemmas
(about 1 day).

**What it buys.** The `bd_pipe` contract is now one list of named
obligations, per stage and per boundary:
- rule I appears word for word at the internal boundary, with SDELAY on
  the closing path twice, plus the latch-loop arc that 6c says rule I
  misses;
- rule H appears with DACK's slow-path credit;
- four items are checked by no rule today:
  - per-stage env latency (`H_LAT_i`);
  - enable pulse width (`H_PW_i`);
  - reset sequencing including line flushing (`H_RST_*`);
  - the FASTRISE flush (`H_ACK_FLUSH`).

It also isolates the single physical assumption the composition rests on:
FIFO, single-edge LUTs and lines (`H_LUT_FIFO`). This should be a named
target for the board-fidelity GLS.

## Fidelity per primitive

- **Controller LUT.** Real INIT `0x00B2…` via `lutB`. Binary pins; no X and
  no metastability. Lumped arc. The LUT's Boolean function of its
  instantaneous pins is read through a **FIFO** bounded delay
  `[L.lo, L.hi]`. This is stronger than 5b/6d's window channel (and
  implies it: `fifo_win`, `ctl_loop`). It assumes:
  - no static hazard when a pin changes and the function does not (a
    pass-transistor mux selecting between equal leaves; this is
    H_KLEENE_LUT territory, 6a);
  - edges do not overtake.
- **Controller feedback wire.** 5b's window channel `[wl, wh]`. Non-FIFO is
  allowed here: only its stable stretches are used.
- **Request line (SDELAY + wires).** FIFO. A chain of FIFO LUT1s and wires
  is FIFO by `fifo_comp`.
- **Acknowledge line (DACK FASTRISE + wires).** The OR of two FIFO copies of
  the node (tap path and ripple path). This abstracts 6c's gate-level
  `fastrise_line`; see above.
- **Latch LUTs.** 6c's Kleene closure of the real INITs over per-pin windows
  (H_KLEENE_LUT), unchanged. In the witness: the real `ODD` INIT as a
  transport LUT.
- **Environment.** Clean pins plus causal latencies `Es`, `Er` and `Erel`,
  measured from the proven node edges.
- **Time.** ℕ ticks. FIFO is the ℕ version of shard A's real-time `Pure.Chan`.
