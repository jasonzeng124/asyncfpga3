# B probe 6f: a timed `bd_pipe` with any number of stages `N ≥ 1`

File: `formal/lean/Formal/Cells/PipeTimedN.lean` (core Lean, about 1200
lines). It imports `Formal.Cells.PipeTimed` (6e) read-only, and through it
`LinkTimed`, `CElemTiming`, `Bundling` and `LinkHandshake`. The
`PipeTimed` olean was missing, so it was compiled with the brief's
command. This file adds no shared definitions; its new general-purpose
definitions (`fmin`, `fmax`, `orAll`, `cpath`, `cguard`, `fr_bin`) live in
it.

The file checks clean, with no errors and no warnings, in about 5 s. It
contains no `sorry`, `admit`, `axiom` or `native_decide`.

Check command:

    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/PipeTimedN.lean

**Axioms.** `#print axioms` was run on a scratch copy.
- These use only {propext, Classical.choice, Quot.sound}: `pipe_ctl`,
  `nodes_clean`, `pins_clean`, `live`, `token`, `pipe_forward`,
  `orn_hold_true`, `orn_hold_false`, `Wit.witness` and `Wit.witness_data`.
- These use only {propext, Quot.sound}: `fastrise_or`, `Wit.chain_w` and
  `Wit.witness_dack1`.

No routed numbers are reported here. Nothing in this probe depends on a
nextpnr build.

## What is proved

**The model.**
- Every `N ≥ 1` is covered, with per-stage delays `L i`.
- Each boundary `b ∈ [1, N)` has a request line `Rq b` and a DACK line made
  of `m b + 1` FIFO paths `Ap b k`.
- The environment's edge times are `ρ` (at `r[0]`) and `γ` (at `a[N]`).

**Event times are defined, not assumed.** `PN.cc` defines them by an outer
recursion on the phase `j` and an inner, ascending recursion on the stage
`i` (`PN.row`). This is the `2j + i` order from 6e's notes:
- `c i j = max (Rin i j) (Ain i j)`
- `Rin 0 j = ρ j`
- `Rin (i+1) j = Rq(i+1).fst (τ i j)`
- `Ain i 0 = R`
- `Ain i (j+1)` is `ackT (i+1) j (τ (i+1) j)` inside the pipe, and `γ j`
  at the last stage
- `τ i j = L i .fst (c i j)`

`c_eq` checks the closed equation definitionally.

| theorem | statement |
|---|---|
| `ge_R`, `tau_lo`, `Rin_lo`, `Ain_lo`, `fwd`, `rho_le`, `gam_le` | Bookkeeping: every phase of every stage starts after reset, and each derived time is at least its cause plus the channel's `lo`. |
| `depR`, `depA`, `dep_c` | **Causality at every boundary is derived.** The request (or acknowledge) pin of stage `i` departs at least `ER i` (or `EA i`) after stage `i`'s node edge. `ER 0 = Es` and `EA (N-1) = Er` are the environment's. Inside the pipe, `ER (i+1) = alo + L i.lo + Rq(i+1).lo` and `EA i = Rq(i+1).lo + L(i+1).lo + alo`. |
| `gap` | Stage `i`'s node edges are at least `Won i = L i.lo + max (ER i) (EA i)` apart. |
| `back_odd` | Stage `i`'s rise after stage `i+1`'s fall comes through the slowest DACK path (`aslow`). |
| `pre` | Before the first phase, every excitation is 0 and every node is low from `L.hi` on. Proved by induction on `i`. |
| `pipe_ctl` | **(1) Clean control for all N.** For every phase `j` and every stage `i < N`, the excitation of the real `bd_c2n` INIT equals `Vph j` on `[c i j, c i (j+1))`. See "Proof of `pipe_ctl`" below. |
| `nodes_clean` | Every node is low from `L.hi` to its first edge, then `Vph j` on `[τ i j, τ i (j+1))`. One edge per phase. |
| `pins_clean` | At every boundary `b`, stage `b`'s request pin is `Vph j` on `[Rin b j, Rin b (j+1))`, and stage `b-1`'s acknowledge pin is `!Vph j` on `[Ain (b-1) j, Ain (b-1) (j+1))`. |
| `live` | Every stage's node edges strictly increase. This needs `1 ≤ L i.lo + wh i`. |
| `token` | **(2) Every stage latches every token, every bit** on `[Sx i k b, τ i (2k+2) + elo)`. Induction on the stage, through 6c's `Bundling.capture` unchanged. |
| `pipe_forward` | **(3) Delivery.** The last stage's output carries token `k`'s value until the receiver's acknowledge falls (`γ(2k+1)`). If `Dl (N-1) b ≤ Er`, it also carries it from the acknowledge's rise `γ(2k)`. |
| `orn_hold_false`, `orn_hold_true` | A clean stretch passes through an OR of `m+1` FIFO copies. The high stretch needs the line flushed: every copy takes the rise before any copy takes the fall. |
| `fastrise_or` | **DACK, gate by gate**: the real FASTRISE chain is an OR of FIFO copies of its input. See "The DACK refinement" below. |
| `Wit.witness`, `Wit.witness_data`, `Wit.chain_w`, `Wit.witness_dack1` | Non-vacuity, described in its own section below. |

**Proof of `pipe_ctl`.** The outer induction is on `j` and the inner one on
`i`, ascending.
- Phase `(i, j)` takes its request pin from `(i-1, j)`, through `req_of`
  (`node_phase` and then `fifo_hold`).
- It takes its acknowledge pin from `(i+1, j-1)`, through `ack_succ`
  (`orn_hold_*`). For `j = 0` it uses `ack_zero`, and at the last stage the
  environment (`ack_last`).
- The step itself is 6e's `exc_phase`, unchanged.

**The DACK refinement (`fastrise_or`).**
- **The cell.** `bd_delay #(.N(DACK), .FASTRISE(1))`:
  - `s1 = lutB BUF [s0]`;
  - `s(i+1) = lutB FR_SIDE [s i, s0]`, with I0 = chain, I1 = tap, and the
    real INITs `2'h2` and `4'hE`;
  - each LUT is a FIFO map, with each pin's wire composed into it.
- **The result.** `s(n+1)` is the OR of `n+1` FIFO copies `cpath n k` of
  `s0`:
  - path 0 is the full ripple;
  - path `k ≥ 1` enters at side stage `k`'s tap.
- **What replaces 6e's two-path abstraction.** `GatesN.H_ACK_LINE` is the
  `m+1`-path OR. The real chain discharges it with `m = DACK-1`,
  `Ap = cpath`, `Ag = cguard`. 6e's two-path line is the case `m = 1`.

## Non-vacuity (all N ≥ 1)

`Wit.witness N` and `Wit.witness_data N` cover every `N ≥ 1`.

**The run.**
- **Delays.** Every map is a unit delay. Reset is released at 4, and
  `Es = Er = 3`.
- **Traces.** Stage `i` has its request pin at `sq (4+2i)`, its node at
  `sq (5+2i)`, its feedback at `sq (6+2i)` and its acknowledge pin at
  `sq (8+2i)`.
- **Gate relations.** They hold at every instant (`ctl_w` uses 6e's `key`
  for the real `bd_c2n` INIT).
- **Derived times.** The recursion is solved in closed form:
  `c i j = 4+2i+4j` and `τ i j = 5+2i+4j` (`cc_w`, `τ_w`). The result is
  computed, not stated.

**Data.**
- One bit, with alternating token values.
- Every latch bit is the real `ODD` INIT as a transport LUT (6e's
  `latch_of`, through 6c's `odd_latch`). Stage `i` shows token `m` on
  `[6+2i+8m, 14+2i+8m)`.
- `Dl i = 1` for all `i` (`Dl_w`).
- `pipe_forward` is applied: the last stage delivers token `k`'s value on
  `[γ(2k), γ(2k+1))` for every `k`.
- The output is not constant: true at `γ 0`, false at `γ 2`.

**The chain.**
- `Wit.chain_w`: a unit-delay FASTRISE chain of length `n+1 ≥ 2`, for any
  input trace, satisfies `fastrise_or`'s hypotheses.
- Its fastest path has `lo = 1`, so a rise crosses in one hop. Its slowest
  has `lo = n+1`, so a fall takes the whole chain. The DACK credit `aslow`
  is the chain length, derived from the INITs.
- `witness_dack1`: the pipe witness's lines are exactly the `DACK = 1`
  chain (one LUT1).

## The contract for N stages

**Notation.**
- `ER`, `EA` and `Won` are defined in "What is proved" above.
- `alo b = min_k Ap(b,k).lo` (fastest path).
- `ahi b = max_k Ap(b,k).hi`.
- `aslow b = max_k Ap(b,k).lo` (the slowest path's minimum: the ripple).

**"Rule" column.** H, I, F and A are rules in `cells/verify/tighten.py`.

| scope | field | statement | rule (as in 6e) |
|---|---|---|---|
| stage `i` | `GatesN.H_CTL i` | 6e `Ctl`: real INIT, `H_LUT_FIFO`, `H_FB`, `H_LOOP_POS` | FIFO assumption (6e row 1) |
| boundary `b` | `H_REQ_LINE` | `r b = O (b-1) ∘ Rq b`, FIFO | SDELAY |
| boundary `b` | `H_ACK_LINE` | `a (b-1) = OR_k O b ∘ Ap(b,k)`; a THEOREM for the real chain (`fastrise_or`) | DACK |
| stage `i` | `H_RST_LONG i` | `L i.hi + wh i ≤ R` | **unchecked** |
| boundary `b` | `H_RST_LINES b` | `L(b-1).hi + Rq b.hi ≤ R`, `L b.hi + ahi b ≤ R`, `Ag b ≤ R` | **unchecked** |
| stage `i` | `H_LAT i` | `L i.hi + wh i ≤ L i.lo + min (ER i) (EA i)`; the internal terms are DERIVED round trips | **unchecked** |
| boundary `b` | `H_ACK_FLUSH b` | `ahi b ≤ Won b + alo b`: stage `b`'s high phase outlasts the line's path spread | **unchecked** (FASTRISE dual of F). With `fastrise_or` this is now a statement about the real chain's paths: `ahi` is the ripple's `hi`, and `alo` is the last tap's `lo` |
| env | `EnvN` | clean pins plus `H_SND`, `H_RCV` | environment |
| input | `H_DATA_LEAD`, `H_DATA_REL`, `H_HOLD0`, `H_SETUP0` | as 6e | A, H, I (input) |
| stage `i` | `H_PW i` | `ehi + fhi ≤ Won i + elo` | **unchecked** |
| boundary `b` | `H_I b` | `Dl (b-1) + dhi_b + fhi_b ≤ Won (b-1) + Rq b.lo + L b.lo + elo_b` (in ℤ) | **rule I** at boundary `b`; for `b = 1` it is 6e's `H_I1` and `H_I1_SRC` together |
| boundary `b` | `H_H b` | `ehi_b ≤ aslow b + L(b-1).lo + elo_{b-1} + dlo_b` | **rule H** with the slowest DACK path's credit |
| output | `pipe_forward` | `Dl (N-1) b ≤ Er` | the consumer's own rule |

**The depth recursion (`Dl`).** This is the integer-valued lateness of the
data relative to each stage's own rise:
- `Dl 0 = max ehi0 (Lag - Sdr - L0.lo + dhi0)`;
- `Dl (i+1) = max ehi(i+1) (Dl i - Rq(i+1).lo - L(i+1).lo + dhi(i+1))`.

`Sx_le` proves `Sx i ≤ τ i (2k) + Dl i`.

Reading it:
- each boundary credits `Rq.lo + L.lo` against the data arc `dhi`;
- this is where the request's lead over the data, which grows with depth,
  enters the proof;
- `H_I` at every boundary is one inequality on `Dl`, so the source-ripple
  term 6e had as a separate `H_I1_SRC` is folded in.

## What did not work / not done

- **Joint witness with DACK ≥ 2 in the pipe: not done.**
  - The pipe witness uses `DACK = 1` lines.
  - `chain_w` separately shows longer chains are OR lines with
    `alo = 1` and `aslow = n+1`.
  - A pipe witness with longer chains has unequal rise and fall latencies,
    so the acknowledge waves are not `sq`. It needs a new closed-form
    waveform and controller check (estimate 1–2 h).
- **The DACK refinement uses FIFO LUTs, not 6c's Kleene/window
  `fastrise_line`.**
  - 6c's model allows in-window glitches. A glitching acknowledge breaks
    the per-phase hazard-freedom of the next C-element (6e's notes,
    route (b)).
  - So the chain is refined at gate level under the same `H_LUT_FIFO`
    assumption as the controllers. The real INITs are evaluated by
    `lutB`; the FIFO maps carry the timing.
  - 6c's `fast_edge`, `slow_not_early` and `slow_arrives` are not used.
- **Unchanged from 6e:**
  - the FIFO assumption itself is assumed, not derived;
  - the environment's causality is stated against the proven node edges;
  - there is no instantiation through 6d's `CtlEnv`;
  - the witnesses use unit delays, not prjxray numbers.
- **The `H_I` closing path is one of two valid lower bounds.** `H_I b` uses
  the path through stage `b-1`'s fall, which is rule I's closing path. A
  second valid bound, through stage `b`'s own on-time
  (`τ b (2k) + Won b`), is not offered as an alternative. A design meeting
  only the second bound would need a variant of `token` (small change).

## Verdict

**Works.** This is the general-N statement 6e left as a skeleton. For every
`N ≥ 1`:
- every controller excitation, node and internal pin of `bd_pipe` is
  proved to be a clean one-edge-per-phase signal;
- causality is derived at every boundary;
- every token's value passes every stage and is delivered;
- the pipe is live;
- a unit-delay witness satisfies every hypothesis for every `N`.

The DACK line is now the real gate-level FASTRISE chain, with FIFO LUTs and
real INITs, instead of a two-path abstraction. The DACK credit
(`aslow` = the ripple's `lo`) and the flush condition (`ahi`, `alo`) are
properties of named chain paths.

The effort was about 2 h, against the 1-day estimate in the 6e notes,
because the 6e step lemmas carried over unchanged.

**What it buys.** The whole `bd_pipe` contract is a finite list of
inequalities:
- per stage: `H_LAT`, `H_PW`, `H_RST_LONG`;
- per boundary: `H_I`, `H_H`, `H_ACK_FLUSH`, `H_RST_LINES`.

Rule I and rule H appear at every boundary. The depth-growing data lead is
explicit as `Dl`. These are the targets a tighten.py audit (or a GLS check)
of an N-stage pipe should cover. Four rows are still checked by no rule
today: `H_LAT`, `H_PW`, `H_RST_*` and `H_ACK_FLUSH`.

## Fidelity per primitive

- **Controller LUT.** As 6e: real `bd_c2n` INIT via `lutB`, binary pins, a
  FIFO read-time map `[L.lo, L.hi]` (`H_LUT_FIFO`). It assumes:
  - no static-hazard glitch;
  - no edge overtaking.
- **Controller feedback wire.** 5b's window channel (non-FIFO allowed).
- **Request line.** FIFO (`fifo_comp` of the LUT1s and wires).
- **DACK line.** Gate level:
  - a LUT1 `BUF` and LUT2 `4'hE` side stages with the real INITs via
    `lutB`;
  - each a FIFO map, with pin wires composed into the arc maps (`C i` for
    the chain pin, `U i` for the tap pin);
  - the output is proved to be an OR of FIFO path copies (`fastrise_or`);
  - same FIFO assumption as the controllers.
- **Latch LUTs.** 6c's Kleene closure of the real INITs over windows
  (`LatchRel`). In the witness, the real `ODD` INIT as a transport LUT.
- **Environment.** Clean pins and causal latencies `Es`, `Er`, `Erel`.
- **Time.** ℕ ticks. The data lateness `Dl` is in ℤ.
