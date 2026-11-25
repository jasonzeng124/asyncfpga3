# Probe Bq: fidelity of H_LUT_FIFO (the controller LUT as a FIFO channel)

File: `formal/lean/Formal/Cells/FifoFidelity.lean` (core Lean, about 520 lines).
It imports `Formal.Cells.PipeTimed` and `Formal.Core.Delay.SAF` (read-only, via
their existing oleans). It adds no shared definitions that other files need;
its own definitions are in namespace `Formal.Cells.FifoFidelity`.

Check command:

    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/FifoFidelity.lean

Status: **checks clean** in about 2 s, with no errors and no warnings. It has no
`sorry`, `admit`, `axiom` or `native_decide`. `#print axioms` was run on a
scratch copy for every theorem listed below. The worst case is
{propext, Classical.choice, Quot.sound}; `fifo_of_transport` uses no axioms.

No routed numbers are reported, and no nextpnr build was run. The pin
assignments quoted in section 3 were read from the existing fixtures in
`formal/tools/fasm2lean/fixture/ce_pair_s{1..4}.fasm` (C-11b). Their toolchain
record is in the `.toolchain` files next to them.

## The question

`PipeTimed` and `PipeTimedN` assume `Ctl.H_LUT_FIFO`:

    O t = ex req ack qp rst (L.σ t)     (σ monotone, t - L.hi ≤ σ t ≤ t - L.lo)

Here `ex` is the LUT's Boolean function of its pins **at one instant**. The
assumption has two parts:
- **(F1)** no edge overtakes another;
- **(F2)** a pin change that leaves the function unchanged causes no output
  glitch.

A real LUT does not read its pins at one instant. Each pin reaches its
mux-tree select through its own site-pin buffer, and these delays differ by up
to about 0.5 ns (prjxray: A1 0.416–0.516 ns slow, A5 0.091–0.112, A6 about
0.005). nextpnr's SDF charges a flat 25 ps per pin (C-10c), and the router
permutes pins freely (C-11a).

## 1. Which other models imply H_LUT_FIFO

| model | implies H_LUT_FIFO? | proved here / where |
|---|---|---|
| A's bounded transport (`Core/Trace/Discrete` `Transport`, the ℕ form of `Core/Delay/Pure` `Chan`), placed after a zero-time function of the pins | **yes, same band**. A `Warp` is a `Ret` | `retOfWarp`, `fifo_of_transport` |
| research GLS LUT = SAF (A-delay-saf), one `d` per LUT | **yes, but with band `[1, d]`**. With a spaced excitation (one edge per `d`) it gives band `[d, d]` | `saf_fifo`, `gls_lut_fifo`, `gls_lut_fifo_spaced` |
| research GLS with per-pin specify arcs (A's Wip W1) | **yes, in value order, with band `[~1, d_max]`** (sketch only, not proved). Every fire copies `f` of the *current* pins and fire instants increase, so a crossed fire order changes latency, not value order | not in Lean |
| involution channel (A, `Core/Delay/Involution.lean`) | **single input only.** Order of non-cancelled transitions is FIFO by A's `cancel_iff` (output `n+1` is after output `n` iff `t(n+1) − o(n) > −δmin`). Pulses either cancel in pairs or shrink, and never invert. The band is `[δ(T0), δ∞)` only under input separation `T ≥ T0` (A's `up_bounds`, `down_bounds`). Without separation a surviving runt has delay below any fixed `lo` | A's theorems, not re-proved here (Mathlib/ℝ) |
| 5b/6d window channel (`WinDelay`) | **no**. It is strictly weaker (`PipeTimed.fifo_win` goes one way only) | 6e |
| per-pin site delays into the function (C-10b `gate_window`, the model of section 3 here) | **no in general** (counterexample, section 4). **Yes** if the pin maps are equal (`equal_pins_fifo`). **Yes** under the select-order condition H_SEL_ORDER, run by run (`sel_phase` + `pinlut_fifo_of_edges`) | here |

**What follows from the table.** All of A's channels are *single-input*. In
each of them the function is evaluated at one instant and the delay comes
after it, so they all imply (F2) by construction. (F1) then follows from
monotonicity of the read-time map, and for involution channels from
`cancel_iff`. None of them can show the one way a LUT really violates
H_LUT_FIFO: pins that reach the function at different times.

This has a direct consequence for the GLS:

- **The research GLS cannot falsify H_LUT_FIFO** (`gls_lut_fifo`). Its
  `SLICE_LUTX` is a zero-time mux tree followed by a specify path. Every GLS
  run satisfies H_LUT_FIFO, with band `[1, d]`.
- To test the assumption, the GLS must put per-pin delays **before** the
  function. For example, write each pin as a transport delay of its site-pin
  value from prjxray (`assign #(d_Ak) a_int = a;`). Currently the GLS models
  them, if at all, as arcs after the function.

## 2. The real `bd_c2n` INIT: which pin orders matter

`exc INIT_c2n a b q r = ¬r ∧ maj(a, ¬b, q)`. This is 5b's `c2n_eq`, from the
real INIT `0x00B2…`.

- **(req, c_next) is order-free.** Three lemmas cover it:
  - `c2n_set`: both inputs at the target give `v`, whatever `q` is.
  - `c2n_hold`: `q = v` and either input at the target give `v`.
  - `c2n_stay`: `q = !v` and either input not yet at the target give `!v`.
- In a phase, req and `¬c_next` each move once toward the target. Whichever
  reaches the tree first, the excitation stays `!v` until the later one
  arrives, then becomes `v`. So **this pair can produce neither a static
  glitch nor a reorder, whatever the per-pin delays.** Reordering them only
  moves the edge, to the later of the two select arrivals (`sel_edge_lo/hi`).
- The protocol guarantees the "each moves once toward the target" premise.
  With `U, O, N` the upstream, own and downstream nodes:
  - `O` is excited iff `U ≠ O ∧ N = O`;
  - `U` can move only when `U = O`, which makes `U ≠ O`;
  - `N` can move only when `N ≠ O`, which makes `N = O`.

  So both inputs only ever move toward exciting `O`, and both are frozen
  while `O` is excited.
- **The rst pin is order-free at release too.** `c2n_reset` gives 0 while
  `rst = 1`. Once `rst = 0`, `c2n_stay` with `v = 1` gives 0 until the request
  arrives. A late `rst` select only delays the first edge.
- **The one ordered pair is (feedback `q`, first departure).** After `O`
  changes, the environment may answer. If the departing request or
  acknowledge reaches its select **before** the feedback reaches its own, the
  excitation falls back to `!v`. This is `sel_runt`, the runt of 5b's
  `runt_oscillates`. This is 5b's `H_ENV_LATENCY`, but it must hold **at the
  selects**, not at the pins.

## 3. The per-pin model and the exact condition

`PinLut req ack rst O qp` has the following parts:
- four pin-to-select FIFO maps `pr pa pq ps`. This is **H_PIN_FIFO**: an input
  buffer is a single-input chain, so it is FIFO by A's `Pure` argument;
- one output map `out`. This is **H_TREE_FIFO**: the mux tree plus the output
  stage, read as one FIFO channel of the select-level function;
- the relation `O t = exSel … (out.σ t)`.

| theorem | statement |
|---|---|
| `equal_pins_fifo` | if all four pin maps are the same `p`, the node satisfies `Ctl.H_LUT_FIFO` with `L = p ; out` |
| `sel_phase` | **select-level phase.** Request `v` on `[ρ,ρ')`, ack `!v` on `[α,α')`, feedback `v` on `[κ,κ')`, rst low from `R`. Under **H_SEL_ORDER** `pq.fst κ ≤ min (pr.fst ρ') (pa.fst α')` and `H_SEL_KEEP`, the select-level excitation is exactly `v` on `[max(pr.fst ρ, pa.fst α), max(pr.fst ρ', pa.fst α'))` |
| `sel_runt` | if at the selects the request has left, the ack has not, and the feedback has not arrived, the excitation is `!v` (a runt) |
| `sel_order_of_lat` | **arithmetic form.** If the feedback reaches its pin by `K`, both departures leave their pins at or after `D ≥ 1`, and `K + pq.hi ≤ D + min pr.lo pa.lo`, then H_SEL_ORDER holds |
| `sel_edge_lo`, `sel_edge_hi` | the select-level edge lies in `[max ρ α + min(pr.lo,pa.lo), max ρ α + max(pr.hi,pa.hi)]`. So a lumped band must span the per-pin spread |
| `ret_of_edges` | **events ⇒ FIFO.** If `y` makes exactly `x`'s phase sequence, each edge delayed within `[lo,hi]` (`lo ≤ hi`), then `y` is a FIFO read of `x`. This is the ℕ, alternating-signal case of A's open `Wip.events_adequate`. The explicit map is `σ t = max (c (idx t)) (t − hi)` |
| `pinlut_fifo_of_edges` | **per-pin model ⇒ H_LUT_FIFO, run by run.** If the pin-level `ex` and the select-level `exSel` have the same phase sequence with edge delays in `[lo,hi]`, the node satisfies `Ctl.H_LUT_FIFO` with band `[lo + out.lo, hi + out.hi]` |

**The exact condition, stated from the node edge `τ`.** Let `E_τ` be the
earliest time after `τ` at which request or acknowledge leaves its target at
its **pin**, and `w_hi` the feedback wire's upper delay. Then:

    H_SEL_ORDER:   w_hi + pq.hi  ≤  E_τ + min(pr.lo, pa.lo)

This is `sel_order_of_lat` with `K = τ + w_hi` and `D = τ + E_τ`.

- With equal pin delays this reduces to the lumped 5b/6e `H_ENV_LATENCY`
  shape, `w_hi ≤ E_τ` up to the LUT spread.
- **The new term is `pq.hi − min(pr.lo, pa.lo)`**: the feedback pin's slowest
  site-pin delay minus the departing pins' fastest.

**Answer to the probe's guess.** The guess was "consecutive changes on
different pins separated by more than the per-pin spread". That condition is
sufficient for a generic LUT (not proved here), but it is **the wrong shape
for `bd_c2n`**:
- req and c_next need **no** separation at all;
- only the (feedback, departure) pair needs one;
- the needed separation is the signed difference above, not the symmetric
  spread. It is negative, and therefore free, when the feedback lands on the
  faster pin.

**Where the routed pins actually land** (fixtures, function-matching per
C-11a plus the `IMUX` sources in the FASM):

| fixture | pins carrying {req, feedback} | ack | rst |
|---|---|---|---|
| `ce_pair_s1` | A1 and A5 | A4 | A3 |
| `ce_pair_s2` | A1 and A5 | A3 | A4 |
| `ce_pair_s3` | A1 and A2 | A5 | A3 |
| `ce_pair_s4` | A1 and A5 | A3 | A4 |

- req and feedback are symmetric in `maj`, so the INIT alone cannot tell which
  of the two pins is which.
- In s1, the A5 source is `LOGIC_OUTS12`, which is probably the LUT's own
  output. That reading puts the feedback on A5 (fast), which is favourable.
- In s4, the A1 source is `LOGIC_OUTS17`, which is probably the LUT's own
  output through its MUX output. That reading puts the feedback on A1, the
  slowest pin, with the request on A5. This is the unfavourable case:
  `pq.hi − pr.lo ≈ 0.516 − 0.091 ≈ 0.43 ns` at the slow corner.
- **Not verified**: I did not check the LOGIC_OUTS index map against
  prjxray-db. C-11b's fasm2lean already resolves net-to-pin and would settle
  it.
- **Conclusion: the placer does put a feedback on A1 in some routes**
  (probably), so the term is not hypothetical.

## 4. Counterexample with the real INIT (`ce_*`, `cj_*`)

The time unit is ticks. The run is built as follows:
- pin-to-select delays: req 1, ack 1, **feedback 6**, rst 1;
- tree plus output stage: 2;
- feedback wire: 1;
- the request is high on `[10, 16)`, so the upstream stage answers 3 ticks
  after the node rose at 13;
- the acknowledge stays low, because the downstream stage is slow.

A 5-tick difference between the feedback pin and the request pin is the
A1/A5 slow-corner difference at about 0.085 ns per tick.

- `ceLut`: this trace is a behaviour of `PinLut` with every gate relation
  holding at every instant. The closed form is proved against the real INIT
  (`eI_loop`, which is `decide` up to 40 and periodicity beyond).
- `ce_node`: the node rises at 13, **drops at 19, and rises again at 22**. It
  then oscillates with period 9, because the loop with req = ack = 0 is a
  buffer that recirculates the hole.
- `ce_not_fifo`: **for every `Ret` with `hi ≤ 18`** (the physical band is
  `[3, 8]`), the node is **not** a FIFO read of the pin-level `ex`. So
  H_LUT_FIFO fails.
- The pin-level timing satisfies 5b/6e's lumped `H_ENV_LATENCY` when the LUT
  band is taken from equal pin delays (`L = [3,3]`, `wh = 1`, `E = 3`:
  `4 ≤ 6`). It fails with the true band `L = [3,8]` (`9 > 6`), and it fails
  H_SEL_ORDER (`1 + 6 > 3 + 1`).
- `cj_fifo` and `cj_clean`: **the same environment with the feedback on a
  1-tick pin** is clean. The node makes one edge at 13 and satisfies
  H_LUT_FIFO via `equal_pins_fifo`.

So moving one net to a slower site pin, which the SDF does not see, is enough
to break a run that every SDF-based number calls safe.

## 5. Verdict: the precise condition, and which rule checks it

**H_LUT_FIFO holds for `bd_link_ctl`** (proved run by run by `sel_phase` +
`pinlut_fifo_of_edges`, with `H_SEL_KEEP` and phase bookkeeping as in 6e)
under these conditions:

1. **H_PIN_FIFO**: each pin's input buffer is a FIFO channel (single-input
   CMOS chain, A's `Pure` argument). Grade: high.
2. **H_TREE_FIFO**: the tree and output stage are a FIFO read of the
   select-level function. This includes "one select switching between equal
   leaves makes no glitch" (B-muxtree-fidelity: plausible, unverified;
   charge-sharing runt not excluded). Grade: B.
3. **H_SEL_ORDER at every phase**: `w_hi + pq.hi ≤ E_τ + min(pr.lo, pa.lo)`,
   with `pq`, `pr`, `pa` the site-pin bands of the PHYSICAL pins the router
   chose.
4. **H_RST_LONG**, as in 6e. The rst pin needs no ordering of its own beyond
   it.

The 6e band to use is `L = [out.lo + min(pr.lo, pa.lo), out.hi + max(pr.hi, pa.hi)]`.

**Which rule checks it: none.**
- Item 3 is 6e's row 9 (`H_LAT_i`, already "unchecked") with a new per-pin
  term.
- No rule in `cells/verify/tighten.py` compares the feedback arrival with the
  environment's answer.
- Every rule reads the SDF, which flattens site pins to 25 ps (C-10c), so the
  term `pq.hi − min(pr.lo, pa.lo)` (up to about +0.43 ns) is invisible to
  every gate.

**Likely margin (not measured).**
- `E_τ` contains at least one neighbour LUT, two routed wires and, on the
  request side, the SDELAY chain. That is probably well above `w_hi` (fixture
  feedback 295 ps; prjxray [213, 709] ps) plus 0.43 ns.
- But nothing checks it. Short or RFAST links and a downstream-side answer
  (DACK fast tap) are the cases to look at first.

**Proposed check.** Make it a gate in the audit:
- For every `bd_c2*`, read from FASM which physical pin carries the feedback
  and which carry the inputs. C-11b's fasm2lean already does this.
- Then check `w_hi + site(pq).slow_max ≤ E_τ,min + min site(pr/pa).fast_min`
  with the guardband applied.
- As a cheap structural alternative, LOCK_PINS the feedback to A6 or A5 in
  `cells/rtl/bd_ce.v`. That makes the term non-positive, but it changes a
  frozen cell, so it needs a stated reason and a routed-GLS result.

**Effort to finish.**
- A full `PipeTimed` instantiation through `PinLut`, deriving every phase's
  `exSel` edges from `sel_phase` and feeding `pinlut_fifo_of_edges`: about
  half a day. It is bookkeeping parallel to `pipe_ctl`; no new idea.
- A generic-LUT version ("different-pin changes separated by more than the
  spread ⇒ FIFO"): about half a day.
- The GLS-with-per-pin-arcs FIFO claim (section 1, row 3): about 2 h, by
  adapting A's `gsaf`.

**What it buys.**
- The one physical assumption that the timed pipe rests on is reduced to:
  - an inequality that a tool can check from FASM plus prjxray (item 3);
  - plus the single-mux static-hazard question already isolated in
    B-muxtree-fidelity (item 2).
- It also shows that the current GLS cannot test the assumption, and what the
  GLS would need in order to test it.

## Fidelity per primitive

- **Controller LUT (`bd_c2n`)**:
  - Real INIT `0x00B2…` via `CElemTiming.exc`/`lutB`, with binary pins.
  - The per-pin model is a FIFO map per pin into a zero-time function at the
    selects, then one FIFO output map. It is more faithful than 6e's lumped
    read: it is the prjxray split (site-pin delay per pin, then one cell arc),
    the same as C-10b's `gate_window`.
  - Not modelled: per-level mux delays inside the tree (H_TREE_FIFO lumps
    them), and analog runts or charge sharing.
  - No X and no metastability: the pins are clean protocol signals here.
- **Feedback wire**: 5b's window channel. In the counterexample it is a fixed
  1-tick delay (`ce_fb`).
- **GLS LUT**: A's SAF, one `d` per LUT. It is used only to show what the GLS
  can and cannot exhibit.
- **Time**: ℕ ticks. In the counterexample, 1 tick ≈ 0.085 ns is only an
  illustrative scale; the witness is not a route.

## What did not work / not done

- The involution corollaries were not re-proved. They need Mathlib's ℝ, and
  A's `cancel_iff`, `up_bounds` and `down_bounds` already are the statements.
- No complete multi-phase per-pin theorem: `sel_phase` is one phase, and
  `pinlut_fifo_of_edges` takes the phase sequences as hypotheses (see
  "Effort").
- The LOGIC_OUTS-to-own-output reading in the fixture table is unverified.
- The GLS-with-per-pin-arcs claim is a sketch only.
