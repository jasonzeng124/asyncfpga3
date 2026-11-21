# B probe Bng: which channels give H_NO_REVERT, and what a LUT needs for it

Shard B, 2026-10-27. Lean: `formal/lean/Formal/Cells/NoRevert.lean`, core Lean only.
Check: `scratchpad/bchk.sh formal/lean/Formal/Cells/NoRevert.lean` prints `[bchk] OK`.
`#print axioms` for every theorem below is a subset of `[propext, Classical.choice, Quot.sound]`.
There is no sorry, admit, axiom or native_decide.

Context: Bw/Bex (`B-win-fifo.md`, `B-win-fifo-causal.md`) showed that under the spacing
(H_SPREAD_PULSE) B's FIFO hypothesis is equivalent to `Win` + **H_NO_REVERT**: inside one input
edge's uncertainty zone, once the output shows the new value it keeps it. H_NO_REVERT has a zone
form, `WinFifo.NoRevert`, and an intrinsic form, `WinFifoCausal.NoRevertI`.

## 1. Delay channels

| channel | gives H_NO_REVERT? | theorem |
|---|---|---|
| B's inertial `CElemTiming.Inertial d` | **yes, for every input** (`NoRevertI d hi`, any `hi`; no spacing needed) | `inertial_noRevertI` |
| Core's inertial `TraceDiscrete.inertial (d-1)`, one tick late (PrelimCore's relation) | yes, for every input | `coreInertial_noRevertI` |
| fixed transport `Transport d` | yes, for every input, band `[d, d]` | `transport_noRevertI` |
| fixed transport `d` read in a band `[lo, hi] ∋ d` | yes on a clean input with H_SPREAD_PULSE | `transport_ret`, `transport_noRevert` |
| same, without the spacing | **no**: `Transport 2` violates `NoRevertI 0 2` when an input pulse sits just before the held interval | `transport_band_needs_spread` |
| FIFO `PipeTimed.Ret` | yes on a clean spaced input (Bw/Bex) | `no_revert_of_ret`, `noRevertI_of_ret` |
| Core's bounded transport `TraceDiscrete.Transport lo hi` (monotone warp) | it is a `Ret` with the same band, so yes on a clean spaced input | `coreTransport_ret`, `coreTransport_noRevert` |
| event channel (one surviving, ordered output event per input edge, inside its zone) | yes under H_SPREAD_PULSE | `EventCh`, `eventCh_noRevert` |
| involution channel, discrete event abstraction `invTimes` (`o(j+1) = c(j+1) + δ(c(j+1) - o j)`) | under **H_INV_BAND** (every occurring delay lies in `[lo, hi]`) and H_SPREAD_PULSE, no transition cancels and each is in its zone, so it is an `EventCh` and gives H_NO_REVERT | `invTimes_eventCh` |
| window `Win lo hi`, `hi ≥ lo + 2` | **no**, even on a clean input with ONE edge (every spacing holds) | `win_not_noRevert` |
| C's `Net.BoundedDelay lo hi`, `hi ≥ lo + 2` | **no**: the same glitch trace `1, 0, 1` satisfies both its `cause` and its `settle` field | `bdelay_glitch`, `bdelay_not_noRevert` |

Non-vacuity:
- `transport_witness`: Bw's witness (edges 0, 200, 500, …, a 100-tick delay, band `[45, 124]`) is a
  fixed transport, an `EventCh`, and the constant-delay involution channel. All hypotheses are met.
- `PrelimCore.inertial_of_core` gives an `Inertial d` behaviour of every input.

Involution caveat: A's real-valued channel (`Core/Delay/Involution.lean`) needs Mathlib, which is not
built (`pgrep` shows setup's `lake build` still running). The step "A's channel without cancellation
equals `invTimes`, with H_INV_BAND given by A's `up_bounds`/`down_bounds` and no-cancel from A's
`cancel_iff`" is argued on paper, not checked. (A's `cancel_iff`: transition `n+1` cancels iff
`t(n+1) - o(n) ≤ -δmin`. In `invTimes_eventCh` the scheduled times are strictly increasing, which is
the no-cancel case.)

**Reading.** Every channel whose output is an ordered replay of the input gives H_NO_REVERT:
- transport and FIFO, through `Ret`;
- inertial, which holds or copies;
- involution, through one event per edge.

The two "set-of-allowed-values" channels (`Win`, `BoundedDelay`) do not. They constrain WHICH value
the output shows at each instant, never the ORDER in which values show. Inertial is the only one
that gives it with no input spacing at all.

## 2. The LUT: when can the output revert inside one edge's zone?

The model is A's timed tree `Core.LutTree.PhysTree`:
- per-mux select and data delays;
- per-copy select arrival;
- every node a K3 waveform, where `X` = mid-rail.

A transition `A → B` is **monotone** (`Tree.Mono`) when the waveform is `A…, X…, B…` and never goes
back. For `A ≠ B` this is the K3 form of H_NO_REVERT. `read_mono` shows that every fixed-threshold
binary reading of it (`X` read as a fixed `c`) changes at most once.

| theorem | assumed | proved |
|---|---|---|
| `kleene_revert` | — | **H_SRAM + H_MUX_KLEENE + one moving pin with a monotone `0 → X → 1` select do NOT give H_NO_REVERT.** A one-mux buffer tree meets all three, and its root shows `0, 1, 0, 1` while the select is mid-rail. The reason: with the select at `X` and unequal legs the Kleene mux is `X`, and H_MUX_KLEENE then assumes nothing. The tree violates H_MUX_MONO. |
| A's `PhysTree.sic_glitch_free` (existing) | H_SRAM, H_MUX_KLEENE | Static case: if old and new INIT entries are equal, a single moving pin gives a constant root, for any delays, even mid-rail or ringing. So H_MUX_KLEENE does cover the no-change case. |
| `PhysTree'.root_mono` | H_SRAM; H_MUX_KLEENE; **H_MUX_MONO** (one 2:1 mux: if the Kleene value of its delayed inputs is a monotone `A → B` transition, `A ≠ B`, so is the node); **H_ONE_PIN** (every pin but `i` steady); **H_PIN_MONO** (pin `i`'s select waveform is a monotone `o → nw`, i.e. the input buffer does not revert). Per-mux and per-copy delays are arbitrary integers. | With `A`, `B` the old and new INIT entries, the root is constantly `A` if `A = B`, and a monotone `A → B` transition otherwise. Proof (`claim`): below the pin's level everything is constant; at its level ONE mux with constant legs turns a monotone select into a monotone node (`sel_step`, by cases); above it every select is static, so each node follows one child. |
| `exact_mux_mono`, `root_mono_witness` | — | Non-vacuity. A's exact Kleene timed tree (`exactTree`, pass transistors with transport delays) meets H_MUX_MONO. The exact buffer LUT with `kleene_revert`'s select waveform meets every hypothesis of `root_mono`, with `A ≠ B`. |

**Answer to "does H_MUX_KLEENE plus a single moving pin imply H_NO_REVERT at the root?"**
- **No** (`kleene_revert`), except in the equal-cofactor case (A's `sic_glitch_free`).
- What is missing is exactly ONE per-mux property, H_MUX_MONO. Plus the input buffer's H_PIN_MONO,
  it gives H_NO_REVERT at the root for any tree depth, pin level and delays (`root_mono`).
- This is the same "one 2:1 mux" reduction that `MuxTree.lean` made for H_KLEENE_LUT. A single
  moving pin sensitizes only one mux, with static legs, behind a static pass path. The tree is
  read-once, so there is no reconvergence.

**Physically, where can a revert come from?**
1. **Inside the selected mux (H_MUX_MONO).** The select (and its complement from the same input
   buffer) moves monotonically, and the legs are SRAM-driven and static. The node then sits on a
   divider of two NMOS conductances, each monotone in its gate voltage. So its quasi-static level is
   monotone in the select.
   - Skew between `sel` and `sel_b`:
     - break-before-make: the node floats and holds its value (delay, not revert);
     - make-before-break: the legs fight, giving a mid level (still between the rails, monotone).
   - The output restorer (weak PMOS keeper on the NMOS-tree output) adds positive feedback. It
     sharpens the crossing but cannot reverse a monotone drive.
   - Charge sharing at the switch moves the node toward the newly selected, driven leg.
   - So H_MUX_MONO is credible. There is no transistor model in the repo to check it.
2. **At the input threshold (H_PIN_MONO).** LUT pins have no Schmitt trigger. A slow edge at the pin
   (long route, heavily loaded net) plus crosstalk or supply noise near the threshold can cross it
   more than once. Each extra crossing is a real binary runt, sent through the LUT faithfully.
   - This is the most likely physical violation.
   - It is an input-side effect. In the model, the pin's waveform is then not monotone, so the input
     is not `Clean` and the spacing premise already fails.
   - On-chip internal slews (tens of ps) make it unlikely on buffered 7-series pips. FEASIBILITY
     notes buffered INT pips with monotone RC trees.
3. **Two pins moving within one zone.** This is a function hazard (A's `and_glitch`) and is a real
   revert. It is outside H_NO_REVERT's scope, which is ONE input edge.
   - In WinFifoCausal the LUT is a `Win` channel of the *lumped* excitation. The excitation's edge
     there may be several pin edges, arriving in a skewed order.
   - So H_NO_REVERT on the lumped excitation silently includes "the per-pin order inside one zone
     is hazard-free". That is FifoFidelity's H_SEL_ORDER. **Finding below.**
4. **Crosstalk from an unrelated aggressor** switching near the LUT input or inside the CLB. This is
   not a single-input effect and no model here covers it.

## 3. Grade proposal

**H_NO_REVERT: B** (credible, physically motivated, untested on this silicon), split as:
- **H_MUX_MONO: B.**
  - For: a monotone single-stage pass network with static legs and a keeper.
  - No contrary evidence.
  - Not A: no SPICE or board measurement exists.
- **H_PIN_MONO: B** for nets with on-chip buffered-pip slews. **C-risk** for any slow net: an IOB
  input, a very long route, or a LUT pin driven through many unbuffered stages. This must be
  measured (test T-NR1b).
- **Wire / pip / line FIFO** (H_WIRE_FIFO, H_LINE_FIFO via Bw's bridge): **B**. A buffered
  monotone RC tree is a single-input monotone stage, and the event/transport results above apply.
- The **lumped-excitation** use in `ctl_of_win` / `stage_fifo` is only as good as H_SEL_ORDER for
  the multi-pin excitation edges. Grade it with H_SEL_ORDER (per route), not as B by itself.

## 4. Tests

**T-NR1 (board, the core test).**
- **Setup.** One LUT6 configured as a buffer or inverter of pin `A_k`, with the other five pins tied
  to constants chosen so the two cofactors differ.
- **Drive.** A ring-oscillator or a fabric toggle source, through the pin.
- **Count.** Count output edges with an async ripple counter (FDCE toggle chain, clocked by `O6`).
  Count the source's edges with an identical counter fed from a separate tap of the source net, upstream
  of the LUT pin.
- **Where.**
  - Every `k = 1..6`: A1 is the leaf level, A6 the root mux.
  - Two LUT positions per slice (A and D).
  - At least two clock regions.
- **Pass.** The count difference is ≤ 1 (stop ambiguity) after ≥ 10^9 edges per configuration, at
  room temperature and at the hot/low-VCCINT corner if a supply knob exists.
- **Discriminating power.** An extra full edge doubles the count difference rate. A runt below the
  FF clock's minimum pulse width may escape the counter.
  - So also sample `O6` with a CARRY4 TDC (≈ 15–20 ps taps) triggered on the source edge, and
    histogram the number of `O6` transitions per source edge.
  - Pass: every captured window shows exactly one transition.

**T-NR1b (board, stress the H_PIN_MONO risk).**
- Same as T-NR1, but drive `A_k` from an input IOB with an external RC (rise time 5–50 ns),
  optionally with an aggressor toggling an adjacent route at an unrelated frequency.
- Pass criterion as T-NR1.
- If this fails while T-NR1 passes, the revert lives at the input threshold. That means grade C
  for slow nets, and the flow must bound slews (a check on routed net length/fanout).

**T-NR2 (GLS, the scope of the hypothesis).** GLS cannot test transistors. It can test the premise
that one lumped-excitation edge is one pin edge, or a hazard-free sequence of pin edges.
- In routed GLS of gcd_hw with `GLS_MODEL=fid` (per-pin transport), log for every control LUT
  (`bd_link_ctl`, `bd_c2n`, steer and merge LUTs) its pin events and its output events.
- Pass: in every interval between two consecutive output edges, the pins that moved form a sequence
  whose Kleene value (A's `tableEval` over the moved pins) never yields an `X` at the root followed
  by a return. Equivalently: zero function-hazard events.
- This also checks rule F/H_SEL_ORDER coverage. Output count per input zone must be exactly one.

## Not covered / caveats

- Analog content of H_MUX_MONO and H_PIN_MONO: there is no SPICE model. The reasons in §2 are
  physics arguments, not proofs.
- Involution: discrete abstraction only (Mathlib not built). Cancellation regimes (pulses shorter
  than `δ∞ - δmin`) are excluded by H_SPREAD_PULSE, not analysed.
- Inertial tightness: `lo = d` is what is proved. That `NoRevertI` fails for other bands of an
  inertial channel is not proved.
- `root_mono` is per LUT and needs exactly one moving pin. Two moving pins is A's `and_glitch`
  territory.
- The binary bridge (`read_mono`) assumes a reader with a fixed threshold side for mid-rail. A
  reader whose interpretation of `X` drifts in time is not covered. That is the next stage's
  H_PIN_MONO.

## Finding for the cell owner (not confirmed on a route)

`WinFifoCausal.stage_fifo` treats the `bd_link_ctl` LUT as one `Win` + H_NO_REVERT channel of the
lumped excitation. Physically, one excitation edge can be two pin edges in the same zone:
- the request (or ack) pin;
- the feedback pin I2, which arrives after the node's own edge.

H_NO_REVERT is credible only for a single pin edge (`root_mono`). For a multi-pin zone it holds only
if the arrival order is hazard-free, and A's `and_glitch` shows that the order matters. So the LUT
half of "H_NO_REVERT is the only extra assumption" still carries H_SEL_ORDER (FifoFidelity /
tighten.py rule I, whose I2 omission is already listed in JOURNAL-B) for the per-pin view. The
lumped `stage_fifo` result should cite it.
