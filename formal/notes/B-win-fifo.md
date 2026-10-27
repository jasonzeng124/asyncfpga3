# B probe Bw: does the window channel discharge B's FIFO hypotheses?

Shard B, 2026-10-27. Lean: `formal/lean/Formal/Cells/WinFifo.lean` (core Lean only).
Check: `scratchpad/bchk.sh formal/lean/Formal/Cells/WinFifo.lean` gives `[bchk] OK`.
Axioms of every theorem listed below: a subset of `[propext, Classical.choice, Quot.sound]`.
`uenv1_band` uses none. Addresses contradiction X1 (`out/gcd_hw_hypotheses.md` §7).

## What "FIFO" means in B's files

Every B FIFO hypothesis has the same form, `PipeTimed.Ret`:
- `H_LUT_FIFO`: PipeTimed.Ctl, OpsTimedMux, ContractsTruncCel;
- `H_WIRE_FIFO`: OpsTimed `SteerGates`;
- `H_LINE_FIFO`: OpsTimedMux;
- `H_PIN_FIFO` / `H_TREE_FIFO`: FifoFidelity `PinLut`, ConstraintsSel.

The form is: there is a read-time map `σ`, nondecreasing, with `t - hi ≤ σ t ≤ t - lo`, and
`y t = x (σ t)` for every `t ≥ hi`. A `Ret` may drop a pulse, because `σ` can jump over it. It
can never add an output edge the input did not make, and it can never reorder edges. Shard A's
`Substrate.Win` is exactly B's `CElemTiming.WinDelay` (`win_iff`, by `Iff.rfl`).

## Results

The window channel is written `Win`. Time is in ticks. A clean input has edges `c j`.

| theorem | plain statement | status |
|---|---|---|
| `win_glitch_not_fifo` | For every `lo`, and every `hi ≥ lo + 2`, take an input with ONE edge. It has a `Win lo hi` output that glitches 1, 0, 1, and no FIFO read with `hi' ≤ hi` produces that output. **No input spacing makes `Win` FIFO.** | proved |
| `win_fifo_narrow` | If `hi ≤ lo + 1`, every `Win lo hi` behaviour of every input is a FIFO read with band `[lo, hi]`. With the row above: `Win ⊆ Ret` holds exactly when `hi - lo ≤ 1` tick. At 1 ps ticks no real arc qualifies (O6 is 79 ps wide in the box). | proved, exact |
| `win_settled` | `y = val j` on `[c j + hi, c(j+1) + lo)`. **H_SPREAD_PULSE** (`c j + hi < c(j+1) + lo`) is exactly the condition for this stretch to be nonempty. | proved |
| `win_zone` | Under H_SPREAD_PULSE, inside edge `j`'s zone `[c j + lo, c j + hi)` the output shows only `val(j-1)` or `val j`. Nothing older or newer shows up, so no edge overtakes another. | proved |
| `win_swallow`, `swallow_witness` | Exactness. Take a pulse of width `w` with `1 ≤ w ≤ hi - lo`. The constant output is a `Win` behaviour of it, so the pulse is swallowed. Witness: `[45, 124]`, 79-tick pulse. | proved |
| `win_fifo_of_one_edge` | **H_ONE_EDGE**: one output edge `e j` inside each zone, the output stepping from `val(j-1)` to `val j`. `Win`, a clean input, H_SPREAD_PULSE and H_ONE_EDGE together give a `Ret` with band `[lo, hi]`. | proved |
| `win_fifo_of_no_revert` | **The bridge.** **H_NO_REVERT**: inside each zone, once the output shows the new value it keeps it until the zone ends. `Win`, a clean input, H_SPREAD_PULSE and H_NO_REVERT give B's FIFO form with band `[lo, hi]`. | proved |
| `no_revert_of_ret` | Converse: under H_SPREAD_PULSE, every FIFO read with band `[lo, hi]` is a `Win` behaviour and satisfies H_NO_REVERT. **So under the spacing, B's FIFO hypothesis is equivalent to `Win` + H_NO_REVERT.** | proved |
| `spread_of_loop` | Two conditions give H_SPREAD_PULSE. **H_LOOP**: the next input edge comes at least `D` after the output edge of the previous one (the four-phase loop). **H_BAND**: `hi < 2·lo + D`, i.e. the spread `hi - lo` is below the minimum phase `lo + D`. | proved |
| `ctl_of_win` | Gives `PipeTimed.Ctl` (`H_LUT_FIFO` with band `[lo, hi]`) from: a `Win` LUT on the excitation; **H_EX_CLEAN** (the excitation has clean edges `c`, as in `pinlut_fifo_of_edges`); H_ONE_EDGE; H_LOOP; H_BAND; Ctl's own H_FB and H_LOOP_POS. Every PipeTimed/PipeTimedN theorem then applies to that run. | proved; no separate witness |
| `steer_wq_of_win`, `Wit.steer_wit` | Gives the steer's `H_WQ` (H_WIRE_FIFO, req → u.I0) from: a `Win` wire; a request that is clean from time 0 (`H_REQ` with `Tr = 0`); H_SPREAD_PULSE; H_NO_REVERT. A witness satisfies all of these. | proved, non-vacuous |
| `Wit.wit`, `Wit.wit_fifo` | Non-vacuity of the bridge. A 100-tick delay of an alternating input with edges at 0, 200, 500, … satisfies `Win 45 124`, H_SPREAD_PULSE and H_NO_REVERT. | proved |

## Numbers (`uenv1_band`, box corner)

The LUT6 O6 arc is prjxray (45::56)(100::124) ps (A-fidelity R5, A-lut-tree). The box reading
takes `lo = 45` (FAST_MIN) and `hi = 124` (SLOW_MAX), so the spread is 79 ps.

The loop comes from B-gcd-routes.md §Step 2, the binding H_SELORD instance `urig.uenv1`,
seed 4. There, E = 440 ps at FAST_MIN. E is the earliest arrival, from the node's own O6 edge,
at a non-feedback mux select. The lumped excitation is read at the pins, so I subtract the
largest FAST_MIN site-pin delay (A1, 172 ps). That gives `D = 268`.

- H_BAND: `124 < 2·45 + 268`. It holds with a 234 ps margin. A spread of 79 is below a minimum
  phase of 313.
- SLOW corner alone (`lo = 100`): the spread is 24 ps.
- The kernel's worst instance has E = 877 ps, so its margin is larger.

**H_BAND is not the binding constraint. H_NO_REVERT is.**

## Which B FIFO hypotheses are now discharged

**Fully discharged from `Win`: none, and none can be** (`win_glitch_not_fifo`).

**Reduced, under the spacing (provably equivalent): every B FIFO hypothesis**, wherever the
channel's input is clean:
- the FIFO hypothesis becomes `Win` + H_NO_REVERT;
- the spacing itself (no swallow, no overtaking) is derived from the protocol by
  `spread_of_loop`.

Instantiated:
- `PipeTimed.Ctl.H_LUT_FIFO` (`ctl_of_win`);
- `OpsTimed.SteerGates.H_WQ` (`steer_wq_of_win`).

Every other `H_WIRE_FIFO`, `H_LINE_FIFO` and `H_LUT_FIFO` field is the same `Ret` form, so the
bridge applies field by field. That application was not written out.

**Not discharged, with reasons:**
- **H_NO_REVERT** (glitch freedom inside one edge's uncertainty zone). It is an inertial-type
  property.
  - A proves inertial filtering is not derivable from `Win`.
  - `win_glitch_not_fifo` shows it is needed even for one isolated edge.
  - Its physical content: a single-input CMOS chain (wire, site pin, LUT arc), given one
    monotone input edge, makes one output edge. Board test: a ring of LUTs never shows an
    extra edge per revolution (PipeTimed's own test).
- **H_EX_CLEAN in `ctl_of_win`.** The excitation's edges are an input of the theorem.
  - In PipeTimed, the excitation is clean because the node is clean (`node_phase`), so the
    closure needs a causal induction (clean up to edge `j` ⇒ H_LOOP for edge `j+1`). That
    induction is not done.
  - The steer's `H_WQ` has no such circularity: its input is the environment's request.
- **`H_TREE_FIFO`.** The select-level excitation is not clean in general. `sel_runt` and
  `ce_not_fifo` are exactly the glitchy case, so the bridge's clean-input premise fails there.
- **Start time.** The bridge needs the input clean from time 0 (for the steer, `Tr = 0`). A
  power-up prefix with junk before `Tr` gives no `Ret` valid from `hi`, which is B's form.
- **Exactness of H_SPREAD_PULSE.** It is proved exact for "every input edge shows on the
  output" (`win_swallow`). It is not claimed necessary for `Ret` given H_NO_REVERT, because
  `Ret` itself may swallow pulses.

## Finding for the cell owner

`FifoFidelity.ret_of_edges` and `pinlut_fifo_of_edges` require `hlo : ∀ j, c j + lo ≤ e j`
with `c 0 = e 0 = 0`. At `j = 0` that forces `lo = 0`. So the per-pin bridge only ever yields
the band `[0 + out.lo, hi + out.hi]`: the select-level lower bound is lost.

`WinFifo.ret_of_zones` asks for the zone bound only for `j ≥ 1`. The same fix would restore
`lo` there.
