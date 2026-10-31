# B-zero-delay-refine (probe Bzd): physical cell traces to C's zero-delay traces

File: `formal/lean/Formal/Cells/ZeroDelayRefine.lean` (core Lean, checks with
`/tmp/claude-0/btools/bcheck.py Formal/Cells/ZeroDelayRefine.lean`; axioms: propext,
Classical.choice, Quot.sound at most; `steer_unsel_never` uses none).

This is the cell-level half of bridge **Br2** (C's 8x, which exists only as `Wip/C8x`). C's
capstone `H_BUNDLE` is `Ops.Held` on zero-delay traces (Nat ticks, Bool wires, the gate fields
of `Ops.Link.Link`, `Ops.Steer.Steer`, `Ops.Mux.Mux`). C's definitions are imported, not restated.

## The refinement notion (all named in the file)

- **Event window** `Ev = [lo, hi]`: the wire is surely old before `lo` and surely new from `hi`.
  Inside the window it may glitch or be X. This is the definite-window convention of LinkExact,
  LibGapSteer and LibGapMux.
- **Monotone retiming** `Mono`: each event gets an abstract step. If an event surely precedes
  another physically (`e.hi < e'.lo`), it gets the earlier step.
- **Window image** `WinImg p lo hi T0 er ef`: between its event windows the physical wire is
  definite and equal to the abstract one-token wire `tokA kr kf`. The high phase is nonempty.
- **Data**: the abstract bus carries the token value for the whole transaction, so `Held`
  holds on it. The physical side is related **at capture**: the latch output equals `v` from its
  capture on (`Capt`, `Spec.out`). It is not related sample by sample (see "Is C's predicate an
  image" below).

## Results

| cell | theorem | assumed | proved |
|---|---|---|---|
| bd_link stage (bd_c2n + bd_latch) | `link_refines` | `Wf`, the six `bd_link.stage` rows (`LinkExact.Conj`), `Causal`, any `Beh` | explicit run `lI/lO/lC` meets C's `Link`, `Protocol` ×2, `Held` ×2; physical `LinkRef` (Mono, images of req_in / ack_out / node, `Capt`, `out`); abstract latch = `vN v` |
| | `link_ref_iff` | `Wf`, `Split`, `Causal` | every behaviour refines **iff** `Conj` (exact) |
| | `link_ref_breaks i` | row `i` violated by 1 tick (`Pv i`), Wf/Split/Causal met | some behaviour has no `LinkRef` |
| | `link_witness` | P0 | hypotheses jointly satisfiable, a behaviour refines |
| bd_steer | `steer_refines` | `bundled_s_setup/_hold` for both outputs (read-map form), `H_REQ_WIDTH`, `H_ACK_WIDTH`, `H_UNSEL_ACK`, delays ≥ 0, `SCausal` | explicit run meets C's `Steer`, `Protocol` ×3, `Held` ×3; physical `SteerRef` (incl. the `uack` OR at its real INIT) |
| | `steer_unsel_never` | any C `Steer` run whose select reads `v` while req is high | unselected branch never requests (holds under every retiming) |
| | `steer_setup_breaks`, `steer_hold_breaks` | LibGapSteer's `spurious_token` / `late_hold_glitch` runs | no `SteerRef`, so no refinement under any retiming |
| | `steer_witness` | concrete numbers | all hypotheses hold |
| bd_mux join (y selected, x waiting) | `mux_refines` | `bundled_s_setup/_hold` for uj0 and uj1, `H_JOIN_RACE`, env pulses, delays ≥ 0, loops ≥ 1, H_RESET, `MCausal` | explicit run meets C's whole `Mux`, `Protocol` ×4, `Held` ×4; physical `MuxRef` (uj1 a window token, uj0 ≡ 0) |
| | `mux_unsel_never` | any C `Mux` run whose select token reads 1 while ctl is high | `j0` never fires |
| | `mux_setup_breaks` | `wrong_branch_latched` run (exists via `run_luteq`) | uj0 is 1 from 1300, so no refinement under any retiming |
| | `mux_hold_breaks` | hold violated by 500 ps, setup and race met | every uj1 trace is 0 at 2800, inside the forced-high phase `[1300, 3300)` |
| | `mux_witness` | concrete numbers, traces built by `run_luteq` | all hypotheses hold, a `MuxRef` exists |

### Which timing conditions are needed

- **Cell rows** (cell_constraints): `bd_link.stage` (all six, exact: `link_ref_iff`);
  `bd_steer.bundled_s_setup/_hold`; `bd_mux.bundled_s_setup/_hold` (both joins). One mux
  condition, `H_JOIN_RACE: max(Yr1+pr.hi, Cr+pc.hi) + pq.hi ≤ min(Yf+pr.lo, Cf+pc.lo)`, is the
  selected join's own-feedback race. It is the read-map form of `bd_mux.uj_env_latency_*`, which
  the JSON lists as sufficient only. Here it is used as a sufficient condition; necessity is not
  proved.
- **Not cell rows**, named and needed only for monotonicity: `Causal`, `SCausal`, `MCausal`.
  They say the environment does not surely answer before the cell could have spoken, e.g.
  `U0 ≤ Rb1`, `U0 ≤ Fa1`, `V0 ≤ Fb1` for the link. These are exactly the `Mono` obligations of
  the chosen schedule. Every closed loop with nonnegative wire delays should meet them, but that
  is the network half and is not proved here. The six `Pv i` meet `Causal` (`Pv_causal`), so in
  `link_ref_breaks` it is the cell row that fails, not `Causal`.
- Width hypotheses `H_REQ_WIDTH` / `H_ACK_WIDTH` (steer): a pulse longer than its read skew. Without
  them the image's high phase may be empty.

## Is C's zero-delay predicate an image at all?

- **Handshake fields: yes.** Every C gate field is "moves only to the value of the previous tick".
  DI wires may lag independently: `i.ack` and `o.req` may move at the same or different steps.
  No field demands simultaneity, and the explicit runs above are images.
- **Data fields: only in the captured-value sense.** `H_LATCH_OPEN` (`c t → o.dat t = i.dat t`),
  `Steer.dat`, `Mux.dat` and `Join.dat` equate buses at one tick. Physically the latch output
  reaches `v` only at `max(U1 + pe.hi, Td + pd.hi)`. Under `Conj` that can be after the node opens
  and even after `V0` (`H_SETUP_DATA` allows `Td + Dhi` up to `V0 + Elo - Fhi`). So
  `o.dat = i.dat` sampled at the physical instants of the open phase is not an image in general.
  This argument is **not mechanised**; no Lean counter-behaviour is built for it.
- **Weakest predicate that works (proposal):** keep C's handshake fields. Read the data fields as
  "the abstract bus is the value captured downstream", which is what `LinkRef.capt/out` gives. In
  Lean terms the cell half needs no change to C's definitions. The obligation moves to the network
  half: the downstream capture of this cell's output equals this cell's abstract `o.dat`.

## NOT covered

- the network half (per-cell retimings consistent across wires; Br3 / `Bridge*`);
- more than one token;
- the link's own output wires `ack_in` / `req_out` (definite intervals: `LinkExact.rout_definite`;
  cleanliness: `H_ROUT`);
- the mux's `zr`, `xa`, `ya`, `ca` nodes (abstract only here);
- x selected (symmetric, not written);
- a link refinement that places the node's edges outside `[U0, U1]`, `[V0, V1]`;
- the retiming-independence of `mux_hold_breaks` (argued, not proved: the uj1 fall surely
  precedes `ctl_req↓`);
- correlated corners (box form only).
