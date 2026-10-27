# B probe 7e: the handover-ordering claim and the A0 hold (bd_arb.v)

File: `formal/lean/Formal/Cells/ArbHandover.lean` (core Lean, imports only
`Formal.Cells.Prelim`). Checks clean in about 5 s. No `sorry`/`admit`/`axiom`,
and no compiled evaluation. Kernel `decide +kernel` is used for the finite
checks. `#print axioms` on every main theorem gives a subset of
`propext, Classical.choice, Quot.sound`.

Check command:

    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/ArbHandover.lean

Shared definitions: none were added to Prelim. Everything is local to the file:
`LutOut3`, `Arcs`, `Cell`, `countTrue`, `St`, `Gate`, `Reach`.

## Audit correction (claude/audit REPORT rows 10, 21, 24; 2026-10-27)

- **Corner mix.** The arcs used for every number in Part 1 (O6 56/124, O5 I2
  52/150, O5 I0 55/152, from `cells/sim/bd_prims_sim.v`) were read as
  rise/fall. They are prjxray's FAST_MAX and SLOW_MAX of ONE arc
  (`prjxray/utils/makesdf.py:63` writes `(FAST_MIN::FAST_MAX)(SLOW_MIN::SLOW_MAX)`,
  each for both edges; prjxray has no edge split). The general theorems
  (`overlap_duration_r2_to_r1`, the skew theorems, any `Arcs`) stand. The
  numeric instances `header_16ps`, `header_routed`, `header_r1_to_r2`,
  `sim_overlap`, `prj_overlap_caps` (16 ps, w ≥ 16, 28 + w, 16 − R, 72/94 ps)
  and ARBITER.md's "+68 ps" (= 124 − 56) mix corners
  (`ArbCorners.prjArcs_is_mix`, `simArcs_is_mix`, `mix_header_16`). They are
  exact only in the simulator's (mixed) arc model. Corrected (B-arb-corners.md
  §1): overlap `max 0 (d6 − o5q − w)` = **0 at every consistent corner, every
  w ≥ 0** (`ArbCorners.overlap_C`, `corner_no_overlap`, `slow_header`,
  `fast_header`; `sim_overlap_C` for the simulator); an overlap needs an
  unmeasured asymmetry larger than a whole O5 arc (`header_needs_asym`);
  reverse margin 96 + w (SLOW_MAX) / 46 + w (FAST_MIN) (`r1_to_r2_margins`);
  skew caps 0/26 ps (SLOW_MAX), 3/0 ps (FAST_MIN) (`caps_are`), box 82/105
  (`box_caps`). Corrected values are inlined below; withdrawn ones are in
  brackets.
- **Scope of `held_protocol`.** Part 2 is speed-independent with ZERO wire
  delay, so the A0 fork is isochronic. With wire delay the property depends on
  the A0-fork ordering (H_A0_FORK, `ArbA0Fork.no_early_ack_iff`,
  `TernaryPhases.arb_a0_fall_skewed_early_ack`).

## Verdict

**Works.** (1) The header's 16 ps arc claim is proved exactly in the
simulator's arc model (corner-mixed; 0 ps at any consistent corner, see the
audit correction), in both directions, and extended to arbitrary request-fork
skew, where it gives a cap.
(2) The unheld protocol violation is reproduced as a reachable trace. The held
INIT is proved to meet the merge's counting precondition in every interleaving
of a zero-wire-delay model (A0 fork isochronic).
(3) The same exhaustive model also shows that two of the header's claims are
stronger than the hold supports without timing:
- grant exclusion during handover
- "A1 falls before q flips"

Both are reachable in the untimed model. They are relative-timing facts with
the margin of a server round trip, not structural ones.

Effort to finish (see "Missing"): about 1-2 days.
- Put fork wires into Part 2 (QDI check).
- Prove the two relative-timing conditions RT1 and RT2 in Part 1's channel.
- Port `LutOut3` onto shard A's Core delay channels.

What it buys the project:
- The tier table in ARBITER.md gets a proof-backed correction.
- tb_arb's threshold gets an exact value in the simulator's arc model (16 ps,
  not 56). [At a consistent corner there is no threshold: 0 ps for every R,
  `ArbCorners.sim_overlap_C`.]
- The structural-overlap cap (72/94 ps for any skew, corner-mixed; 26/3 ps at
  SLOW_MAX/FAST_MIN, 82/105 in the box, `ArbCorners.caps_are`, `box_caps`) is
  proved, which closes the structural explanation of the unexplained 8% under
  this channel model.

## Part 1: timed, bare `bd_arbcell` (one isolated handover)

### Model

Time is `ℤ` picoseconds. Each LUT output uses the **rise-fast asymmetric
pure-delay channel** `LutOut3`:

    o t = f(pins delayed by their rise arcs) || f(pins delayed by their fall arcs)

This needs rise ≤ fall per pin (`H_rise_le_fall`). For an isolated edge, the
output rises exactly `dr` and falls exactly `df` after the input edge, which is
what `bd_prims_sim.v`'s `specify` paths do. High pulses are stretched by
`df - dr`, which is ARBITER.md's "+68 ps". [That 68 = 124 − 56 is SLOW_MAX −
FAST_MAX of one O6 arc (makesdf.py:63), not a measured rise/fall asymmetry;
the asymmetry is the unmeasured `ArbCorners.RF` (H_RF_ASYM).]

The functions are the real INITs through `lutB`/`o5B`/`o6B`:
- `stateF` uses `bd_c2n_set` 0xFFB2…
- `g1F`/`g2F` use `ugrant` 0x0C0C0C0CA0A0A0A0.

Lemmas `stateF_eqn`, `g1F_eqn` and `g2F_eqn` prove them equal to
C(r1,~r2), r1.q and r2.~q.

### Named hypotheses (`Arcs`)

| field | meaning |
| --- | --- |
| `qr`, `qf` | state LUT O6 rise/fall arcs |
| `w` | q routing to ugrant's I2 |
| `wfb` | q routing back to its own I2 (does not appear in results) |
| `g1r_q`, `g1f_q` | O5 arcs from pin I2 |
| `g1r_r1`, `g1f_r1` | O5 arcs from pin I0 |
| `g2r`, `g2f` | O6 arcs, flat over pins |
| `H_nonneg` | every arc and wire is non-negative |
| `H_rise_le_fall` | rise ≤ fall on every arc |

Scenario hypotheses:
- `H_r1`/`H_r2`: the waiting request stays high and the holder drops at `t0`.
- `H_init`: q was settled in the holder's favour before `t0`.
- `H_REQ_ISO`: both LUTs read the same request trace. It is dropped in the
  skew theorems.

To test the arcs on GLS, read the routed SDF arcs per copy. On the board, they
cannot be measured directly.

### Theorems

- `q_rises`, `g1_rises`, `g2_falls`: the exact edge times in the r2→r1
  handover. g2 falls through its **r2 pin**, not through q.
- **`overlap_r2_to_r1`**: both grants are high at t iff
  `t0 + qr + w + g1r_q ≤ t < t0 + g2f`.
- **`overlap_duration_r2_to_r1`**: the number of ps with both grants high is
  `max 0 (g2f − (qr + w + g1r_q))`. This is exactly the brief's formula.
- **`overlap_exists_r2_to_r1`**: if the deficit is positive, both grants are
  high at the instant g1 rises.
- **`no_overlap_r2_to_r1`**: if `qr + w + g1r_q ≥ g2f`, there is never an
  overlap.
- `q_falls` and **`overlap_r1_to_r2`**: the other direction. The overlap is
  `[t0+qf+w+g2r, t0+g1f_r1)`, under `H_g1_by_r1`, which says g1 is lowered
  by r1 and not by q.
- **`header_16ps`**: with the bd_prims_sim arcs (56, 52, 124: FAST_MAX
  "rises" against a SLOW_MAX "fall") and w = 0, the overlap is exactly
  `[t0+108, t0+124)`, which is 16 ps. Corrected: 0 ps at every consistent
  corner (`ArbCorners.slow_header`, `fast_header`).
- **`header_routed`**: with w ≥ 16 ps there is no overlap (consistent corner:
  every w ≥ 0, `ArbCorners.corner_no_overlap`).
- **`header_r1_to_r2`**: the reverse direction never overlaps, for any w ≥ 0.
  The margin is 180 + w − 152 = 28 + w ps (corner-mixed; 96 + w SLOW_MAX,
  46 + w FAST_MIN, `ArbCorners.r1_to_r2_margins`; in the box only a bound
  `max 0 (62 − w)` on an overlap, `box_r1_to_r2_le`).
- **`sim_overlap`**: the simulator's `BD_ROUTE_PS = R` adds R to every arc,
  so the overlap is `max 0 (16 − R)` ps (corner-mixed; 0 for every R with
  consistent arcs, `ArbCorners.sim_overlap_C`).
- **`overlap_skew_r2_to_r1`/`_le`, `overlap_skew_r1_to_r2`/`_le`**: the
  request reaches the grant LUT σ after the state LUT, with σ of either sign.
  - r2→r1: the overlap is `[t0+qr+w+g1r_q, t0+min(σ, qr+w)+g2f)`.
  - r1→r2: the overlap is `[t0+qf+w+g2r, t0+min(σ+g1f_r1, qf+w+g1f_q))`.
  - For every σ and w, the duration is at most `max 0 (g2f − g1r_q)` (r2→r1)
    or `max 0 (g1f_q − g2r)` (r1→r2).
- **`prj_overlap_caps`**: those caps are 72 ps and 94 ps for the bd_prims_sim
  (corner-mixed) arcs. Corrected: 0/26 ps at SLOW_MAX, 3/0 ps at FAST_MIN
  (`ArbCorners.corner_caps`, `caps_are`), 82/105 ps in the box (`box_caps`).

## Part 2: untimed `bd_arbiter`, every interleaving

### The unheld INIT

The unheld INIT is **0xFFB2FFB2ACACACAC**. It is `ARB_STATE_R0` in
`cells/verify/inits.py`, computed there from O6 = rst + maj(r1, ~r2, q) and
O5 = r1.q + r2.~q. It never appeared in the RTL history: commit 1b81a36
introduced the held constant directly.

Lemmas:
- `unheld_q_eqn`: the unheld INIT ignores A0.
- `held_q_eqn`: q = rst + (A0 ? q : C(r1,~r2)).
- `r0_eqn`: R0 = r1.q + r2.~q for both INITs.
- `c2_eqn`: the ack C-element equation.
- `reset_values`: rst forces q = 1 and A = 0.

### Model

Speed-independent (SI) interleaving: unbounded gate delays and zero wire
delays.
- Each of q, R0, g1, g2, A1 and A2 is its own gate. The O5 and O6 outputs of
  one LUT6_2 are independent gates. Each evaluates the real INIT on the
  current wires.
- Server: A0 follows R0.
- Client i: r_i follows ¬A_i (always hungry).

Monitors:
- `c` (credit): set when A0 rises, cleared when an ack rises.
- `z`: set when R0 falls, cleared when an ack rises.

`okTrans`:
- an ack may rise only if `c ∧ z`;
- A0 may rise only if `¬c`.

The exhaustive check is an inductive invariant. It is a literal bitmask of the
112 reachable states, computed outside Lean and not trusted. `held_closed`
proves it closed under every enabled transition (`decide +kernel` over 2048
encodings × 9 gates), and `held_inv` proves it contains reset.

### Theorems

- **`held_protocol`**: with the held INIT, every enabled transition from every
  reachable state satisfies `okTrans`. Three consequences:
  - Client acks and server transactions alternate one for one.
  - An ack never rises unless R0 has returned to zero since the previous ack.
  - A0 never re-rises before its transaction is delivered.
- **`held_no_phantom_ack`**: A2 cannot rise while A0 is still high from a
  delivered transaction, such as client 1's.
- **`held_live`**: no reachable deadlock.
- **`unheld_violation`/`unheld_not_protocol`**: the header's trace is reachable
  with the unheld INIT:

      r1↑ R0↑ g1↑ A0↑ A1↑ r1↓ r2↑ q↓ g2↑

  Then A2 is excited with A0 high, `c = 0`, `z = 0` and R0 still high. The
  ack fires against no server transaction, and R0 never returned to zero.
- **`held_grant_overlap_untimed`**: g1 and g2 are both high in a reachable
  state of the HELD arbiter:

      r1↑ R0↑ g1↑ A0↑ A1↑ r1↓ R0↓ A0↓ r2↑ q↓ g2↑

  g1's own fall is still pending. R0 is computed from r1, r2 and q, not from
  the grants, so R0 can fall, the server can drop A0, the hold can release
  and g2 can rise before g1 falls.
- **`held_ack_overlap_untimed`**: A1 and A2 are both high in a reachable
  state. A1's pending fall is overtaken by the next A0 rise. This is not a
  phantom ack, because `held_protocol` still holds.
- **`held_q_runt`**: q is excited and then withdrawn by r1 rising one step
  after r2. This is the arbitration race, which is the metastability tier.
- **`held_a1_runt`**: A1's pending fall is withdrawn by A0 rising.

A Python BFS (not in the repo) found that the held design's non-persistent
gates are exactly q (disabled by r1/r2) and A1/A2 (disabled by A0). R0 has no
hazard. In the unheld design, R0 and A0 are also non-persistent.

### Timing assumptions the interleaving model hides

1. **Isochronic forks and zero wire delay.** This covers:
   - q to its own I2, to ugrant and to R0 (inside the LUT);
   - r1/r2 to ustate and ugrant;
   - A0 to ustate I4, ua1 and ua2;
   - g1/g2 to the C-elements.

   Shard B's ArbKleene probe shows the A0 fork matters (`H_A0_FORK`).
2. **Atomic, hazard-free gates.** An input edge that does not change a LUT's
   function produces no glitch (the Kleene/mux-tree lemma). A transition that
   starts always completes: no runts and no metastability. Where this fails
   is exactly the non-persistence found above.
3. **Fundamental mode inside each feedback LUT.** The output re-reaches its
   own pin before anything else changes, because the feedback wire is
   modelled as zero.
4. **Atomic four-phase environment.** The server and clients react
   atomically.

The stronger properties additionally need two relative-timing conditions,
which are not proved here:
- **RT1, grant exclusion in bd_arbiter.** The r1→g1 fall (O5 arc, 152 at
  SLOW_MAX, plus routing) must beat the chain r1→R0 fall (152), then the
  server's A0 fall, then A0→q (124 at SLOW_MAX), then q→g2 rise (124 at
  SLOW_MAX) plus routing. [The original "124 or 56", "rise (56)" mixed
  corners; see ArbCorners §2.] The margin is
  at least a server response plus two arcs.
- **RT2, ack exclusion.** A1's fall after A0 falls (124 plus routing) must beat
  the chain A0↓→q→g2/R0↑→server→A0↑.

## Comparison with ARBITER.md's measured numbers

(All numbers in this section are in the simulator's corner-mixed arc model,
which is what tb_arb and tb_arb_overlap run on; they are not silicon
predictions. At a consistent corner the bare-cell overlap is 0.)

**tb_arb** (1 overlap at BD_ROUTE_PS = 0, 0 at 354). This matches
`sim_overlap`: a single r2→r1 handover gives 16 ps at R = 0 and none for
R ≥ 16. The bench gates on R ≥ 56 and tb_arb_overlap on R ≥ 50. The exact
boundary is 16 in the sim's uniform-R model. A checkable prediction: R = 8
gives 8 ps, and R = 16 gives 0. The header's "about twenty times the margin"
is 354/16 ≈ 22.

**tb_arb_overlap** (89 overlaps arc-only, 0 routed). Each isolated r2→r1
handover is 16 ps. That is below the W = 1 passband (≤ 80 ps rejected), which
is consistent with "one link removes every instance".
- The model does not count how many of the 89 are isolated handovers. With
  free-running stimuli, some are non-isolated edges, and the single-edge
  channel does not cover those.
- It does prove that no isolated r1→r2 handover overlaps at any routing.

**Hardware, bare cell.**
- **RAW fired 139/192.** With isochronic requests and any real q routing
  (w ≥ 16 ps), the model predicts no overlap. RAW firing therefore needs
  request-fork skew σ > w − 16, or non-isolated edges. The skew theorems allow
  that.
- **FILTERED fired 15/192, unexplained.** The skew theorems cap every isolated
  handover's overlap at 72 or 94 ps (corner-mixed arcs; 26/3 ps at a consistent
  corner, 82/105 ps in the box), for every skew and every routing.
  Assuming, not proving here, that the detector AND adds a +68 ps stretch, the
  raw pulse is at most about 162 ps. That is below the 203 ps minimum
  threshold of the W = 2 filter. [The +68 ps (= 124 − 56) is SLOW_MAX −
  FAST_MAX of one O6 arc (prjxray makesdf.py:63), a corner mix, not a
  rise/fall stretch. At one consistent corner this channel adds no stretch
  (rise = fall), so the bound is the cap itself; the box's stretch would be
  at most SLOW_MAX − FAST_MIN = 124 − 45 = 79 ps, about 105 + 79 = 184 ps,
  still below 203 (arithmetic, not proved). Consistent-corner caps:
  `ArbCorners.caps_are`, `box_caps`; per routed seed, B-arb-corners-pin.md.]
- **What this means for the 8%.** Within this channel model, the structural
  handover mechanism **cannot** produce the 15 filtered copies. This confirms
  ARBITER.md's "predicts no copy should ever fire", and it holds for all skews
  rather than only at zero skew. The 8% must come from outside the model:
  - non-isolated or runt edges (oscillator periods are 2.9 and 3.8 ns, so
    `held_q_runt`-type races happen constantly);
  - per-pin O6 arcs that prjxray does not characterise (the A5 lead);
  - analog behaviour.

  The model does **not** explain the 8%. It removes the digital-overlap
  explanation, conditional on `H_rise_le_fall`, flat O6 arcs and the OR
  channel.

**hw/arb_prot** (viol 0/96, ovl 0/96).
- `held_protocol` explains why there are no phantom acks (in the
  zero-wire-delay model; with wires it also needs H_A0_FORK).
- `held_ack_overlap_untimed` shows that A1.A2 is reachable in the held design
  without timing. So `viol` is **not** an exclusive signature of the protocol
  defect, contrary to ARBITER.md: in the held design it would also fire if
  RT2 failed. A 0/96 reading is evidence for RT2 as well.
- Likewise, ovl 0/96 depends on RT1 and is not structural.

**The header's prose.**
- "A1 falls, client 1 completes — and only then does q flip": q waits only for
  A0↓, not A1↓, so the order of A1↓ and q is RT2.
- "During handover structural WITH THE HOLD": this is relative timing, with a
  server round trip of margin (RT1). It is not SI-structural.

## Fidelity per primitive

- **LUT function**: exact. The real INIT is used via `lutB`/`o5B`/`o6B`, with
  the RTL pin maps and the constant pins tied as in the RTL.
- **LUT timing (Part 1)**: rise-fast pure-delay channel with per-pin O5 arcs
  and flat O6 arcs (the numeric instances use bd_prims_sim's corner-mixed
  pairs; prjxray itself gives one value per corner for both edges). Exact for isolated single-pin edges. For pulses
  it is transport/stretching with no inertial rejection, unlike iverilog's
  default inertial specify. No glitch or Kleene behaviour is modelled, since
  every LUT here sees only function-irrelevant extra edges. Per-pin O6 arcs
  are assumed flat, because prjxray does not characterise them.
- **LUT timing (Part 2)**: unbounded, atomic, hazard-free gate (SI).
- **Routing**: Part 1 uses pure delays: `w`, `wfb`, and σ in the skew
  theorems. Other request wires are folded into `t0`. Part 2 has no wires,
  which is the isochronic-fork assumption.
- **C-element / state node**: a LUT whose output feeds back to its own pin.
  In Part 1 the feedback is a wire `wfb`, and the state LUT is the same
  channel as the others. In Part 2 the feedback is zero-delay.
- **Fractured LUT6_2**: O5 and O6 are separate channels or gates sharing
  inputs. Their shared mux tree, and any correlation between them, is not
  modelled.
- **Metastability**: absent by construction in both models. Part 2 locates it
  as the non-persistence of q.

## Missing / unproved

- RT1 and RT2 are not proved in a timed model of the full bd_arbiter with a
  server. This is the natural next step, using Part 1's channel and a bounded
  server delay.
- No QDI check with explicit fork wires, so which forks must be isochronic is
  not established.
- The detector LUT's +68 ps stretch is not proved here (it would be one more
  `LutOut3` lemma). [68 is the corner mix SLOW_MAX − FAST_MAX; at a
  consistent corner the stretch is 0.]
- Non-isolated or multi-edge behaviour of the channel, and the free-running
  regime of tb_arb_overlap, are not modelled.
- Not yet ported to shard A's `Formal/Core` channels.
