# B-necessity4: bd_mux / bdc_muxn latency rows (probe Bnx4)

Shard B, 2026-10-29. All Lean is core-only. Each file checks with
`/tmp/claude-0/btools/bcheck.py` (OK, no warnings). `#print axioms` on every
headline theorem gives propext / Classical.choice / Quot.sound or a subset.
No sorry, admit, native_decide or axiom. Value checks use `decide` or
`decide +kernel`.

- `formal/lean/Formal/Cells/Necessity4Mux.lean`: bd_mux `S_J0_X` / `S_J1_Y`
  (`uj_env_latency_req`). Max-form replacement, its sufficiency, the passing
  run that violates the shipped form, and the counter-run for the max form.
- `formal/lean/Formal/Cells/Necessity4MuxC.lean`: bd_mux `S_J0_C`
  (`uj_env_latency_ctl`). Counter-run at slack 1 against the SHIPPED theorem.
- `formal/lean/Formal/Cells/Necessity4MuxN.lean`: bdc_muxn `S_J_X`
  (`uj_env_latency_req`). Max-form replacement, its sufficiency, and the
  passing run that violates the shipped form.

## Rows in scope

These are the sufficient-only rows of cell_constraints.json for bd_mux and
bdc_muxn. bd_steer has no sufficient-only row: its two rows are already
exact.

- bd_mux: `bundled_z`, `isochronic_forks`, `uj_env_latency_req`,
  `uj_env_latency_ctl`, `uxa_join_latency`, `reset_first`.
- bdc_muxn: `iso_ctl`, `iso_zack`, `bundled_z_data`, `uj_env_latency_req`.
- `bdc_muxn.rtz` is `sufficient+necessary_untimed`, not plain sufficient.

None of these rows is a flush row. The muxn line's `H_FLUSH_STAGE` is the
`bd_delay[FASTFALL].flush_per_stage` row, which is taken as a hypothesis
(`hFL`), and this probe did not touch it.

This probe did the three join env-latency rows. The others are unchanged
(see "Not done").

## Method

The method is the same as Bsx/Bsx2/Bsx3. `Claim s` is the cited theorem with
one field weakened by `s` ticks. Every other hypothesis is kept word for
word, in a copy of the hypothesis structure that has a slack field.

There is one addition for the non-necessity results. "Not necessary" is shown
in the box sense:
- A SUFFICIENT theorem is proved for a weaker replacement condition, over
  every run.
- A parameter point is exhibited where the replacement holds, the shipped
  field fails, and every other field holds.
- A concrete run is given at that point: real INITs, every gate relation for
  all `t`, an open-loop periodic environment that satisfies `MuxCausal` /
  `MN3Causal` for every token.

So at that point EVERY run in the box (all arc windows and partner minimum
latencies as declared) passes, although the shipped field fails. One lucky
slow run would not show this, because the declared minima are part of the
box.

## Table (for the JSON probe)

| row id | old | new | Lean |
|---|---|---|---|
| bd_mux.uj_env_latency_req | sufficient | **sufficient, NOT necessary**. Replace the form by the max form (below), labelled sufficient+necessary_at_boundary (uj0 form; the uj1 form is the symmetric statement, not built) | Necessity4Mux: `staticN_of_static`, `mux_timing_of_staticN`, `mux_ok_staticN` (sufficient), `pass8` + `pass8_values` (not necessary), `claimX0`, `fail10`, `claimX1_false` (max form at boundary) |
| bd_mux.uj_env_latency_ctl | sufficient | **sufficient+necessary_at_boundary** (S_J0_C form; S_J1_C by symmetry, not built) | Necessity4MuxC: `claimC0` (= shipped `mux_ok_static`), `failC8`, `claimC1_false`; `pass7` (non-vacuity next to the boundary) |
| bdc_muxn.uj_env_latency_req | sufficient | **sufficient, NOT necessary**. Replace the form by the max form, labelled sufficient (its boundary is not shown for muxn) | Necessity4MuxN (`Formal.Cells.MuxN3Timed.Nec4`): `staticN_of_static`, `muxn3_timing_of_staticN`, `muxn3_ok_staticN` (sufficient), `pass8` + `pass8_values` (not necessary) |
| bd_mux.bundled_z, isochronic_forks, uxa_join_latency, reset_first; bdc_muxn.iso_ctl, iso_zack, bundled_z_data | sufficient | unchanged | none (see "Not done") |

### The max form (replacement for `uj_env_latency_req`)

bd_mux, uj0 (`MuxStaticN.S_J0_XR` at slack 0):

    Lj0.hi + wj0h ≤ Lj0.lo + max(W0x.lo, W0o.lo + Lor.lo + Dz.lo + Es + Wzx.lo)
                    + Lxa.lo + Wxa.lo + Ex + Wx.lo

For uj1, read W1y, W1o, Wzy, Lya, Wya, Ey, Wy. The z_ack branch uses the
per-branch wire `W0o.lo` (j0 -> uor.I0), not the min `wo`.

bdc_muxn, input i (`MN3StaticN.S_J_XR` at slack 0):

    Lj(i).hi + wjh(i) ≤ Lj(i).lo + max(Wja(i).lo, wo + Lo.lo + Dl + Es + Wza(i).lo)
                        + La(i).lo + Wak(i).lo + Ex + Wx(i).lo

This uses the shipped lower bounds `wo` (over the three inputs) and `Dl`.

In JSON terms, a max on the request side is an OR of two forms. Each join
should become its own row with `combine: any` over two forms that have the
same data path:
- (a) the current form, the j -> ack-C-element branch;
- (b) the request path `Lj.lo + j -> uor/|j wire + uor/|j arc + line + Es +
  z_ack -> ack-C-element wire + La.lo + Wak.lo + Ex + Wx.lo`.

The current row cannot hold this, because its `combine` is `all` over the
uj0 and uj1 forms.

### Which form (audit P8 item 1)

Lean proves the binary `≤` forms. The JSON rows carry the strict `+1`
(CElemStrict, the Kleene X window).

- **Non-necessity results (`pass8`, both cells).** The passing runs satisfy
  the STRICT max form (`1 + 8 + 1 ≤ 10`). They violate the shipped form by 3
  in `≤` form and by 4 in strict form. So "not necessary" holds for both the
  `≤` and the strict reading. The pass itself is proved in the binary model.
- **Boundary results (`fail10`, `failC8`).** These refute the binary `≤`
  form at slack 1 (`lhs = rhs + 1`). The strict form `L + 1 ≤ R` is
  therefore 2 ticks from the refuted point.
- **Unchanged.** As in P8: equality failing under a Kleene X window is
  CElemStrict's generic own-feedback result (`boundary_x`). It is not
  re-proved for these composed paths. The strict form is sufficient because
  it implies `≤`.

## Plain-language statements

**Necessity4Mux (bd_mux `S_J0_X`).**

Assumed: OpsTimedMux's model. LUT arcs are lumped FIFO (`H_LUT_FIFO`), wires
are windows, the FASTFALL = 0 line is FIFO, and the partners are port-level
causal with minimum latencies (`MuxCausal`). The INITs of uj0 / uj1 / uor /
bd_c2 are the real ones.

Proved:
- **Sufficient** (`mux_ok_staticN`). Every run that meets MuxGates, MuxEnv,
  MuxCausal, reset sequencing and `MuxStaticN … 0 0` meets `mux_ok`'s whole
  conclusion. `MuxStaticN … 0 0` is the shipped `MuxStatic` with `S_J0_X` /
  `S_J1_Y` in max form. The conclusion covers both joins, z_req, both acks
  and the order facts. The shipped form implies the max form
  (`staticN_of_static`).
- **Not necessary** (`pass8`). The run `N4.run 8` has unit delays except
  uj0's 8-tick feedback net. Tokens alternate x/y, and the x client and the
  control sender are tight (Ex = 1, Ec = 6, Es = 1). In this run:
  - `S_J0_X` reads `9 ≤ 6` (false);
  - every max-form field holds;
  - the cell meets its full spec.

  The race is live. j0 rises at 22, and its net shows that from 30. x_req is
  low at the join's pin at 31. The return from the node edge to that pin
  takes 9 ticks, because x_ack waits for z_ack. `S_J0_X` counts 5.
- **Max form necessary at the boundary** (`fail10`, `claimX1_false`). In
  `N4.run 10` every hypothesis holds with `S_J0_XR` weakened by 1, and
  `S_J0_XR` itself fails by exactly 1. The conclusion fails:
  - j0 is 0 at 32, inside its token-0 window [22, 35);
  - z_req is 0 at 35, inside [25, 38).

  The max is taken by the z_ack branch (5 > W0x = 1). So the term the shipped
  form omits is the one that is tight here.

NOT covered:
- the uj1 counter-run;
- per-pin LUT arcs. The `Lj0.hi` / `Lj0.lo` pair is kept as the house's
  lumped box. In OpsTimedMux's single-σ LUT model these two would cancel. In
  a per-pin model they are the feedback-pin arc and the release-pin arc.
- an iff over the box. This is one parameter point.

**Necessity4MuxC (bd_mux `S_J0_C`).**

The control return (join -> uor -> line -> server -> z_ack -> control sender
-> ctl_req -> join) is the only path, so the shipped form needs no max.

`claimC1_false`: the SHIPPED `mux_ok_static` with `S_J0_C` weakened by 1 is
false. The run `N5.run 8` is the same family with 6-tick ack wires, a 1-tick
control sender and an 8-tick uj0 net. In it:
- every shipped `MuxStatic` field holds, `S_J0_X` included (`9 ≤ 11`);
- `S_J0_C` fails by exactly 1;
- reset sequencing holds;
- z_req is 0 at 33, inside [25, 40). ctl_req's fall reaches the join at 29,
  while x_req is still high and the net shows j0's rise only from 30, so j0
  has a one-tick runt.

`pass7`: with a 7-tick net, the shipped theorem applies.

NOT covered: the uj1 form, and per-pin arcs.

**Necessity4MuxN (bdc_muxn `S_J_X`).**

Proved:
- **Sufficient** (`muxn3_ok_staticN`). This is `muxn3_ok_staticN`'s full
  conclusion (joins, z_req, acks) with `S_J_X` in max form. Reset
  sequencing, the line flush and `1 ≤ N` are taken as before.
- **Not necessary** (`pass8`). `Mn3Wit`'s unit run, with every join's
  feedback net set to 8 and reset held to 11. Its closed forms, environment
  and causality are reused from MuxN3Timed. `S_J_X` fails for every input
  (`9 ≤ 6`), the max form holds, and the cell's conclusion holds.

NOT covered: a muxn boundary run for the max form. In this run `S_J_C` has
the same right side (10), so violating the max form by 1 would also break
`S_J_C`. An isolated counter-run needs a run with a slower control sender.

## Not done (and why)

- **bd_mux.uxa_join_latency (S_XA_J). Analysis only, not proved.** In x's
  own tokens the next j0 edge at uxa waits for the x client as well. j0 is
  C(x_req, decode), and x_req moves only after x_ack. So the form looks not
  necessary there. But `cel_run` also needs `H_DEP_XA` at bookkeeping edges,
  in tokens that do not select x, where only the control path applies.
  Showing non-necessity needs a new sufficiency proof that drops those
  edges. Not attempted.
- **bd_mux.isochronic_forks, bdc_muxn.iso_zack (S_*_FORK).** Not attempted.
  For inputs the next token does not select, the fork condition constrains a
  bookkeeping edge (MuxN3Timed note). Same obstacle as above.
- **bdc_muxn.iso_ctl (S_J_C per branch).** This is the muxn analogue of
  `uj_env_latency_ctl`, and `failC8` shows the mechanism on bd_mux. A muxn
  counter-run was not built. It needs a schedule where S_J_C is binding
  alone; `Mn3Wit`'s does not have that.
- **bd_mux.bundled_z.** Already known to be not necessary in its classic form
  (`Bundling.setup_not_classic`). Not re-done.
- **bdc_muxn.bundled_z_data.** Not attempted.
- **bd_mux.reset_first.** Already covered by Bsx: the loop terms are
  necessary, and H_RST_EARLY is not. Not re-done.

## Finding for the cell owner

The checker's `uj_env_latency_req` form for bd_mux and bdc_muxn is
pessimistic whenever z_ack reaches the ack C-element later than the join
node does. That should be common, because the z_ack path contains the
request line and the server, but it was not checked on any route.

The shipped form charges only the j -> uxa wire. The real return also
waits for z_ack. The max form is still sound (`mux_ok_staticN`), and it is
tight on the z_ack branch (`fail10`).

The control-path row (`uj_env_latency_ctl`) cannot be relaxed by even one
tick (`claimC1_false`).
