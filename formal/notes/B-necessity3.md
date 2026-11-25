# B-necessity3: third necessity pass over the sufficient-only rows (probe Bsx3)

Shard B, 2026-10-27. Lean (core only, every file `bchk` OK, `#print axioms`
= propext / Classical.choice / Quot.sound only, no sorry / native_decide):

- `formal/lean/Formal/Cells/Necessity3Pipe.lean`: bd_pipe data side (H_I, H_H, H_DATA_LEAD, output)
- `formal/lean/Formal/Cells/Necessity3PipeCtl.lean`: bd_pipe control (H_LAT, H_RST_LONG, H_RST_LINES request term)
- `formal/lean/Formal/Cells/Necessity3Arb.lean`: bd_arbcell H_GRANT_SKEW
- `formal/lean/Formal/Cells/Necessity3AMerge.lean`: bdc_amerge BidxB.gack

Draft JSON (not merged, Bsx2's format):
`/tmp/claude-0/-home-user-asyncfpga3/2410103a-6b9c-55d0-893c-8f5f867f7a22/scratchpad/Bsx3/draft_exactness.json`.
Axiom audit: `/tmp/claude-0/-home-user-asyncfpga3/2410103a-6b9c-55d0-893c-8f5f867f7a22/scratchpad/Bsx3/ax.lean`.

## Method

The method is the same as Bsx / Bsx2. `Claim s` is the row's shipped theorem
with that row's hypothesis weakened by `s` ticks. Every other hypothesis is
kept word for word, using a verbatim copy of the hypothesis structure with
slack fields: `DataS`, `TimingS`, `BidxBs`, `SkewClaim`.

- `Claim 0` is the shipped theorem.
- `¬ Claim 1` is shown by an explicit run. The run uses the real INITs, and
  every gate relation holds for ALL t. The weakened hypothesis is off by
  exactly 1 (`*_viol`), and the conclusion fails.

This gives necessity at the boundary: one parameter point per form, in the
binary model. It is not an iff. The JSON's strict +1 (Bs) is the Kleene X
window at equality, not these runs.

gcd_hw instantiates `bd_pipe` (N = 2 and 3), `bd_mux`, `bdc_muxn3`,
`bdc_amerge2/3` and FASTRISE `bd_delay`. It does not instantiate `bd_arbcell`,
`bd_flink` or `bd_mem` (B-gcd-cells.md). `bd_arbcell` was done anyway because
the probe prioritised it; its grant LUT is bd_arbiter's `ugrant`.

## Table

| row id | old | new | Lean |
|---|---|---|---|
| bd_pipe.boundary_I | sufficient | s+n_at_boundary | Necessity3Pipe.tok0, I_false (run RI), I_viol |
| bd_pipe.boundary_H | sufficient | s+n_at_boundary | tok0, H_false (RH), H_viol |
| bd_pipe.data_lead | sufficient | s+n_at_boundary (Lean form; the classic form stays not necessary) | tok0, L_false (RL), L_viol |
| bd_pipe.output | sufficient | s+n_at_boundary | out0, out_false (RO), O_viol |
| bd_pipe.lat_lumped | sufficient | s+n_at_boundary (N = 1 run) | Necessity3PipeCtl.ctl0, lat_false (RLat), lat_viol, lat_exc |
| bd_pipe.rst_lines | sufficient | unchanged; 2 terms at boundary | ctl0, long_false (RLong, N = 1), lines_false (RLines, N = 2) |
| bd_arbcell.grant_skew | sufficient | s+n_at_boundary (both forms) | Necessity3Arb.skew0, formA_false, formB_false |
| bdc_amerge.bundled_idx_ack_g | sufficient | s+n_at_boundary (+ general counter) | Necessity3AMerge.gack0, gack_counter, gack1_false |

That is 7 rows upgraded and 1 row (rst_lines) with 2 of its terms shown
necessary.

## Plain-language statements

**bd_pipe data side (Necessity3Pipe).** Assumed:
- `token` / `pipe_forward`'s hypotheses;
- the unit-delay control run `PipeTimedN.Wit` with N = 2, which satisfies
  GatesN, EnvN and TimingN at every instant;
- one-bit latches made of the real ODD INIT as transport LUTs, with one fixed
  delay per pin (`latch_tr`, point windows, so one corner);
- latch outputs in closed form, checked against the gate equation for all t;
- token values that alternate.

Proved, one statement per row:
- **H_I.** Stage 0's enable arc is 6. Data reaches stage 1 one tick too late
  for D plus its loop, and stage 1 still shows the reset value at 12.
- **H_H.** Stage 1's enable arc is 5. Stage 0's next token reaches stage 1
  while stage 1's closing enable is still in flight: wrong value at 15.
- **H_DATA_LEAD.** H_SETUP0 is tight and the data is 1 tick late. Stage 0
  closes before the new value's loop settles: stale value at 10.
- **output.** `Dl 1 = Er + 1`: stale value at the receiver's ack rise, 10.

Not covered: N = 3 and wide latch windows (the runs use point windows).

**bd_pipe control (Necessity3PipeCtl).** Proved, one statement per term:
- **H_LAT.** One stage. The sender drops its request exactly Es = 2 after
  the node rises, and the receiver acks Er = 3 after it. The feedback window
  [1, 3] still shows the old node value when the request falls. The node
  drops for 1 tick inside its high phase.
- **H_RST_LONG.** At release, the feedback shows the node's power-up value
  and the node rises 1 tick early.
- **Request-line term.** The N = 2 unit run, with boundary 1's request line
  a FIFO window [1, 4] that still reads stage 0's power-up value at release.
  Stage 1's node rises at 5, before its first edge at 7. Every derived event
  time is nominal (`ccq`).

In every run the feedback pins pick clean points afterwards, so the rest of
the run is the nominal one.

Not covered:
- The DACK term and the guard term of H_RST_LINES. A stray ack at release
  delays stage b-1's first rise, and the deviation propagates; no
  closed-form run was built.
- H_RST_SEL.
- H_ACK_FLUSH.
- The H_LAT and H_RST_LONG runs have N = 1, which is not a gcd_hw size.

**bd_arbcell H_GRANT_SKEW (Necessity3Arb).** Setup: L = 4 and an
opposite-sense handover, with request edges 5 > L apart. Each form is
weakened by 1: (d5, d6) = (1, 6) and (6, 1). Proved: both grants are high at
16.

The same runs violate only the skew bound of `opposite_sense_exclusion`, so
that bound is tight there too.

**bdc_amerge gack (Necessity3AMerge).**
- `gack_counter` is general. Take ANY Run + Scn2 whose server answers in
  exactly smin. If both forms of gack fail, A2 is still high in the index
  LUT's view at the minimal capture, and the index names the previous owner.
- `gack1_false` gives a concrete run, at one consistent corner, with a long
  r2 -> ugrant.I1 route (16). In it:
  - the r2 form is off by exactly 1;
  - the q form is off by 3;
  - RT2b, ack, grant and H_REQ_PATH hold;
  - the index is 1 at the capture.

Not covered: servers slower than smin and later captures. The Bfd caveat
(an edge-sampling consumer) is unchanged.

## Findings for the cell owner

1. **The H_LAT race needs asymmetric neighbour latencies.** In the unit
   witness (ER = EA) the request and ack edges coincide, so there is no hold
   window and no failure. The counter-run needs min(ER, EA) < max(ER, EA).
   This means the checker's `min` is the right term.
2. **The skew bound in `opposite_sense_exclusion` is tight.** ArbBinary
   says opposite-sense moves are clean "at any separation, given only the
   skew bound". The counter-runs show that this bound cannot be relaxed by
   1: at |d6 - d5| = L + 1 the grants overlap, even with request edges more
   than L apart. So the runt-free handover is not a reason to drop the
   skew check.
3. **gack is the exact condition at the minimal capture.** It needs no
   assumption on `ack` or `grant`, so the OR form in the JSON is right as is.

## Not done (from round 2's list)

- **bd_mux / bdc_muxn latency rows** (bundled_z, isochronic_forks,
  uj_env_latency_req/ctl, uxa_join_latency, iso_ctl, iso_zack,
  bundled_z_data, uj_env_latency_req). Each needs a whole-cell counter-run of
  OpsTimedMux / MuxN3Timed for all t: joins, ack C-elements, uor and the
  delay line. Not attempted. Lt4's analysis that uj_env_latency_req is only
  sufficient, because the return also waits for z_ack, suggests a
  non-necessity result rather than a boundary run.
- **bd_arbcell.bbm.** This is an involution-model row with no static form.
- **bd_delay[FASTRISE].ack_flush (H_ACK_FLUSH).** A violation glitches only
  the DACK pin (`pins_clean`) while the stage is already low. It would refute
  `pins_clean`, not `pipe_ctl`, and needs the copies to be a real chain.
  Not done.
- **design.rst_flush.** Not attempted.
- **Not in gcd_hw:** bd_flink and bd_mem.
- **Skipped as instructed:** bd_link_dc and bd_ctree.

## Check

    /tmp/claude-0/-home-user-asyncfpga3/2410103a-6b9c-55d0-893c-8f5f867f7a22/scratchpad/bchk.sh \
      formal/lean/Formal/Cells/Necessity3PipeCtl.lean formal/lean/Formal/Cells/Necessity3Pipe.lean \
      formal/lean/Formal/Cells/Necessity3Arb.lean formal/lean/Formal/Cells/Necessity3AMerge.lean
    -> [bchk] OK: (all four)
