# B-necessity2: second necessity pass over the sufficient-only rows (probe Bsx2)

Shard B, 2026-10-27. Lean (core only, every file `bchk` OK, `#print axioms`
= propext / Classical.choice / Quot.sound only):

- `formal/lean/Formal/Cells/Necessity2Arb.lean`: bd_arbiter RT2 fields
- `formal/lean/Formal/Cells/Necessity2AMerge.lean`: bdc_amerge3 H_RT2_CASCADE fields
- `formal/lean/Formal/Cells/Necessity2Delay.lean`: bd_delay FASTFALL flush
- `formal/lean/Formal/Cells/Necessity2Latch.lean`: bd_latch_rst H_PW

Draft JSON (not merged):
`/tmp/claude-0/-home-user-asyncfpga3/2410103a-6b9c-55d0-893c-8f5f867f7a22/scratchpad/Bsx2/draft_exactness.json`
(same format as Bsx's draft). Not touched: bd_merge.uxa_*, bd_ctree.node_fork (probe Bmg).

## Method

For each row, `Claim slack` is the row's sufficient theorem with that row's
hypothesis weakened by `slack` ticks (ps), and every other hypothesis kept
word for word. `Claim 0` is the existing theorem. `¬ Claim 1` is shown by an
explicit run that meets every other hypothesis. The runs use the real INITs,
the gate relations hold for ALL t (and for the arbiter, so does the server
relation), and the violated hypothesis is off by exactly 1 (`*_viol` lemmas).
On each run the conclusion fails. That is "necessary at the boundary": one
parameter point per form. It does NOT show that every violating point
fails, and it does not show an iff.

## Table

| row id | old | new | Lean |
|---|---|---|---|
| bd_arbiter.rt2_g1 | sufficient | sufficient+necessary_at_boundary | Necessity2Arb.claim0, g1_false (SG1, c1f=2>c1r=1), g1_false_1C (SG1c, every arc rise=fall) |
| bd_arbiter.rt2_forkA | sufficient | s+n_at_boundary | claim0, forkA_false (SFA, one corner) |
| bd_arbiter.rt2_forkG | sufficient | s+n_at_boundary | claim0, forkG_false (SFG, one corner) |
| bd_arbiter.rt2b_g2 | sufficient | s+n_at_boundary | claim2_0, g2_false (SG2, c2f=2>c2r=1) |
| bd_arbiter.rt2b_forkA2 | sufficient | s+n_at_boundary | claim2_0, forkA2_false (SFA2) |
| bd_arbiter.rt2b_forkG2 | sufficient | s+n_at_boundary | claim2_0, forkG2_false (SFG2) |
| bd_arbiter.rt2_pulse | s+n_matched_fork | s+n_at_boundary | claim0, pulse_false (SP: unmatched forks, one corner) |
| bd_arbiter.rt2b_pulse2 | s+n_matched_fork | s+n_at_boundary | claim2_0, pulse2_false (SP2) |
| bdc_amerge3.rt2_cascade_pulse / _g1 / _forkA / _forkG | sufficient | s+n_at_boundary | Necessity2AMerge.cclaim0; cpulse_false, cg1_false (+ cg1_false_1C), cforkA_false, cforkG_false |
| bdc_amerge3.rt2_cascade_pulse2 / _g2 / _forkA2 / _forkG2 | sufficient | s+n_at_boundary | cclaim2_0; cpulse2_false, cg2_false, cforkA2_false, cforkG2_false |
| bd_delay[FASTFALL].flush_per_stage | sufficient | s+n_at_boundary | Necessity2Delay.flush0, flush1_false |
| bd_delay[FASTFALL].flush_uniform | sufficient | not_necessary (replacement: flush_per_stage) | Necessity2Delay.uniform_not_necessary, uw_line |
| bd_latch_rst.setup_pulse | sufficient | s+n_at_boundary (Lean '<=' form, both INITs) | Necessity2Latch.pw0, pw1_false_rst0, pw1_false_rst1 |
| bd_fork.branch_data_edge | sufficient | not_necessary (replacement: bd_fork.branch_data) | existing ForkData.edge_form_not_needed (reclassification only, no new Lean) |

That is 18 of the 51 sufficient-only rows: 17 with new Lean and 1
reclassified from existing Lean. Two more rows move up from
necessary_matched_fork. For every row with a strict +1 in the JSON form, the
run refutes the Lean `≤` form by 1. The JSON's extra +1 is CElemStrict's
Kleene X window at equality, as in Bsx's NecessityMuxRtz.

## Plain-language statements

**Arbiter, RT2 fields (Necessity2Arb).** Assumed: the theorem's hypotheses,
which are the real ustate / ugrant / ua1 / ua2 INITs, the rise-fast OR
channel, one routed delay per pin, a four-phase server with minimum
response smin, the handover scenario, the A0 fork, and the four RT2 fields.

Proved: for each of the fields pulse, g1, forkA and forkG, and their four
mirrors, there is a run that satisfies all of these with only that field
1 ps short, and on that run both acks are high at once. Each run's server
answers in exactly smin, and the arc form is stated for that worst case.

Two mechanisms show up:
- In the fork fields, the releasing client's ack falls 1 ps after the other
  ack rises. Every arc is 1 ps, so these runs sit at one corner.
- In g1 and pulse, the releasing C-element falls, its own low edge is still
  on the feedback wire when A0 re-rises, and it re-latches high.

Not covered: servers slower than smin. The fields are worst-case-server
bounds, so a slow server can pass them.

**Cascade (Necessity2AMerge).** Assumed: everything in `rt2_cascade`, with
runs of both arbiters. Arbiter 2 is `C2 1 1 1 6` at one corner, so its
acc1_ack output equals arbiter 1's A0 at every instant and sF = sR = 8.

Proved: each of the 8 fields, weakened by 1 ps, admits an ack overlap of
arbiter 1. Not covered: an in2 handover during arbiter 1's handover (the
theorem itself excludes it).

**FASTFALL (Necessity2Delay).** Assumed: window channels, the real
2'h2 / 4'h8 INITs, taps on `s 0`.

Proved, per-stage form: weakening every per-stage condition by 1 tick lets
z rise at 13, while the matched rise is at 16. Proved, uniform form: it can
fail while every line still meets the conclusion. Not covered: bd_delay_gated
(not instantiated) and FASTRISE `ack_flush`.

**bd_latch_rst H_PW (Necessity2Latch).** Proved: with the enable pulse one
tick shorter than `ehi + fhi - elo`, both reset INITs lose the token at 13,
and a period-3 runt train follows. Every other capture hypothesis holds on
that run.

## Findings for the cell owner

1. **7j's runt-decay remark does not hold in general.** ArbHeldTimed2 says
   ua1's hole "shrinks by c1f - c1r per round, so A1 ends latched high". At
   one corner (rise = fall) there is no shrink, and the hole recirculates
   forever: SG1c, SP and SP2 are eternal runt trains, proved for all t. A
   Python simulation of the same Run equations also gives a non-decaying
   period-3 train with c1r = 1, c1f = 4, wfa1 = 2, because c1f + wfa1 is a
   multiple of the loop c1r + wfa1. That one is simulation only, not Lean.
   The silicon outcome of sub-arc runts is still outside the model.
2. **The g1 arc field's slack can come from the q path.** The arc form uses
   the r1 path, an upper bound on G1, while g1 can fall earlier through q
   (`g1fq`). Hitting the g1 boundary needs wq slow enough that the r1 path
   is the earlier one (SG1: wq = 6). When q's path wins, the field is
   conservative.
3. The forkA / forkG counter-runs keep RT1 (grant exclusion) intact (proved
   in `FA_viol`, `FG_viol`). Ack exclusion fails on its own, with no grant
   overlap. For SP the same is seen in simulation only.

## Not done (remaining sufficient-only rows)

These rows were not attempted:
- bd_pipe.* (lat_lumped, boundary_I/H, rst_lines, data_lead, output)
- bd_delay[FASTRISE].ack_flush
- design.rst_flush
- bd_link_dc rule_K/L (not used in gcd_hw)
- bd_flink.qfb_first
- bd_mux / bdc_muxn env-latency rows
- bd_mem.*
- bdc_amerge.bundled_idx_ack_g
- bd_arbcell.grant_skew / bbm

PipeTimedN's N-stage model (`PN`) needs a full pipe counter-run, which is a
bigger construction.
