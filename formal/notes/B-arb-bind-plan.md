# Plan: binding the arbiter (amerge) into the driver-bound network (not done)

2026-10-31, shard B. `FiniteNetBoundMCensus`: of the 39 link sides still unbound in
`FiniteNetBoundM`, 28 end at an `amerge` (23 request sides: the arbiter's output `z.req = R0`; 5
acknowledge sides: `x.ack = A1`, `y.ack = A2`). This note is the design for the next session.

## The cells (cells/rtl/bd_arb.v `bd_arbiter`)

| cell | LUT | pins | node | channel it drives |
|---|---|---|---|---|
| `ustate` O6 | `64'hFFF0_FFB2_ACAC_ACAC` | r1 (x.req), r2 (y.req), q (own feedback), rst, A0 (z.ack) | q | none (internal) |
| `ustate` O5 | same INIT, low half | r1, r2, q, rst, A0 | R0 | z.req |
| `ugrant` O5 / O6 | `64'h0C0C_0C0C_A0A0_A0A0` | r1, r2, q | g1 / g2 | none (internal) |
| `ua1` / `ua2` | `bd_c2` | g1 / g2, A0 | A1 / A2 | x.ack / y.ack |

So the bindings are: `reqSrc z = ustate.O5`, `ackSrc x = ua1`, `ackSrc y = ua2`; internal pins
q (O6 -> O5, O6, ugrant), g1 -> ua1, g2 -> ua2; external pins r1, r2 (bound by `reqSrc`), A0
(bound by `ackSrc z`).

## What each cell's truncated contract needs

`ua1`/`ua2` are C-elements: `FCelSpec GC2` with one internal pin (as `uxa`/`uya` in `BWit2Lib`;
`celB` checks them). The other three are where arbitration lives. A truncated contract
("pins clean on [0, T) => node clean on [0, T + lo)") is FALSE for them without race
hypotheses: `ArbAMergeRunWit.sep_cex_run` is a from-reset run that misses H_SEP by 1 ps in which
q, g1, g2 make runts. So their specs must carry the race conditions as named fields, which is
the honest form of "the arbitration resolves cleanly":
- per epoch (grant from idle, release, handover, idle race, hold: the classes of
  `ArbAMergeRunStitch.Plan`), the window conditions `RowsG`/`RowsR`/`RowsX`, RA1, and H_SEP;
- in the network form, as edge-time inequalities between the r1/r2/A0 pin edges and the q
  edges (like H_SND/H_RCV), so that the network closure (`fmixed_closed`) can use them.
`amerge_of_plan` already turns the gate-level arbiter run into C's `AMerge` on Plan schedules;
what is missing is the per-cell truncated form of the same windows.

## The witness

`bsim2.py` keeps C's 1-tick arbiter. A gate-level arbiter in the simulator (ustate, ugrant, ua1,
ua2 at LUT 1 + wire 1) must still meet C's `AMerge` fields on chB; C's internal g1/g2 traces would
be B's grant nodes delayed (as the mux joins are, 6 ticks). gcd_hw's 9 arbiters are uncontested
on C's runs (`gcd_hw_arbiters_uncontended3`), so only the grant-from-idle / release / hold
epochs occur, where no race condition is tight.

## Expected outcome

Request sides: 23 of the 24 unbound would bind (the last is the source, which cannot be gate-
modelled on a terminating run: `FiniteNetSrc.chW_src_unwired`); acknowledge sides: 5 of 15
(muxn 4 and the fork trees 6 remain). The network theorem would then carry the arbiter's race
conditions as explicit hypotheses, which is the digital-race content the owner asked for (PROGRAM
item 4), now inside the gcd_hw theorem rather than beside it.
