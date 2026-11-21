# What shard B's cell layer gives the network argument (S4), as of 2026-11-07

All theorems below are about every behaviour of `circuit DecodedPS.net DecodedPS.boundary` (THE target), at the
behaviour's corner, standard axioms, built with lake (check.sh audit). "Premises" are value facts about named nodes
over time windows; discharging them is the network (order-level) argument.

## Storage nodes: clean switches (`Formal.Cells.RaceAllPS.target_switches`, `RaceAllPS2.target_switches`, `BigCertPS.target_switches`; all at once: `RaceAllTarget.target_switches_181`)
For g = 1, κ ≤ 83/200, one corner c for all rows (per theorem); for each of 135 + 23 + 23 = 181 storage nodes (`sws`), for any a, E, PS, sT, e':
- the node is at its OLD value on [a, sT - 1] (it is about to switch at sT);
- each certificate static node (`r.pc.1.sn`, values `sv`) keeps its value on [a, E k], with E k ≥ sT - 1 + PS and
  PS ≥ every row's `psum` (the acknowledge path's summed lower bands, a few ns);
- each memory row of the certificate is at its value on its feedback window before its hold starts;
- the certificate's window started early enough (`win … .1 + hi(ack pin) ≤ sT`; a is a few ns before sT);
- the force row's other pins (`F.P` minus the ack pin) and the confirm row's pins (`C.P`) read their listed values
  over [sT, e'] (these are the node's other inputs: x stays, reset stays low, …);
- timing: `sT + hi(feedback) ≤ e' + 1`, `1 ≤ lo(feedback)`;
then the node is at its NEW value on all of [sT, e'] (rises/falls once, no runt).
Concretely: the node's own acknowledge cannot come back early; what is left is "the node's inputs are where the
handshake says they are, and they stay there while it switches" (the C-element environment hypothesis hA, in a form
that no longer involves any timing race). Per-row data (static nodes, memory rows, force/confirm pins):
`out/target_ps_certs1.json`, `out/target_ps_certs2.json`; Lean rows in `RaceAllPS(2)/Bxx.lean` (`swNN`).

## Storage nodes: the acknowledge hold alone (`RaceAllPS(2).target_races`)
Same rows, without the force/confirm part: after the node flips (it was old on [a, e]), every read of its
acknowledge pin within the node's feedback-loop upper delay sees the old acknowledge value.

## Arbiters (`Formal.Cells.ArbServerPS.target_arbs_settle`)
With H_ARB(T) (`ArbOK T arbs x`), any sane p: for 5 of the 9 arbiters, if q is unchanged on [a, e], the
certificate premises hold, and the state LUT's other inputs are constant on [t1, t2] with t2 ≤ e + psum (the
server path's lower bands, ≥ ~1.5 ns at the fast corner, κ = 0), then q is constant on [t1 + T, t2]: the state
settles before the server's answer reaches it (the obligation `ArbTSpec.spec_double_ack` shows is needed).

Arbiter 0, transaction where q falls (`Formal.Cells.ArbOneAckPS.target_arb0_one_ack`): with the same premises plus
q low at t1 + T, the reset low, A1 low before s0 and the overlap condition (T small enough), the losing client's
acknowledge A1 stays low on [s0, t2 + …]: the one-acknowledge property for that transaction.

Updated 14:29: settle also for arbs[1], arbs[3] (`Formal.Cells.ArbServerPS3.target_arbs_settle`, 7 of 9 in all).
One-acknowledge (`ArbOneAck.one_ack_of` instances): `ArbOneAckAllPS.target_one_ack` (arbs[0],[5],[6],[7],[8], one
direction of q), `ArbOneAckAllPS2.target_one_ack` (arbs[0],[5],[7],[8], the other direction),
`ArbOneAckAllPS3.target_one_ack` (arbs[1],[3], q leaving true), `ArbOneAckAllPS4.target_one_ack` (arbs[6], the
other direction). Same premise shape as above.

## Latch hold windows (`Formal.Cells.LatchHoldCert.target_latch_holds_of`, instance `LatchHoldPS.target_latch_holds`)
Updated 14:46. For each listed latch, with one corner for certificates and latches: if the enable source shows its
open value on `[a, e]` (the certificate's cause), the certificate's static side inputs / memory rows hold, the
enable is closed on `[e + 1, E']`, the data source shows `v` from `e + 1 - Wd` up to the certificate's window start
(setup half), and the latch's own inequalities hold, then the latch holds `v` on `[A, E' + lo e]`. The HOLD half of
the data window (`… ≤ τ + hi e`) and the open window are no longer premises. Each row is valid for κ with
`(1+κ)·kB ≤ kA·(1-κ)` (its own range). Instances: LatchHoldPS (112), LatchHoldPS2 (214), LatchHoldPS3 (344; full-width run): 670
latches; κ ranges min 0.291 (SLICE_X32Y90.C O6), median ~0.63.
Sharper (use these): `Formal.Cells.LatchHoldPin.target_latch_holds_pin_of`, instances LatchHoldPinPS/PS2/PS3 (same
670 latches): the data premise is at the PIN (`t + lo d < τ + hi e`); κ ranges min 0.376 (SLICE_X20Y96.D O5), binding
hold latch SLICE_X32Y90.C O6 0.440, medians ~0.70. Premise lists: out/target_ps_latchholds*.json
(when generated).

## Generic tools (reusable for other nodes / kernels)
`CtlChain` (hold_set, hold_mem), `CertPS` (certOK / cert_sound), `CertMarginPS` (win_end_ge, margin_of_sums),
`CertRaceAll` (race_holds, target_races_of), `CertSwitchAll` (switch_row, target_switches_of), `ArbServer`
(q_settles). Generator: `tools-B/ps/gen_certs_ps.py` (rows from simb dumps; every row is re-checked in Lean).

## Not covered
4 RaceTablePS rows (power-up episodes); arbs[2], arbs[4] (q never flips after reset in any dump here); the other
direction of the one-acknowledge property for arbs[1], [3]; latches (LatchViewPS's data windows
are the analogous premises); non-vacuity of the premises in Lean (they hold in the simulated runs they came from).
