# B-necessity6: sixth necessity pass over the last "sufficient" rows (probe Bnx6)

Shard B, 2026-10-29. The scope is the rows of `formal/out/cell_constraints.json`
that were still labelled `sufficient` and that the B-necessity4, B-necessity5
and B-constraints-update notes left open. The JSON is NOT edited. The table
below is the proposed relabelling.

All Lean is core-only. Each file checks with `/tmp/claude-0/btools/bcheck.py`
(OK, no warnings):

- `formal/lean/Formal/Cells/Necessity6Mux.lean`: bd_mux uj1 max form, boundary run.
- `formal/lean/Formal/Cells/Necessity6MuxN.lean`: bdc_muxn max form, boundary run.
- `formal/lean/Formal/Cells/Necessity6MuxJ.lean`: bd_mux `S_XA_J.2`, boundary run.
- `formal/lean/Formal/Cells/Necessity6PipeSel.lean`: bd_pipe per-pin `H_RST_SEL`,
  all four terms.

`#print axioms` was run on 16 headline theorems. Each gives
`[propext, Classical.choice, Quot.sound]`. The scratch file is
`/tmp/claude-0/probes/Bnx6/Ax.lean` and is not delivered. There is no sorry,
admit, native_decide or axiom. Values are checked with `decide` or
`decide +kernel`.

## Method

The method is the house pattern (Bsx, Bnx4, Bnx5).

- `Claim s` is the row's shipped theorem with ONE hypothesis weakened by `s`.
  Every other hypothesis is copied word for word.
- `Claim 0` is proved from the shipped theorem.
- `¬ Claim 1` is shown by an explicit run:
  - real INITs;
  - every gate relation for ALL `t`, because each trace is defined by
    structural recursion on its own gate equation;
  - an open-loop periodic environment;
  - the weakened hypothesis off by exactly 1, and the others met;
  - the conclusion false at a decided sample point;
  - the race live.

That is "necessary at the boundary": one parameter point, not an iff over the
box.

All results are for the binary Lean `≤` form. Where the JSON carries the
strict `+1` (Bs, which is H_X_UNIFORM at w = 1, KleeneWin), the refuted point
is 2 ticks from the JSON form, and the `+1` itself is not addressed.

## Table

| row id | old | new | form covered | Lean |
|---|---|---|---|---|
| bd_mux.uj1_env_latency_req_max | sufficient | **sufficient+necessary_at_boundary** | Lean `≤` (`S_J1_YR`); JSON has strict `+1`, so the refuted point is 2 ticks from it | Necessity6Mux: `claimY0`, `failY10`, `claimY1_false`, `passY9` (passes at 9 ticks with equality) |
| bdc_muxn.uj_env_latency_req_max | sufficient | **sufficient+necessary_at_boundary** | Lean `≤` (`Nec4.MN3StaticN.S_J_XR`); JSON strict `+1` not addressed | Necessity6MuxN (`Formal.Cells.MuxN3Timed.Nec6`): `claimN0`, `failN`, `claimN1_false` |
| bd_mux.uxa_join_latency | sufficient | **unchanged (sufficient)**. The second conjunct (`S_XA_J.2`, uxa) is now necessary at the boundary. The first conjunct (`S_XA_J.1`) and the uya mirror have no result | Lean `≤` of `S_XA_J.2`; JSON strict `+1` not addressed | Necessity6MuxJ: `claimJ0`, `failJ`, `claimJ1_false` |
| bd_pipe.rst_lines | sufficient | **sufficient+necessary_at_boundary**. Every term now has a boundary run: the four PipeTimedN terms (Bsx3, Bnx5) and the four per-pin `H_RST_SEL` terms (here) | (a), (c), (d): Lean = JSON (no strict). (b): Lean `≤`, JSON strict `+1`, so 2 ticks from it | Necessity6PipeSel: `claim0`, `rst_sel_boundary`, `Runs.a_false`, `b_false`, `c_false`, `d_false`, `a_viol` … `d_viol` |
| bd_mux.isochronic_forks | sufficient | unchanged (analysis below: probably not necessary as written; not proved) | none | none |
| bdc_muxn.iso_zack | sufficient | unchanged (same analysis; the `S_A_J.2` analogue of `failJ` was not built) | none | none |
| bdc_muxn.bundled_z_data | sufficient | unchanged (not attempted) | none | none |
| design.rst_flush | sufficient | unchanged (not attempted: needs a lower-bound GMW chain run) | none | none |
| bd_arbcell.bbm | sufficient | unchanged (not attempted: involution model, no static form) | none | none |

Not in scope and not touched: bd_mux.bundled_z, bd_mux.reset_first and
bdc_muxn.iso_ctl. These were also still sufficient. The caller did not list
them. B-necessity4 has the notes on them.

## Plain-language statements

**Necessity6Mux, the uj1 max form.**

Assumed: OpsTimedMux's model. LUT arcs are lumped FIFO, wires are windows,
the line is FIFO, and the partners are port-level causal with minimum
latencies. The INITs of uj0, uj1, uor and bd_c2 are the real ones.

Proved: `ClaimY 1` is false. The run `N6.run 10` is Necessity4Mux's family
(unit delays, x and y tokens alternating, `Ex = Ey = 1`, `Ec = 6`, `Es = 1`)
with uj0's net at 1 tick and uj1's net at 10 ticks. In this run:

- every other `MuxStaticN` field holds, and `S_J1_YR` is off by exactly 1;
- reset sequencing holds;
- y_req's fall reaches uj1 at 57, one tick before the net shows j1's rise;
- j1 is 0 at 58, inside its token-1 window `[48, 61)`;
- z_req is 0 at 61, inside `[51, 64)`;
- the max is taken by the z_ack branch.

At 9 ticks the same family passes with equality (`passY9`).

NOT covered: an iff, per-pin arcs, the `+1`.

**Necessity6MuxN, the bdc_muxn max form.**

The new run `Mn6.run` has unit delays, a 10-tick feedback net on every join,
and reset held to 11. Control tokens select inputs 0, 1, 2 with a period of
22. The clients and the server are tight (`Ex = Es = 1`).

The point of the run is the control sender. It is one tick slower than
Mn3Wit's (`Ec = 2`). That gives `S_J_C` one tick more, so it holds (with
equality) while the max form alone is off by 1. Bnx4 could not build this
boundary because in Mn3Wit both forms have the same right side.

In this run:

- every other `MN3StaticN` field holds;
- reset sequencing holds, `H_FLUSH` is vacuous (N = 1), and `1 ≤ N`;
- in_0_req's fall reaches uj_0 at 41, while the decode is still on and the
  feedback pin reads 0;
- j_0 is 0 at 42, inside `[E 0, E 1) = [32, 43)`.

NOT covered: DELAY > 1, an iff, the `+1`.

**Necessity6MuxJ, `S_XA_J.2`.**

The race: j0's fall at the end of an x token travels the j0 → uxa wire. The
same fall also runs through uor, the line and the server, then the control
sender, the NEXT token's join (a y token), uor, the line and the server
again, and returns as z_ack's next rise at uxa. `S_XA_J.2` says j0's fall
plus uxa's loop must come first.

The run `J.run` has unit delays except a 12-tick j0 → uxa wire. Tokens
alternate x and y, and every partner is tight (`Ex = Ey = Ec = Es = 1`).
Reset is held to 14. The schedule has period 43 per x/y pair (x token 25
ticks, y token 18).

In this run:

- every other `MuxStatic` field holds, including `S_XA_J.1` and the whole of
  `S_YA_J`, and `S_XA_J.2` is off by exactly 1 (`14 = 13 + 1`);
- reset sequencing holds;
- j0's fall reaches uxa at 57 and z_ack's next rise at 58;
- x_ack (at the client) then oscillates with period 2 through the y
  transaction. It is 1 at 60, inside `[XA 1, XA 2) = [59, 67)`, where
  `mux_ok` says it is 0.

NOT covered: the uya mirror, `S_XA_J.1`, an iff, the `+1`.

**Necessity6PipeSel, the per-pin `H_RST_SEL` terms.**

Assumed: PipePerPin's per-pin model. Each pin is its own FIFO site-pin map,
the output map is FIFO, the feedback wire is a window, and `rst` is an exact
step. N = 1 with the real `bd_c2n` INIT.

`TimingS` is `TimingP` with each of the four terms weakened separately. Each
counter-run weakens exactly one term by 1. The conclusion is `nodes_clean`.

| term | what it says | run | outcome |
|---|---|---|---|
| (a) | `R0 + pr.hi ≤ R + ps.lo` | request pin 4 ticks, power-up request garbage 1 before `R0` (EnvP only constrains `r 0` from `R0`) | the node fires at 6, before `τ 0 0 = 12` |
| (b) | `out.hi + wh + pq.hi ≤ R + ps.lo` | feedback pin 4 ticks, node power-up value 1 (CtlP only constrains it from `out.hi`) | stale feedback fires the node at 6, before `τ 0 0 = 9` |
| (c) | `R + ps.hi ≤ ρ0 + pr.lo` | reset pin 5 ticks | the node rises at 10, not at `τ 0 0 = 9`: one tick late |
| (d) | `R0 + pa.hi ≤ ρ0 + pr.lo` | `R0 = R = 4`, first request at 4, ack pin 2 | `τ 0 0 = 7` is derived from the ack select's flush at `R0 + pa`, but the ack pin reads 0 before `R0` too (allowed), so the node rises at 6: one tick early |

Terms (a) and (b) guard against a real early fire from power-up garbage.
Terms (c) and (d) only guard the derived event times: the node is shifted by
a tick and the data is not corrupted. Data correctness under (c) or (d)
violated was not examined.

NOT covered: N ≥ 2, an iff, Kleene X at the selects.

## Analysis that is not proved (for the next probe)

**bd_mux.isochronic_forks (`S_XA_FORK`) and `S_XA_J.1`.** These look not
necessary as written. Both constrain uxa's `H_DEP_XA` against the next j0
edge at uxa, and there are two cases.

- *Tokens that select x.* The next j0 edge is causally after x_ack's edge,
  through the x client: x_req moves only after x_ack. The real bound is the
  client loop, `Lxa.hi + wxah ≤ Lxa.lo + Wxa.lo + Ex + Wx.lo + Lj0.lo +
  W0x.lo`. For `S_XA_J.1` there is also a max with
  `Kz + Kc + W0x.lo - W0x.hi`.
- *Tokens that do not select x.* j0 does not move. The "edge" that `cel_run`
  charges is a bookkeeping edge of a gated-off `Tok`.

The real fork race is the y → x transition: z_ack's fall from a y token
reaches uxa late, after the next x token's j0 rise. That race is an order
condition, `Wzx.hi ≤ Kc + W0x.lo` (up to the same-tick convention). The loop
term should not be needed there, because uxa's output is 0 throughout.

Proving any of this needs a `cel_run` that requires `H_DEP` only at real
(gate-on) edges, or a lemma that retimes a gated-off token's bookkeeping
edges anywhere between its neighbours. A `Tok` with gate false is invariant
under that retiming. bdc_muxn.iso_zack has the same structure (`S_A_FORK`,
`S_A_J`). Not attempted.

**design.rst_flush.** This needs a lower-bound run on a rank-m chain in
`TernarySound.Run`, with every gate at its slowest and every wire at W, to
see whether `(m+1)(D+W+1)` is attained. Not built.

**bd_arbcell.bbm.** This needs ArbInvolution's involution channels. There is
no static inequality to weaken by 1. Not attempted.

**bdc_muxn.bundled_z_data.** By analogy with bd_mux `S_Z_X`, this is
probably exact only when the decode is the late input. Not attempted.

## Findings for the cell owner

1. The z_ack branch of the env-latency max form is binding on both bd_mux
   joins and on bdc_muxn. A checker must evaluate the max form, not the
   shipped `S_J*_X` form.
2. A slow j0 → uxa route is a real hazard on a y token that follows an x
   token. `W0x.hi + loop` must beat the two-transaction return
   `2 Kz + Kc + Wzx.lo`. In the counter-run, x_ack oscillates through the
   whole y transaction.
3. At reset release, power-up garbage on a stage's request pin or on its own
   node can fire bd_pipe's first controller early, unless (a) and (b) hold
   per pin. Terms (c) and (d) only shift the first edge.
