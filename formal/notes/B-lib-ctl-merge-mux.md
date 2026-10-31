# B probe Lib1: every LUT of bd_ctl.v, bd_merge.v, bd_mux.v (binary + Kleene)

File: `formal/lean/Formal/Cells/LibCtlMergeMux.lean` (core Lean, imports only
`Formal.Cells.Prelim`; 79 theorems; about 19 s wall).

Check (clean, no warnings):

    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/LibCtlMergeMux.lean
    /home/user/asyncfpga3/formal/check.sh Formal/Cells/LibCtlMergeMux.lean   # -> [audit] 173 declarations checked, [check] OK

`#print axioms` on `j0_singleX`, `dr_d_K_closed`, `dr_settled_valid`,
`glitchFree_of_singleX`, `mux_joins_excl_K`: only `propext`. No
sorry/admit/axiom/native_decide.

Negative control: a scratch copy with one INIT bit flipped in `INIT_j0`
(AE08 -> AE0C) and in `INIT_dr` (B2 -> B3) fails 16 theorems (spec, closed
forms, fixed points, exclusion, ...), so the proofs do read the INITs.

Local defs (Prelim untouched): `K3.decForall` instance, `cSpec`, `kand`/`kor`,
`cK` (copies of CElemFn's), `Settled` (H_FB_SETTLED), `SingleX n init` (the
`n`-pin generalisation of CElemFn's `SingleX`), `allVecs`. `INIT_c2` is a
verbatim copy of bd_ce.v's (CElemFn proves the same constant); a later port
could import CElemFn instead.

## LUT inventory and parameter values

| cell | instance | primitive | INIT | pins |
|---|---|---|---|---|
| bd_fork, bd_join | none: `bd_ctree` | | | proved in CElemFn/CTree |
| bd_steer | u | LUT6_2 | 8888_8888_2222_2222 | I0=req I1=s I2..I4=0 I5=1, O5=req0 O6=req1 |
| bd_steer | uack | LUT2 | E | ack0, ack1 |
| bd_bd2dr | u | LUT6_2 | same as steer | I0=req I1=d, O5=f O6=t |
| bd_dr2bd HOLD=1 | ghold.u | LUT6_2, keep, O5→I2 | EEEE_EEEE_B2B2_B2B2 | I0=t I1=f I2=d I5=1 |
| bd_dr2bd HOLD=0 | gbare.uor | LUT2 | E | t, f (d = t wire) |
| bd_merge | uor, usel | LUT2 | E | |
| bd_merge, bd_mux | uxa, uya | bd_c2 | 00E8_00E8_00E8_00E8 | a, b=z_ack, q, rst |
| bd_mux | uj0 | LUT6, keep, O→I3 | 0000_AE08_0000_AE08 | x_req ctl_req s j0 rst 0 |
| bd_mux | uj1 | LUT6, keep, O→I3 | 0000_EA80_0000_EA80 | y_req ctl_req s j1 rst 0 |
| bd_mux | uor | LUT2 | E | j0, j1 |

Parameters: `HOLD` is 1 in `cells/verify/soak_top.v` and tb_conv, 0 in
tb_conv; both covered. `bdc/` never emits the converters; it emits bd_fork,
bd_join, bd_steer, bd_mux (with FASTFALL 0/1). `FASTFALL`, `DELAY`, `W` only
reach `bd_delay`/`bd_datamux` (bd_latch.v), not a LUT here: those are out of
this probe's scope (Lib part 2).

## Theorems

### (1) INIT = header equation (all match; NO mismatch found)
- steer: `steer_req0` (req.~s on O5), `steer_req1` (req.s on O6); bd2dr:
  `bd2dr_t`, `bd2dr_f`; `or2_spec` (every LUT2 E is OR).
- dr2bd: `dr_either` (O6 = t+f), `dr_d_majority` (O5 = maj(t,~f,d)),
  `dr_d_celem` (= C(t,~f), i.e. bd_c2n's function), `dr_codes` (ONE sets,
  ZERO resets, spacer holds, illegal 11 holds, as the header says),
  `dr_hold0_spacer_eats` (HOLD=0: d=t is 0 on spacer, HOLD=1 keeps it),
  `dr_hold0_either`.
- merge: `c2_spec`; mux: `j0_spec` (= ~rst . C(x_req, ctl_req.~s)),
  `j1_spec` (C(y_req, ctl_req.s)), `j1_is_j0_mirror`.
- Tied pins: `steer_tied_dontcare(_K)`, `dr_tied_dontcare(_K)`,
  `j0/j1_tied_dontcare(_K)`: I2..I4 (steer), I3,I4 (dr2bd), I5 (mux joins)
  are don't-cares, binary and even under X. Exception (fact, not a bug):
  `steer_I5_low`/`steer_I5_x`: the LUT6_2's I5=1 tie is load-bearing for O6
  (I5=0 turns O6 into the O5 function; X on I5 makes O6 X unless req=f).
  This is the standard LUT6_2 dual-output requirement; same for INIT_dr.

### (2) Kleene: single-X glitch freedom
- `SingleX n init`: for every binary vector and every pin, X on that pin =
  join of the two endpoint binary values. Proved for every INIT: O6 of both
  LUT6_2s, O5 (lower LUT5) of both, uj0, uj1, bd_c2, LUT2 OR
  (`*_singleX`). `glitchFree_of_singleX`: equal endpoints => definite.
- Remark: under the closure semantics `lutK` SingleX holds for ANY INIT (it
  is a consequence of the definition), so the per-INIT decides are
  confirmations; the content is in H_KLEENE_LUT (MuxTree.lean reduces it to
  one per-mux hypothesis plus read-once).
- Hence NO pin of any cell glitches under a single X. The pins where X
  reaches the output are exactly the real transitions (endpoints differ).
  Named, protocol-relevant ones:
  - steer: `steer_idle_s_free` (req=0: s may move, both branches 0);
    `steer_req_x_unselected` (req in transit: unselected branch stays 0);
    `steer_s_x_while_req` (s moving with req=1: X on BOTH branches, excluded by
    H_BUNDLED_S); `steer_excl`, `steer_excl_K` (never both t);
    `steer_K_closed` (Kleene AND).
  - merge: `merge_sel_xreq_fall_K` (sel does not glitch when x_req falls
    with x_ack=1), `merge_sel_xack_fall_K` (sel's fall is x_ack's);
    `merge_idle_not_acked(_K)` (C(0,z_ack) stays 0 even with X on z_ack).
  - mux: `j0_s_free_idle` (s free while ctl_req low and j0=0);
    `j0_s_free_high` (j0=1, s moving: definite iff x_req=1 or ctl_req=0 —
    if x_req fell first while ctl_req still high, s must be held: the
    control channel contract, s held to ctl_ack↓); `j0_s_free_high_xreq`;
    `j0/j1_blocked_by_s(_K)` (j0 cannot rise when s=1 definite, even with X
    on x_req and ctl_req); `mux_joins_excl(_K)`.
  - Kleene closed forms: `j0K_closed`, `j1K_closed`, `dr_d_K_closed`,
    `dr_either_K` (O6 independent of the feedback pin: an X decode never
    reaches the request path).

### (2b) Multi-pin (function) hazards — where single-X is not enough
Under closure semantics two pins in transit give X if any intermediate
vector differs. Each proved, with the protocol fact excluding it:
- `dr_either_hazard`: ONE→ZERO without spacer (t↓,f↑) can glitch `either`
  low (H_DR_SPACER). `dr_d_direct_change_x`.
- `j0_hazard_x_up_c_down`: x_req↑ with ctl_req↓ (s=0, j0=0): endpoints 0,
  middle fires. Excluded: ctl_req falls only after z_ack, which needs a join
  to have fired; with s=0 j1 cannot (`j1_blocked_by_s`). Harmless when
  deselected (`j0_no_hazard_when_deselected`).
- `steer_req_s_together` (H_BUNDLED_S), `merge_sel_hazard` (x_req↓ with
  x_ack↑ is impossible: x_ack↑ needs x_req=1 at the C input).

### (3) Feedback cells: hold / fixed-point structure
- dr2bd HOLD=1 (O5→I2): `dr_fixed_iff` (d stable iff not (t=~d ∧ f=d)),
  `dr_settled_valid` (under H_FB_SETTLED a valid code shows its bit),
  `dr_meta_resolve` (X on d resolves iff code valid & definite),
  `dr_meta_resolves_to` (to t), `dr_x_held_on_spacer` (power-up X persists
  across a spacer; the header's "never read" argument rests on req rising
  only behind a valid code — hypothesis H_DR_REQ_AFTER_D, not proved here).
- mux joins (O→I3): `j0_fixed_iff`, `j0/j1_rst_forced`, `j0_settled_fire`
  (H_FB_SETTLED), `j0_meta_resolve` (X on j0 resolves iff x_req definite and
  equals the Kleene decode ctl.~s), `j0_rst_clears_x`.
- merge/mux acks: bd_c2 (`c2_spec`; full fixed-point/meta theory in CElemFn).
  `merge_txn_celem` (each x_ack step of the header's x transaction is a
  legal bd_c2 move), `merge_sel_window` (sel = 1 from x_req↑ to x_ack↓,
  0 idle), `merge_req_as_sel_fails` (x_req falls 2 states early),
  `merge_ack_holds` (C holds, AND would drop), `merge_early_y_spurious_ack`
  (header's obligation: y_req into a high z_ack fires C(y_req,z_ack) —
  hypothesis H_MERGE_SEQ needed).

## Named hypotheses
- H_KLEENE_LUT (Prelim), H_FB_SETTLED (structure `Settled`, defined here).
- Named in statements' docs but not formalised as trace hypotheses (they
  need the trace model): H_BUNDLED_S (steer s stable req↑..ack↓),
  H_DR_SPACER (spacer between valid codes), H_DR_REQ_AFTER_D (dr2bd req after
  decode), H_MERGE_SEQ (second merge input waits for first transaction).
  Each is exhibited as necessary by a proved counterexample state.

## What did not work / not done
- Nothing failed except one wrong guess of mine (`j0_s_free_high` first
  stated as "= t"; decide refuted it: x_req=0, ctl_req=0 gives a definite 0,
  the legitimate fall). Restated correctly.
- Not done: trace-level handshake proofs of merge/mux (only the header's
  state sequence, not all interleavings); bd_delay/bd_datamux (bd_latch.v);
  feedback-wire timing (CElemTiming-style) for uj0/uj1 and dr2bd's O5 loop.

## Verdict
Works. Every LUT of the three files is covered; all INITs match their headers
(no finding against the cell library); all are single-X glitch-free; the only
X-sensitive behaviours are real transitions, and the multi-pin hazards are
each excluded by a named protocol hypothesis. Effort to extend to a
speed-independent interleaving proof of bd_merge/bd_mux (like CTree): about
1 day each; it would turn H_MERGE_SEQ / H_BUNDLED_S into derived constraints
for `cell_constraints.json`. Port to Core when Prelim goes: mechanical.

## Fidelity
- LUT6 / LUT2: Kleene closure semantics (H_KLEENE_LUT), equal to a read-once
  Kleene mux tree in any input order (MuxTree.lean). LUT2 modelled as a
  2-input table; on silicon it is a LUT6 with unused pins replicated/tied —
  covered by the tied-pin don't-care lemmas only for the LUT6s, not for the
  toolchain's LUT2 packing (grade B).
- LUT6_2: O6 = full INIT, O5 = lower LUT5 on I0..I4 (Prelim's o5B/o5K),
  matching 7-series (O5 is the lower LUT5, I5 selects for O6). Faithful.
- Feedback: next-state function with the feedback pin as an input, plus
  H_FB_SETTLED for stable states; wire delay not modelled.
- No timing, no runts, no analog: X is the only non-binary value.
