# B-lib-gap-mux: `bd_mux`'s select timing at the joins, made exact per pin

Probe Bmx (shard B, Phase 2), 2026-10-27. This follows B-lib-gap.md section 5,
item 1. New Lean file: `formal/lean/Formal/Cells/LibGapMux.lean` (core Lean
only; it imports LibGapSteer for `Rd`, `pulse`, `Stable` and `sAdv`). JSON
drafts are not merged, and neither the JSON nor its generator was edited:
`/tmp/claude-0/-home-user-asyncfpga3/2410103a-6b9c-55d0-893c-8f5f867f7a22/scratchpad/Bmx/draft_entries.json`
(made by `draft_entries.py` in the same directory). No route, board or
toolchain run was used.

## Problem statement

Cells: `bd_mux.uj0` (INIT 0000_AE08_0000_AE08) and `bd_mux.uj1` (0000_EA80_0000_EA80).
Both are LUT6s whose output O feeds back to I3. The pin map is I0 = x_req / y_req,
I1 = ctl_req, I2 = s, I3 = j, I4 = rst. Join b (uj0: b = 0, uj1: b = 1) is
evaluated from the real INITs, and `jB_eq` proves it equals
`C(r, ctl_req && (s == b))` with feedback q.

**Assumed:**
- **H_PIN_READ** (`LutEq`). For t >= 0, the join's output is its INIT applied
  to four reads:
  - r at `pr.σ t`;
  - ctl_req at `pc.σ t`;
  - s at `ps.σ t`;
  - its own output at `pq.σ t`.

  Each read map has its own window [t - hi, t - lo], made of the wire, the
  site pin and that pin's arc to O6. The maps need not be monotone. rst
  reads 0.
- **H_RESET** (`Rest`): the output is 0 for t < 0.
- **H_CTL_PULSE**: ctl_req at its driver is high exactly on [Cr, Cf).
- **H_S_STABLE**: s at its driver equals v on [S0, S1). Outside that window
  it is arbitrary.
- The client request r is arbitrary.

**Spec `JSpec`:** `j t = C(r read, ctl_req read && (v == b), j read)`. The
join obeys the C-element law on its own reads, but the decode uses the token's
value v instead of the wire s. When the join is selected, JSpec is exactly
bd_c2 on (r, ctl_req). When it is unselected, JSpec plus H_RESET gives j = 0
for ever (`unsel_low`), so no wrong-branch token can appear.

**Proved:**
- `dev_iff` (decided on the INITs) holds pointwise. At one instant, the LUT
  differs from the spec iff all three hold:
  - ctl_req reads 1;
  - s reads !v;
  - the request read differs from the feedback read.
- `join_box_exact` (headline). Take a box with `pr` in [Rlo, Rhi], `pc` in
  [Clo, Chi], `ps` in [Slo, Shi] and `pq` in [Qlo, Qhi], where Qlo >= 1, and
  assume Cr < Cf and 0 <= Cr + Clo. JSpec holds for every read-map quadruple
  in the box, every r, every admissible s and every trace satisfying
  H_PIN_READ and H_RESET **iff**
  `S0 + Shi <= Cr + Clo` and `Cf + Chi <= S1 + Slo`.
- `join_pin_exact` states the same with fixed delays. Use it per corner
  realisation. `join_pin_ok` is the sufficient half for any read maps. It
  needs no hypothesis on the request pin, the feedback pin, reset or the
  loop. `mux_joins` covers both joins with four inequalities, each join
  with its own ctl_req and s maps. `join_pin_ok_K` is the Kleene sufficient
  half: s, r and the feedback may be X.
- Necessity (`join_needed`): every violation has a request trace and a real
  join trace that satisfy H_PIN_READ and H_RESET at every t. The trace is
  constructed by `run`, by well-founded recursion on the loop
  (`run_luteq`, `run_rest`). The four cases:
  - `caseA` (s is wrong when the rise is read): a waiting request.
  - `caseB_unsel`: the unselected join with the other client's request
    waiting rises at S1 + ds.
  - `caseB_sel_short`: the selected join whose bad instant falls within one
    loop of firing.
  - `caseB_sel_long`: the selected join whose request has already fallen,
    as read, falls early.
- Counter-traces. Each holds for every trace satisfying H_PIN_READ (and
  H_RESET where used); `run` shows such traces exist.
  - `wrong_branch_latched`: setup is short by 100 ps and the loop is 50 ps.
    With x_req waiting, uj0 latches 1 from 1300 for ever, so x's token is
    taken for y's control token.
  - `wrong_branch_runt`: the same violation with a 200 ps loop. j0 is 1 at
    1300, 0 at 1400 and 1 at 1500: a runt that recirculates.
  - `selected_early_fall`: hold is violated. uj1 is 1 at 2700 and 0 at 2800,
    while the spec holds it at 1, so it falls 500 ps early.
- Non-vacuity: `witness_hyps` and `witness_run`. In a constructed run that
  meets every hypothesis, with both requests waiting, uj1 fires at 1300 and
  uj0 is 0 at every t.

**Finding.** The request pin (I0) and the feedback pin (I3) **drop out** of the
exact condition. The feedback window only shapes the failure:
- if the bad window outlasts the loop, the wrong token latches;
- otherwise a runt recirculates (under transport delay, as in MuxRtzTimed).

So the per-join select condition is the steer's, with ctl_req in the role
of req and O6 as the only output.

**NOT covered:**
- the uxa/uya acks and the RTZ rows;
- z bundling;
- the ctl_req fork as a cross-join obligation (shard C's rule K; here each
  join simply has its own `pc`);
- where S0 and S1 come from (s is held to ctl_ack↓ = z_ack↓);
- reset timing (the `reset_first` row);
- bdc_muxn, which has different join INITs;
- a mid-rail select inside the NMOS mux tree (H_KLEENE_LUT, grade B);
- internal tree delay, which is folded into the per-pin arcs;
- correlated pin delays (box necessity assumes the pins are independent);
- packaging for several tokens: `dev_iff` and `join_ok_of_reads` apply per
  token.

## Relation to the existing JSON rows (14 bd_mux entries)

- **Become exact:** `bd_mux.bundled_s_setup` and `bd_mux.bundled_s_hold`.
  The inequality keeps its shape: the old `Ts + shi <= Tc + clo` and
  `Tcf + chi <= Ts' + slo` are `S0 + ps.hi <= Cr + pc.lo` and
  `Cf + pc.hi <= S1 + ps.lo`, per join, and their windows already meant
  "route + site pin + uj arc". What changes:
  - exactness goes from `sufficient` to `exact` (an iff per join over the
    box);
  - the model now reads all four live pins separately, the feedback pin
    included;
  - the drafts drop `also_applies_to: bdc_muxn`, which is not covered.

  In prjxray the O6 arcs are flat over pins (45/124), so the per-pin content
  is the site pins SP[I2] (s, hi side) and SP[I1] (ctl_req, lo side). That is
  the term rule E is missing (`exact_structure_missing_site_pins`, unchanged).
  The hold half still has no rule (UNCHECKED).
- **Already exact, unchanged:** `uxa_rtz` and `uya_rtz`.
- **Stay sufficient**, or sufficient+necessary at the boundary, all
  untouched: `uxa_rtz_env`, `uya_rtz_env`, `bundled_z`, `isochronic_forks`,
  `uj_env_latency_req`, `uj_env_latency_ctl`, `uxa_join_latency`,
  `reset_first`, `bundled_z_s`, `bundled_z_data`.
- The old sufficient proofs (ConstraintsMux `*_unsel_low_timed`,
  `*_selected_c2`, MergeMuxSI's untimed necessity) are still cited. The new
  theorems supersede them for this obligation.

## Check

`/tmp/claude-0/-home-user-asyncfpga3/2410103a-6b9c-55d0-893c-8f5f867f7a22/scratchpad/bchk.sh formal/lean/Formal/Cells/LibGapMux.lean`
prints `[bchk] OK: formal/lean/Formal/Cells/LibGapMux.lean`. The only warning
is an unused `if h` binder in `runN`. `#print axioms` on the 15 main
theorems (`Bmx/ax.lean`) shows at most `propext`, `Quot.sound` and
`Classical.choice`. There is no sorry, admit, native_decide or declared axiom.
