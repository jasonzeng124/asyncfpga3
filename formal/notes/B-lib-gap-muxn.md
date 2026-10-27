# B-lib-gap-muxn: `bdc_muxn`'s select timing at the joins, exact per pin and per index bit

Probe Bmn (shard B, Phase 2), 2026-10-27. Follows B-lib-gap-mux.md (probe Bmx),
which covered `bd_mux` and left `bdc_muxn` out. New Lean file:
`formal/lean/Formal/Cells/LibGapMuxN.lean` (core Lean only; imports LibGapMux
for `int_ind`/`run`, LibGapSteer for `Rd`/`pulse`/`Stable`, AMergeGates for the
INITs). JSON drafts are not merged, and neither the JSON nor its generator was
edited:
`/tmp/claude-0/-home-user-asyncfpga3/2410103a-6b9c-55d0-893c-8f5f867f7a22/scratchpad/Bmn/draft_entries.json`
(made by `draft_entries.py` in the same directory). No route, board or
toolchain run was used.

## The cell

`bdc/emit.py` `emit_muxn` does not fold the decode into the join, as `bd_mux`
does. For each input k it emits

    assign sel[k] = ctl_req & (s == 2'dk);     // ordinary logic, mapped by yosys
    bd_c2 uj{k} (.a(in{k}_req), .b(sel[k]), .rst(rst), .q(j[k]));

So each join is two LUTs:
- a combinational decode LUT3. Its INITs come from AMergeGates, under
  H_YOSYS_MAP: `sel[0]` = `8'h10` on `[s0, s1, ctl_req]`, `sel[1]` = `8'h40`
  on `[s1, s0, ctl_req]`, `sel[2]` = `8'h40` on `[s0, s1, ctl_req]`. `dec_eq`
  proves each one equals `ctl_req & (s == k)`.
- a wire from the decode to `uj_k.I1`, then `bd_c2` (`00E8_00E8_00E8_00E8`)
  with its feedback.

The 2-bit index enters each decode on two pins, each with its own window.

## Problem statement

**Assumed:**
- **H_PIN_READ (decode)** (`DecEq`). At every t the decode output is its INIT
  applied to three reads: s0 at `p0.σ t`, s1 at `p1.σ t` and ctl_req at
  `pc.σ t`. Each read map has its own window (wire + site pin + that pin's
  arc). The maps need not be monotone. The decode has no reset and no state.
- **H_PIN_READ (join)** (`JEq`). For t >= 0 the join output is bd_c2's INIT
  applied to three reads:
  - the request at `pr.σ t`;
  - the decode output at `pd.σ t`;
  - its own output at `pq.σ t`.

  rst reads 0.
- **H_RESET** (`Rest`): the join is 0 for t < 0.
- **H_CTL_PULSE**: ctl_req is high exactly on [Cr, Cf).
- The index comes in one of three forms:
  - any given trace per bit (`join_exact_fixed`);
  - **M1**, H_S_STABLE_BIT: bit b equals the token's bit on its own window
    [S0_b, S1_b) and is arbitrary outside it;
  - **M2**, H_S_STEP: bit b changes once, cleanly, at T_b.
- **H_S_RANGE**: the codes are < 3.
- The client request is arbitrary.

**Spec `NSpec`:** `j = c2(request read, ctl_req read && (v == k), j read)`.
ctl_req is read through the composite map `pc ∘ pd`. When the token selects
the join, this is bd_c2 on (request, ctl_req). Otherwise (`unsel_low`), the
join is 0 for ever.

**Proved (all check; axioms at most propext, Quot.sound, Classical.choice):**
- `join_exact_fixed` (the core). Take fixed per-pin delays and any traces
  for the index bits. NSpec holds for every request trace and every trace
  satisfying H_PIN_READ and H_RESET **iff** there is no instant u at which
  ctl_req reads 1 at the decode while the code read bit by bit disagrees with
  the token about k.
  - Necessity (`join_needed`) builds a real trace with `run`:
    - unselected join: the request is waiting and the join rises;
    - selected join, at the least bad instant w: either the join is still 0
      one loop back and fails to rise, or the request falls (as read)
      exactly at w and the join falls early.
  - Several terms drop out of the condition: the decode-to-join wire `pd`,
    the join's request pin and its feedback pin.
- `maps_ok` and `maps_needed`: the box versions, per instant.
- **M1, over the box:**
  - `sel_box_exact` (selected join): iff both bits meet setup
    `S0_b + hi_b <= Cr + Clo` and hold `Cf + Chi <= S1_b + lo_b`. Only the
    decode pins enter.
  - `unsel_box_exact` (unselected join): iff `Cover`. Every instant at which
    ctl_req may read 1 must lie inside the read-stable window
    [S0_b + hi_b, S1_b + lo_b) of some bit in which k and v differ.
    - When k and v differ in one bit, Cover is bd_mux's single-bit form
      (`cover_01`).
    - For {k, v} = {1, 2} both bits differ, and the two windows may cover
      the ctl_req window together (`cover_12`, closed form `cover2_iff`).
  - `sel_cond_cover` and `decode_exact_all_tokens`: join k is correct for
    every token value v < 3 **iff** decode k's two index pins meet the
    per-bit setup and hold. This is the form the JSON row needs.
- **M2, the third branch** (`third_fixed_exact`, `third_fixed_exact_21`,
  `third_box_exact`). Take an index change 1 → 2 or 2 → 1. Both bits change.
  The intermediate code 00 selects join 0, which neither token wants; 11
  selects nothing. Let r be the bit going 0→1 and f the bit going 1→0,
  each read at decode 0. Join 0 is correct **iff H_NO_THIRD** holds:

      Cf + Chi <= T_f + lo_f  ∨  T_r + hi_r <= Cr + Clo  ∨  T_r + hi_r <= T_f + lo_f

  In words, one of three things holds:
  - the falling bit is read changed only after ctl_req's read window;
  - the rising bit is set up before ctl_req can read 1;
  - the rising bit is read changed before the falling bit can be, so the
    transition passes through 11.

  The same theorem serves the setup side (token = the new code) and the hold
  side (token = the old code, T = the next change).
- **The third branch is never alone:**
  - `step_sel_exact`: after a clean step, the selected join is correct iff
    **both** changed bits are read changed by the time ctl_req reads 1.
  - `third_implied_by_setup`: whenever the selected join is correct, join 0
    is too.
  - `step_old_exact`: the old branch is excluded as soon as **one** changed
    bit is read changed.
  - `rise_first_example`: in the rise-first case, join 0 is correct and the
    selected join fires late. That is a deviation from NSpec, but no token
    goes to the wrong input.
- **Counter-trace** (`third_branch_latched`). The index goes 1 → 2 for a
  token meant for input 2. The rising bit s1 is read through 700 ps
  (changed from 1500), the falling bit s0 through 100 ps (changed from 900),
  and ctl_req at the decode from 1300. Decode 0 then reads 00 on
  [1300, 1500). With in0_req waiting, join 0 latches 1 from 1400 for ever,
  on every trace that satisfies H_PIN_READ. Input 0's token is consumed by a
  control token for input 2.
- **Non-vacuity:**
  - `witness_third`: a constructed run with the same change and good timing,
    both requests waiting. Join 0 is 0 at every instant and join 2 fires
    at 1400.
  - `selcond_witness`: SelCond is satisfiable.
  - `run_jeq`: every fixed-delay environment has a join trace.

**Finding.** At bdc_muxn's joins the exact select condition is bd_mux's, once
per decode and once per index bit, read at the **decode LUT3's** pins.
Several things that one might expect to matter drop out:
- the decode-to-join wire;
- the join's request pin;
- the join's feedback pin;
- the extra LUT stage itself (the decode is combinational and glitches, but
  only as its pins read).

The multi-bit hazard (a third branch through an intermediate code) has its
own exact per-join condition, H_NO_THIRD. It adds **no** obligation beyond
the per-bit setup of the rising bit or the hold of the falling bit, which the
selected join (or the hold side) needs anyway. The old row's "+ per-pin arc
margin sel_i.I{0,1} vs sel_i.I2" is inside the pin windows here, because each
window includes its own arc to O6.

**NOT covered:**
- the ua_k acks, `|j`, the line and z bundling (MuxN3Timed);
- the data LUT5 (`S_Z_S` stays sufficient);
- the ctl_req and s forks as cross-decode obligations (each decode has its
  own maps here);
- where S0, S1 and T come from (the sender's contract; the composed
  round-trip hold form stays sufficient);
- reset timing;
- X or mid-rail values on the bits (H_KLEENE_LUT): no Kleene version was
  written;
- internal mux-tree delay, which is folded into the per-pin arcs;
- correlated pin delays: box necessity assumes the pins are independent, so
  under a corner model use `join_exact_fixed` per realisation;
- n > 3: more index bits, and a decode that may be split over several LUTs.
  That case is not mapped, and H_YOSYS_MAP is only for muxn3;
- M2 with several changes of a bit inside one window (M1 covers that);
- packaging for several tokens.

## JSON drafts (3 rows)

- **`bdc_muxn.s_setup`**: the decode form becomes exact.
  - Inequality: `S0_b + ps_b(k).hi <= Cr + pc(k).lo`, per decode k and
    per bit b (old: `Ws_b(i).hi <= Lsd + Wc(i).lo` with `S0_b = Cr - Lsd`).
  - The LUT arcs are now inside the Lean windows.
  - Row exactness: `exact_decode_form+sufficient_data_form`, because the
    data LUT5 form is unchanged.
- **`bdc_muxn.s_hold`**: `Cf + pc(k).hi <= S1_b + ps_b(k).lo`, exact given
  S1_b. The old round-trip form (S1_b from the sender's contract) is kept as
  the sufficient way to obtain S1_b. Still no rule (UNCHECKED).
- **New: `bdc_muxn.no_third_branch`** (H_NO_THIRD, exact per join 0).
  This row is informational: s_setup and s_hold imply it.

Validator: I merged the drafts into a scratch copy
(`Bmn/merged_check.json`) and ran
`formal/out/cell_constraints.validate.py` on it. The only errors are "file is
untracked", because LibGapMuxN.lean has not been committed yet.

## Check

`/tmp/claude-0/-home-user-asyncfpga3/2410103a-6b9c-55d0-893c-8f5f867f7a22/scratchpad/bchk.sh formal/lean/Formal/Cells/LibGapMuxN.lean`
prints `[bchk] OK: formal/lean/Formal/Cells/LibGapMuxN.lean`, with no
warnings. `Bmn/ax.lean` runs `#print axioms` on 25 theorems, and each depends
on a subset of {propext, Quot.sound, Classical.choice}. There is no sorry,
admit, native_decide or declared axiom.
