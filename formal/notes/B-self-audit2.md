# B-self-audit2 (probe Bsa2): adversarial audit of shard B's ten headline "exact" theorems

2026-10-27. Scope: the iff theorems that `formal/out/cell_constraints.json` cites with role
`exact` from this session's shard-B files (CElemStrict, LibGapSteer, LibGapMux, LibGapMuxN,
LibGapDelay, LibGapLatch, NecessityReset, RigIdx). Every check goes through
`scratchpad/bchk.sh` (lakefile options, `-DautoImplicit=false`). No route, no toolchain run.
New file: `formal/lean/Formal/Cells/SelfAuditB5.lean` (`[bchk] OK`). Mutants:
`formal/lean/Formal/Cells/_Mut2/` (for the lead to delete).

## 1. What was checked per theorem

(1) the statement is an iff with the claimed quantifiers; (2) the hypotheses hold together at
a point with lo < hi, using non-monotone read maps where the trace constructor allows it
(new, SelfAuditB5); (3) the necessity direction builds a trace that meets every hypothesis
(read from the proof); (4) the model matches the note, and the INIT constants match
`cells/rtl/*.v`. I grepped the INITs: bd_c2 00E8, c2_set FFE8, c2n 00B2, c2n_set FFB2,
c3 0000_FE80, c4 0000_0000_FFFE_8000, uj0 0000_AE08, uj1 0000_EA80, steer 8888_8888_2222_2222,
latch odd B8B8, pair FF33_CC00_B8B8_B8B8, latch_rst 00B8/FFB8, delay LUT1 2 / LUT2 8. All match,
and so do the pin maps. The bdc_muxn decode LUT3s (10/40/40) are not in cells/rtl. They are
H_YOSYS_MAP (AMergeGates); bdc/emit.py:544 emits `sel[k] = ctl_req & (s == k)`, which those
INITs compute.

## 2. Verdicts

| # | theorem (file) | verdict | evidence |
|---|---|---|---|
| 1 | `box_iff`, `clean_iff` (CElemStrict) | CONFIRMED (scope) | Iff over D in [Dlo,Dhi] and every release start s >= slo. The feedback is a PURE delay D (H_FB_PURE), not a window or non-monotone read map, and D and s are independent (box). Necessity: `loop_exists` simulates at (Dhi, slo). New witness `celem_box_nd`: box [200,420], safe from 421, not safe from 420. `celem_inside`: D = 300 strictly inside, clean |
| 2 | `env_latency_iff` / `_strict` (CElemStrict) | CONFIRMED in the model; JSON citation OVERSTATED on 11 rows | `env_nd`: dlmin 100 < dlmax 124, safe at E = 325, unsafe at 324. JSON: 11 rows carry `strict.backing = "mechanism (Facts not decided)"`: bd_c3/bd_c4 pulse_width (exactness `exact`), env_latency, sel_order, the four reset_width rows, design.rst_hold. These still cite the generic theorems as `exact`. The Facts ARE decided in CElemStrict2 (`c3_all`, `c4_all`, `*_rst_race`, `reset_width_iff`), but the JSON cites nothing from CElemStrict2. Stale: fix the citation, not the theorem. Separately, `exact`-role citations sit on rows whose own exactness is `sufficient` (e.g. bd_mux.isochronic_forks, bd_merge.reset_first). That is disclosed as "for the race inside this entry", but a role count overstates the rows |
| 3 | `steer_box_exact` (LibGapSteer) | CONFIRMED | ∀ pr ps in the box, ∀ s stable on [S0,S1). Necessity at the box corners with `sAdv` (Stable). `setup_needed` / `hold_needed` hold for either branch, so the unselected (spurious-token) case alone gives exactness. New `steer_nd`: both maps non-monotone over [200,400] and [300,600], SpecOK on O5 and O6, O6 high and O5 low at 1400 |
| 4 | `join_box_exact` (LibGapMux) | CONFIRMED | Four per-pin maps; request and feedback drop out. Necessity uses `run_luteq` / `run_rest` traces. The spec is pointwise conformance (JSpec), and the cases in the file show that a violation is harmful (wrong-branch latch or runt). New `join_nd`: r, ctl_req and s maps non-monotone (lo < hi); feedback box [50,150] with run at 100; uj1 fires at 1600, uj0 is 0 forever |
| 5 | `sel_box_exact` (+ `unsel_box_exact`, `decode_exact_all_tokens`) (LibGapMuxN) | CONFIRMED (H_YOSYS_MAP) | New `muxn_nd`: both index pins and ctl_req non-monotone (lo < hi), every left-side hypothesis holds, join 2 fires at 1400. The request, decode->join and feedback maps are constant (fixed by the trace constructor) inside lo < hi boxes |
| 6 | `third_box_exact` (LibGapMuxN) | CONFIRMED | Iff under H_S_STEP (one clean change per bit); necessity via `maps_needed` at u = max(Cr+Clo, T0+Alo); `witness_third` |
| 7 | `box_exact_flushed` / `_no_early` (LibGapDelay) | CONFIRMED, conditional | Iff only under H_BAL_HI, H_LO_ORDER, H_START (and H_SHORT). The JSON states this in `exact_under`, and `rescue_*` shows those conditions are needed. `real_ok` already has a non-point box (500..624, 310..388). Necessity via `fits_corner` |
| 8 | `box_exact`, `odd/o5/o6_box_exact`, `box_exact_edges`, `strict_edges` (LibGapLatch) | CONFIRMED | Necessity via `mk_trace` and `Rd.two` (a two-phase map in the box). New `latch_nd`: d and en maps non-monotone over [300,700] and [400,800], setup_pulse and hold at slack 0, power-up 0, captures 1 at every closed-enable read (4200 and 4201 are such instants) |
| 9 | `reset_box_exact`, `c2_box_exact` ... (NecessityReset) | CONFIRMED (scope) | Iff for inputs HELD at a non-enabling vector (H_IN_HELD), any power-up. Moving inputs are outside this theorem (disclosed). The JSON form `Rhi + Qhi + 1 <= W + Rlo` is the box condition plus the Kleene +1 (CElemStrict2 `reset_width_strict`). New `reset_nd`: rst map non-monotone over [100,300], power-up 1, 0 from 300 on, forever |
| 10 | `idx_setup_iff` (RigIdx) | CONFIRMED, conditional | Side conditions: Tlo > 0, bands at most one period wide, H_RST_LONG_EN, H_SHORT. `idx_nonvacuous` has lo < hi bands (rst [1200,4800], idx [900,4200], en [150,1125], LUT [100,500]). The run uses transport delays inside the bands, and `cex_rig` meets every Rig field |

No theorem was REFUTED or VACUOUS.

## 3. Mutation (copies in `_Mut2/`, `lean -DautoImplicit=false` against the bchk oleans)

| mutant | change | breaks at |
|---|---|---|
| M1 | bd_c2 INIT 00E8 -> 00E0 (follow bit a=b=1,q=0) in `c2F` | `c2_facts_dec` (decide, l.349) |
| M2 | `env_latency_iff` RHS `+1` | omega l.293, 302, 311 |
| M3 | steer INIT ...2222 -> ...2223 (O5 high with no request) | `outB_eq` l.93, `spurious_token` |
| M4 | `steer_box_exact` setup `+1` | l.200, 207 |
| M5 | `join_box_exact` hold `+1` | l.412, 418 |
| M6 | latch odd INIT B8 -> B9 | `odd_eq` l.108, `odd_iff` |
| M7 | latch `box_exact` hold `+1` | l.425, 469, 521, 534, 551 |
| M8 | bd_c2 INIT for `Fc2` E8 -> EA (hold bit) | `cells` (decide, l.270) |
| M9 | `reset_box_exact` `+1` | l.221, 280, ... |
| M10 | muxn SEL0 10 -> 11 | `dec_eq` l.132 |
| M11 | `third_box_exact` middle disjunct `+1` | l.723 |
| M12 | `idx_setup_iff` `+1` | l.339 |
| M13 | H_GFLUSH (`GF`) `+1` | l.278 (sufficiency), `real_bad` l.683 |

13/13 mutants break, each at the mutated obligation or INIT fact.

## 4. JSON name check

All 1399 `lean` citations with a local path resolve to a declaration of that name in that
file. The other 4 point to `audit/lean/B/W_CElem.lean` on `origin/claude/audit` (`branch` field
set); `drop_env_latency_cex` exists there. Every `exact` citation from the audited files is an
iff (↔ in the statement). Outside the audited files, five `exact` citations are not iffs:
ArbHandover `overlap_duration_r2_to_r1`, ArbCorners `overlap_C` and `corner_no_overlap`,
ArbBinary `settled_exclusion`, MuxRtzTimed `rtz_exact_safe`; LibCtlMergeMux `steer_excl_K`
(on bd_steer rows next to LibGapSteer's iff) is a sixth. Their role label should be checked by
their owners.

## 5. Not done
- A witness with a non-constant FEEDBACK read map (all trace constructors fix the loop delay).
- Sufficiency of CElemStrict under a window or non-monotone feedback channel. The argument
  carries over (the feedback reads n once t - d >= tb + wb), but it is not proved.
- The correlated-corner versions (every box necessity takes pins independent, as disclosed).
