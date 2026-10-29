# B-gcd-arb-kappa-tight (probe Bkx19): the exact κ threshold of gcd_hw's binding arbiter row

Shard B, 2026-10-29. Answers audit row 19 (`claude/audit` `audit/findings/P7-kappa.md`, row
OnGcdArbKappa, "tight" mildly OVERSTATED, and "Model remarks (kappa)" (b)).
Files:
- `formal/lean/Formal/Cells/OnGcdArbKappaTight.lean`: core Lean (no Mathlib), checks.
- `formal/lean/Wip/Bkx19/OnGcdArbKappaTightA.lean`: bridge to `OnGcdArbKappa`'s own
  (Mathlib) objects. Written, NOT checked (see Check status).
- Scratch scripts in `/tmp/claude-0/probes/Bkx19/`: `a2d.py` (global search), `ex.py`, `wit.py`,
  `cert.py`, `dE.py`, `cons.py`, `genlean.py`.

## Answer

The binding row is seed 3 `merge12.uarb1`, RT1b server-free, `lit` reading:

    d(rg2) + d(ag2r)  ≤  d(qgw) + d(pqg) + d(rs2) + d(aR2) + d(ag1q)      (fs, one delay per arc)

| | κ·749546 | κ |
|---|---|---|
| OnGcdArbKappa κ\* (real relaxation, safe proved up to here) | 33174 | 0.0442588 |
| **κS (safe proved up to here, this probe)** | **33176.932320** | 0.0442627034 |
| **κ_ex (exact ℕ-model threshold, irrational)** | 33176.93232062… | 0.0442627034 |
| **κU (a violation proved from here, this probe)** | **33176.932321** | 0.0442627034 |
| violation at the fast endpoint c = 0 alone would start at (script) | 33178.3557 | 0.0442646 |
| OnGcdArbKappa κu (violation proved from here) | 33181 | 0.0442681 |

- **(1) Gap closed.** For every κ ≤ κS, no realization of A's corner model violates the row
  (`rt1b_safe`). For every κ ≥ κU some realization does (`rt1b_unsafe`), by 1 fs.
  κU − κS = 1/749546000000 (1.3e-12). So in (κ\*, κu) a violating assignment exists exactly for
  κ > κ_ex, to within 1.3e-12. There is none on (κ\*, κS], and there is one on [κU, κu).
  `kex_bracket` shows that κ_ex is the root, between κS and κU, of
  `(D1F2 − D2F1)(1−κ²) + D2·327052·(1−κ) − D1·217299·(1+κ) = 0`
  (F1, D1 = 313186, 665000 for rg2; F2, D2 = 227360, 527000 for rs2). That is, κ_ex is the
  crossing of two step curves: rg2's floor step `(1+κ)n_rg2(c) = 327052` and rs2's ceiling
  step `(1−κ)n_rs2(c) = 217299`. They cross at corner c ≈ 5.099e-6. This interior corner
  binds, not the fast endpoint. The discriminant is not a square, so κ_ex is irrational
  (script).
  - Why κ\* itself is not the threshold: OnGcdArbKappa's κ\* is the real-delay bound. With
    whole-fs delays, a violation needs ≥ 1 fs after flooring every data arc and ceiling every
    request arc. That needs a corner where the five request arcs' ceilings and the two data
    arcs' floors all fall favourably.
  - The whole difference, κ_ex − κ\* ≈ 3.9e-6, is an artefact of the 1 fs grid. With real-valued
    delays the threshold is κ\* exactly (not proved here).
- **(2) Gate level.** `rt1b_gate_unsafe`: for every κ ≥ κU there is a realization `dU`, a 7j
  delay record `DU` realizing it (`OnGcdArbFix.Real2`), a run `SU` of 7j's gate relations,
  and the scenario `Scn2` for every horizon past 259353 fs. The run uses the real INITs, holds
  at every t ∈ ℤ and includes the server relation. In it g1 and g2 are both high at
  t = 374043 fs (`SU_overlap`, through 7j's own `rt1_counter2_minserver`).
  `rt1b_gate_safe` is the other side: for κ ≤ κS, every record realizing the row and every
  server give grant exclusion (via `OnGcdArbFix.excl2`). So the gate-level threshold of this
  row, in 7j's model, is the same κ_ex, to 1.3e-12.
  - **Caveat (it matters for what the 0.0443 means).** The counter-record has `smin = 0`,
    `wa0s = 0`, `qr = 0` and q prefix `cq = 0`. RT1b's full condition is
    `m2 + smin + wa0s + qr + cq ≥ 0` (`OnGcdArbFix.rt1b_iff`). The server-free form drops the
    server, the A0 route to ustate and ustate's own O6 arc. The model allows that, since every
    `smin ≥ 0` is a valid server. But the binding 1 fs violation becomes an overlap only when
    those terms are 0. If they are the corner-model delays of the arcs `srv`, `ac`/`dS2`/`es`/
    `ps` and `aq` (H_SERVER_GRAPH, OnGcdArbKappa's `rt1bs_gate`), this arbiter's RT1b is the
    RT1bs row, and its κ\* is 0.651. The design's lit minimum is then 0.0802 (seed 2
    merge3.uarb1, h21, `OnGcdArbKappa.lit_srv_min`), not 0.0443.
  - So 0.0443 is tight for the server-free form and for 7j's model taken over all servers. It
    is not tight against a trace whose server, A0 branch and q arc are themselves
    corner-model delays.
- **(3) The spread hypothesis.**
  - `lit` puts each arc's corner endpoints at FAST_MIN and SLOW_MAX. At κ = 0.0443 the fast
    corner then allows rg2 only up to 1.0443 × 313.186 ps. prjxray's within-corner range for
    rg2 is 313.186..382.186 ps (+22 %); for ag1q it is +31 %.
  - **H_SPREAD_CORRELATED** (`OnGcdArbKappaTight.H_SPREAD_CORRELATED`): the within-corner
    min..max spread is die-wide. It is carried by the shared corner c, and only the residual
    per-arc scatter is bounded by κ. Under it the row is safe for κ ≤ κS
    (`spread_correlated_safe`).
  - **H_SPREAD_INDEP**: each arc's endpoints lie anywhere in its own within-corner ranges,
    independently of the other arcs. It admits the `cons` arcs (`consArc_indep`), and the row
    then fails at every κ, κ = 0 included (`spread_indep_fails`, `spread_indep_not_safe`). At
    the fast endpoint the data side is 438.186 ps at FAST_MAX and the request side 391.360 ps
    at FAST_MIN, a −46.8 ps margin.
  - `cons_rows_k0` gives the other four cons rows that fail at κ = 0, as endpoint arithmetic:
    seed 2 merge3.uarb1 RT1b −29.0 ps, h21 −8.8 ps, o1x −11.8 ps (fast); seed d merge9.uarb1
    RT1 −21.0 ps (slow). That makes 5 rows on 3 arbiters, as OnGcdArbKappa claims.
  - With the server credited (RT1s/RT1bs, cons, κ = 0, endpoint arithmetic in `cons.py`, not
    Lean), the three server-free rows pass with ≥ +1.35 ns. Only seed 2 merge3.uarb1 h21/o1x
    (the bare-cell handover race, no server in it) stay negative.
  - So the cons alternative, read with the server credited, gives one arbiter (seed 2
    merge3.uarb1) that fails for every κ.

## Problem statement

**Assumed.**
- A's corner model, from `CornerNat`, restated verbatim in core Lean. The hypotheses are
  H_ENDPOINTS, H_AFFINE, H_SHARED_CORNER and H_SCATTER κ, with one whole-fs delay per arc per
  run (rise = fall).
- The seven arcs' prjxray numbers, copied from `OnGcdArbKappa.v_g3_merge12_uarb1` (UNTRUSTED
  extraction of probe Bar; the routes are not on disk).
- The form `F_rt1b` (netted, H_DISJ).
- For the gate theorems, 7h/7j's model (`Run`, `Scn2`, `Dl`'s hypotheses) and H_INST
  `Real2`.
- For (3), H_SPREAD_CORRELATED or H_SPREAD_INDEP as stated.

**Proved (core Lean, checks).**
- `allOK_of_chk` (generic): a finite list of corner points with per-point checks, open-interval
  checks and a real-relaxation tail. It is sound for every rational corner and every whole-fs
  realization.
- `scat_mono`: κ-monotonicity.
- `rt1b_safe` (κ ≤ κS) and `rt1b_unsafe` / `rt1b_not_allOK` (κ ≥ κU).
- `kex_bracket`, `kS_kU_inside`.
- `rt1b_gate_safe` and `rt1b_gate_unsafe`.
- The §6 spread theorems.
- Non-vacuity: `rt1b_safe_nonvacuous` (κS realised at the fast corner), `spread_nonvacuous`.
  The gate counter-trace is itself a witness that `Run`/`Scn2` are jointly satisfiable with
  this record.

**NOT covered.**
- That the restated model is A's: this is definitional by construction (same fields and
  formulas), but `scat_iff` (`Iff.rfl`) and the transfer to `OnGcdArbKappa.model … .lit F_rt1b`
  over all 35 arcs are in the unchecked bridge.
- The other 1295 rows (only this row is decided exactly; every other row keeps OnGcdArbKappa's
  sandwich, gap ≤ 1.8e-5).
- The exact thresholds of the server-credited forms.
- A gate-level trace in which the server, the A0 route and ustate's O6 arc are also
  corner-model delays.
- Per-edge scatter, Kleene X, metastability, the extraction, and κ itself (unmeasured).

## Method (why the safe side is a finite check)

- At a fixed κ and corner `t = w1/(w0+w1)`, the worst whole-fs assignment puts data arcs at
  ⌊(1+κ)n(t)⌋ and request arcs at ⌈(1−κ)n(t)⌉. These steps are piecewise constant in t, with
  rational step points.
- `chk` takes the 44 points `(0, step points in (0, 26229e-9), 26229e-9)` and checks:
  - at each point, the floors/ceilings at that point;
  - on each open interval, the right point's ⌈⌉−1 for data and the left point's ⌊⌋+1 for
    requests. These are exact when no step lies strictly inside the interval.
  - beyond the last point, the real relaxation `(1+κ)D(t) − (1−κ)R(t) < 1 fs`, checked at
    `t_last` and at `t = 1` (it is affine in t).
- The check is `decide +kernel` over GMP naturals (about 26 s for the whole file).
- The certificate is exact: the same check run at κU fails on 3 intervals (`cert.py`).
- Mutations, all killed: κS numerator +1; `dU` rg2 +1; ag1q's FAST_MIN −1.

## The test that decides lit vs cons (H_SPREAD_CORRELATED vs H_SPREAD_INDEP)

The two readings differ only in **how the prjxray within-corner spread is distributed within one
die at one PVT point**. A GLS cannot decide this, because it is handed one number per arc. The
board can.

**T_SPREAD (board).**
1. On one die, at one fixed temperature and voltage, measure N ≥ 30 routed path pairs with a
   carry-chain TDC or as ring-oscillator periods (counter against the PS clock). Each pair is
   two different arc mixes. Include the binding row's own two sides: rebuild seed 3 with
   merge12.uarb1 placed and routed as in the bitstream (FASM-locked), and launch r2 from a
   flop, timing r2 → ugrant O6 against r2 → ustate O5 → q → ugrant O5. Add pairs of the other
   dominant arc types (CLB site pins, INT pips, LUT O5/O6).
2. Fit one corner c for the die by least squares on all paths, against prjxray's lerp
   `(1−c)·FAST_MIN + c·SLOW_MAX`.
3. Compute each path's residual `ρ_i = d_i / n_i(c) − 1`.
4. Decide:
   - **lit / H_SPREAD_CORRELATED holds at κ** if every |ρ_i| ≤ κ, in particular ≤ 0.0443 for
     the binding row. The within-corner spread is then a die-wide shift.
   - **cons / H_SPREAD_INDEP** is indicated if residuals reach the within-corner range
     (|ρ| ~ 0.1–0.3).
   - For the binding row the direct observable is the ratio r = (rg2 + ag2r)/(qgw + pqg + rs2 +
     aR2 + ag1q). lit at κS predicts r ≤ 1 at every corner (r = 0.915 at the fast endpoint
     nominal, 0.860 slow); cons allows r up to 1.12 at the fast corner.
5. Repeat at two more temperatures (heater or fan) to check that ρ_i does not move with c,
   i.e. that the residual is not itself corner-dependent.

**GLS checks (gate-model fidelity, not the reading).**
- (a) Run `cells/gls` on the seed-3 route with the binding arcs set to the cons values (SDF
  edit: rg2, ag2r at FAST_MAX; qgw, pqg, rs2, aR2, ag1q at FAST_MIN), with a zero-delay
  testbench server. 7j predicts NO overlap: the routed A0 route to ustate (≥ 395.8 ps at
  FAST_MIN) plus ustate O6 (45 ps) exceed the −46.8 ps margin. This shows the server-free
  row's pessimism.
- (b) Additionally zero `wa0s`, `qr` and the q prefix in the SDF. 7j then predicts a g1/g2
  overlap on `[G1b, G2b)` (`overlap_exact2`, `rt1_counter2`). Its width is
  `min(46.8 ps, d(ag2r) − d(ag1q)) = min(46.8, 56 − 48) = 8 ps`, because at these values g2's
  fall comes through q first. This confirms the gate model's trace, which the 1 fs lit
  counter-trace cannot do at ps resolution.

## Check status

- `/tmp/claude-0/btools/bcheck.py Formal/Cells/OnGcdArbKappaTight.lean`: **OK**, no warnings.
- `formal/scan.py` on the file: clean.
- `#print axioms` (companion file, since removed): `rt1b_safe`, `rt1b_unsafe`,
  `rt1b_not_allOK`, `rt1b_gate_safe`, `rt1b_gate_unsafe`, `allOK_of_chk`, `scat_mono`,
  `spread_correlated_safe`: [propext, Classical.choice, Quot.sound]. `spread_indep_not_safe`:
  [propext, Quot.sound]. `rt1b_safe_nonvacuous`, `spread_indep_fails`, `spread_nonvacuous`:
  [propext]. `kex_bracket`, `kS_kU_inside`, `cons_rows_k0`: none.
- Bridge `Wip/Bkx19/OnGcdArbKappaTightA.lean`: **NOT checked**. The Mathlib oleans needed by
  `CornerNat` (Mathlib.Tactic.Linarith/Ring) exist, but `bcheck.py` adds
  `.lake/packages/proofwidget/...` to LEAN_PATH while the package directory is
  `.lake/packages/proofwidgets`. Every Mathlib-closure file therefore fails with "unknown module
  prefix 'ProofWidgets'" (ConstraintsKappa too). Once the checker path is fixed, check the
  bridge and move it to `Formal/Cells/`. Proof-script risk: `cases e <;> rfl` on `arc_eq` and
  the 35 `decide`s of `dE_realizes`.


**Update (lead, 2026-10-29 09:50):** the Mathlib bridge OnGcdArbKappaTightA.lean now checks (the checker path bug was fixed: proofwidgets) and is in Formal/Cells/.
