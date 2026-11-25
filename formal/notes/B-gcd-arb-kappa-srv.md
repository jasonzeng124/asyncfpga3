# B-gcd-arb-kappa-srv (probe Bsrv): gcd_hw's arbiters at gate level with the server credited

Shard B, 2026-10-29. Follows `notes/B-gcd-arb-kappa-tight.md` (Bkx19) and `notes/B-gcd-arb-kappa.md` (Bk3).
Files:
- `formal/lean/Formal/Cells/OnGcdArbKappaSrv.lean` (1054 lines, Mathlib closure through
  `OnGcdArbKappa`). Checks.
- Scratch scripts in `/tmp/claude-0/probes/Bsrv/`:
  - `data.py`: parses OnGcdArbKappa's data, forms and rows, and recomputes all 1296 κ\*;
  - `exact.py`, `refine.py`: the exact whole-fs threshold by bisection;
  - `gen.py`: the certificates, plus a mirror of the Lean checks;
  - `wit.py`: the witnesses;
  - `gentail.py`, `head.lean`, `tail_tmpl.lean`: assembly of the Lean file;
  - `drv.py`: what drives A0 in the four synth netlists.

## Answer

Here "server credited" means the server-free RT1/RT1b forms are replaced by RT1s/RT1bs. In
RT1s/RT1bs, the following are all delays of one corner-model realization:
- the A0 branch to ustate (`ac+dS1+dS2+es+ps`);
- ustate's O6 arc (`aq`);
- the q prefix (`cq`);
- the server's graph path (`srv`, with H_SERVER_GRAPH `d srv ≤ smin`).

Every threshold below uses the `lit` reading (H_SPREAD_CORRELATED) and is exact on the 1 fs
grid to 10⁻¹².

| design | forms | binding row | safe for κ ≤ (Lean) | violated from κ ≥ (Lean) | gate-level counter-run |
|---|---|---|---|---|---|
| **D1** = OnGcdArbKappa's conjunction, server credited | 16: forks, RT2/RT2b, RT1s/RT1bs, ArbPin2's h12/h21/o1x/o2x | seed 2 merge3.uarb1 **h21** | **κS1 = 0.080163500491** | κS1 + 10⁻¹² | bare cell (ArbPin, A0 low) at the realization's point box; the same race as a 7j run, with every delay realised, but not four-phase |
| **D2** = held arbiter, four-phase scenarios only | 12: forks (7g), RT2/RT2b with srv (7h/7j), RT1s/RT1bs (7h/7j) | seed 4 merge12.uarb2 **fork2** | **κS2 = 0.216552148868** | κS2 + 10⁻¹² | 7g run, through the exact `fork2_box_iff`: A2 fires spuriously |

### (1) Thresholds

- **Every row is safe up to its κ\*.** OnGcdArbKappa's certificates already cover every
  server-credited row (`row_safe`). This file re-certifies all of them at the design value:
  - `cert_D1a`, `cert_D1b`: all 36 arbiters × 16 forms at κS1;
  - `cert_D2a`, `cert_D2b`: all 36 × 12 at κS2.

  Only the binding row is above its own relaxation bound κ\*, so it needs the exact certificate.
- **h21, seed 2 merge3.uarb1** (D1's binding row): `rg2 + ag2r ≤ cq + qgw + pqg + rs2 + aq + ag1q`.
  - It binds at the SLOW end, where κ\* = 138217/1724217 = 0.0801622.
  - The exact threshold lies in (κS1, κS1 + 10⁻¹²], 1.3e-6 above κ\*.
  - Certificate: the new head-start check `chkH` over 147 corner points.
  - The q prefix `cq` (23.253 ps at every corner) is moved into the constants by `allOK_split`.
  - Witness `dE1`: all 35 arcs at the corner t = 1 − 1.1e-5. The violation is by 1 fs
    (856563 vs 856562 fs).
- **fork2, seed 4 merge12.uarb2** (D2's binding row):
  `d12 + e2 + p2 ≤ dS1 + es + ps + cq + qgw + pqg + gw2 + pg2 + aq + ag2`.
  - It binds at the FAST end, where κ\* = 121144/559431 = 0.2165486.
  - Certificate: Tight's `chk` over 73 points.
  - Witness `dE2`: corner t = 1.28e-5, violation by 1 fs.
- **Mutations, all killed:** κS1 +10⁻¹² (cert1 fails), κS2 +10⁻¹² (cert2 fails), and
  `dE1` rg2 +1 fs (the realization check fails).

### Gate level

- **D1 safe**: `design_gate_srv`. For κ ≤ κS1, on every arbiter and every realization:
  - both A0 forks are safe (7g);
  - A1/A2 are exclusive across both handovers (7h/7j), for every server no faster than `srv`;
  - g1/g2 are exclusive across both handovers (7h/7j, RT1s/RT1bs), for every record whose A0
    branch, O6 arc and q prefix are the realised ones;
  - the bare cell is exclusive for every per-pin behaviour, in all four request scenarios.
- **D1 unsafe**: `h21_gate_unsafe` / `design_srv_tight`, for κ ≥ κU1.
  - The realization `dE1` has q→O5 faster than q→O6 (`ag1q` 109.460 < `ag2` 133.939 ps).
  - ArbPin2's `h21_kfail` then gives a transport behaviour of `bd_arbcell` on the point box
    (real INITs, r1 waiting, r2 released) with both grants high.
- **7j's gate relations**: `h21_7j_bare`.
  - `D7` is the 7h/7j record of `dE1`, with every route and arc realised:
    `Real7 (xOfB dE1) D7`, server `smin = d srv` = 3.797 ns, and no zero arc except those
    the data makes zero (dS1, dS2, d12).
  - `S7` is a run of 7j's gate relations (real INITs, every t ∈ ℤ, `Server` included). In it
    g1 and g2 are both high at 856562 fs.
  - **But A0 never rises in `S7`**, and client 2 withdraws a request that was never
    acknowledged. So `S7` is not a four-phase run: no `Scn2`.
  - In 7j's four-phase handover (`Scn2`, which assumes H_SETTLED), the A0 hold covers this
    race. For the same arbiter the r2→r1 handover is then RT1bs, safe up to κ = 0.769
    (`g2m3_held_rt1bs`).
  - **So D1's 0.0802 is a bare-cell (H_A0_LOW) number.** It binds only if gcd_hw ever runs the
    bare race, which takes either a withdrawn request or A0's rise reaching ustate after
    client 2's release (H_SETTLED violated).
  - For this arbiter H_SETTLED's arcs favour the hold at small κ. A0 reaches ua2 later than
    ustate (p2 172–506 ps vs ps 110–351 ps), plus ua2's arc. This is script arithmetic: no
    Lean theorem about H_SETTLED is proved here.
- **D2 safe**: `design_gate_held`, the held part of the above, for κ ≤ κS2.
- **D2 unsafe**: `fork2_gate_unsafe` / `design_held_tight`, for κ ≥ κU2. At `dE2`,
  `¬ Safe2 (xOf dE2)`: some 7g run (real INITs, per-pin transport delays of `dE2`) fires A2
  spuriously. This follows from 7g's exact `fork2_box_iff` and `xin_point` (a point box
  contains only its own record).
  - The 7g model has no server: fork2 contains no `srv`.
  - 7g is a separate gate model, not 7j's `Run`. 7j's `rt2_counter2` is the corresponding
    A2-stuck counter for RT2b. I did not build a 7j counter-run for fork2.

### (2) Design statement

- **lit (H_SPREAD_CORRELATED):**
  - D1: all 36 arbiters are safe at gate level for κ ≤ 0.080163500491 and unsafe from
    +10⁻¹² (bare cell).
  - D2: safe for κ ≤ 0.216552148868 and unsafe from +10⁻¹² (7g A0 fork).
  - Non-vacuity (`design_nonvacuous`): κ = κS1 and κ = κS2 meet the hypotheses, the fast
    endpoints realise every model, and the loop hypotheses hold on all 36 arbiters.
- **cons (H_SPREAD_INDEP):** `cons_srv_neg`.
  - Among the 16 server-credited forms, the rows failing at κ = 0 are **exactly** seed 2
    merge3.uarb1 h21 and o1x. Both have `pu = 0`, so they fail at every κ
    (OnGcdArbKappa `row_verdict`). This confirms the script.
  - Every other cons row passes at κ = 0, and none of the D2 forms fails.
  - So under cons, D1 has no safe κ.
  - D2's cons minimum is 0.1288 (seed 4 merge12.uarb2 fork2). That is the relaxation κ\* from
    the script, not an exact threshold.
  - cons is a per-form reading, not one model, so it has no gate-level design theorem (as in
    OnGcdArbKappa).

### (3) The server

- **What drives A0.** From the four synth netlists (`formal/tools/fasm2lean3/fixture/gcd_hw_{2,3,4,d}.synth.json`,
  read with `drv.py`): every merge's last-stage A0 (`z_ack`) is driven by a `bd_c2` C-element,
  `ucontrol_mergeN_f.u.genblk1.g2.u.u` (INIT 00E8…, own output on I2). It is the ack-join of the
  fork `ucontrol_mergeN_f` that consumes the merge's output.
  - Its other inputs are the two consumers' acks, for example `ucontrol_merge4` and the C-tree
    `ufork15…g3` for merge3.
  - merge12 is a 3-input cascade: uarb1's A0 is uarb2's A1 (uarb2's `ua1` C-element).
- **What the server delay is.** R0 → `uor`/`udly` matched delay → z_req → the fork → both
  consumers → their acks → the C-join.
- **What the theorems assume.** H_SERVER_GRAPH: the server answers no faster than `srv`, the
  min routed path from ustate O5 (R0) to that A0 driver's output. srv runs 0.588 ns
  (FAST_MIN) to 11.2 ns (SLOW_MAX) over the 36 arbiters.
- **Where its bounds come from.** The same extraction as every other arc: probe Bar's
  `a0extract` over C-10j's routed timing graph, prjxray-priced.
  - C-10j's 0.772 × SDF fallback (H_FALLBACK_BAND) applies to arcs prjxray does not price.
    Bar's scratch scripts are gone, so I cannot say which arbiters' min paths contain a
    fallback arc.
  - It is a lower bound over causal paths (H_CAUSAL_PATH), not a measured latency.
  - Treating it as one corner-model arc is conservative. A sum of per-arc κ-scatters is
    within κ of the summed nominal. The min over paths of affine nominals is concave in the
    corner, so its chord, which is what `lit` uses, underestimates it at interior corners.
- **Sensitivity.** Neither binding row contains `srv`. The rows that do (RT2/RT2b, RT1s/RT1bs)
  have lit κ\* ≥ 0.4307 (seed 4 merge12.uarb1 nG).
  - They stay above κS2 as long as the real server is at least ~25 % of `srv` (script).
  - With srv = 0, seed 2 merge10.uarb1 mG fails at κ = 0. This is the known server-free RT2
    failure, so the server credit is load-bearing for RT2.

## Problem statement

**Assumed.**
- A's corner model, as in OnGcdArbKappa / Tight:
  - H_ENDPOINTS from Bar's UNTRUSTED extraction;
  - H_AFFINE, H_SHARED_CORNER, H_SCATTER κ;
  - whole fs, rise = fall, one delay per arc per run.
- The `lit` reading (H_SPREAD_CORRELATED).
- The gate models and their hypotheses:
  - 7g `Run` (H_LOOP_*);
  - 7h/7j `Run`/`Scn`/`Scn2`/`Server` (H_SETTLED inside `Scn`/`Scn2`);
  - ArbPin `Cell` (H_A0_LOW: ustate's A0 and rst pins at 0).
- The record realisations `Real7`, `Real1`/`Real2` plus the A0-branch, O6 and q-prefix
  equations.
- H_SERVER_GRAPH.

**Proved (Lean, checks).**
- `allOK_of_chkH` (generic head-start certificate) and `allOK_split` (constant arcs).
- `h21_safe` / `h21_unsafe` / `h21_inside`.
- `h21_gate_unsafe`, `h21_7j_bare`, `g2m3_held_rt1bs`.
- `fork2_safe` / `fork2_unsafe` / `fork2_inside` / `fork2_gate_unsafe`.
- `design_srv_holds`, `design_held_holds`, `design_gate_srv`, `design_gate_held`.
- `design_srv_tight`, `design_held_tight`, `design_nonvacuous`, `cons_srv_neg`.

**NOT covered.**
- Whether gcd_hw ever runs the bare race (H_A0_LOW with a request falling). H_SETTLED is a
  hypothesis of 7h/7j, not proved from the routes, and it involves the client's own release
  latency, which is not extracted.
- A 7j (rather than 7g) counter-run for fork2.
- The server's real latency.
- The exact thresholds of the non-binding rows: they are certified safe at the design κ,
  and each is decided to within 1.8e-5 by OnGcdArbKappa.
- Per-edge scatter, Kleene X, metastability, the extraction, and κ itself.

## Check status

- `/tmp/claude-0/btools/bcheck.py Formal/Cells/OnGcdArbKappaSrv.lean`: **OK**, no warnings.
  The run took about 100 s, including the wait for a slot. `formal/scan.py` is clean.
- `#print axioms` (companion file, since removed):
  - `[propext, Classical.choice, Quot.sound]`: every headline theorem;
  - `[propext, Quot.sound]`: `allOK_split`;
  - `[propext]`: `design_nonvacuous`, `fork2_inside`;
  - none: `cons_srv_neg`, `h21_inside`.
