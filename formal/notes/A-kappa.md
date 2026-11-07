> **Correction (2026-10-27 ~07:00):** the ring ratios behind κ ≥ 0.311 are
> measured/predicted against SDFs written *before*
> `patches/nextpnr-xilinx-lut-perm-sink.patch` (shard C,
> `notes/C-10c-prjxdelay.md`): those SDFs charged 0–150 ps for permuted LUT pins
> where the routed hop is ~295 ps, on ~85% of chain hops. Against corrected
> predictions, comparable rings agree to 1.1% (prjxray median) / 6.7% (current
> SDF), population against population. So the 0.311 bound measures that SDF bug,
> not silicon scatter, and does **not** refute the per-path hypotheses of
> `ruleE_sound`/`ruleA_sound_rel`. κ (per path and on differences) is unmeasured
> on the current toolchain; the per-ring data and bitstreams needed to redo it
> are not in the tree.

# A / kappa: an estimator for the Corner model's local scatter

PROGRAM.md Phase 1, item A: "Write the κ estimator so it can run on per-route two-path data".

Files:
- `formal/tools-A/kappa/kappa.py`: the estimator. Python 3, stdlib only (there is no numpy on this machine).
- `formal/tools-A/kappa/data/`: every ring or two-path dataset found in the repo, each with a provenance header.
  - `ro_top_2026-08-03.csv` and `ro_top_2026-08-23.csv`: per-ring periods, measured and predicted, for two
    `ro_top` routes (cells/hw/README.md).
  - `ro_many_2026-08-23_summary.csv`: the 128-ring per-class table (cells/hw/README.md).
  - `shmoo_ucmpi1_pairs.csv`: two-path censored data, derived from `cells/hw/shmoo_ucmpi1_results.tsv`
    (origin/claude/research).
  - `f1_rings_ro_*.rebuild.tsv`: copies of `research/data/fid/f1_rings_*.tsv` (origin/claude/research).
    They hold predictions only (nextpnr, prjxray fast-min and slow-max) for **rebuilt** routes.
  - `pairs_template.csv`: the empty two-path schema.
- this note.

No Lean was written. The pair bound is already the theorem `Formal.Core.Corner.ring_kappa_lower`
(formal/lean/Formal/Core/Delay/Corner.lean). Below I list the two small lemmas that would make the rest of
the tool's logic theorems.

## Commands

    cd formal/tools-A/kappa
    python3 kappa.py selftest          # 8 groups of checks, prints PASS/FAIL, exit 0/1; ~3 s
    python3 kappa.py repo [--json F]   # every dataset in data/, output reproduced below
    python3 kappa.py rings FILE...     # a ring/absolute-path population (grouped by die, session)
    python3 kappa.py pairs FILE [--scale s] [--trust-pass]
    python3 kappa.py summary FILE      # the published per-class quantile table
    python3 kappa.py rawlogs build/hw/ro_many_top/raw --pred PRED.tsv   # once the raw logs exist
    python3 kappa.py model FILE        # predictions only: how proportional are F, S and P?
    python3 kappa.py --help            # also prints the schemas

`selftest` passes, with 0 failures.

## The model

This is the model of `formal/notes/A-delay-corner.md`. The estimator never assumes more than it does.

- **SharedCorner.** All paths of one (die, session) share one corner. In proportional form the nominal
  delay is `D_i = s·P_i`. In affine form it is `D_i(c) = (1−c)F_i + cS_i` with `c ∈ [0,1]`.
- **LocalScatter κ.** `(1−κ)D_i ≤ d_i ≤ (1+κ)D_i`. This is `Scat κ D d` in Corner.lean. The scatter is
  relative to the **nominal** delay.
- **Common offset θ0.** Optional, and a systematic term: `d_i = s·P_i(1+ε_i) + θ0`. It is what the 988 ps
  intercept in the 128-ring fit would be.
- **Additive scatter θ.** Optional, and a random term: `|d_i − sP_i| ≤ sθ`. This is rule A's `θ` in
  `ruleA_sound`. It is a different object from θ0, and the tool keeps the two separate.

**Convention warning.** `cells/hw/ro_many_measure.py` (and so README/tighten.py's "|resid| p90 25.2 %,
max 34.6 %") defines the residual as `(m − kP)/m`, relative to the *measured* value. Corner's ε is
`m/(sP) − 1`, so `ε = resid/(1−resid)`. The 34.6 % ring is therefore ε = +52.9 % under the global LS scale,
not 34.6 %. A-delay-corner.md quotes the 25.2 %/34.6 % figures as if they were κ. They are not in κ's
convention.

## Estimators, and what each one assumes

### 1. The distribution-free pair bound, `kappa_min`

**Derivation.** Assume, for paths i and j:
- both on one die, in one session (one `s`);
- ratios `r = m/P` with `P > 0`;
- `|ε| ≤ κ ≤ 1` for both.

Then `r_i ≤ s(1+κ)` and `r_j ≥ s(1−κ)`, so `(1−κ)r_i ≤ s(1−κ)(1+κ) ≤ (1+κ)r_j`, that is
**`r_i − r_j ≤ κ(r_i + r_j)`**. This is exactly `ring_kappa_lower` (hypotheses `Scat κ s r_i`, `Scat κ s r_j`,
`−1 ≤ κ ≤ 1`). Over a whole population the best pair is (max, min), giving
`κ_min = (r_max − r_min)/(r_max + r_min)`.

**The bound is sharp.** At `s = (r_max+r_min)/2` and `κ = κ_min`, every r in `[r_min, r_max]` satisfies
`Scat`. So κ_min is the *smallest* κ consistent with the data under the model. The data can say nothing
more about the worst case: no finite sample gives an upper bound on a worst-case κ.

**Exact assumptions:**
- (a) **Shared scale.** The same `s` for both paths. This means one die and one session (one temperature
  and voltage), and the same route.
- (b) **Proportional nominal.** `D = s·P`. Under the affine form the bound holds for every fixed c, so
  `min_c κ_min(m/D(c))` is the valid bound; the tool computes it whenever F and S are given.
- (c) **No common offset θ0.** If θ0 ≠ 0, `κ_min((m−θ0)/P)` is the right quantity. The tool reports it at the
  fitted θ0, and also minimised over θ0's bootstrap 95 % interval. That minimum is sound for every θ0 in
  the interval.
- (d) **Measurement error.** Each observed ratio is within a relative η of the truth. The tool widens the
  bound to `(A−B)/(A+B)` with `A = max r/(1+η)` and `B = min r/(1−η)`. Rings: η = 2·10⁻⁴ for ro_top
  (0.01–0.02 % window reproducibility) and 5·10⁻⁴ by default (ro_many 0.052 %).
- (e) **Path-level scatter only.** A ring is one path. By `path_scatter`, arc-level κ is at least the
  path-level κ, so the bound also bounds the arc κ from below.

What it does **not** assume: any distribution, independence, or s itself.

### 2. Quantile estimates (population statements, not worst cases)

- `ε̂_i = r_i/ŝ − 1`, with ŝ chosen three ways:
  - `global`: the median of all r;
  - `class`: the median within each length class, which absorbs any length-systematic term;
  - `offset`: from the θ0 fit.
- `κ̂_q` is the q-quantile of `|ε̂|`.
- **Confidence:**
  - a distribution-free one-sided **order-statistic UCB95**: the smallest order statistic x_(k) with
    `P(Bin(n,q) ≤ k−1) ≥ 0.95`. It needs n ≥ 29 for p90, n ≥ 59 for p95 and n ≥ 299 for p99, and the tool
    says "n/a" below those;
  - a stratified **bootstrap** interval of κ̂_90 that re-estimates ŝ on every resample.
- **Coverage.** The fraction of paths with `|ε̂| ≤` each limit.

### 3. Separating θ0 from relative scatter

The tool fits both models on the ratio scale: `r = a` (relative) and `r = a + θ0·(1/P)` (offset). In ratio
terms this is weighted least squares that gives every path equal weight. It also reports the
OLS-on-periods fit that `ro_many_measure.py` uses; this reproduces the README's −1596 ps and +2303 ps for
the two ro_top routes.

The tests:
- permutation p-value for θ0 ≠ 0;
- Spearman ρ of the residual against P under each model, with permutation p;
- per-class median ε under each model;
- verdict: RELATIVE, OFFSET, or OFFSET+TREND.

**Scatter shape.** The tool also fits `β` in `spread_ps ∝ P^β`, using per-class MAD of the residual in ps.
- β = 1 is relative κ (the Corner model);
- β = ½ is independent per-arc scatter averaging over the path;
- β = 0 is additive.

It also reports the pure-additive alternative: `θ_min = min_s max |m − sP|`, judged against rule A's
50 ps per path (100 ps per ring period).

### 4. Two-path (differential) data: the schema

There is one CSV row per pair. Path `a` must arrive **early** (data or select) and path `b` **late**
(request). Only the divergent tails are given, because the shared prefix cancels exactly (`ruleE_sound`'s C).

```
die,session,pair,class,meas_a_ps,pred_a_ps,fast_a_ps,slow_a_ps,meas_b_ps,pred_b_ps,fast_b_ps,slow_b_ps,meas_diff_ps,outcome,meas_rel_err
```

**Per pair:**
- **pair bound** `|r_a−r_b|/(r_a+r_b)` (when both absolute delays are measured);
- **differential κ** `κ_diff = |Δ/ŝ − (P_b−P_a)|/(P_a+P_b)`, where Δ is the measured `d_b − d_a`. ŝ is
  `--scale` or the session median of the absolute ratios. κ_diff is exactly the scatter projected onto
  the difference rule E/A compare. If each tail has `|ε| ≤ κ`, then `κ_diff ≤ κ`, but not conversely:
  correlated tails make κ_diff small;
- **censored outcomes:**
  - `FAIL_LATE_FIRST` (the request was seen no later than the data) gives `κ ≥ (P_b−P_a)/(P_a+P_b)`, and
    `κ ≥ (P_b−P_a−100)/(P_a+P_b)` with θ = 50 ps per path;
  - `PASS_EARLY_FIRST` (a rig that certifies the order) gives the mirror bound;
  - `PASS_UNCERTIFIED` gives nothing. `--trust-pass` shows what it would give.

The rule-E/A verdicts on pair data use the largest certain lower bound.

## Self-test (`python3 kappa.py selftest`): all pass

| # | data | checked |
|---|---|---|
| 1 | 2000 random small populations, κ ∈ [0, 0.5], η ∈ {0, 0.1 %, 1 %} | κ_min ≤ κ_true in **every** trial (soundness) |
| 2 | n = 128, κ = 0.15, θ0 = 0, uniform ε | κ_min = 0.149 ∈ [0.135, 0.15]; κ̂_90 = 0.129 ≈ 0.9κ; no spurious θ0 (p = 0.55); rule E not refuted, rule A refuted; β = 1.11 |
| 3 | n = 128, κ = 0.10, s = 0.938, θ0 = +988 ps | θ0 recovered (+1034, CI [821, 1246] contains 988); a = 0.937; verdict OFFSET; offset-model κ_min = 0.0995; ignoring θ0 inflates κ_min to 0.15 |
| 4 | **negative control**: κ = 0.30 | rule E **reported EXCEEDED** (κ_min = 0.293), and both rule-A limits too. Control: κ = 0.04 reports no limit exceeded |
| 4b | mixed model κ = 1/22, θ = 50 ps | feasible on its own data; one path 20 % slow makes it infeasible |
| 5 | affine, c = 0.37, S/F ∈ [2.8, 3.1], κ = 0.08 | strict affine κ_min = 0.0790; ĉ = 0.370; free-scale bound ≤ strict |
| 6 | 200 two-path pairs, κ = 0.12 | κ_diff, pair bound and censored bound are all ≤ 0.12; κ_diff max = 0.115 |
| 7 | 300 × n = 64 half-normal | order-statistic UCB95 covers the true p90 in 289/300 (96 %) |
| 8 | (1.470, 0.773) | 0.3107 = `guard_refuted_by_7link_rings`'s 0.697/2.243 |

## Results on the repo's data (`python3 kappa.py repo`)

**Where the data stands:**
- **The per-ring numbers of the 128-ring `ro_many_top` run are not in the repo**, on either branch. They
  would be `build/hw/ro_many_top/raw/gNN.log`. Only the per-class table is published. The research
  branch's `f1_rings_ro_many_top.tsv` holds predictions for a **rebuild** (a different route) and no
  measurements. Its own header says the board periods are not in the repo.
- The only per-ring measured+predicted data are the two 5-ring `ro_top` routes.
- The only two-path data is the ucmpi1 shmoo, and its results are binary and censored.

**Toolchain.** No routed number here was produced by me. The provenance of each one:
- The ro_top and ro_many routes' nextpnr fingerprints are not recorded in cells/hw/README.md.
- The rebuild TSVs are from nextpnr 9c732bc6303458df.
- The shmoo used NEXTPNR_SEED=1, with each row its own route.

| dataset | κ_min (certain lower bound, proportional, θ0 = 0) | with θ0 | model verdict | quantiles |
|---|---|---|---|---|
| ro_top 2026-08-03, n = 5 | **0.052** (ro4 0.997 vs ro1 0.899) | θ0 = +21 ps (ratio WLS), p = 0.99: none; 0.045 minimised over the θ0 CI | RELATIVE | κ̂_50 0.026, κ̂_90 0.071 (no UCB at n = 5) |
| ro_top 2026-08-23, n = 5 | **0.190** (ro0 1.346 vs ro4 0.915) | θ0 = +1963 ps (CI [+382, +2594]), p = 0.021; κ_min **0.057** (0.052 over the CI) | OFFSET (ρ −0.90 → 0.00) | κ̂_90: global 0.25, offset 0.06 |
| ro_many 7-link class, n = 32 (summary) | **0.311** (1.470 vs 0.773) | **still 0.311** for any common θ0 ∈ [0, 988] ps and any P in the rebuild's 7-link range [6704, 10052] ps | — (needs raw data) | slow side, class-centred: p90 +0.223, max +0.250 (= UCB95 of the slow-side p90 at n = 32); fast side −0.343 at the min |
| ro_many 15/31/63-link (summary) | not computable (no published min) | — | — | slow side p90 / max: 0.132/0.219, 0.131/0.191, 0.093/0.170 |
| ro_many all 128 | **≥ 0.311** | — | README: OFFSET (p 5.6e−5 → 0.39) | — |
| shmoo ucmpi1, 13 routes | **≥ 0.072** (n = 10: FAIL with predicted request 628 ps after data); 0.060 with θ = 50 ps | — | — | — |

**Two numbers that do not depend on measurement:**
- **Affine ≈ proportional here.** On the 128-ring rebuild, prjxray's S/F ranges only 2.81–3.06 per ring
  (`model`). Between proportional and affine, the corner can move a path ratio by at most about ±4 %. So
  the single-SDF and two-corner forms of rule E disagree by less than the scatter.
- **nextpnr and prjxray disagree by about as much as the silicon does.** On the same rebuild, the
  model-vs-model κ_min (nextpnr P against prjxray's midpoint) is 0.17 on 7-link rings, 0.14 on 15, 0.07
  on 31 and 0.07 on 63. A large part of the measured "scatter" may be prediction error that a better
  delay model would remove. That is a reason to run this tool against prjxray predictions of the
  *measured* route, once that route exists.

**Scatter shape.** From the summary, using approximate class P values, β ≈ **0.55**. The slow-side spread
in ps grows like √P, not like P. Under that reading the scatter is independent per arc and averages
down along a path, so relative κ grows as the path gets shorter.
- This contradicts the Corner model's constant κ across lengths only as a statistical shape. Corner's κ
  is a worst case, so a length-dependent κ is still sound if κ is chosen **per length class**, as the
  tool does.
- It does mean the short tails that rule E and rule A compare (1–3 links) are where κ is largest.
- Rough extrapolation from the 7-link class: κ̂_90 at about a 1.5 ns tail would be roughly
  `0.22 × (7.3/1.5)^0.45 ≈ 0.45`. This is speculative, because it combines approximate P, the slow side
  only, and an extrapolation.

## Are rule E's 19.9 % and rule A's 9.1 % met?

- **As the theorems state them (path-level LocalScatter), no.**
  - The 7-link rings of `ro_many_top` force κ ≥ 0.311. That exceeds rule E's 0.1988 and rule A's 0.0909
    (and the 1/22 + 50 ps mixed form: the additive θ alone would need ≥ 2336 ps per period). This holds
    with or without the 988 ps common offset, because both extreme rings are in the same length class.
  - ro_top's second route needs 0.190 without θ0, which exceeds rule A, and 0.057 with it.
  - So the *hypothesis* of `ruleE_sound` and `ruleA_sound_rel` is false for these paths, and those
    theorems do not apply to designs built from such paths.
- **That does not show rule E or rule A is unsafe.** Both rules compare **two tails on one route**, and the
  hypothesis they really need is about the *difference*: κ_diff ≤ 0.1988 (or ≤ 1/11). If the two tails'
  errors are correlated, as they are when they share arc types and neighbourhoods, κ_diff can be far
  below the path κ. No dataset in the repo measures κ_diff:
  - rings measure absolute loops;
  - the shmoo is censored, not attributed to one cell, and every point is its own route.

  The shmoo's single attributable FAIL gives κ_diff ≥ 0.072, conditional on attributing the failure to
  ucmpi1. That is below both limits, and it refutes only the 1/22 + 50 ps form.
- **Population view** (class-centred, slow side only, because only upper quantiles are published).
  - Rule E's 19.9 % sits just below the 7-link class's slow-side p90 (+0.223), and on the fast side the
    7-link minimum is −0.343. It is above the slow-side p90 of the longer classes (0.13, 0.13, 0.09) but
    below their maxima (0.22, 0.19, 0.17).
  - Rule A's 9.1 % is below every class's slow-side p90 except the 63-link class (0.093). The README's
    global-scale figure is that 8.5 % covers 15.6 % of 7-link rings and 52 % overall.
  - Neither is a bound.
- **Verdict: not settled.** The path-level hypothesis is refuted. The differential hypothesis, which is
  what the rules actually need, is unmeasured.

## What would settle it: a differential tail ring

Build a ring whose period difference **is** the divergent-tail difference, so that κ is measured on
`d_b − d_a` and not on an absolute loop.

1. **Structure.** One ring has a shared body C: the inverter, the counter tap, and about 15 links so
   that it oscillates slowly enough to count. At one node, C fans out into two **tails A and B** that
   reconverge on the two data inputs of one LUT6 used as a 2:1 mux. A static select bit, set through the
   existing USER1 scan chain of `ro_many_top`, picks the tail.
   - `T_B − T_A = 2(d_B − d_A) + 2μ`, where μ is the mux pin-to-pin difference. Everything in C, and the
     fan-out node's extra sink, is physically shared and cancels **exactly**. So the 988 ps question
     disappears from the measurement.
   - **μ is calibrated** by a third select setting that routes tail A to *both* mux pins (or by a mirror
     build with the tails swapped onto opposite pins).
   - Period repeatability is 0.052 %, about 8 ps on a 15 ns ring. Δ is resolved to about 10 ps against
     tails of 0.3–3 ns, so a 10 % κ (≥ 30 ps) is visible.
2. **Tails to build.** These are the populations rule E and rule A compare:
   - (i) a `bd_delay` chain of k = 0…6 links (request-like) against a LUT cone plus general routing of
     similar predicted delay (data/select-like);
   - (ii) **tail pairs lifted from real routes**: the select/request divergent tails that `skew.py`
     walks on gcd/xorshift, re-placed with their RLOCs;
   - (iii) matched tails A ≡ B, the null, where κ_diff should come out as measurement noise;
   - (iv) a negative control: B = A plus one extra `bd_delay` link, whose Δ must come out at the
     link's measured cost.
3. **Population.** At least 64 pairs per tail class. At n ≥ 59 the order-statistic UCB95 of the p95
   exists. Use 4 placer seeds (CLAUDE.md: one route is a sample), with `NEXTPNR_SEED` pinned per arm
   and the bitstreams checked with `cmp`. Take two die temperatures, to test SharedCorner: the spread
   of `period(T₂)/period(T₁)` across rings estimates the non-shared part (`near_corner`'s δ).
4. **Predictions per tail, from the same routed.json:**
   - the nextpnr SDF (`pred_*`);
   - prjxray fast-min and slow-max via the research branch's `xray_delay.py` (`fast_*`, `slow_*`).

   Then `kappa.py pairs` reports κ_diff per class, with the pair bound, the affine bound and quantiles.
   `ruleE_two_corner` says to judge rule E on both endpoint columns.
5. **Save the raw logs** (`gNN.log`) and the per-tail predictions in the repo. `kappa.py rawlogs` already
   parses the ro_many log format. The missing ro_many raw logs are the reason this note cannot quote a
   two-sided κ̂_q for the 128 rings.

The cheaper half-step: commit `build/hw/ro_many_top/raw/gNN.log` and that route's per-ring SDF
prediction, if they still exist on the bench machine. `kappa.py rawlogs DIR --pred PRED.tsv` (keys
`g{g}.b{b}`) then gives the full table for the absolute κ: two-sided quantiles per class with UCBs, the
θ0 fit with its CI and β. It still would not give κ_diff.

## Lean status

- **Theorem already proved:** `Formal.Core.Corner.ring_kappa_lower` is the pair bound;
  `guard_refuted_by_7link_rings` is its 7-link instance, which the tool reproduces. Check:
  `cd formal/lean && ../slot.sh lake env lean Formal/Core/Delay/Corner.lean` (per A-delay-corner.md;
  not re-run here, no Lean was written).
- **Small lemmas that would make the rest theorems.** These are not written: this probe's write scope
  was the tool and this note. Each one is a few lines of `nlinarith`.
  - `ring_kappa_attained`: with `s = (rᵢ+rⱼ)/2` and `κ = (rᵢ−rⱼ)/(rᵢ+rⱼ)`, both `Scat κ s rᵢ` and
    `Scat κ s rⱼ` hold. So κ_min is the exact minimum, not merely a bound.
  - `ruleE_sound_diff`: replace the two per-tail `Scat` hypotheses by the **differential** one,
    `s·((Pr−Ps) − κd·(Pr+Ps)) ≤ ar − as_`, with `κd ≤ kappaE`. The conclusion `C+as_ < C+ar` follows
    from the same guard. This is the theorem that the differential tail ring's κ_diff would discharge,
    and it is strictly weaker in its hypothesis than `ruleE_sound`, because per-tail `Scat κ` implies
    the differential one with `κd = κ`.
  - The η-widened bound and the censored bound are one-line corollaries of `ring_kappa_lower`.

## Fidelity notes

- Ring periods are 2× the loop, both measured and predicted, so ratios are unaffected. An additive θ per
  path is 2θ per period, and the tool uses 100 ps per period for rule A's 50 ps.
- In the rings, κ mixes rising and falling transits. Rule E/A tails see one edge direction at a time.
  The differential ring has the same mix, so a rise/fall split needs a pulse-width variant
  (`ro_link_fit.py`'s low-pulse census is a model).
- The rebuild-route P values in the summary analysis (β, the θ0-robustness line) are **approximations**
  from a different route. The κ_min = 0.311 itself uses only the published ratios.
- The shmoo's censored bound assumes that the failure is ucmpi1's request overtaking its data, which the
  README explicitly does not establish.
- On rings with θ ≠ 0, the mixed-rule coverage line in `rings` output judges `|ε| ≤ 1/22` only
  (θ ignored). The mixed-rule *verdict* uses the full feasibility test.

## Verdict

**Works.** The estimator exists, is self-tested (soundness over 2000 random populations, recovery of κ, θ0
and c, a negative control reported as exceeding), and runs on every dataset in the repo.

**It is blocked on data for the question that matters.** The path-level κ is at least 0.311 (7-link
rings), so the hypotheses of `ruleE_sound` and `ruleA_sound_rel` fail at path level. The differential κ
that the rules actually need has never been measured.

Effort:
- about 1 h to add `ruleE_sound_diff` and `ring_kappa_attained` to Corner.lean;
- about 1 day of board work for the differential tail ring (RTL is a variant of `ro_many_top`; the
  analysis is `kappa.py pairs`).
