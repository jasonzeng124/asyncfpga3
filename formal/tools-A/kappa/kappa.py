#!/usr/bin/env python3
"""kappa.py -- estimate the local-scatter parameter kappa of the Corner model.

The model (formal/lean/Formal/Core/Delay/Corner.lean, formal/notes/A-delay-corner.md):

  * SharedCorner: every path on one die, in one session, sits at ONE corner.
      proportional form:  nominal D_i = s * P_i      (P_i = SDF prediction, s > 0 shared)
      affine form:        nominal D_i(c) = (1-c) F_i + c S_i,  c in [0,1] shared
                          (F_i, S_i = fast-min / slow-max endpoint predictions)
  * LocalScatter kappa:   (1-kappa) D_i <= d_i <= (1+kappa) D_i    (`Scat kappa D d`)
  * optional common offset theta0 (the ~988 ps per ring period in the 128-ring fit):
                          d_i = s * P_i * (1 + eps_i) + theta0

The limits the theorems need:
  rule E   kappa <= 383/1927 = 0.19876   (ruleE_sound, tight by ruleE_tight)
  rule A   kappa <= 1/11     = 0.09091   (ruleA_sound_rel, theta = 0, tight by ruleA_tight)
  rule A   kappa <= 1/22 with additive scatter theta <= 50 ps   (ruleA_sound)

Estimators (all stdlib, no numpy):
  kappa_min     the smallest kappa consistent with the data under the model = the
                distribution-free pair bound max_{i,j} (r_i - r_j)/(r_i + r_j)
                (ring_kappa_lower), widened for measurement error eta.  It is a
                CERTAIN lower bound on the worst-case kappa (no statistics), valid
                only under the stated assumptions.  No data can give an upper
                bound on a worst case.
  kappa_q       q-quantile of |r_i / s_hat - 1| (population statement), with a
                distribution-free order-statistic upper confidence bound and a
                stratified bootstrap interval that includes the s_hat estimation.
  model fit     relative (r = a) vs offset (r = a + theta0 / P) on the ratio scale,
                slope permutation test, residual trend vs length, and the scatter
                shape exponent beta (spread_ps ~ P^beta: 1 = relative kappa,
                0.5 = independent per-arc scatter, 0 = additive).
  differential  for two-path pairs: kappa_diff = |Delta/s - (P_b - P_a)| / (P_a + P_b),
                the scatter actually projected onto the difference rule E/A compare.

Run `python3 kappa.py --help`, `python3 kappa.py selftest`, `python3 kappa.py repo`.
Input schemas: SCHEMA below (also printed by --help) and formal/notes/A-kappa.md.
"""
import argparse
import csv
import json
import math
import os
import random
import re
import statistics
import sys

KAPPA_E = 383 / 1927          # Corner.kappaE
KAPPA_A_REL = 1 / 11          # ruleA_sound_rel
KAPPA_A_MIX = 1 / 22          # ruleA_sound (with theta <= 50 ps)
LIMITS = [("rule E", KAPPA_E), ("rule A (theta=0)", KAPPA_A_REL),
          ("rule A (theta<=50ps)", KAPPA_A_MIX)]
THETA_MAX = 988.0             # cells/hw/README.md two-parameter fit, ps per ring period
HERE = os.path.dirname(os.path.abspath(__file__))

SCHEMA = """
RING CSV/TSV (one row per closed path; `rings` subcommand)
  required: measured_ps, pred_ps                (aliases: period_measured_ps,
            nextpnr_period_ps / sdf_ps for pred_ps)
  optional: ring (id), links (length class; alias class), die, session,
            fast_ps (alias xray_fastmin_ps), slow_ps (alias xray_slowmax_ps)
  Lines starting with '#' are comments.  All rows of one (die, session) share s or c.

TWO-PATH CSV (one row per measured PAIR of paths on one die; `pairs` subcommand)
  die, session, pair, class,
  meas_a_ps, pred_a_ps, fast_a_ps, slow_a_ps,      path a = the path that must be EARLY
  meas_b_ps, pred_b_ps, fast_b_ps, slow_b_ps,      path b = the path that must be LATE
  meas_diff_ps,      measured d_b - d_a when the rig measures the difference directly
  outcome,           optional censored observation instead of delays:
                       FAIL_LATE_FIRST : path b (request) was seen no later than a (data)
                       PASS_EARLY_FIRST: a certified a-before-b (rig exercises the worst a)
                       PASS_UNCERTIFIED: a pass that does not certify the order (ignored)
  meas_rel_err       relative measurement error eta of each meas_* (default 0)
  Empty cells are allowed.  pred_* is the prediction under the proportional form;
  fast_*/slow_* the endpoints under the affine form.  Only tails after the
  divergence point should be given (the shared prefix cancels exactly).

RING SUMMARY CSV (`summary` subcommand; what cells/hw/README.md publishes)
  links, n, median, p90, p99, max, min, p_approx_ps    (ratios measured/predicted)
"""


# ----------------------------------------------------------------- statistics

def quantile(xs, q):
    """Linear-interpolation quantile (numpy default, type 7)."""
    v = sorted(xs)
    if not v:
        return float("nan")
    h = (len(v) - 1) * q
    lo = math.floor(h)
    hi = min(lo + 1, len(v) - 1)
    return v[lo] + (h - lo) * (v[hi] - v[lo])


def binom_cdf(k, n, p):
    return sum(math.comb(n, i) * p ** i * (1 - p) ** (n - i) for i in range(0, k + 1))


def order_stat_ucb(xs, q, conf=0.95):
    """Distribution-free one-sided upper confidence bound for the q-quantile:
    x_(k) with the smallest k such that P(Bin(n,q) <= k-1) >= conf.  None if
    n is too small for this confidence."""
    v = sorted(xs)
    n = len(v)
    for k in range(1, n + 1):
        if binom_cdf(k - 1, n, q) >= conf:
            return v[k - 1]
    return None


def min_n_for_ucb(q, conf=0.95):
    n = 1
    while 1 - q ** n < conf:   # UCB = max needs 1 - q^n >= conf
        n += 1
    return n


def ranks(v):
    o = sorted(range(len(v)), key=lambda i: v[i])
    r = [0.0] * len(v)
    i = 0
    while i < len(o):
        j = i
        while j + 1 < len(o) and v[o[j + 1]] == v[o[i]]:
            j += 1
        for k in range(i, j + 1):
            r[o[k]] = (i + j) / 2 + 1
        i = j + 1
    return r


def pearson(x, y):
    mx, my = statistics.fmean(x), statistics.fmean(y)
    sxy = sum((a - mx) * (b - my) for a, b in zip(x, y))
    sxx = sum((a - mx) ** 2 for a in x)
    syy = sum((b - my) ** 2 for b in y)
    return sxy / math.sqrt(sxx * syy) if sxx > 0 and syy > 0 else 0.0


def spearman(x, y):
    return pearson(ranks(x), ranks(y))


def perm_p(stat, x, y, trials=2000, seed=1):
    """Two-sided permutation p-value of |stat(x, y)|."""
    rng = random.Random(seed)
    obs = abs(stat(x, y))
    yy = list(y)
    hit = 0
    for _ in range(trials):
        rng.shuffle(yy)
        if abs(stat(x, yy)) >= obs - 1e-15:
            hit += 1
    return (hit + 1) / (trials + 1)


def ols(x, y):
    mx, my = statistics.fmean(x), statistics.fmean(y)
    sxx = sum((a - mx) ** 2 for a in x)
    b = sum((a - mx) * (c - my) for a, c in zip(x, y)) / sxx
    return my - b * mx, b


# ------------------------------------------------------------ core estimators

def kappa_min(ratios, eta=0.0):
    """Smallest kappa such that some s > 0 has every true ratio in s(1 +- kappa),
    when each observed ratio may be off by a relative eta.  Equals the pair
    bound (r_max - r_min)/(r_max + r_min) at eta = 0 (ring_kappa_lower, and it
    is attained: s = (r_max + r_min)/2).  Returns (kappa, s_mid, i_max, i_min)."""
    lo = [r / (1 + eta) for r in ratios]
    hi = [r / (1 - eta) for r in ratios]
    imax = max(range(len(lo)), key=lambda i: lo[i])
    imin = min(range(len(hi)), key=lambda i: hi[i])
    A, B = lo[imax], hi[imin]
    if A <= B:
        return 0.0, (A + B) / 2, imax, imin
    return (A - B) / (A + B), (A + B) / 2, imax, imin


def pair_bound(ri, rj, eta=0.0):
    k, _, _, _ = kappa_min([ri, rj], eta)
    return k


def lerp(F, S, c):
    return (1 - c) * F + c * S


def minimize_1d(f, lo, hi, grid=400, refine=60):
    """Grid then golden-section refinement around the best grid point."""
    best = min((f(lo + (hi - lo) * i / grid), lo + (hi - lo) * i / grid)
               for i in range(grid + 1))
    step = (hi - lo) / grid
    a, b = max(lo, best[1] - step), min(hi, best[1] + step)
    g = (math.sqrt(5) - 1) / 2
    x1, x2 = b - g * (b - a), a + g * (b - a)
    f1, f2 = f(x1), f(x2)
    for _ in range(refine):
        if f1 <= f2:
            b, x2, f2 = x2, x1, f1
            x1 = b - g * (b - a)
            f1 = f(x1)
        else:
            a, x1, f1 = x1, x2, f2
            x2 = a + g * (b - a)
            f2 = f(x2)
    cand = [(best[0], best[1]), (f1, x1), (f2, x2)]
    return min(cand)


def kappa_min_affine(m, F, S, eta=0.0, free_scale=True):
    """Affine SharedCorner: nominal D_i(c) = lerp(F_i, S_i, c), c in [0,1] unknown.
    free_scale=True also allows an unknown scale on top (die outside the
    endpoint envelope); then the bound is min_c kappa_min(m/D(c)).
    free_scale=False is the strict model (no scale): min_c max_i |m_i/D_i(c) - 1|."""
    def f(c):
        r = [mi / lerp(Fi, Si, c) for mi, Fi, Si in zip(m, F, S)]
        if free_scale:
            return kappa_min(r, eta)[0]
        return max(max(ri / (1 + eta) - 1, 1 - ri / (1 - eta), 0.0) for ri in r)
    return minimize_1d(f, 0.0, 1.0)


def kappa_min_offset(m, P, theta_lo, theta_hi, eta=0.0):
    """min over theta0 in [theta_lo, theta_hi] of kappa_min((m - theta0)/P).
    Sound for every theta0 in the interval (the minimum is a lower bound)."""
    hi = min(theta_hi, min(m) * 0.999)
    if hi < theta_lo:
        return float("nan"), float("nan")
    return minimize_1d(lambda t: kappa_min([(mi - t) / Pi for mi, Pi in zip(m, P)], eta)[0],
                       theta_lo, hi)


def theta_min_additive(m, P):
    """Pure additive scatter (rule A's theta): smallest theta such that some s > 0
    has every |m_i - s P_i| <= theta.  Chebyshev fit through the origin."""
    r = [mi / Pi for mi, Pi in zip(m, P)]
    v, s = minimize_1d(lambda s: max(abs(mi - s * Pi) for mi, Pi in zip(m, P)),
                       min(r), max(r))
    return v, s


def fit_models(m, P):
    """Fit relative (m = a P) and offset (m = a P + theta0) on the RATIO scale
    (r = a, resp. r = a + theta0 * (1/P)), i.e. weighted LS with every path
    weighted by its relative error.  Returns dict with eps per model."""
    r = [mi / Pi for mi, Pi in zip(m, P)]
    x = [1 / Pi for Pi in P]
    a_rel = statistics.median(r)                       # robust scale
    a_rel_mean = statistics.fmean(r)
    a_off, th = ols(x, r)[0], ols(x, r)[1]
    # also the OLS-on-periods fit cells/hw/ro_many_measure.py uses (long rings dominate)
    k_lsq = sum(mi * Pi for mi, Pi in zip(m, P)) / sum(Pi * Pi for Pi in P)
    i_p, b_p = ols(P, m)
    eps_rel = [ri / a_rel - 1 for ri in r]
    eps_off = [(mi - th) / (a_off * Pi) - 1 for mi, Pi in zip(m, P)]
    return dict(r=r, a_rel=a_rel, a_rel_mean=a_rel_mean, a_off=a_off, theta=th,
                k_lsq_origin=k_lsq, lsq_periods=(b_p, i_p),
                eps_rel=eps_rel, eps_off=eps_off)


def slope_perm_p(m, P, trials=2000, seed=7):
    """Permutation p-value for theta0 != 0 (slope of r on 1/P)."""
    r = [mi / Pi for mi, Pi in zip(m, P)]
    x = [1 / Pi for Pi in P]
    return perm_p(lambda a, b: ols(a, b)[1], x, r, trials, seed)


def scatter_shape(classes, P, resid_ps):
    """beta in spread_ps ~ P^beta, from per-class MAD of residual (ps) against
    per-class median P.  1 = relative (kappa), 0.5 = sqrt(n) averaging of
    independent arcs, 0 = additive.  Needs >= 2 classes with >= 4 members."""
    by = {}
    for c, p, e in zip(classes, P, resid_ps):
        by.setdefault(c, []).append((p, e))
    pts = []
    for c, v in by.items():
        if len(v) < 4:
            continue
        med = statistics.median(e for _, e in v)
        mad = statistics.median(abs(e - med) for _, e in v)
        if mad > 0:
            pts.append((math.log(statistics.median(p for p, _ in v)), math.log(mad)))
    if len(pts) < 2:
        return None, pts
    return ols([a for a, _ in pts], [b for _, b in pts])[1], pts


def quantile_table(eps, qs=(0.5, 0.9, 0.95, 0.99), conf=0.95):
    a = [abs(e) for e in eps]
    out = {}
    for q in qs:
        out[q] = dict(point=quantile(a, q), ucb=order_stat_ucb(a, q, conf))
    return out


def bootstrap_kq(m, P, classes, q, scale="class", B=1000, seed=3):
    """Stratified bootstrap (by class) of kappa_q, re-estimating s_hat each time."""
    rng = random.Random(seed)
    by = {}
    for i, c in enumerate(classes):
        by.setdefault(c, []).append(i)
    vals = []
    for _ in range(B):
        idx = [rng.choice(v) for v in by.values() for _ in v]
        mm = [m[i] for i in idx]
        pp = [P[i] for i in idx]
        cc = [classes[i] for i in idx]
        eps = eps_with_scale(mm, pp, cc, scale)
        vals.append(quantile([abs(e) for e in eps], q))
    return quantile(vals, 0.025), quantile(vals, 0.975)


def eps_with_scale(m, P, classes, scale):
    r = [mi / Pi for mi, Pi in zip(m, P)]
    if scale == "global":
        s = statistics.median(r)
        return [ri / s - 1 for ri in r]
    if scale == "class":
        med = {}
        for c in set(classes):
            med[c] = statistics.median(ri for ri, ci in zip(r, classes) if ci == c)
        return [ri / med[ci] - 1 for ri, ci in zip(r, classes)]
    if scale == "offset":
        return fit_models(m, P)["eps_off"]
    raise ValueError(scale)


def mixed_feasible(m, P, kappa, theta, eta=0.0):
    """Is there s > 0 with s((1-kappa)P_i - theta) <= m_i <= s((1+kappa)P_i + theta) for all i
    (ruleA_sound's model, theta in SDF ps)?  Measurement error eta widens each m_i."""
    lo, hi = 0.0, float("inf")
    for mi, Pi in zip(m, P):
        lo = max(lo, mi * (1 - eta) / ((1 + kappa) * Pi + theta))
        d = (1 - kappa) * Pi - theta
        if d > 0:
            hi = min(hi, mi * (1 + eta) / d)
    return lo <= hi


def limit_verdicts(kmin, eps=None, mP=None, eta=0.0):
    """Worst-case verdict from kappa_min, population coverage from eps.  The mixed
    rule-A limit (kappa <= 1/22 AND theta <= 50 ps) needs m and P (mP) to be judged;
    without them it is judged on kappa alone, which is only valid if theta = 0."""
    out = []
    for name, L in LIMITS:
        refuted = kmin > L
        if name.startswith("rule A (theta<=50") and mP is not None:
            # theta is per path; a ring PERIOD is two traversals of the loop, so mP[2] = 2
            refuted = not mixed_feasible(mP[0], mP[1], L, 50.0 * (mP[2] if len(mP) > 2 else 1), eta)
        row = dict(rule=name, limit=L, refuted=refuted)
        if eps is not None:
            a = [abs(e) for e in eps]
            row["coverage"] = sum(1 for x in a if x <= L) / len(a)
        out.append(row)
    return out


# --------------------------------------------------------------------- input

ALIASES = {
    "measured_ps": ["measured_ps", "period_measured_ps", "meas_ps", "measured"],
    "pred_ps": ["pred_ps", "nextpnr_period_ps", "sdf_ps", "predicted_ps", "predicted"],
    "fast_ps": ["fast_ps", "xray_fastmin_ps"],
    "slow_ps": ["slow_ps", "xray_slowmax_ps"],
    "links": ["links", "class", "length_class"],
    "ring": ["ring", "id", "path"],
    "die": ["die"], "session": ["session"],
}


def read_table(path):
    with open(path) as f:
        lines = [l for l in f if l.strip() and not l.lstrip().startswith("#")]
    delim = "\t" if "\t" in lines[0] else ","
    return list(csv.DictReader(lines, delimiter=delim))


def get(row, key):
    for k in ALIASES.get(key, [key]):
        if k in row and row[k] not in ("", None):
            return row[k]
    return None


def fnum(x):
    return None if x in (None, "") else float(x)


def load_rings(path):
    rows = []
    for row in read_table(path):
        rows.append(dict(ring=get(row, "ring"), links=get(row, "links") or "all",
                         die=get(row, "die") or "die0",
                         session=get(row, "session") or os.path.basename(path),
                         m=fnum(get(row, "measured_ps")), P=fnum(get(row, "pred_ps")),
                         F=fnum(get(row, "fast_ps")), S=fnum(get(row, "slow_ps"))))
    return rows


# ------------------------------------------------------------------ analyses

def fmt(x, n=4):
    if x is None:
        return "n/a"
    if isinstance(x, float) and math.isnan(x):
        return "nan"
    return f"{x:.{n}f}"


def analyse_rings(rows, eta, out, label, boot=1000):
    """Full analysis of one (die, session) ring population."""
    rows = [r for r in rows if r["m"] is not None and r["P"] is not None]
    res = dict(label=label, n=len(rows))
    w = out.append
    w(f"\n=== rings: {label}  (n = {len(rows)}, eta = {eta}) ===")
    if len(rows) < 2:
        w("  fewer than 2 measured paths with a prediction: nothing to estimate")
        return res
    m = [r["m"] for r in rows]
    P = [r["P"] for r in rows]
    cls = [r["links"] for r in rows]
    fm = fit_models(m, P)
    r = fm["r"]

    # 1. distribution-free bound, proportional form
    k0, smid, imax, imin = kappa_min(r, eta)
    res["kappa_min_prop"] = k0
    w("1. distribution-free bound (proportional SharedCorner, theta0 = 0)")
    w(f"   kappa_min = {fmt(k0)}  from rings {rows[imax]['ring']} (r={fmt(r[imax], 3)}) and "
      f"{rows[imin]['ring']} (r={fmt(r[imin], 3)}); s* = {fmt(smid)}")
    for v in limit_verdicts(k0, mP=(m, P, 2), eta=eta):
        w(f"   {v['rule']:<22} limit {fmt(v['limit'])}: "
          f"{'REFUTED (no s fits the data within it)' if v['refuted'] else 'not refuted by this data'}")

    th_add, s_add = theta_min_additive(m, P)
    w(f"   pure additive scatter instead (|m - sP| <= theta): theta_min = {th_add:.0f} ps "
      f"at s = {fmt(s_add)}  (rule A's ruleA_sound allows 50 ps, per path)")
    res["theta_min_additive_ps"] = th_add
    res["kappa_min_class"] = {}
    for c in sorted(set(cls), key=lambda z: (len(str(z)), str(z))):
        rc = [ri for ri, ci in zip(r, cls) if ci == c]
        if len(rc) >= 2:
            if not res["kappa_min_class"]:
                w(f"   per length class: {'class':>6} {'n':>4} {'kappa_min':>10}  (pairs within the class)")
            kc = kappa_min(rc, eta)[0]
            res["kappa_min_class"][c] = kc
            w(f"                     {c:>6} {len(rc):>4} {fmt(kc):>10}")
    if not res["kappa_min_class"]:
        w("   (one ring per length class: no within-class bound)")

    # 2. offset vs relative
    w("2. model separation: relative (r = a) vs offset (r = a + theta0/P), ratio scale")
    p_slope = slope_perm_p(m, P)
    rho_rel = spearman(P, fm["eps_rel"])
    rho_off = spearman(P, fm["eps_off"])
    p_rel = perm_p(spearman, P, fm["eps_rel"])
    p_off = perm_p(spearman, P, fm["eps_off"])
    b_p, i_p = fm["lsq_periods"]
    w(f"   relative: a = {fmt(fm['a_rel'])} (median ratio); OLS through origin on periods "
      f"k = {fmt(fm['k_lsq_origin'])}")
    w(f"   offset  : a = {fmt(fm['a_off'])}, theta0 = {fm['theta']:+.0f} ps (ratio-scale WLS); "
      f"OLS on periods: {fmt(b_p)} x P {i_p:+.0f} ps")
    w(f"   theta0 != 0 permutation p = {fmt(p_slope, 3)}")
    w(f"   residual trend vs P (Spearman): relative rho = {fmt(rho_rel, 3)} (p {fmt(p_rel, 3)}), "
      f"offset rho = {fmt(rho_off, 3)} (p {fmt(p_off, 3)})")
    classes_sorted = sorted(set(cls), key=lambda z: (len(str(z)), str(z)))
    for name, eps in (("relative", fm["eps_rel"]), ("offset", fm["eps_off"])):
        meds = []
        for c in classes_sorted:
            ec = [e for e, ci in zip(eps, cls) if ci == c]
            meds.append(f"{c}:{statistics.median(ec) * 100:+.1f}%")
        a = [abs(e) for e in eps]
        w(f"   {name:<9} eps median by class {', '.join(meds)}; |eps| p50 {quantile(a, .5) * 100:.1f}% "
          f"p90 {quantile(a, .9) * 100:.1f}% max {max(a) * 100:.1f}%")
    if p_slope >= 0.05:
        verdict = "RELATIVE: no significant theta0"
    elif p_off >= 0.05 and abs(rho_off) < abs(rho_rel):
        verdict = ("OFFSET: theta0 is significant and the offset fit leaves no length trend"
                   + ("" if p_rel < 0.05 else " (the relative-model trend itself is not significant at this n)"))
    else:
        verdict = "OFFSET+TREND: theta0 significant but a length trend survives it"
    w(f"   verdict: {verdict}")
    res.update(theta0=fm["theta"], a_off=fm["a_off"], a_rel=fm["a_rel"], p_theta=p_slope,
               trend_rel=(rho_rel, p_rel), trend_off=(rho_off, p_off), model_verdict=verdict)

    # theta0 interval by bootstrap and the offset-model bound
    rng = random.Random(11)
    ths = []
    for _ in range(boot):
        idx = [rng.randrange(len(m)) for _ in m]
        try:
            ths.append(fit_models([m[i] for i in idx], [P[i] for i in idx])["theta"])
        except ZeroDivisionError:
            pass
    tlo, thi = quantile(ths, 0.025), quantile(ths, 0.975)
    k_fix = kappa_min([(mi - fm["theta"]) / Pi for mi, Pi in zip(m, P)], eta)[0]
    k_free, t_at = kappa_min_offset(m, P, tlo, thi, eta)
    w(f"   theta0 bootstrap 95% interval [{tlo:+.0f}, {thi:+.0f}] ps")
    w(f"   kappa_min with theta0 = fit: {fmt(k_fix)}; minimised over that interval: "
      f"{fmt(k_free)} (at theta0 = {t_at:+.0f} ps)")
    res.update(theta_ci=(tlo, thi), kappa_min_offset_fit=k_fix, kappa_min_offset_ci=k_free)

    # scatter shape
    resid_ps = [mi - fm["a_off"] * Pi - fm["theta"] for mi, Pi in zip(m, P)]
    beta, pts = scatter_shape(cls, P, resid_ps)
    if beta is not None:
        w(f"   scatter shape: spread_ps ~ P^beta, beta = {fmt(beta, 2)}  "
          f"(1 relative kappa, 0.5 independent arcs, 0 additive)")
    res["beta"] = beta

    # 3. quantiles
    w("3. quantile estimates kappa_q = q-quantile of |eps| "
      "(population statement, NOT a worst case)")
    n = len(rows)
    class_ok = min(cls.count(c) for c in set(cls)) >= 3
    for scale in ("global", "class", "offset") if class_ok else ("global", "offset"):
        eps = eps_with_scale(m, P, cls, scale)
        qt = quantile_table(eps)
        cov = {nm: sum(1 for e in eps if abs(e) <= L) / n for nm, L in LIMITS}
        line = "   s_hat=%-7s" % scale + "  ".join(
            f"k{int(q * 100)} {fmt(v['point'], 3)} (UCB95 {fmt(v['ucb'], 3)})" for q, v in qt.items())
        w(line)
        w("                  coverage: " + ", ".join(f"{nm} {c * 100:.0f}%" for nm, c in cov.items()))
        res[f"quantiles_{scale}"] = {str(q): v for q, v in qt.items()}
        res[f"coverage_{scale}"] = cov
    if n >= 8 and boot and class_ok:
        lo, hi = bootstrap_kq(m, P, cls, 0.9, "class", B=boot)
        w(f"   bootstrap 95% interval of k90 (s_hat=class, re-estimated): [{fmt(lo, 3)}, {fmt(hi, 3)}]")
        res["k90_boot"] = (lo, hi)
    w(f"   (an order-statistic UCB95 of the p99 needs n >= {min_n_for_ucb(0.99)}; "
      f"of p95 n >= {min_n_for_ucb(0.95)}; of p90 n >= {min_n_for_ucb(0.90)})")
    if class_ok:
        w("   per class (s_hat = class median):")
        w(f"   {'class':>6} {'n':>4} {'k50':>7} {'k90':>7} {'UCB95(k90)':>11} {'max|eps|':>9} "
          f"{'cov E':>6} {'cov A':>6}")
    else:
        w("   (fewer than 3 rings in some length class: no per-class scale or quantiles)")
    eps_c = eps_with_scale(m, P, cls, "class") if class_ok else []
    res["class_quantiles"] = {}
    for c in (classes_sorted if class_ok else []):
        ec = [abs(e) for e, ci in zip(eps_c, cls) if ci == c]
        u = order_stat_ucb(ec, 0.9)
        cE = sum(1 for x in ec if x <= KAPPA_E) / len(ec)
        cA = sum(1 for x in ec if x <= KAPPA_A_REL) / len(ec)
        res["class_quantiles"][c] = dict(n=len(ec), k50=quantile(ec, .5), k90=quantile(ec, .9),
                                         ucb90=u, max=max(ec), covE=cE, covA=cA)
        w(f"   {c:>6} {len(ec):>4} {fmt(quantile(ec, .5), 3):>7} {fmt(quantile(ec, .9), 3):>7} "
          f"{fmt(u, 3):>11} {fmt(max(ec), 3):>9} {cE * 100:5.0f}% {cA * 100:5.0f}%")

    # 4. affine form if endpoints are present
    if all(r_["F"] is not None and r_["S"] is not None for r_ in rows):
        F = [r_["F"] for r_ in rows]
        S = [r_["S"] for r_ in rows]
        kA, cA_ = kappa_min_affine(m, F, S, eta, free_scale=True)
        kS, cS_ = kappa_min_affine(m, F, S, eta, free_scale=False)
        w("4. affine SharedCorner (fast/slow endpoints)")
        w(f"   with free scale: kappa_min = {fmt(kA)} at c = {fmt(cA_, 3)}")
        w(f"   strict (c in [0,1], no scale): kappa_min = {fmt(kS)} at c = {fmt(cS_, 3)}")
        res.update(kappa_min_affine=kA, c_affine=cA_, kappa_min_affine_strict=kS, c_strict=cS_)
    return res


def analyse_pairs(rows, out, scale=None, trust_pass=False):
    """Two-path data: per-pair bounds, the differential kappa, censored outcomes."""
    w = out.append
    w(f"\n=== two-path pairs (n rows = {len(rows)}) ===")
    res = dict(pairs=[])
    # session scale from absolute measurements in the same (die, session)
    sess = {}
    for r in rows:
        key = (r.get("die") or "die0", r.get("session") or "s0")
        for side in "ab":
            mm, pp = fnum(r.get(f"meas_{side}_ps")), fnum(r.get(f"pred_{side}_ps"))
            if mm and pp:
                sess.setdefault(key, []).append(mm / pp)
    shat = {k: statistics.median(v) for k, v in sess.items()}
    bounds = []
    for r in rows:
        key = (r.get("die") or "die0", r.get("session") or "s0")
        eta = fnum(r.get("meas_rel_err")) or 0.0
        ma, mb = fnum(r.get("meas_a_ps")), fnum(r.get("meas_b_ps"))
        pa, pb = fnum(r.get("pred_a_ps")), fnum(r.get("pred_b_ps"))
        md = fnum(r.get("meas_diff_ps"))
        oc = (r.get("outcome") or "").strip().upper()
        rec = dict(pair=r.get("pair"), cls=r.get("class"))
        s = scale if scale else shat.get(key)
        if ma and mb and pa and pb:
            rec["pair_bound"] = pair_bound(ma / pa, mb / pb, eta)
            if md is None:
                md = mb - ma
        if md is not None and pa and pb and s:
            rec["kappa_diff"] = abs(md / s - (pb - pa)) / (pa + pb)
            rec["s_used"] = s
        if oc == "FAIL_LATE_FIRST" and pa and pb:
            # real b <= real a  =>  (1-k) s pb <= (1+k) s pa  =>  k >= (pb-pa)/(pa+pb)
            rec["censored_bound"] = max(0.0, (pb - pa) / (pa + pb))
            # with ruleA_sound's additive theta = 50 ps per path as well
            rec["censored_bound_theta50"] = max(0.0, (pb - pa - 100) / (pa + pb))
        if oc == "PASS_EARLY_FIRST" and pa and pb:
            rec["censored_bound"] = max(0.0, (pa - pb) / (pa + pb))
        if oc == "PASS_UNCERTIFIED" and pa and pb and trust_pass:
            rec["conditional_bound"] = max(0.0, (pa - pb) / (pa + pb))
        rec["outcome"] = oc or None
        res["pairs"].append(rec)
        for k in ("pair_bound", "kappa_diff", "censored_bound"):
            if k in rec:
                bounds.append((rec[k], k, rec["pair"]))
        w(f"   pair {rec['pair']!s:>6} class {rec['cls']!s:>4}  "
          + "  ".join(f"{k} {fmt(rec[k])}" for k in
                      ("pair_bound", "kappa_diff", "censored_bound", "conditional_bound") if k in rec)
          + (f"  [{oc}]" if oc else ""))
    if bounds:
        b, k, p = max(bounds)
        w(f"   max certain lower bound: kappa >= {fmt(b)} ({k}, pair {p})")
        b50 = max([p_.get("censored_bound_theta50", 0) for p_ in res["pairs"]] +
                  [p_.get("pair_bound", 0) for p_ in res["pairs"]])
        for v in limit_verdicts(b):
            if v["rule"].startswith("rule A (theta<=50"):
                v["refuted"] = b50 > v["limit"] and not any("kappa_diff" in p_ for p_ in res["pairs"])
                note = f" (kappa lower bound with theta = 50 ps: {fmt(b50)})"
            else:
                note = ""
            w(f"   {v['rule']:<22} limit {fmt(v['limit'])}: "
              f"{'REFUTED' if v['refuted'] else 'not refuted by this data'}{note}")
        res["kappa_lower"] = b
    diffs = [p_["kappa_diff"] for p_ in res["pairs"] if "kappa_diff" in p_]
    if len(diffs) >= 2:
        qt = quantile_table(diffs)
        w("   differential kappa quantiles: " + "  ".join(
            f"k{int(q * 100)} {fmt(v['point'], 3)} (UCB95 {fmt(v['ucb'], 3)})" for q, v in qt.items()))
        res["diff_quantiles"] = {str(q): v for q, v in qt.items()}
    return res


def analyse_summary(rows, out):
    """What can be said from the published per-class quantile table alone."""
    w = out.append
    w("\n=== ring summary table (per-ring raw numbers NOT available) ===")
    res = {}
    allmax = max(float(r["max"]) for r in rows)
    mins = [(float(r["min"]), r["links"]) for r in rows if r.get("min")]
    w(f"   {'links':>6} {'n':>4} {'med':>6} {'p90':>6} {'max':>6} {'min':>6} "
      f"{'kmin(class)':>11} {'eps+p90':>8} {'eps+max':>8}  (eps+ = r/s_class - 1, slow side)")
    for r in rows:
        med, p90, mx = float(r["median"]), float(r["p90"]), float(r["max"])
        mn = fnum(r.get("min"))
        kc = kappa_min([mx, mn])[0] if mn else None
        w(f"   {r['links']:>6} {r['n']:>4} {med:6.3f} {p90:6.3f} {mx:6.3f} {fmt(mn, 3):>6} "
          f"{fmt(kc):>11} {p90 / med - 1:8.3f} {mx / med - 1:8.3f}")
        res[r["links"]] = dict(kmin=kc, eps_p90_slow=p90 / med - 1, eps_max_slow=mx / med - 1)
    if mins:
        mn, cl = min(mins)
        k = kappa_min([allmax, mn])[0]
        w(f"   whole population: max ratio {allmax:.3f}, min ratio <= {mn:.3f} (class {cl}) "
          f"=> kappa_min >= {fmt(k)}")
        res["kappa_min_all_lower"] = k
        mix = None
        for rr in rows:
            if rr.get("min") and rr.get("p_min_ps"):
                pm = float(rr["p_min_ps"])   # smallest P = most room for theta: lenient direction
                mix = ([float(rr["max"]) * pm, float(rr["min"]) * pm], [pm, pm], 2)
        # does a common offset theta0 in [0, THETA_MAX] rescue the within-class bound?  For
        # theta0 >= 0 the spread is smallest when the high ring has the smallest P and the low
        # ring the largest, so take P from the class range [p_min_ps, p_max_ps] that way.
        for rr in rows:
            if rr.get("min") and rr.get("p_min_ps") and rr.get("p_max_ps"):
                hi_, lo_ = float(rr["max"]), float(rr["min"])
                pmin, pmax = float(rr["p_min_ps"]), float(rr["p_max_ps"])
                best = min((kappa_min([hi_ - t / pmin, lo_ - t / pmax])[0], t)
                           for t in [THETA_MAX * i / 200 for i in range(201)])
                w(f"   class {rr['links']}: with a common offset theta0 in [0, {THETA_MAX:.0f}] ps and P in "
                  f"[{pmin:.0f}, {pmax:.0f}] ps, kappa_min >= {fmt(best[0])} (at theta0 = {best[1]:.0f})")
                res[f"kappa_min_{rr['links']}_offset_robust"] = best[0]
                # pure additive scatter: smallest when both rings have the smallest P
                th = (hi_ - lo_) * pmin / 2
                w(f"   class {rr['links']}: as pure additive scatter |m - sP| <= theta: theta_min >= "
                  f"{th:.0f} ps per period (P >= {pmin:.0f} ps); rule A's ruleA_sound allows 50 ps")
                res[f"theta_min_{rr['links']}_additive_ps"] = th
        for v in limit_verdicts(k, mP=mix):
            w(f"   {v['rule']:<22} limit {fmt(v['limit'])}: "
              f"{'REFUTED' if v['refuted'] else 'not refuted'}")
    # scatter shape from (p90 - median) * P_approx per class
    pts = [(math.log(float(r["p_approx_ps"])),
            math.log((float(r["p90"]) - float(r["median"])) * float(r["p_approx_ps"])))
           for r in rows if r.get("p_approx_ps")]
    if len(pts) >= 2:
        beta = ols([a for a, _ in pts], [b for _, b in pts])[1]
        w(f"   scatter shape (slow-side p90-median spread in ps vs class P, P approximate): "
          f"beta = {beta:.2f}  (1 relative, 0.5 independent arcs, 0 additive)")
        res["beta_approx"] = beta
    return res


def model_only(rows, out):
    """No measurement: how far from proportional are the endpoint predictions?"""
    w = out.append
    w("\n=== model-only: proportionality of the predictions (no measurement) ===")
    by = {}
    for r in rows:
        by.setdefault(r["links"], []).append(r)
    w(f"   {'class':>6} {'n':>4} {'S/F min':>8} {'S/F max':>8} {'P/F min':>8} {'P/F max':>8} "
      f"{'kmin(P vs xray mid)':>20}")
    res = {}
    for c, v in sorted(by.items(), key=lambda kv: (len(kv[0]), kv[0])):
        sf = [x["S"] / x["F"] for x in v]
        pf = [x["P"] / x["F"] for x in v]
        # kappa_min if silicon were exactly the xray midpoint c=0.5 and the check used P
        k = kappa_min([x["P"] / lerp(x["F"], x["S"], 0.5) for x in v])[0]
        res[c] = dict(sf=(min(sf), max(sf)), pf=(min(pf), max(pf)), kmodel=k)
        w(f"   {c:>6} {len(v):>4} {min(sf):8.3f} {max(sf):8.3f} {min(pf):8.3f} {max(pf):8.3f} "
          f"{fmt(k):>20}")
    allk = kappa_min([x["P"] / lerp(x["F"], x["S"], 0.5) for x in rows])[0]
    w(f"   all: model-vs-model kappa_min (nextpnr P vs prjxray lerp(F,S,0.5)) = {fmt(allk)}")
    w("   S/F nearly constant => the affine and proportional forms agree to that spread;")
    w("   P/F spread => nextpnr's SDF and prjxray disagree per route by that much on their own.")
    res["all"] = allk
    return res


# ---------------------------------------------------------- raw ro_many logs

def load_ro_many_raw(d, pred_path):
    """Parse build/hw/ro_many_top/raw/gNN.log (WINDOW/COUNT lines, as
    cells/hw/ro_many_measure.py) and join with a prediction table keyed
    g{g}.b{b}.  The prediction table MUST be from the measured route."""
    B, LENS = 8, [7, 15, 31, 63]
    pred = {r["ring"]: r for r in load_rings(pred_path)}
    rows = []
    for fn in sorted(os.listdir(d)):
        mt = re.match(r"g(\d+)\.log$", fn)
        if not mt:
            continue
        g = int(mt.group(1))
        txt = open(os.path.join(d, fn)).read()
        if f"GROUPDONE {g}" not in txt:
            continue
        win = {int(r): int(us) for _g, r, us in re.findall(r"^WINDOW (\d+) (\d+) (\d+)$", txt, re.M)}
        cnt = {}
        for _g, rep, a, h in re.findall(r"^COUNT (\d+) (\d+) (\d+) ([0-9a-fA-F]+)$", txt, re.M):
            word = int.from_bytes(bytes.fromhex(h), "little")
            data = word & 0xFFFFFFFF
            if data and data != 0xFFFFFFFF and not (word >> 37) & 1:
                cnt.setdefault(int(a), []).append(win[int(rep)] * 1e6 / data)
        for b in range(B):
            key = f"g{g}.b{b}"
            if b in cnt and key in pred:
                rows.append(dict(ring=key, links=str(LENS[(g + b) % 4]), die="die0",
                                 session="ro_many", m=statistics.fmean(cnt[b]),
                                 P=pred[key]["P"], F=pred[key]["F"], S=pred[key]["S"]))
    return rows


# ------------------------------------------------------------------ self-test

def synth(n_per, Pcls, s, kappa, theta, eta, rng, dist="uniform", F_S=None, c=None):
    rows = []
    for L, Pm in Pcls:
        for i in range(n_per):
            P = Pm * rng.uniform(0.9, 1.1)
            if dist == "uniform":
                e = rng.uniform(-kappa, kappa)
            else:
                e = max(-kappa, min(kappa, rng.gauss(0, kappa / 2.5)))
            if F_S:
                F = P * rng.uniform(*F_S[0])
                S = F * rng.uniform(*F_S[1])
                D = lerp(F, S, c)
            else:
                F = S = None
                D = s * P
            m = D * (1 + e) + theta
            m *= 1 + rng.uniform(-eta, eta)
            rows.append(dict(ring=f"{L}.{i}", links=str(L), die="d", session="syn",
                             m=m, P=P if not F_S else lerp(F, S, 0.5), F=F, S=S, eps=e))
    return rows


def selftest(verbose=False):
    rng = random.Random(2026)
    PCLS = [(7, 7300), (15, 15400), (31, 30800), (63, 63100)]
    fails = []
    out = []

    def check(cond, msg):
        print(("  ok    " if cond else "  FAIL  ") + msg)
        if not cond:
            fails.append(msg)

    print("selftest 1: soundness of kappa_min (pair bound) -- 2000 random small populations")
    bad = 0
    for t in range(2000):
        k = rng.uniform(0, 0.5)
        eta = rng.choice([0, 0.001, 0.01])
        rows = synth(rng.randint(1, 3), PCLS[:rng.randint(1, 4)], rng.uniform(0.5, 2), k, 0, eta, rng)
        if len(rows) < 2:
            continue
        km = kappa_min([r["m"] / r["P"] for r in rows], eta)[0]
        if km > k + 1e-12:
            bad += 1
    check(bad == 0, f"kappa_min <= true kappa in every trial ({bad} violations)")

    print("selftest 2: recovery, relative scatter, kappa = 0.15, theta0 = 0, n = 128")
    rows = synth(32, PCLS, 0.96, 0.15, 0.0, 0.0005, rng)
    res = analyse_rings(rows, 0.0005, out, "synthetic relative", boot=200)
    check(0.135 <= res["kappa_min_prop"] <= 0.15, f"kappa_min {res['kappa_min_prop']:.4f} in [0.135, 0.15]")
    k90 = res["quantiles_global"]["0.9"]["point"]
    check(abs(k90 - 0.135) < 0.03, f"k90 {k90:.3f} ~ 0.9*kappa = 0.135 (uniform eps)")
    check(res["p_theta"] >= 0.01, f"no spurious theta0 (p = {res['p_theta']:.3f})")
    check(not any(v["refuted"] for v in limit_verdicts(res["kappa_min_prop"])[:1]),
          "rule E not refuted at kappa = 0.15")
    check(limit_verdicts(res["kappa_min_prop"])[1]["refuted"], "rule A (1/11) refuted at kappa = 0.15")
    check(res["beta"] is not None and res["beta"] > 0.7, f"scatter shape beta {res['beta']:.2f} ~ 1")

    print("selftest 3: recovery with an offset, kappa = 0.10, s = 0.938, theta0 = 988 ps, n = 128")
    rows = synth(32, PCLS, 0.938, 0.10, 988.0, 0.0005, rng)
    res = analyse_rings(rows, 0.0005, out, "synthetic offset", boot=300)
    check(abs(res["theta0"] - 988) < 250, f"theta0 {res['theta0']:+.0f} within 250 ps of +988")
    check(abs(res["a_off"] - 0.938) < 0.02, f"a {res['a_off']:.4f} within 0.02 of 0.938")
    check(res["theta_ci"][0] <= 988 <= res["theta_ci"][1], f"988 inside theta0 CI {res['theta_ci']}")
    check(res["model_verdict"].startswith("OFFSET"), f"model verdict: {res['model_verdict']}")
    check(res["kappa_min_offset_ci"] <= 0.10 + 1e-9 and res["kappa_min_offset_ci"] >= 0.08,
          f"offset-model kappa_min {res['kappa_min_offset_ci']:.4f} in [0.08, 0.10]")
    check(res["kappa_min_prop"] > 0.10, f"ignoring theta0 inflates kappa_min to {res['kappa_min_prop']:.4f}")

    print("selftest 4: NEGATIVE CONTROL, kappa = 0.30 > rule E's 0.1988")
    rows = synth(32, PCLS, 1.0, 0.30, 0.0, 0.0005, rng)
    res = analyse_rings(rows, 0.0005, out, "synthetic kappa=0.30", boot=0)
    v = limit_verdicts(res["kappa_min_prop"])
    check(v[0]["refuted"], f"rule E reported EXCEEDED (kappa_min {res['kappa_min_prop']:.4f})")
    check(all(x["refuted"] for x in v), "rule A limits also reported exceeded")
    # and a population at 0.05 must NOT be reported as exceeding anything but nothing is "proved met"
    rows = synth(32, PCLS, 1.0, 0.04, 0.0, 0.0005, rng)
    res = analyse_rings(rows, 0.0005, out, "synthetic kappa=0.04", boot=0)
    check(not any(x["refuted"] for x in limit_verdicts(res["kappa_min_prop"])),
          f"kappa = 0.04: no limit reported exceeded (kappa_min {res['kappa_min_prop']:.4f})")

    print("selftest 4b: mixed rule-A model (kappa 1/22, theta 50 ps) on its own synthetic data")
    rows = []
    for L, Pm in PCLS:
        for i in range(32):
            P = Pm * rng.uniform(0.9, 1.1)
            rows.append((0.97 * ((1 + rng.uniform(-1, 1) / 22) * P + rng.uniform(-50, 50)), P))
    m_, P_ = [a for a, _ in rows], [b for _, b in rows]
    check(mixed_feasible(m_, P_, 1 / 22, 50.0), "data generated inside the mixed model is feasible")
    m2 = [x * (1.2 if i == 0 else 1.0) for i, x in enumerate(m_)]
    check(not mixed_feasible(m2, P_, 1 / 22, 50.0), "one path 20% slow makes it infeasible (negative control)")

    print("selftest 5: affine corner, c = 0.37, S/F in [2.8, 3.1], kappa = 0.08")
    rows = synth(32, PCLS, 1.0, 0.08, 0.0, 0.0, rng, F_S=((0.5, 0.6), (2.8, 3.1)), c=0.37)
    m = [r["m"] for r in rows]
    kA, cA = kappa_min_affine(m, [r["F"] for r in rows], [r["S"] for r in rows], free_scale=False)
    check(kA <= 0.08 + 1e-9 and kA >= 0.07, f"strict affine kappa_min {kA:.4f} in [0.07, 0.08]")
    check(abs(cA - 0.37) < 0.05, f"corner recovered c = {cA:.3f} ~ 0.37")
    kF, _ = kappa_min_affine(m, [r["F"] for r in rows], [r["S"] for r in rows], free_scale=True)
    check(kF <= kA + 1e-9, f"free-scale affine bound {kF:.4f} <= strict {kA:.4f}")

    print("selftest 6: two-path differential and censored data, kappa = 0.12, s = 0.95")
    prs = []
    kap, s = 0.12, 0.95
    for i in range(200):
        pa = rng.uniform(300, 3000)
        pb = pa * rng.uniform(0.8, 1.6)
        da = s * pa * (1 + rng.uniform(-kap, kap))
        db = s * pb * (1 + rng.uniform(-kap, kap))
        oc = "FAIL_LATE_FIRST" if db <= da else "PASS_UNCERTIFIED"
        prs.append(dict(die="d", session="x", pair=str(i), **{"class": "1"},
                        meas_a_ps=str(da), pred_a_ps=str(pa), meas_b_ps=str(db), pred_b_ps=str(pb),
                        outcome=oc if i % 2 else ""))
    res = analyse_pairs(prs, out, scale=s)
    mx_d = max(p["kappa_diff"] for p in res["pairs"])
    mx_c = max([p.get("censored_bound", 0) for p in res["pairs"]])
    mx_p = max(p["pair_bound"] for p in res["pairs"])
    check(mx_d <= kap + 1e-9, f"kappa_diff max {mx_d:.4f} <= 0.12 with the true s")
    check(mx_p <= kap + 1e-9, f"pair bound max {mx_p:.4f} <= 0.12")
    check(mx_c <= kap + 1e-9, f"censored bound max {mx_c:.4f} <= 0.12")
    check(mx_d >= 0.09, f"kappa_diff max {mx_d:.4f} recovers most of 0.12")

    print("selftest 7: coverage of the order-statistic UCB95 for the p90 (known s, n = 64)")
    cover = 0
    T = 300
    for t in range(T):
        e = [abs(rng.gauss(0, 0.1)) for _ in range(64)]
        u = order_stat_ucb(e, 0.9)
        true_q90 = 0.1 * 1.6448536   # |N(0,0.1)| 90th percentile
        cover += u is not None and u >= true_q90
    check(cover / T >= 0.92, f"UCB95 covered the true p90 in {cover}/{T} trials")

    print("selftest 8: summary-table path reproduces the Lean number")
    k = kappa_min([1.470, 0.773])[0]
    check(abs(k - 0.697 / 2.243) < 1e-12, f"(1.470-0.773)/(1.470+0.773) = {k:.4f} (guard_refuted_by_7link_rings)")

    if verbose:
        print("\n".join(out))
    print(f"\nselftest: {'PASS' if not fails else 'FAIL'} ({len(fails)} failures)")
    return 0 if not fails else 1


# ---------------------------------------------------------------- repo run

def repo(boot=1000, as_json=None):
    D = os.path.join(HERE, "data")
    out = []
    allres = {}
    out.append("kappa.py repo run -- every ring/two-path dataset found in the repo")
    out.append("limits: rule E %.4f, rule A %.4f (theta=0), %.4f (theta<=50ps)" %
               (KAPPA_E, KAPPA_A_REL, KAPPA_A_MIX))
    for fn, eta in (("ro_top_2026-08-03.csv", 0.0002), ("ro_top_2026-08-23.csv", 0.0002)):
        rows = load_rings(os.path.join(D, fn))
        allres[fn] = analyse_rings(rows, eta, out, fn + " (per-ring, n=5, one route, one session)",
                                   boot=boot)
    allres["ro_many_summary"] = analyse_summary(read_table(os.path.join(D, "ro_many_2026-08-23_summary.csv")), out)
    rows = load_rings(os.path.join(D, "f1_rings_ro_many_top.rebuild.tsv"))
    allres["model_only_ro_many"] = model_only(rows, out)
    allres["shmoo"] = analyse_pairs(read_table(os.path.join(D, "shmoo_ucmpi1_pairs.csv")), out)
    print("\n".join(out))
    if as_json:
        with open(as_json, "w") as f:
            json.dump(allres, f, indent=1, default=str)
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter,
                                 epilog=SCHEMA)
    sub = ap.add_subparsers(dest="cmd", required=True)
    a = sub.add_parser("rings", help="ring / absolute-path population(s)")
    a.add_argument("files", nargs="+")
    a.add_argument("--eta", type=float, default=0.0005, help="relative measurement error (default 0.0005)")
    a.add_argument("--boot", type=int, default=1000)
    a.add_argument("--json")
    b = sub.add_parser("pairs", help="two-path CSV")
    b.add_argument("file")
    b.add_argument("--scale", type=float, help="known session scale s (else median of absolute ratios)")
    b.add_argument("--trust-pass", action="store_true",
                   help="also show the bound a PASS_UNCERTIFIED would give if it certified the order")
    c = sub.add_parser("summary", help="published per-class quantile table")
    c.add_argument("file")
    r = sub.add_parser("rawlogs", help="cells/hw ro_many raw gNN.log directory + prediction TSV")
    r.add_argument("dir")
    r.add_argument("--pred", required=True)
    r.add_argument("--eta", type=float, default=0.0005)
    m = sub.add_parser("model", help="model-only proportionality of a prediction TSV")
    m.add_argument("file")
    s = sub.add_parser("selftest")
    s.add_argument("-v", action="store_true")
    p = sub.add_parser("repo", help="run on the datasets in formal/tools-A/kappa/data")
    p.add_argument("--boot", type=int, default=1000)
    p.add_argument("--json")
    args = ap.parse_args()
    out = []
    if args.cmd == "selftest":
        return selftest(args.v)
    if args.cmd == "repo":
        return repo(args.boot, args.json)
    if args.cmd == "rings":
        allres = {}
        for f in args.files:
            rows = load_rings(f)
            groups = {}
            for r_ in rows:
                groups.setdefault((r_["die"], r_["session"]), []).append(r_)
            for key, g in groups.items():
                allres[str(key)] = analyse_rings(g, args.eta, out, f"{f} {key}", boot=args.boot)
        print("\n".join(out))
        if args.json:
            with open(args.json, "w") as fh:
                json.dump(allres, fh, indent=1, default=str)
    elif args.cmd == "pairs":
        analyse_pairs(read_table(args.file), out, args.scale, args.trust_pass)
        print("\n".join(out))
    elif args.cmd == "summary":
        analyse_summary(read_table(args.file), out)
        print("\n".join(out))
    elif args.cmd == "rawlogs":
        rows = load_ro_many_raw(args.dir, args.pred)
        analyse_rings(rows, args.eta, out, f"ro_many raw {args.dir}")
        print("\n".join(out))
    elif args.cmd == "model":
        model_only(load_rings(args.file), out)
        print("\n".join(out))
    return 0


if __name__ == "__main__":
    sys.exit(main())
