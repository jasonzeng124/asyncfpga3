# A-inv-exp: the real exp-channel as an involution pair, slope bounds, loop resolution rate (probe InvExp)

STATUS (09:17 UTC): DONE. check.sh OK (below). File: `formal/lean/Formal/Core/Delay/InvolutionExp.lean`
(Mathlib `Analysis.SpecialFunctions.Log.Basic` + `Analysis.Real.Sqrt`; both oleans present this session).
Check command and result: see "Check" at the end. `Wip/InvTrace/ExpReal.lean` is superseded by it
(its `realExpLog'` is `realExpLog` here, its `real_exp_channel_runt` is `expR_pulse_cancel_iff`); the
lead may delete it. Scratch (not committed): `scratchpad/InvExp/{table.py,gopt.py,table.out,deps.sh}`.

## The channel (what it is, and which formula)

`expR τ Tp hτ hTp : InvolutionPair` is A's `ExpLog.expPair` with Mathlib's `Real.exp`/`Real.log`
(`E x = e^{x/τ}`, `L y = τ ln y`), so every abstract `ExpLog` theorem now holds for real exp/log with no
extra hypothesis. Symmetric (`δ↑ = δ↓`), `τ > 0`, `T_p > 0`:

    δ(T) = T_p + τ ln(2 − e^{−(T+T_p)/τ})          (T > −δ∞)
         = δ∞ + τ ln(1 − e^{−(T+δ∞)/τ})            (expR_paper)
    δ∞ = T_p + τ ln 2,   δmin = T_p                (expR_infUp, expR_dmin)

Derivation (in `Involution.lean`'s docstring): pure delay `T_p`, then a first-order RC stage with
threshold 1/2 that starts from wherever the previous opposite ramp has reached; `T` is the input time
minus the previous output crossing. Source: M. Függer, R. Najvirt, T. Nowak, U. Schmid, "A Faithful
Binary Circuit Model", IEEE TCAD 39(10):2784-2797, 2020 (doi 10.1109/TCAD.2019.2937748), which defines
the exp-channel; its full text was NOT readable from this sandbox (web search gives only the abstract
pages: hal-02395251, repositum.tuwien.at 20.500.12708/140078), so the symbols were not compared with
the paper's.

The task's form `δ(T) = τ ln(1 − e^{−(T+δ∞−T_p)/τ}) + δ∞` is **not** an involution when `T_p` is the
pure delay and `δ∞ = T_p + τ ln 2`: `bad_not_involution` proves `−δ(−δ(0)) ≠ 0` for every
`0 < T_p < τ ln 2` (with that form `δ(0) = T_p` and the identity would force `(e^{T_p/τ} − 1)² = 0`).
So either the paper's `T_p` means something else in that formula or the formula was misremembered;
the form used here is the one that IS an involution (`ExpLog.exp_inv`); in δ∞ terms it reads
`δ(T) = δ∞ + τ ln(1 − e^{−(T+δ∞)/τ})`, the task's shape with `T_p` absent from the exponent.

## What is proved (plain language)

Assumed: `τ > 0`, `T_p > 0`; one symmetric exp-channel; for the loop results, InvolutionLoop's setting
(runt `[0, s)` ORed in zero time into this channel, output fed back; widths `wd P s n` of the orbit,
B's `loop_orb` bridge for the signal-level meaning, see A-inv-loop.md).

1. **Instance and pulse threshold.** `expR` is an `InvolutionPair`; `expR_dmin`: `δmin = T_p`;
   `expR_pulse`: `channel [a, a+Δ]` (Δ > 0) is `[]` if `Δ ≤ τ ln 2`, else
   `[a + δ∞, a + δ∞ + pulseWidth Δ]`; `expR_pulse_cancel_iff`: cancelled ⇔ `Δ ≤ τ ln 2` (exact, the
   boundary is cancelled, the "≤" rule of InvolutionTrace).
2. **Stationary train in closed form** (`expR_stat`, `expR_crit`). With `a = e^{T_p/τ}` and
   `x = (√(1+8a) − 1)/2` (the positive root of `x² + x = 2a`): the train is high = low =
   `w* = τ ln x`, it is the only stationary train, `0 < w* < T_p` (`wStar_pos`, `wStar_lt_Tp`),
   `δ(−w*) = 2w*` (`expR_up_wStar`), `2w* < δ∞` (`two_wStar_lt`), and the critical runt is
   **`s* = δ∞ − w* = T_p + τ ln(2/x)`**.
3. **Slope bounds** (elementary: `ln y ≤ y − 1`, `1 + t ≤ e^t`; no derivatives). Writing
   `u(T) = e^{−(T+T_p)/τ}`, `δ' = u/(2−u)`, decreasing in `T` (δ is concave):
   - `slope_lower` (`H_SLOPE`): for `−δ∞ < a ≤ b ≤ 0`, `κ(b − a) ≤ δ(b) − δ(a)` with
     **`κ = q/(2 − q)`, `q = e^{−T_p/τ}`** (= δ'(0)). Domain `(−δ∞, 0]`: every argument `−wd n` and
     `s − δ∞` the orbit uses while cancellation-free (InvolutionLoopRate's `H_SLOPE` domain).
   - `slope_upper`, `expR_lip` (`H_LIP`): for `a, b ≥ −M`, `M < δ∞`,
     `|δ(a) − δ(b)| ≤ K(M)|a − b|` with **`K(M) = r/(2 − r)`, `r = e^{(M − T_p)/τ}`** (= δ'(−M)).
     Used with `M = w* + g`, `0 < g ≤ w*` (so `M ≤ 2w* < δ∞`): the domain `[−(w*+g), ∞)` contains
     every argument while the widths stay within `g` of `w*`, which is what `dev_lower` needs.
   `K(M) → ∞` as `M → δ∞` (δ' blows up at the domain edge), so no global `K` exists; that is why M is
   tied to the orbit's neighbourhood of `w*`.
4. **Rate law for this channel** (`exp_laps`, `exp_laps_log`, `exp_resolution`). For
   `0 < s < δ∞`, `m` = first cancellation index (`Chain P s m`, `wd P s m ≤ 0`), `d = |s − s*|`,
   any `0 < g ≤ w*`, `K = K(w* + g)`:
   - `(1+K)^(N+1) d < g → N < m`, i.e. **`m > ln(g/d)/ln(1+K) − 1`**;
   - `δ∞ ≤ (1+κ)^(N+1) d → m ≤ N`, i.e. **`m ≤ ⌈ln(δ∞/d)/ln(1+κ)⌉ − 1`**.
   - `exp_resolution`: for `s ≠ s*` such an `m` exists, and `m` is odd (q latched at 1) iff `s > s*`
     (even: lost). All hypotheses of `laps_two_sided` are discharged; nothing about the channel is
     assumed beyond `τ, T_p > 0`.

## What is NOT covered
- The bounds are LOOSE, especially the upper one: κ is the global minimum slope δ'(0) on `(−δ∞, 0]`,
  while the orbit near `s*` sees the local slope δ'(−w*) (the true per-transition gain
  `λ = 1 + δ'(−w*)`). A tight two-sided law needs a local slope lower bound on a neighbourhood of
  `−w*` plus control of the escape phase (not attempted). The lower bound is within ~2× of the
  computed `m` when `g` is optimised (table).
- Asymmetric exp channels (`τ↑ ≠ τ↓`, `T_p↑ ≠ T_p↓`), other thresholds `V_th ≠ 1/2`.
- Noise/jitter (any lap-to-lap jitter larger than the current deviation decides the race instead),
  multi-cell loops, whether a LUT + route IS an exp involution channel (B's `H_CH`), and which τ, T_p a
  real loop has. Reading TLOOP (an SDF transport number) as δ∞ is a modelling choice.
- The time of the last transition is not stated in Lean for the exp channel (InvolutionLoopRate's
  `time_lower` would give `lo N ≥ δ∞ + N g/2` under `2(1+K)^(N+1)d < g`; not instantiated).

## Numeric table (COMPUTATION in the model, not silicon, not a theorem)

`scratchpad/InvExp/table.py`: iterates InvolutionLoop's orbit recurrence (`wd0 = (s−δ∞) + δ(s−δ∞)`,
`wd_{n+1} = δ(−wd_n) − wd_n`) in Python decimal (60 digits) and IEEE double (Float); both agree to
the digits shown (double differs by < 1 ps in t_last at 1e-9 ps). TLOOP = 424 ps read as δ∞, so
`T_p = 424 − τ ln 2`. `m` = first cancellation index (transitions of q before it resolves; laps ≈ m/2);
`t_last` = time of the last surviving q edge `lo(m−1)`, from the r1 rise. Lean bounds: lower with the
best `g` (gopt.py), upper with κ.

| τ (ps) | T_p | w* | s* (s*/TLOOP) | κ = δ'(0) | λ = 1+δ'(−w*) | τ_res = w*/ln λ |
|---|---|---|---|---|---|---|
| 40 | 396.27 | 211.90 | 212.10 (0.5002) | 2.49e-5 | 1.00500 | 42 450 ps |
| 100 | 354.69 | 206.00 | 218.00 (0.5141) | 1.46e-2 | 1.12745 | 1 717 ps |
| 200 | 285.37 | 177.53 | 246.47 (0.5813) | 1.36e-1 | 1.41163 | 515 ps |

| τ | d = \|s−s*\| | m (s*+d → latched / s*−d → lost) | t_last (ps) | Lean: m > (best g) | Lean: m ≤ |
|---|---|---|---|---|---|
| 40 | 1 ps | 875 / 876 | 185 462 / 185 659 | 371 | 242 802 |
| 40 | 1 fs | 2259 / 2260 | 478 730 / 478 927 | 1 504 | 520 040 |
| 40 | 1e-6 fs | 5027 / 5028 | 1 065 266 / 1 065 462 | 4 080 | 1 074 516 |
| 100 | 1 ps | 41 / 42 | 8 562 / 8 740 | 19 | 416 |
| 100 | 1 fs | 99 / 100 | 20 500 / 20 675 | 68 | 892 |
| 100 | 1e-6 fs | 215 / 214 | 44 371 / 44 194 | 175 | 1 844 |
| 200 | 1 ps | 15 / 14 | 2 819 / 2 671 | 7 | 47 |
| 200 | 1 fs | 35 / 34 | 6 370 / 6 223 | 24 | 101 |
| 200 | 1e-6 fs | 75 / 74 | 13 474 / 13 326 | 62 | 209 |

Every computed m lies between the two Lean bounds (as it must; a computed m outside them would have
been a bug in one of the two). Parity matches `exp_resolution` (odd = latched above s*, even = lost
below) in every row.

**Resolution-time constant of the model.** t_last grows linearly in ln(1/d): fitting the 1 ps and 1e-6 fs
rows gives 42 460 / 1 728 / 514 ps per e-fold for τ = 40 / 100 / 200, matching the linearised
`τ_res = w*/ln(1 + δ'(−w*))` (time per transition ≈ w*, gain per transition λ). This agrees with
A-fid3 §3's TAU_eff (1741 ps at τ = 100, 503 ps at τ = 200, obtained there by another Float fit). It is
**3.4× (τ = 200) to 280× (τ = 40) longer than the research GLS's `TAU = 150 ps`**, and grows as the loop
becomes more transport-like (small τ), because the gain per transition is δ'(−w*) ≈ e^{(w*−T_p)/τ}/…,
tiny when the train width w* is many τ below T_p. Plainly: this is the deterministic digital model of
one lumped involution channel, with an assumed τ; it is not silicon. Real loops have noise that ends
the pulse train sooner, and nothing here measures τ. The only test is the board (hw/arb_mtbf
resolution-time histogram, A-fid3).

## Check

    formal/check.sh Formal/Core/Delay/InvolutionTrace.lean Formal/Cells/CElemInvolution.lean \
      Formal/Cells/ArbInvolution.lean Formal/Core/Delay/InvolutionLoop.lean \
      Formal/Core/Delay/InvolutionLoopBridge.lean Formal/Core/Delay/InvolutionLoopRate.lean \
      Formal/Core/Delay/InvolutionExp.lean

(the first six are listed only because their oleans are not in `.lake/build`; none is edited.)
Result (09:13 UTC): `[audit] 1227 declarations checked` / `[check] OK` (count covers all seven modules).
The three unused-variable linter warnings of the first compile were removed (unused hypotheses dropped); a warning-free rerun was not separately checked.

Controls (`Wip/InvExp/NegControl.lean`, not claimed, compiled against a scratch overlay): (1) claiming the
slope lower bound with 2κ from `slope_lower` fails (type mismatch); (2) the threshold pulse Δ = τ ln 2 is
cancelled: elaborates; (3) the same proof for Δ = 1.01·τ ln 2 fails (application type mismatch at `le_rfl`).
