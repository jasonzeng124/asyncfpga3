import Formal.Core.Delay.InvolutionLoopBridge

/-!
# The involution OR loop: how many transitions before it resolves (rate law)

Probe InvLoop2 (shard A).  Setting of `InvolutionLoop`: the runt `[0, s)` ORed into one
involution channel `P` whose output is fed back; `wd P s n` are the pulse widths of `q`,
`s* = crit P l` with `Stat P h l` the stationary train; the critical widths are
`wd P s* n = h, l, h, l, ...` (`wd_crit`).  The run is cancellation-free for `n`
transitions while `Chain P s n`; the first index `m` with `wd P s m ≤ 0` is the first
cancellation, after which `q` is constant (`InvolutionLoopSignal`).

The deviation `e n = |wd P s n - wd P s* n|` obeys, through the half-lap map
`w ↦ δ(-w) - w` (slope `-(1 + δ')`):
* `dev_lower` (named hypothesis `H_LIP`: slope of `δ↑, δ↓` at most `K` on `[-M, ∞)`,
  `M ≥ max(h, l) + g`, `g ≤ min(h, l)`): `e n ≤ (1+K)^(n+1) |s - s*|`.  So if
  `(1+K)^(N+1) |s - s*| < g`, the first `N + 1` widths are positive (`Chain P s (N+1)`):
  at least `N + 1` cancellation-free transitions, i.e. `m > log(g/|s-s*|)/log(1+K) - 1`.
  `time_lower`: with `g/2`, the `N`-th transition is after `δ∞↑ + N g/2`.
* `dev_upper` (named hypothesis `H_SLOPE`: slope at least `κ ≥ 0` on the part of the
  domain that widths reach, `(-δ∞, 0]`): while the run is cancellation-free,
  `e n ≥ (1+κ)^(n+1) |s - s*|`.  `laps_upper`: every width is below `δ∞` of its side, so
  `Chain P s (N+1)` forces `(1+κ)^(N+1) |s - s*| < δ∞`; i.e.
  `m < log(δ∞/|s-s*|)/log(1+κ)`, a bound only when `κ > 0`.
* Together (`laps_two_sided`): `m(s)` is between `log(g/|s-s*|)/log(1+K) - 1` and
  `log(max δ∞ / |s-s*|)/log(1+κ)`: logarithmic in `1/|s - s*|`, with the per-transition gain
  between `1 + κ` and `1 + K`.  (Stated in power form; no logarithm is used.)
* `quantHyp_of_stat`: B's `QuantHyp P s* K M g` (the hypotheses of `window_lower`) holds
  at A's `s*` under `H_LIP` with `g = min`-type margins, so B's `window_lower` applies to
  `s*`; B's bound needs `2 (1+2K)^N (1+K) |s - s*| < g` (transition times), ours
  `(1+K)^(N+1) |s - s*| < g` (widths): ours is weaker as a hypothesis, B's gives the time.

Not covered: whether a measured LUT + route satisfies `H_LIP` / `H_SLOPE` (for A's
exp-channel the slope is positive and bounded on `(-δ∞ + ε, 0]`, not proved here); noise
(any lap-to-lap jitter larger than `e n` decides the race instead).
-/

namespace Formal.Core.InvolutionLoop.Rate
open Formal.Core.DelayInvolution Formal.Core.InvolutionLoop

variable {P : InvolutionPair}

/-! ## Critical widths -/

theorem wc_cases {h l : ℝ} (S : Stat P h l) (n : ℕ) :
    (n % 2 = 0 ∧ wd P (crit P l) n = h) ∨ (n % 2 = 1 ∧ wd P (crit P l) n = l) := by
  obtain ⟨k, hk | hk⟩ : ∃ k, n = 2 * k ∨ n = 2 * k + 1 := ⟨n / 2, by omega⟩
  · left; subst hk; exact ⟨by omega, (wd_crit S k).1⟩
  · right; subst hk; exact ⟨by omega, (wd_crit S k).2⟩

theorem infAt_succ_even {n : ℕ} (h : n % 2 = 0) : P.infAt (n + 1) = P.infDown := by
  unfold InvolutionPair.infAt; rw [if_neg (by omega)]

theorem infAt_succ_odd {n : ℕ} (h : n % 2 = 1) : P.infAt (n + 1) = P.infUp := by
  unfold InvolutionPair.infAt; rw [if_pos (by omega)]

theorem infAt_add_two' (n : ℕ) : P.infAt (n + 2) = P.infAt n := by
  unfold InvolutionPair.infAt
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg (by omega), if_neg (by omega)]

theorem wc_lt {h l : ℝ} (S : Stat P h l) (n : ℕ) : wd P (crit P l) n < P.infAt (n + 1) := by
  rcases wc_cases S n with ⟨hp, e⟩ | ⟨hp, e⟩
  · rw [e, infAt_succ_even hp]; exact S.h_lt
  · rw [e, infAt_succ_odd hp]; exact S.l_lt

/-- The next width stays inside the next delay's domain. -/
theorem wd_succ_lt {s : ℝ} {n : ℕ} (h0 : 0 < wd P s n) (h1 : wd P s n < P.infAt (n + 1)) :
    wd P s (n + 1) < P.infAt (n + 1 + 1) := by
  rw [wd_succ, show n + 1 + 1 = n + 2 from rfl, infAt_add_two']
  rcases Nat.mod_two_eq_zero_or_one n with hp | hp
  · rw [delayAt_even P hp]
    rw [infAt_succ_even hp] at h1
    have := P.up_lt (-wd P s n) (by linarith)
    unfold InvolutionPair.infAt; rw [if_pos hp]; linarith
  · rw [delayAt_odd P hp]
    rw [infAt_succ_odd hp] at h1
    have := P.down_lt (-wd P s n) (by linarith)
    unfold InvolutionPair.infAt; rw [if_neg (by omega)]; linarith

/-! ## One-step deviation bounds -/

/-- Lipschitz step of the half-lap map `w ↦ f(-w) - w`. -/
theorem lip_half {f : ℝ → ℝ} {K M w v : ℝ}
    (hL : ∀ a b, -M ≤ a → -M ≤ b → |f a - f b| ≤ K * |a - b|) (hw : w ≤ M) (hv : v ≤ M) :
    |(f (-w) - w) - (f (-v) - v)| ≤ (1 + K) * |w - v| := by
  have h1 := hL (-w) (-v) (by linarith) (by linarith)
  rw [show -w - -v = -(w - v) by ring, abs_neg] at h1
  have h2 : |(f (-w) - w) - (f (-v) - v)| ≤ |f (-w) - f (-v)| + |w - v| := by
    rw [show (f (-w) - w) - (f (-v) - v) = (f (-w) - f (-v)) + -(w - v) by ring]
    refine le_trans (abs_add_le _ _) (le_of_eq ?_)
    rw [abs_neg]
  linarith

/-- Lipschitz bound of the first width map `x ↦ x + f x`. -/
theorem lip_base {f : ℝ → ℝ} {K M x y : ℝ}
    (hL : ∀ a b, -M ≤ a → -M ≤ b → |f a - f b| ≤ K * |a - b|) (hx : -M ≤ x) (hy : -M ≤ y) :
    |(x + f x) - (y + f y)| ≤ (1 + K) * |x - y| := by
  have h1 := hL x y hx hy
  have h2 : |(x + f x) - (y + f y)| ≤ |x - y| + |f x - f y| := by
    rw [show (x + f x) - (y + f y) = (x - y) + (f x - f y) by ring]; exact abs_add_le _ _
  linarith

/-- Expansion of the half-lap map under a slope lower bound `κ`. -/
theorem smono_half {f : ℝ → ℝ} {L κ w v : ℝ} (hκ : 0 ≤ κ)
    (hS : ∀ a b, -L < a → a ≤ b → b ≤ 0 → κ * (b - a) ≤ f b - f a)
    (hw0 : 0 ≤ w) (hwL : w < L) (hv0 : 0 ≤ v) (hvL : v < L) :
    (1 + κ) * |w - v| ≤ |(f (-w) - w) - (f (-v) - v)| := by
  rcases le_total w v with c | c
  · have h := hS (-v) (-w) (by linarith) (by linarith) (by linarith)
    have hp : 0 ≤ κ * (v - w) := mul_nonneg hκ (by linarith)
    rw [abs_of_nonpos (by linarith : w - v ≤ 0)]
    rw [abs_of_nonneg (by linarith : 0 ≤ (f (-w) - w) - (f (-v) - v))]
    linarith
  · have h := hS (-w) (-v) (by linarith) (by linarith) (by linarith)
    have hp : 0 ≤ κ * (w - v) := mul_nonneg hκ (by linarith)
    rw [abs_of_nonneg (by linarith : 0 ≤ w - v)]
    rw [abs_of_nonpos (by linarith : (f (-w) - w) - (f (-v) - v) ≤ 0)]
    linarith

/-- Expansion of the first width map `x ↦ x + f x` under a slope lower bound. -/
theorem smono_base {f : ℝ → ℝ} {L κ x y : ℝ} (hκ : 0 ≤ κ)
    (hS : ∀ a b, -L < a → a ≤ b → b ≤ 0 → κ * (b - a) ≤ f b - f a)
    (hx0 : -L < x) (hx : x ≤ 0) (hy0 : -L < y) (hy : y ≤ 0) :
    (1 + κ) * |x - y| ≤ |(x + f x) - (y + f y)| := by
  rcases le_total x y with c | c
  · have h := hS x y hx0 c hy
    have hp : 0 ≤ κ * (y - x) := mul_nonneg hκ (by linarith)
    rw [abs_of_nonpos (by linarith : x - y ≤ 0)]
    rw [abs_of_nonpos (by linarith : (x + f x) - (y + f y) ≤ 0)]
    linarith
  · have h := hS y x hy0 c hx
    have hp : 0 ≤ κ * (x - y) := mul_nonneg hκ (by linarith)
    rw [abs_of_nonneg (by linarith : 0 ≤ x - y)]
    rw [abs_of_nonneg (by linarith : 0 ≤ (x + f x) - (y + f y))]
    linarith

/-! ## Lower bound on the number of transitions -/

/-- **Deviation lower-bound law (`H_LIP`).**  If `δ↑, δ↓` have slope at most `K` on
`[-M, ∞)` with `g ≤ min(h, l)` and `max(h, l) + g ≤ M`, and
`(1+K)^(N+1) |s - s*| < g`, then the first `N + 1` widths are positive and each is within
`(1+K)^(j+1) |s - s*|` of the critical width. -/
theorem dev_lower {h l s K M g : ℝ} (S : Stat P h l) (hK : 0 ≤ K)
    (hL : ∀ n a b, -M ≤ a → -M ≤ b → |P.delayAt n a - P.delayAt n b| ≤ K * |a - b|)
    (hgh : g ≤ h) (hgl : g ≤ l) (hMh : h + g ≤ M) (hMl : l + g ≤ M) (N : ℕ)
    (hN : (1 + K) ^ (N + 1) * |s - crit P l| < g) :
    Chain P s (N + 1) ∧
      ∀ j ≤ N, |wd P s j - wd P (crit P l) j| ≤ (1 + K) ^ (j + 1) * |s - crit P l| := by
  set c := crit P l with hcdef
  set A := |s - c| with hAdef
  have hA0 : 0 ≤ A := abs_nonneg _
  have hpow : ∀ j ≤ N, (1 + K) ^ (j + 1) * A ≤ (1 + K) ^ (N + 1) * A := fun j hj =>
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith) (by omega)) hA0
  have hwc : ∀ j, g ≤ wd P c j ∧ wd P c j + g ≤ M := fun j => by
    rcases wc_cases S j with ⟨_, e⟩ | ⟨_, e⟩ <;> rw [e] <;> exact ⟨by linarith, by linarith⟩
  have hAg : A < g := by
    have : A ≤ (1 + K) ^ (N + 1) * A := le_mul_of_one_le_left hA0 (one_le_pow₀ (by linarith))
    linarith
  have hL1 : ∀ a b, -M ≤ a → -M ≤ b → |P.down a - P.down b| ≤ K * |a - b| := by
    intro a b ha hb; have := hL 1 a b ha hb; rwa [delayAt_odd P (n := 1) rfl] at this
  have key : ∀ j ≤ N, |wd P s j - wd P c j| ≤ (1 + K) ^ (j + 1) * A := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [wd_zero, wd_zero, zero_add, pow_one]
      have hcI : c - P.infUp = -l := by rw [hcdef]; unfold crit; ring
      have hsI : -M ≤ s - P.infUp := by
        have := neg_abs_le (s - c)
        have : s - P.infUp = (s - c) + (c - P.infUp) := by ring
        linarith
      have := lip_base hL1 hsI (show -M ≤ c - P.infUp by rw [hcI]; linarith)
      rw [show s - P.infUp - (c - P.infUp) = s - c by ring] at this
      exact this
    | succ j ih =>
      intro hj
      have i0 := ih (by omega)
      have hb := hpow j (by omega)
      have hw : wd P s j ≤ M := by
        have := (abs_le.mp i0).2; linarith [(hwc j).2]
      rw [wd_succ, wd_succ]
      have h1 := lip_half (f := P.delayAt j) (v := wd P c j) (hL j) hw (by linarith [(hwc j).2])
      calc _ ≤ (1 + K) * |wd P s j - wd P c j| := h1
        _ ≤ (1 + K) * ((1 + K) ^ (j + 1) * A) := mul_le_mul_of_nonneg_left i0 (by linarith)
        _ = (1 + K) ^ (j + 1 + 1) * A := by ring
  refine ⟨fun j hj => ?_, key⟩
  have := (abs_le.mp (key j (by omega))).1
  have := hpow j (by omega)
  linarith [(hwc j).1]

/-- **Time lower bound.** Under the same hypotheses with margin `g/2`, the `N`-th
transition of `q` is after `δ∞↑ + N·g/2`. -/
theorem time_lower {h l s K M g : ℝ} (S : Stat P h l) (hK : 0 ≤ K)
    (hL : ∀ n a b, -M ≤ a → -M ≤ b → |P.delayAt n a - P.delayAt n b| ≤ K * |a - b|)
    (hgh : g ≤ h) (hgl : g ≤ l) (hMh : h + g ≤ M) (hMl : l + g ≤ M) (N : ℕ)
    (hN : 2 * ((1 + K) ^ (N + 1) * |s - crit P l|) < g) :
    Chain P s (N + 1) ∧ P.infUp + N * (g / 2) ≤ lo P s N := by
  have hg : 0 < g := by
    have : 0 ≤ (1 + K) ^ (N + 1) * |s - crit P l| :=
      mul_nonneg (pow_nonneg (by linarith) _) (abs_nonneg _)
    linarith
  obtain ⟨hc, hd⟩ := dev_lower S hK hL hgh hgl hMh hMl N (by linarith)
  refine ⟨hc, lo_lin (P := P) (fun n hn => ?_)⟩
  have h1 := (abs_le.mp (hd n (by omega))).1
  have h2 : (1 + K) ^ (n + 1) * |s - crit P l| ≤ (1 + K) ^ (N + 1) * |s - crit P l| :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith) (by omega)) (abs_nonneg _)
  have h3 : g ≤ wd P (crit P l) n := by
    rcases wc_cases S n with ⟨_, e⟩ | ⟨_, e⟩ <;> rw [e] <;> linarith
  linarith

/-! ## Upper bound on the number of transitions -/

/-- **Deviation growth law (`H_SLOPE`).**  If `δ_n` has slope at least `κ ≥ 0` on
`(-δ∞, 0]` (the arguments widths reach), then while the run is cancellation-free every
deviation from the critical train is at least `(1+κ)^(j+1) |s - s*|`, and every width
stays in the next delay's domain. -/
theorem dev_upper {h l s κ : ℝ} (S : Stat P h l) (hκ : 0 ≤ κ)
    (hS : ∀ n a b, -P.infAt (n + 1) < a → a ≤ b → b ≤ 0 →
      κ * (b - a) ≤ P.delayAt n b - P.delayAt n a)
    (hs0 : 0 < s) (hsI : s < P.infUp) (N : ℕ) (hc : Chain P s N) :
    ∀ j ≤ N, (1 + κ) ^ (j + 1) * |s - crit P l| ≤ |wd P s j - wd P (crit P l) j| ∧
      wd P s j < P.infAt (j + 1) := by
  set c := crit P l with hcdef
  set A := |s - c| with hAdef
  have hc0 : 0 < c := crit_pos S
  have hcI : c < P.infUp := crit_lt S
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨?_, ?_⟩
    · rw [wd_zero, wd_zero, zero_add, pow_one]
      have hS1 : ∀ a b, -P.infUp < a → a ≤ b → b ≤ 0 → κ * (b - a) ≤ P.down b - P.down a := by
        intro a b ha hab hb
        have := hS 1 a b (by rw [infAt_succ_odd (n := 1) rfl]; exact ha) hab hb
        rwa [delayAt_odd P (n := 1) rfl] at this
      have := smono_base hκ hS1 (x := s - P.infUp) (y := c - P.infUp)
        (by linarith) (by linarith) (by linarith) (by linarith)
      rw [show s - P.infUp - (c - P.infUp) = s - c by ring] at this
      exact this
    · rw [infAt_succ_even (n := 0) rfl]; exact wd0_lt_infDown hs0 hsI
  | succ j ih =>
    intro hj
    obtain ⟨i0, i1⟩ := ih (by omega)
    have hp : 0 < wd P s j := hc j (by omega)
    have hcp : 0 < wd P c j := wd_crit_pos S j
    refine ⟨?_, wd_succ_lt hp i1⟩
    rw [wd_succ, wd_succ]
    have h1 := smono_half (f := P.delayAt j) hκ (hS j) (le_of_lt hp) i1 (le_of_lt hcp)
      (wc_lt S j)
    calc (1 + κ) ^ (j + 1 + 1) * A = (1 + κ) * ((1 + κ) ^ (j + 1) * A) := by ring
      _ ≤ (1 + κ) * |wd P s j - wd P c j| := mul_le_mul_of_nonneg_left i0 (by linarith)
      _ ≤ _ := h1

/-- **Upper bound on the transitions before resolution.** Under `H_SLOPE`, a run that is
cancellation-free for `N + 1` widths has `(1+κ)^(N+1) |s - s*| < δ∞` of the side of
width `N`; so once `(1+κ)^(N+1) |s - s*| ≥ max(δ∞↑, δ∞↓)` it has cancelled among its
first `N + 1` widths. -/
theorem laps_upper {h l s κ : ℝ} (S : Stat P h l) (hκ : 0 ≤ κ)
    (hS : ∀ n a b, -P.infAt (n + 1) < a → a ≤ b → b ≤ 0 →
      κ * (b - a) ≤ P.delayAt n b - P.delayAt n a)
    (hs0 : 0 < s) (hsI : s < P.infUp) (N : ℕ) (hc : Chain P s (N + 1)) :
    (1 + κ) ^ (N + 1) * |s - crit P l| < max P.infUp P.infDown := by
  obtain ⟨i0, i1⟩ := dev_upper S hκ hS hs0 hsI (N + 1) hc N (by omega)
  have hp : 0 < wd P s N := hc N (by omega)
  have hcp : 0 < wd P (crit P l) N := wd_crit_pos S N
  have hcl := wc_lt S N
  have hmax : P.infAt (N + 1) ≤ max P.infUp P.infDown := by
    unfold InvolutionPair.infAt; split
    · exact le_max_left _ _
    · exact le_max_right _ _
  have : |wd P s N - wd P (crit P l) N| < P.infAt (N + 1) :=
    abs_lt.mpr ⟨by linarith, by linarith⟩
  linarith

theorem not_chain_of_big {h l s κ : ℝ} (S : Stat P h l) (hκ : 0 ≤ κ)
    (hS : ∀ n a b, -P.infAt (n + 1) < a → a ≤ b → b ≤ 0 →
      κ * (b - a) ≤ P.delayAt n b - P.delayAt n a)
    (hs0 : 0 < s) (hsI : s < P.infUp) (N : ℕ)
    (hbig : max P.infUp P.infDown ≤ (1 + κ) ^ (N + 1) * |s - crit P l|) :
    ¬ Chain P s (N + 1) := fun hc => by
  have := laps_upper S hκ hS hs0 hsI N hc; linarith

/-- **Two-sided law for the first cancellation index.** Under both slope bounds, the
first cancellation index `m` of the run (`Chain P s m`, `wd P s m ≤ 0`) satisfies:
`(1+K)^(N+1) |s - s*| < g → N < m` and
`max δ∞ ≤ (1+κ)^(N+1) |s - s*| → m ≤ N`. -/
theorem laps_two_sided {h l s K M g κ : ℝ} (S : Stat P h l) (hK : 0 ≤ K) (hκ : 0 ≤ κ)
    (hL : ∀ n a b, -M ≤ a → -M ≤ b → |P.delayAt n a - P.delayAt n b| ≤ K * |a - b|)
    (hS : ∀ n a b, -P.infAt (n + 1) < a → a ≤ b → b ≤ 0 →
      κ * (b - a) ≤ P.delayAt n b - P.delayAt n a)
    (hgh : g ≤ h) (hgl : g ≤ l) (hMh : h + g ≤ M) (hMl : l + g ≤ M)
    (hs0 : 0 < s) (hsI : s < P.infUp) {m : ℕ} (hcm : Chain P s m) (hm : wd P s m ≤ 0)
    (N : ℕ) :
    ((1 + K) ^ (N + 1) * |s - crit P l| < g → N < m) ∧
    (max P.infUp P.infDown ≤ (1 + κ) ^ (N + 1) * |s - crit P l| → m ≤ N) := by
  refine ⟨fun hN => ?_, fun hbig => ?_⟩
  · by_contra hc
    have := (dev_lower S hK hL hgh hgl hMh hMl N hN).1 m (by omega)
    linarith
  · by_contra hc
    exact not_chain_of_big S hκ hS hs0 hsI N hbig (fun j hj => hcm j (by omega))

/-! ## Comparison with B's `QuantHyp` / `window_lower` -/

/-- Under `H_LIP` (with the margins above, `0 < g`), A's critical runt satisfies B's
`QuantHyp`, so B's `window_lower` applies to `s* = crit P l`. -/
theorem quantHyp_of_stat {h l K M g : ℝ} (S : Stat P h l) (hK : 0 ≤ K) (hg : 0 < g)
    (hL : ∀ n a b, -M ≤ a → -M ≤ b → |P.delayAt n a - P.delayAt n b| ≤ K * |a - b|)
    (hgh : g ≤ h) (hgl : g ≤ l) (hMh : h + g ≤ M) (hMl : l + g ≤ M) :
    Formal.Cells.CElemInvolution.QuantHyp P (crit P l) K M g := by
  have hw : ∀ n, Formal.Cells.CElemInvolution.orb P (crit P l) (n + 1) -
      Formal.Cells.CElemInvolution.orb P (crit P l) n = wd P (crit P l) n := fun n => by
    unfold wd; rw [Bridge.lo_eq_orb, Bridge.lo_eq_orb]
  refine ⟨hL, hK, hg, fun n => ?_, fun n => ?_, ?_⟩
  · rw [hw]; rcases wc_cases S n with ⟨_, e⟩ | ⟨_, e⟩ <;> rw [e] <;> linarith
  · rw [hw]; rcases wc_cases S n with ⟨_, e⟩ | ⟨_, e⟩ <;> rw [e] <;> linarith
  · unfold crit; linarith

end Formal.Core.InvolutionLoop.Rate
