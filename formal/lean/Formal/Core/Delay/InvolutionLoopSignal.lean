import Formal.Core.Delay.InvolutionLoopBridge

/-!
# The involution OR loop at signal level: latch iff `s > s*`, lost iff `s < s*`,
# eternal iff `s = s*`, for EVERY solution of the arbiter loop

Probe InvLoop2 (shard A).  Setting: shard B's arbiter state loop `ALoop P s r1 r2 x qp`
(`Formal.Cells.ArbInvolution`): `r1` rises at `0`, `r2` at `s`, the state LUT is the
REAL `bd_c2n_set` INIT applied in zero time (`H_LUT`), LUT + feedback route are ONE
involution channel `P` in B's signal-level fragment `InvChanF` (`H_CH`).  Every
hypothesis is a field of `ALoop` or of A's `InvolutionPair`; nothing else is assumed.

`s* = crit P l = δ∞↑ - l`, where `Stat P h l` is the (unique, `stat_unique`; existing,
`stat_exists`) stationary pulse train of the loop.

Results.
* `arb_trichotomy`: for `0 < s < δ∞↑` and EVERY solution, `q` is eventually 1
  (`Latched`, r1 wins) iff `s > s*`, eventually 0 (`Lost`, r2 wins) iff `s < s*`, and
  takes both values after every time bound (`Eternal`) iff `s = s*`.
* `arb_threshold`: the same with `s*` produced (no `Stat` argument), plus existence of
  a solution for every gap.
* `arb_eternal_gap`, `arb_eternal_is_crit`: the gap of B's `arb_eternal` (any gap in
  `(0, δ∞↑)` with a solution all of whose solutions oscillate forever) is exactly
  `δ∞↑ - l*`; `lft_lt_crit`: `s* > δ∞↑ - δ↑(0)` (B's `lft`).

Not covered: gaps outside `(0, δ∞↑)` (B's `ALoop` theorems need them inside); noise;
whether a LUT plus route is an involution channel (B's `H_CH`).
-/

namespace Formal.Core.InvolutionLoop.Signal
open Formal.Core.DelayInvolution Formal.Core.InvolutionLoop Formal.Core.InvolutionLoop.Bridge
open Formal.Cells.CElemInvolution Formal.Cells.ArbInvolution

/-- `q` is eventually constant 1 (latched: the first request `r1` wins). -/
def Latched (q : Sig) : Prop := ∃ T : ℝ, ∀ u, T ≤ u → q u = true
/-- `q` is eventually constant 0 (lost: the later request `r2` wins). -/
def Lost (q : Sig) : Prop := ∃ T : ℝ, ∀ u, T ≤ u → q u = false
/-- `q` takes both values after every time bound (never resolves). -/
def Eternal (q : Sig) : Prop :=
  ∀ B : ℝ, (∃ u, B < u ∧ q u = true) ∧ (∃ u, B < u ∧ q u = false)

theorem not_latched_lost {q : Sig} (h1 : Latched q) (h2 : Lost q) : False := by
  obtain ⟨T1, h1⟩ := h1
  obtain ⟨T2, h2⟩ := h2
  have a := h1 (max T1 T2) (le_max_left _ _)
  have b := h2 (max T1 T2) (le_max_right _ _)
  rw [a] at b; exact Bool.noConfusion b

theorem not_eternal_latched {q : Sig} (h1 : Eternal q) (h2 : Latched q) : False := by
  obtain ⟨T, hT⟩ := h2
  obtain ⟨u, hu, hq⟩ := (h1 T).2
  rw [hT u (le_of_lt hu)] at hq; exact Bool.noConfusion hq

theorem not_eternal_lost {q : Sig} (h1 : Eternal q) (h2 : Lost q) : False := by
  obtain ⟨T, hT⟩ := h2
  obtain ⟨u, hu, hq⟩ := (h1 T).1
  rw [hT u (le_of_lt hu)] at hq; exact Bool.noConfusion hq

/-! ## Denoted signals after the last transition -/

theorem den_tail {o : ℕ → ℝ} {j : ℕ} (hc : ∀ i < j + 1, o i < o (i + 1)) {u : ℝ}
    (hu : o j ≤ u) : den o (fun n => n < j + 1) u = true ↔ j % 2 = 0 := by
  have hd : DownC (fun n : ℕ => n < j + 1) := fun n h => by omega
  have hi : Incr o (fun n => n < j + 1) := fun n h => hc n (by omega)
  rw [den_true]
  exact hi_iff hd hi (show j < j + 1 by omega) hu (fun h => absurd h (by omega))

theorem den_none (o : ℕ → ℝ) (u : ℝ) : den o (fun n => n < 0) u = false := by
  rw [Bool.eq_false_iff]; intro h
  obtain ⟨n, _, hn, _⟩ := den_true.mp h
  exact absurd hn (by omega)

theorem orb_lt_of_wd {P : InvolutionPair} {s : ℝ} {j : ℕ} (h : 0 < wd P s j) :
    orb P s j < orb P s (j + 1) := by
  unfold wd at h; rw [lo_eq_orb, lo_eq_orb] at h; linarith

theorem orb_le_of_wd {P : InvolutionPair} {s : ℝ} {j : ℕ} (h : wd P s j ≤ 0) :
    orb P s (j + 1) ≤ orb P s j := by
  unfold wd at h; rw [lo_eq_orb, lo_eq_orb] at h; linarith

section loop
variable {P : InvolutionPair}

/-- If A's width orbit first cancels at index `m`, every arbiter loop solution's `q`
is B's orbit truncated at `m`. -/
theorem q_of_first {s : ℝ} (hs0 : 0 < s) (hsI : s < P.infUp) {r1 r2 x qp : Sig}
    (L : ALoop P s r1 r2 x qp) {m : ℕ} (hc : Chain P s m) (hm : wd P s m ≤ 0) :
    qp = den (orb P s) (fun n => n < m) := by
  rcases arb_q_orb P hs0 hsI L with ⟨hosc, _⟩ | ⟨m', cm', fm', hq⟩
  · exfalso; have := (osc_iff P s).mp hosc m; linarith
  · have e : m' = m := by
      rcases lt_trichotomy m' m with h | h | h
      · exfalso; have := orb_lt_of_wd (hc m' h); linarith
      · exact h
      · exfalso; have := cm' m h; have := orb_le_of_wd hm; linarith
    rw [← e]; exact hq

/-- First cancellation at an odd index: `q` is eventually 1. -/
theorem latched_of_first {s : ℝ} (hs0 : 0 < s) (hsI : s < P.infUp) {r1 r2 x qp : Sig}
    (L : ALoop P s r1 r2 x qp) {k : ℕ} (hc : Chain P s (2 * k + 1))
    (hm : wd P s (2 * k + 1) ≤ 0) : Latched qp := by
  have hq := q_of_first hs0 hsI L hc hm
  have hco : ∀ i < 2 * k + 1, orb P s i < orb P s (i + 1) := fun i hi => orb_lt_of_wd (hc i hi)
  refine ⟨orb P s (2 * k), fun u hu => ?_⟩
  rw [hq]; exact (den_tail hco hu).mpr (by omega)

/-- First cancellation at an even index: `q` is eventually 0. -/
theorem lost_of_first {s : ℝ} (hs0 : 0 < s) (hsI : s < P.infUp) {r1 r2 x qp : Sig}
    (L : ALoop P s r1 r2 x qp) {k : ℕ} (hc : Chain P s (2 * k))
    (hm : wd P s (2 * k) ≤ 0) : Lost qp := by
  have hq := q_of_first hs0 hsI L hc hm
  rcases k with _ | j
  · exact ⟨0, fun u _ => by rw [hq]; exact den_none _ u⟩
  · have e : 2 * (j + 1) = (2 * j + 1) + 1 := by ring
    rw [e] at hq hc
    have hco : ∀ i < (2 * j + 1) + 1, orb P s i < orb P s (i + 1) :=
      fun i hi => orb_lt_of_wd (hc i hi)
    refine ⟨orb P s (2 * j + 1), fun u hu => ?_⟩
    rw [hq, Bool.eq_false_iff]; intro hh
    have := (den_tail hco hu).mp hh
    omega

/-- At an `Osc` gap every solution never resolves. -/
theorem eternal_of_osc {s : ℝ} (hs0 : 0 < s) (hsI : s < P.infUp) {r1 r2 x qp : Sig}
    (L : ALoop P s r1 r2 x qp) (hosc : Osc P s) : Eternal qp := by
  intro B
  rcases arb_q_orb P hs0 hsI L with ⟨_, hq⟩ | ⟨m, _, hf, _⟩
  · obtain ⟨k, hk⟩ := osc_unbounded P hosc B
    have hd : DownC (fun _ : ℕ => True) := fun _ _ => trivial
    have hi : Incr (orb P s) (fun _ => True) := fun n _ => hosc n
    refine ⟨⟨orb P s (2 * k), hk, ?_⟩, ⟨orb P s (2 * k + 1), by linarith [hosc (2 * k)], ?_⟩⟩
    · rw [hq, den_true]
      exact (hi_iff hd hi trivial (le_refl _) (fun _ => hosc _)).mpr (by omega)
    · rw [hq, Bool.eq_false_iff]; intro hh
      have := (hi_iff hd hi trivial (le_refl _) (fun _ => hosc _)).mp (den_true.mp hh)
      omega
  · exact absurd (hosc m) (not_lt.mpr hf)

/-- **Signal-level trichotomy.** For a gap `0 < s < δ∞↑` and EVERY solution of B's
arbiter loop: `q` latches iff `s > s*`, is lost iff `s < s*`, oscillates forever iff
`s = s*`, where `s* = δ∞↑ - l` and `(h, l)` is the stationary train. -/
theorem arb_trichotomy {h l s : ℝ} (S : Stat P h l) (hs0 : 0 < s) (hsI : s < P.infUp)
    {r1 r2 x qp : Sig} (L : ALoop P s r1 r2 x qp) :
    (Latched qp ↔ crit P l < s) ∧ (Lost qp ↔ s < crit P l) ∧ (Eternal qp ↔ s = crit P l) := by
  have hA : crit P l < s → Latched qp := fun hs => by
    obtain ⟨k, hc, hm⟩ := latch S hs hsI
    exact latched_of_first hs0 hsI L hc hm
  have hB : s < crit P l → Lost qp := fun hs => by
    obtain ⟨k, hc, hm⟩ := lost S hs0 hs
    exact lost_of_first hs0 hsI L hc hm
  have hC : s = crit P l → Eternal qp := fun hs => by
    refine eternal_of_osc hs0 hsI L ((osc_iff P s).mpr ?_)
    rw [hs]; exact wd_crit_pos S
  refine ⟨⟨fun hq => ?_, hA⟩, ⟨fun hq => ?_, hB⟩, ⟨fun hq => ?_, hC⟩⟩
  · rcases lt_trichotomy s (crit P l) with c | c | c
    · exact absurd (not_latched_lost hq (hB c)) id
    · exact absurd (not_eternal_latched (hC c) hq) id
    · exact c
  · rcases lt_trichotomy s (crit P l) with c | c | c
    · exact c
    · exact absurd (not_eternal_lost (hC c) hq) id
    · exact absurd (not_latched_lost (hA c) hq) id
  · rcases lt_trichotomy s (crit P l) with c | c | c
    · exact absurd (not_eternal_lost hq (hB c)) id
    · exact c
    · exact absurd (not_eternal_latched hq (hA c)) id

variable (P) in
/-- **The arbiter threshold, unconditionally.** Every involution pair has a critical
gap `s* = δ∞↑ - l*` in `(δ∞↑ - δ↑(0), δ∞↑)` (`l*` the low width of the stationary
train) such that for every gap `0 < s < δ∞↑` the arbiter loop has a solution and in
EVERY solution: latched iff `s > s*`, lost iff `s < s*`, eternal iff `s = s*`. -/
theorem arb_threshold : ∃ h l : ℝ, Stat P h l ∧ lft P < crit P l ∧ crit P l < P.infUp ∧
    ∀ s, 0 < s → s < P.infUp →
      (∃ x qp : Sig, ALoop P s r1R (r2R s) x qp) ∧
      ∀ r1 r2 x qp : Sig, ALoop P s r1 r2 x qp →
        (Latched qp ↔ crit P l < s) ∧ (Lost qp ↔ s < crit P l) ∧
        (Eternal qp ↔ s = crit P l) := by
  obtain ⟨h, l, S, _⟩ := stat_exists (P := P)
  refine ⟨h, l, S, ?_, crit_lt S, fun s hs0 hsI =>
    ⟨arb_exists P hs0 hsI, fun r1 r2 x qp L => arb_trichotomy S hs0 hsI L⟩⟩
  -- lft = δ∞↑ - δ↑(0) < δ∞↑ - l, i.e. l < δ↑(0) = δ↑(-h) - (δ↑(-h) - δ↑(0))
  unfold lft crit
  have := P.up_strictMono (-h) 0 (by linarith [S.h_lt]) (by linarith [S.h_pos])
  linarith [S.up_eq, S.h_pos]

/-- The critical gap lies above B's `lft = δ∞↑ - δ↑(0)`. -/
theorem lft_lt_crit {h l : ℝ} (S : Stat P h l) : lft P < crit P l := by
  unfold lft crit
  have := P.up_strictMono (-h) 0 (by linarith [S.h_lt]) (by linarith [S.h_pos])
  linarith [S.up_eq, S.h_pos]

/-- **B's eternal gap is `δ∞↑ - l*`.** Any gap in `(0, δ∞↑)` for which the arbiter
loop has a solution and every solution oscillates forever equals `crit P l`. -/
theorem arb_eternal_gap {h l s : ℝ} (S : Stat P h l) (hs0 : 0 < s) (hsI : s < P.infUp)
    (hex : ∃ x qp : Sig, ALoop P s r1R (r2R s) x qp)
    (hall : ∀ r1 r2 x qp : Sig, ALoop P s r1 r2 x qp → Eternal qp) : s = crit P l := by
  obtain ⟨x, qp, L⟩ := hex
  exact ((arb_trichotomy S hs0 hsI L).2.2).mp (hall _ _ _ _ L)

/-- The gap that B's `arb_eternal` produces is `δ∞↑ - l*`. -/
theorem arb_eternal_is_crit {h l : ℝ} (S : Stat P h l) : ∃ s, lft P < s ∧ s < P.infUp ∧
    (∃ x qp : Sig, ALoop P s r1R (r2R s) x qp) ∧
    (∀ r1 r2 x qp : Sig, ALoop P s r1 r2 x qp → Eternal qp) ∧ s = crit P l := by
  obtain ⟨s, hls, hsI, hex, hall⟩ := arb_eternal P
  have hs0 : 0 < s := lt_trans (lft_pos P) hls
  exact ⟨s, hls, hsI, hex, hall, arb_eternal_gap S hs0 hsI hex hall⟩

/-- B's `crit_exists` gap (an `Osc` width in `(0, δ∞↑)`) is `δ∞↑ - l*` too. -/
theorem osc_iff_crit {h l s : ℝ} (S : Stat P h l) (hs0 : 0 < s) (hsI : s < P.infUp) :
    Osc P s ↔ s = crit P l :=
  ⟨arb_crit P S hs0 hsI, fun e => (osc_iff P s).mpr (by rw [e]; exact wd_crit_pos S)⟩

end loop

end Formal.Core.InvolutionLoop.Signal
