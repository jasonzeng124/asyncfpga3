import Formal.Net.PerLinkPin

/-!
# Probe C-8h, part 3: per-event delays and the pulse-width condition

Which per-event channels are `EPin`s (and so are covered by `end_to_end2`)?

1. **Prelim's `BoundedDelay` is not enough, whatever the input pulse widths**
   (`bd_echo`): with ONE input change, a `BoundedDelay 1 3` output may change
   three times (follow the new value, echo the old one, follow again), all
   inside the `[lo, hi]` window of that one change. Its change count then
   exceeds the source's, so it is no `EPin` for any bounds, and the count
   invariant of `ELink` has nothing to stand on. A pulse-width condition on
   the INPUT cannot exclude this; the relation itself allows it.
2. **Per-event transport** (`evOut s D`): the change of `s` at `σ` is
   delivered at `σ + D σ`, each event with its own delay (`D` arbitrary,
   inside per-edge bounds). Under the **pulse-width condition** `H_PULSE`
   (consecutive input changes `σ1 < σ2` satisfy
   `σ1 + hi (k) < σ2 + lo (k+1)`, i.e. for constant bounds every input pulse
   is longer than `hi - lo`), the delivered events keep their order and the
   output IS an `EPin lo hi` of the input (`event_epin`). So the change-count
   invariant, and all of `end_to_end2`, survive per-event delays on every
   control pin that meets `H_PULSE`.
3. **FASTRISE line, two taps** (`or2_epin`): `z t = s (t - d1) ∨ s (t - d2)`,
   `d1 ≤ d2`, is `evOut` with rise delay `d1` and fall delay `d2`, hence an
   `EPin (ed d1 d2) (ed d1 d2)`, when every pulse of `s` is longer than
   `d2 - d1`.
-/

namespace Formal.Net.PerLink
open Formal.Net Formal.Net.Handshake Formal.Net.EndToEnd

/-! ## 1. BoundedDelay echoes -/

def echoIn : Trace := fun t => decide (5 ≤ t)
def echoOut : Trace := fun t => decide (t = 6 ∨ 8 ≤ t)

theorem echo_bd : BoundedDelay 1 3 echoIn echoOut where
  cause := by
    intro t ht
    by_cases h5 : t = 5
    · subst h5; exact ⟨1, by decide, by decide, by decide, by decide⟩
    by_cases h6 : t = 6
    · subst h6; exact ⟨3, by decide, by decide, by decide, by decide⟩
    by_cases h7 : t = 7
    · subst h7; exact ⟨1, by decide, by decide, by decide, by decide⟩
    exfalso; apply ht
    simp only [echoOut]
    rw [decide_eq_decide]; omega
  settle := by
    intro t ht hst
    by_cases h8 : 8 ≤ t
    · simp only [echoIn, echoOut, decide_eq_decide]; omega
    by_cases h4 : t ≤ 4
    · simp only [echoIn, echoOut, decide_eq_decide]; omega
    exfalso
    have a := hst 5 (by omega) (by omega)
    simp [echoIn] at a; omega

theorem N_echoIn : N echoIn 10 = 1 := by decide
theorem N_echoOut : N echoOut 10 = 3 := by decide

/-! ## Counting lemmas -/

theorem cnt_le_of {f g : Nat → Bool} : ∀ t, (∀ σ, σ < t → f σ = true → g σ = true) →
    cnt f t ≤ cnt g t := by
  intro t
  induction t with
  | zero => intro _; exact Nat.le_refl _
  | succ t ih =>
    intro h
    have := ih (fun σ hσ => h σ (by omega))
    simp only [cnt]
    cases hf : f t
    · simp; split <;> omega
    · simp [h t (by omega) hf]; omega

theorem cnt_congr {f g : Nat → Bool} : ∀ t, (∀ σ, σ < t → f σ = g σ) → cnt f t = cnt g t := by
  intro t h
  exact Nat.le_antisymm (cnt_le_of t (fun σ hσ hf => by rw [← h σ hσ]; exact hf))
    (cnt_le_of t (fun σ hσ hg => by rw [h σ hσ]; exact hg))

theorem cnt_ext {f : Nat → Bool} {a : Nat} : ∀ k, (∀ σ, a ≤ σ → σ < a + k → f σ = false) →
    cnt f (a + k) = cnt f a := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro h
    rw [← Nat.add_assoc]
    simp only [cnt, h (a + k) (by omega) (by omega)]
    simp; exact ih (fun σ h1 h2 => h σ h1 (by omega))

theorem cnt_below (s : Trace) (k : Nat) : ∀ t,
    cnt (fun σ => chg s σ && decide (N s σ < k)) t = min (N s t) k := by
  intro t
  induction t with
  | zero => simp [cnt, N_zero]
  | succ t ih =>
    simp only [cnt] at ih ⊢
    rw [ih]
    by_cases hc : s (t + 1) = s t
    · rw [N_stay hc]; simp [chg, hc]
    · rw [N_move hc]; simp only [chg, ne_eq, hc, not_false_eq_true, decide_true, Bool.true_and]
      by_cases hk : N s t < k
      · simp [hk]; omega
      · simp [hk]; omega

/-- The `k`-th change exists once `k+1` changes happened. -/
theorem exists_kth (s : Trace) (k : Nat) : ∀ t, k < N s t → ∃ σ, σ < t ∧ chg s σ = true ∧ N s σ = k := by
  intro t
  induction t with
  | zero => intro h; simp [N_zero] at h
  | succ t ih =>
    intro h
    by_cases hc : s (t + 1) = s t
    · rw [N_stay hc] at h
      obtain ⟨σ, h1, h2, h3⟩ := ih h
      exact ⟨σ, by omega, h2, h3⟩
    · rw [N_move hc] at h
      by_cases hk : k < N s t
      · obtain ⟨σ, h1, h2, h3⟩ := ih hk
        exact ⟨σ, by omega, h2, h3⟩
      · exact ⟨t, by omega, by simp [chg, hc], by omega⟩

theorem chg_N_succ {s : Trace} {σ : Nat} (h : chg s σ = true) : N s (σ + 1) = N s σ + 1 := by
  have : s (σ + 1) ≠ s σ := by simpa [chg] using h
  exact N_move this

theorem idx_lt {s : Trace} {σ1 σ2 : Nat} (h1 : chg s σ1 = true) (hlt : σ1 < σ2) :
    N s σ1 < N s σ2 := by
  have := chg_N_succ h1
  have : N s (σ1 + 1) ≤ N s σ2 := N_mono (by omega)
  omega

theorem idx_inj {s : Trace} {σ1 σ2 : Nat} (h1 : chg s σ1 = true) (h2 : chg s σ2 = true)
    (he : N s σ1 = N s σ2) : σ1 = σ2 := by
  rcases Nat.lt_trichotomy σ1 σ2 with h | h | h
  · have := idx_lt h1 h; omega
  · exact h
  · have := idx_lt h2 h; omega

/-! ## 2. Per-event transport -/

/-- Number of input changes delivered by `t` (the change at `σ` is delivered
at `σ + D σ`, i.e. visible from `σ + D σ + 1`). -/
def evCnt (s : Trace) (D : Nat → Nat) (t : Nat) : Nat :=
  cnt (fun σ => chg s σ && decide (σ + D σ < t)) t

/-- The per-event transport output: parity of the delivered changes. -/
def evOut (s : Trace) (D : Nat → Nat) : Trace := fun t => decide (evCnt s D t % 2 = 1)

/-- Order preservation of delivered events. -/
def OrderPres (s : Trace) (D : Nat → Nat) : Prop :=
  ∀ σ1 σ2, chg s σ1 = true → chg s σ2 = true → σ1 < σ2 → σ1 + D σ1 < σ2 + D σ2

/-- **H_PULSE** (per-edge pulse width): consecutive input changes `σ1 < σ2`
(indices `k`, `k+1`) satisfy `σ1 + hi k < σ2 + lo (k+1)`. For constant bounds:
every pulse of the input is longer than `hi - lo`. -/
def Pulse (lo hi : Nat → Nat) (s : Trace) : Prop :=
  ∀ σ1 σ2, chg s σ1 = true → chg s σ2 = true → N s σ2 = N s σ1 + 1 →
    σ1 + hi (N s σ1) < σ2 + lo (N s σ2)

/-- Per-event delays inside the per-edge bounds. -/
def InBounds (lo hi : Nat → Nat) (s : Trace) (D : Nat → Nat) : Prop :=
  ∀ σ, chg s σ = true → lo (N s σ) ≤ D σ ∧ D σ ≤ hi (N s σ)

theorem orderPres_of_pulse {lo hi : Nat → Nat} {s : Trace} {D : Nat → Nat}
    (HP : Pulse lo hi s) (HB : InBounds lo hi s D) : OrderPres s D := by
  have main : ∀ g σ1 σ2, chg s σ1 = true → chg s σ2 = true → N s σ2 = N s σ1 + 1 + g →
      σ1 + D σ1 < σ2 + D σ2 := by
    intro g
    induction g with
    | zero =>
      intro σ1 σ2 h1 h2 he
      have a := HP σ1 σ2 h1 h2 he
      have b1 := HB σ1 h1
      have b2 := HB σ2 h2
      omega
    | succ g ih =>
      intro σ1 σ2 h1 h2 he
      obtain ⟨σm, hm1, hm2, hm3⟩ := exists_kth s (N s σ1 + 1) σ2 (by omega)
      -- σ1 → σm is consecutive, σm → σ2 has gap g
      have c := HP σ1 σm h1 hm2 hm3
      have b1 := HB σ1 h1
      have bm := HB σm hm2
      have b := ih σm σ2 hm2 h2 (by omega)
      omega
  intro σ1 σ2 h1 h2 hlt
  have := idx_lt h1 hlt
  exact main (N s σ2 - N s σ1 - 1) σ1 σ2 h1 h2 (by omega)

/-- **Delivered-prefix characterisation.** With order preservation, `k`
changes have been delivered by `t` beyond the first `k` exactly when the
`k`-th change has. -/
theorem ev_char {s : Trace} {D : Nat → Nat} (OP : OrderPres s D) (k t : Nat) :
    k < evCnt s D t ↔ ∃ σ, chg s σ = true ∧ N s σ = k ∧ σ + D σ < t := by
  constructor
  · intro h
    apply Classical.byContradiction; intro hn
    have hle : evCnt s D t ≤ cnt (fun σ => chg s σ && decide (N s σ < k)) t := by
      apply cnt_le_of
      intro σ _ hf
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hf ⊢
      refine ⟨hf.1, ?_⟩
      apply Classical.byContradiction; intro hk
      by_cases he : N s σ = k
      · exact hn ⟨σ, hf.1, he, hf.2⟩
      · obtain ⟨σk, hk1, hk2, hk3⟩ := exists_kth s k σ (by omega)
        have := OP σk σ hk2 hf.1 hk1
        exact hn ⟨σk, hk2, hk3, by omega⟩
    rw [cnt_below] at hle
    have : min (N s t) k ≤ k := Nat.min_le_right _ _
    omega
  · rintro ⟨σ, h1, h2, h3⟩
    have hge : cnt (fun σ' => chg s σ' && decide (σ' ≤ σ)) t ≤ evCnt s D t := by
      apply cnt_le_of
      intro σ' _ hf
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hf ⊢
      refine ⟨hf.1, ?_⟩
      rcases Nat.lt_or_eq_of_le hf.2 with hl | hl
      · have := OP σ' σ hf.1 h1 hl; omega
      · subst hl; exact h3
    have e1 : cnt (fun σ' => chg s σ' && decide (σ' ≤ σ)) t =
        cnt (fun σ' => chg s σ' && decide (σ' ≤ σ)) (σ + 1) := by
      have := cnt_ext (f := fun σ' => chg s σ' && decide (σ' ≤ σ)) (a := σ + 1) (t - (σ + 1))
        (fun σ' h1 _ => by simp; omega)
      rwa [show σ + 1 + (t - (σ + 1)) = t by omega] at this
    have e2 : cnt (fun σ' => chg s σ' && decide (σ' ≤ σ)) (σ + 1) = N s (σ + 1) :=
      cnt_congr _ (fun σ' h => by simp; omega)
    rw [e1, e2, chg_N_succ h1, h2] at hge
    omega

theorem ev_step {s : Trace} {D : Nat → Nat} (OP : OrderPres s D) (t : Nat) :
    evCnt s D t ≤ evCnt s D (t + 1) ∧ evCnt s D (t + 1) ≤ evCnt s D t + 1 := by
  constructor
  · apply Classical.byContradiction; intro h
    have := (ev_char OP (evCnt s D (t + 1)) t).mp (by omega)
    obtain ⟨σ, h1, h2, h3⟩ := this
    have := (ev_char OP (evCnt s D (t + 1)) (t + 1)).mpr ⟨σ, h1, h2, by omega⟩
    omega
  · apply Classical.byContradiction; intro h
    obtain ⟨σa, a1, a2, a3⟩ := (ev_char OP (evCnt s D t) (t + 1)).mp (by omega)
    obtain ⟨σb, b1, b2, b3⟩ := (ev_char OP (evCnt s D t + 1) (t + 1)).mp (by omega)
    have hlt : σa < σb := by
      rcases Nat.lt_trichotomy σa σb with h' | h' | h'
      · exact h'
      · subst h'; omega
      · have := idx_lt b1 h'; omega
    have := OP σa σb a1 b1 hlt
    have := (ev_char OP (evCnt s D t) t).mpr ⟨σa, a1, a2, by omega⟩
    omega

theorem N_evOut {s : Trace} {D : Nat → Nat} (OP : OrderPres s D) :
    ∀ t, N (evOut s D) t = evCnt s D t := by
  intro t
  induction t with
  | zero => simp [N_zero, evCnt, cnt]
  | succ t ih =>
    have ⟨a, b⟩ := ev_step OP t
    by_cases he : evCnt s D (t + 1) = evCnt s D t
    · have : evOut s D (t + 1) = evOut s D t := by simp only [evOut, he]
      rw [N_stay this, ih, he]
    · have he' : evCnt s D (t + 1) = evCnt s D t + 1 := by omega
      have : evOut s D (t + 1) ≠ evOut s D t := by
        simp only [evOut, he', ne_eq, decide_eq_decide]; omega
      rw [N_move this, ih, he']

/-- **Per-event transport is an `EPin`** under order preservation (which the
pulse-width condition gives, `orderPres_of_pulse`). -/
theorem event_epin_op {lo hi : Nat → Nat} {s : Trace} {D : Nat → Nat}
    (OP : OrderPres s D) (HB : InBounds lo hi s D) : EPin lo hi s (evOut s D) where
  z := by simp [evOut, evCnt, cnt]
  early := by
    intro k t h
    rw [N_evOut OP] at h
    obtain ⟨σ, h1, h2, h3⟩ := (ev_char OP k t).mp h
    have b := HB σ h1
    rw [h2] at b
    have := chg_N_succ h1
    have : N s (σ + 1) ≤ N s (t - lo k) := N_mono (by omega)
    omega
  late := by
    intro k t h
    rw [N_evOut OP]
    obtain ⟨σ, h1, h2, h3⟩ := exists_kth s k _ h
    have b := HB σ h2
    rw [h3] at b
    exact (ev_char OP k t).mpr ⟨σ, h2, h3, by omega⟩

/-- **Per-event delays, pulse-width form.** Every control-pin channel that
delivers each input change after its own delay inside the per-edge bounds,
fed by an input meeting `H_PULSE`, is an `EPin`, so `end_to_end2` covers it. -/
theorem event_epin {lo hi : Nat → Nat} {s : Trace} {D : Nat → Nat}
    (H_PULSE : Pulse lo hi s) (HB : InBounds lo hi s D) : EPin lo hi s (evOut s D) :=
  event_epin_op (orderPres_of_pulse H_PULSE HB) HB

theorem echoIn_chg {σ : Nat} (h : chg echoIn σ = true) : σ = 4 := by
  simp [chg, echoIn] at h; omega

/-- **Echo**: a `BoundedDelay` pin of a signal with a single change (so every
pulse-width condition on the input holds) changes three times; it is not an
`EPin` for any bounds. -/
theorem bd_echo : BoundedDelay 1 3 echoIn echoOut ∧
    (∀ lo hi : Nat → Nat, Pulse lo hi echoIn) ∧
    ¬ ∃ lo hi, EPin lo hi echoIn echoOut := by
  refine ⟨echo_bd, fun lo hi σ1 σ2 h1 h2 he => ?_, ?_⟩
  · have := echoIn_chg h1; have := echoIn_chg h2; subst_vars; omega
  rintro ⟨lo, hi, P⟩
  have := P.le 10
  rw [N_echoIn, N_echoOut] at this
  omega

/-! ## 3. The two-tap FASTRISE line -/

/-- Two-tap OR line: the rise passes the fast tap, the fall waits for the slow one. -/
def or2 (d1 d2 : Nat) (s : Trace) : Trace := fun t => s (t - d1) || s (t - d2)

theorem or2_eq_ev {d1 d2 : Nat} {s : Trace} (h0 : s 0 = false) (hd : d1 ≤ d2)
    (HW : ∀ σ1 σ2, chg s σ1 = true → chg s σ2 = true → σ1 < σ2 → d2 - d1 < σ2 - σ1) :
    ∀ t, or2 d1 d2 s t = evOut s (fun σ => ed d1 d2 (N s σ)) t := by
  have OP : OrderPres s (fun σ => ed d1 d2 (N s σ)) := by
    intro σ1 σ2 h1 h2 hlt
    have := HW σ1 σ2 h1 h2 hlt
    simp only [ed]; split <;> split <;> omega
  intro t
  let a := N s (t - d1)
  let b := N s (t - d2)
  have hab : b ≤ a := N_mono (by omega)
  -- at most one change in [t - d2, t - d1)
  have h1 : a ≤ b + 1 := by
    apply Classical.byContradiction; intro hc
    obtain ⟨σ1, p1, p2, p3⟩ := exists_kth s b (t - d1) (by omega)
    obtain ⟨σ2, q1, q2, q3⟩ := exists_kth s (b + 1) (t - d1) (by omega)
    have hlt : σ1 < σ2 := by
      rcases Nat.lt_trichotomy σ1 σ2 with h' | h' | h'
      · exact h'
      · subst h'; omega
      · have := idx_lt q2 h'; omega
    have hσ1 : t - d2 ≤ σ1 := by
      apply Classical.byContradiction; intro hc'
      have := chg_N_succ p2
      have : N s (σ1 + 1) ≤ N s (t - d2) := N_mono (by omega)
      omega
    have := HW σ1 σ2 p2 q2 hlt
    omega
  -- the delivered count
  have hc : evCnt s (fun σ => ed d1 d2 (N s σ)) t = b + (if a = b + 1 ∧ b % 2 = 0 then 1 else 0) := by
    apply Nat.le_antisymm
    · apply Classical.byContradiction; intro hlt
      obtain ⟨σ, c1, c2, c3⟩ := (ev_char OP (b + (if a = b + 1 ∧ b % 2 = 0 then 1 else 0)) t).mp (by omega)
      -- σ is a change with index ≥ b, delivered by t
      have hσ : t - d2 ≤ σ := by
        apply Classical.byContradiction; intro hc'
        have := chg_N_succ c1
        have : N s (σ + 1) ≤ N s (t - d2) := N_mono (by omega)
        split at c2 <;> omega
      have hd1 : σ < t - d1 := by
        have : ed d1 d2 (N s σ) ≥ d1 := by simp only [ed]; split <;> omega
        omega
      have hidx : N s σ < a := idx_lt c1 hd1
      have hidx' : N s σ = b := by split at c2 <;> omega
      have hodd : ¬ (b % 2 = 0) := by
        intro hb
        split at c2
        · omega
        · rename_i hn; exact hn ⟨by omega, hb⟩
      have : ed d1 d2 (N s σ) = d2 := by rw [hidx']; exact ed_odd (by omega)
      simp only [this] at c3
      omega
    · apply Classical.byContradiction; intro hlt
      have hk : evCnt s (fun σ => ed d1 d2 (N s σ)) t < b + (if a = b + 1 ∧ b % 2 = 0 then 1 else 0) := by
        omega
      by_cases hk' : evCnt s (fun σ => ed d1 d2 (N s σ)) t < b
      · obtain ⟨σ, c1, c2, c3⟩ := exists_kth s _ (t - d2) hk'
        have := (ev_char OP _ t).mpr ⟨σ, c2, c3, by
          have : ed d1 d2 (N s σ) ≤ d2 := by simp only [ed]; split <;> omega
          omega⟩
        omega
      · have hab' : a = b + 1 ∧ b % 2 = 0 := by
          apply Classical.byContradiction; intro hn; simp only [hn, if_false] at hk; omega
        obtain ⟨σ, c1, c2, c3⟩ := exists_kth s b (t - d1) (by omega)
        have := (ev_char OP b t).mpr ⟨σ, c2, c3, by
          have : ed d1 d2 (N s σ) = d1 := by rw [c3]; exact ed_even hab'.2
          omega⟩
        rw [if_pos hab'] at hk
        omega
  simp only [or2, evOut, hc]
  rw [parity h0 (t - d1), parity h0 (t - d2)]
  show (decide (a % 2 = 1) || decide (b % 2 = 1)) = _
  by_cases e : a = b
  · rw [e]
    have : ¬ (b = b + 1 ∧ b % 2 = 0) := by omega
    simp only [this, if_false, Nat.add_zero, Bool.or_self]
  · have e' : a = b + 1 := by omega
    rw [e']
    by_cases hb : b % 2 = 0
    · have : (b + 1 = b + 1 ∧ b % 2 = 0) := ⟨rfl, hb⟩
      simp only [this, and_self, if_true]
      have : (b + 1) % 2 = 1 := by omega
      simp [this]
    · have : ¬ (b + 1 = b + 1 ∧ b % 2 = 0) := fun h => hb h.2
      simp only [this, if_false, Nat.add_zero]
      have : b % 2 = 1 := by omega
      simp [this]

/-- **FASTRISE two-tap line**: rise delay `d1`, fall delay `d2`, an `EPin`
when every pulse of the input is longer than `d2 - d1`. -/
theorem or2_epin {d1 d2 : Nat} {s : Trace} (h0 : s 0 = false) (hd : d1 ≤ d2)
    (HW : ∀ σ1 σ2, chg s σ1 = true → chg s σ2 = true → σ1 < σ2 → d2 - d1 < σ2 - σ1) :
    EPin (ed d1 d2) (ed d1 d2) s (or2 d1 d2 s) := by
  have OP : OrderPres s (fun σ => ed d1 d2 (N s σ)) := by
    intro σ1 σ2 h1 h2 hlt
    have := HW σ1 σ2 h1 h2 hlt
    simp only [ed]; split <;> split <;> omega
  have e : or2 d1 d2 s = evOut s (fun σ => ed d1 d2 (N s σ)) := funext (or2_eq_ev h0 hd HW)
  rw [e]
  exact event_epin_op OP (fun σ _ => ⟨Nat.le_refl _, Nat.le_refl _⟩)

end Formal.Net.PerLink
