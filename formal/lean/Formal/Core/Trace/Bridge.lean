import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Bridge: event lists ↔ continuous-time Boolean traces

An **event trace** is an initial value plus a strictly increasing finite list
of transition times (`EvTrace`). It *denotes* the function `ℝ → Bool`

  `denote init ts t = init xor (parity of #{τ ∈ ts | τ ≤ t})`

i.e. the value starts at `init` and flips at every listed time; at a
transition time the trace already has its new value (right-continuous).

Main results (all proved, no axioms beyond Lean/Mathlib's standard ones):

* `denote_rightCont`   : the denotation is right-continuous.
* `denote_eq_of_gap`   : it is constant on every interval `[s, t]` containing
  no transition time in `(s, t]` (piecewise constant).
* `denote_below`       : before the first transition it equals `init`.
* `changesAt_denote`   : for a strictly increasing list, the denotation
  *changes* at `t` (is not constant on any left neighbourhood of `t`) iff
  `t ∈ ts`; hence `denote_finChanges` (finitely many changes).
* `denote_injective`, `EvTrace.toFun_injective` : the map is injective.
* `exists_evTrace`     : **surjectivity onto well-formed traces**: every
  right-continuous `f : ℝ → Bool` whose change points lie in some finite list
  is the denotation of an event trace.
* `eq_of_sameChanges`  : uniqueness principle used for the above (two
  right-continuous functions with the same finitely many change points that
  agree before all of them are equal). Its core is `eq_of_noChange`, the
  connectedness argument (via `Real.exists_isLUB`): a right-continuous Bool
  function with no change point in `(a, b]` has `f b = f a`.

So the event-list representation and "right-continuous ℝ → Bool with finitely
many changes" are in bijection (`EvTrace.toFun` is injective with image exactly
`{f | RightCont f ∧ FinChanges f}`): theorems may be proved in whichever is
convenient.

Signals on `ℝ≥0` are the special case where every transition time is `≥ 0`
and `init` is the value at time 0⁻ (not formalised separately).
-/

namespace Formal.Core.Bridge

noncomputable section

/-! ## Definitions -/

/-- Parity of the number of list elements `≤ t`. -/
def flips : List ℝ → ℝ → Bool
  | [], _ => false
  | a :: l, t => (decide (a ≤ t)) ^^ flips l t

/-- The denotation of an initial value and a list of transition times. -/
def denote (init : Bool) (ts : List ℝ) (t : ℝ) : Bool := init ^^ flips ts t

/-- A well-formed event trace: initial value and strictly increasing
transition times. Finite variability holds by construction. -/
structure EvTrace where
  init : Bool
  ts : List ℝ
  sorted : ts.Pairwise (· < ·)

/-- The continuous-time Boolean trace an event trace denotes. -/
def EvTrace.toFun (e : EvTrace) : ℝ → Bool := denote e.init e.ts

/-- Right-continuity of a Boolean signal (in the discrete topology on Bool:
locally constant on the right). -/
def RightCont (f : ℝ → Bool) : Prop :=
  ∀ t, ∃ ε > 0, ∀ s, t ≤ s → s < t + ε → f s = f t

/-- `f` is constant on some left neighbourhood `(t - ε, t]` of `t`. -/
def LeftConst (f : ℝ → Bool) (t : ℝ) : Prop :=
  ∃ ε > 0, ∀ s, t - ε < s → s < t → f s = f t

/-- `t` is a change point of `f`. -/
def ChangesAt (f : ℝ → Bool) (t : ℝ) : Prop := ¬ LeftConst f t

/-- Finitely many change points (all of them occur in some finite list). -/
def FinChanges (f : ℝ → Bool) : Prop := ∃ l : List ℝ, ∀ t, ChangesAt f t → t ∈ l

/-! ## Elementary list facts -/

theorem exists_gap_right (l : List ℝ) (t : ℝ) :
    ∃ ε > 0, ∀ a ∈ l, t < a → t + ε ≤ a := by
  induction l with
  | nil => exact ⟨1, one_pos, fun a ha => nomatch ha⟩
  | cons a l ih =>
    obtain ⟨ε, hε, h⟩ := ih
    by_cases hta : t < a
    · refine ⟨min ε (a - t), lt_min hε (by linarith), ?_⟩
      intro b hb htb
      rcases List.mem_cons.mp hb with rfl | hb
      · have := min_le_right ε (b - t); linarith
      · have := min_le_left ε (a - t); have := h b hb htb; linarith
    · refine ⟨ε, hε, ?_⟩
      intro b hb htb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact absurd htb hta
      · exact h b hb htb

theorem exists_gap_left (l : List ℝ) (t : ℝ) :
    ∃ ε > 0, ∀ a ∈ l, a < t → a ≤ t - ε := by
  induction l with
  | nil => exact ⟨1, one_pos, fun a ha => nomatch ha⟩
  | cons a l ih =>
    obtain ⟨ε, hε, h⟩ := ih
    by_cases hta : a < t
    · refine ⟨min ε (t - a), lt_min hε (by linarith), ?_⟩
      intro b hb htb
      rcases List.mem_cons.mp hb with rfl | hb
      · have := min_le_right ε (t - b); linarith
      · have := min_le_left ε (t - a); have := h b hb htb; linarith
    · refine ⟨ε, hε, ?_⟩
      intro b hb htb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact absurd htb hta
      · exact h b hb htb

theorem exists_below (l : List ℝ) : ∃ T, ∀ a ∈ l, T < a := by
  induction l with
  | nil => exact ⟨0, fun a ha => nomatch ha⟩
  | cons a l ih =>
    obtain ⟨T, h⟩ := ih
    refine ⟨min T (a - 1), ?_⟩
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · have := min_le_right T (b - 1); linarith
    · have := min_le_left T (a - 1); have := h b hb; linarith

/-- Two strictly increasing lists with the same elements are equal. -/
theorem eq_of_mem_iff : ∀ {l₁ l₂ : List ℝ}, l₁.Pairwise (· < ·) →
    l₂.Pairwise (· < ·) → (∀ x, x ∈ l₁ ↔ x ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).mpr (List.mem_cons_self ..)) (by simp)
  | a :: _, [], _, _, h => absurd ((h a).mp (List.mem_cons_self ..)) (by simp)
  | a :: l₁, b :: l₂, h₁, h₂, h => by
    rw [List.pairwise_cons] at h₁ h₂
    have hab : a = b := by
      have ha := (h a).mp (List.mem_cons_self ..)
      have hb := (h b).mpr (List.mem_cons_self ..)
      rcases List.mem_cons.mp ha with e | ha'
      · exact e
      · rcases List.mem_cons.mp hb with e | hb'
        · exact e.symm
        · have := h₂.1 a ha'; have := h₁.1 b hb'; linarith
    subst hab
    have ht : l₁ = l₂ := by
      apply eq_of_mem_iff h₁.2 h₂.2
      intro x
      constructor
      · intro hx
        have hax := h₁.1 x hx
        rcases List.mem_cons.mp ((h x).mp (List.mem_cons_of_mem _ hx)) with e | e
        · subst e; exact absurd hax (lt_irrefl _)
        · exact e
      · intro hx
        have hax := h₂.1 x hx
        rcases List.mem_cons.mp ((h x).mpr (List.mem_cons_of_mem _ hx)) with e | e
        · subst e; exact absurd hax (lt_irrefl _)
        · exact e
    rw [ht]

/-! ## Properties of the denotation -/

theorem flips_eq_of_gap (l : List ℝ) {s t : ℝ} (hst : s ≤ t)
    (h : ∀ a ∈ l, ¬ (s < a ∧ a ≤ t)) : flips l s = flips l t := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [flips]
    have ha := h a (List.mem_cons_self ..)
    have hiff : (a ≤ s ↔ a ≤ t) := by
      constructor
      · intro h1; linarith
      · intro h2
        by_contra hc
        exact ha ⟨lt_of_not_ge hc, h2⟩
    rw [ih (fun b hb => h b (List.mem_cons_of_mem _ hb)), decide_eq_decide.mpr hiff]

/-- **Piecewise constant**: no transition in `(s, t]` means equal values. -/
theorem denote_eq_of_gap (i : Bool) (l : List ℝ) {s t : ℝ} (hst : s ≤ t)
    (h : ∀ a ∈ l, ¬ (s < a ∧ a ≤ t)) : denote i l s = denote i l t := by
  simp only [denote, flips_eq_of_gap l hst h]

theorem flips_below (l : List ℝ) {t : ℝ} (h : ∀ a ∈ l, t < a) : flips l t = false := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ha : ¬ a ≤ t := not_le.mpr (h a (List.mem_cons_self ..))
    simp only [flips, decide_eq_false ha, ih (fun b hb => h b (List.mem_cons_of_mem _ hb)),
      Bool.false_xor]

/-- Before the first transition the trace has its initial value. -/
theorem denote_below (i : Bool) (l : List ℝ) {t : ℝ} (h : ∀ a ∈ l, t < a) :
    denote i l t = i := by
  simp only [denote, flips_below l h, Bool.xor_false]

theorem denote_rightCont (i : Bool) (l : List ℝ) : RightCont (denote i l) := by
  intro t
  obtain ⟨ε, hε, h⟩ := exists_gap_right l t
  refine ⟨ε, hε, fun s hts hs => ?_⟩
  refine (denote_eq_of_gap i l hts ?_).symm
  rintro a ha ⟨h1, h2⟩
  have := h a ha h1
  linarith

/-- Parity of the number of list elements in `(s, t]`. -/
def flipsIn : List ℝ → ℝ → ℝ → Bool
  | [], _, _ => false
  | a :: l, s, t => (decide (s < a ∧ a ≤ t)) ^^ flipsIn l s t

theorem flips_split (l : List ℝ) {s t : ℝ} (hst : s ≤ t) :
    flips l t = (flips l s ^^ flipsIn l s t) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [flips, flipsIn, ih]
    by_cases h1 : a ≤ s
    · have h2 : a ≤ t := le_trans h1 hst
      have h3 : ¬ (s < a ∧ a ≤ t) := fun h => absurd h.1 (not_lt.mpr h1)
      rw [decide_eq_true h1, decide_eq_true h2, decide_eq_false h3]
      cases flips l s <;> cases flipsIn l s t <;> rfl
    · by_cases h2 : a ≤ t
      · have h3 : s < a ∧ a ≤ t := ⟨lt_of_not_ge h1, h2⟩
        rw [decide_eq_false h1, decide_eq_true h2, decide_eq_true h3]
        cases flips l s <;> cases flipsIn l s t <;> rfl
      · have h3 : ¬ (s < a ∧ a ≤ t) := fun h => h2 h.2
        rw [decide_eq_false h1, decide_eq_false h2, decide_eq_false h3]
        cases flips l s <;> cases flipsIn l s t <;> rfl

theorem flipsIn_single {l : List ℝ} (hl : l.Pairwise (· < ·)) {s τ : ℝ} (hsτ : s < τ)
    (H : ∀ a ∈ l, s < a → a ≤ τ → a = τ) : flipsIn l s τ = decide (τ ∈ l) := by
  induction l with
  | nil => simp [flipsIn]
  | cons a l ih =>
    rw [List.pairwise_cons] at hl
    have ih' := ih hl.2 (fun b hb => H b (List.mem_cons_of_mem _ hb))
    simp only [flipsIn, ih']
    by_cases ha : a = τ
    · subst ha
      have hnot : a ∉ l := fun hm => lt_irrefl a (hl.1 a hm)
      have h3 : s < a ∧ a ≤ a := ⟨hsτ, le_refl a⟩
      rw [decide_eq_true h3, decide_eq_false hnot, decide_eq_true (List.mem_cons_self ..)]
      rfl
    · have h3 : ¬ (s < a ∧ a ≤ τ) := fun h => ha (H a (List.mem_cons_self ..) h.1 h.2)
      have h4 : (τ ∈ a :: l) ↔ τ ∈ l := by
        rw [List.mem_cons]
        exact ⟨fun h => h.elim (fun e => absurd e.symm ha) id, Or.inr⟩
      rw [decide_eq_false h3, Bool.false_xor, decide_eq_decide.mpr h4]

/-- **Change points of the denotation are exactly the listed times.** -/
theorem changesAt_denote (i : Bool) {l : List ℝ} (hl : l.Pairwise (· < ·)) (t : ℝ) :
    ChangesAt (denote i l) t ↔ t ∈ l := by
  obtain ⟨ε₀, hε₀, hgap⟩ := exists_gap_left l t
  constructor
  · intro hc
    by_contra hnot
    apply hc
    refine ⟨ε₀, hε₀, fun s hs1 hs2 => denote_eq_of_gap i l hs2.le ?_⟩
    rintro a ha ⟨h1, h2⟩
    rcases eq_or_lt_of_le h2 with e | e
    · exact hnot (e ▸ ha)
    · have := hgap a ha e; linarith
  · rintro hmem ⟨ε, hε, h⟩
    have hm : 0 < min ε ε₀ := lt_min hε hε₀
    set s := t - min ε ε₀ / 2 with hs
    have hst : s < t := by linarith
    have h1 : t - ε < s := by have := min_le_left ε ε₀; linarith
    have h2 : t - ε₀ < s := by have := min_le_right ε ε₀; linarith
    have hval := h s h1 hst
    have hsplit := flips_split l hst.le
    have hin : flipsIn l s t = true := by
      rw [flipsIn_single hl hst]
      · exact decide_eq_true hmem
      · intro a ha hsa hat
        rcases eq_or_lt_of_le hat with e | e
        · exact e
        · have := hgap a ha e; linarith
    simp only [denote, hsplit, hin] at hval
    cases i <;> cases flips l s <;> simp at hval

theorem denote_finChanges (i : Bool) {l : List ℝ} (hl : l.Pairwise (· < ·)) :
    FinChanges (denote i l) :=
  ⟨l, fun t h => (changesAt_denote i hl t).mp h⟩

/-- **Injectivity** of the denotation on strictly increasing lists. -/
theorem denote_injective {i₁ i₂ : Bool} {l₁ l₂ : List ℝ} (h₁ : l₁.Pairwise (· < ·))
    (h₂ : l₂.Pairwise (· < ·)) (h : denote i₁ l₁ = denote i₂ l₂) : i₁ = i₂ ∧ l₁ = l₂ := by
  have hl : l₁ = l₂ := by
    apply eq_of_mem_iff h₁ h₂
    intro x
    rw [← changesAt_denote i₁ h₁, ← changesAt_denote i₂ h₂, h]
  subst hl
  refine ⟨?_, rfl⟩
  obtain ⟨T, hT⟩ := exists_below l₁
  have := congrFun h T
  rwa [denote_below i₁ l₁ hT, denote_below i₂ l₁ hT] at this

theorem EvTrace.toFun_injective : Function.Injective EvTrace.toFun := by
  rintro ⟨i₁, l₁, h₁⟩ ⟨i₂, l₂, h₂⟩ h
  obtain ⟨rfl, rfl⟩ := denote_injective h₁ h₂ h
  rfl

theorem EvTrace.rightCont (e : EvTrace) : RightCont e.toFun := denote_rightCont _ _

theorem EvTrace.finChanges (e : EvTrace) : FinChanges e.toFun := denote_finChanges _ e.sorted

/-! ## Uniqueness and surjectivity -/

/-- **Connectedness**: a right-continuous Bool signal with no change point in
`(a, b]` takes the same value at `a` and `b`. -/
theorem eq_of_noChange {f : ℝ → Bool} (hf : RightCont f) {a b : ℝ} (hab : a ≤ b)
    (hn : ∀ t, a < t → t ≤ b → LeftConst f t) : f b = f a := by
  let S : Set ℝ := {s | a ≤ s ∧ s ≤ b ∧ ∀ u, a ≤ u → u ≤ s → f u = f a}
  have haS : a ∈ S := ⟨le_refl a, hab, fun u h1 h2 => by rw [le_antisymm h2 h1]⟩
  have hbdd : BddAbove S := ⟨b, fun s hs => hs.2.1⟩
  obtain ⟨c, hc⟩ := Real.exists_isLUB ⟨a, haS⟩ hbdd
  have hac : a ≤ c := hc.1 haS
  have hcb : c ≤ b := hc.2 (fun s hs => hs.2.1)
  have hbelow : ∀ u, a ≤ u → u < c → f u = f a := by
    intro u hau huc
    by_contra hne
    have hub : u ∈ upperBounds S := by
      intro s hs
      by_contra hsu
      exact hne (hs.2.2 u hau (le_of_lt (lt_of_not_ge hsu)))
    have := hc.2 hub
    linarith
  have hfc : f c = f a := by
    rcases eq_or_lt_of_le hac with h | h
    · rw [← h]
    · obtain ⟨ε, hε, hl⟩ := hn c h hcb
      have hs1 : c - ε < max a (c - ε / 2) :=
        lt_of_lt_of_le (by linarith) (le_max_right _ _)
      have hs2 : max a (c - ε / 2) < c := max_lt h (by linarith)
      rw [← hl _ hs1 hs2]
      exact hbelow _ (le_max_left _ _) hs2
  have hcS : ∀ u, a ≤ u → u ≤ c → f u = f a := fun u h1 h2 =>
    (eq_or_lt_of_le h2).elim (fun e => by rw [e]; exact hfc) (hbelow u h1)
  rcases eq_or_lt_of_le hcb with h | h
  · rw [← h]; exact hfc
  · exfalso
    obtain ⟨δ, hδ, hr⟩ := hf c
    have hsS : min b (c + δ / 2) ∈ S := by
      refine ⟨le_min hab (by linarith), min_le_left _ _, fun u h1 h2 => ?_⟩
      by_cases huc : u ≤ c
      · exact hcS u h1 huc
      · have h3 : c ≤ u := le_of_lt (lt_of_not_ge huc)
        have h4 : u < c + δ := by
          have := min_le_right b (c + δ / 2); linarith
        rw [hr u h3 h4]; exact hfc
    have h5 := hc.1 hsS
    have h6 : c < min b (c + δ / 2) := lt_min h (by linarith)
    linarith

theorem not_changesAt {f : ℝ → Bool} {t : ℝ} (h : ¬ ChangesAt f t) : LeftConst f t :=
  not_not.mp h

/-- Just left of a change point (and of every other point of the covering list),
a Bool signal is constant and equal to the negation of its value at the point. -/
theorem left_of_change {f : ℝ → Bool} (hf : RightCont f) {L : List ℝ}
    (hL : ∀ t, ChangesAt f t → t ∈ L) {t ε₀ : ℝ}
    (hgap : ∀ a ∈ L, a < t → a ≤ t - ε₀) (hc : ChangesAt f t) :
    ∀ s, t - ε₀ < s → s < t → f s = !f t := by
  -- on (t - ε₀, t) the signal is constant
  have hconst : ∀ s s', t - ε₀ < s → s ≤ s' → s' < t → f s' = f s := by
    intro s s' h1 h2 h3
    refine eq_of_noChange hf h2 (fun u hu1 hu2 => not_changesAt fun hu => ?_)
    have := hgap u (hL u hu) (by linarith)
    linarith
  intro s hs1 hs2
  cases hfs : f s <;> cases hft : f t
  · exfalso
    apply hc
    refine ⟨t - s, by linarith, fun s' h1 h2 => ?_⟩
    rw [hconst s s' hs1 (by linarith) h2, hfs, hft]
  · rfl
  · rfl
  · exfalso
    apply hc
    refine ⟨t - s, by linarith, fun s' h1 h2 => ?_⟩
    rw [hconst s s' hs1 (by linarith) h2, hfs, hft]

/-- **Uniqueness**: two right-continuous Bool signals with the same change
points, all lying in a finite list `L`, that agree at a time `T` before every
point of `L`, are equal. -/
theorem eq_of_sameChanges {f g : ℝ → Bool} (hf : RightCont f) (hg : RightCont g)
    (L : List ℝ) (hL : ∀ t, ChangesAt f t → t ∈ L)
    (hfg : ∀ t, ChangesAt f t ↔ ChangesAt g t)
    (T : ℝ) (hT : ∀ a ∈ L, T < a) (h0 : f T = g T) : f = g := by
  have hL' : ∀ t, ChangesAt g t → t ∈ L := fun t h => hL t ((hfg t).mpr h)
  let h : ℝ → Bool := fun t => decide (f t = g t)
  have hrc : RightCont h := by
    intro t
    obtain ⟨ε₁, hε₁, h₁⟩ := hf t
    obtain ⟨ε₂, hε₂, h₂⟩ := hg t
    refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun s hts hs => ?_⟩
    have := min_le_left ε₁ ε₂; have := min_le_right ε₁ ε₂
    simp only [h, h₁ s hts (by linarith), h₂ s hts (by linarith)]
  have hlc : ∀ t, LeftConst h t := by
    intro t
    by_cases hc : ChangesAt f t
    · obtain ⟨ε₀, hε₀, hgap⟩ := exists_gap_left L t
      refine ⟨ε₀, hε₀, fun s h1 h2 => ?_⟩
      have e1 := left_of_change hf hL hgap hc s h1 h2
      have e2 := left_of_change hg hL' hgap ((hfg t).mp hc) s h1 h2
      simp only [h, e1, e2, Bool.not_inj_iff]
    · obtain ⟨ε₁, hε₁, h₁⟩ := not_changesAt hc
      obtain ⟨ε₂, hε₂, h₂⟩ := not_changesAt (fun hc' => hc ((hfg t).mpr hc'))
      refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun s hs1 hs2 => ?_⟩
      have := min_le_left ε₁ ε₂; have := min_le_right ε₁ ε₂
      simp only [h, h₁ s (by linarith) hs2, h₂ s (by linarith) hs2]
  funext t
  by_cases htT : T ≤ t
  · have := eq_of_noChange hrc htT (fun u _ _ => hlc u)
    simp only [h, h0, decide_true] at this
    exact of_decide_eq_true this
  · have htT' : t ≤ T := le_of_lt (lt_of_not_ge htT)
    have hnc : ∀ (k : ℝ → Bool), (∀ u, ChangesAt k u → u ∈ L) →
        ∀ u, t < u → u ≤ T → LeftConst k u := by
      intro k hk u _ hu2
      apply not_changesAt
      intro hu
      have := hT u (hk u hu)
      linarith
    have e1 := eq_of_noChange hf htT' (hnc f hL)
    have e2 := eq_of_noChange hg htT' (hnc g hL')
    rw [← e1, ← e2, h0]

/-! ### Sorting a finite list into a strictly increasing one -/

/-- Insert into a strictly increasing list (dropping duplicates). -/
def ins (x : ℝ) : List ℝ → List ℝ
  | [] => [x]
  | a :: l => if x < a then x :: a :: l else if x = a then a :: l else a :: ins x l

theorem mem_ins {x y : ℝ} : ∀ {l : List ℝ}, y ∈ ins x l ↔ y = x ∨ y ∈ l
  | [] => by simp [ins]
  | a :: l => by
    unfold ins
    split_ifs with h1 h2
    · simp only [List.mem_cons]
    · subst h2
      simp only [List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (h | h)
        · exact Or.inl h
        · exact h
    · simp only [List.mem_cons, mem_ins (l := l)]
      exact or_left_comm

theorem ins_sorted (x : ℝ) : ∀ {l : List ℝ}, l.Pairwise (· < ·) → (ins x l).Pairwise (· < ·)
  | [], _ => by simp [ins]
  | a :: l, h => by
    rw [List.pairwise_cons] at h
    unfold ins
    split_ifs with h1 h2
    · rw [List.pairwise_cons]
      refine ⟨?_, List.pairwise_cons.mpr h⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact h1
      · exact lt_trans h1 (h.1 b hb)
    · exact List.pairwise_cons.mpr h
    · rw [List.pairwise_cons]
      refine ⟨?_, ins_sorted x h.2⟩
      intro b hb
      rcases mem_ins.mp hb with rfl | hb
      · exact lt_of_le_of_ne (not_lt.mp h1) (fun e => h2 e.symm)
      · exact h.1 b hb

/-- Sort and deduplicate. -/
def sortStrict (l : List ℝ) : List ℝ := l.foldr ins []

theorem mem_sortStrict {y : ℝ} : ∀ {l : List ℝ}, y ∈ sortStrict l ↔ y ∈ l
  | [] => by simp [sortStrict]
  | a :: l => by
    show y ∈ ins a (sortStrict l) ↔ _
    rw [mem_ins, mem_sortStrict, List.mem_cons]

theorem sortStrict_sorted : ∀ (l : List ℝ), (sortStrict l).Pairwise (· < ·)
  | [] => List.Pairwise.nil
  | a :: l => ins_sorted a (sortStrict_sorted l)

/-- **Surjectivity onto well-formed signals**: every right-continuous
`f : ℝ → Bool` with finitely many change points is the denotation of an
event trace. -/
theorem exists_evTrace {f : ℝ → Bool} (hf : RightCont f) (hfin : FinChanges f) :
    ∃ e : EvTrace, e.toFun = f := by
  classical
  obtain ⟨l, hl⟩ := hfin
  let ts := sortStrict (l.filter (fun t => decide (ChangesAt f t)))
  have hmem : ∀ t, t ∈ ts ↔ ChangesAt f t := by
    intro t
    simp only [ts, mem_sortStrict, List.mem_filter, decide_eq_true_iff]
    exact ⟨fun h => h.2, fun h => ⟨hl t h, h⟩⟩
  have hsorted : ts.Pairwise (· < ·) := sortStrict_sorted _
  obtain ⟨T, hT⟩ := exists_below ts
  refine ⟨⟨f T, ts, hsorted⟩, ?_⟩
  show denote (f T) ts = f
  apply eq_of_sameChanges (denote_rightCont _ _) hf ts
    (fun t h => (changesAt_denote _ hsorted t).mp h)
    (fun t => (changesAt_denote _ hsorted t).trans (hmem t)) T hT
  exact denote_below _ _ hT

/-- The image of `EvTrace.toFun` is exactly the right-continuous signals with
finitely many changes. -/
theorem range_toFun (f : ℝ → Bool) :
    (∃ e : EvTrace, e.toFun = f) ↔ RightCont f ∧ FinChanges f := by
  constructor
  · rintro ⟨e, rfl⟩
    exact ⟨e.rightCont, e.finChanges⟩
  · rintro ⟨h1, h2⟩
    exact exists_evTrace h1 h2

end

end Formal.Core.Bridge
