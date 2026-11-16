/- T121: own restatement of formal Spec.lean:265-277 (ReqMoves, ReqLive), copied verbatim
   in meaning. Claim checked: with a,b,start sharing one request node (Spec.lean:392),
   a run where a's ack is high and start's ack low for ever from t (r high at t)
   admits no continuation satisfying EnvIn(a) and EnvIn(start): Env is unsatisfiable,
   so NetCorrectSeq holds vacuously on such a deadlocked run. -/
abbrev Sig := Nat → Bool
def ReqMoves (r a : Sig) (t0 : Nat) : Prop :=
  ∀ t, t0 ≤ t → r (t + 1) ≠ r t → r t = a t
def ReqLive (r a : Sig) (t0 : Nat) (more : Nat → Prop) : Prop :=
  ∀ t, t0 ≤ t → r t = a t → (r t = true ∨ more 0) → ∃ s, t ≤ s ∧ r s ≠ a s

theorem stuck_high (r sa : Sig) (R t : Nat) (hRt : R ≤ t) (hr : r t = true)
    (hsa : ∀ s, t ≤ s → sa s = false) (hm : ReqMoves r sa R) :
    ∀ k, r (t + k) = true := by
  intro k
  induction k with
  | zero => simpa using hr
  | succ k ih =>
    by_cases h : r (t + k + 1) = r (t + k)
    · rw [← Nat.add_assoc, h]; exact ih
    · have := hm (t + k) (by omega) h
      rw [ih, hsa (t + k) (by omega)] at this; exact absurd this (by decide)

theorem env_vacuous (r aa sa : Sig) (R t : Nat) (more : Nat → Prop) (hRt : R ≤ t)
    (hr : r t = true) (haa : ∀ s, t ≤ s → aa s = true) (hsa : ∀ s, t ≤ s → sa s = false) :
    ¬ (ReqMoves r sa R ∧ ReqLive r aa R more) := by
  rintro ⟨hm, hl⟩
  obtain ⟨s, hts, hne⟩ := hl t hRt (by rw [hr, haa t (Nat.le_refl _)]) (Or.inl hr)
  have := stuck_high r sa R t hRt hr hsa hm (s - t)
  rw [Nat.add_sub_cancel' hts] at this
  exact hne (by rw [this, haa s hts])

#print axioms env_vacuous
