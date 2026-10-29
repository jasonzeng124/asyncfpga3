def r1c : Nat → Bool := fun t => decide (18 ≤ t)
def r2c : Nat → Bool := fun t => decide (10 ≤ t)
def qc : Nat → Bool := fun t => decide (t ≤ 10 ∨ 8 ≤ (t - 11) % 10)
example (t : Nat) : qc t = (false || if false then qc (t - 10) else ((r1c (t-1) && !r2c (t-1)) || (qc (t - 10) && !(!r1c (t-1) && r2c (t-1))))) := by
  simp only [qc, r1c, r2c, Bool.false_or, Bool.false_eq_true, if_false]
  rw [Bool.eq_iff_iff]; simp; omega
def g2c : Nat → Bool := fun t => r2c (t - 1) && !qc (t - 1)
example (k : Nat) : (∀ u, 22 + 10 * k ≤ u → u ≤ 29 + 10 * k → g2c u = true) ∧ g2c (30 + 10 * k) = false := by
  constructor
  · intro u h1 h2
    simp [g2c, r2c, qc]; omega
  · simp [g2c, r2c, qc]; omega
