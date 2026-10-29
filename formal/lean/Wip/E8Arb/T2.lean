def a0h : Nat → Bool := fun t => decide (t < 10)
def qh : Nat → Bool := fun t => decide (t ≤ 10)
example (t : Nat) : qh t = (false || if a0h (t - 1) then qh (t - 1) else ((false && !true) || (qh (t - 1) && !(!false && true)))) := by
  simp only [qh, a0h, Bool.false_or]
  by_cases h : t - 1 < 10
  · simp only [h, decide_true, if_true]; rw [Bool.eq_iff_iff]; simp; omega
  · simp only [h, decide_false, Bool.false_eq_true, if_false]; rw [Bool.eq_iff_iff]; simp; omega
