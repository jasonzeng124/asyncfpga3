theorem t1 (N D : Int) (h0 : 3*D ≤ 10*N) (h1 : 10*N ≤ 4*D) : (10*N - 3*D)*(4*D-10*N) ≥ 0 := by
  have a : 0 ≤ 10*N - 3*D := by omega
  have b : 0 ≤ 4*D - 10*N := by omega
  exact Int.mul_nonneg a b
theorem t2 (N D : Int) (h : (10*N - 3*D)*(4*D-10*N) ≥ 0) (h2 : (10*N - 3*D)*(10*N - 3*D) ≥ 0) :
    -100*N*N + 70*N*D - 12*D*D ≥ 0 := by
  grind
theorem t3 (a b c d : Nat) (h : a ≤ b) (h2 : c ≤ d) : a*c ≤ b*d := by grind
theorem t4 (w0 w1 a0 a1 F S : Nat) (hFS : F ≤ S) (h : a1*(w0+w1) ≤ w1*(a0+a1)) :
    (a0*F+a1*S)*(w0+w1) ≤ (w0*F+w1*S)*(a0+a1) := by
  obtain ⟨Δ, rfl⟩ := Nat.exists_eq_add_of_le hFS
  have := Nat.mul_le_mul_left Δ h
  grind
