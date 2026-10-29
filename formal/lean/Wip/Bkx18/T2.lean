theorem g1 (D N w0 w1 F S m : Nat) (hN : N ≤ D)
    (h : (D - N) * (w0*F + w1*S) ≤ D*(w0+w1)*m) :
    (w0:Int) * (((D:Int)-N)*F - D*m) + (w1:Int)*(((D:Int)-N)*S - D*m) ≤ 0 := by
  grind
-- symbolic corner Scat-style goal in Nat from Int facts
theorem g2 (N D : Nat) (hN : N ≤ D) (h0 : 3*D ≤ 10*N) (h1 : 10*N ≤ 4*D)
    (hb : 0 ≤ (10*(N:Int) - 3*D)*(4*D-10*N)) :
    (D - N) * ((D+N)*5 - D*3) ≤ D * ((D+N)*7) := by
  grind
theorem s1 (a b c d : Nat) (h : a < b) (h2 : c ≤ d) (hc : 0 < c) : a * c < b * d :=
  Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right h hc) (Nat.mul_le_mul_left _ h2)
