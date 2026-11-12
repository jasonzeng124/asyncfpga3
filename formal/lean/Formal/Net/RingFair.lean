import Formal.Net.Ring

/-!
# Ring fair window, the tight form N(N-1)/2 (audit answer, probe C-aud)

`Ring.fair_window` proves that an execution of a ring of `N ≥ 3` `bd_link`
controllers in which stage `i` never fires has at most `N(N-1)` transitions.
Ring.lean's module header promised `N(N-1)/2` (audit C.md row 3). That bound is
true: `Ring.nf_dist` bounds the stage `j` steps downstream of the starving stage
by `j` firings, and `0 + 1 + ... + (N-1) = N(N-1)/2`. Here it is proved.

Assumed: exactly Ring.lean's model (H_SI interleaving `Run`, the hand `ctl`
excitation, bridged to the real LUT by `Ring.excited_gate`). Proved:
`fair_window_half` (`2 · length ≤ N(N-1)`) and `every_stage_fires_half` (every
window of more than `N(N-1)/2` transitions fires every stage). Not covered:
whether `N(N-1)/2` is attained (no lower-bound witness here).
-/

namespace Formal.Net.Ring

theorem sumTo_ext {g h : Nat → Nat} : ∀ {m : Nat}, (∀ x, x < m → g x = h x) →
    sumTo g m = sumTo h m
  | 0, _ => rfl
  | m + 1, H => by
    simp only [sumTo]
    rw [sumTo_ext (fun x hx => H x (by omega)), H m (by omega)]

theorem sumTo_mono {g h : Nat → Nat} : ∀ {m : Nat}, (∀ x, x < m → g x ≤ h x) →
    sumTo g m ≤ sumTo h m
  | 0, _ => Nat.le_refl _
  | m + 1, H => by
    simp only [sumTo]
    have := sumTo_mono (m := m) (fun x hx => H x (by omega))
    have := H m (by omega)
    omega

theorem sumTo_add (g : Nat → Nat) (a : Nat) : ∀ b,
    sumTo g (a + b) = sumTo g a + sumTo (fun j => g (a + j)) b
  | 0 => rfl
  | b + 1 => by
    rw [← Nat.add_assoc]
    simp only [sumTo]
    rw [sumTo_add g a b]; omega

/-- `0 + 1 + ... + (m-1)`, doubled. -/
theorem two_sumTo_id : ∀ m, 2 * sumTo (fun j => j) m = m * (m - 1)
  | 0 => rfl
  | m + 1 => by
    simp only [sumTo]
    rw [Nat.mul_add, two_sumTo_id m]
    cases m with
    | zero => rfl
    | succ k =>
      simp only [Nat.add_sub_cancel, Nat.mul_comm, Nat.mul_succ]
      omega

/-- Rotating the summation index by `i < m` does not change a sum over `0..m-1`. -/
theorem sumTo_rotate (f : Nat → Nat) {i m : Nat} (hi : i < m) :
    sumTo f m = sumTo (fun j => f ((i + j) % m)) m := by
  have e1 : m = i + (m - i) := by omega
  have lhs : sumTo f m = sumTo f i + sumTo (fun j => f (i + j)) (m - i) := by
    rw [← sumTo_add]; rw [← e1]
  have rhs : sumTo (fun j => f ((i + j) % m)) m =
      sumTo (fun j => f ((i + j) % m)) (m - i) +
        sumTo (fun j => f ((i + ((m - i) + j)) % m)) i := by
    have := sumTo_add (fun j => f ((i + j) % m)) (m - i) i
    rw [show m - i + i = m by omega] at this
    exact this
  rw [lhs, rhs]
  have a1 : sumTo (fun j => f ((i + j) % m)) (m - i) = sumTo (fun j => f (i + j)) (m - i) :=
    sumTo_ext (fun j hj => by rw [Nat.mod_eq_of_lt (by omega)])
  have a2 : sumTo (fun j => f ((i + ((m - i) + j)) % m)) i = sumTo f i := by
    apply sumTo_ext
    intro j hj
    have : i + ((m - i) + j) = j + m := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  rw [a1, a2]; omega

/-- **Tight fair window.** On a ring of `N ≥ 3` stages, an execution in which
stage `i` never fires has at most `N(N-1)/2` transitions (stated without
division: `2 · length ≤ N(N-1)`). Strengthens `Ring.fair_window` (`≤ N(N-1)`). -/
theorem fair_window_half {n : Nat} (hn : 3 ≤ n) {i : Nat} (hi : i < n) {s : State}
    {is : List Nat} (hr : Run n s is) (h0 : nf i is = 0) : 2 * is.length ≤ n * (n - 1) := by
  rw [length_eq_sum (run_lt hr), sumTo_rotate (fun x => nf x is) hi, ← two_sumTo_id n]
  apply Nat.mul_le_mul_left
  exact sumTo_mono (fun j _ => nf_dist hn hi hr h0 j)

/-- The same with the division written out, as Ring.lean's header states it. -/
theorem fair_window_div {n : Nat} (hn : 3 ≤ n) {i : Nat} (hi : i < n) {s : State}
    {is : List Nat} (hr : Run n s is) (h0 : nf i is = 0) : is.length ≤ n * (n - 1) / 2 := by
  have := fair_window_half hn hi hr h0; omega

/-- Every window of more than `N(N-1)/2` transitions fires every stage. -/
theorem every_stage_fires_half {n : Nat} (hn : 3 ≤ n) {s : State} {is : List Nat}
    (hr : Run n s is) (hlen : n * (n - 1) < 2 * is.length) : ∀ i, i < n → 0 < nf i is := by
  intro i hi
  apply Classical.byContradiction; intro h
  have := fair_window_half hn hi hr (by omega); omega

end Formal.Net.Ring
