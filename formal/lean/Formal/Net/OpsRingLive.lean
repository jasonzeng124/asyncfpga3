import Formal.Net.BridgeRing
import Formal.Net.OpsTimedLive

/-!
# Probe C-8o (goal 2): a ring of link controllers, linear liveness bound

The ring of `tb_ring.v` (`BridgeRing.ringNet n K`: stage `i` is the real
`bd_c2n`/`bd_c2n_set` LUT in run mode, `c_i = C(c_{i-1}, ¬c_{i+1})`), as a
timed trace in which every stage is an inertial channel `[lo i, hi i]`
(`Bridge.Timed`, H_BOUNDED_DELAY inertial form) with isochronic neighbour
wires (H_ISO, as in C-8d) and the feedback read from the node (H_FB_SETTLED).

8d's `timed_ring_every_stage` bounds the gap between toggles of a stage by
`(N(N-1)+1)·H` (from 9a's SI counting argument). Here:

* `ring_every_window`: with one loop token (`D = 2` wavefronts at every
  time, which `timed_ring_safe` gives from a clean reset), EVERY stage `j`
  toggles in EVERY window `[t, t + N·H)`, where `H` bounds every `hi i`.

Proof (8n's plan, slightly sharper): take the wavefront nearest behind `j`, at
offset `m` (`m ≤ N-2`). Every stage strictly between it and `j` has no
wavefront, so it is frozen (`frozen`), and the wavefront itself is excited (its
successor has no wavefront); it moves within `hi` (`fire_local`, from the
upper bound alone) while its neighbours hold, so `m` drops by one per `H`
(`near`). At `m = 0` the wavefront sits at `j`: either `j` is excited
(within `H`), or the other wavefront is at `j+1`, which is then excited
(`D = 2`, `N ≥ 3`) and frees `j` within `H`, and `j` moves within another
`H`. Total `(m+2)·H ≤ N·H`. No fairness, no SI-run counting.

* `ring_every_window_reset`: the same from `x 0 = resetState K`, `0 < K < N`.
* `ring_unit_live`: non-vacuity (the unit-delay run satisfies the hypotheses).

Not proved here: a matching lower bound. The informal worst case (both
wavefronts adjacent, just behind `j`, the front one slow on every stage) gives
about `(N-1)·H`, so `N·H` should be within one `H` of tight; at uniform unit
delay the actual gap is much smaller (3 ticks for N = 5).
-/

namespace Formal.Net.Ops.RingLive
open Formal.Net Formal.Net.Bridge Formal.Net.Bridge.RingT
open Formal.Net.Ops.TimedLive (cause1 reach_step)
open Formal.Net.Ring (prv nxt ctl tok D cnt prv_eq nxt_eq prv_lt nxt_lt prv_nxt nxt_prv)

variable {n K : Nat} {lo hi : Nat → Nat} {x : Nat → State}

theorem ring_f (n K i : Nat) (s : State) :
    (ringNet n K).f i s = ctl (s (prv n i)) (s (nxt n i)) (s i) := Ring.gate_run n K s i

theorem ctl_tie (b q : Bool) : ctl q b q = q := by cases b <;> cases q <;> decide
theorem ctl_blk (a q : Bool) : ctl a (!q) q = q := by cases a <;> cases q <;> decide
theorem ctl_go (q : Bool) : ctl (!q) q q = !q := by cases q <;> decide

/-- A stage with no wavefront (`c_{i-1} = c_i`) does not change in the next tick. -/
theorem frozen (hx : Timed (ringNet n K) lo hi x) {i t : Nat} (hi' : i < n)
    (h : x t (prv n i) = x t i) : x (t + 1) i = x t i := by
  apply Classical.byContradiction
  intro hc
  apply hc
  rw [cause1 hx hi' hc, ring_f, h, ctl_tie]

/-- A stage whose successor carries a wavefront (`c_{i+1} ≠ c_i`) does not change. -/
theorem blocked (hx : Timed (ringNet n K) lo hi x) {i t : Nat} (hi' : i < n)
    (h : x t (nxt n i) ≠ x t i) : x (t + 1) i = x t i := by
  apply Classical.byContradiction
  intro hc
  have e : x t (nxt n i) = !x t i := by revert h; cases x t (nxt n i) <;> cases x t i <;> simp
  apply hc
  rw [cause1 hx hi' hc, ring_f, e, ctl_blk]

/-- First change: a trace that differs from its value at `t` somewhere in `[t, w]`
has a first time `w' ∈ (t, w]` at which it differs. -/
theorem first_change (s : Nat → Bool) (t : Nat) : ∀ w,
    (∃ v, t ≤ v ∧ v ≤ w ∧ s v ≠ s t) →
    ∃ w', t < w' ∧ w' ≤ w ∧ s w' ≠ s t ∧ ∀ u, t ≤ u → u < w' → s u = s t := by
  intro w
  induction w with
  | zero =>
    rintro ⟨v, h1, h2, h3⟩
    have : v = 0 := by omega
    subst this; have : t = 0 := by omega
    subst this; exact absurd rfl h3
  | succ w ih =>
    rintro ⟨v, h1, h2, h3⟩
    by_cases hex : ∃ v, t ≤ v ∧ v ≤ w ∧ s v ≠ s t
    · obtain ⟨w', a, b, c, d⟩ := ih hex
      exact ⟨w', a, by omega, c, d⟩
    · have hv : v = w + 1 := by
        apply Classical.byContradiction; intro hne
        exact hex ⟨v, h1, by omega, h3⟩
      subst hv
      have ht : t < w + 1 := by
        rcases Nat.eq_or_lt_of_le h1 with e | e
        · rw [e] at h3; exact absurd rfl h3
        · exact e
      refine ⟨w + 1, ht, Nat.le_refl _, h3, fun u a b => ?_⟩
      apply Classical.byContradiction; intro hu
      exact hex ⟨u, a, by omega, hu⟩

/-- **One wavefront move.** An excited stage (`c_{i-1} ≠ c_i = c_{i+1}`) changes
within `hi i`; until it does (and at that instant) both neighbours hold. Uses
only the upper bound (`settle`) and `cause1`. -/
theorem fire_local (hx : Timed (ringNet n K) lo hi x) {i t : Nat} (hi' : i < n)
    (h1 : x t (prv n i) ≠ x t i) (h2 : x t (nxt n i) = x t i) :
    ∃ w, t < w ∧ w ≤ t + hi i ∧ x w i ≠ x t i ∧ (∀ u, t ≤ u → u < w → x u i = x t i) ∧
      ∀ u, t ≤ u → u ≤ w → x u (prv n i) = x t (prv n i) ∧ x u (nxt n i) = x t (nxt n i) := by
  have inv : ∀ u, t ≤ u → (∀ v, t ≤ v → v < u → x v i = x t i) →
      x u (prv n i) = x t (prv n i) ∧ x u (nxt n i) = x t (nxt n i) := by
    intro u
    induction u with
    | zero => intro h _; have : t = 0 := by omega
              subst this; exact ⟨rfl, rfl⟩
    | succ u ih =>
      intro htu hv
      rcases Nat.eq_or_lt_of_le htu with e | e
      · rw [← e]; exact ⟨rfl, rfl⟩
      · obtain ⟨a, b⟩ := ih (by omega) (fun v h h' => hv v h (by omega))
        have hu := hv u (by omega) (by omega)
        refine ⟨?_, ?_⟩
        · rw [blocked hx (prv_lt hi') (by rw [nxt_prv hi', hu, a]; exact fun e => h1 e.symm), a]
        · rw [frozen hx (nxt_lt hi') (by rw [prv_nxt hi', hu, b, h2]), b]
  obtain ⟨w, hw1, hw2, hw3⟩ := reach_step (v := !x t i) hx (g := i) (T := t) (t := t) hi'
    (Nat.le_refl _) (fun u h1u _ hnr => by
      have hv : ∀ v, t ≤ v → v < u → x v i = x t i := fun v a b => by
        have := hnr v a (by omega); revert this; cases x v i <;> cases x t i <;> simp
      have hu : x u i = x t i := by
        have := hnr u h1u (Nat.le_refl _); revert this; cases x u i <;> cases x t i <;> simp
      obtain ⟨a, b⟩ := inv u h1u hv
      have e : x t (prv n i) = !x t i := by
        revert h1; cases x t (prv n i) <;> cases x t i <;> simp
      rw [ring_f, a, b, hu, e, h2, ctl_go])
  have hne : x w i ≠ x t i := by rw [hw3]; cases x t i <;> simp
  obtain ⟨w', a, b, c, d⟩ := first_change (fun u => x u i) t w ⟨w, hw1, Nat.le_refl _, hne⟩
  refine ⟨w', a, by omega, c, d, fun u h1u h2u => inv u h1u (fun v e f => d v e (by omega))⟩

/-! ## Offsets behind the target stage `j` -/

/-- The stage `d` places behind `j` (cyclically), for `d ≤ n`. -/
def off (n j d : Nat) : Nat := if d ≤ j then j - d else j + n - d

theorem off_lt {j d : Nat} (hj : j < n) (hd : d ≤ n) : off n j d < n := by
  unfold off; split <;> omega
theorem off_zero (j : Nat) : off n j 0 = j := by simp [off]
theorem off_n {j : Nat} (hj : j < n) : off n j n = j := by
  unfold off; split <;> omega
theorem off_prv {j d : Nat} (hj : j < n) (hd : d < n) : prv n (off n j d) = off n j (d + 1) := by
  rw [prv_eq (off_lt hj (by omega))]; unfold off; (repeat' split) <;> omega
theorem off_nxt {j d : Nat} (hj : j < n) (hd : d < n) : nxt n (off n j (d + 1)) = off n j d := by
  rw [← off_prv hj hd, nxt_prv (off_lt hj (by omega))]
theorem off_surj {j i : Nat} (hj : j < n) (hi : i < n) : ∃ k, k < n ∧ off n j k = i :=
  ⟨if i ≤ j then j - i else j + n - i, by split <;> omega, by unfold off; (repeat' split) <;> omega⟩

theorem three_distinct {j : Nat} (hn : 3 ≤ n) (hj : j < n) :
    j ≠ nxt n j ∧ nxt n j ≠ nxt n (nxt n j) ∧ j ≠ nxt n (nxt n j) ∧
    prv n j ≠ j ∧ prv n j ≠ nxt n j := by
  have e1 := nxt_eq hj
  have e2 := nxt_eq (nxt_lt hj)
  have e3 := prv_eq hj
  generalize nxt n (nxt n j) = c at *
  generalize nxt n j = b at *
  generalize prv n j = a at *
  (repeat' split at e1) <;> (repeat' split at e2) <;> (repeat' split at e3) <;> omega

/-- Three distinct wavefronts give `D ≥ 3`. -/
theorem cnt_three {f : Nat → Bool} {a b c : Nat} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (ha : f a = true) (hb : f b = true) (hc : f c = true) : ∀ m,
    (if a < m then 1 else 0) + (if b < m then 1 else 0) + (if c < m then 1 else 0) ≤ cnt f m := by
  intro m
  induction m with
  | zero => simp [cnt]
  | succ m ih =>
    simp only [cnt]
    have ea : (if a < m + 1 then 1 else 0) = (if a < m then 1 else 0) + (if a = m then 1 else 0) := by
      (repeat' split) <;> omega
    have eb : (if b < m + 1 then 1 else 0) = (if b < m then 1 else 0) + (if b = m then 1 else 0) := by
      (repeat' split) <;> omega
    have ec : (if c < m + 1 then 1 else 0) = (if c < m then 1 else 0) + (if c = m then 1 else 0) := by
      (repeat' split) <;> omega
    have key : (if a = m then 1 else 0) + (if b = m then 1 else 0) + (if c = m then 1 else 0)
        ≤ (if f m = true then 1 else 0) := by
      by_cases hA : a = m
      · subst hA; simp [ha, Ne.symm hab, Ne.symm hac]
      · by_cases hB : b = m
        · subst hB; simp [hb, hA, Ne.symm hbc]
        · by_cases hC : c = m
          · subst hC; simp [hc, hA, hB]
          · simp [hA, hB, hC]
    rw [ea, eb, ec]; omega

theorem tok_true {s : State} {i : Nat} (h : s (prv n i) ≠ s i) : tok n s i = true :=
  (Ring.tok_iff n s i).2 h

/-- With one loop token, two adjacent wavefronts at `i`, `nxt i` leave none at `k`
for any third stage `k`. -/
theorem no_third {s : State} (hD : D n s = 2) {a b c : Nat} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (ha : a < n) (hb : b < n) (hc : c < n)
    (h1 : s (prv n a) ≠ s a) (h2 : s (prv n b) ≠ s b) : s (prv n c) = s c := by
  apply Classical.byContradiction; intro h3
  have := cnt_three hab hbc hac (tok_true h1) (tok_true h2) (tok_true h3) n
  simp only [ha, hb, hc, ite_true] at this
  unfold D at hD; omega

theorem bool3 {a b c : Bool} (h1 : a ≠ b) (h2 : c ≠ a) : c = b := by
  revert h1 h2; cases a <;> cases b <;> cases c <;> simp

section near
variable (hx : Timed (ringNet n K) lo hi x) (hn : 3 ≤ n) (hD : ∀ t, D n (x t) = 2)
  {H : Nat} (hH : ∀ i, hi i ≤ H) {j : Nat} (hj : j < n)
include hx hn hD hH hj

/-- **The wavefront nearest behind `j`**, at offset `m`, reaches and moves `j`
within `(m + 2)·H`. -/
theorem near : ∀ m t, m < n → (∀ k, k ≤ m → x t (off n j k) = x t j) →
    x t (off n j (m + 1)) ≠ x t (off n j m) →
    ∃ u, t ≤ u ∧ u < t + (m + 2) * H ∧ x (u + 1) j ≠ x u j := by
  intro m
  induction m with
  | zero =>
    intro t _ _ htok
    rw [off_zero, ← off_prv hj (by omega), off_zero] at htok
    obtain ⟨d1, d2, d3, d4, d5⟩ := three_distinct hn hj
    by_cases hA : x t (nxt n j) = x t j
    · obtain ⟨w, a, b, c, d, _⟩ := fire_local hx hj htok hA
      refine ⟨w - 1, by omega, by have := hH j; omega, ?_⟩
      rw [show w - 1 + 1 = w by omega, d (w - 1) (by omega) (by omega)]; exact c
    · -- the other wavefront is at `nxt j`; it is excited
      have hi1 := nxt_lt (n := n) hj
      have g1 : x t (prv n (nxt n j)) ≠ x t (nxt n j) := by
        rw [prv_nxt hj]; exact fun e => hA e.symm
      have g2 : x t (nxt n (nxt n j)) = x t (nxt n j) := by
        have := no_third (hD t) d1 d2 d3 hj hi1 (nxt_lt hi1) htok g1
        rw [prv_nxt hi1] at this; exact this.symm
      obtain ⟨w1, a1, b1, c1, d1', e1⟩ := fire_local hx hi1 g1 g2
      have P : ∀ u, t ≤ u → u ≤ w1 → x u (prv n j) = x t (prv n j) := by
        intro u
        induction u with
        | zero => intro h _; have : t = 0 := by omega
                  subst this; rfl
        | succ u ih =>
          intro h1 h2
          rcases Nat.eq_or_lt_of_le h1 with e | e
          · rw [← e]
          · have hp := ih (by omega) (by omega)
            have hjj : x u j = x t j := by
              have := (e1 u (by omega) (by omega)).1; rwa [prv_nxt hj] at this
            have hii := d1' u (by omega) (by omega)
            have t1 : x u (prv n j) ≠ x u j := by rw [hp, hjj]; exact htok
            have t2 : x u (prv n (nxt n j)) ≠ x u (nxt n j) := by
              rw [prv_nxt hj, hjj, hii]; exact fun e => hA e.symm
            have hpj := prv_lt (n := n) hj
            have : x u (prv n (prv n j)) = x u (prv n j) :=
              no_third (hD u) d1 (Ne.symm d5) (Ne.symm d4) hj hi1 hpj t1 t2
            rw [frozen hx hpj this, hp]
      have hjw : x w1 j = x t j := by
        have := (e1 w1 (by omega) (Nat.le_refl _)).1; rwa [prv_nxt hj] at this
      have k1 : x w1 (prv n j) ≠ x w1 j := by rw [P w1 (by omega) (Nat.le_refl _), hjw]; exact htok
      have k2 : x w1 (nxt n j) = x w1 j := by rw [hjw]; exact bool3 hA c1
      obtain ⟨w2, a2, b2, c2, d2', _⟩ := fire_local hx hj k1 k2
      refine ⟨w2 - 1, by omega, by have := hH j; have := hH (nxt n j); omega, ?_⟩
      rw [show w2 - 1 + 1 = w2 by omega, d2' (w2 - 1) (by omega) (by omega)]; exact c2
  | succ m ih =>
    intro t hm heq htok
    have hi1 : off n j (m + 1) < n := off_lt hj (by omega)
    have g1 : x t (prv n (off n j (m + 1))) ≠ x t (off n j (m + 1)) := by
      rw [off_prv hj (by omega)]; exact htok
    have g2 : x t (nxt n (off n j (m + 1))) = x t (off n j (m + 1)) := by
      rw [off_nxt hj (by omega), heq m (by omega), heq (m + 1) (Nat.le_refl _)]
    obtain ⟨w, a, b, c, d, _⟩ := fire_local hx hi1 g1 g2
    have Q : ∀ u, t ≤ u → u ≤ w → ∀ k, k ≤ m → x u (off n j k) = x t j := by
      intro u
      induction u with
      | zero => intro h _; have : t = 0 := by omega
                subst this; exact fun k hk => heq k (by omega)
      | succ u ih' =>
        intro h1 h2 k hk
        rcases Nat.eq_or_lt_of_le h1 with e | e
        · rw [← e]; exact heq k (by omega)
        · have hq := ih' (by omega) (by omega)
          have hk1 : x u (off n j (k + 1)) = x t j := by
            by_cases e' : k + 1 ≤ m
            · exact hq (k + 1) e'
            · have : k = m := by omega
              subst this
              rw [d u (by omega) (by omega)]; exact heq (k + 1) (Nat.le_refl _)
          rw [frozen hx (off_lt hj (by omega)) (by rw [off_prv hj (by omega), hk1, hq k hk]), hq k hk]
    have hjw : x w j = x t j := by have := Q w (by omega) (Nat.le_refl _) 0 (by omega); rwa [off_zero] at this
    obtain ⟨u, h1, h2, h3⟩ := ih w (by omega)
      (fun k hk => by rw [Q w (by omega) (Nat.le_refl _) k hk, hjw])
      (by rw [Q w (by omega) (Nat.le_refl _) m (Nat.le_refl _)]
          exact fun e => c (by rw [e]; exact (heq (m + 1) (Nat.le_refl _)).symm))
    refine ⟨u, by omega, ?_, h3⟩
    have := hH (off n j (m + 1))
    rw [show m + 1 + 2 = (m + 2) + 1 by omega, Nat.add_mul, Nat.one_mul]; omega

/-- **Linear liveness bound.** With one loop token at every time, every stage `j`
toggles in every window `[t, t + N·H)`. -/
theorem ring_every_window (t : Nat) : ∃ u, t ≤ u ∧ u < t + n * H ∧ x (u + 1) j ≠ x u j := by
  -- find the nearest wavefront behind `j`
  have search : ∀ m, m < n → (∀ k, k ≤ m → x t (off n j k) = x t j) ∨
      ∃ m', m' < m ∧ (∀ k, k ≤ m' → x t (off n j k) = x t j) ∧
        x t (off n j (m' + 1)) ≠ x t (off n j m') := by
    intro m
    induction m with
    | zero => intro _; left; intro k hk; have : k = 0 := by omega
              subst this; rw [off_zero]
    | succ m ih =>
      intro hm
      rcases ih (by omega) with h | ⟨m', a, b, c⟩
      · by_cases e : x t (off n j (m + 1)) = x t j
        · left; intro k hk
          rcases Nat.eq_or_lt_of_le hk with e' | e'
          · rw [e']; exact e
          · exact h k (by omega)
        · right; exact ⟨m, by omega, h, by rw [h m (Nat.le_refl _)]; exact e⟩
      · right; exact ⟨m', by omega, b, c⟩
  rcases search (n - 1) (by omega) with h | ⟨m, a, b, c⟩
  · -- no wavefront anywhere: contradicts D = 2
    exfalso
    have hz : ∀ i, i < n → tok n (x t) i = false := by
      intro i hi
      obtain ⟨k, hk, rfl⟩ := off_surj hj hi
      have : x t (prv n (off n j k)) = x t (off n j k) := by
        rw [off_prv hj hk, h k (by omega)]
        by_cases e : k + 1 = n
        · rw [e, off_n hj]
        · exact h (k + 1) (by omega)
      unfold tok; rw [this]; simp
    have := hD t
    unfold D at this
    obtain ⟨i, hi, hti⟩ := Ring.cnt_pos (f := tok n (x t)) (m := n) (by omega)
    rw [hz i hi] at hti; cases hti
  · obtain ⟨u, h1, h2, h3⟩ := near hx hn hD hH hj m t (by omega) b c
    refine ⟨u, h1, ?_, h3⟩
    have : (m + 2) * H ≤ n * H := Nat.mul_le_mul_right _ (by omega)
    omega

end near

/-- **From a clean reset** (`x 0 = resetState K`, `0 < K < N`, `N ≥ 3`): every
stage toggles in every window of `N·H`. Improves 8d's `(N(N-1)+1)·H`. -/
theorem ring_every_window_reset (hn : 3 ≤ n) (hK0 : 0 < K) (hKn : K < n)
    (hx : Timed (ringNet n K) lo hi x) (h0 : x 0 = Ring.resetState K)
    {H : Nat} (hH : ∀ i, hi i ≤ H) (t j : Nat) (hj : j < n) :
    ∃ u, t ≤ u ∧ u < t + n * H ∧ x (u + 1) j ≠ x u j :=
  ring_every_window hx hn (fun t => timed_ring_safe hn hK0 hKn hx.toF h0 t) hH hj t

/-- Non-vacuity: the unit-delay run from reset meets every hypothesis. -/
theorem ring_unit_live (n K : Nat) (hn : 3 ≤ n) (hK0 : 0 < K) (hKn : K < n) (t j : Nat) (hj : j < n) :
    ∃ u, t ≤ u ∧ u < t + n ∧
      unitTrace (ringNet n K) (Ring.resetState K) (u + 1) j ≠
        unitTrace (ringNet n K) (Ring.resetState K) u j := by
  have := ring_every_window_reset hn hK0 hKn (unit_timed (ringNet n K) (Ring.resetState K)) rfl
    (H := 1) (fun _ => Nat.le_refl _) t j hj
  simpa using this

end Formal.Net.Ops.RingLive
