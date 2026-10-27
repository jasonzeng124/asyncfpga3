import Formal.Net.HandshakeMuller

/-!
# Track 8a: liveness of the Muller pipeline

What liveness needs, as named hypotheses (none is implied by the safety
model, where "never move" is always allowed):

* `H_SRC_LIVE`: the source is an infinite producer: whenever it is its turn on
  link 0 (`req = ack`), it eventually moves `req`.
* `H_SNK_LIVE`: the sink is an always-ready consumer: whenever it is its turn
  on link n (`ack ≠ req`), it eventually moves `ack`.
* `H_CEL_FAIR`: every C-element that is excited (its LUT function differs from
  its output) eventually changes. This is the liveness half of
  H_BOUNDED_DELAY (`settle`); the safety half is `H_CEL_SI`.
  (Weak fairness is enough because an excited C-element stays excited under
  the protocol; we do not even need that, since the proof only uses
  excitation in a state that never changes.)

Result `muller_live`: every link's ack changes infinitely often, and the
number of tokens delivered to the sink is unbounded.

Proof idea: (1) on a protocol channel, changes of `req` and `ack` alternate,
so if one wire stops, the other stops one change later (`stops_of`);
(2) every stage node is the ack of one link and the req of the next, so one
stopped wire stops every wire (induction both ways along the pipeline);
(3) a state where every wire is stable forever has some element excited
(`deadlock_free`, the combinational core), contradicting fairness.
-/

namespace Formal.Net.Handshake
open Formal.Net Formal.Cells

theorem bool_flip : ∀ a c b : Bool, (a == c) = b → ((!a) == c) = b → False := by decide

/-- If `x` moves only when `(x == y) = b`, then once `y` stops, `x` stops after at most one more change. -/
theorem stops_of {x y : Trace} (b : Bool)
    (hx : ∀ t, x (t+1) ≠ x t → (x t == y t) = b)
    (T : Nat) (hy : ∀ t, T ≤ t → y (t+1) = y t) :
    ∃ T', ∀ t, T' ≤ t → x (t+1) = x t := by
  have yconst : ∀ k, y (T + k) = y T := by
    intro k; induction k with
    | zero => rfl
    | succ k ih => rw [← Nat.add_assoc, hy (T + k) (by omega), ih]
  by_cases h : ∃ t1, T ≤ t1 ∧ x (t1+1) ≠ x t1
  · obtain ⟨t1, ht1, hc⟩ := h
    have hb := hx t1 hc
    have xflip : x (t1 + 1) = !x t1 := by
      cases h1 : x t1 <;> cases h2 : x (t1+1) <;> simp_all
    have yt : ∀ u, T ≤ u → y u = y T := by
      intro u hu; have := yconst (u - T); rwa [show T + (u - T) = u by omega] at this
    have hyt1 : y t1 = y T := yt t1 ht1
    -- x never moves again after t1+1
    have stay : ∀ k, x (t1 + 1 + k) = x (t1 + 1) := by
      intro k; induction k with
      | zero => rfl
      | succ k ih =>
        rw [← Nat.add_assoc]
        by_cases hm : x (t1 + 1 + k + 1) = x (t1 + 1 + k)
        · rw [hm, ih]
        · exfalso
          have h2 := hx _ hm
          rw [ih, xflip, yt _ (by omega), ← hyt1] at h2
          exact bool_flip _ _ _ hb h2
    refine ⟨t1 + 1, fun t ht => ?_⟩
    have a1 := stay (t + 1 - (t1 + 1)); have a2 := stay (t - (t1 + 1))
    rw [show t1 + 1 + (t + 1 - (t1 + 1)) = t + 1 by omega] at a1
    rw [show t1 + 1 + (t - (t1 + 1)) = t by omega] at a2
    rw [a1, a2]
  · refine ⟨T, fun t ht => ?_⟩
    apply Classical.byContradiction; intro hc
    exact h ⟨t, ht, hc⟩

/-- On a protocol channel, if `ack` eventually stops then `req` does. -/
theorem req_stops {c : Chan} (hp : Protocol c) (T : Nat)
    (hy : ∀ t, T ≤ t → c.ack (t+1) = c.ack t) : ∃ T', ∀ t, T' ≤ t → c.req (t+1) = c.req t := by
  refine stops_of true (fun t hc => ?_) T hy
  have := (hp.2 t).1 hc; simp [this]

/-- On a protocol channel, if `req` eventually stops then `ack` does. -/
theorem ack_stops {c : Chan} (hp : Protocol c) (T : Nat)
    (hy : ∀ t, T ≤ t → c.req (t+1) = c.req t) : ∃ T', ∀ t, T' ≤ t → c.ack (t+1) = c.ack t := by
  refine stops_of false (fun t hc => ?_) T hy
  have := (hp.2 t).2 hc; simp [this]

/-- The wires of the pipeline: `sig 0` = source request, `sig (j+1)` = ack of
link `j` (= node of stage `j` for `j < n`, sink ack for `j = n`). -/
def sig (ch : Nat → Chan) : Nat → Trace
  | 0 => (ch 0).req
  | j + 1 => (ch j).ack

def Stops (s : Trace) : Prop := ∃ T, ∀ t, T ≤ t → s (t+1) = s t

/-- Finitely many eventually-stopping wires stop together. -/
theorem stops_common (s : Nat → Trace) : ∀ N, (∀ j, j ≤ N → Stops (s j)) →
    ∃ T, ∀ j, j ≤ N → ∀ t, T ≤ t → s j (t+1) = s j t := by
  intro N
  induction N with
  | zero =>
    intro h; obtain ⟨T, hT⟩ := h 0 (Nat.le_refl _)
    exact ⟨T, fun j hj t ht => by rw [Nat.le_zero.mp hj]; exact hT t ht⟩
  | succ N ih =>
    intro h
    obtain ⟨T1, h1⟩ := ih (fun j hj => h j (by omega))
    obtain ⟨T2, h2⟩ := h (N+1) (Nat.le_refl _)
    refine ⟨T1 + T2, fun j hj t ht => ?_⟩
    by_cases hj' : j ≤ N
    · exact h1 j hj' t (by omega)
    · rw [show j = N + 1 by omega]; exact h2 t (by omega)

/-- Combinational core of deadlock freedom: in any state of the pipeline,
the source may move, or some C-element is excited, or the sink may move. -/
theorem deadlock_free (n : Nat) (v : Nat → Bool)
    (hsrc : v 0 ≠ v 1)
    (hcel : ∀ j, j < n → celN (v j) (v (j+2)) (v (j+1)) = v (j+1))
    (hsnk : v (n + 1) = v n) : False := by
  have : ∀ j, j ≤ n → v j ≠ v (j+1) := by
    intro j
    induction j with
    | zero => intro _; exact hsrc
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have h2 := hcel j (by omega)
      rw [celN_eq] at h2
      revert h1 h2
      cases v j <;> cases v (j+1) <;> cases v (j+2) <;> simp
  exact this n (Nat.le_refl _) hsnk.symm

/-- A signal that changes infinitely often falls infinitely often. -/
theorem fall_between (s : Trace) (a : Nat) : ∀ k, s a = true → s (a + k) = false →
    ∃ u, a ≤ u ∧ u < a + k ∧ fallB s u = true := by
  intro k
  induction k with
  | zero => intro h1 h2; rw [Nat.add_zero, h1] at h2; cases h2
  | succ k ih =>
    intro h1 h2
    cases hk : s (a + k)
    · obtain ⟨u, hu1, hu2, hu3⟩ := ih h1 hk
      exact ⟨u, hu1, by omega, hu3⟩
    · refine ⟨a + k, by omega, by omega, ?_⟩
      rw [← Nat.add_assoc] at h2; simp [fallB, hk, h2]

theorem falls_unbounded (s : Trace) (h : ∀ T, ∃ t, T ≤ t ∧ s (t+1) ≠ s t) :
    ∀ K, ∃ t, K ≤ cnt (fallB s) t := by
  have fall_after : ∀ T, ∃ u, T ≤ u ∧ fallB s u = true := by
    intro T
    obtain ⟨t1, h1, c1⟩ := h T
    cases hs : s t1
    · -- rise at t1; find a later change, which ends in a fall
      have hs1 : s (t1+1) = true := by cases h' : s (t1+1) <;> simp_all
      obtain ⟨t2, h2, c2⟩ := h (t1 + 1)
      cases hs2 : s t2
      · obtain ⟨u, hu1, _, hu3⟩ := fall_between s (t1+1) (t2 - (t1+1)) hs1
          (by rw [show t1 + 1 + (t2 - (t1 + 1)) = t2 by omega]; exact hs2)
        exact ⟨u, by omega, hu3⟩
      · have : s (t2+1) = false := by cases h' : s (t2+1) <;> simp_all
        exact ⟨t2, by omega, by simp [fallB, hs2, this]⟩
    · have : s (t1+1) = false := by cases h' : s (t1+1) <;> simp_all
      exact ⟨t1, h1, by simp [fallB, hs, this]⟩
  intro K
  induction K with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ K ih =>
    obtain ⟨t, ht⟩ := ih
    obtain ⟨u, hu1, hu2⟩ := fall_after t
    refine ⟨u + 1, ?_⟩
    have := cnt_mono (fallB s) hu1
    rw [cnt_succ_of hu2]; omega

/-- **Liveness of the Muller pipeline.** Under the safety model of
`muller_pipeline` (no data hypotheses needed) plus `H_SRC_LIVE`, `H_SNK_LIVE`
and `H_CEL_FAIR`, every link's ack changes infinitely often and the sink
receives unboundedly many tokens. -/
theorem muller_live {m h n : Nat} {ch : Nat → Chan}
    (H_STAGE : ∀ j, j < n → MullerStage m h (ch j) (ch (j + 1)))
    (srcInit : (ch 0).req 0 = false) (snkInit : (ch n).ack 0 = false)
    (src : ∀ t, (∀ s, s < t → Rules (ch 0) s) → SendStep (ch 0) t)
    (snk : ∀ t, (∀ s, s < t → Rules (ch n) s) → RecvStep (ch n) t)
    (H_SRC_LIVE : ∀ t, (ch 0).req t = (ch 0).ack t → ∃ s, t ≤ s ∧ (ch 0).req (s+1) ≠ (ch 0).req s)
    (H_SNK_LIVE : ∀ t, (ch n).ack t ≠ (ch n).req t → ∃ s, t ≤ s ∧ (ch n).ack (s+1) ≠ (ch n).ack s)
    (H_CEL_FAIR : ∀ j, j < n → ∀ t,
      celN ((ch j).req t) ((ch (j+1)).ack t) ((ch j).ack t) ≠ (ch j).ack t →
      ∃ s, t ≤ s ∧ (ch j).ack (s+1) ≠ (ch j).ack s) :
    (∀ j, j ≤ n → ∀ T, ∃ t, T ≤ t ∧ (ch j).ack (t+1) ≠ (ch j).ack t) ∧
    (∀ K, ∃ t, K ≤ cnt (fallB (ch n).ack) t) := by
  have P : Pipeline m h n ch :=
    { stage := fun j hj => muller_stageSpec (H_STAGE j hj)
      srcInit, snkInit, src, snk }
  have hp := pipeline_protocol P
  -- link j has req = sig j, ack = sig (j+1)
  have hreq : ∀ j, j ≤ n → (ch j).req = sig ch j := by
    intro j hj; cases j with
    | zero => rfl
    | succ j => exact funext (H_STAGE j (by omega)).H_NODE
  -- one stopped wire stops all wires
  have spread : ∀ i, i ≤ n + 1 → Stops (sig ch i) → ∀ j, j ≤ n + 1 → Stops (sig ch j) := by
    intro i hi hs
    have up : ∀ k, i + k ≤ n + 1 → Stops (sig ch (i + k)) := by
      intro k; induction k with
      | zero => intro _; exact hs
      | succ k ih =>
        intro hk
        obtain ⟨T, hT⟩ := ih (by omega)
        rw [← hreq (i+k) (by omega)] at hT
        exact ack_stops (hp (i + k) (by omega)) T hT
    have down : ∀ k, k ≤ i → Stops (sig ch (i - k)) := by
      intro k; induction k with
      | zero => intro _; exact hs
      | succ k ih =>
        intro hk
        obtain ⟨T, hT⟩ := ih (by omega)
        have e : i - k = (i - (k+1)) + 1 := by omega
        rw [e] at hT
        have := req_stops (hp (i - (k+1)) (by omega)) T hT
        rwa [hreq (i - (k+1)) (by omega)] at this
    intro j hj
    by_cases hij : i ≤ j
    · have := up (j - i) (by omega); rwa [show i + (j - i) = j by omega] at this
    · have := down (i - j) (by omega); rwa [show i - (i - j) = j by omega] at this
  -- no wire stops
  have nostop : ∀ i, i ≤ n + 1 → ¬ Stops (sig ch i) := by
    intro i hi hs
    obtain ⟨T, hT⟩ := stops_common (sig ch) (n+1) (spread i hi hs)
    have const : ∀ j, j ≤ n + 1 → ∀ t, T ≤ t → sig ch j t = sig ch j T := by
      intro j hj t ht
      have : ∀ k, sig ch j (T + k) = sig ch j T := by
        intro k; induction k with
        | zero => rfl
        | succ k ih => rw [← Nat.add_assoc, hT j hj (T+k) (by omega), ih]
      have := this (t - T); rwa [show T + (t - T) = t by omega] at this
    have nomove : ∀ j, j ≤ n + 1 → ∀ s, T ≤ s → sig ch j (s+1) = sig ch j s := by
      intro j hj s hs; rw [const j hj (s+1) (by omega), const j hj s hs]
    apply deadlock_free n (fun j => sig ch j T)
    · intro he
      obtain ⟨s, hs, hc⟩ := H_SRC_LIVE T he
      exact hc (nomove 0 (by omega) s hs)
    · intro j hj
      apply Classical.byContradiction; intro hne
      have hr : (ch j).req T = sig ch j T := by rw [hreq j (by omega)]
      obtain ⟨s, hs, hc⟩ := H_CEL_FAIR j hj T (by
        rw [hr]; exact hne)
      exact hc (nomove (j+1) (by omega) s hs)
    · apply Classical.byContradiction; intro hne
      have hr : (ch n).req T = sig ch n T := by rw [hreq n (Nat.le_refl _)]
      obtain ⟨s, hs, hc⟩ := H_SNK_LIVE T (by rw [hr]; exact hne)
      exact hc (nomove (n+1) (Nat.le_refl _) s hs)
  have inf : ∀ j, j ≤ n → ∀ T, ∃ t, T ≤ t ∧ (ch j).ack (t+1) ≠ (ch j).ack t := by
    intro j hj T
    apply Classical.byContradiction; intro hno
    apply nostop (j+1) (by omega)
    refine ⟨T, fun t ht => ?_⟩
    apply Classical.byContradiction; intro hc
    exact hno ⟨t, ht, hc⟩
  exact ⟨inf, falls_unbounded _ (inf n (Nat.le_refl _))⟩

end Formal.Net.Handshake
