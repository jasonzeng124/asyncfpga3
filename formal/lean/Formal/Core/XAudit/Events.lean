import Formal.Core.Trace.Discrete

/-!
# Formal.Core.XAudit.Events — an event-count (counter) domain for Muller networks

Probe A-events. See `formal/notes/A-events.md`.

## Why

`XSim` abstracts a wire by a `K3` value per time step (an X-window). It is
sound for the non-FIFO window channel, and on a free-running ring it loses
the phase after about one lap (A-xaudit, ring3): every X window is wider than
the one before it, and once the X window of a C-element's own feedback pin
overlaps the X window of its neighbour's next request, the C-element's value
is X and the loop latches it.

The loss is in the abstraction, not in the circuit. What a correct
self-timed loop relies on is *relative* timing between causally related
events (my own feedback arrives before my neighbour's answer to my output)
and that is a relation between two events, which per-time values cannot
express however the windows are drawn.

## The domain

Each node `c j` of a Muller network (every gate a LUT C-element
`maj(a, ¬b, q)` with its own routed feedback `q` and a reset pin) is
abstracted by a **count**: a monotone function `M t j : ℕ` such that

    c j t = ph (v j) (M t j)          (value = reset value, flipped M times)

The counts are defined (`M`) by the counter (min-plus) recursion of a timed
marked graph, but over the *concrete* delay warps of the behaviour:

    M t j = if rst pin of j is high at F j t then 0
            else min over the two input pins p of
                 M (G j p (F j t)) (src j p) + off j p

where `F j` is the LUT's warp and `G j p` the route warp of pin `p`.
Because a transport channel is a monotone warp, composing counts with warps
keeps them monotone: this is exactly the FIFO fact that the window channel
lacks. A count can jump by more than one in a step (a pulse annihilated by a
warp); nothing below assumes it cannot.

## Main theorem

`safe`: in EVERY behaviour of the network (any power-up, any delays of any
LUT and route as monotone warps inside its band) the node values are
`ph (v j) (M t j)` at every time — so no node ever glitches or holds a value
other than the one the counter system dictates — provided

* `Pairing`: every input pin of stage `j` reads a neighbour `k` that reads
  `j` back through one of its own pins, with offsets summing to 1 (the
  Muller handshake structure; decidable, true for rings and pipes), and
* `Race`: own feedback is no slower than the fastest round trip through any
  neighbour: `hiQ j ≤ loG j p + loF k + loG k p'` (route, neighbour LUT,
  route back). This is the relative-timing assumption A-xaudit found for the
  LUT C-element, now as an explicit, checked hypothesis,

plus the reset pins falling once (`r j 0 = true`, antitone).

The proof is a strong induction on time, with no case analysis on the
network: the only facts used are `M` monotone (`M_mono`), the min-plus upper
bounds through the neighbour (`M_le_pin`), and a four-case lemma on the
majority function (`maj_ph`).
-/

namespace Formal.Core.XAudit.Events

open Formal.Core.TraceDiscrete (Sig Warp)

/-! ## Phases -/

/-- The value of a node with reset value `v` after `m` flips. -/
def ph (v : Bool) (m : Nat) : Bool := if m % 2 = 0 then v else !v

theorem ph_zero (v : Bool) : ph v 0 = v := by simp [ph]

theorem ph_succ (v : Bool) (m : Nat) : ph v (m + 1) = !ph v m := by
  unfold ph
  by_cases h : m % 2 = 0
  · have : ¬ (m + 1) % 2 = 0 := by omega
    simp [h, this]
  · have : (m + 1) % 2 = 0 := by omega
    simp [h, this]

theorem ph_not (v : Bool) (m : Nat) : (!ph v m) = ph (!v) m := by
  unfold ph; split <;> simp

/-- The offset that re-expresses a source phase in the target's reset value. -/
def offB (vs vj : Bool) : Nat := if vs = vj then 0 else 1

theorem ph_off (vs vj : Bool) (m : Nat) : ph vs m = ph vj (m + offB vs vj) := by
  unfold offB
  by_cases h : vs = vj
  · simp [h]
  · simp only [h, ite_false, ph_succ]
    have : vs = !vj := by cases vs <;> cases vj <;> simp_all
    rw [this, ph_not]

theorem offB_le (vs vj : Bool) : offB vs vj ≤ 1 := by unfold offB; split <;> omega

/-- Majority (the settled function of `bd_c2n` with its inputs `a`, `¬b`, `q`). -/
def maj (a b q : Bool) : Bool := (a && b) || (a && q) || (b && q)

/-- **The C-element as a counter.** If the feedback count `mq` is no ahead of
either input phase and at most one behind each, the majority is the phase of
the minimum: the element has fired exactly `min pa pb` times. -/
theorem maj_ph (v : Bool) (pa pb mq : Nat) (h1 : mq ≤ pa) (h2 : mq ≤ pb)
    (h3 : pa ≤ mq + 1) (h4 : pb ≤ mq + 1) :
    maj (ph v pa) (ph v pb) (ph v mq) = ph v (min pa pb) := by
  have hm : maj (ph v pa) (ph v pb) (ph v mq) = maj (ph v pa) (ph v pb) (ph v mq) := rfl
  rcases Nat.lt_or_ge mq pa with ha | ha <;> rcases Nat.lt_or_ge mq pb with hb | hb
  · rw [show pa = mq + 1 by omega, show pb = mq + 1 by omega, Nat.min_self, ph_succ]
    generalize ph v mq = y; cases y <;> rfl
  · rw [show pa = mq + 1 by omega, show pb = mq by omega, show min (mq + 1) mq = mq by omega,
      ph_succ]
    generalize ph v mq = y; cases y <;> rfl
  · rw [show pa = mq by omega, show pb = mq + 1 by omega, show min mq (mq + 1) = mq by omega,
      ph_succ]
    generalize ph v mq = y; cases y <;> rfl
  · rw [show pa = mq by omega, show pb = mq by omega, Nat.min_self]
    generalize ph v mq = y; cases y <;> rfl

/-! ## Muller networks -/

/-- A Muller network of `N` C-element stages. Pin `false` is the LUT's `a`
input (I0, taken positively), pin `true` is its `b` input (I1, taken
negated); the feedback `q` (I2) and the reset pin (I3) are implicit. -/
structure MNet (N : Nat) where
  /-- reset value of the stage (`bd_c2n`: false, `bd_c2n_set`: true) -/
  v : Fin N → Bool
  /-- the stage read by input pin `p` -/
  src : Fin N → Bool → Fin N

namespace MNet
variable {N : Nat} (net : MNet N)

/-- Phase offset of pin `p` of stage `j`: the pin value is `v (src j p)`
flipped by the source count, negated for `p = true`. -/
def off (j : Fin N) (p : Bool) : Nat := offB (net.v (net.src j p) ^^ p) (net.v j)

theorem off_le (j : Fin N) (p : Bool) : net.off j p ≤ 1 := offB_le _ _

/-- **Pairing** (the handshake structure, decidable): every pin of `j` reads
a stage `k` that has a pin reading `j` back, and the two offsets sum to 1. -/
def Pairing : Prop :=
  ∀ j p, ∃ p', net.src (net.src j p) p' = j ∧ net.off j p + net.off (net.src j p) p' = 1

instance : Decidable net.Pairing := by unfold Pairing; exact inferInstance

/-- The settled LUT function of a stage: reset value under reset, else
`maj(a, ¬b, q)`. -/
def lutF (j : Fin N) (a b q rst : Bool) : Bool := if rst then net.v j else maj a (!b) q

end MNet

/-- Delay bands of a Muller network (in steps). -/
structure Bands (N : Nat) where
  loF : Fin N → Nat
  hiF : Fin N → Nat
  loG : Fin N → Bool → Nat
  hiG : Fin N → Bool → Nat
  loQ : Fin N → Nat
  hiQ : Fin N → Nat

/-- **Race** (relative timing, decidable): own feedback no slower than the
fastest round trip through a neighbour that reads this stage back. -/
def Race {N : Nat} (net : MNet N) (b : Bands N) : Prop :=
  ∀ j p p', net.src (net.src j p) p' = j →
    b.hiQ j ≤ b.loG j p + b.loF (net.src j p) + b.loG (net.src j p) p'

instance {N : Nat} (net : MNet N) (b : Bands N) : Decidable (Race net b) := by
  unfold Race; exact inferInstance

/-- A concrete behaviour of the gate-level network: node signals `c`, routed
input pins `pin`, routed own feedback `q`, routed reset pin `r`, and the
transport warps that relate them (`F` LUT, `G` input routes, `Q` feedback).
Every channel is a Discrete transport (monotone warp) inside its band. -/
structure Beh {N : Nat} (net : MNet N) (b : Bands N) where
  c : Fin N → Sig
  pin : Fin N → Bool → Sig
  q : Fin N → Sig
  r : Fin N → Sig
  F : Fin N → Nat → Nat
  G : Fin N → Bool → Nat → Nat
  Q : Fin N → Nat → Nat
  wF : ∀ j, Warp (b.loF j) (b.hiF j) (F j)
  wG : ∀ j p, Warp (b.loG j p) (b.hiG j p) (G j p)
  wQ : ∀ j, Warp (b.loQ j) (b.hiQ j) (Q j)
  /-- causality: every LUT, route and feedback has a delay of at least one step -/
  loF1 : ∀ j, 1 ≤ b.loF j
  loG1 : ∀ j p, 1 ≤ b.loG j p
  loQ1 : ∀ j, 1 ≤ b.loQ j
  /-- the LUT: its settled function of the pins, through the warp `F j` -/
  hc : ∀ j t, c j t = net.lutF j (pin j false (F j t)) (pin j true (F j t)) (q j (F j t)) (r j (F j t))
  hpin : ∀ j p t, pin j p t = c (net.src j p) (G j p t)
  hq : ∀ j t, q j t = c j (Q j t)
  /-- reset: high at time 0, falls at most once -/
  r0 : ∀ j, r j 0 = true
  ranti : ∀ j a b, a ≤ b → r j b = true → r j a = true

namespace Beh
variable {N : Nat} {net : MNet N} {b : Bands N} (x : Beh net b)

theorem F_lt (j : Fin N) (t : Nat) (ht : 1 ≤ t) : x.F j t < t := by
  have := (x.wF j).le_late t; have := x.loF1 j; omega

theorem G_lt (j : Fin N) (p : Bool) (t : Nat) (ht : 1 ≤ t) : x.G j p t < t := by
  have := (x.wG j p).le_late t; have := x.loG1 j p; omega

theorem Q_lt (j : Fin N) (t : Nat) (ht : 1 ≤ t) : x.Q j t < t := by
  have := (x.wQ j).le_late t; have := x.loQ1 j; omega

theorem F_zero (j : Fin N) : x.F j 0 = 0 := by have := (x.wF j).le_late 0; omega

/-- **The counts** of a behaviour: the counter recursion of the network over
the behaviour's own warps (well founded: every warp is strictly causal). -/
def M (t : Nat) (j : Fin N) : Nat :=
  if h : x.F j t < t then
    if x.r j (x.F j t) then 0 else
      min (if h0 : x.G j false (x.F j t) < x.F j t then
             M (x.G j false (x.F j t)) (net.src j false) + net.off j false else 0)
          (if h1 : x.G j true (x.F j t) < x.F j t then
             M (x.G j true (x.F j t)) (net.src j true) + net.off j true else 0)
  else 0
termination_by t

/-- Phase count of pin `p` of stage `j` at LUT sample time `s`. -/
def P (j : Fin N) (p : Bool) (s : Nat) : Nat := x.M (x.G j p s) (net.src j p) + net.off j p

/-- Count of the LUT function (before its output delay) at time `s`. -/
def E (j : Fin N) (s : Nat) : Nat := if x.r j s then 0 else min (x.P j false s) (x.P j true s)

theorem M_eq (t : Nat) (j : Fin N) : x.M t j = x.E j (x.F j t) := by
  rw [M]
  by_cases ht : 1 ≤ t
  · have hF := x.F_lt j t ht
    rw [dif_pos hF]
    unfold E
    by_cases hr : x.r j (x.F j t) = true
    · simp [hr]
    · have hs : 1 ≤ x.F j t := by
        rcases Nat.eq_zero_or_pos (x.F j t) with h | h
        · rw [h] at hr; exact absurd (x.r0 j) hr
        · exact h
      simp only [hr, ite_false, Bool.false_eq_true]
      rw [dif_pos (x.G_lt j false _ hs), dif_pos (x.G_lt j true _ hs)]
      rfl
  · have : t = 0 := by omega
    subst this
    rw [dif_neg (by rw [x.F_zero]; exact Nat.lt_irrefl 0)]
    unfold E; rw [x.F_zero, x.r0]; simp

theorem E_zero (j : Fin N) : x.E j 0 = 0 := by unfold E; rw [x.r0]; simp

/-- Counts are monotone in time (strong induction; uses only that every warp
is monotone and causal, and that reset falls once). -/
theorem M_mono : ∀ (n : Nat) (j : Fin N) (a : Nat), a ≤ n → x.M a j ≤ x.M n j := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro j a han
    rcases Nat.lt_or_ge a n with hlt | hge
    · -- compare through the unfolding
      have hn : 1 ≤ n := by omega
      rw [x.M_eq a j, x.M_eq n j]
      have hFa := (x.wF j).mono a n (Nat.le_of_lt hlt)
      have hFn := x.F_lt j n hn
      unfold E
      by_cases hrn : x.r j (x.F j n) = true
      · have := x.ranti j _ _ hFa hrn; simp [hrn, this]
      · by_cases hra : x.r j (x.F j a) = true
        · simp [hra]
        · simp only [hra, hrn, ite_false, Bool.false_eq_true]
          have key : ∀ p, x.P j p (x.F j a) ≤ x.P j p (x.F j n) := by
            intro p
            unfold P
            have hG := (x.wG j p).mono _ _ hFa
            have hs : 1 ≤ x.F j n := by
              rcases Nat.eq_zero_or_pos (x.F j n) with h | h
              · rw [h] at hrn; exact absurd (x.r0 j) hrn
              · exact h
            have hGn := x.G_lt j p _ hs
            have := ih (x.G j p (x.F j n)) (by omega) (net.src j p) _ hG
            omega
          have k0 := key false; have k1 := key true
          omega
    · have : a = n := by omega
      subst this; exact Nat.le_refl _

theorem E_mono (j : Fin N) (a s : Nat) (h : a ≤ s) : x.E j a ≤ x.E j s := by
  unfold E
  by_cases hrs : x.r j s = true
  · have := x.ranti j _ _ h hrs; simp [hrs, this]
  · by_cases hra : x.r j a = true
    · simp [hra]
    · simp only [hra, hrs, ite_false, Bool.false_eq_true]
      have key : ∀ p, x.P j p a ≤ x.P j p s := by
        intro p; unfold P
        have := x.M_mono (x.G j p s) (net.src j p) _ ((x.wG j p).mono _ _ h)
        omega
      have k0 := key false; have k1 := key true
      omega

/-- The count of a stage is bounded by the phase of each of its pins, read
through the stage's own LUT warp. -/
theorem M_le_pin (k : Fin N) (p' : Bool) (u : Nat) :
    x.M u k ≤ x.M (x.G k p' (x.F k u)) (net.src k p') + net.off k p' := by
  rw [x.M_eq]; unfold E P
  by_cases hr : x.r k (x.F k u) = true
  · simp [hr]
  · simp only [hr, ite_false, Bool.false_eq_true]
    cases p' <;> omega

/-- **Neighbour bound.** With `Pairing` and `Race`, the phase of every pin of
`j` at time `s` is at most one ahead of `j`'s own feedback count. -/
theorem pin_le_q (hP : net.Pairing) (hR : Race net b) (j : Fin N) (p : Bool) (s : Nat) :
    x.P j p s ≤ x.M (x.Q j s) j + 1 := by
  obtain ⟨p', hsrc, hoff⟩ := hP j p
  unfold P
  have h1 := x.M_le_pin (net.src j p) p' (x.G j p s)
  rw [hsrc] at h1
  have hrace := hR j p p' hsrc
  -- the round trip ends no later than the feedback sample
  have hle : x.G (net.src j p) p' (x.F (net.src j p) (x.G j p s)) ≤ x.Q j s := by
    have a1 := (x.wG j p).le_late s
    have a2 := (x.wF (net.src j p)).le_late (x.G j p s)
    have a3 := (x.wG (net.src j p) p').le_late (x.F (net.src j p) (x.G j p s))
    have a4 := (x.wQ j).early_le s
    omega
  have := x.M_mono (x.Q j s) j _ hle
  omega

/-- The feedback count is never ahead of the LUT's current count. -/
theorem q_le_E (j : Fin N) (s : Nat) : x.M (x.Q j s) j ≤ x.E j s := by
  rw [x.M_eq]
  apply x.E_mono
  have a1 := (x.wF j).le_late (x.Q j s)
  have a2 := (x.wQ j).le_late s
  omega

/-- **Soundness of the counter domain.** Every node of every behaviour equals
its reset value flipped `M t j` times, at every time. -/
theorem safe (hP : net.Pairing) (hR : Race net b) :
    ∀ t (j : Fin N), x.c j t = ph (net.v j) (x.M t j) := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
    intro j
    rw [x.hc j t, x.M_eq t j]
    unfold MNet.lutF E
    by_cases hr : x.r j (x.F j t) = true
    · simp [hr, ph_zero]
    · simp only [hr, ite_false, Bool.false_eq_true]
      have hs1 : 1 ≤ x.F j t := by
        rcases Nat.eq_zero_or_pos (x.F j t) with h | h
        · rw [h] at hr; exact absurd (x.r0 j) hr
        · exact h
      have ht1 : 1 ≤ t := by
        rcases Nat.eq_zero_or_pos t with h | h
        · rw [h, x.F_zero] at hs1; omega
        · exact h
      have hst : x.F j t < t := x.F_lt j t ht1
      generalize x.F j t = s at hr hs1 hst ⊢
      -- pins and feedback, by the induction hypothesis
      have hpin : ∀ p, x.pin j p s = ph (net.v (net.src j p)) (x.M (x.G j p s) (net.src j p)) := by
        intro p
        rw [x.hpin j p s]
        exact ih _ (Nat.lt_trans (x.G_lt j p s hs1) hst) _
      have hq : x.q j s = ph (net.v j) (x.M (x.Q j s) j) := by
        rw [x.hq j s]; exact ih _ (Nat.lt_trans (x.Q_lt j s hs1) hst) _
      have pA : x.pin j false s = ph (net.v j) (x.P j false s) := by
        rw [hpin false]; unfold P MNet.off
        rw [ph_off _ (net.v j)]; simp
      have pB : (!x.pin j true s) = ph (net.v j) (x.P j true s) := by
        rw [hpin true, ph_not]; unfold P MNet.off
        rw [ph_off _ (net.v j)]; simp
      rw [pA, pB, hq]
      have e1 := x.q_le_E j s
      unfold E at e1
      simp only [hr, ite_false, Bool.false_eq_true] at e1
      apply maj_ph
      · omega
      · omega
      · exact x.pin_le_q hP hR j false s
      · exact x.pin_le_q hP hR j true s

end Beh

end Formal.Core.XAudit.Events
