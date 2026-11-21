import Formal.Net.Bridge
import Formal.Net.OpsGen

/-!
# Probe C-8n (O5): circuit liveness with bounded delays, and a latency bound

The Ops SI models never force a gate to fire: every gate there is an unbounded
inertial delay, so the all-quiet run satisfies every gate model (C-8l, O5
obstacle 1). This file adds the upper bound, as Bridge (C-8d) and MullerTimed
(C-8g) do: a timed trace `x` of a `Bridge.Net` in which every gate is an
inertial channel `[lo i, hi i]` (`Bridge.Timed`; H_BOUNDED_DELAY in its
inertial form, `lo i ≥ 1`), and proves a LATENCY bound.

## Generic part (any network)

* `cause1`: an inertial gate changes only to its excitation one tick earlier
  (this is exactly the Ops models' SI field, so every timed trace is also an
  Ops trace).
* `hold`: a node whose excitation stays `v` keeps the value `v`.
* `reach_step`: if, from `t` on, gate `g` is excited towards `v` for as long as
  it has not shown `v` (since `T`), it shows `v` by `t + hi g`. Only the
  `settle` half of the channel is used.
* `quiet`: a region `Q` of nodes that are all 0 at `T`, and whose excitations are
  0 whenever `Q` and a guard node `g` are 0, stays 0 as long as `g` does
  (nothing downstream of the token front can move before the front arrives).
* `chain`: event `j` reached by `t` implies event `j+1` reached by
  `t + d (j+1)`; so event `m` by `t + Σ d`.

## The pipeline (any number `n ≥ 1` of link stages)

`pipe n`: source (generated `bd_src` LUT1, `req = ¬ack`), `n` link controllers
(the generated `bd_link` LUT6 `ctl.u.u` = B's `ctlB`, `pipe_ctl_gen`), every
request and acknowledge ROUTE a buffer gate of its own (delay-insensitive
wires: each with its own bounds, H_WIRE_DI made timed), and the sink
(`bd_snk`: `ack` is a wire copy of `req`). Node ids: `r k = 3k` (request into
stage `k`; `r 0` is the source, `r n` the request offered to the sink),
`c k = 3k+1` (controller of stage `k`, `k < n`), `a k = 3k+2` (acknowledge back
to the sender of stage `k`; `a n` is the sink's). Id order is token order.

`pipe_latency`: from an EMPTY state at `T` (every node 0: reset), the sink's
acknowledge rises by

    T + hi(r 0) + Σ_{k<n} (hi(c k) + hi(r (k+1))) + hi(a n)

and the request offered at the input (`r 0`) at `t0 ≥ T` is delivered
(`a n` rises) by `t0 + Σ_{k<n} (hi(c k) + hi(r(k+1))) + hi(a n)`. No fairness
assumption: the upper bounds alone force progress. Hypotheses: H_BOUNDED_DELAY
(inertial, per gate and per route), H_FB_SETTLED (the controller reads its own
node: by O4 this is `FbFirst`, B's C2), H_EMPTY (the state at `T`).
`pipe_latency_nonvacuous`: the unit-delay run from reset satisfies every
hypothesis, so the bound is not vacuous.
-/

namespace Formal.Net.Ops.TimedLive
open Formal.Net Formal.Net.Bridge

variable {N : Bridge.Net} {lo hi : Nat → Nat} {x : Nat → State}

/-! ## 1. Generic lemmas -/

/-- An inertial gate changes only to its excitation one tick earlier. -/
theorem cause1 (hx : Timed N lo hi x) {i t : Nat} (hi' : i < N.n) (h : x (t + 1) i ≠ x t i) :
    x (t + 1) i = N.f i (x t) := by
  have g := hx.gate i hi'
  obtain ⟨_, hw⟩ := g.cause t (fun e => h e.symm)
  have := g.lo_pos
  exact (hw t (by omega) (Nat.le_refl _)).symm

/-- A node keeps `v` while its excitation is `v`. -/
theorem hold (hx : Timed N lo hi x) {i a : Nat} {v : Bool} (hi' : i < N.n) (ha : x a i = v) :
    ∀ b, a ≤ b → (∀ w, a ≤ w → w < b → x w i = v → N.f i (x w) = v) → x b i = v := by
  intro b hab hexc
  induction b with
  | zero => have : a = 0 := by omega
            subst this; exact ha
  | succ b ih =>
    rcases Nat.eq_or_lt_of_le hab with e | hlt
    · rw [← e]; exact ha
    · have hb := ih (by omega) (fun w h1 h2 => hexc w h1 (by omega))
      by_cases hc : x (b + 1) i = x b i
      · rw [hc, hb]
      · rw [cause1 hx hi' hc]; exact hexc b (by omega) (by omega) hb

/-- First rise: a Bool trace that is `false` at `T` and `true` at `w` rises somewhere in `[T, w)`. -/
theorem first_rise (s : Nat → Bool) {T w : Nat} (h0 : s T = false) (h1 : s w = true) (hTw : T ≤ w) :
    ∃ r, T ≤ r ∧ r < w ∧ s r = false ∧ s (r + 1) = true := by
  induction w with
  | zero => have : T = 0 := by omega
            subst this; rw [h0] at h1; cases h1
  | succ w ih =>
    by_cases hw : s w = true
    · rcases Nat.eq_or_lt_of_le hTw with e | hlt
      · rw [← e, h0] at h1; cases h1
      · obtain ⟨r, a, b, c, d⟩ := ih hw (by omega)
        exact ⟨r, a, by omega, c, d⟩
    · rcases Nat.eq_or_lt_of_le hTw with e | hlt
      · rw [← e, h0] at h1; cases h1
      · exact ⟨w, by omega, by omega, by simpa using hw, h1⟩

/-- **One causal step.** If, on `[t, t + hi g]`, gate `g` is excited towards `v`
whenever it has not shown `v` since `T`, then it shows `v` by `t + hi g`. -/
theorem reach_step (hx : Timed N lo hi x) {g T t : Nat} {v : Bool} (hg : g < N.n) (hT : T ≤ t)
    (hexc : ∀ u, t ≤ u → u ≤ t + hi g → (∀ w, T ≤ w → w ≤ u → x w g ≠ v) → N.f g (x u) = v) :
    ∃ w, T ≤ w ∧ w ≤ t + hi g ∧ x w g = v := by
  apply Classical.byContradiction
  intro hno
  have nr : ∀ w, T ≤ w → w ≤ t + hi g → x w g ≠ v := fun w h1 h2 e => hno ⟨w, h1, h2, e⟩
  have ev : ∀ u, t ≤ u → u ≤ t + hi g → N.f g (x u) = v :=
    fun u h1 h2 => hexc u h1 h2 (fun w a b => nr w a (by omega))
  have s := (hx.gate g hg).settle (t + hi g) (by omega) (by
    intro u h1 h2
    show N.f g (x u) = N.f g (x (t + hi g - hi g))
    rw [ev u (by omega) h2, ev _ (by omega) (by omega)])
  exact nr (t + hi g) (by omega) (Nat.le_refl _) (s.trans (ev _ (by omega) (Nat.le_refl _)))

/-- **Quiet region.** -/
theorem quiet (hx : Timed N lo hi x) {g T u : Nat} (Q : Nat → Prop) (hQn : ∀ i, Q i → i < N.n)
    (hcl : ∀ w, (∀ i, Q i → x w i = false) → x w g = false → ∀ i, Q i → N.f i (x w) = false)
    (h0 : ∀ i, Q i → x T i = false) (hg : ∀ w, T ≤ w → w ≤ u → x w g = false) :
    ∀ w, T ≤ w → w ≤ u → ∀ i, Q i → x w i = false := by
  intro w hT hu
  induction w with
  | zero => have : T = 0 := by omega
            subst this; exact h0
  | succ w ih =>
    rcases Nat.eq_or_lt_of_le hT with e | hlt
    · rw [← e]; exact h0
    · have hw := ih (by omega) (by omega)
      intro i hq
      by_cases hc : x (w + 1) i = x w i
      · rw [hc]; exact hw i hq
      · rw [cause1 hx (hQn i hq) hc]
        exact hcl w hw (hg w (by omega) (by omega)) i hq

/-- Sum of the step delays `d 1 + … + d m`. -/
def sumD (d : Nat → Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => sumD d m + d (m + 1)

/-- **Chain.** -/
theorem chain {R : Nat → Nat → Prop} (d : Nat → Nat) (m : Nat)
    (hstep : ∀ j t, j < m → R j t → R (j + 1) (t + d (j + 1))) :
    ∀ t, R 0 t → R m (t + sumD d m) := by
  induction m with
  | zero => intro t h; simpa [sumD] using h
  | succ m ih =>
    intro t h
    have h1 := ih (fun j t' hj hr => hstep j t' (by omega) hr) t h
    have := hstep m (t + sumD d m) (by omega) h1
    simpa [sumD, Nat.add_assoc] using this

/-! ## 2. The pipeline -/

open Formal.Cells.LinkHandshake (ctlB)

/-- Excitation of node `i` (ids as in the module doc). -/
def pf (n i : Nat) (s : State) : Bool :=
  if i % 3 = 0 then (if i = 0 then !s 2 else s (i - 2))
  else if i % 3 = 1 then (if i / 3 < n then ctlB (s (i - 1)) (s (i + 4)) (s i) false else s i)
  else (if i / 3 < n then s (i - 1) else s (3 * n))

def pipe (n : Nat) : Bridge.Net := ⟨3 * n + 3, pf n⟩

/-- The gates are the generated cells: the controller of stage `k` is the
generated `bd_link` LUT (`Gen.linkF`), the source is the generated `bd_src` LUT. -/
theorem pipe_ctl_gen (n k : Nat) (hk : k < n) (s : State) :
    pf n (3 * k + 1) s = Gen.linkF (s (3 * k), s (3 * k + 5)) (s (3 * k + 1)) := by
  have h1 : (3 * k + 1) % 3 = 1 := by omega
  have h2 : (3 * k + 1) / 3 = k := by omega
  have h0 : (3 * k + 1) % 3 ≠ 0 := by omega
  simp only [pf, h0, h1, h2, hk, ite_true, ite_false, Gen.link_gate]
  rfl

theorem pipe_src_gen (n : Nat) (s : State) :
    pf n 0 s = Gen.genF Formal.Gen.Cells.bd_src_W2 "u" .O ["ack"] [s 2] := by
  rw [Gen.src_gate]; rfl

theorem ctlB_ff : ctlB false false false false = false := by decide
theorem ctlB_hold (r : Bool) : ctlB r false true false = true := by cases r <;> decide
theorem ctlB_go (q : Bool) : ctlB true false q false = true := by cases q <;> decide

/-- Closure: if every node from `g` up is 0, every excitation above `g` is 0
(`g` is a request or controller node, `g ≤ 3n`). -/
theorem pipe_closed (n g : Nat) (hg2 : g % 3 ≠ 2) (hgn : g ≤ 3 * n) (s : State)
    (hz : ∀ j, g ≤ j → j < 3 * n + 3 → s j = false) :
    ∀ i, g < i → i < 3 * n + 3 → pf n i s = false := by
  intro i h1 h2
  unfold pf
  by_cases a0 : i % 3 = 0
  · simp only [a0, ite_true]
    have : i ≠ 0 := by omega
    simp only [this, ite_false]
    exact hz _ (by omega) (by omega)
  · simp only [a0, ite_false]
    by_cases a1 : i % 3 = 1
    · simp only [a1, ite_true]
      by_cases hk : i / 3 < n
      · simp only [hk, ite_true]
        rw [hz (i - 1) (by omega) (by omega), hz (i + 4) (by omega) (by omega), hz i (by omega) h2]
        exact ctlB_ff
      · simp only [hk, ite_false]; exact hz i (by omega) h2
    · simp only [a1, ite_false]
      by_cases hk : i / 3 < n
      · simp only [hk, ite_true]; exact hz _ (by omega) (by omega)
      · simp only [hk, ite_false]; exact hz _ (by omega) (by omega)

/-- Node `g` shown `true` at some time in `[T, u]`. -/
def Rch (x : Nat → State) (T g u : Nat) : Prop := ∃ w, T ≤ w ∧ w ≤ u ∧ x w g = true

theorem rch_mono {x : Nat → State} {T g u u' : Nat} (h : u ≤ u') (r : Rch x T g u) : Rch x T g u' :=
  let ⟨w, a, b, c⟩ := r; ⟨w, a, by omega, c⟩

/-- H_EMPTY at `T`: every node except possibly the source request is 0. -/
def Empty (n : Nat) (x : Nat → State) (T : Nat) : Prop := ∀ i, 1 ≤ i → i < 3 * n + 3 → x T i = false

section pipeline
variable {n : Nat} {T : Nat}

/-- The region above a not-yet-reached front node `g` stays quiet. -/
theorem pipe_quiet (hx : Timed (pipe n) lo hi x) (hE : Empty n x T) {g u : Nat}
    (hg2 : g % 3 ≠ 2) (hgn : g ≤ 3 * n) (hnr : ∀ w, T ≤ w → w ≤ u → x w g ≠ true) :
    ∀ w, T ≤ w → w ≤ u → ∀ i, g < i → i < 3 * n + 3 → x w i = false := by
  have hgz : ∀ w, T ≤ w → w ≤ u → x w g = false := fun w a b => by simpa using hnr w a b
  have := quiet (N := pipe n) hx (g := g) (T := T) (u := u) (fun i => g < i ∧ i < 3 * n + 3)
    (fun i h => h.2)
    (fun w hw hgw i hq => pipe_closed n g hg2 hgn (x w) (fun j h1 h2 => by
        rcases Nat.eq_or_lt_of_le h1 with e | e
        · rw [← e]; exact hgw
        · exact hw j ⟨e, h2⟩) i hq.1 hq.2)
    (fun i h => hE i (by omega) h.2) hgz
  exact fun w a b i h1 h2 => this w a b i ⟨h1, h2⟩

/-- A controller `c k` that is 1 at `w1` stays 1 up to `u` while `a (k+1)` is 0. -/
theorem ctl_stays (hx : Timed (pipe n) lo hi x) {k w1 u : Nat} (hk : k < n)
    (h1 : x w1 (3 * k + 1) = true) (hu : w1 ≤ u)
    (hz : ∀ w, w1 ≤ w → w < u → x w (3 * k + 5) = false) : x u (3 * k + 1) = true := by
  refine hold hx (show 3 * k + 1 < 3 * n + 3 by omega) h1 u hu (fun w a b hq => ?_)
  show pf n (3 * k + 1) (x w) = true
  have e1 : (3 * k + 1) % 3 = 1 := by omega
  have e2 : (3 * k + 1) / 3 = k := by omega
  have e0 : (3 * k + 1) % 3 ≠ 0 := by omega
  simp only [pf, e0, e1, e2, hk, ite_true, ite_false, Nat.one_ne_zero]
  rw [show 3 * k + 1 + 4 = 3 * k + 5 by omega, hz w a b, hq]
  exact ctlB_hold _

/-- A request wire `r (k+1)` (copy of `c k`) that rose after `T` stays 1 while
`a (k+1)` is 0 (its controller cannot fall). -/
theorem req_stays (hx : Timed (pipe n) lo hi x) (hE : Empty n x T) {k u : Nat} (hk : k < n)
    (hr : Rch x T (3 * k + 3) u)
    (hz : ∀ w, T ≤ w → w ≤ u → x w (3 * k + 5) = false) : x u (3 * k + 3) = true := by
  obtain ⟨w0, hw0, hw0u, hx0⟩ := hr
  obtain ⟨r, hr1, hr2, hr3, hr4⟩ := first_rise (fun t => x t (3 * k + 3)) (hE _ (by omega) (by omega))
    hx0 hw0
  have hn3 : 3 * k + 3 < 3 * n + 3 := by omega
  have hc : x r (3 * k + 1) = true := by
    have := cause1 hx hn3 (show x (r + 1) (3 * k + 3) ≠ x r (3 * k + 3) by simp_all)
    rw [hr4] at this
    have e0 : (3 * k + 3) % 3 = 0 := by omega
    have e1 : 3 * k + 3 ≠ 0 := by omega
    simp only [pipe, pf, e0, e1, ite_true, ite_false, show 3 * k + 3 - 2 = 3 * k + 1 by omega] at this
    exact this.symm
  refine hold hx hn3 hr4 u (by omega) (fun w a b _ => ?_)
  show pf n (3 * k + 3) (x w) = true
  have e0 : (3 * k + 3) % 3 = 0 := by omega
  have e1 : 3 * k + 3 ≠ 0 := by omega
  simp only [pf, e0, e1, ite_true, ite_false, show 3 * k + 3 - 2 = 3 * k + 1 by omega]
  exact ctl_stays hx hk hc (by omega) (fun w' c d => hz w' (by omega) (by omega))

/-- The chain events: `ev (2k) = r k = 3k`, `ev (2k+1) = c k = 3k+1`; `ev (2n+1) = a n`. -/
def ev (n j : Nat) : Nat := if j = 2 * n + 1 then 3 * n + 2 else 3 * (j / 2) + j % 2

/-- Step delays: the upper bound of the gate reached at event `j`. -/
def dd (n : Nat) (hi : Nat → Nat) (j : Nat) : Nat := hi (ev n j)

theorem pipe_step (hx : Timed (pipe n) lo hi x) (hE : Empty n x T) (hn : 1 ≤ n) :
    ∀ j t, j < 2 * n + 1 → Rch x T (ev n j) t → T ≤ t →
      Rch x T (ev n (j + 1)) (t + dd n hi (j + 1)) := by
  intro j t hj hr hT
  have hlt : ev n (j + 1) < (pipe n).n := by
    show ev n (j + 1) < 3 * n + 3; unfold ev; split <;> omega
  suffices hexc : ∀ u, t ≤ u → u ≤ t + hi (ev n (j + 1)) →
      (∀ w, T ≤ w → w ≤ u → x w (ev n (j + 1)) ≠ true) → (pipe n).f (ev n (j + 1)) (x u) = true by
    obtain ⟨w, a, b, c⟩ := reach_step (v := true) hx hlt hT hexc
    exact ⟨w, a, b, c⟩
  intro u h1 h2 hnr
  -- excitation of the next event's gate at u
  have hru : Rch x T (ev n j) u := rch_mono h1 hr
  by_cases hpar : j % 2 = 0
  · obtain ⟨k, rfl⟩ : ∃ k, j = 2 * k := ⟨j / 2, by omega⟩
    have ej : ev n (2 * k) = 3 * k := by unfold ev; split <;> omega
    rw [ej] at hru
    by_cases hkn : k = n
    · -- the sink step: from r n to a n
      subst hkn
      have ej1 : ev k (2 * k + 1) = 3 * k + 2 := by unfold ev; simp
      rw [ej1] at hnr ⊢
      have hz : ∀ w, T ≤ w → w ≤ u → x w (3 * k + 2) = false := fun w a b => by simpa using hnr w a b
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hrn := req_stays hx hE (k := k') (u := u) (by omega)
        (by rw [show 3 * k' + 3 = 3 * (k' + 1) by omega]; exact hru)
        (fun w a b => by rw [show 3 * k' + 5 = 3 * (k' + 1) + 2 by omega]; exact hz w a b)
      show pf (k' + 1) (3 * (k' + 1) + 2) (x u) = true
      have e0 : (3 * (k' + 1) + 2) % 3 ≠ 0 := by omega
      have e1 : (3 * (k' + 1) + 2) % 3 ≠ 1 := by omega
      have e2 : ¬ (3 * (k' + 1) + 2) / 3 < k' + 1 := by omega
      simp only [pf, e0, e1, e2, ite_false]
      rwa [show 3 * k' + 3 = 3 * (k' + 1) by omega] at hrn
    · -- from r k to c k (k < n)
      have hk : k < n := by omega
      have ej1 : ev n (2 * k + 1) = 3 * k + 1 := by unfold ev; split <;> omega
      rw [ej1] at hnr ⊢
      have Q := pipe_quiet hx hE (g := 3 * k + 1) (by omega) (by omega) hnr
      have hrk : x u (3 * k) = true := by
        obtain ⟨w0, hw0, hw0u, hx0⟩ := hru
        by_cases k0 : k = 0
        · subst k0
          refine hold hx (show 0 < 3 * n + 3 by omega) hx0 u hw0u (fun w' c d _ => ?_)
          show pf n 0 (x w') = true
          simp only [pf, Nat.zero_mod, ite_true]
          rw [Q w' (by omega) (by omega) 2 (by omega) (by omega)]; rfl
        · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
          have := req_stays hx hE (k := k') (u := u) (by omega)
            ⟨w0, hw0, hw0u, by rw [show 3 * k' + 3 = 3 * (k' + 1) by omega]; exact hx0⟩
            (fun w' c d => Q w' c d _ (by omega) (by omega))
          rwa [show 3 * k' + 3 = 3 * (k' + 1) by omega] at this
      show pf n (3 * k + 1) (x u) = true
      have e1 : (3 * k + 1) % 3 = 1 := by omega
      have e2 : (3 * k + 1) / 3 = k := by omega
      have e0 : (3 * k + 1) % 3 ≠ 0 := by omega
      simp only [pf, e0, e1, e2, hk, ite_true, ite_false, show 3 * k + 1 - 1 = 3 * k by omega]
      rw [hrk, Q u (by omega) (Nat.le_refl _) (3 * k + 1 + 4) (by omega) (by omega)]
      exact ctlB_go _
  · -- j = 2k+1: from c k to r (k+1), k < n
    obtain ⟨k, rfl⟩ : ∃ k, j = 2 * k + 1 := ⟨j / 2, by omega⟩
    have hk : k < n := by omega
    have ej : ev n (2 * k + 1) = 3 * k + 1 := by unfold ev; split <;> omega
    rw [ej] at hru
    have ej1 : ev n (2 * k + 1 + 1) = 3 * k + 3 := by unfold ev; split <;> omega
    rw [ej1] at hnr ⊢
    have Q := pipe_quiet hx hE (g := 3 * k + 3) (by omega) (by omega) hnr
    obtain ⟨w0, hw0, hw0u, hx0⟩ := hru
    have hc := ctl_stays hx hk hx0 hw0u
      (fun w' c d => Q w' (by omega) (by omega) _ (by omega) (by omega))
    show pf n (3 * k + 3) (x u) = true
    have e0 : (3 * k + 3) % 3 = 0 := by omega
    have e1 : 3 * k + 3 ≠ 0 := by omega
    simp only [pf, e0, e1, ite_true, ite_false, show 3 * k + 3 - 2 = 3 * k + 1 by omega]
    exact hc

/-- **Pipeline latency (offered → delivered).** From an empty state at `T`, a
request offered at the input (`r 0 = 1` at `t0 ≥ T`) is acknowledged by the
sink (`a n` rises) by `t0 + Σ_{j=1}^{2n+1} hi (ev n j)`. -/
theorem pipe_latency (hx : Timed (pipe n) lo hi x) (hE : Empty n x T) (hn : 1 ≤ n)
    {t0 : Nat} (hT : T ≤ t0) (h0 : x t0 0 = true) :
    ∃ w, T ≤ w ∧ w ≤ t0 + sumD (dd n hi) (2 * n + 1) ∧ x w (3 * n + 2) = true := by
  have := chain (R := fun j t => Rch x T (ev n j) t ∧ T ≤ t) (dd n hi) (2 * n + 1)
    (fun j t hj ⟨hr, ht⟩ => ⟨pipe_step hx hE hn j t hj hr ht, by omega⟩) t0
    ⟨⟨t0, hT, Nat.le_refl _, by
      have : ev n 0 = 0 := by unfold ev; split <;> omega
      rw [this]; exact h0⟩, hT⟩
  obtain ⟨⟨w, a, b, c⟩, _⟩ := this
  have : ev n (2 * n + 1) = 3 * n + 2 := by unfold ev; simp
  rw [this] at c
  exact ⟨w, a, b, c⟩

/-- The source offers within its own bound from an empty state. -/
theorem pipe_offer (hx : Timed (pipe n) lo hi x) (hE : Empty n x T) :
    ∃ w, T ≤ w ∧ w ≤ T + hi 0 ∧ x w 0 = true := by
  refine reach_step (v := true) hx (show 0 < 3 * n + 3 by omega) (Nat.le_refl _) (fun u h1 h2 hnr => ?_)
  have Q := pipe_quiet hx hE (g := 0) (by omega) (by omega) hnr
  show pf n 0 (x u) = true
  simp only [pf, Nat.zero_mod, ite_true]
  rw [Q u h1 (Nat.le_refl _) 2 (by omega) (by omega)]; rfl

/-- **Pipeline latency from reset.** -/
theorem pipe_latency_empty (hx : Timed (pipe n) lo hi x) (hE : Empty n x T) (hn : 1 ≤ n) :
    ∃ w, T ≤ w ∧ w ≤ T + hi 0 + sumD (dd n hi) (2 * n + 1) ∧ x w (3 * n + 2) = true := by
  obtain ⟨t0, a, b, c⟩ := pipe_offer hx hE
  obtain ⟨w, d, e, f⟩ := pipe_latency hx hE hn a c
  exact ⟨w, d, by omega, f⟩

/-- The bound in closed form. -/
theorem sumD_dd (n : Nat) (hi : Nat → Nat) : ∀ m, m ≤ 2 * n →
    sumD (dd n hi) m = sumD (fun j => hi (3 * (j / 2) + j % 2)) m := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro hm
    simp only [sumD, ih (by omega), dd, ev]
    have : m ≠ 2 * n := by omega
    simp [this]

theorem sumD_le (d : Nat → Nat) {H : Nat} (hH : ∀ j, d j ≤ H) : ∀ m, sumD d m ≤ m * H := by
  intro m
  induction m with
  | zero => simp [sumD]
  | succ m ih => simp only [sumD, Nat.succ_mul]; have := hH (m + 1); omega

/-- **Uniform bound.** If every gate and route has upper delay `≤ H`, the sink
acknowledges within `(2n + 2)·H` of an empty state. -/
theorem pipe_latency_uniform (hx : Timed (pipe n) lo hi x) (hE : Empty n x T) (hn : 1 ≤ n)
    {H : Nat} (hH : ∀ i, hi i ≤ H) :
    ∃ w, T ≤ w ∧ w ≤ T + (2 * n + 2) * H ∧ x w (3 * n + 2) = true := by
  obtain ⟨w, a, b, c⟩ := pipe_latency_empty hx hE hn
  have := sumD_le (dd n hi) (fun j => hH _) (2 * n + 1)
  have := hH 0
  refine ⟨w, a, ?_, c⟩
  have e : (2 * n + 2) * H = H + (2 * n + 1) * H := by rw [Nat.add_mul, Nat.add_comm]; simp [Nat.add_mul]; omega
  omega

/-- **The same traces are Ops traces.** Every stage of a timed pipeline meets the
three control fields of the Ops `Link` gate model (C-8l), so the safety
theorems (`link_op`, `net_refines`) apply to exactly the runs whose liveness is
bounded here. -/
theorem pipe_ops_link (hx : Timed (pipe n) lo hi x) {k : Nat} (hk : k < n) (d d' : Nat → Nat) :
    let i : Formal.Net.Handshake.Chan := ⟨fun t => x t (3 * k), fun t => x t (3 * k + 2), d⟩
    let o : Formal.Net.Handshake.Chan := ⟨fun t => x t (3 * k + 3), fun t => x t (3 * k + 5), d'⟩
    let c : Trace := fun t => x t (3 * k + 1)
    (∀ t, c (t + 1) ≠ c t → c (t + 1) = ctlB (i.req t) (o.ack t) (c t) false) ∧
    (∀ t, i.ack (t + 1) ≠ i.ack t → i.ack (t + 1) = c t) ∧
    (∀ t, o.req (t + 1) ≠ o.req t → o.req (t + 1) = c t) := by
  intro i o c
  refine ⟨fun t h => ?_, fun t h => ?_, fun t h => ?_⟩
  · show x (t + 1) (3 * k + 1) = _
    rw [cause1 hx (show 3 * k + 1 < 3 * n + 3 by omega) h]
    show pf n (3 * k + 1) (x t) = _
    have e1 : (3 * k + 1) % 3 = 1 := by omega
    have e2 : (3 * k + 1) / 3 = k := by omega
    have e0 : (3 * k + 1) % 3 ≠ 0 := by omega
    simp only [pf, e0, e1, e2, hk, ite_true, ite_false, Nat.one_ne_zero,
      show 3 * k + 1 - 1 = 3 * k by omega, show 3 * k + 1 + 4 = 3 * k + 5 by omega]
    rfl
  · show x (t + 1) (3 * k + 2) = _
    rw [cause1 hx (show 3 * k + 2 < 3 * n + 3 by omega) h]
    show pf n (3 * k + 2) (x t) = _
    have e1 : (3 * k + 2) % 3 = 2 := by omega
    have e2 : (3 * k + 2) / 3 = k := by omega
    simp only [pf, e1, e2, hk, ite_true, ite_false, show (2:Nat) ≠ 0 by decide,
      show (2:Nat) ≠ 1 by decide, show 3 * k + 2 - 1 = 3 * k + 1 by omega]
    rfl
  · show x (t + 1) (3 * k + 3) = _
    rw [cause1 hx (show 3 * k + 3 < 3 * n + 3 by omega) h]
    show pf n (3 * k + 3) (x t) = _
    have e0 : (3 * k + 3) % 3 = 0 := by omega
    have e1 : 3 * k + 3 ≠ 0 := by omega
    simp only [pf, e0, e1, ite_true, ite_false, show 3 * k + 3 - 2 = 3 * k + 1 by omega]
    rfl

end pipeline

/-- **Non-vacuity.** The unit-delay run of `pipe n` from reset satisfies every
hypothesis of `pipe_latency_uniform` (with `H = 1`), so its sink acknowledges by
`2n + 2`. -/
theorem pipe_live_unit (n : Nat) (hn : 1 ≤ n) :
    ∃ w, w ≤ 2 * n + 2 ∧ unitTrace (pipe n) (fun _ => false) w (3 * n + 2) = true := by
  obtain ⟨w, _, b, c⟩ := pipe_latency_uniform (T := 0) (unit_timed (pipe n) (fun _ => false))
    (fun i _ _ => rfl) hn (H := 1) (fun _ => Nat.le_refl _)
  exact ⟨w, by omega, c⟩

/-- **Tightness at unit delay** (n = 3): the sink acknowledges exactly at
`2n + 2 = 8`, not before. -/
theorem pipe_unit_exact :
    unitTrace (pipe 3) (fun _ => false) 7 11 = false ∧
    unitTrace (pipe 3) (fun _ => false) 8 11 = true := by decide

end Formal.Net.Ops.TimedLive
