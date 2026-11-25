import Formal.Net.OpsTimedLive

/-!
# Probe C-8o (goal 1): a per-token period bound, by a marked-graph argument

8n's `pipe_latency` bounds the FIRST token through an empty pipeline. With the
free-running source (`bd_src`: `req = ¬ack`) the pipeline never returns to
the all-zero state (the next token enters stage 0 while the previous one is
still draining), so a steady-state argument is needed. This file gives one
that does not need the pipeline to empty:

## Generic part (any network of C-elements and buffers)

A gate is a marked-graph transition (`MG`): it has a list of input PLACES
`(u, inv)`; place `(u, false)` of gate `g` is marked iff `s u ≠ s g` (a
buffer/forward input), `(u, true)` iff `s u = s g` (an inverted input, e.g. the
`¬ack` input of a link controller); the gate's function flips its node exactly
when all its places are marked. `bd_link`'s controller `C(r, ¬a)`, a buffer
route, the source inverter and the sink wire all have this form
(`pipe_mg`, from the generated LUT functions of 8n's `pipe n`).

`SafeInv s`: a marked place disables its source gate (one token per elementary
cycle; this is 1-safeness of the marked graph). `readyB s d g`: every backward
path of UNMARKED places from `g` has fewer than `d` places (`d = 1`: `g` is
excited).

* `mg_fire_within`: in a timed trace (inertial `[lo, hi]` per gate, `hi ≤ H`)
  in which `SafeInv` holds at every time, `readyB (x t) d g` implies that `g`
  toggles in `[t, t + d·H)`. Each unmarked input place is filled by its source
  within `(d-1)·H` (induction), every marked place stays marked until `g`
  fires (SafeInv), and then `g` fires within `H` (upper bound only).
* `mg_window`: if `readyB · d g` holds at every time, `g` toggles in every
  window of `d·H`: a PERIOD bound, in any steady state.

## Reachable-set certificates

`Cert`: a list of states (as bit lists) that contains the reset state and is
closed under firing excited gates, on which the net is persistent, `SafeInv`
holds and `readyB d g` holds. `cert_window`: a checked certificate gives the
period bound for every timed trace from reset (Bridge's `timed_reach` maps the
timed trace into the certificate). The checks are `decide +kernel`.

## Pipeline instances

`pipe_period_n1` … `pipe_period_n3`: the sink acknowledge `a n` of 8n's
`pipe n` (generated `bd_src`, `bd_link` controllers, every route a gate)
toggles in every window of `d_n · H` from reset, so the sink accepts one token
every `2·d_n·H`; and the same for every node.
-/

namespace Formal.Net.Ops.Period
open Formal.Net Formal.Net.Bridge
open Formal.Net.Ops.TimedLive (cause1 reach_step pipe pf ctlB_ff)

/-- Marking of input place `p = (u, inv)` of gate `g`. -/
def marked (s : State) (g : Nat) (p : Nat × Bool) : Bool :=
  if p.2 then s p.1 == s g else s p.1 != s g

/-- Every gate is a marked-graph transition with input places `ins g`. -/
def MG (N : Bridge.Net) (ins : Nat → List (Nat × Bool)) : Prop :=
  ∀ g, g < N.n → ∀ s, N.f g s = if (ins g).all (marked s g) then !s g else s g

/-- A marked place disables its source (1-safeness), as a Bool check. -/
def safeB (N : Bridge.Net) (ins : Nat → List (Nat × Bool)) (s : State) : Bool :=
  (List.range N.n).all fun g => (ins g).all fun p => !marked s g p || (N.f p.1 s == s p.1)

/-- Every backward path of unmarked places from `g` is shorter than `d`. -/
def readyB (ins : Nat → List (Nat × Bool)) (s : State) : Nat → Nat → Bool
  | 0, _ => false
  | d + 1, g => (ins g).all fun p => marked s g p || readyB ins s d p.1

variable {N : Bridge.Net} {ins : Nat → List (Nat × Bool)} {lo hi : Nat → Nat} {x : Nat → State}

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

theorem marked_flip {s s' : State} {g : Nat} {p : Nat × Bool} (h1 : s' p.1 ≠ s p.1) (h2 : s' g = s g) : marked s' g p = !marked s g p := by
  unfold marked
  rw [h2]
  have : s' p.1 = !s p.1 := by revert h1; cases s' p.1 <;> cases s p.1 <;> simp
  rw [this]
  split <;> cases s p.1 <;> cases s g <;> rfl

section generic
variable (hx : Timed N lo hi x) (hmg : MG N ins)
  (hsrc : ∀ g p, g < N.n → p ∈ ins g → p.1 < N.n)
  (hS : ∀ t, safeB N ins (x t) = true)
include hx hmg hsrc hS

theorem safe_at {t g : Nat} {p : Nat × Bool} (hg : g < N.n) (hp : p ∈ ins g)
    (hm : marked (x t) g p = true) : x (t + 1) p.1 = x t p.1 := by
  have h := hS t
  unfold safeB at h
  rw [List.all_eq_true] at h
  have h2 := h g (List.mem_range.2 hg)
  rw [List.all_eq_true] at h2
  have h3 := h2 p hp
  rw [hm] at h3
  simp only [Bool.not_true, Bool.false_or, beq_iff_eq] at h3
  apply Classical.byContradiction; intro hc
  exact hc (by rw [cause1 hx (hsrc g p hg hp) hc, h3])

/-- A marked place stays marked while its gate holds. -/
theorem mark_stays {g : Nat} {p : Nat × Bool} (hg : g < N.n) (hp : p ∈ ins g) {v0 : Nat}
    (hm : marked (x v0) g p = true) :
    ∀ v, v0 ≤ v → (∀ u, v0 ≤ u → u ≤ v → x u g = x v0 g) → marked (x v) g p = true := by
  intro v
  induction v with
  | zero => intro h _; have : v0 = 0 := by omega
            subst this; exact hm
  | succ v ih =>
    intro h1 hc
    rcases Nat.eq_or_lt_of_le h1 with e | e
    · rw [← e]; exact hm
    · have hv := ih (by omega) (fun u a b => hc u a (by omega))
      have e1 := safe_at hx hmg hsrc hS hg hp hv
      have e2 : x (v + 1) g = x v g := by rw [hc (v + 1) (by omega) (Nat.le_refl _), hc v (by omega) (by omega)]
      unfold marked at hv ⊢
      rw [e1, e2]; exact hv

/-- **Marked-graph progress.** -/
theorem mg_fire_within {H : Nat} (hH : ∀ i, hi i ≤ H) :
    ∀ d t g, g < N.n → readyB ins (x t) d g = true →
      ∃ u, t ≤ u ∧ u < t + d * H ∧ x (u + 1) g ≠ x u g := by
  intro d
  induction d with
  | zero => intro t g _ h; simp [readyB] at h
  | succ d ih =>
    intro t g hg hr
    by_cases hch : ∃ u, t ≤ u ∧ u < t + d * H ∧ x (u + 1) g ≠ x u g
    · obtain ⟨u, a, b, c⟩ := hch
      exact ⟨u, a, by rw [Nat.succ_mul]; omega, c⟩
    have hconst : ∀ u, t ≤ u → u ≤ t + d * H → x u g = x t g := by
      intro u
      induction u with
      | zero => intro h _; have : t = 0 := by omega
                subst this; rfl
      | succ u ih' =>
        intro h1 h2
        rcases Nat.eq_or_lt_of_le h1 with e | e
        · rw [← e]
        · rw [← ih' (by omega) (by omega)]
          apply Classical.byContradiction; intro hc
          exact hch ⟨u, by omega, by omega, hc⟩
    -- every input place is marked at T1 = t + d*H
    unfold readyB at hr
    rw [List.all_eq_true] at hr
    have hmT : ∀ p, p ∈ ins g → marked (x (t + d * H)) g p = true := by
      intro p hp
      have hpr := hr p hp
      by_cases hm0 : marked (x t) g p = true
      · exact mark_stays hx hmg hsrc hS hg hp hm0 _ (by omega)
          (fun u a b => hconst u a b)
      · have hm0' : marked (x t) g p = false := by simpa using hm0
        rw [hm0', Bool.false_or] at hpr
        obtain ⟨u, a, b, c⟩ := ih t p.1 (hsrc g p hg hp) hpr
        have hpg : p.1 ≠ g := by
          intro e; rw [e] at c; exact hch ⟨u, a, b, c⟩
        obtain ⟨w, wa, wb, wc, wd⟩ := first_change (fun v => x v p.1) t (u + 1) (by
          by_cases e : x u p.1 = x t p.1
          · exact ⟨u + 1, by omega, Nat.le_refl _, by rw [← e]; exact c⟩
          · exact ⟨u, a, by omega, e⟩)
        have hmw : marked (x w) g p = true := by
          rw [marked_flip wc (hconst w (by omega) (by omega)), hm0']; rfl
        exact mark_stays hx hmg hsrc hS hg hp hmw _ (by omega)
          (fun v a' b' => by rw [hconst v (by omega) b', hconst w (by omega) (by omega)])
    obtain ⟨w, w1, w2, w3⟩ := reach_step (v := !x t g) hx hg (T := t) (t := t + d * H) (by omega)
      (fun u h1 _ hnr => by
        have hc : ∀ v, t ≤ v → v ≤ u → x v g = x t g := fun v a b => by
          have := hnr v a b; revert this; cases x v g <;> cases x t g <;> simp
        rw [hmg g hg]
        have hall : (ins g).all (marked (x u) g) = true := by
          rw [List.all_eq_true]; intro p hp
          exact mark_stays hx hmg hsrc hS hg hp (hmT p hp) u h1
            (fun v a b => by rw [hc v (by omega) b, hc (t + d * H) (by omega) (by omega)])
        rw [hall, if_pos rfl, hc u (by omega) (Nat.le_refl _)])
    obtain ⟨w', a, b, c, e⟩ := first_change (fun v => x v g) t w
      ⟨w, w1, Nat.le_refl _, by rw [w3]; cases x t g <;> simp⟩
    refine ⟨w' - 1, by omega, ?_, ?_⟩
    · have := hH g; rw [Nat.succ_mul]; omega
    · rw [show w' - 1 + 1 = w' by omega, e (w' - 1) (by omega) (by omega)]; exact c

/-- **Period bound.** If `readyB · d g` holds at every time, `g` toggles in every
window of `d·H`. -/
theorem mg_window {H : Nat} (hH : ∀ i, hi i ≤ H) {d g : Nat} (hg : g < N.n)
    (hR : ∀ t, readyB ins (x t) d g = true) (t : Nat) :
    ∃ u, t ≤ u ∧ u < t + d * H ∧ x (u + 1) g ≠ x u g :=
  mg_fire_within hx hmg hsrc hS hH d t g hg (hR t)

end generic

/-! ## Reachable-set certificates (bit lists) -/

def ofL (l : List Bool) : State := fun i => l.getD i false

def flipL : List Bool → Nat → List Bool
  | [], _ => []
  | b :: l, 0 => (!b) :: l
  | b :: l, k + 1 => b :: flipL l k

theorem flipL_get : ∀ (l : List Bool) (i j : Nat), i < l.length →
    (flipL l i).getD j false = if j = i then !l.getD i false else l.getD j false := by
  intro l
  induction l with
  | nil => intro i j h; simp at h
  | cons b l ih =>
    intro i j h
    cases i with
    | zero => cases j <;> simp [flipL]
    | succ i =>
      cases j with
      | zero => simp [flipL]
      | succ j =>
        simp only [flipL, List.getD_cons_succ]
        rw [ih i j (by simp at h; omega)]
        simp

theorem flipL_length : ∀ (l : List Bool) (i : Nat), (flipL l i).length = l.length := by
  intro l; induction l with
  | nil => intro i; rfl
  | cons b l ih => intro i; cases i <;> simp [flipL, ih]

theorem ofL_flip {l : List Bool} {i : Nat} (h : i < l.length) : ofL (flipL l i) = fire (ofL l) i := by
  funext j
  show (flipL l i).getD j false = _
  rw [flipL_get l i j h]
  unfold fire ofL; rfl

/-- Bool excitation on a bit list. -/
def exB (N : Bridge.Net) (l : List Bool) (i : Nat) : Bool := N.f i (ofL l) != l.getD i false

/-- The certificate check on a chunk `C` of the state list `S`: closure (into `S`),
persistence, SafeInv and `readyB d` for the targets `gs`. -/
def certC (N : Bridge.Net) (ins : Nat → List (Nat × Bool)) (S C : List (List Bool)) (d : Nat)
    (gs : List Nat) : Bool :=
  C.all fun l => l.length == N.n &&
    (List.range N.n).all (fun i => !exB N l i || S.contains (flipL l i)) &&
    (List.range N.n).all (fun i => (List.range N.n).all fun j =>
      i == j || !exB N l i || !exB N l j || exB N (flipL l j) i) &&
    safeB N ins (ofL l) &&
    gs.all (fun g => readyB ins (ofL l) d g)

/-- The whole certificate. -/
def certB (N : Bridge.Net) (ins : Nat → List (Nat × Bool)) (S : List (List Bool)) (d : Nat)
    (gs : List Nat) : Bool := certC N ins S S d gs

theorem certC_append {N : Bridge.Net} {ins : Nat → List (Nat × Bool)} {S A B : List (List Bool)}
    {d : Nat} {gs : List Nat} (ha : certC N ins S A d gs = true) (hb : certC N ins S B d gs = true) :
    certC N ins S (A ++ B) d gs = true := by
  unfold certC at *; rw [List.all_append, ha, hb]; rfl

theorem certB_reach {S : List (List Bool)} {d : Nat} {gs : List Nat} (hc : certB N ins S d gs = true)
    {l0 : List Bool} (h0 : l0 ∈ S) :
    ∀ s, Reach N (ofL l0) s → ∃ l, l ∈ S ∧ s = ofL l := by
  intro s hr
  induction hr with
  | refl => exact ⟨l0, h0, rfl⟩
  | step i _ he ih =>
    obtain ⟨l, hl, rfl⟩ := ih
    unfold certB certC at hc
    rw [List.all_eq_true] at hc
    have h := hc l hl
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
    obtain ⟨⟨⟨⟨hlen, hcl⟩, _⟩, _⟩, _⟩ := h
    have := hcl i he.1
    have hex : exB N l i = true := by
      unfold exB; have := he.2; simp only [bne_iff_ne, ne_eq]; exact this
    rw [hex] at this
    simp only [Bool.not_true, Bool.false_or, List.contains_iff_mem] at this
    exact ⟨_, this, (ofL_flip (by rw [hlen]; exact he.1)).symm⟩

theorem certB_persistent {S : List (List Bool)} {d : Nat} {gs : List Nat}
    (hc : certB N ins S d gs = true) {l0 : List Bool} (h0 : l0 ∈ S) : Persistent N (ofL l0) := by
  intro s hr i j hi hj hij
  obtain ⟨l, hl, rfl⟩ := certB_reach hc h0 s hr
  unfold certB certC at hc
  rw [List.all_eq_true] at hc
  have h := hc l hl
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨hlen, _⟩, hp⟩, _⟩, _⟩ := h
  have := hp i hi.1 j hj.1
  have ei : exB N l i = true := by unfold exB; simp only [bne_iff_ne, ne_eq]; exact hi.2
  have ej : exB N l j = true := by unfold exB; simp only [bne_iff_ne, ne_eq]; exact hj.2
  rw [ei, ej] at this
  have hij' : (i == j) = false := by simpa using hij
  rw [hij'] at this
  simp only [Bool.not_true, Bool.false_or] at this
  refine ⟨hi.1, ?_⟩
  rw [← ofL_flip (by rw [hlen]; exact hj.1)]
  unfold exB at this; exact bne_iff_ne.1 this

/-- **Certificate ⇒ period bound** for every timed trace from the certified reset
state. -/
theorem cert_window {S : List (List Bool)} {d : Nat} {gs : List Nat}
    (hc : certB N ins S d gs = true) {l0 : List Bool} (h0 : l0 ∈ S)
    (hmg : MG N ins) (hsrc : ∀ g p, g < N.n → p ∈ ins g → p.1 < N.n)
    (hx : Timed N lo hi x) (hx0 : x 0 = ofL l0) {H : Nat} (hH : ∀ i, hi i ≤ H)
    {g : Nat} (hg : g < N.n) (hgs : g ∈ gs) (t : Nat) :
    ∃ u, t ≤ u ∧ u < t + d * H ∧ x (u + 1) g ≠ x u g := by
  have hp := certB_persistent hc h0
  have inS : ∀ t, ∃ l, l ∈ S ∧ x t = ofL l := fun t => certB_reach hc h0 _ (timed_reach hp hx hx0 t)
  have facts : ∀ t, safeB N ins (x t) = true ∧ readyB ins (x t) d g = true := by
    intro t
    obtain ⟨l, hl, e⟩ := inS t
    rw [e]
    unfold certB certC at hc
    rw [List.all_eq_true] at hc
    have h := hc l hl
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    exact ⟨h.1.2, h.2 g hgs⟩
  exact mg_window hx hmg hsrc (fun t => (facts t).1) hH hg (fun t => (facts t).2) t

/-! ## The pipeline of 8n is a marked graph -/

/-- Input places of `pipe n` (ids: `r k = 3k`, `c k = 3k+1`, `a k = 3k+2`). The
unused node `3n+1` gets a self place, never marked (it never moves). -/
def pins (n i : Nat) : List (Nat × Bool) :=
  if i % 3 = 0 then (if i = 0 then [(2, true)] else [(i - 2, false)])
  else if i % 3 = 1 then (if i / 3 < n then [(i - 1, false), (i + 4, true)] else [(i, false)])
  else (if i / 3 < n then [(i - 1, false)] else [(3 * n, false)])

theorem ctlB_mg : ∀ r a q : Bool, Formal.Cells.LinkHandshake.ctlB r a q false =
    if ((r != q) && (a == q)) then !q else q := by decide

theorem pipe_mg (n : Nat) : MG (pipe n) (pins n) := by
  intro g hg s
  show pf n g s = _
  unfold pf pins
  by_cases a0 : g % 3 = 0
  · simp only [a0, ite_true]
    by_cases g0 : g = 0
    · simp only [g0, ite_true, List.all_cons, List.all_nil, marked, Bool.and_true]
      cases s 2 <;> cases s 0 <;> rfl
    · simp only [g0, ite_false, List.all_cons, List.all_nil, marked, Bool.and_true]
      cases s (g - 2) <;> cases s g <;> rfl
  · simp only [a0, ite_false]
    by_cases a1 : g % 3 = 1
    · simp only [a1, ite_true]
      by_cases hk : g / 3 < n
      · simp only [hk, ite_true, List.all_cons, List.all_nil, marked, Bool.and_true, ite_false,
          Bool.false_eq_true]
        rw [ctlB_mg]
      · simp only [hk, ite_false, List.all_cons, List.all_nil, marked, Bool.and_true,
          Bool.false_eq_true]
        cases s g <;> rfl
    · simp only [a1, ite_false]
      by_cases hk : g / 3 < n
      · simp only [hk, ite_true, List.all_cons, List.all_nil, marked, Bool.and_true,
          Bool.false_eq_true, ite_false]
        cases s (g - 1) <;> cases s g <;> rfl
      · simp only [hk, ite_false, List.all_cons, List.all_nil, marked, Bool.and_true,
          Bool.false_eq_true]
        cases s (3 * n) <;> cases s g <;> rfl

theorem pipe_src (n : Nat) : ∀ g p, g < (pipe n).n → p ∈ pins n g → p.1 < (pipe n).n := by
  intro g p hg hp
  show p.1 < 3 * n + 3
  have hg' : g < 3 * n + 3 := hg
  unfold pins at hp
  by_cases a0 : g % 3 = 0 <;> by_cases g0 : g = 0 <;> by_cases a1 : g % 3 = 1 <;>
    by_cases hk : g / 3 < n <;> simp [a0, g0, a1, hk] at hp <;> (try rcases hp with hp | hp) <;>
    (try subst hp) <;> simp <;> omega

/-! ## Pipeline certificates (n = 1, 2, 3)

The state lists are the SI-reachable sets of `pipe n` from reset (all nodes 0),
computed by a BFS outside the kernel and given as bit masks (node `i` = bit
`i`); `certB` re-checks closure, persistence, SafeInv and `readyB` in the
kernel, so nothing about the list is trusted. Sizes: 18, 72, 288 states
(`18·4^(n-1)`). The depth `2n + 3` is the smallest that works for the sink
`a n` and the source (an `#eval` sweep, not a theorem; inner nodes need less).
-/

def toL (m b : Nat) : List Bool := (List.range m).map fun i => b.testBit i

def pipeS1 : List (List Bool) := [0, 1, 3, 7, 11, 6, 15, 43, 14, 47, 46, 44, 40, 36, 41, 32, 4, 33].map (toL 6)

def pipeS2 : List (List Bool) := [0, 1, 3, 7, 11, 6, 15, 27, 14, 31, 59, 91, 30, 63, 95, 123, 347, 62, 94, 127, 351, 379, 60, 126, 350, 383, 56, 52, 124, 382, 57, 48, 120, 116, 380, 49, 121, 112, 376, 372, 113, 377, 368, 356, 369, 352, 324, 292, 353, 320, 288, 260, 36, 321, 289, 256, 32, 4, 323, 257, 33, 327, 331, 259, 326, 335, 263, 267, 334, 262, 271, 270].map (toL 9)

def pipeS3_0 : List (List Bool) := [0, 1, 3, 7, 11, 6, 15, 27, 14, 31, 59, 91, 30, 63, 95, 123, 219, 62, 94, 127, 223, 251, 475, 731, 60, 126, 222, 255, 479, 735, 507, 763, 987, 2779, 56, 52].map (toL 12)
def pipeS3_1 : List (List Bool) := [124, 254, 478, 734, 511, 767, 991, 2783, 1019, 2811, 3035, 57, 48, 120, 116, 252, 510, 766, 990, 2782, 1023, 2815, 3039, 3067, 49, 121, 112, 248, 244, 508, 764, 1022, 2814, 3038, 3071, 113].map (toL 12)
def pipeS3_2 : List (List Bool) := [249, 240, 504, 760, 500, 756, 1020, 2812, 3070, 241, 505, 761, 496, 752, 1016, 2808, 484, 1012, 2804, 3068, 497, 753, 1017, 2809, 480, 1008, 2800, 3064, 452, 420, 996, 3060, 481, 1009, 2801, 3065].map (toL 12)
def pipeS3_3 : List (List Bool) := [448, 416, 992, 3056, 388, 964, 932, 3044, 449, 417, 993, 3057, 384, 960, 928, 3040, 900, 3012, 2980, 451, 385, 961, 929, 3041, 896, 3008, 2976, 2948, 2852, 455, 459, 387, 963, 897, 3009, 2977].map (toL 12)
def pipeS3_4 : List (List Bool) := [2944, 2848, 2820, 2596, 2340, 454, 463, 391, 967, 395, 971, 899, 3011, 2945, 2849, 2816, 2592, 2336, 2564, 2308, 2084, 292, 462, 390, 966, 399, 975, 903, 3015, 907, 3019, 2947, 2817, 2593, 2337, 2560].map (toL 12)
def pipeS3_5 : List (List Bool) := [2304, 2080, 288, 2052, 260, 36, 398, 974, 902, 3014, 911, 3023, 2951, 2955, 2819, 2561, 2305, 2081, 289, 2048, 256, 32, 4, 910, 3022, 2950, 2959, 2823, 2827, 2563, 2307, 2049, 257, 33, 2958, 2822].map (toL 12)
def pipeS3_6 : List (List Bool) := [2831, 2567, 2311, 2571, 2315, 2051, 259, 2830, 2566, 2310, 2575, 2319, 2055, 263, 2587, 2059, 267, 2574, 2318, 2054, 262, 2591, 2063, 271, 2619, 2651, 2075, 2590, 2062, 270, 2623, 2655, 2079, 2683, 2107, 2139].map (toL 12)
def pipeS3_7 : List (List Bool) := [2622, 2654, 2078, 2687, 2111, 2143, 2171, 2620, 2686, 2110, 2142, 2175, 2616, 2612, 2684, 2108, 2174, 2617, 2608, 2680, 2104, 2676, 2100, 2172, 2609, 2681, 2105, 2672, 2096, 2168, 2164, 2673, 2097, 2169, 2160, 2161].map (toL 12)
def pipeS3 : List (List Bool) := pipeS3_0 ++ pipeS3_1 ++ pipeS3_2 ++ pipeS3_3 ++ pipeS3_4 ++ pipeS3_5 ++ pipeS3_6 ++ pipeS3_7

theorem pipe_cert1 : certB (pipe 1) (pins 1) pipeS1 5 ((List.range 6).filter (· != 4)) = true := by
  decide +kernel

theorem pipe_reset1 : List.replicate 6 false ∈ pipeS1 := by decide +kernel

/-- **Period, n = 1.** Every node (except the unused id `3n+1`) of `pipe 1` (in particular the sink `a 1`,
node 5) toggles in every window of `5·H` of every timed trace from reset. -/
theorem pipe_period_n1 {lo hi : Nat → Nat} {x : Nat → State} (hx : Timed (pipe 1) lo hi x)
    (h0 : x 0 = ofL (List.replicate 6 false)) {H : Nat} (hH : ∀ i, hi i ≤ H)
    {g : Nat} (hg : g < 6) (hg' : g ≠ 4) (t : Nat) :
    ∃ u, t ≤ u ∧ u < t + 5 * H ∧ x (u + 1) g ≠ x u g :=
  cert_window pipe_cert1 pipe_reset1 (pipe_mg 1) (pipe_src 1) hx h0 hH hg
    (List.mem_filter.2 ⟨List.mem_range.2 hg, by simpa using hg'⟩) t

theorem pipe_cert2 : certB (pipe 2) (pins 2) pipeS2 7 ((List.range 9).filter (· != 7)) = true := by
  decide +kernel

theorem pipe_reset2 : List.replicate 9 false ∈ pipeS2 := by decide +kernel

/-- **Period, n = 2.** Every node (except the unused id `3n+1`) of `pipe 2` (in particular the sink `a 2`,
node 8) toggles in every window of `7·H` of every timed trace from reset. -/
theorem pipe_period_n2 {lo hi : Nat → Nat} {x : Nat → State} (hx : Timed (pipe 2) lo hi x)
    (h0 : x 0 = ofL (List.replicate 9 false)) {H : Nat} (hH : ∀ i, hi i ≤ H)
    {g : Nat} (hg : g < 9) (hg' : g ≠ 7) (t : Nat) :
    ∃ u, t ≤ u ∧ u < t + 7 * H ∧ x (u + 1) g ≠ x u g :=
  cert_window pipe_cert2 pipe_reset2 (pipe_mg 2) (pipe_src 2) hx h0 hH hg
    (List.mem_filter.2 ⟨List.mem_range.2 hg, by simpa using hg'⟩) t

theorem pipe_cert3_0 : certC (pipe 3) (pins 3) pipeS3 pipeS3_0 9 ((List.range 12).filter (· != 10)) = true := by
  decide +kernel

theorem pipe_cert3_1 : certC (pipe 3) (pins 3) pipeS3 pipeS3_1 9 ((List.range 12).filter (· != 10)) = true := by
  decide +kernel

theorem pipe_cert3_2 : certC (pipe 3) (pins 3) pipeS3 pipeS3_2 9 ((List.range 12).filter (· != 10)) = true := by
  decide +kernel

theorem pipe_cert3_3 : certC (pipe 3) (pins 3) pipeS3 pipeS3_3 9 ((List.range 12).filter (· != 10)) = true := by
  decide +kernel

theorem pipe_cert3_4 : certC (pipe 3) (pins 3) pipeS3 pipeS3_4 9 ((List.range 12).filter (· != 10)) = true := by
  decide +kernel

theorem pipe_cert3_5 : certC (pipe 3) (pins 3) pipeS3 pipeS3_5 9 ((List.range 12).filter (· != 10)) = true := by
  decide +kernel

theorem pipe_cert3_6 : certC (pipe 3) (pins 3) pipeS3 pipeS3_6 9 ((List.range 12).filter (· != 10)) = true := by
  decide +kernel

theorem pipe_cert3_7 : certC (pipe 3) (pins 3) pipeS3 pipeS3_7 9 ((List.range 12).filter (· != 10)) = true := by
  decide +kernel

theorem pipe_cert3 : certB (pipe 3) (pins 3) pipeS3 9 ((List.range 12).filter (· != 10)) = true := by
  unfold certB pipeS3
  exact (certC_append (certC_append (certC_append (certC_append (certC_append (certC_append (certC_append pipe_cert3_0 pipe_cert3_1) pipe_cert3_2) pipe_cert3_3) pipe_cert3_4) pipe_cert3_5) pipe_cert3_6) pipe_cert3_7)

theorem pipe_reset3 : List.replicate 12 false ∈ pipeS3 := by decide +kernel

/-- **Period, n = 3.** Every node (except the unused id `3n+1`) of `pipe 3` (in particular the sink `a 3`,
node 11) toggles in every window of `9·H` of every timed trace from reset. -/
theorem pipe_period_n3 {lo hi : Nat → Nat} {x : Nat → State} (hx : Timed (pipe 3) lo hi x)
    (h0 : x 0 = ofL (List.replicate 12 false)) {H : Nat} (hH : ∀ i, hi i ≤ H)
    {g : Nat} (hg : g < 12) (hg' : g ≠ 10) (t : Nat) :
    ∃ u, t ≤ u ∧ u < t + 9 * H ∧ x (u + 1) g ≠ x u g :=
  cert_window pipe_cert3 pipe_reset3 (pipe_mg 3) (pipe_src 3) hx h0 hH hg
    (List.mem_filter.2 ⟨List.mem_range.2 hg, by simpa using hg'⟩) t

/-- Non-vacuity: the unit-delay run of `pipe 3` from reset meets every
hypothesis, so its sink toggles in every window of 9 ticks. -/
theorem pipe_period_unit (t : Nat) :
    ∃ u, t ≤ u ∧ u < t + 9 ∧ unitTrace (pipe 3) (ofL (List.replicate 12 false)) (u + 1) 11 ≠
      unitTrace (pipe 3) (ofL (List.replicate 12 false)) u 11 := by
  obtain ⟨u, a, b, c⟩ := pipe_period_n3 (unit_timed (pipe 3) _) rfl (H := 1) (fun _ => Nat.le_refl _)
    (g := 11) (by decide) (by decide) t
  exact ⟨u, a, by omega, c⟩

end Formal.Net.Ops.Period
