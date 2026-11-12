import Formal.Core.XAudit.Events2Time

/-!
# Formal.Core.XAudit.Events3 — choice (steer + exclusive merge) in the event-count domain (E5)

Probe A-events3. See `formal/notes/A-events3.md`.

`Events2` covers marked graphs: every token of a stage goes to every reader.
bdc's control for loops has CHOICE: a steer (`bd_steer`: `req_b = req · [s = b]`,
two AND gates on a 4-phase request and a select `s`) sends each token down ONE
of two arms, and an OR (`bd_mux`'s `z_req = Δ(j0 + j1)`, or the steer's own
acknowledge `ack = ack0 + ack1`) merges the arms back. The token's path depends
on data.

## The abstraction

* **The select is an environment choice.** A sequence `sel : Nat → Bool`,
  `sel k` = the branch of the `k`-th 4-phase transaction of the steered
  request. Nothing is assumed about it: every theorem holds for every `sel`.
* **Per-branch counters.** On arm `b`, the request after the steer has fired
  `filt sel b m` times when the request before it has fired `m` times
  (`filt`: the events of the first `m` that belong to branch-`b` transactions).
* **Conservation.** `filt sel false m + filt sel true m = m` (`filt_add`): every
  event goes down exactly one arm.
* **The steer is exact on counts** (`steer_val`): if `x` = the request's count
  and the select seen at the AND gate is `sel (x / 2)` whenever the request
  is high (the BUNDLING hypothesis: `s` stable while `req` is high), then
  `ph x ∧ [s = b] = ph (filt sel b x)`. Return to zero needs nothing.
* **The exclusive merge is a sum** (`or_val`): `ph (filt sel false x0) ∨ ph
  (filt sel true x1) = ph (filt sel false x0 + filt sel true x1)` whenever
  `|x0 − x1| ≤ 1`: the two arms see counts of the source at most one event
  apart, so they cannot both be high (two different transactions).
* **A choice pin is a channel with two arms.** A C-element pin that reads a
  source through steer → arm `b` → OR has count
  `filt sel false (M src (G₀ s)) + filt sel true (M src (G₁ s))`, which lies
  between the source's counts at the two arm sample times (`fsum_le_max`,
  `min_le_fsum`). So the min-plus walk bounds of `Events2` go through it with
  the arm band `[min lo, max hi]`, and the counter domain stays one
  monotone recursion.
* **Exclusivity is a timing condition** (`Skew`): a closed walk through the
  steered source with at most one token whose fastest traversal is at least
  the arm skew `max hi − min lo`. Then the source fires at most once inside
  the skew window (`Events2Time.cycle_le` for this recursion), which gives
  `|x0 − x1| ≤ 1`.

Main theorem: `Beh3.safe`: under `Back` (of `Events2`, on the arm-merged bands),
`ChoiceOK` (steered sources are 4-phase requests, reset 0) and `Skew`, for EVERY
select sequence satisfying the bundling hypothesis `SelOK`, every node is its
reset value flipped `M t j` times at every time; the per-branch arm counts
are `filt sel b (M ..)` and conserve the source's count.
-/

namespace Formal.Core.XAudit.Events3

open Formal.Core.TraceDiscrete (Sig Warp)
open Formal.Core.XAudit.Events (ph ph_zero ph_succ ph_not offB ph_off offB_le)
open Formal.Core.XAudit.Events2

/-! ## Per-branch counters -/

/-- Events among the first `m` of a 4-phase wire that belong to branch-`b`
transactions (`sel k` = branch of transaction `k`, events `2k`, `2k+1`). -/
def filt (sel : Nat → Bool) (b : Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => filt sel b n + (if sel (n / 2) = b then 1 else 0)

theorem filt_succ_le (sel : Nat → Bool) (b : Bool) (n : Nat) : filt sel b (n + 1) ≤ filt sel b n + 1 := by
  simp only [filt]; split <;> omega

theorem filt_mono (sel : Nat → Bool) (b : Bool) : ∀ {a c : Nat}, a ≤ c → filt sel b a ≤ filt sel b c := by
  intro a c h
  induction c with
  | zero => have : a = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ c ih =>
    rcases Nat.lt_or_ge a (c + 1) with h' | h'
    · have := ih (by omega); simp only [filt]; omega
    · have : a = c + 1 := by omega
      subst this; exact Nat.le_refl _

/-- **Conservation**: every event goes down exactly one arm. -/
theorem filt_add (sel : Nat → Bool) : ∀ n, filt sel false n + filt sel true n = n
  | 0 => rfl
  | n + 1 => by
      have := filt_add sel n
      simp only [filt]
      cases sel (n / 2) <;> simp <;> omega

theorem filt_even (sel : Nat → Bool) (b : Bool) : ∀ k, filt sel b (2 * k) % 2 = 0
  | 0 => rfl
  | k + 1 => by
      have ih := filt_even sel b k
      have e : 2 * (k + 1) = 2 * k + 1 + 1 := by omega
      rw [e]; simp only [filt]
      have h1 : (2 * k + 1) / 2 = k := by omega
      have h2 : (2 * k) / 2 = k := by omega
      rw [h1, h2]; split <;> omega

theorem filt_odd (sel : Nat → Bool) (b : Bool) (k : Nat) :
    filt sel b (2 * k + 1) = filt sel b (2 * k) + (if sel k = b then 1 else 0) := by
  simp only [filt]; rw [show (2 * k) / 2 = k by omega]

theorem ph_false_eq (m : Nat) : ph false m = decide (m % 2 = 1) := by
  unfold ph; by_cases h : m % 2 = 0 <;> simp [h] <;> omega

/-- **The steer is exact on counts**: the AND of a 4-phase request (count `x`,
reset low) with the select test `[s = b]` is the branch-`b` count, provided
the select is `sel (x / 2)` while the request is high. -/
theorem steer_val (sel : Nat → Bool) (b : Bool) (x : Nat) (sv : Bool)
    (h : x % 2 = 1 → sv = sel (x / 2)) :
    (ph false x && (sv == b)) = ph false (filt sel b x) := by
  rw [ph_false_eq, ph_false_eq]
  obtain ⟨k, hk | hk⟩ : ∃ k, x = 2 * k ∨ x = 2 * k + 1 := ⟨x / 2, by omega⟩
  · subst hk
    have he := filt_even sel b k
    have n1 : ¬ (2 * k) % 2 = 1 := by omega
    have n2 : ¬ filt sel b (2 * k) % 2 = 1 := by omega
    simp [n1, n2]
  · subst hk
    have he := filt_even sel b k
    have hs := h (by omega)
    rw [show (2 * k + 1) / 2 = k by omega] at hs
    rw [filt_odd, hs]
    simp only [show (2 * k + 1) % 2 = 1 by omega, decide_true, Bool.true_and]
    cases hb : sel k <;> cases b <;> simp <;> omega

/-- The sum of two arm counts lies between the source counts. -/
theorem fsum_le_max (sel : Nat → Bool) (x y : Nat) :
    filt sel false x + filt sel true y ≤ max x y := by
  have h1 := filt_mono sel false (Nat.le_max_left x y)
  have h2 := filt_mono sel true (Nat.le_max_right x y)
  have := filt_add sel (max x y); omega

theorem min_le_fsum (sel : Nat → Bool) (x y : Nat) :
    min x y ≤ filt sel false x + filt sel true y := by
  have h1 := filt_mono sel false (Nat.min_le_left x y)
  have h2 := filt_mono sel true (Nat.min_le_right x y)
  have := filt_add sel (min x y); omega

theorem fsum_mono (sel : Nat → Bool) {x y x' y' : Nat} (hx : x ≤ x') (hy : y ≤ y') :
    filt sel false x + filt sel true y ≤ filt sel false x' + filt sel true y' := by
  have := filt_mono sel false hx; have := filt_mono sel true hy; omega

/-- **The exclusive merge is a sum**: if the arms see source counts at most one
apart, they are never both high, and their OR has the summed count. -/
theorem or_val (sel : Nat → Bool) (x0 x1 : Nat) (h0 : x0 ≤ x1 + 1) (h1 : x1 ≤ x0 + 1) :
    (ph false (filt sel false x0) || ph false (filt sel true x1)) =
      ph false (filt sel false x0 + filt sel true x1) := by
  -- both high would need x0, x1 odd, hence equal, hence the same transaction
  have excl : ¬ (filt sel false x0 % 2 = 1 ∧ filt sel true x1 % 2 = 1) := by
    rintro ⟨a, b⟩
    obtain ⟨k0, hk0 | hk0⟩ : ∃ k, x0 = 2 * k ∨ x0 = 2 * k + 1 := ⟨x0 / 2, by omega⟩ <;>
    obtain ⟨k1, hk1 | hk1⟩ : ∃ k, x1 = 2 * k ∨ x1 = 2 * k + 1 := ⟨x1 / 2, by omega⟩
    · subst hk0; have := filt_even sel false k0; omega
    · subst hk0; have := filt_even sel false k0; omega
    · subst hk1; have := filt_even sel true k1; omega
    · subst hk0; subst hk1
      have e : k0 = k1 := by omega
      subst e
      rw [filt_odd] at a b
      have := filt_even sel false k0; have := filt_even sel true k0
      cases h : sel k0 <;> simp [h] at a b <;> omega
  rw [ph_false_eq, ph_false_eq, ph_false_eq]
  by_cases a : filt sel false x0 % 2 = 1 <;> by_cases b : filt sel true x1 % 2 = 1
  · exact absurd ⟨a, b⟩ excl
  · have : (filt sel false x0 + filt sel true x1) % 2 = 1 := by omega
    simp [a, b, this]
  · have : (filt sel false x0 + filt sel true x1) % 2 = 1 := by omega
    simp [a, b, this]
  · have : ¬ (filt sel false x0 + filt sel true x1) % 2 = 1 := by omega
    simp [a, b, this]

/-! ## Negative controls for the two primitives -/

/-- NEGATIVE CONTROL (bundling): if the select changes while the request is
high (`sv ≠ sel (x / 2)`), the steer output is NOT the branch count: here
transaction 0 is a branch-1 transaction but the AND sees `s = 0` and raises
arm 0. -/
theorem steer_neg : (ph false 1 && (false == false)) ≠ ph false (filt (fun _ => true) false 1) := by
  decide

/-- NEGATIVE CONTROL (exclusivity): arms two events apart (`x1 = x0 + 2`, the
source fired twice inside the arm skew) are both high, and the OR loses a
token: OR = 1 but the summed count is even. -/
theorem or_neg : (ph false (filt (fun k => k == 1) false 1) || ph false (filt (fun k => k == 1) true 3)) ≠
    ph false (filt (fun k => k == 1) false 1 + filt (fun k => k == 1) true 3) := by
  decide

/-! ## Networks with choice pins -/

/-- Choice structure on a `CNet`: pin `p` of `j` is a CHOICE pin (`kind`) when
it reads `src j p` through a steer (select sequence `sel j p`), two arms and an
OR; otherwise it is a plain channel (arm `false` only). -/
structure Choice {N : Nat} (net : CNet N) where
  kind : (j : Fin N) → Fin (net.ar j) → Bool
  sel : (j : Fin N) → Fin (net.ar j) → Nat → Bool

/-- Delay bands: LUT, feedback, and per pin per arm (a plain pin uses arm
`false`). An arm's band is the whole path source → steer → arm → OR → pin
(composition of transport channels, `chain_warp`). -/
structure Bands3 {N : Nat} (net : CNet N) where
  loF : Fin N → Nat
  hiF : Fin N → Nat
  loA : (j : Fin N) → Fin (net.ar j) → Bool → Nat
  hiA : (j : Fin N) → Fin (net.ar j) → Bool → Nat
  loQ : Fin N → Nat
  hiQ : Fin N → Nat

namespace Bands3
variable {N : Nat} {net : CNet N} (ch : Choice net) (b : Bands3 net)

/-- A pin's merged band: `[min lo, max hi]` over its arms. -/
def loP (j : Fin N) (p : Fin (net.ar j)) : Nat :=
  if ch.kind j p then min (b.loA j p false) (b.loA j p true) else b.loA j p false

def hiP (j : Fin N) (p : Fin (net.ar j)) : Nat :=
  if ch.kind j p then max (b.hiA j p false) (b.hiA j p true) else b.hiA j p false

/-- The `Events2` bands of the merged pins: walks, tokens and `Back` are reused. -/
def toB : Bands net where
  loF := b.loF
  hiF := b.hiF
  loG := b.loP ch
  hiG := b.hiP ch
  loQ := b.loQ
  hiQ := b.hiQ

end Bands3

/-- Steered sources are 4-phase requests with reset value 0 (`req` high =
odd count). -/
def ChoiceOK {N : Nat} {net : CNet N} (ch : Choice net) : Prop :=
  ∀ j p, ch.kind j p = true → net.v (net.src j p) = false

instance {N : Nat} {net : CNet N} (ch : Choice net) : Decidable (ChoiceOK ch) := by
  unfold ChoiceOK; exact inferInstance

/-- **Skew** (decidable, with a certificate walk per choice pin): a closed walk
through the steered source with at most one token whose fastest traversal
covers the arm skew `max hi − min lo`. -/
def Skew {N : Nat} {net : CNet N} (ch : Choice net) (b : Bands3 net)
    (sk : (j : Fin N) → Fin (net.ar j) → List (Arc net)) : Prop :=
  ∀ j p, ch.kind j p = true →
    walkOK net (net.src j p) (net.src j p) (sk j p) = true ∧ wTok net (sk j p) ≤ 1 ∧
    b.hiP ch j p - b.loP ch j p ≤ wLo (b.toB ch) (sk j p)

instance {N : Nat} {net : CNet N} (ch : Choice net) (b : Bands3 net)
    (sk : (j : Fin N) → Fin (net.ar j) → List (Arc net)) : Decidable (Skew ch b sk) := by
  unfold Skew; exact inferInstance

/-- A concrete behaviour with choice pins. `sv j p a t`: the select as seen,
at time `t`, by arm `a`'s AND gate (composed with the arm's delays). -/
structure Beh3 {N : Nat} (net : CNet N) (ch : Choice net) (b : Bands3 net) where
  c : Fin N → Sig
  pin : (j : Fin N) → Fin (net.ar j) → Sig
  q : Fin N → Sig
  r : Fin N → Sig
  sv : (j : Fin N) → Fin (net.ar j) → Bool → Sig
  F : Fin N → Nat → Nat
  G : (j : Fin N) → Fin (net.ar j) → Bool → Nat → Nat
  Q : Fin N → Nat → Nat
  wF : ∀ j, Warp (b.loF j) (b.hiF j) (F j)
  wG : ∀ j p a, Warp (b.loA j p a) (b.hiA j p a) (G j p a)
  wQ : ∀ j, Warp (b.loQ j) (b.hiQ j) (Q j)
  loF1 : ∀ j, 1 ≤ b.loF j
  loA1 : ∀ j p a, 1 ≤ b.loA j p a
  loQ1 : ∀ j, 1 ≤ b.loQ j
  hc : ∀ j t, c j t = net.lutF j (fun p => pin j p (F j t)) (q j (F j t)) (r j (F j t))
  hpin : ∀ j p t, pin j p t = (net.inv j p ^^
    (if ch.kind j p then
      ((c (net.src j p) (G j p false t) && (sv j p false t == false)) ||
       (c (net.src j p) (G j p true t) && (sv j p true t == true)))
    else c (net.src j p) (G j p false t)))
  hq : ∀ j t, q j t = c j (Q j t)
  r0 : ∀ j, r j 0 = true
  ranti : ∀ j a b, a ≤ b → r j b = true → r j a = true

namespace Beh3
variable {N : Nat} {net : CNet N} {ch : Choice net} {b : Bands3 net} (x : Beh3 net ch b)

theorem F_lt (j : Fin N) (t : Nat) (ht : 1 ≤ t) : x.F j t < t := by
  have := (x.wF j).le_late t; have := x.loF1 j; omega

theorem G_lt (j : Fin N) (p : Fin (net.ar j)) (a : Bool) (t : Nat) (ht : 1 ≤ t) : x.G j p a t < t := by
  have := (x.wG j p a).le_late t; have := x.loA1 j p a; omega

theorem Q_lt (j : Fin N) (t : Nat) (ht : 1 ≤ t) : x.Q j t < t := by
  have := (x.wQ j).le_late t; have := x.loQ1 j; omega

theorem F_zero (j : Fin N) : x.F j 0 = 0 := by have := (x.wF j).le_late 0; omega

/-- The pin count from the source counts at the arm sample times. -/
def pc (j : Fin N) (p : Fin (net.ar j)) (m0 m1 : Nat) : Nat :=
  if ch.kind j p then filt (ch.sel j p) false m0 + filt (ch.sel j p) true m1 else m0

theorem pc_mono (j : Fin N) (p : Fin (net.ar j)) {a0 a1 b0 b1 : Nat} (h0 : a0 ≤ b0) (h1 : a1 ≤ b1) :
    pc (ch := ch) j p a0 a1 ≤ pc (ch := ch) j p b0 b1 := by
  unfold pc; split
  · exact fsum_mono _ h0 h1
  · exact h0

/-- **The counts** (min-plus recursion; choice pins sum their arms' branch counts). -/
def M (t : Nat) (j : Fin N) : Nat :=
  if h : x.F j t < t then
    if x.r j (x.F j t) then 0 else
      fmin (net.ar j) (fun p =>
        pc (ch := ch) j p
          (if h0 : x.G j p false (x.F j t) < x.F j t then M (x.G j p false (x.F j t)) (net.src j p) else 0)
          (if h1 : x.G j p true (x.F j t) < x.F j t then M (x.G j p true (x.F j t)) (net.src j p) else 0)
        + net.off j p)
  else 0
termination_by t

/-- Phase count of pin `p` of `j` at LUT sample time `s`. -/
def P (j : Fin N) (p : Fin (net.ar j)) (s : Nat) : Nat :=
  pc (ch := ch) j p (x.M (x.G j p false s) (net.src j p)) (x.M (x.G j p true s) (net.src j p)) + net.off j p

def E (j : Fin N) (s : Nat) : Nat := if x.r j s then 0 else fmin (net.ar j) (fun p => x.P j p s)

theorem hs1 (j : Fin N) (s : Nat) (hr : ¬ x.r j s = true) : 1 ≤ s := by
  rcases Nat.eq_zero_or_pos s with h | h
  · rw [h] at hr; exact absurd (x.r0 j) hr
  · exact h

theorem M_eq (t : Nat) (j : Fin N) : x.M t j = x.E j (x.F j t) := by
  rw [M]
  by_cases ht : 1 ≤ t
  · rw [dif_pos (x.F_lt j t ht)]
    unfold E
    by_cases hr : x.r j (x.F j t) = true
    · simp [hr]
    · have hs := x.hs1 j _ hr
      simp only [hr, ite_false, Bool.false_eq_true]
      congr 1; funext p
      rw [dif_pos (x.G_lt j p false _ hs), dif_pos (x.G_lt j p true _ hs)]; rfl
  · have : t = 0 := by omega
    subst this
    rw [dif_neg (by rw [x.F_zero]; exact Nat.lt_irrefl 0)]
    unfold E; rw [x.F_zero, x.r0]; simp

theorem E_zero (j : Fin N) : x.E j 0 = 0 := by unfold E; rw [x.r0]; simp

theorem M_zero (j : Fin N) : x.M 0 j = 0 := by rw [M_eq, F_zero, E_zero]

theorem M_mono : ∀ (n : Nat) (j : Fin N) (a : Nat), a ≤ n → x.M a j ≤ x.M n j := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro j a han
    rcases Nat.lt_or_ge a n with hlt | hge
    · have hn : 1 ≤ n := by omega
      rw [x.M_eq a j, x.M_eq n j]
      have hFa := (x.wF j).mono a n (Nat.le_of_lt hlt)
      have hFn := x.F_lt j n hn
      unfold E
      by_cases hrn : x.r j (x.F j n) = true
      · have := x.ranti j _ _ hFa hrn; simp [hrn, this]
      · by_cases hra : x.r j (x.F j a) = true
        · simp [hra]
        · simp only [hra, hrn, ite_false, Bool.false_eq_true]
          apply fmin_mono _ _ _ (net.ar_pos j)
          intro p
          unfold P
          have hs := x.hs1 j _ hrn
          have m0 := ih (x.G j p false (x.F j n)) (by have := x.G_lt j p false _ hs; omega) (net.src j p) _
            ((x.wG j p false).mono _ _ hFa)
          have m1 := ih (x.G j p true (x.F j n)) (by have := x.G_lt j p true _ hs; omega) (net.src j p) _
            ((x.wG j p true).mono _ _ hFa)
          have := pc_mono (ch := ch) j p m0 m1
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
      apply fmin_mono _ _ _ (net.ar_pos j)
      intro p; unfold P
      have m0 := x.M_mono (x.G j p false s) (net.src j p) _ ((x.wG j p false).mono _ _ h)
      have m1 := x.M_mono (x.G j p true s) (net.src j p) _ ((x.wG j p true).mono _ _ h)
      have := pc_mono (ch := ch) j p m0 m1
      omega

/-- A pin's count is at most the source's count `loP` earlier. -/
theorem P_le (j : Fin N) (p : Fin (net.ar j)) (s : Nat) :
    x.P j p s ≤ x.M (s - b.loP ch j p) (net.src j p) + net.off j p := by
  unfold P pc Bands3.loP
  have g0 := (x.wG j p false).le_late s
  have g1 := (x.wG j p true).le_late s
  split
  · have h := fsum_le_max (ch.sel j p) (x.M (x.G j p false s) (net.src j p)) (x.M (x.G j p true s) (net.src j p))
    have a0 := x.M_mono (s - min (b.loA j p false) (b.loA j p true)) (net.src j p) (x.G j p false s) (by omega)
    have a1 := x.M_mono (s - min (b.loA j p false) (b.loA j p true)) (net.src j p) (x.G j p true s) (by omega)
    have : max (x.M (x.G j p false s) (net.src j p)) (x.M (x.G j p true s) (net.src j p)) ≤
        x.M (s - min (b.loA j p false) (b.loA j p true)) (net.src j p) := Nat.max_le.mpr ⟨a0, a1⟩
    omega
  · have := x.M_mono (s - b.loA j p false) (net.src j p) (x.G j p false s) (by omega)
    omega

theorem M_le_pin (k : Fin N) (p : Fin (net.ar k)) (u : Nat) : x.M u k ≤ x.P k p (x.F k u) := by
  rw [x.M_eq]; unfold E
  by_cases hr : x.r k (x.F k u) = true
  · simp [hr]
  · simp only [hr, ite_false, Bool.false_eq_true]
    exact fmin_le _ _ p

/-- **Walk bound** through plain and choice pins (merged bands). -/
theorem walk_le : ∀ (w : List (Arc net)) (a bb : Fin N), walkOK net a bb w = true →
    ∀ u, x.M u a ≤ x.M (u - wLo (b.toB ch) w) bb + wTok net w
  | [], a, bb, h, u => by
      simp only [walkOK, beq_iff_eq] at h; subst h; simp [wLo, wTok]
  | ⟨k, p⟩ :: w, a, bb, h, u => by
      simp only [walkOK, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨hk, hw⟩ := h
      subst hk
      have h1 := x.M_le_pin k p u
      have h2 := x.P_le k p (x.F k u)
      have a1 := (x.wF k).le_late u
      have h3 := x.M_mono (u - b.loF k - b.loP ch k p) (net.src k p) (x.F k u - b.loP ch k p) (by omega)
      have h4 := walk_le w (net.src k p) bb hw (u - b.loF k - b.loP ch k p)
      have e : u - b.loF k - b.loP ch k p - wLo (b.toB ch) w = u - wLo (b.toB ch) (⟨k, p⟩ :: w) := by
        simp only [wLo, Bands3.toB]; omega
      rw [e] at h4
      simp only [wTok]
      omega

theorem cycle_le (w : List (Arc net)) (j : Fin N) (hw : walkOK net j j w = true) (t : Nat) :
    x.M (t + wLo (b.toB ch) w) j ≤ x.M t j + wTok net w := by
  have := x.walk_le w j j hw (t + wLo (b.toB ch) w)
  rwa [Nat.add_sub_cancel] at this

theorem pin_le_q {back : (j : Fin N) → Fin (net.ar j) → List (Arc net)} (hB : Back (b.toB ch) back)
    (j : Fin N) (p : Fin (net.ar j)) (s : Nat) : x.P j p s ≤ x.M (x.Q j s) j + 1 := by
  obtain ⟨hw, htok, hrace⟩ := hB j p
  have h0 := x.P_le j p s
  have h1 := x.walk_le (back j p) _ _ hw (s - b.loP ch j p)
  have a4 := (x.wQ j).early_le s
  have hrace' : b.hiQ j ≤ b.loP ch j p + wLo (b.toB ch) (back j p) := hrace
  have := x.M_mono (x.Q j s) j (s - b.loP ch j p - wLo (b.toB ch) (back j p)) (by omega)
  omega

theorem q_le_E (j : Fin N) (s : Nat) : x.M (x.Q j s) j ≤ x.E j s := by
  rw [x.M_eq]
  apply x.E_mono
  have a1 := (x.wF j).le_late (x.Q j s)
  have a2 := (x.wQ j).le_late s
  omega

/-- **Exclusivity from Skew**: the two arms of a choice pin see source counts
at most one apart. -/
theorem arms_close {sk : (j : Fin N) → Fin (net.ar j) → List (Arc net)} (hS : Skew ch b sk)
    (j : Fin N) (p : Fin (net.ar j)) (hk : ch.kind j p = true) (s : Nat) (a a' : Bool) :
    x.M (x.G j p a s) (net.src j p) ≤ x.M (x.G j p a' s) (net.src j p) + 1 := by
  obtain ⟨hw, htok, hskew⟩ := hS j p hk
  have c := x.cycle_le (sk j p) (net.src j p) hw (s - b.hiP ch j p)
  have la := (x.wG j p a).le_late s
  have ea' := (x.wG j p a').early_le s
  have hlo : b.loP ch j p ≤ b.loA j p a := by
    unfold Bands3.loP; rw [if_pos hk]; cases a
    · exact Nat.min_le_left _ _
    · exact Nat.min_le_right _ _
  have hhi : b.hiA j p a' ≤ b.hiP ch j p := by
    unfold Bands3.hiP; rw [if_pos hk]; cases a'
    · exact Nat.le_max_left _ _
    · exact Nat.le_max_right _ _
  have m1 := x.M_mono (s - b.hiP ch j p + wLo (b.toB ch) (sk j p)) (net.src j p) (x.G j p a s) (by omega)
  have m2 := x.M_mono (x.G j p a' s) (net.src j p) (s - b.hiP ch j p) (by omega)
  omega

/-- The BUNDLING hypothesis on the select (named, never derived here): at
every arm sample where the steered request is high (odd count), the select seen
by that arm is the branch of that transaction. In bdc the select is channel
data held from `req↑` to `ack↓` (`bd_mux`: "it converts a timing obligation
into a data one"); discharging it is E6. -/
def SelOK : Prop :=
  ∀ j p a s, ch.kind j p = true → x.M (x.G j p a s) (net.src j p) % 2 = 1 →
    x.sv j p a s = ch.sel j p (x.M (x.G j p a s) (net.src j p) / 2)

/-- **Soundness of the counter domain with choice.** Under `Back` (merged
bands), `ChoiceOK`, `Skew`, and for every select sequence satisfying the
bundling hypothesis `SelOK`, every node of every behaviour equals its reset
value flipped `M t j` times, at every time. -/
theorem safe {back : (j : Fin N) → Fin (net.ar j) → List (Arc net)} (hB : Back (b.toB ch) back)
    (hC : ChoiceOK ch) {sk : (j : Fin N) → Fin (net.ar j) → List (Arc net)} (hS : Skew ch b sk)
    (hsel : x.SelOK) :
    ∀ t (j : Fin N), x.c j t = ph (net.v j) (x.M t j) := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
    intro j
    rw [x.hc j t, x.M_eq t j]
    unfold CNet.lutF E
    by_cases hr : x.r j (x.F j t) = true
    · simp [hr, ph_zero]
    · simp only [hr, ite_false, Bool.false_eq_true]
      have hs1 := x.hs1 j _ hr
      have ht1 : 1 ≤ t := by
        rcases Nat.eq_zero_or_pos t with h | h
        · rw [h, x.F_zero] at hs1; omega
        · exact h
      have hst : x.F j t < t := x.F_lt j t ht1
      generalize x.F j t = s at hr hs1 hst ⊢
      have hpin : ∀ p, (x.pin j p s ^^ net.neg j p) = ph (net.v j) (x.P j p s) := by
        intro p
        have ihA : ∀ a, x.c (net.src j p) (x.G j p a s) = ph (net.v (net.src j p)) (x.M (x.G j p a s) (net.src j p)) :=
          fun a => ih _ (Nat.lt_trans (x.G_lt j p a s hs1) hst) _
        rw [x.hpin j p s]
        unfold P pc CNet.off
        by_cases hk : ch.kind j p = true
        · have hv := hC j p hk
          rw [if_pos hk, if_pos hk, ihA false, ihA true, hv]
          have st0 := steer_val (ch.sel j p) false (x.M (x.G j p false s) (net.src j p)) (x.sv j p false s)
            (fun h => hsel j p false s hk h)
          have st1 := steer_val (ch.sel j p) true (x.M (x.G j p true s) (net.src j p)) (x.sv j p true s)
            (fun h => hsel j p true s hk h)
          rw [st0, st1, or_val _ _ _ (x.arms_close hS j p hk s false true) (x.arms_close hS j p hk s true false)]
          rw [ph_xor, ← hv]
          exact ph_off _ _ _
        · have hk' : ch.kind j p = false := by simpa using hk
          rw [if_neg (by simp [hk']), if_neg (by simp [hk']), ihA false, ph_xor]
          exact ph_off _ _ _
      have hq : x.q j s = ph (net.v j) (x.M (x.Q j s) j) := by
        rw [x.hq j s]; exact ih _ (Nat.lt_trans (x.Q_lt j s hs1) hst) _
      simp only [hpin, hq]
      have e1 := x.q_le_E j s
      unfold E at e1
      simp only [hr, ite_false, Bool.false_eq_true] at e1
      apply cel_ph _ _ (net.ar_pos j)
      · intro p; exact Nat.le_trans e1 (fmin_le _ _ p)
      · intro p; exact x.pin_le_q hB j p s

/-- **Per-branch counters and conservation**: on a choice pin, arm `a`
carries `filt sel a` of the source count (as seen by that arm), and the two
arms together carry the source count when they see the same count. -/
theorem branch_counts (j : Fin N) (p : Fin (net.ar j)) (n : Nat) :
    filt (ch.sel j p) false n + filt (ch.sel j p) true n = n := filt_add _ n

end Beh3

end Formal.Core.XAudit.Events3
