import Formal.Core.XAudit.Events

/-!
# Formal.Core.XAudit.Events2 — the counter domain for open nets, n-input C-elements and long pins

Probe A-events2 (extends A-events, `Events.lean`). See `formal/notes/A-events2.md`.

`Events.safe` covers closed networks of 2-input `bd_c2n` stages whose every
pin is one routed arc from a neighbour that reads it back (`Pairing`). This
file generalises the network and the soundness theorem in three ways at once:

* **E4, n-input C-elements.** A stage has `ar j ≥ 1` input pins, each with a
  LUT bubble `neg j p` (`bd_c2`: none, `bd_c2n`: on pin 1, `bd_c3`/`bd_c4`:
  none). Its settled function is `cel`: all (bubbled) inputs 1 ⇒ 1, all 0 ⇒ 0,
  otherwise hold the own feedback `q`. `cel_ph` is the counter form: if the
  feedback phase is at most one behind every input phase, the output phase is
  the minimum.
* **E1/E2, pins as channels.** Pin `p` of stage `j` reads stage `src j p`
  through ONE transport channel (a monotone warp in `[loG, hiG]`) that may
  invert (`inv j p`). A channel stands for a routed arc, a chain of buffers
  and routes (E1, composed at the netlist level in `Events2Design`), or the
  ENVIRONMENT (E2): an open pipe's sender is modelled as an inverting channel
  from the stage whose acknowledge it waits for (`req_in = ¬ack_in` delayed,
  an eager sender) and its receiver as a buffering channel from the stage
  whose request it acknowledges (`ack_out = req_out` delayed). With the
  environment closed this way, an open pipe is a closed counter system.
* **Back walks instead of `Pairing`.** The neighbour bound (`pin_le_q`) now
  follows any walk of pins from `src j p` back to `j` whose tokens, plus the
  pin's own, are at most 1, and whose fastest traversal is no faster than the
  feedback (`Back`, decidable). `Pairing ∧ Race` is the special case of
  one-arc walks; the environment's self-loop is the special case of the
  empty walk.

Main theorem: `Beh.safe`: under `Back`, in every behaviour every node is its
reset value flipped `M t j` times, at every time.
-/

namespace Formal.Core.XAudit.Events2

open Formal.Core.TraceDiscrete (Sig Warp)
open Formal.Core.XAudit.Events (ph ph_zero ph_succ ph_not offB ph_off offB_le)

/-! ## Minimum over `Fin n` -/

/-- Minimum of `f` over `Fin n` (0 for `n = 0`). -/
def fmin : (n : Nat) → (Fin n → Nat) → Nat
  | 0, _ => 0
  | 1, f => f 0
  | n + 2, f => min (f 0) (fmin (n + 1) (fun i => f i.succ))

theorem fmin_le : ∀ (n : Nat) (f : Fin n → Nat) (i : Fin n), fmin n f ≤ f i
  | 0, _, i => i.elim0
  | 1, f, i => by
      have : i = 0 := Fin.ext (by omega)
      subst this; exact Nat.le_refl _
  | n + 2, f, i => by
      show min (f 0) (fmin (n + 1) (fun i => f i.succ)) ≤ f i
      refine Fin.cases ?_ (fun k => ?_) i
      · exact Nat.min_le_left _ _
      · have := fmin_le (n + 1) (fun i => f i.succ) k
        exact Nat.le_trans (Nat.min_le_right _ _) this

theorem fmin_mem : ∀ (n : Nat) (f : Fin n → Nat), 0 < n → ∃ i, fmin n f = f i
  | 0, _, h => absurd h (Nat.lt_irrefl 0)
  | 1, f, _ => ⟨0, rfl⟩
  | n + 2, f, _ => by
      show ∃ i, min (f 0) (fmin (n + 1) (fun i => f i.succ)) = f i
      obtain ⟨k, hk⟩ := fmin_mem (n + 1) (fun i => f i.succ) (Nat.succ_pos _)
      by_cases h : f 0 ≤ fmin (n + 1) (fun i => f i.succ)
      · exact ⟨0, Nat.min_eq_left h⟩
      · exact ⟨k.succ, by rw [Nat.min_eq_right (by omega)]; exact hk⟩

theorem le_fmin (n : Nat) (f : Fin n → Nat) (hn : 0 < n) (c : Nat) (h : ∀ i, c ≤ f i) :
    c ≤ fmin n f := by
  obtain ⟨i, hi⟩ := fmin_mem n f hn; rw [hi]; exact h i

theorem fmin_mono (n : Nat) (f g : Fin n → Nat) (hn : 0 < n) (h : ∀ i, f i ≤ g i) :
    fmin n f ≤ fmin n g :=
  le_fmin n g hn _ (fun i => Nat.le_trans (fmin_le n f i) (h i))

/-! ## The n-input C-element -/

/-- Settled function of an n-input Muller C-element with own feedback `q`. -/
def cel {n : Nat} (x : Fin n → Bool) (q : Bool) : Bool :=
  if ∀ i, x i = true then true else if ∀ i, x i = false then false else q

theorem cel_all {n : Nat} (x : Fin n → Bool) (q y : Bool) (hn : 0 < n) (h : ∀ i, x i = y) :
    cel x q = y := by
  unfold cel
  cases y
  · have : ¬ ∀ i, x i = true := fun h' => by have := h' ⟨0, hn⟩; rw [h] at this; exact absurd this (by decide)
    rw [if_neg this, if_pos h]
  · rw [if_pos h]

theorem cel_hold {n : Nat} (x : Fin n → Bool) (q : Bool) (h : ∃ i, x i = q) : cel x q = q := by
  obtain ⟨i, hi⟩ := h
  unfold cel
  split
  · rename_i ha; rw [← hi, ha i]
  · split
    · rename_i _ hb; rw [← hi, hb i]
    · rfl

/-- **The n-input C-element as a counter** (E4; generalises `Events.maj_ph`).
If the feedback count `mq` is never ahead of an input phase and at most one
behind each, the element has fired exactly `min_i p i` times. -/
theorem cel_ph (v : Bool) (n : Nat) (hn : 0 < n) (p : Fin n → Nat) (mq : Nat)
    (h1 : ∀ i, mq ≤ p i) (h2 : ∀ i, p i ≤ mq + 1) :
    cel (fun i => ph v (p i)) (ph v mq) = ph v (fmin n p) := by
  by_cases hex : ∃ i, p i = mq
  · obtain ⟨i, hi⟩ := hex
    have hm : fmin n p = mq := by
      have := fmin_le n p i; have := le_fmin n p hn mq h1; omega
    rw [hm]; exact cel_hold _ _ ⟨i, by rw [hi]⟩
  · have hall : ∀ i, p i = mq + 1 := fun i => by
      have := h1 i; have := h2 i
      rcases Nat.lt_or_ge mq (p i) with h | h
      · omega
      · exact absurd ⟨i, by omega⟩ hex
    have hm : fmin n p = mq + 1 := by
      have := fmin_le n p ⟨0, hn⟩; have := hall ⟨0, hn⟩; have := le_fmin n p hn (mq + 1) (fun i => Nat.le_of_eq (hall i).symm); omega
    rw [hm]; exact cel_all _ _ _ hn (fun i => by rw [hall i])

/-- An inverter / bubble commutes with phases. -/
theorem ph_xor (i n v : Bool) (m : Nat) : ((i ^^ ph v m) ^^ n) = ph (v ^^ i ^^ n) m := by
  unfold ph; split <;> cases i <;> cases n <;> cases v <;> rfl

/-! ## Networks of C-elements with channel pins -/

/-- A network of `N` C-element stages. Pin `p : Fin (ar j)` of stage `j` reads
stage `src j p` through a channel that inverts iff `inv j p` (an environment
sender, or an odd buffer chain); the LUT reads that pin through a bubble iff
`neg j p`. The feedback `q` and the reset pin are implicit. -/
structure CNet (N : Nat) where
  /-- reset value of the stage (`_set` cells: true) -/
  v : Fin N → Bool
  /-- number of input pins (2 for `bd_c2*`, 3 for `bd_c3`, 4 for `bd_c4`) -/
  ar : Fin N → Nat
  ar_pos : ∀ j, 0 < ar j
  src : (j : Fin N) → Fin (ar j) → Fin N
  inv : (j : Fin N) → Fin (ar j) → Bool
  neg : (j : Fin N) → Fin (ar j) → Bool

namespace CNet
variable {N : Nat} (net : CNet N)

/-- Phase offset of pin `p` of stage `j` (the token on that arc of the
counter graph): 1 iff the pin, as the LUT sees it, starts opposite to `v j`. -/
def off (j : Fin N) (p : Fin (net.ar j)) : Nat :=
  offB (net.v (net.src j p) ^^ net.inv j p ^^ net.neg j p) (net.v j)

theorem off_le (j : Fin N) (p : Fin (net.ar j)) : net.off j p ≤ 1 := offB_le _ _

/-- The settled LUT function of a stage: reset value under reset, else the
C-element of the bubbled pins with the own feedback. -/
def lutF (j : Fin N) (x : Fin (net.ar j) → Bool) (q rst : Bool) : Bool :=
  if rst then net.v j else cel (fun p => x p ^^ net.neg j p) q

end CNet

/-- Delay bands (in steps): LUT, pin channel, own feedback. -/
structure Bands {N : Nat} (net : CNet N) where
  loF : Fin N → Nat
  hiF : Fin N → Nat
  loG : (j : Fin N) → Fin (net.ar j) → Nat
  hiG : (j : Fin N) → Fin (net.ar j) → Nat
  loQ : Fin N → Nat
  hiQ : Fin N → Nat

/-! ## Walks of the counter graph -/

/-- An arc of the counter graph, named by the pin that reads it. -/
abbrev Arc {N : Nat} (net : CNet N) := (k : Fin N) × Fin (net.ar k)

/-- `walkOK a b w`: following the pins of `w` upstream from `a` (each arc
`⟨k, p⟩` steps from `k` to `src k p`) reaches `b`. -/
def walkOK {N : Nat} (net : CNet N) : Fin N → Fin N → List (Arc net) → Bool
  | a, b, [] => a == b
  | a, b, ⟨k, p⟩ :: w => k == a && walkOK net (net.src k p) b w

/-- Tokens on a walk. -/
def wTok {N : Nat} (net : CNet N) : List (Arc net) → Nat
  | [] => 0
  | ⟨k, p⟩ :: w => net.off k p + wTok net w

/-- Fastest traversal of a walk (LUT + pin channel per arc). -/
def wLo {N : Nat} {net : CNet N} (b : Bands net) : List (Arc net) → Nat
  | [] => 0
  | ⟨k, p⟩ :: w => b.loF k + b.loG k p + wLo b w

/-- Slowest traversal of a walk. -/
def wHi {N : Nat} {net : CNet N} (b : Bands net) : List (Arc net) → Nat
  | [] => 0
  | ⟨k, p⟩ :: w => b.hiF k + b.hiG k p + wHi b w

/-- **Back** (decidable; replaces `Pairing ∧ Race`): for every pin `p` of `j`
a walk `back j p` from `src j p` upstream to `j`, carrying with the pin at
most one token, whose fastest traversal plus the pin channel is no faster
than `j`'s slowest own feedback. -/
def Back {N : Nat} {net : CNet N} (b : Bands net)
    (back : (j : Fin N) → Fin (net.ar j) → List (Arc net)) : Prop :=
  ∀ j p, walkOK net (net.src j p) j (back j p) = true ∧
    wTok net (back j p) + net.off j p ≤ 1 ∧ b.hiQ j ≤ b.loG j p + wLo b (back j p)

instance {N : Nat} {net : CNet N} (b : Bands net)
    (back : (j : Fin N) → Fin (net.ar j) → List (Arc net)) : Decidable (Back b back) := by
  unfold Back; exact inferInstance

/-! ## Behaviours -/

/-- A concrete behaviour: every LUT, pin channel and feedback a Discrete
transport (monotone warp) inside its band; any power-up; reset pins high at
0 and falling at most once. -/
structure Beh {N : Nat} (net : CNet N) (b : Bands net) where
  c : Fin N → Sig
  pin : (j : Fin N) → Fin (net.ar j) → Sig
  q : Fin N → Sig
  r : Fin N → Sig
  F : Fin N → Nat → Nat
  G : (j : Fin N) → Fin (net.ar j) → Nat → Nat
  Q : Fin N → Nat → Nat
  wF : ∀ j, Warp (b.loF j) (b.hiF j) (F j)
  wG : ∀ j p, Warp (b.loG j p) (b.hiG j p) (G j p)
  wQ : ∀ j, Warp (b.loQ j) (b.hiQ j) (Q j)
  loF1 : ∀ j, 1 ≤ b.loF j
  loG1 : ∀ j p, 1 ≤ b.loG j p
  loQ1 : ∀ j, 1 ≤ b.loQ j
  hc : ∀ j t, c j t = net.lutF j (fun p => pin j p (F j t)) (q j (F j t)) (r j (F j t))
  hpin : ∀ j p t, pin j p t = (net.inv j p ^^ c (net.src j p) (G j p t))
  hq : ∀ j t, q j t = c j (Q j t)
  r0 : ∀ j, r j 0 = true
  ranti : ∀ j a b, a ≤ b → r j b = true → r j a = true

namespace Beh
variable {N : Nat} {net : CNet N} {b : Bands net} (x : Beh net b)

theorem F_lt (j : Fin N) (t : Nat) (ht : 1 ≤ t) : x.F j t < t := by
  have := (x.wF j).le_late t; have := x.loF1 j; omega

theorem G_lt (j : Fin N) (p : Fin (net.ar j)) (t : Nat) (ht : 1 ≤ t) : x.G j p t < t := by
  have := (x.wG j p).le_late t; have := x.loG1 j p; omega

theorem Q_lt (j : Fin N) (t : Nat) (ht : 1 ≤ t) : x.Q j t < t := by
  have := (x.wQ j).le_late t; have := x.loQ1 j; omega

theorem F_zero (j : Fin N) : x.F j 0 = 0 := by have := (x.wF j).le_late 0; omega

/-- **The counts**: the min-plus counter recursion over the behaviour's warps. -/
def M (t : Nat) (j : Fin N) : Nat :=
  if h : x.F j t < t then
    if x.r j (x.F j t) then 0 else
      fmin (net.ar j) (fun p =>
        if h' : x.G j p (x.F j t) < x.F j t then
          M (x.G j p (x.F j t)) (net.src j p) + net.off j p else 0)
  else 0
termination_by t

/-- Phase count of pin `p` of stage `j` at LUT sample time `s`. -/
def P (j : Fin N) (p : Fin (net.ar j)) (s : Nat) : Nat :=
  x.M (x.G j p s) (net.src j p) + net.off j p

/-- Count of the LUT function at time `s`. -/
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
      rw [dif_pos (x.G_lt j p _ hs)]; rfl
  · have : t = 0 := by omega
    subst this
    rw [dif_neg (by rw [x.F_zero]; exact Nat.lt_irrefl 0)]
    unfold E; rw [x.F_zero, x.r0]; simp

theorem E_zero (j : Fin N) : x.E j 0 = 0 := by unfold E; rw [x.r0]; simp

theorem M_zero (j : Fin N) : x.M 0 j = 0 := by rw [M_eq, F_zero, E_zero]

/-- Counts are monotone in time. -/
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
          have hG := (x.wG j p).mono _ _ hFa
          have hGn := x.G_lt j p _ (x.hs1 j _ hrn)
          have := ih (x.G j p (x.F j n)) (by omega) (net.src j p) _ hG
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
      have := x.M_mono (x.G j p s) (net.src j p) _ ((x.wG j p).mono _ _ h)
      omega

/-- Min-plus upper bound through one pin. -/
theorem M_le_pin (k : Fin N) (p : Fin (net.ar k)) (u : Nat) :
    x.M u k ≤ x.M (x.G k p (x.F k u)) (net.src k p) + net.off k p := by
  rw [x.M_eq]; unfold E
  by_cases hr : x.r k (x.F k u) = true
  · simp [hr]
  · simp only [hr, ite_false, Bool.false_eq_true]
    exact fmin_le _ _ p

/-- **Walk bound.** Along a walk upstream from `a` to `b`, the count of `a`
is at most the count of `b` read `wLo` steps earlier plus the walk's tokens. -/
theorem walk_le : ∀ (w : List (Arc net)) (a bb : Fin N), walkOK net a bb w = true →
    ∀ u, x.M u a ≤ x.M (u - wLo b w) bb + wTok net w
  | [], a, bb, h, u => by
      simp only [walkOK, beq_iff_eq] at h; subst h; simp [wLo, wTok]
  | ⟨k, p⟩ :: w, a, bb, h, u => by
      simp only [walkOK, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨hk, hw⟩ := h
      subst hk
      have h1 := x.M_le_pin k p u
      have h2 := walk_le w (net.src k p) bb hw (x.G k p (x.F k u))
      have a1 := (x.wF k).le_late u
      have a2 := (x.wG k p).le_late (x.F k u)
      have h3 := x.M_mono (u - wLo b (⟨k, p⟩ :: w)) bb (x.G k p (x.F k u) - wLo b w)
        (by simp only [wLo]; omega)
      simp only [wTok]
      omega

/-- **Neighbour bound** from `Back`: every pin phase is at most one ahead of
the stage's own fed-back count. -/
theorem pin_le_q {back : (j : Fin N) → Fin (net.ar j) → List (Arc net)} (hB : Back b back)
    (j : Fin N) (p : Fin (net.ar j)) (s : Nat) : x.P j p s ≤ x.M (x.Q j s) j + 1 := by
  obtain ⟨hw, htok, hrace⟩ := hB j p
  unfold P
  have h1 := x.walk_le (back j p) _ _ hw (x.G j p s)
  have a1 := (x.wG j p).le_late s
  have a4 := (x.wQ j).early_le s
  have := x.M_mono (x.Q j s) j (x.G j p s - wLo b (back j p)) (by omega)
  omega

theorem q_le_E (j : Fin N) (s : Nat) : x.M (x.Q j s) j ≤ x.E j s := by
  rw [x.M_eq]
  apply x.E_mono
  have a1 := (x.wF j).le_late (x.Q j s)
  have a2 := (x.wQ j).le_late s
  omega

/-- **Soundness of the counter domain for open nets, n-input C-elements and
channel pins.** Under `Back`, every node of every behaviour equals its reset
value flipped `M t j` times, at every time: no glitch, no X, ever. -/
theorem safe {back : (j : Fin N) → Fin (net.ar j) → List (Arc net)} (hB : Back b back) :
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
        rw [x.hpin j p s, ih _ (Nat.lt_trans (x.G_lt j p s hs1) hst), ph_xor]
        unfold P CNet.off
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

end Beh

end Formal.Core.XAudit.Events2
