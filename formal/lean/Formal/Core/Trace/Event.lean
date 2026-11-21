import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Trace representation (b): event lists

Track 2, probe "event lists" (see `formal/notes/A-trace-event.md`).

A binary signal is an initial value (the value at `-∞`) plus a finite,
strictly increasing list of transition times in `ℝ`. Since `Val = Bool`,
every transition is a toggle, so an event carries only its time. The value at
time `t` counts the transitions at times `≤ t` (right-continuous: the new
value holds from the transition instant on).

Finite variability is built in (a list is finite) — in fact the type only
contains signals with finitely many transitions in *total*, which is stronger
than non-Zeno; see the notes.
-/

namespace Formal.Core.TraceEvent

noncomputable section

/-! ## B0: definitions -/

/-- Parity of the number of events at or before `t`. Works for any (also
unsorted) list; for sorted lists it is the usual toggle count. -/
def flips : List ℝ → ℝ → Bool
  | [], _ => false
  | e :: es, t => xor (decide (e ≤ t)) (flips es t)

/-- A binary signal: initial value plus strictly increasing transition times. -/
structure Sig where
  init : Bool
  evs : List ℝ
  sorted : evs.Pairwise (· < ·)

/-- The value of a signal at time `t`. -/
def Sig.val (s : Sig) (t : ℝ) : Bool := xor s.init (flips s.evs t)

/-- The constant signal. -/
def const (v : Bool) : Sig := ⟨v, [], List.Pairwise.nil⟩

theorem const_val (v : Bool) (t : ℝ) : (const v).val t = v := by
  simp [const, Sig.val, flips]

theorem xor_cancel {a b c : Bool} (h : xor a b = xor a c) : b = c := by
  cases a <;> cases b <;> cases c <;> simp_all

theorem flips_of_lt {l : List ℝ} {t : ℝ} (h : ∀ e ∈ l, t < e) : flips l t = false := by
  induction l with
  | nil => rfl
  | cons e es ih =>
    have h1 : ¬ e ≤ t := not_le.mpr (h e (by simp))
    simp only [flips, ih (fun x hx => h x (by simp [hx]))]
    simp [h1]

theorem flips_head {e : ℝ} {es : List ℝ} (h : (e :: es).Pairwise (· < ·)) :
    flips (e :: es) e = true := by
  have hes : ∀ x ∈ es, e < x := (List.pairwise_cons.mp h).1
  simp [flips, flips_of_lt hes]

/-- Toggles commute: the order of two raw events does not matter. -/
theorem flips_swap (b c : ℝ) (l : List ℝ) (t : ℝ) :
    flips (b :: c :: l) t = flips (c :: b :: l) t := by
  simp only [flips]
  cases decide (b ≤ t) <;> cases decide (c ≤ t) <;> simp

/-- Two coincident raw events cancel. -/
theorem flips_dup (c : ℝ) (l : List ℝ) (t : ℝ) : flips (c :: c :: l) t = flips l t := by
  simp only [flips]
  cases decide (c ≤ t) <;> simp

/-- Sorted toggle lists are determined by their parity function. -/
theorem flips_inj : ∀ {l₁ l₂ : List ℝ}, l₁.Pairwise (· < ·) → l₂.Pairwise (· < ·) →
    (∀ t, flips l₁ t = flips l₂ t) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], f :: fs, _, h2, h => by
      have := h f; rw [flips_head h2] at this; simp [flips] at this
  | e :: es, [], h1, _, h => by
      have := h e; rw [flips_head h1] at this; simp [flips] at this
  | e :: es, f :: fs, h1, h2, h => by
      have he : e = f := by
        rcases lt_trichotomy e f with hlt | heq | hgt
        · exfalso
          have := h e
          rw [flips_head h1, flips_of_lt] at this
          · simp at this
          · intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · exact hlt
            · exact lt_trans hlt ((List.pairwise_cons.mp h2).1 x hx)
        · exact heq
        · exfalso
          have := h f
          rw [flips_head h2, flips_of_lt] at this
          · simp at this
          · intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · exact hgt
            · exact lt_trans hgt ((List.pairwise_cons.mp h1).1 x hx)
      subst he
      have hrest : es = fs :=
        flips_inj (List.pairwise_cons.mp h1).2 (List.pairwise_cons.mp h2).2
          (fun t => xor_cancel (by have := h t; simpa only [flips] using this))
      rw [hrest]

theorem exists_lt_all (l : List ℝ) : ∃ t, ∀ e ∈ l, t < e := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons e es ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨min t (e - 1), ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · have := min_le_right t (x - 1); linarith
    · have := min_le_left t (e - 1); have := ht x hx; linarith

/-- Canonicity: two signals with the same value at every time are equal. -/
theorem Sig.ext_val {s s' : Sig} (h : ∀ t, s.val t = s'.val t) : s = s' := by
  obtain ⟨t, ht⟩ := exists_lt_all (s.evs ++ s'.evs)
  have hi : s.init = s'.init := by
    have := h t
    simpa [Sig.val, flips_of_lt (fun e he => ht e (List.mem_append_left _ he)),
      flips_of_lt (fun e he => ht e (List.mem_append_right _ he))] using this
  have hf : ∀ t, flips s.evs t = flips s'.evs t := by
    intro t
    have := h t
    simp only [Sig.val, hi] at this
    exact xor_cancel this
  have he := flips_inj s.sorted s'.sorted hf
  obtain ⟨i, l, hl⟩ := s
  obtain ⟨i', l', hl'⟩ := s'
  simp only at hi he
  subst hi he
  rfl

/-! ## B1: fixed pure delay -/

theorem pairwise_map_add (d : ℝ) {l : List ℝ} (h : l.Pairwise (· < ·)) :
    (l.map (· + d)).Pairwise (· < ·) := by
  rw [List.pairwise_map]
  exact h.imp (fun hab => by linarith)

/-- Pure delay by `d` (meaningful for `d ≥ 0`; the algebra holds for all `d`). -/
def delay (d : ℝ) (s : Sig) : Sig := ⟨s.init, s.evs.map (· + d), pairwise_map_add d s.sorted⟩

theorem flips_map_add (d t : ℝ) (l : List ℝ) : flips (l.map (· + d)) t = flips l (t - d) := by
  induction l with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map, flips, ih]
    congr 1
    exact decide_eq_decide.mpr ⟨fun h => by linarith, fun h => by linarith⟩

/-- `out(t) = in(t - d)`. -/
theorem delay_val (d : ℝ) (s : Sig) (t : ℝ) : (delay d s).val t = s.val (t - d) := by
  simp [delay, Sig.val, flips_map_add]

theorem delay_delay (d₁ d₂ : ℝ) (s : Sig) : delay d₂ (delay d₁ s) = delay (d₁ + d₂) s := by
  simp [delay, List.map_map, Function.comp_def, add_assoc]

theorem delay_zero (s : Sig) : delay 0 s = s := by
  simp [delay]

/-! ## B2: bounded transport delay as a relation -/

/-- `Within lo hi l l'`: `l'` is `l` with the `i`-th event moved later by a
delay in `[lo, hi]`, one-to-one, in order. -/
def Within (lo hi : ℝ) : List ℝ → List ℝ → Prop
  | [], [] => True
  | a :: as, b :: bs => (lo ≤ b - a ∧ b - a ≤ hi) ∧ Within lo hi as bs
  | _, _ => False

theorem Within.trans {lo₁ hi₁ lo₂ hi₂ : ℝ} :
    ∀ {l₁ l₂ l₃ : List ℝ}, Within lo₁ hi₁ l₁ l₂ → Within lo₂ hi₂ l₂ l₃ →
      Within (lo₁ + lo₂) (hi₁ + hi₂) l₁ l₃
  | [], [], [], _, _ => trivial
  | a :: as, b :: bs, c :: cs, h, h' => by
      simp only [Within] at h h' ⊢
      exact ⟨⟨by linarith, by linarith⟩, Within.trans h.2 h'.2⟩
  | [], [], _ :: _, _, h' => by simp [Within] at h'
  | [], _ :: _, _, h, _ => by simp [Within] at h
  | _ :: _, [], _, h, _ => by simp [Within] at h
  | _ :: _, _ :: _, [], _, h' => by simp [Within] at h'

theorem Within.mono {lo hi lo' hi' : ℝ} (hlo : lo' ≤ lo) (hhi : hi ≤ hi') :
    ∀ {l l' : List ℝ}, Within lo hi l l' → Within lo' hi' l l'
  | [], [], _ => trivial
  | a :: as, b :: bs, h => by
      simp only [Within] at h ⊢
      exact ⟨⟨by linarith, by linarith⟩, Within.mono hlo hhi h.2⟩
  | [], _ :: _, h => by simp [Within] at h
  | _ :: _, [], h => by simp [Within] at h

theorem within_map (d : ℝ) : ∀ l : List ℝ, Within d d l (l.map (· + d))
  | [] => trivial
  | a :: as => by
      simp only [Within, List.map]
      exact ⟨⟨by linarith, by linarith⟩, within_map d as⟩

theorem Within.eq_map {d : ℝ} : ∀ {l l' : List ℝ}, Within d d l l' → l' = l.map (· + d)
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
      simp only [Within] at h
      simp only [List.map, Within.eq_map h.2, List.cons.injEq, and_true]
      linarith [h.1.1, h.1.2]
  | [], _ :: _, h => by simp [Within] at h
  | _ :: _, [], h => by simp [Within] at h

/-- Bounded transport channel: same initial value, every input transition
appears at the output after a delay in `[lo, hi]`, order preserved (the output
list is strictly sorted), no other output transitions. -/
def Chan (lo hi : ℝ) (x y : Sig) : Prop := y.init = x.init ∧ Within lo hi x.evs y.evs

theorem Chan.comp {lo₁ hi₁ lo₂ hi₂ : ℝ} {x y z : Sig}
    (h₁ : Chan lo₁ hi₁ x y) (h₂ : Chan lo₂ hi₂ y z) : Chan (lo₁ + lo₂) (hi₁ + hi₂) x z :=
  ⟨h₂.1.trans h₁.1, h₁.2.trans h₂.2⟩

theorem Chan.mono {lo hi lo' hi' : ℝ} {x y : Sig} (hlo : lo' ≤ lo) (hhi : hi ≤ hi')
    (h : Chan lo hi x y) : Chan lo' hi' x y :=
  ⟨h.1, h.2.mono hlo hhi⟩

/-- The degenerate channel `[d, d]` is exactly the pure delay. -/
theorem chan_point_iff (d : ℝ) (x y : Sig) : Chan d d x y ↔ y = delay d x := by
  constructor
  · rintro ⟨hi, hw⟩
    obtain ⟨i, l, hl⟩ := y
    simp only at hi hw
    have := hw.eq_map
    subst hi this
    rfl
  · rintro rfl
    exact ⟨rfl, within_map d x.evs⟩

/-- The channel is total: every input has some output (e.g. the delay `lo`). -/
theorem Chan.total {lo hi : ℝ} (h : lo ≤ hi) (x : Sig) : ∃ y, Chan lo hi x y :=
  ⟨delay lo x, Chan.mono le_rfl h ((chan_point_iff lo x _).mpr rfl)⟩

theorem Within.flips_stable {lo hi t : ℝ} :
    ∀ {l l' : List ℝ}, Within lo hi l l' → (∀ e ∈ l, e < t - hi ∨ t - lo < e) →
      flips l' t = flips l (t - lo)
  | [], [], _, _ => rfl
  | a :: as, b :: bs, h, hs => by
      simp only [Within] at h
      simp only [flips, Within.flips_stable h.2 (fun e he => hs e (by simp [he]))]
      congr 1
      rcases hs a (by simp) with ha | ha
      · simp only [decide_eq_decide]; constructor <;> intro <;> linarith [h.1.1, h.1.2]
      · simp only [decide_eq_decide]; constructor <;> intro <;> linarith [h.1.1, h.1.2]
  | [], _ :: _, h, _ => by simp [Within] at h
  | _ :: _, [], h, _ => by simp [Within] at h

/-- Settled output: if no input transition lies in the window `[t-hi, t-lo]`,
the output at `t` equals the input at `t - lo` (equivalently at any time in the
window). This is the lemma circuit proofs use to read a gate's output. -/
theorem Chan.val_stable {lo hi t : ℝ} {x y : Sig} (h : Chan lo hi x y)
    (hs : ∀ e ∈ x.evs, e < t - hi ∨ t - lo < e) : y.val t = x.val (t - lo) := by
  simp [Sig.val, h.1, h.2.flips_stable hs]

/-! ## B3: pulses through a transport channel -/

/-- A pulse: starts at `v`, toggles at `a` and back at `a + w`. -/
def pulse (v : Bool) (a w : ℝ) (hw : 0 < w) : Sig :=
  ⟨v, [a, a + w], by simp; linarith⟩

/-- Pulse width through an order-preserving `[lo, hi]` channel: the output is a
pulse of width `w' ∈ [w - (hi-lo), w + (hi-lo)]`, and `w' > 0` (never lost). -/
theorem chan_pulse {lo hi a w : ℝ} {v : Bool} {hw : 0 < w} {y : Sig}
    (h : Chan lo hi (pulse v a w hw) y) :
    ∃ b w', y.init = v ∧ y.evs = [b, b + w'] ∧ lo ≤ b - a ∧ b - a ≤ hi ∧
      0 < w' ∧ w - (hi - lo) ≤ w' ∧ w' ≤ w + (hi - lo) := by
  obtain ⟨hi0, hwi⟩ := h
  obtain ⟨i, l, hl⟩ := y
  simp only [pulse] at hi0 hwi ⊢
  match l, hl, hwi with
  | [b, c], hl, hwi =>
    simp only [Within] at hwi
    have hbc : b < c := by simpa using hl
    refine ⟨b, c - b, hi0, by simp, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith [hwi.1.1, hwi.1.2, hwi.2.1.1, hwi.2.1.2]
  | [], _, hwi => simp [Within] at hwi
  | [_], _, hwi => simp [Within] at hwi
  | _ :: _ :: _ :: _, _, hwi => simp [Within] at hwi

/-- Crossing-permitting transport channel: each input event is moved by a
delay in `[lo, hi]` independently (the raw list need not be sorted), and the
output is the toggle-parity of the raw events. Coincident events cancel,
crossed events commute. -/
def ChanX (lo hi : ℝ) (x y : Sig) : Prop :=
  ∃ raw : List ℝ, Within lo hi x.evs raw ∧ ∀ t, y.val t = xor x.init (flips raw t)

theorem Chan.toX {lo hi : ℝ} {x y : Sig} (h : Chan lo hi x y) : ChanX lo hi x y :=
  ⟨y.evs, h.2, fun t => by simp [Sig.val, h.1]⟩

theorem ChanX.mono {lo hi lo' hi' : ℝ} {x y : Sig} (hlo : lo' ≤ lo) (hhi : hi ≤ hi')
    (h : ChanX lo hi x y) : ChanX lo' hi' x y := by
  obtain ⟨raw, hw, hv⟩ := h
  exact ⟨raw, hw.mono hlo hhi, hv⟩

/-- If `w ≤ hi - lo` the crossing-permitting channel can swallow the pulse. -/
theorem chanX_pulse_lost {lo hi a w : ℝ} {v : Bool} (hw : 0 < w) (hshort : w ≤ hi - lo) :
    ChanX lo hi (pulse v a w hw) (const v) := by
  refine ⟨[a + hi, a + hi], ?_, ?_⟩
  · simp only [pulse, Within]
    refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, trivial⟩
  · intro t
    simp [const_val, pulse, flips]

/-- If `w > hi - lo` the pulse always survives the crossing-permitting channel. -/
theorem chanX_pulse_kept {lo hi a w : ℝ} {v : Bool} {hw : 0 < w} {y : Sig}
    (hlong : hi - lo < w) (h : ChanX lo hi (pulse v a w hw) y) : ∃ t, y.val t ≠ v := by
  obtain ⟨raw, hwi, hval⟩ := h
  match raw, hwi with
  | [b, c], hwi =>
    simp only [pulse, Within] at hwi
    have hbc : ¬ c ≤ b := by linarith [hwi.1.1, hwi.1.2, hwi.2.1.1, hwi.2.1.2]
    refine ⟨b, ?_⟩
    rw [hval b]
    simp [pulse, flips, hbc]
  | [], hwi => simp [pulse, Within] at hwi
  | [_], hwi => simp [pulse, Within] at hwi
  | _ :: _ :: _ :: _, hwi => simp [pulse, Within] at hwi

/-! ## B4: inertial delay -/

/-- Inertial delay `δ` on a sorted event list (VHDL `inertial` with reject
limit `δ`): an event followed by the next one less than `δ` later forms a
pulse that is swallowed (both events removed); otherwise it is propagated
`δ` later. -/
def inert (δ : ℝ) : List ℝ → List ℝ
  | [] => []
  | [e] => [e + δ]
  | e :: e' :: rest => if e' - e < δ then inert δ rest else (e + δ) :: inert δ (e' :: rest)
termination_by l => l.length

theorem inert_sublist (δ : ℝ) : ∀ l : List ℝ, (inert δ l).Sublist (l.map (· + δ))
  | [] => by simp [inert]
  | [e] => by simp [inert]
  | e :: e' :: rest => by
      rw [inert]
      split
      · exact ((inert_sublist δ rest).cons _).cons _
      · exact (inert_sublist δ (e' :: rest)).cons_cons _
termination_by l => l.length

/-- Inertial delay of a signal. -/
def inertial (δ : ℝ) (s : Sig) : Sig :=
  ⟨s.init, inert δ s.evs, List.Pairwise.sublist (inert_sublist δ s.evs) (pairwise_map_add δ s.sorted)⟩

/-- Inertial delay never invents transitions: its output events are a
subsequence of the input events delayed by `δ`. -/
theorem inertial_sub (δ : ℝ) (s : Sig) : (inertial δ s).evs.Sublist (delay δ s).evs :=
  inert_sublist δ s.evs

/-- A pulse shorter than `δ` produces no output transition. -/
theorem inertial_short {δ a w : ℝ} {v : Bool} (hw : 0 < w) (h : w < δ) :
    inertial δ (pulse v a w hw) = const v := by
  have : a + w - a < δ := by linarith
  simp [inertial, pulse, inert, const, h]

/-- A pulse of width at least `δ` is propagated, delayed by `δ`. -/
theorem inertial_long {δ a w : ℝ} {v : Bool} (hw : 0 < w) (h : δ ≤ w) :
    inertial δ (pulse v a w hw) = delay δ (pulse v a w hw) := by
  have : ¬ a + w - a < δ := by linarith
  simp [inertial, pulse, inert, delay, h]

/-- Consecutive events at least `δ` apart. -/
def Spaced (δ : ℝ) : List ℝ → Prop
  | e :: e' :: rest => δ ≤ e' - e ∧ Spaced δ (e' :: rest)
  | _ => True

theorem inert_spaced (δ : ℝ) : ∀ l : List ℝ, Spaced δ l → inert δ l = l.map (· + δ)
  | [], _ => by simp [inert]
  | [e], _ => by simp [inert]
  | e :: e' :: rest, h => by
      simp only [Spaced] at h
      have : ¬ e' - e < δ := not_lt.mpr h.1
      rw [inert]
      simp only [this, ↓reduceIte, inert_spaced δ (e' :: rest) h.2, List.map]
termination_by l => l.length

/-- If all input pulses are at least `δ` wide, inertial delay is pure delay. -/
theorem inertial_spaced {δ : ℝ} {s : Sig} (h : Spaced δ s.evs) : inertial δ s = delay δ s := by
  simp [inertial, delay, inert_spaced δ s.evs h]

/-! ## Zero-delay gates on event lists (merge) -/

/-- Emit a transition at `e` iff the gate output changes from `o` to `n`. -/
def emit (e : ℝ) (o n : Bool) (r : List ℝ) : List ℝ := if o = n then r else e :: r

theorem mem_emit {e x : ℝ} {o n : Bool} {r : List ℝ} (h : x ∈ emit e o n r) : x = e ∨ x ∈ r := by
  unfold emit at h; split at h
  · exact Or.inr h
  · exact List.mem_cons.mp h

theorem pairwise_emit {e : ℝ} {o n : Bool} {r : List ℝ} (hr : r.Pairwise (· < ·))
    (he : ∀ y ∈ r, e < y) : (emit e o n r).Pairwise (· < ·) := by
  unfold emit; split
  · exact hr
  · exact List.pairwise_cons.mpr ⟨he, hr⟩

theorem xor_emit (e : ℝ) (o n : Bool) (r : List ℝ) (t : ℝ) :
    xor o (flips (emit e o n r) t) = xor (if e ≤ t then n else o) (flips r t) := by
  unfold emit
  cases o <;> cases n <;> by_cases het : e ≤ t <;> simp [flips, het]

/-- Zero-delay 2-input gate on event lists: merge the input transitions,
emit an output transition exactly when the gate value changes. -/
def gateEv (g : Bool → Bool → Bool) : Bool → Bool → List ℝ → List ℝ → List ℝ
  | _, _, [], [] => []
  | va, vb, e :: es, [] => emit e (g va vb) (g (!va) vb) (gateEv g (!va) vb es [])
  | va, vb, [], f :: fs => emit f (g va vb) (g va (!vb)) (gateEv g va (!vb) [] fs)
  | va, vb, e :: es, f :: fs =>
      if e < f then emit e (g va vb) (g (!va) vb) (gateEv g (!va) vb es (f :: fs))
      else if f < e then emit f (g va vb) (g va (!vb)) (gateEv g va (!vb) (e :: es) fs)
      else emit e (g va vb) (g (!va) (!vb)) (gateEv g (!va) (!vb) es fs)
termination_by _ _ la lb => la.length + lb.length

theorem mem_gateEv (g : Bool → Bool → Bool) : ∀ (va vb : Bool) (la lb : List ℝ) (x : ℝ),
    x ∈ gateEv g va vb la lb → x ∈ la ∨ x ∈ lb
  | _, _, [], [], x, h => by simp [gateEv] at h
  | va, vb, e :: es, [], x, h => by
      rw [gateEv] at h
      rcases mem_emit h with rfl | h
      · simp
      · rcases mem_gateEv g _ _ es [] x h with h | h <;> simp_all
  | va, vb, [], f :: fs, x, h => by
      rw [gateEv] at h
      rcases mem_emit h with rfl | h
      · simp
      · rcases mem_gateEv g _ _ [] fs x h with h | h <;> simp_all
  | va, vb, e :: es, f :: fs, x, h => by
      rw [gateEv] at h
      split_ifs at h
      · rcases mem_emit h with rfl | h
        · simp
        · rcases mem_gateEv g _ _ es (f :: fs) x h with h | h <;> simp_all
      · rcases mem_emit h with rfl | h
        · simp
        · rcases mem_gateEv g _ _ (e :: es) fs x h with h | h <;> simp_all
      · rcases mem_emit h with rfl | h
        · simp
        · rcases mem_gateEv g _ _ es fs x h with h | h <;> simp_all
termination_by _ _ la lb => la.length + lb.length

theorem gateEv_sorted (g : Bool → Bool → Bool) : ∀ (va vb : Bool) (la lb : List ℝ),
    la.Pairwise (· < ·) → lb.Pairwise (· < ·) → (gateEv g va vb la lb).Pairwise (· < ·)
  | _, _, [], [], _, _ => by simp [gateEv]
  | va, vb, e :: es, [], ha, hb => by
      rw [gateEv]
      have ha' := List.pairwise_cons.mp ha
      refine pairwise_emit (gateEv_sorted g _ _ es [] ha'.2 hb) (fun y hy => ?_)
      rcases mem_gateEv g _ _ _ _ y hy with h | h
      · exact ha'.1 y h
      · simp at h
  | va, vb, [], f :: fs, ha, hb => by
      rw [gateEv]
      have hb' := List.pairwise_cons.mp hb
      refine pairwise_emit (gateEv_sorted g _ _ [] fs ha hb'.2) (fun y hy => ?_)
      rcases mem_gateEv g _ _ _ _ y hy with h | h
      · simp at h
      · exact hb'.1 y h
  | va, vb, e :: es, f :: fs, ha, hb => by
      have ha' := List.pairwise_cons.mp ha
      have hb' := List.pairwise_cons.mp hb
      rw [gateEv]
      split_ifs with h1 h2
      · refine pairwise_emit (gateEv_sorted g _ _ es (f :: fs) ha'.2 hb) (fun y hy => ?_)
        rcases mem_gateEv g _ _ _ _ y hy with h | h
        · exact ha'.1 y h
        · rcases List.mem_cons.mp h with rfl | h
          · exact h1
          · exact lt_trans h1 (hb'.1 y h)
      · refine pairwise_emit (gateEv_sorted g _ _ (e :: es) fs ha hb'.2) (fun y hy => ?_)
        rcases mem_gateEv g _ _ _ _ y hy with h | h
        · rcases List.mem_cons.mp h with rfl | h
          · exact h2
          · exact lt_trans h2 (ha'.1 y h)
        · exact hb'.1 y h
      · have hef : e = f := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
        subst hef
        refine pairwise_emit (gateEv_sorted g _ _ es fs ha'.2 hb'.2) (fun y hy => ?_)
        rcases mem_gateEv g _ _ _ _ y hy with h | h
        · exact ha'.1 y h
        · exact hb'.1 y h
termination_by _ _ la lb => la.length + lb.length

theorem xor_not_flip (a b : Bool) : xor a (!b) = xor (!a) b := by cases a <;> cases b <;> rfl

theorem gateEv_val (g : Bool → Bool → Bool) : ∀ (va vb : Bool) (la lb : List ℝ),
    la.Pairwise (· < ·) → lb.Pairwise (· < ·) → ∀ t,
    xor (g va vb) (flips (gateEv g va vb la lb) t) = g (xor va (flips la t)) (xor vb (flips lb t))
  | _, _, [], [], _, _, t => by simp [gateEv, flips]
  | va, vb, e :: es, [], ha, hb, t => by
      have ha' := List.pairwise_cons.mp ha
      have ih := gateEv_val g (!va) vb es [] ha'.2 hb t
      rw [gateEv, xor_emit]
      by_cases het : e ≤ t
      · simp only [het, ite_true, ih, flips, decide_true, Bool.true_xor, xor_not_flip]
      · have h0 : flips (gateEv g (!va) vb es []) t = false := flips_of_lt (fun y hy => by
          rcases mem_gateEv g _ _ _ _ y hy with h | h
          · exact lt_trans (not_le.mp het) (ha'.1 y h)
          · simp at h)
        have h1 : flips es t = false := flips_of_lt (fun y hy => lt_trans (not_le.mp het) (ha'.1 y hy))
        simp [het, h0, h1, flips]
  | va, vb, [], f :: fs, ha, hb, t => by
      have hb' := List.pairwise_cons.mp hb
      have ih := gateEv_val g va (!vb) [] fs ha hb'.2 t
      rw [gateEv, xor_emit]
      by_cases hft : f ≤ t
      · simp only [hft, ite_true, ih, flips, decide_true, Bool.true_xor, xor_not_flip]
      · have h0 : flips (gateEv g va (!vb) [] fs) t = false := flips_of_lt (fun y hy => by
          rcases mem_gateEv g _ _ _ _ y hy with h | h
          · simp at h
          · exact lt_trans (not_le.mp hft) (hb'.1 y h))
        have h1 : flips fs t = false := flips_of_lt (fun y hy => lt_trans (not_le.mp hft) (hb'.1 y hy))
        simp [hft, h0, h1, flips]
  | va, vb, e :: es, f :: fs, ha, hb, t => by
      have ha' := List.pairwise_cons.mp ha
      have hb' := List.pairwise_cons.mp hb
      rw [gateEv]
      split_ifs with h1 h2
      · have ih := gateEv_val g (!va) vb es (f :: fs) ha'.2 hb t
        rw [xor_emit]
        by_cases het : e ≤ t
        · simp only [het, ite_true, ih, flips, decide_true, Bool.true_xor, xor_not_flip]
        · have h0 : flips (gateEv g (!va) vb es (f :: fs)) t = false := flips_of_lt (fun y hy => by
            rcases mem_gateEv g _ _ _ _ y hy with h | h
            · exact lt_trans (not_le.mp het) (ha'.1 y h)
            · rcases List.mem_cons.mp h with rfl | h
              · exact lt_trans (not_le.mp het) h1
              · exact lt_trans (not_le.mp het) (lt_trans h1 (hb'.1 y h)))
          have h3 : flips es t = false :=
            flips_of_lt (fun y hy => lt_trans (not_le.mp het) (ha'.1 y hy))
          have h4 : flips (f :: fs) t = false := flips_of_lt (fun y hy => by
            rcases List.mem_cons.mp hy with rfl | h
            · exact lt_trans (not_le.mp het) h1
            · exact lt_trans (not_le.mp het) (lt_trans h1 (hb'.1 y h)))
          simp only [flips] at h4
          simp [het, h0, h3, h4, flips]
      · have ih := gateEv_val g va (!vb) (e :: es) fs ha hb'.2 t
        rw [xor_emit]
        by_cases hft : f ≤ t
        · simp only [hft, ite_true, ih, flips, decide_true, Bool.true_xor, xor_not_flip]
        · have h0 : flips (gateEv g va (!vb) (e :: es) fs) t = false := flips_of_lt (fun y hy => by
            rcases mem_gateEv g _ _ _ _ y hy with h | h
            · rcases List.mem_cons.mp h with rfl | h
              · exact lt_trans (not_le.mp hft) h2
              · exact lt_trans (not_le.mp hft) (lt_trans h2 (ha'.1 y h))
            · exact lt_trans (not_le.mp hft) (hb'.1 y h))
          have h3 : flips fs t = false :=
            flips_of_lt (fun y hy => lt_trans (not_le.mp hft) (hb'.1 y hy))
          have h4 : flips (e :: es) t = false := flips_of_lt (fun y hy => by
            rcases List.mem_cons.mp hy with rfl | h
            · exact lt_trans (not_le.mp hft) h2
            · exact lt_trans (not_le.mp hft) (lt_trans h2 (ha'.1 y h)))
          simp only [flips] at h4
          simp [hft, h0, h3, h4, flips]
      · have hef : e = f := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
        subst hef
        have ih := gateEv_val g (!va) (!vb) es fs ha'.2 hb'.2 t
        rw [xor_emit]
        by_cases het : e ≤ t
        · simp only [het, ite_true, ih, flips, decide_true, Bool.true_xor, xor_not_flip]
        · have h0 : flips (gateEv g (!va) (!vb) es fs) t = false := flips_of_lt (fun y hy => by
            rcases mem_gateEv g _ _ _ _ y hy with h | h
            · exact lt_trans (not_le.mp het) (ha'.1 y h)
            · exact lt_trans (not_le.mp het) (hb'.1 y h))
          have h3 : flips es t = false :=
            flips_of_lt (fun y hy => lt_trans (not_le.mp het) (ha'.1 y hy))
          have h4 : flips fs t = false :=
            flips_of_lt (fun y hy => lt_trans (not_le.mp het) (hb'.1 y hy))
          simp [het, h0, h3, h4, flips]
termination_by _ _ la lb => la.length + lb.length

/-- The ideal zero-delay 2-input gate `g` on signals. -/
def gate (g : Bool → Bool → Bool) (a b : Sig) : Sig :=
  ⟨g a.init b.init, gateEv g a.init b.init a.evs b.evs,
    gateEv_sorted g a.init b.init a.evs b.evs a.sorted b.sorted⟩

theorem gate_val (g : Bool → Bool → Bool) (a b : Sig) (t : ℝ) :
    (gate g a b).val t = g (a.val t) (b.val t) :=
  gateEv_val g a.init b.init a.evs b.evs a.sorted b.sorted t

/-! ## B5: a gate as a relation, a circuit as a conjunction -/

/-- AND gate with a bounded transport output channel: there is an ideal
zero-delay AND signal `z`, and the output is `z` through `Chan lo hi`. -/
def AndGate (lo hi : ℝ) (a b y : Sig) : Prop :=
  ∃ z : Sig, (∀ t, z.val t = (a.val t && b.val t)) ∧ Chan lo hi z y

/-- The gate relation is exactly "ideal gate, then channel". -/
theorem andGate_iff {lo hi : ℝ} {a b y : Sig} :
    AndGate lo hi a b y ↔ Chan lo hi (gate (· && ·) a b) y := by
  constructor
  · rintro ⟨z, hz, hc⟩
    have : z = gate (· && ·) a b := Sig.ext_val (fun t => by rw [hz, gate_val])
    exact this ▸ hc
  · intro h
    exact ⟨_, fun t => gate_val _ a b t, h⟩

/-- The gate relation is total (never vacuous) when `lo ≤ hi`. -/
theorem AndGate.total {lo hi : ℝ} (h : lo ≤ hi) (a b : Sig) : ∃ y, AndGate lo hi a b y := by
  obtain ⟨y, hy⟩ := Chan.total h (gate (· && ·) a b)
  exact ⟨y, andGate_iff.mpr hy⟩

/-- With `b` held at 1, the output of `AND(a, b)` follows `a` within `[lo, hi]`. -/
theorem and_follows {lo hi : ℝ} {a b y : Sig} (hb : ∀ t, b.val t = true)
    (h : AndGate lo hi a b y) : Chan lo hi a y := by
  obtain ⟨z, hz, hc⟩ := h
  have : z = a := Sig.ext_val (fun t => by simp [hz, hb])
  exact this ▸ hc

/-- A two-gate circuit (conjunction of gate relations): `y₁ = AND(a, b)`,
`y₂ = AND(y₁, c)` with `b, c` held at 1. Then `y₂` follows `a` within the
summed window. -/
theorem and_chain {lo₁ hi₁ lo₂ hi₂ : ℝ} {a b c y₁ y₂ : Sig}
    (hb : ∀ t, b.val t = true) (hc : ∀ t, c.val t = true)
    (hckt : AndGate lo₁ hi₁ a b y₁ ∧ AndGate lo₂ hi₂ y₁ c y₂) :
    Chan (lo₁ + lo₂) (hi₁ + hi₂) a y₂ :=
  (and_follows hb hckt.1).comp (and_follows hc hckt.2)

end

end Formal.Core.TraceEvent
