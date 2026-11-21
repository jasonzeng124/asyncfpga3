/-!
# Track 2, representation (c): discrete-time traces

A signal is `ℕ → Bool`: its value at integer time steps (one step = a fixed
quantum, e.g. 1 ps). Delays are naturals. Lean core only (no Mathlib): every
proof is `omega` + case splits, and `decide` evaluates bounded checks in the
kernel.

Conventions (all modelling choices, stated once here and in
`formal/notes/A-trace-discrete.md`):
* Before time 0 every signal is constant at its time-0 value. This is exactly
  what truncated natural subtraction gives: `s (t - d)` reads `s 0` when
  `t < d`.
* A transition "at `t+1`" means `s (t+1) ≠ s t`. At most one transition per
  step, so finite variability (non-Zeno) holds by construction (B0).
* Bounded transport delay is a *monotone time warp* `o = i ∘ f` with
  `t - hi ≤ f t ≤ t - lo` (B2). Order of transitions is preserved, never
  crossed; two transitions whose delays make them land on the same step
  annihilate (that is how a short pulse is lost, B3).

Benchmark items B0..B5 of `bench.md` are marked below.
-/

namespace Formal.Core.TraceDiscrete

/-! ## B0: signals -/

/-- A discrete-time binary signal. `s t` is the value during step `t`. -/
abbrev Sig := Nat → Bool

/-- `s` has a transition entering step `t+1`. -/
def Tr (s : Sig) (t : Nat) : Prop := s (t + 1) ≠ s t

/-- Number of transitions entering steps `a+1 .. a+n`. -/
def trCount (s : Sig) (a n : Nat) : Nat :=
  ((List.range n).filter (fun k => s (a + k + 1) != s (a + k))).length

/-- B0 (finite variability / non-Zeno, for free): at most `n` transitions
in any window of `n` steps. No well-formedness side condition is needed. -/
theorem trCount_le (s : Sig) (a n : Nat) : trCount s a n ≤ n := by
  unfold trCount
  exact Nat.le_trans (List.length_filter_le _ _) (by simp)

/-- Discrete intermediate value theorem: a signal that differs at `a` and `b`
has a transition in between. Used everywhere below. -/
theorem exists_tr (s : Sig) (a : Nat) :
    ∀ b, a ≤ b → s a ≠ s b → ∃ u, a ≤ u ∧ u < b ∧ s (u + 1) ≠ s u := by
  intro b
  induction b with
  | zero =>
    intro h hne
    have : a = 0 := by omega
    subst this; exact absurd rfl hne
  | succ b ih =>
    intro hab hne
    by_cases hb : a ≤ b
    · by_cases h : s a = s b
      · exact ⟨b, hb, by omega, by rw [← h]; exact fun h' => hne h'.symm⟩
      · obtain ⟨u, h1, h2, h3⟩ := ih hb h
        exact ⟨u, h1, by omega, h3⟩
    · have : a = b + 1 := by omega
      subst this; exact absurd rfl hne

/-- Least element of a nonempty set of naturals (core has no `Nat.find`
without Mathlib's `Mathlib.Data.Nat.Find`, which is not built here). -/
theorem exists_least (P : Nat → Prop) (h : ∃ n, P n) :
    ∃ n, P n ∧ ∀ m, m < n → ¬ P m := by
  obtain ⟨n, hn⟩ := h
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hm : ∃ m, m < n ∧ P m
    · obtain ⟨m, hmn, hpm⟩ := hm
      exact ih m hmn hpm
    · exact ⟨n, hn, fun m hmn hpm => hm ⟨m, hmn, hpm⟩⟩

/-! ## B1: fixed pure delay -/

/-- Fixed pure delay by `d` steps. Before time `d` the output holds the
input's initial value (the input is constant before time 0). -/
def delay (d : Nat) (s : Sig) : Sig := fun t => s (t - d)

theorem delay_zero (s : Sig) : delay 0 s = s := by
  funext t; simp [delay]

/-- B1: delay `d1` then `d2` is delay `d1 + d2`. -/
theorem delay_delay (d1 d2 : Nat) (s : Sig) :
    delay d2 (delay d1 s) = delay (d1 + d2) s := by
  funext t; simp only [delay]; congr 1; omega

/-! ## B2: bounded transport delay as a relation -/

/-- Monotone (non-decreasing) map on time. -/
def Mono (f : Nat → Nat) : Prop := ∀ a b, a ≤ b → f a ≤ f b

/-- A time warp for a `[lo, hi]` channel: output step `t` shows the input as
it was at step `f t`, which is between `lo` and `hi` steps ago (truncated at
0, where the input is its constant initial value). -/
structure Warp (lo hi : Nat) (f : Nat → Nat) : Prop where
  mono : Mono f
  le_late : ∀ t, f t ≤ t - lo
  early_le : ∀ t, t - hi ≤ f t

/-- B2: the bounded transport (pure) delay channel `[lo, hi]`, as a relation
between input `i` and output `o`. -/
def Transport (lo hi : Nat) (i o : Sig) : Prop :=
  ∃ f, Warp lo hi f ∧ ∀ t, o t = i (f t)

/-- B2: composition. A `[lo1,hi1]` channel followed by a `[lo2,hi2]` channel
is contained in the `[lo1+lo2, hi1+hi2]` channel. -/
theorem transport_comp {lo1 hi1 lo2 hi2 : Nat} {i m o : Sig}
    (h1 : Transport lo1 hi1 i m) (h2 : Transport lo2 hi2 m o) :
    Transport (lo1 + lo2) (hi1 + hi2) i o := by
  obtain ⟨f, F, hf⟩ := h1
  obtain ⟨g, G, hg⟩ := h2
  refine ⟨fun t => f (g t), ⟨?_, ?_, ?_⟩, ?_⟩
  · intro a b hab; exact F.mono _ _ (G.mono _ _ hab)
  · intro t
    have := F.le_late (g t); have := G.le_late t; omega
  · intro t
    have := F.early_le (g t); have := G.early_le t; omega
  · intro t; rw [hg, hf]

/-- B2: monotonicity in the delay bounds. -/
theorem transport_mono {lo hi lo' hi' : Nat} {i o : Sig}
    (hlo : lo' ≤ lo) (hhi : hi ≤ hi') (h : Transport lo hi i o) :
    Transport lo' hi' i o := by
  obtain ⟨f, F, hf⟩ := h
  refine ⟨f, ⟨F.mono, ?_, ?_⟩, hf⟩
  · intro t; have := F.le_late t; omega
  · intro t; have := F.early_le t; omega

/-- B1 is the degenerate case `lo = hi` of B2, in both directions. -/
theorem delay_transport (d : Nat) (i : Sig) : Transport d d i (delay d i) :=
  ⟨fun t => t - d, ⟨fun a b h => by omega, fun t => by omega,
    fun t => by omega⟩, fun _ => rfl⟩

theorem transport_exact {d : Nat} {i o : Sig} (h : Transport d d i o) :
    o = delay d i := by
  obtain ⟨f, F, hf⟩ := h
  funext t
  have h1 := F.le_late t; have h2 := F.early_le t
  rw [hf]; simp only [delay]; congr 1; omega

/-- B2, "no other output transitions": every output transition is caused by
an input transition between `lo` and `hi` steps earlier. -/
theorem transport_cause {lo hi : Nat} {i o : Sig} (h : Transport lo hi i o)
    {t : Nat} (ht : o (t + 1) ≠ o t) :
    ∃ u, i (u + 1) ≠ i u ∧ u ≤ t ∧ lo ≤ t - u ∧ t - u ≤ hi := by
  obtain ⟨f, F, hf⟩ := h
  rw [hf, hf] at ht
  have hm := F.mono t (t + 1) (by omega)
  obtain ⟨u, h1, h2, h3⟩ := exists_tr i (f t) (f (t + 1)) hm (fun e => ht e.symm)
  have a1 := F.le_late (t + 1); have a2 := F.early_le t
  exact ⟨u, h3, by omega, by omega, by omega⟩

/-- B2, "every input transition appears, order preserved", for a transition
that is isolated by `hi - lo` steps on either side: the output makes exactly
one transition in the window, from the old value to the new one, after a
delay in `[lo, hi]`. (A transition closer than `hi - lo` to a neighbour may
annihilate with it: see B3.) -/
theorem transport_isolated {lo hi : Nat} {i o : Sig} (h : Transport lo hi i o)
    (hlh : lo ≤ hi) {u : Nat} {a : Bool}
    (hA : ∀ x, u + lo ≤ x + hi → x ≤ u → i x = a)
    (hB : ∀ x, u < x → x + lo ≤ u + 1 + hi → i x = !a) :
    ∃ t, u ≤ t ∧ lo ≤ t - u ∧ t - u ≤ hi ∧ o t = a ∧ o (t + 1) = !a ∧
      ∀ t', u + lo ≤ t' → t' ≤ u + hi → o (t' + 1) ≠ o t' → t' = t := by
  obtain ⟨f, F, hf⟩ := h
  -- inside the window the output is a step: `!a` once `f t` passes `u`
  have val : ∀ t, u + lo ≤ t → t ≤ u + 1 + hi →
      o t = (if u < f t then !a else a) := by
    intro t h1 h2
    have := F.le_late t; have := F.early_le t
    rw [hf]
    by_cases hu : u < f t
    · simp [hu, hB (f t) hu (by omega)]
    · simp [hu, hA (f t) (by omega) (by omega)]
  -- an output transition in the window is exactly a crossing of `u` by `f`
  have cross : ∀ t, u + lo ≤ t → t ≤ u + hi → o (t + 1) ≠ o t →
      ¬ u < f t ∧ u < f (t + 1) := by
    intro t h1 h2 hne
    have m := F.mono t (t + 1) (by omega)
    rw [val t (by omega) (by omega), val (t + 1) (by omega) (by omega)] at hne
    by_cases c1 : u < f t
    · have c2 : u < f (t + 1) := by omega
      simp [c1, c2] at hne
    · by_cases c2 : u < f (t + 1)
      · exact ⟨c1, c2⟩
      · simp [c1, c2] at hne
  have o0 : o (u + lo) = a := by
    have := F.le_late (u + lo)
    rw [val _ (by omega) (by omega)]; split <;> first | rfl | omega
  have o1 : o (u + 1 + hi) = !a := by
    have := F.early_le (u + 1 + hi)
    rw [val _ (by omega) (by omega)]; split <;> first | rfl | omega
  obtain ⟨t, ht1, ht2, ht3⟩ :=
    exists_tr o (u + lo) (u + 1 + hi) (by omega) (by rw [o0, o1]; cases a <;> simp)
  obtain ⟨c1, c2⟩ := cross t ht1 (by omega) ht3
  refine ⟨t, by omega, by omega, by omega, ?_, ?_, ?_⟩
  · rw [val t (by omega) (by omega)]; split <;> first | rfl | omega
  · rw [val (t + 1) (by omega) (by omega)]; split <;> first | rfl | omega
  · intro t' h1 h2 hne
    obtain ⟨d1, d2⟩ := cross t' h1 h2 hne
    -- two distinct crossings of the threshold `u` contradict monotonicity
    rcases Nat.lt_trichotomy t' t with hl | he | hg
    · have := F.mono (t' + 1) t (by omega); omega
    · exact he
    · have := F.mono (t + 1) t' (by omega); omega

/-! ## B3: pulses through a transport channel

Order-crossing: in the warp form `o = i ∘ f` with `f` monotone, output
transitions can never cross (no inverted ordering, no split pulse; see
`pulse_convex`). When two input transitions get delays that make them land on
the same output step, they annihilate: the pulse is lost (`pulse_lost`). This
is the discrete counterpart of "the falling edge overtakes the rising edge".
-/

/-- A pulse of value `!a` on steps `[p, p+w)`, `a` elsewhere. -/
def pulse (a : Bool) (p w : Nat) : Sig :=
  fun x => if p ≤ x ∧ x < p + w then !a else a

theorem pulse_eq_not {a : Bool} {p w x : Nat} :
    pulse a p w x = !a ↔ p ≤ x ∧ x < p + w := by
  simp only [pulse]; split <;> rename_i h <;> cases a <;> simp [h]

/-- B3: the output of a pulse is never split or inverted: the set of steps
where it shows `!a` is convex. -/
theorem pulse_convex {lo hi p w : Nat} {a : Bool} {o : Sig}
    (h : Transport lo hi (pulse a p w) o) {t1 t t2 : Nat}
    (h1 : o t1 = !a) (h2 : o t2 = !a) (ht1 : t1 ≤ t) (ht2 : t ≤ t2) :
    o t = !a := by
  obtain ⟨f, F, hf⟩ := h
  rw [hf, pulse_eq_not] at h1 h2 ⊢
  have := F.mono _ _ ht1; have := F.mono _ _ ht2; omega

/-- B3: the output pulse lies inside `[p+lo, p+w+hi)`. -/
theorem pulse_outer {lo hi p w : Nat} {a : Bool} {o : Sig}
    (h : Transport lo hi (pulse a p w) o) (hp : 1 ≤ p) {t : Nat}
    (ht : o t = !a) :
    p + lo ≤ t ∧ t < p + w + hi := by
  obtain ⟨f, F, hf⟩ := h
  rw [hf, pulse_eq_not] at ht
  have := F.le_late t; have := F.early_le t; omega

/-- B3: the output pulse covers `[p+hi, p+w+lo)` (nonempty iff `w > hi-lo`). -/
theorem pulse_inner {lo hi p w : Nat} {a : Bool} {o : Sig}
    (h : Transport lo hi (pulse a p w) o) (hlh : lo ≤ hi) {t : Nat}
    (h1 : p + hi ≤ t) (h2 : t < p + w + lo) : o t = !a := by
  obtain ⟨f, F, hf⟩ := h
  rw [hf, pulse_eq_not]
  have := F.le_late t; have := F.early_le t; omega

/-- B3: the output pulse is a single interval `[s, e)` (possibly empty). -/
theorem pulse_interval {lo hi p w : Nat} {a : Bool} {o : Sig}
    (h : Transport lo hi (pulse a p w) o) (hp : 1 ≤ p) :
    ∃ s e, ∀ t, o t = !a ↔ s ≤ t ∧ t < e := by
  by_cases hne : ∃ t, o t = !a
  · obtain ⟨s, hs, hsmin⟩ := exists_least _ hne
    have hout := pulse_outer h hp hs
    have hend : ∃ t, s ≤ t ∧ o t ≠ !a :=
      ⟨p + w + hi, by omega, fun e => by have := pulse_outer h hp e; omega⟩
    obtain ⟨e, ⟨he1, he2⟩, hemin⟩ := exists_least _ hend
    refine ⟨s, e, fun t => ⟨fun ht => ⟨?_, ?_⟩, fun ⟨h1, h2⟩ => ?_⟩⟩
    · exact Nat.le_of_not_lt (fun hlt => hsmin t hlt ht)
    · refine Nat.lt_of_not_le (fun hle => he2 ?_)
      exact pulse_convex h hs ht he1 hle
    · cases ho : o t <;> cases a <;> simp_all <;>
        exact absurd (by simp_all) (hemin t h2)
  · exact ⟨0, 0, fun t => ⟨fun ht => absurd ⟨t, ht⟩ hne, fun h => by omega⟩⟩

/-- B3: width bounds. A pulse of width `w` comes out with width in
`[w - (hi-lo), w + (hi-lo)]`, and is certainly present if `w > hi - lo`. -/
theorem pulse_width {lo hi p w s e : Nat} {a : Bool} {o : Sig}
    (h : Transport lo hi (pulse a p w) o) (hp : 1 ≤ p)
    (hse : ∀ t, o t = !a ↔ s ≤ t ∧ t < e) :
    (s < e → e - s ≤ w + hi - lo) ∧
    (lo ≤ hi → hi - lo < w → s < e ∧ w - (hi - lo) ≤ e - s) := by
  constructor
  · intro hlt
    have a1 := pulse_outer h hp ((hse s).2 ⟨Nat.le_refl _, hlt⟩)
    have a2 := pulse_outer h hp ((hse (e - 1)).2 ⟨by omega, by omega⟩)
    omega
  · intro hlh hw
    have b1 := (hse (p + hi)).1 (pulse_inner h hlh (Nat.le_refl _) (by omega))
    have b2 := (hse (p + w + lo - 1)).1 (pulse_inner h hlh (by omega) (by omega))
    omega

/-- B3: a pulse no wider than `hi - lo` may be lost entirely: the channel
admits the constant output. (`1 ≤ p` so the pulse starts after time 0.) -/
theorem pulse_lost {lo hi p w : Nat} (a : Bool) (hp : 1 ≤ p)
    (hw : w + lo ≤ hi) : Transport lo hi (pulse a p w) (fun _ => a) := by
  refine ⟨fun t => if t - lo < p then t - lo else if t - lo < p + w then p - 1
            else if t - hi < p + w then p + w else t - hi, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro x y hxy
    dsimp only
    repeat' split
    all_goals omega
  · intro t; repeat' split
    all_goals omega
  · intro t; repeat' split
    all_goals omega
  · intro t
    simp only [pulse]
    repeat' split
    all_goals first | rfl | omega

/-- B3: the same short pulse may also pass unchanged (e.g. fixed delay `lo`):
the channel is genuinely nondeterministic about short pulses. -/
theorem pulse_may_pass {lo hi p w : Nat} (a : Bool) (hlh : lo ≤ hi) :
    Transport lo hi (pulse a p w) (delay lo (pulse a p w)) :=
  transport_mono (Nat.le_refl _) hlh (delay_transport lo _)

/-! ## B4: inertial delay

`inertial δ i` is a function, not a relation: the output takes the input's
value at step `t` once the input has held that value for the last `δ+1`
samples `[t-δ, t]`. An input transition at `u` therefore reaches the output at
`u + δ` unless the input moves again within `(u, u+δ]`. -/

/-- The input has been constant on `[t-δ, t]`. A `Bool`, so it computes. -/
def stab (i : Sig) (δ t : Nat) : Bool :=
  (List.range (δ + 1)).all (fun k => i (t - k) == i t)

theorem stab_iff {i : Sig} {δ t : Nat} :
    stab i δ t = true ↔ ∀ k, k ≤ δ → i (t - k) = i t := by
  simp [stab, List.all_eq_true, List.mem_range, Nat.lt_succ_iff]

/-- Inertial delay by `δ` steps (rejects pulses of width `≤ δ`). -/
def inertial (δ : Nat) (i : Sig) : Sig
  | 0 => i 0
  | t + 1 => if stab i δ (t + 1) then i (t + 1) else inertial δ i t

/-- B4: pulses no wider than `δ` produce no output transition. -/
theorem inertial_filters {δ p w : Nat} {a : Bool} (hp : 1 ≤ p) (hw : w ≤ δ) :
    ∀ t, inertial δ (pulse a p w) t = a := by
  intro t
  induction t with
  | zero => simp [inertial, pulse]; omega
  | succ t ih =>
    simp only [inertial]
    split
    · rename_i hs
      have hk := (stab_iff.1 hs) (t + 2 - p)
      simp only [pulse] at hk ⊢
      repeat' split at hk
      all_goals (repeat' split) <;> (first | rfl | omega | (cases a <;> simp_all) | skip)
      all_goals omega
    · exact ih

/-- B4: pulses wider than `δ` are propagated, delayed by exactly `δ`, with
their width unchanged. -/
theorem inertial_passes {δ p w : Nat} {a : Bool} (hp : 1 ≤ p) (hw : δ < w) :
    ∀ t, inertial δ (pulse a p w) t = pulse a (p + δ) w t := by
  intro t
  induction t with
  | zero =>
    simp only [inertial, pulse]
    repeat' split
    all_goals first | rfl | omega
  | succ t ih =>
    simp only [inertial]
    split
    · rename_i hs
      have hst := stab_iff.1 hs
      by_cases r1 : t + 1 < p + δ
      · -- still before the delayed rise: a `!a` sample would need p-1 in the window
        have hk := hst (t + 2 - p)
        simp only [pulse] at hk ⊢
        repeat' split at hk
        all_goals (repeat' split) <;> (first | rfl | omega | (cases a <;> simp_all) | skip)
        all_goals omega
      · by_cases r2 : p + w ≤ t + 1 ∧ t + 1 < p + w + δ
        · have hk := hst (t + 2 - p - w) (by omega)
          simp only [pulse] at hk ⊢
          repeat' split at hk
          all_goals (repeat' split) <;> (first | rfl | omega | (cases a <;> simp_all) | skip)
          all_goals omega
        · simp only [pulse]
          repeat' split
          all_goals first | rfl | omega
    · rename_i hs
      rw [ih]
      -- not stable: the window holds both values, so we are within δ after an edge
      have hns : ¬ ∀ k, k ≤ δ → pulse a p w (t + 1 - k) = pulse a p w (t + 1) :=
        fun h => hs (stab_iff.2 h)
      simp only [pulse] at hns ⊢
      by_cases c1 : p + δ ≤ t + 1 ∧ t + 1 < p + w
      · exact absurd (fun k hk => by
          repeat' split
          all_goals first | rfl | omega) hns
      · by_cases c2 : t + 1 < p
        · exact absurd (fun k hk => by
            repeat' split
            all_goals first | rfl | omega) hns
        · by_cases c3 : p + w + δ ≤ t + 1
          · exact absurd (fun k hk => by
              repeat' split
              all_goals first | rfl | omega) hns
          · repeat' split
            all_goals first | rfl | omega

/-- Output transitions of the inertial channel need a stable input window. -/
theorem inertial_change {δ : Nat} {i : Sig} {t : Nat}
    (h : inertial δ i (t + 1) ≠ inertial δ i t) :
    stab i δ (t + 1) = true ∧ inertial δ i (t + 1) = i (t + 1) := by
  simp only [inertial] at h ⊢
  split at h
  · rename_i hs; simp [hs]
  · exact absurd rfl h

/-- B4 (extra): every output pulse of `inertial δ` is at least `δ+1` wide:
after an output transition at `t+1` the output holds for `δ` more steps. -/
theorem inertial_min_width {δ : Nat} {i : Sig} {t : Nat}
    (h : inertial δ i (t + 1) ≠ inertial δ i t) :
    ∀ j, j ≤ δ → inertial δ i (t + 1 + j) = inertial δ i (t + 1) := by
  obtain ⟨hs, he⟩ := inertial_change h
  have hst := stab_iff.1 hs
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    rw [show t + 1 + (j + 1) = (t + 1 + j) + 1 by omega]
    simp only [inertial]
    split
    · rename_i hs2
      have := (stab_iff.1 hs2) (j + 1) hj
      rw [show t + 1 + j + 1 - (j + 1) = t + 1 by omega] at this
      exact this.symm
    · rw [← he]; exact ih (by omega)

/-! ## B5: a gate as a relation, a circuit as a conjunction -/

/-- AND gate: the Boolean AND of the inputs, through a `[lo, hi]` transport
channel. (A pure-Boolean gate with lumped delay; NOT the LUT mux-tree model,
which is track 4's job.) -/
def AndGate (lo hi : Nat) (a b o : Sig) : Prop :=
  Transport lo hi (fun t => a t && b t) o

/-- B5: with `b` held at 1, the AND output follows `a` through `[lo, hi]`. -/
theorem and_follows {lo hi : Nat} {a b o : Sig} (h : AndGate lo hi a b o)
    (hb : ∀ t, b t = true) : Transport lo hi a o := by
  obtain ⟨f, F, hf⟩ := h
  exact ⟨f, F, fun t => by rw [hf]; simp [hb]⟩

/-- B5: a two-gate circuit (conjunction of gate relations): `m = AND(a,b)`,
`o = AND(m,c)`, with `b` and `c` held at 1, is a `[lo1+lo2, hi1+hi2]`
channel from `a` to `o`. -/
theorem and_chain {lo1 hi1 lo2 hi2 : Nat} {a b c m o : Sig}
    (g1 : AndGate lo1 hi1 a b m) (g2 : AndGate lo2 hi2 m c o)
    (hb : ∀ t, b t = true) (hc : ∀ t, c t = true) :
    Transport (lo1 + lo2) (hi1 + hi2) a o :=
  transport_comp (and_follows g1 hb) (and_follows g2 hc)

/-- B5: `b` held at 1 only from step `T` on: from `T + hi` the output shows a
value `a` had between `lo` and `hi` steps earlier. -/
theorem and_follows_from {lo hi T : Nat} {a b o : Sig} (h : AndGate lo hi a b o)
    (hb : ∀ t, T ≤ t → b t = true) :
    ∀ t, T + hi ≤ t → ∃ u, t - hi ≤ u ∧ u ≤ t - lo ∧ o t = a u := by
  obtain ⟨f, F, hf⟩ := h
  intro t ht
  have := F.le_late t; have := F.early_le t
  refine ⟨f t, this, by omega, ?_⟩
  rw [hf]; simp [hb (f t) (by omega)]

/-! ## Bounded model checking with `decide`

Signals over a finite horizon are finite objects, so `decide` (kernel
evaluation, no `native_decide`) checks closed statements by enumeration. -/

/-- Input number `n` read as a bit pattern: step `t` is bit `t` of `n`. -/
def bits (n : Nat) : Sig := fun t => n.testBit t

/-- No output transition of `o` in `(t+1, t+1+δ]` after one at `t+1`,
for all `t < H`. -/
def minWidthB (δ H : Nat) (o : Sig) : Bool :=
  (List.range H).all fun t =>
    o (t + 1) == o t || (List.range δ).all fun k => o (t + 2 + k) == o (t + 1 + k)

set_option maxRecDepth 100000 in
/-- BMC: for every input pattern of 8 steps (256 inputs), `inertial 2`
emits no output pulse narrower than 3 steps within 10 steps. This is a
bounded instance of `inertial_min_width`, checked by enumeration. -/
theorem bmc_inertial_min_width :
    ∀ n, n < 256 → minWidthB 2 10 (inertial 2 (bits n)) = true := by
  decide

/-- BMC: exact pulse shape, `δ = 3`, width 5 at step 2, horizon 16. -/
theorem bmc_inertial_pulse :
    (List.range 16).all (fun t =>
      inertial 3 (pulse false 2 5) t == pulse false 5 5 t) = true := by
  decide

/-- Ties are representable exactly: `a` rising and `b` falling in the same
step give an AND with no glitch at all; one step of skew gives a one-step
glitch, which the `[lo, hi]` channel may pass or (if `hi > lo`) lose. -/
theorem tie_no_glitch :
    (List.range 8).all (fun t => (pulse false 3 10 t && pulse true 3 10 t) == false)
      = true := by decide

theorem skew_glitch :
    (List.range 8).all (fun t => (pulse false 3 10 t && pulse true 4 10 t)
      == pulse false 3 1 t) = true := by decide

end Formal.Core.TraceDiscrete
