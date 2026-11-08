import Formal.Net.OccNet

/-!
# Timed occurrence nets: every bounded-delay behaviour follows the certificate (shard C, S4)

**Problem, plainly.** `OccNet` shows that an occurrence-net certificate decides every interleaving of an
abstract machine. A real circuit is not an interleaving machine: each gate reads each of its inputs through a
routed delay, so at one instant a gate may see some inputs new and others old (a hazard), and a storage
node may see its own old value through its feedback route (the race that refutes THE statement at κ = 0.44).
Which conditions make every bounded-delay behaviour follow the certificate's events?

**The timed net (`TNet`, `TBeh`).** Gate `v` reads each source `w` of its pin list at time `r v w t`, with
`lo v w ≤ t - r v w t ≤ hi v w`, `lo ≥ 1`, reads monotone in `t`; its value at `t` is `F v` of the values
read (the shape of `Spec.GateOK`, transport delays on pins, zero-delay function). Free nodes (the
environment) change at `t` only if their rule `envEn` allows it in the state at `t - 1`. Before `t0` every
node is quiet (back to `t0 - H`, as far as reads reach).

**The read tuple** of node `v` at time `t`: for each node `w`, the number of changes of `w` (after `t0`) up to
the time `v` reads it (`t - 1` for nodes `v` does not read; all of them for a free node).

**Hypotheses on the certificate** (all checkable per node, per pin pair, per event):
* `OccNet.LCheck` at every node, for the move rule `tEn` (a gate may move iff `F` of its pins differs from its
  value): exactly the abstract machine's local check, which covers every bound-respecting tuple;
* sound bounds `L` (`LSound`, e.g. from `LStep`), time stamps (`TmOK`);
* separations `Sep b m a k = some d` ("event `(b, m)` happens at least `d` ps before event `(a, k)`"),
  justified one step back along the causes with the pins' `lo` delays (`SepOK`);
* **the skew obligations `TO`**: at gate `v`, for sources `a, b` of `D v` and each event `(a, k)` whose bound
  says event `(b, L a k b - 1)` precedes it: if `b` can be read later than `a` (`hi' v b > lo' v a`), a
  certified separation `d` with `hi' v b ≤ lo' v a + d`. (The feedback race and isochronic forks are
  instances: `a` the acknowledge, `b = v` the feedback.)

**Proved:** `timed_follows`: for every `t ≥ t0`, the count vector of the behaviour at `t` is an ideal of the
certificate and the state is that ideal's state (`x_eq_st`), and every change of every node is the next
event of that node, enabled by what it read. With `OccNet.reach_prop`-style reasoning, every property of all
ideal states holds at every time.

**Not shown here:** liveness in time (every enabled event happens within its pins' `hi`; next), any instance,
the bridge from `Spec.GateOK` (collapsed view) to `TBeh`.
-/

namespace Formal.Net.OccNet.Timed
open Formal.Net.OccNet

variable {α : Type} [DecidableEq α]

structure TNet (α : Type) where
  gate : α → Bool
  pins : α → List α
  F : α → List Bool → Bool
  lo : α → α → Nat
  hi : α → α → Nat

/-- The move rule: a gate may move when `F` of its pins differs from its value; a free node by `envEn`. -/
def tEn (N : TNet α) (envEn : α → (α → Bool) → Bool) (v : α) (s : α → Bool) : Bool :=
  if N.gate v then (N.F v ((N.pins v).map s) != s v) else envEn v s

/-- Changes of `u` in `(t0, s]`. -/
def cnt (x : α → Nat → Bool) (t0 : Nat) (u : α) : Nat → Nat
  | 0 => 0
  | s + 1 => if s + 1 ≤ t0 then 0 else cnt x t0 u s + (if x u (s + 1) != x u s then 1 else 0)

/-- Does `v` read `w` through a pin? -/
def reads (N : TNet α) (v w : α) : Bool := N.gate v && decide (w ∈ N.pins v)

/-- Effective read time, and its delay bounds (1 for nodes read "now", at `t - 1`). -/
def ρ (N : TNet α) (r : α → α → Nat → Nat) (v w : α) (t : Nat) : Nat := if reads N v w then r v w t else t - 1
def lo' (N : TNet α) (v w : α) : Nat := if reads N v w then N.lo v w else 1
def hi' (N : TNet α) (v w : α) : Nat := if reads N v w then N.hi v w else 1

/-- The read tuple of `v` at `t`. -/
def nT (N : TNet α) (x : α → Nat → Bool) (t0 : Nat) (r : α → α → Nat → Nat) (v : α) (t : Nat) : α → Nat :=
  fun w => cnt x t0 w (ρ N r v w t)

structure TBeh (N : TNet α) (envEn : α → (α → Bool) → Bool) (x : α → Nat → Bool) (r : α → α → Nat → Nat)
    (t0 H : Nat) : Prop where
  quiet : ∀ u s, t0 ≤ s + H → s ≤ t0 → x u s = x u t0
  rd : ∀ v w t, N.gate v = true → w ∈ N.pins v → t0 < t →
    N.lo v w ≤ t - r v w t ∧ t - r v w t ≤ N.hi v w ∧ r v w t ≤ t ∧ t0 ≤ r v w t + H
  lo1 : ∀ v w, N.gate v = true → w ∈ N.pins v → 1 ≤ N.lo v w
  mono : ∀ v w t t', N.gate v = true → w ∈ N.pins v → t0 < t → t ≤ t' → r v w t ≤ r v w t'
  geq : ∀ v t, N.gate v = true → t0 < t → x v t = N.F v ((N.pins v).map fun w => x w (r v w t))
  env : ∀ u t, N.gate u = false → t0 < t → x u t ≠ x u (t - 1) → envEn u (fun w => x w (t - 1)) = true

/-! ## Counting -/

section count
variable {x : α → Nat → Bool} {t0 : Nat}

theorem cnt_le_t0 (u : α) : ∀ s, s ≤ t0 → cnt x t0 u s = 0
  | 0, _ => rfl
  | s + 1, h => by simp [cnt, h]

theorem cnt_succ (u : α) (s : Nat) (h : t0 ≤ s) :
    cnt x t0 u (s + 1) = cnt x t0 u s + (if x u (s + 1) != x u s then 1 else 0) := by
  simp only [cnt]; rw [if_neg (by omega)]

theorem cnt_mono (u : α) : ∀ a b, a ≤ b → cnt x t0 u a ≤ cnt x t0 u b := by
  intro a b hab
  induction b with
  | zero => have : a = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ b ih =>
    rcases Nat.lt_or_ge a (b + 1) with h | h
    · refine Nat.le_trans (ih (by omega)) ?_
      simp only [cnt]; split
      · rename_i h'; rw [cnt_le_t0 u b (by omega)]; exact Nat.le_refl _
      · exact Nat.le_add_right _ _
    · have : a = b + 1 := by omega
      subst this; exact Nat.le_refl _

theorem cnt_step_le (u : α) (s : Nat) : cnt x t0 u (s + 1) ≤ cnt x t0 u s + 1 := by
  simp only [cnt]; split
  · exact Nat.zero_le _
  · split <;> omega

/-- The value is the initial value flipped `cnt` times. -/
theorem x_eq_st (u : α) (H : Nat) (hq : ∀ s, t0 ≤ s + H → s ≤ t0 → x u s = x u t0) :
    ∀ s, t0 ≤ s + H → x u s = st (fun w => x w t0) (fun w => cnt x t0 w s) u := by
  intro s hs
  induction s with
  | zero => simp [st, cnt]; exact hq 0 hs (Nat.zero_le _)
  | succ s ih =>
    by_cases h : s + 1 ≤ t0
    · simp only [st, cnt, h, if_true]; simp; exact hq (s + 1) hs h
    · have ih' := ih (by omega)
      simp only [st] at ih' ⊢
      rw [cnt_succ u s (by omega)]
      cases hx : x u (s + 1) <;> cases hx' : x u s <;> rw [hx'] at ih' <;> simp at ih' <;>
        simp [Nat.add_mod] <;>
        rcases Nat.mod_two_eq_zero_or_one (cnt x t0 u s) with h2 | h2 <;> simp_all

/-- An event that happened by `τ` happened at some step `s ≤ τ`, the `k`-th change. -/
theorem event_time (u : α) (k : Nat) : ∀ τ, k < cnt x t0 u τ →
    ∃ s, t0 < s ∧ s ≤ τ ∧ cnt x t0 u (s - 1) = k ∧ cnt x t0 u s = k + 1 ∧ x u s ≠ x u (s - 1)
  | 0, h => by simp [cnt] at h
  | τ + 1, h => by
    by_cases ht : τ + 1 ≤ t0
    · rw [cnt_le_t0 u _ ht] at h; exact absurd h (Nat.not_lt_zero _)
    · by_cases hk : k < cnt x t0 u τ
      · obtain ⟨s, h1, h2, h3, h4, h5⟩ := event_time u k τ hk
        exact ⟨s, h1, by omega, h3, h4, h5⟩
      · have hs := cnt_succ (x := x) (t0 := t0) u τ (by omega)
        rw [hs] at h
        refine ⟨τ + 1, by omega, Nat.le_refl _, ?_, ?_, ?_⟩
        · simp only [Nat.add_sub_cancel]; split at h <;> omega
        · rw [hs]; split at h <;> split <;> omega
        · simp only [Nat.add_sub_cancel]
          intro he; rw [he] at h; simp at h; omega

end count

/-! ## The certificate's timing hypotheses -/

/-- Separation claims justified one step back along causes (with the pins' `lo`) or the node's previous event. -/
def SepOK (N : TNet α) (C : Cert α) (Sep : α → Nat → α → Nat → Option Nat) : Prop :=
  ∀ b m a k d, k < C.len a → Sep b m a k = some d →
    (b = a ∧ m = k ∧ d = 0) ∨
    (∃ p ∈ C.causes a k, ∃ d', Sep b m p.1 p.2 = some d' ∧ d ≤ d' + lo' N a p.1) ∨
    (0 < k ∧ ∃ d', Sep b m a (k - 1) = some d' ∧ d ≤ d' + lo' N a a)

/-- **The skew obligations.** -/
def TO (N : TNet α) (C : Cert α) (L : α → Nat → α → Nat) (D : α → List α)
    (Sep : α → Nat → α → Nat → Option Nat) : Prop :=
  ∀ v a b k, a ∈ D v → b ∈ D v → k < C.len a → 0 < L a k b → lo' N v a < hi' N v b →
    ∃ d, Sep b (L a k b - 1) a k = some d ∧ hi' N v b ≤ lo' N v a + d

/-- What every change satisfies (the induction invariant's second half). -/
def ChangeOK (N : TNet α) (C : Cert α) (x : α → Nat → Bool) (t0 : Nat) (r : α → α → Nat → Nat)
    (v : α) (s : Nat) : Prop :=
  (reads N v v = true → cnt x t0 v (r v v s) = cnt x t0 v (s - 1)) ∧ Enabled C (nT N x t0 r v s) v

/-! ## The induction -/

theorem enabled_mono {C : Cert α} {n n' : α → Nat} {v : α} (h : Enabled C n v) (hv : n v = n' v)
    (hle : ∀ w, n w ≤ n' w) : Enabled C n' v :=
  ⟨hv ▸ h.1, fun p hp => Nat.lt_of_lt_of_le (h.2 p (hv ▸ hp)) (hle p.1)⟩

section main
variable {N : TNet α} {envEn : α → (α → Bool) → Bool} {x : α → Nat → Bool} {r : α → α → Nat → Nat}
  {t0 H : Nat} {C : Cert α} {L : α → Nat → α → Nat} {D : α → List α} {Sep : α → Nat → α → Nat → Option Nat}

theorem rho_bounds (hb : TBeh N envEn x r t0 H) (v w : α) (s : Nat) (hs : t0 < s) :
    ρ N r v w s ≤ s - lo' N v w ∧ s - hi' N v w ≤ ρ N r v w s ∧ ρ N r v w s ≤ s - 1 ∧ t0 ≤ ρ N r v w s + H := by
  unfold ρ lo' hi'
  by_cases h : reads N v w = true
  · simp only [h, if_true]
    simp only [reads, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, h2, h3, h4⟩ := hb.rd v w s h.1 h.2 hs
    have := hb.lo1 v w h.1 h.2
    omega
  · simp only [h, if_false, Bool.false_eq_true]; omega

theorem rho_mono (hb : TBeh N envEn x r t0 H) (v w : α) (s s' : Nat) (hs : t0 < s) (hss : s ≤ s') :
    ρ N r v w s ≤ ρ N r v w s' := by
  unfold ρ
  by_cases h : reads N v w = true
  · simp only [h, if_true]
    simp only [reads, Bool.and_eq_true, decide_eq_true_eq] at h
    exact hb.mono v w s s' h.1 h.2 hs hss
  · simp only [h, if_false, Bool.false_eq_true]; omega

/-- **Separations are sound** while every change so far was a certified event. -/
theorem sep_sound (hb : TBeh N envEn x r t0 H) (hT : TmOK C) (hS : SepOK N C Sep) (t : Nat)
    (hB : ∀ v s, t0 < s → s ≤ t → x v s ≠ x v (s - 1) → ChangeOK N C x t0 r v s) :
    ∀ M a k τ, C.tm a k ≤ M → τ ≤ t → k < cnt x t0 a τ → ∀ b m d, Sep b m a k = some d →
      m < cnt x t0 b (τ - d) := by
  intro M
  refine Nat.strongRecOn M ?_
  intro M ih a k τ hM hτ hk b m d hd
  obtain ⟨s, hs0, hsτ, hs1, hs2, hch⟩ := event_time a k τ hk
  obtain ⟨hfb, hen⟩ := hB a s hs0 (by omega) hch
  have hna : nT N x t0 r a s a = k := by
    unfold nT ρ
    by_cases h : reads N a a = true
    · simp only [h, if_true]; rw [hfb h, hs1]
    · simp only [h, if_false, Bool.false_eq_true]; exact hs1
  have hkl : k < C.len a := hna ▸ hen.1
  rcases hS b m a k d hkl hd with ⟨hb', hm, hd0⟩ | ⟨p, hp, d', hd', hle⟩ | ⟨hk0, d', hd', hle⟩
  · subst hb' hm hd0; simpa using hk
  · have hpc : p.2 < nT N x t0 r a s p.1 := hen.2 p (hna ▸ hp)
    obtain ⟨_, htm⟩ := hT.2 a k hkl p hp
    obtain ⟨r1, _, r3, _⟩ := rho_bounds hb a p.1 s hs0
    have := ih (C.tm p.1 p.2) (by omega) p.1 p.2 (ρ N r a p.1 s) (Nat.le_refl _) (by omega) hpc b m d' hd'
    exact Nat.lt_of_lt_of_le this (cnt_mono b _ _ (by omega))
  · have hprev : k - 1 < cnt x t0 a (ρ N r a a s) := by
      have : cnt x t0 a (ρ N r a a s) = k := hna
      omega
    have htm : C.tm a (k - 1) < C.tm a k := by
      have := hT.1 a (k - 1) (by omega)
      rwa [show k - 1 + 1 = k by omega] at this
    obtain ⟨r1, _, r3, _⟩ := rho_bounds hb a a s hs0
    have := ih (C.tm a (k - 1)) (by omega) a (k - 1) (ρ N r a a s) (Nat.le_refl _) (by omega) hprev b m d' hd'
    exact Nat.lt_of_lt_of_le this (cnt_mono b _ _ (by omega))

/-- **The read tuple respects the bounds** on `D v` (this is where the skew obligations are used). -/
theorem read_consistent (hb : TBeh N envEn x r t0 H) (hT : TmOK C) (hLs : LSound C L) (hS : SepOK N C Sep)
    (hTO : TO N C L D Sep) (t : Nat) (ht : t0 ≤ t)
    (hI : ∀ τ, τ ≤ t → Ideal C (fun u => cnt x t0 u τ))
    (hB : ∀ v s, t0 < s → s ≤ t → x v s ≠ x v (s - 1) → ChangeOK N C x t0 r v s) (v : α) :
    ∀ a ∈ D v, ∀ b ∈ D v, ∀ k, k < nT N x t0 r v (t + 1) a → L a k b ≤ nT N x t0 r v (t + 1) b := by
  intro a ha b hbD k hk
  obtain ⟨ra1, ra2, ra3, _⟩ := rho_bounds hb v a (t + 1) (by omega)
  obtain ⟨rb1, rb2, rb3, _⟩ := rho_bounds hb v b (t + 1) (by omega)
  let τa := ρ N r v a (t + 1)
  have hIa := hI τa (by omega)
  have hL1 : L a k b ≤ cnt x t0 b τa := hLs _ hIa a k b hk
  unfold nT
  by_cases hle : τa ≤ ρ N r v b (t + 1)
  · exact Nat.le_trans hL1 (cnt_mono b _ _ hle)
  · by_cases hL0 : L a k b = 0
    · rw [hL0]; exact Nat.zero_le _
    · have hkl : k < C.len a := Nat.lt_of_lt_of_le hk (hIa a).1
      obtain ⟨d, hd, hdle⟩ := hTO v a b k ha hbD hkl (by omega) (by omega)
      have := sep_sound hb hT hS t hB _ a k τa (Nat.le_refl _) (by omega) hk b (L a k b - 1) d hd
      have h2 := cnt_mono (x := x) (t0 := t0) b (τa - d) (ρ N r v b (t + 1)) (by omega)
      omega

end main

section main2
variable {N : TNet α} {envEn : α → (α → Bool) → Bool} {x : α → Nat → Bool} {r : α → α → Nat → Nat}
  {t0 H : Nat} {C : Cert α} {L : α → Nat → α → Nat} {D : α → List α} {Sep : α → Nat → α → Nat → Option Nat}

theorem bool3 {a b c : Bool} (h1 : (a != b) = true) (h2 : c ≠ b) : a = c := by
  cases a <;> cases b <;> cases c <;> simp_all

/-- The read values of a gate are the state of its read tuple. -/
theorem pins_read (hb : TBeh N envEn x r t0 H) (v : α) (hv : N.gate v = true) (s : Nat) (hs : t0 < s) :
    (N.pins v).map (fun w => x w (r v w s)) = (N.pins v).map (st (fun w => x w t0) (nT N x t0 r v s)) := by
  apply List.map_congr_left
  intro w hw
  have hrd : reads N v w = true := by simp [reads, hv, hw]
  obtain ⟨_, _, _, h4⟩ := hb.rd v w s hv hw hs
  rw [x_eq_st w H (fun s' h1 h2 => hb.quiet w s' h1 h2) _ h4]
  simp only [st, nT, ρ, hrd, if_true]

theorem st_nT_self (hb : TBeh N envEn x r t0 H) (v : α) (hnr : reads N v v = false) (t : Nat) (ht : t0 ≤ t) :
    st (fun w => x w t0) (nT N x t0 r v (t + 1)) v = x v t := by
  rw [x_eq_st v H (fun s' h1 h2 => hb.quiet v s' h1 h2) t (by omega)]
  simp [st, nT, ρ, hnr]

/-- **One step of the induction**: a change at `t + 1` is a certified event. -/
theorem change_ok (hb : TBeh N envEn x r t0 H) (hT : TmOK C) (hLs : LSound C L) (hS : SepOK N C Sep)
    (hTO : TO N C L D Sep) (hloc : ∀ v, LCheck (tEn N envEn) (fun w => x w t0) C L D v)
    (t : Nat) (ht : t0 ≤ t) (hI : ∀ τ, τ ≤ t → Ideal C (fun u => cnt x t0 u τ))
    (hB : ∀ v s, t0 < s → s ≤ t → x v s ≠ x v (s - 1) → ChangeOK N C x t0 r v s)
    (v : α) (hch : x v (t + 1) ≠ x v t) : ChangeOK N C x t0 r v (t + 1) := by
  have hcons := read_consistent hb hT hLs hS hTO t ht hI hB v
  have hlen : ∀ u ∈ D v, nT N x t0 r v (t + 1) u ≤ C.len u := by
    intro u _
    obtain ⟨_, _, h3, _⟩ := rho_bounds hb v u (t + 1) (by omega)
    exact (hI _ (by omega) u).1
  have hL := hloc v (nT N x t0 r v (t + 1)) hlen hcons
  have hq := fun u => x_eq_st (x := x) (t0 := t0) u H (fun s' h1 h2 => hb.quiet u s' h1 h2)
  have hsub : t + 1 - 1 = t := by omega
  show (reads N v v = true → cnt x t0 v (r v v (t + 1)) = cnt x t0 v (t + 1 - 1)) ∧
    Enabled C (nT N x t0 r v (t + 1)) v
  rw [hsub]
  cases hg : N.gate v with
  | false =>
    -- a free node
    have he := hb.env v (t + 1) hg (by omega) (by simpa [hsub] using hch)
    have hrd : reads N v v = false := by simp [reads, hg]
    refine ⟨fun h => absurd h (by simp [hrd]), ?_⟩
    apply hL.1
    unfold tEn; rw [hg]; simp only [Bool.false_eq_true, if_false]
    rw [hsub] at he
    have : (fun w => x w t) = st (fun w => x w t0) (nT N x t0 r v (t + 1)) := by
      funext w
      have hrw : reads N v w = false := by simp [reads, hg]
      rw [hq w t (by omega)]; simp [st, nT, ρ, hrw]
    rw [← this]; exact he
  | true =>
    have hgeq := hb.geq v (t + 1) hg (by omega)
    rw [pins_read hb v hg (t + 1) (by omega)] at hgeq
    by_cases hfb : reads N v v = true
    · -- a gate with a feedback pin
      let nv := nT N x t0 r v (t + 1) v
      have hnv : nv = cnt x t0 v (r v v (t + 1)) := by simp [nv, nT, ρ, hfb]
      obtain ⟨rv1, _, rv3, rv4⟩ := rho_bounds hb v v (t + 1) (by omega)
      have hrle : r v v (t + 1) ≤ t := by
        have : ρ N r v v (t + 1) = r v v (t + 1) := by simp [ρ, hfb]
        omega
      have hnvle : nv ≤ cnt x t0 v t := by rw [hnv]; exact cnt_mono v _ _ hrle
      rcases Nat.lt_or_ge nv (cnt x t0 v t) with hlt | hge
      · -- stale feedback: no change can happen (contradiction)
        exfalso
        obtain ⟨s1, h1a, h1b, h1c, h1d, h1e⟩ := event_time (x := x) (t0 := t0) v nv t hlt
        obtain ⟨fb1, en1⟩ := hB v s1 h1a h1b h1e
        have hr_s1 : r v v (t + 1) < s1 := by
          rcases Nat.lt_or_ge (r v v (t + 1)) s1 with h | h
          · exact h
          · have := cnt_mono (x := x) (t0 := t0) v s1 (r v v (t + 1)) h
            rw [← hnv] at this; omega
        have hn1v : nT N x t0 r v s1 v = nv := by
          simp only [nT, ρ, hfb, if_true]; rw [fb1 hfb, h1c]
        have hEn : Enabled C (nT N x t0 r v (t + 1)) v := by
          refine enabled_mono en1 (by rw [hn1v]) (fun w => ?_)
          exact cnt_mono w _ _ (rho_mono hb v w s1 (t + 1) h1a (by omega))
        have hen := hL.2 hEn
        unfold tEn at hen; rw [hg] at hen; simp only [if_true] at hen
        rw [← hgeq] at hen
        -- the state of `v` in the tuple is its value before event `nv`
        have hstv : st (fun w => x w t0) (nT N x t0 r v (t + 1)) v = x v (s1 - 1) := by
          rw [hq v (s1 - 1) (by omega)]; simp only [st, nT, ρ, hfb, if_true]; rw [← hnv, h1c]
        rw [hstv] at hen
        -- at most one event of `v` after the stale read
        have hcnt : cnt x t0 v t = nv + 1 := by
          rcases Nat.lt_or_ge (nv + 1) (cnt x t0 v t) with h2 | h2
          · exfalso
            obtain ⟨s2, h2a, h2b, h2c, _, h2e⟩ := event_time (x := x) (t0 := t0) v (nv + 1) t h2
            obtain ⟨fb2, _⟩ := hB v s2 h2a h2b h2e
            have := fb2 hfb
            have hs12 : s1 < s2 := by
              rcases Nat.lt_or_ge s1 s2 with h | h
              · exact h
              · have := cnt_mono (x := x) (t0 := t0) v s2 s1 h; omega
            have hm := hb.mono v v s2 (t + 1) hg (by simp [reads] at hfb; exact hfb.2) h2a (by omega)
            have := cnt_mono (x := x) (t0 := t0) v _ _ hm
            rw [← hnv] at this; omega
          · have := cnt_mono (x := x) (t0 := t0) v s1 t h1b
            omega
        have hxt : x v t = x v s1 := by
          rw [hq v t (by omega), hq v s1 (by omega)]; simp only [st]; rw [hcnt, h1d]
        apply hch
        rw [hxt]; exact bool3 hen h1e
      · -- current feedback
        have hnveq : nv = cnt x t0 v t := Nat.le_antisymm hnvle hge
        refine ⟨fun _ => by rw [← hnv, hnveq], ?_⟩
        apply hL.1
        unfold tEn; rw [hg]; simp only [if_true]
        rw [← hgeq]
        have : st (fun w => x w t0) (nT N x t0 r v (t + 1)) v = x v t := by
          rw [hq v t (by omega)]; simp only [st]; rw [show nT N x t0 r v (t + 1) v = nv from rfl, hnveq]
        rw [this]; simpa using hch
    · -- a gate without a feedback pin
      have hfb' : reads N v v = false := by simpa using hfb
      refine ⟨fun h => absurd h hfb, ?_⟩
      apply hL.1
      unfold tEn; rw [hg]; simp only [if_true]
      rw [← hgeq, st_nT_self hb v hfb' t ht]
      simpa using hch

/-- Simultaneous enabled events keep an ideal. -/
theorem ideal_step {c c' : α → Nat} (C : Cert α) (hc : Ideal C c)
    (h : ∀ u, c' u = c u ∨ (c' u = c u + 1 ∧ Enabled C c u)) (hle : ∀ u, c u ≤ c' u) : Ideal C c' := by
  intro u
  rcases h u with h1 | ⟨h1, he⟩
  · rw [h1]
    exact ⟨(hc u).1, fun k hk p hp => Nat.lt_of_lt_of_le ((hc u).2 k hk p hp) (hle _)⟩
  · rw [h1]
    refine ⟨he.1, fun k hk p hp => ?_⟩
    rcases Nat.lt_or_ge k (c u) with hk' | hk'
    · exact Nat.lt_of_lt_of_le ((hc u).2 k hk' p hp) (hle _)
    · have : k = c u := by omega
      subst this
      exact Nat.lt_of_lt_of_le (he.2 p hp) (hle _)

/-- **Every bounded-delay behaviour follows the certificate.** For every `t`, the count vector at `t` is an
ideal, and every change after `t0` is a certified event (the next event of its node, enabled by what the node
read, with a current feedback read). -/
theorem timed_follows (hb : TBeh N envEn x r t0 H) (hT : TmOK C) (hLs : LSound C L) (hS : SepOK N C Sep)
    (hTO : TO N C L D Sep) (hloc : ∀ v, LCheck (tEn N envEn) (fun w => x w t0) C L D v) :
    ∀ t, (∀ τ, τ ≤ t → Ideal C (fun u => cnt x t0 u τ)) ∧
      (∀ v s, t0 < s → s ≤ t → x v s ≠ x v (s - 1) → ChangeOK N C x t0 r v s) := by
  have h0 : Ideal C (fun _ => 0) := fun u => ⟨Nat.zero_le _, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  intro t
  induction t with
  | zero =>
    refine ⟨fun τ hτ => ?_, fun v s h1 h2 => by omega⟩
    have : τ = 0 := by omega
    subst this
    have e : (fun u => cnt x t0 u 0) = fun _ => 0 := by funext u; rfl
    rw [e]; exact h0
  | succ t ih =>
    obtain ⟨hI, hB⟩ := ih
    by_cases ht : t0 ≤ t
    · have hC : ∀ v, x v (t + 1) ≠ x v t → ChangeOK N C x t0 r v (t + 1) :=
        fun v hch => change_ok hb hT hLs hS hTO hloc t ht hI hB v hch
      have hB' : ∀ v s, t0 < s → s ≤ t + 1 → x v s ≠ x v (s - 1) → ChangeOK N C x t0 r v s := by
        intro v s h1 h2 h3
        rcases Nat.lt_or_ge s (t + 1) with h | h
        · exact hB v s h1 (by omega) h3
        · have : s = t + 1 := by omega
          subst this; exact hC v (by simpa using h3)
      refine ⟨fun τ hτ => ?_, hB'⟩
      rcases Nat.lt_or_ge τ (t + 1) with h | h
      · exact hI τ (by omega)
      · have : τ = t + 1 := by omega
        subst this
        apply ideal_step C (hI t (Nat.le_refl _))
        · intro u
          rw [cnt_succ u t ht]
          by_cases hx : x u (t + 1) = x u t
          · left; simp [hx]
          · right
            refine ⟨by simp [hx], ?_⟩
            obtain ⟨hfb, hen⟩ := hC u hx
            refine enabled_mono hen ?_ (fun w => ?_)
            · unfold nT ρ
              by_cases h : reads N u u = true
              · simp only [h, if_true]; rw [hfb h]; rfl
              · simp only [h, if_false, Bool.false_eq_true]; rfl
            · obtain ⟨_, _, h3, _⟩ := rho_bounds hb u w (t + 1) (by omega)
              exact cnt_mono w _ _ (by omega)
        · intro u; exact cnt_mono u _ _ (by omega)
    · refine ⟨fun τ hτ => ?_, fun v s h1 h2 h3 => ?_⟩
      · have e : (fun u => cnt x t0 u τ) = fun _ => 0 := by funext u; exact cnt_le_t0 u τ (by omega)
        rw [e]; exact h0
      · rcases Nat.lt_or_ge s (t + 1) with h | h
        · exact hB v s h1 (by omega) h3
        · omega

/-- **Corollary (safety).** Every property of all ideal states holds at every time from `t0` on. -/
theorem timed_prop (hb : TBeh N envEn x r t0 H) (hT : TmOK C) (hLs : LSound C L) (hS : SepOK N C Sep)
    (hTO : TO N C L D Sep) (hloc : ∀ v, LCheck (tEn N envEn) (fun w => x w t0) C L D v)
    (P : (α → Bool) → Prop) (hP : ∀ c, Ideal C c → P (st (fun w => x w t0) c)) (t : Nat) (ht : t0 ≤ t + H) :
    P (fun u => x u t) := by
  have hI := (timed_follows hb hT hLs hS hTO hloc t).1 t (Nat.le_refl _)
  have : (fun u => x u t) = st (fun w => x w t0) (fun u => cnt x t0 u t) := by
    funext u; exact x_eq_st u H (fun s' h1 h2 => hb.quiet u s' h1 h2) t ht
  rw [this]; exact hP _ hI

end main2

end Formal.Net.OccNet.Timed
