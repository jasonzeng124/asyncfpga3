/-!
# Occurrence-net certificates: one recorded run decides every interleaving (shard C, S4/S6)

**Problem, plainly.** THE target's control network, read as an abstract machine (storage nodes as the
state, zero-delay logic in between, relative-timing (RT) orders as blocking rules; tools/huff), gave the
same results in every order tried (random walks, 125 M moves) and never deadlocked. Random walks are
evidence, not proof; exhaustive search does not scale (40 M states for one pair before move 911).
`Keller.lean` turns persistence on the reachable states into "one terminating run decides every run",
but persistence on the reachable states is itself a property of those (too many) states.

This file replaces the reachable states by a *certificate*: one partial order of events (an occurrence
net), e.g. the causal order of one recorded run. Event `(u, k)` is the `k`-th change of node `u`; the
certificate gives each node's number of events `len u`, each event's immediate causes (events of other
nodes, or earlier events of the same node), and a time stamp `tm` (e.g. its position in the recorded run)
that decreases along causes. An **ideal** is a count vector `c` (`c u` events of node `u` have happened)
closed under causes; its state is the initial state with every node flipped `c u` times.

**The machine.** Nodes `α`, states `α → Bool`; a move fires one node `v` with `en v s = true` and flips
it. `en` is arbitrary: "excited and not blocked by an RT order", the environment's protocol rules, etc.

**Proved (generic):**
* `valid_ideal`: if the **global check** `GCheck` holds (in the state of every ideal, `en v` is true
  exactly when `v`'s next event exists and all its causes have happened), then every valid run from the
  initial state has, after every prefix, the state of an ideal, namely of its own count vector. So any
  property shown for the states of all ideals holds in every reachable state (`reach_prop`): safety.
* `run_length_le`: every valid run has at most `Σ len` moves (no infinite run under any schedule).
* `terminal_full`: an ideal in which no node is enabled is the full one (`c = len`): no deadlock before
  every event of the certificate has happened. Hence `maximal_run` : every valid run that cannot be
  extended fires every node exactly `len` times (the same moves as the certificate, in some order) and
  ends in the certificate's final state; and `extend_run`: every valid run extends to such a run.
* `gcheck_of_local`: the global check follows from a **local** one, per node `v`, over count vectors
  that are only constrained on `v`'s dependency list `D v` by lower bounds `L u k w` ("the `k`-th event of
  `u` has at least `L u k w` events of `w` below it"). `lsound_of_step`: such bounds are sound when they
  pass a one-step check along the causes (`LStep`). So the obligations scale with (nodes x local
  dependency patterns), not with the interleavings.

**Not shown here.** Anything about a particular netlist, the decidable enumerator for `LCheck` (next),
and the relation between the abstract machine and timed behaviours (the timed refinement, S4's other half).
-/

namespace Formal.Net.OccNet

variable {α : Type} [DecidableEq α]

/-- An occurrence-net certificate: per node its number of events, per event its immediate causes
`(node, index)` and a time stamp. -/
structure Cert (α : Type) where
  len : α → Nat
  causes : α → Nat → List (α × Nat)
  tm : α → Nat → Nat

/-- The state after `c u` flips of every node `u`. -/
def st (s0 : α → Bool) (c : α → Nat) : α → Bool := fun v => xor (s0 v) (c v % 2 == 1)

/-- Flip node `v`. -/
def flip (s : α → Bool) (v : α) : α → Bool := fun u => if u = v then !s u else s u

/-- One more event of `v`. -/
def bump (c : α → Nat) (v : α) : α → Nat := fun u => if u = v then c u + 1 else c u

/-- An ideal: at most `len u` events of `u`, and every cause of a happened event has happened. -/
def Ideal (C : Cert α) (c : α → Nat) : Prop :=
  ∀ u, c u ≤ C.len u ∧ ∀ k, k < c u → ∀ p ∈ C.causes u k, p.2 < c p.1

/-- `v`'s next event exists and all its causes have happened. -/
def Enabled (C : Cert α) (c : α → Nat) (v : α) : Prop :=
  c v < C.len v ∧ ∀ p ∈ C.causes v (c v), p.2 < c p.1

/-- **The global check**: in the state of every ideal, `v` may move exactly when its next event is enabled. -/
def GCheck (en : α → (α → Bool) → Bool) (s0 : α → Bool) (C : Cert α) : Prop :=
  ∀ c, Ideal C c → ∀ v, en v (st s0 c) = true ↔ Enabled C c v

/-- A valid run from `s`: each move is allowed in the state it is made in. -/
def Valid (en : α → (α → Bool) → Bool) : (α → Bool) → List α → Prop
  | _, [] => True
  | s, v :: l => en v s = true ∧ Valid en (flip s v) l

/-- The state after a run. -/
def after : (α → Bool) → List α → (α → Bool)
  | s, [] => s
  | s, v :: l => after (flip s v) l

/-- Count vector plus the moves of a run. -/
def addRun (c : α → Nat) (l : List α) : α → Nat := fun u => c u + l.count u

theorem st_bump (s0 : α → Bool) (c : α → Nat) (v : α) : st s0 (bump c v) = flip (st s0 c) v := by
  funext u
  unfold st bump flip
  by_cases h : u = v
  · subst h; simp only [ite_true]
    cases s0 u <;> rcases Nat.mod_two_eq_zero_or_one (c u) with h2 | h2 <;>
      simp [Nat.add_mod, h2]
  · simp [h]

theorem ideal_bump {C : Cert α} {c : α → Nat} {v : α} (hc : Ideal C c) (he : Enabled C c v) :
    Ideal C (bump c v) := by
  intro u
  have hle : ∀ w, c w ≤ bump c v w := by
    intro w; unfold bump; split <;> omega
  by_cases h : u = v
  · subst h
    refine ⟨by unfold bump; simp; exact he.1, fun k hk p hp => ?_⟩
    unfold bump at hk; simp at hk
    rcases Nat.lt_or_ge k (c u) with hk' | hk'
    · exact Nat.lt_of_lt_of_le ((hc u).2 k hk' p hp) (hle _)
    · have : k = c u := by omega
      subst this
      exact Nat.lt_of_lt_of_le (he.2 p hp) (hle _)
  · refine ⟨by unfold bump; simp [h]; exact (hc u).1, fun k hk p hp => ?_⟩
    unfold bump at hk; simp [h] at hk
    exact Nat.lt_of_lt_of_le ((hc u).2 k hk p hp) (hle _)

theorem addRun_cons (c : α → Nat) (v : α) (l : List α) : addRun c (v :: l) = addRun (bump c v) l := by
  funext u
  unfold addRun bump
  by_cases h : u = v
  · subst h; simp [List.count_cons]; omega
  · simp [List.count_cons, h]
    intro h'; exact absurd h'.symm h

/-- **Every valid run stays in ideal states** (from any ideal state). -/
theorem valid_ideal_from {en : α → (α → Bool) → Bool} {s0 : α → Bool} {C : Cert α} (hG : GCheck en s0 C) :
    ∀ (l : List α) (c : α → Nat), Ideal C c → Valid en (st s0 c) l →
      Ideal C (addRun c l) ∧ after (st s0 c) l = st s0 (addRun c l)
  | [], c, hc, _ => by
    have : addRun c [] = c := by funext u; simp [addRun]
    rw [this]; exact ⟨hc, rfl⟩
  | v :: l, c, hc, hv => by
    have he : Enabled C c v := (hG c hc v).1 hv.1
    have hc' := ideal_bump hc he
    have hv' : Valid en (st s0 (bump c v)) l := by rw [st_bump]; exact hv.2
    have ih := valid_ideal_from hG l (bump c v) hc' hv'
    rw [addRun_cons]
    refine ⟨ih.1, ?_⟩
    show after (flip (st s0 c) v) l = _
    rw [← st_bump]; exact ih.2

theorem st_zero (s0 : α → Bool) : st s0 (fun _ => 0) = s0 := by
  funext u; simp [st]

/-- **From the initial state**: after any valid run `l`, the count vector `l.count` is an ideal and the
state is its state. -/
theorem valid_ideal {en : α → (α → Bool) → Bool} {s0 : α → Bool} {C : Cert α} (hG : GCheck en s0 C)
    (l : List α) (hv : Valid en s0 l) :
    Ideal C (fun u => l.count u) ∧ after s0 l = st s0 (fun u => l.count u) := by
  have h0 : Ideal C (fun _ => 0) := fun u => ⟨Nat.zero_le _, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  have := valid_ideal_from hG l (fun _ => 0) h0 (by rw [st_zero]; exact hv)
  have e : addRun (fun _ => 0) l = fun u => l.count u := by funext u; simp [addRun]
  rw [e, st_zero] at this
  exact this

/-- **Safety**: a property of the states of all ideals holds after every valid run. -/
theorem reach_prop {en : α → (α → Bool) → Bool} {s0 : α → Bool} {C : Cert α} (hG : GCheck en s0 C)
    (P : (α → Bool) → Prop) (hP : ∀ c, Ideal C c → P (st s0 c)) (l : List α) (hv : Valid en s0 l) :
    P (after s0 l) := by
  obtain ⟨hi, he⟩ := valid_ideal hG l hv
  rw [he]; exact hP _ hi

/-! ## Termination and no deadlock -/

/-- Time stamps: increasing along each node's events and along causes; causes name existing events. -/
def TmOK (C : Cert α) : Prop :=
  (∀ u k, k + 1 < C.len u → C.tm u k < C.tm u (k + 1)) ∧
  (∀ u k, k < C.len u → ∀ p ∈ C.causes u k, p.2 < C.len p.1 ∧ C.tm p.1 p.2 < C.tm u k)

theorem tm_mono {C : Cert α} (hT : TmOK C) (u : α) :
    ∀ a b, a ≤ b → b < C.len u → C.tm u a ≤ C.tm u b := by
  intro a b hab hb
  induction b with
  | zero => have : a = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ b ih =>
    rcases Nat.lt_or_ge a (b + 1) with h | h
    · exact Nat.le_trans (ih (by omega) (by omega)) (Nat.le_of_lt (hT.1 u b hb))
    · have : a = b + 1 := by omega
      subst this; exact Nat.le_refl _

/-- **No deadlock**: in an ideal that is not full, some node is enabled. -/
theorem enabled_of_not_full {C : Cert α} (hT : TmOK C) {c : α → Nat} (hc : Ideal C c) :
    ∀ N u, c u < C.len u → C.tm u (c u) ≤ N → ∃ v, Enabled C c v := by
  intro N
  refine Nat.strongRecOn N ?_
  intro N ih
  intro u hu hN
  by_cases hall : ∀ p ∈ C.causes u (c u), p.2 < c p.1
  · exact ⟨u, hu, hall⟩
  · simp only [Classical.not_forall] at hall
    obtain ⟨p, hp, hlt⟩ := hall
    have hlt' : c p.1 ≤ p.2 := Nat.le_of_not_lt (by simpa using hlt)
    obtain ⟨hpl, hpt⟩ := hT.2 u (c u) hu p hp
    have hw : c p.1 < C.len p.1 := Nat.lt_of_le_of_lt hlt' hpl
    have hm := tm_mono hT p.1 (c p.1) p.2 hlt' hpl
    exact ih (C.tm p.1 (c p.1)) (by omega) p.1 hw (Nat.le_refl _)

/-- **Terminal ideals are full.** If no node is enabled in an ideal, every node has had all its events. -/
theorem terminal_full {en : α → (α → Bool) → Bool} {s0 : α → Bool} {C : Cert α} (hG : GCheck en s0 C)
    (hT : TmOK C) {c : α → Nat} (hc : Ideal C c) (hno : ∀ v, en v (st s0 c) = false) :
    ∀ u, c u = C.len u := by
  intro u
  rcases Nat.lt_or_ge (c u) (C.len u) with h | h
  · obtain ⟨v, hv⟩ := enabled_of_not_full hT hc _ u h (Nat.le_refl _)
    have := (hG c hc v).2 hv
    rw [hno v] at this; cases this
  · exact Nat.le_antisymm (hc u).1 h

/-- **Maximal runs.** A valid run after which no move is allowed fires every node exactly `len` times
and ends in the state of the full ideal: the same final state (and so the same recorded results) as the
certificate's run, whatever the order. -/
theorem maximal_run {en : α → (α → Bool) → Bool} {s0 : α → Bool} {C : Cert α} (hG : GCheck en s0 C)
    (hT : TmOK C) (l : List α) (hv : Valid en s0 l) (hmax : ∀ v, en v (after s0 l) = false) :
    (∀ u, l.count u = C.len u) ∧ after s0 l = st s0 C.len := by
  obtain ⟨hi, he⟩ := valid_ideal hG l hv
  rw [he] at hmax
  have hf := terminal_full hG hT hi hmax
  refine ⟨hf, ?_⟩
  rw [he]; congr 1; funext u; exact hf u

/-! ## Run length: no infinite schedule -/

/-- Sum of `f` over a list of nodes. -/
def sumOver (U : List α) (f : α → Nat) : Nat := U.foldr (fun u acc => f u + acc) 0

theorem sumOver_le {U : List α} {f g : α → Nat} (h : ∀ u ∈ U, f u ≤ g u) : sumOver U f ≤ sumOver U g := by
  induction U with
  | nil => simp [sumOver]
  | cons a U ih =>
    simp only [sumOver, List.foldr] at *
    have := h a (by simp)
    have := ih (fun u hu => h u (by simp [hu]))
    omega

theorem sumOver_zero (U : List α) : sumOver U (fun _ => 0) = 0 := by
  induction U with
  | nil => rfl
  | cons a U ih => simp only [sumOver, List.foldr] at *; omega

theorem sumOver_count (U : List α) (hU : U.Nodup) : ∀ (l : List α), (∀ v ∈ l, v ∈ U) →
    sumOver U (fun u => l.count u) = l.length
  | [], _ => by
    simp only [List.count_nil, List.length_nil]
    exact sumOver_zero U
  | v :: l, hl => by
    have ih := sumOver_count U hU l (fun w hw => hl w (by simp [hw]))
    have hvU : v ∈ U := hl v (by simp)
    -- sumOver U (count (v :: l)) = sumOver U (count l) + 1
    have key : ∀ (V : List α), V.Nodup →
        sumOver V (fun u => (v :: l).count u) = sumOver V (fun u => l.count u) + (if v ∈ V then 1 else 0) := by
      intro V hV
      induction V with
      | nil => simp [sumOver]
      | cons a V ihV =>
        obtain ⟨ha, hV'⟩ := List.nodup_cons.1 hV
        have := ihV hV'
        simp only [sumOver, List.foldr] at *
        rw [this]
        by_cases hav : a = v
        · subst hav
          simp [List.count_cons, ha]; omega
        · have hva : ¬ (v = a) := fun h => hav h.symm
          simp [List.count_cons, hav, hva]; omega
    rw [key U hU, ih]; simp [hvU]

/-- **Every valid run has at most `Σ len` moves** (`U` lists every node that has events, once each). -/
theorem run_length_le {en : α → (α → Bool) → Bool} {s0 : α → Bool} {C : Cert α} (hG : GCheck en s0 C)
    (U : List α) (hU : U.Nodup) (hcov : ∀ u, 0 < C.len u → u ∈ U) (l : List α) (hv : Valid en s0 l) :
    l.length ≤ sumOver U C.len := by
  obtain ⟨hi, _⟩ := valid_ideal hG l hv
  have hin : ∀ v ∈ l, v ∈ U := by
    intro v hv'
    apply hcov
    have h1 : 0 < l.count v := List.count_pos_iff.2 hv'
    exact Nat.lt_of_lt_of_le h1 (hi v).1
  rw [← sumOver_count U hU l hin]
  exact sumOver_le (fun u _ => (hi u).1)

theorem valid_append {en : α → (α → Bool) → Bool} :
    ∀ (s : α → Bool) (l₁ l₂ : List α), Valid en s l₁ → Valid en (after s l₁) l₂ → Valid en s (l₁ ++ l₂)
  | _, [], _, _, h₂ => h₂
  | s, v :: l₁, l₂, h₁, h₂ => ⟨h₁.1, valid_append (flip s v) l₁ l₂ h₁.2 h₂⟩

theorem after_append : ∀ (s : α → Bool) (l₁ l₂ : List α), after s (l₁ ++ l₂) = after (after s l₁) l₂
  | _, [], _ => rfl
  | s, v :: l₁, l₂ => after_append (flip s v) l₁ l₂

/-- **Every valid run extends to a maximal one** (with `Σ len - length` more moves at most, by
`run_length_le`); so with `maximal_run`, every schedule can be completed and every completion ends in the
certificate's final state. -/
theorem extend_run {en : α → (α → Bool) → Bool} {s0 : α → Bool} {C : Cert α} (hG : GCheck en s0 C)
    (hT : TmOK C) (U : List α) (hU : U.Nodup) (hcov : ∀ u, 0 < C.len u → u ∈ U) :
    ∀ (n : Nat) (l : List α), Valid en s0 l → sumOver U C.len - l.length ≤ n →
      ∃ l', Valid en s0 (l ++ l') ∧ ∀ v, en v (after s0 (l ++ l')) = false := by
  intro n
  induction n with
  | zero =>
    intro l hv hn
    refine ⟨[], by simpa using hv, fun v => ?_⟩
    simp only [List.append_nil]
    cases h : en v (after s0 l) with
    | false => rfl
    | true =>
      have hv2 : Valid en s0 (l ++ [v]) := valid_append s0 l [v] hv ⟨h, trivial⟩
      have := run_length_le hG U hU hcov _ hv2
      simp at this; omega
  | succ n ih =>
    intro l hv hn
    by_cases hex : ∃ v, en v (after s0 l) = true
    · obtain ⟨v, h⟩ := hex
      have hv2 : Valid en s0 (l ++ [v]) := valid_append s0 l [v] hv ⟨h, trivial⟩
      obtain ⟨l', h1, h2⟩ := ih (l ++ [v]) hv2 (by simp; omega)
      exact ⟨v :: l', by simpa using h1, by simpa using h2⟩
    · refine ⟨[], by simpa using hv, fun v => ?_⟩
      simp only [List.append_nil]
      cases h : en v (after s0 l) with
      | false => rfl
      | true => exact absurd ⟨v, h⟩ hex

/-! ## The local check -/

/-- Lower bounds `L u k w`: "at least `L u k w` events of `w` are at or below event `(u, k)`", sound for
every ideal. -/
def LSound (C : Cert α) (L : α → Nat → α → Nat) : Prop :=
  ∀ c, Ideal C c → ∀ u k w, k < c u → L u k w ≤ c w

/-- The one-step justification of a bound through the event's own node and its causes. -/
def causeBound (C : Cert α) (L : α → Nat → α → Nat) (u : α) (k : Nat) (w : α) : Nat :=
  (C.causes u k).foldr (fun p m => max m (max (L p.1 p.2 w) (if p.1 = w then p.2 + 1 else 0))) 0

def LStep (C : Cert α) (L : α → Nat → α → Nat) : Prop :=
  ∀ u k w, k < C.len u →
    L u k w ≤ max (if u = w then k + 1 else 0) (max (if k = 0 then 0 else L u (k - 1) w) (causeBound C L u k w))

theorem causeBound_le {C : Cert α} {L : α → Nat → α → Nat} {u : α} {k : Nat} {w : α} {B : Nat}
    (h : ∀ p ∈ C.causes u k, L p.1 p.2 w ≤ B ∧ (p.1 = w → p.2 + 1 ≤ B)) : causeBound C L u k w ≤ B := by
  unfold causeBound
  revert h
  generalize C.causes u k = cs
  intro h
  induction cs with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldr]
    have ha := h a (by simp)
    have := ih (fun p hp => h p (by simp [hp]))
    refine Nat.max_le.2 ⟨this, Nat.max_le.2 ⟨ha.1, ?_⟩⟩
    split
    · exact ha.2 (by assumption)
    · exact Nat.zero_le _

/-- **Bounds that pass the one-step check are sound** (induction on the time stamps). -/
theorem lsound_of_step {C : Cert α} {L : α → Nat → α → Nat} (hT : TmOK C) (hL : LStep C L) : LSound C L := by
  intro c hc
  suffices H : ∀ N u k w, k < c u → C.tm u k ≤ N → L u k w ≤ c w by
    intro u k w hk; exact H _ u k w hk (Nat.le_refl _)
  intro N
  refine Nat.strongRecOn N ?_
  intro N ih
  intro u k w hk hN
  have hkl : k < C.len u := Nat.lt_of_lt_of_le hk (hc u).1
  refine Nat.le_trans (hL u k w hkl) (Nat.max_le.2 ⟨?_, Nat.max_le.2 ⟨?_, ?_⟩⟩)
  · split
    · rename_i h; subst h; exact hk
    · exact Nat.zero_le _
  · split
    · exact Nat.zero_le _
    · rename_i h0
      have hlt : C.tm u (k - 1) < C.tm u k := by
        have := hT.1 u (k - 1) (by omega)
        rw [show k - 1 + 1 = k by omega] at this; exact this
      exact ih (C.tm u (k - 1)) (by omega) u (k - 1) w (by omega) (Nat.le_refl _)
  · apply causeBound_le
    intro p hp
    obtain ⟨_, hpt⟩ := hT.2 u k hkl p hp
    have hpc : p.2 < c p.1 := (hc u).2 k hk p hp
    refine ⟨ih (C.tm p.1 p.2) (by omega) p.1 p.2 w hpc (Nat.le_refl _), fun he => ?_⟩
    subst he; exact hpc

/-- **The local check at node `v`**: for every count vector `n` that respects the bounds on `v`'s
dependency list `D v` (and `len`), `en v` in `n`'s state is true exactly when `v`'s next event is enabled.
For a decidable version, `en v` must depend only on the nodes of `D v` and the causes of `v`'s events must
lie in `D v`; neither is needed for soundness. -/
def LCheck (en : α → (α → Bool) → Bool) (s0 : α → Bool) (C : Cert α) (L : α → Nat → α → Nat)
    (D : α → List α) (v : α) : Prop :=
  ∀ n : α → Nat, (∀ u ∈ D v, n u ≤ C.len u) → (∀ u ∈ D v, ∀ w ∈ D v, ∀ k, k < n u → L u k w ≤ n w) →
    (en v (st s0 n) = true ↔ Enabled C n v)

/-- **Local checks give the global check.** -/
theorem gcheck_of_local {en : α → (α → Bool) → Bool} {s0 : α → Bool} {C : Cert α} {L : α → Nat → α → Nat}
    {D : α → List α} (hL : LSound C L) (hloc : ∀ v, LCheck en s0 C L D v) : GCheck en s0 C := by
  intro c hc v
  exact hloc v c (fun u _ => (hc u).1) (fun u _ w _ k hk => hL c hc u k w hk)

/-- **Summary theorem.** Local checks, sound bounds and time stamps give: every valid run from the initial
state that cannot be extended fires each node exactly `len` times and ends in the certificate's final state;
every valid run can be so extended; and no valid run is longer than `Σ len`. -/
theorem occnet_summary {en : α → (α → Bool) → Bool} {s0 : α → Bool} {C : Cert α} {L : α → Nat → α → Nat}
    {D : α → List α} (hT : TmOK C) (hLs : LStep C L) (hloc : ∀ v, LCheck en s0 C L D v)
    (U : List α) (hU : U.Nodup) (hcov : ∀ u, 0 < C.len u → u ∈ U) :
    (∀ l, Valid en s0 l → (∀ v, en v (after s0 l) = false) →
        (∀ u, l.count u = C.len u) ∧ after s0 l = st s0 C.len) ∧
    (∀ l, Valid en s0 l → ∃ l', Valid en s0 (l ++ l') ∧ ∀ v, en v (after s0 (l ++ l')) = false) ∧
    (∀ l, Valid en s0 l → l.length ≤ sumOver U C.len) := by
  have hG := gcheck_of_local (lsound_of_step hT hLs) hloc
  exact ⟨fun l hv hm => maximal_run hG hT l hv hm,
    fun l hv => extend_run hG hT U hU hcov _ l hv (Nat.le_refl _),
    fun l hv => run_length_le hG U hU hcov l hv⟩

end Formal.Net.OccNet
