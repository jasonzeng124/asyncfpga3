/-!
# Windowed inductive invariants for guarded Boolean machines (shard C, composition)

**Problem, plainly.** THE target's control network has too many reachable states to list (40 M
for one operand pair before the run is even finished; JOURNAL-C 2026-11-06). Its persistence (needed by
`Keller`) should instead follow from a check whose size grows with the circuit, not with its
interleavings. A **windowed invariant** does that: for each small set of variables `W` (a window,
e.g. a control node and its support), a set `R` of allowed value tuples on `W`. The invariant says
every window's tuple is allowed. It is inductive if every move maps it into itself, and this can be
checked locally: a move only reads its own window and writes its own variables, so it suffices to
join the window being updated with the move's own window.

**Proved (generic, any machine given by guarded moves on Boolean variables).**
* `inv_step` / `inv_reach`: if the invariant holds initially and every window passes `closeOK` for
  every move (a finite Boolean check: for every allowed tuple of the window and every compatible
  allowed tuple of the move's window where the move is enabled, the updated tuple is allowed), then
  the invariant holds in every reachable state.
* `persist_of_check`: if `persistOK a b` (the same kind of join check), then in every state meeting
  the invariant where moves `a` and `b` are both enabled, `a` is still enabled after `b`.

**Not shown here.** That any particular machine's tables are the netlist's next-state functions,
or that a certificate for THE target passes (that is data, to be decided per window).
-/

namespace Formal.Net.WinInv

/-- A valuation of the machine's Boolean variables. -/
abbrev Val := Nat → Bool

/-- The tuple of `v` on window `W`: bit `p` is the value of `W[p]`. -/
def tup : List Nat → Val → Nat
  | [], _ => 0
  | x :: W, v => (if v x then 1 else 0) + 2 * tup W v

/-- The value of variable `x` in tuple `t` on window `W` (first occurrence; `false` if absent). -/
def bit : List Nat → Nat → Nat → Bool
  | [], _, _ => false
  | y :: W, t, x => if y = x then t % 2 = 1 else bit W (t / 2) x

/-- Update: the new value of `x` if the list assigns it, else `old x`. -/
def upd (u : List (Nat × Bool)) (old : Nat → Bool) (x : Nat) : Bool :=
  match u.lookup x with
  | some b => b
  | none => old x

/-- A guarded move: it reads the tuple on its window `win`; `en` is its guard; `eff` lists the
variables it may write; `asg` gives the new values (a function of the tuple). -/
structure Move where
  win : List Nat
  en : Nat → Bool
  eff : List Nat
  asg : Nat → List (Nat × Bool)

/-- The state after move `m` from `v`. -/
def post (m : Move) (v : Val) : Val := upd (m.asg (tup m.win v)) v

/-- The invariant: every window's tuple is allowed. -/
def Inv (Ws : List (List Nat × List Nat)) (v : Val) : Prop := ∀ p ∈ Ws, tup p.1 v ∈ p.2

/-- Two tuples agree on the variables their windows share. -/
def compat (W : List Nat) (t : Nat) (W' : List Nat) (t' : Nat) : Bool :=
  W.all fun x => !(W'.contains x) || (bit W t x == bit W' t' x)

/-- The tuple on `W` after the assignment `u`, from the old tuple `t`. -/
def newtup (W : List Nat) (t : Nat) (u : List (Nat × Bool)) : Nat :=
  tup W (upd u (bit W t))

/-- Assignments write only declared variables. -/
def effOK (m : Move) (Rm : List Nat) : Bool :=
  Rm.all fun t => (m.asg t).all fun p => m.eff.contains p.1

/-- **The closure check** of window `(W, R)` under move `m` whose own window relation is `Rm`. -/
def closeOK (W : List Nat) (R : List Nat) (m : Move) (Rm : List Nat) : Bool :=
  W.all (fun x => !(m.eff.contains x)) ||
  R.all fun t => Rm.all fun tm => !(compat W t m.win tm && m.en tm) || R.contains (newtup W t (m.asg tm))

/-- **The persistence check**: move `a` stays enabled after move `b`. -/
def persistOK (a : Move) (Ra : List Nat) (b : Move) (Rb : List Nat) : Bool :=
  Ra.all fun ta => Rb.all fun tb => !(compat a.win ta b.win tb && a.en ta && b.en tb) ||
    a.en (newtup a.win ta (b.asg tb))

/-! ## Lemmas -/

theorem tup_congr : ∀ (W : List Nat) (v w : Val), (∀ x ∈ W, v x = w x) → tup W v = tup W w
  | [], _, _, _ => rfl
  | x :: W, v, w, h => by
    simp only [tup]
    rw [h x List.mem_cons_self, tup_congr W v w (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem tup_mod (y : Nat) (W : List Nat) (v : Val) : decide (tup (y :: W) v % 2 = 1) = v y := by
  simp only [tup]
  by_cases hv : v y = true
  · simp [hv]
  · have hf : v y = false := by simpa using hv
    simp [hf]

theorem tup_div (y : Nat) (W : List Nat) (v : Val) : tup (y :: W) v / 2 = tup W v := by
  simp only [tup]
  by_cases hv : v y = true
  · simp [hv]; omega
  · have hf : v y = false := by simpa using hv
    simp [hf]

theorem bit_tup : ∀ (W : List Nat) (v : Val) (x : Nat), x ∈ W → bit W (tup W v) x = v x
  | [], _, _, h => by cases h
  | y :: W, v, x, h => by
    by_cases hy : y = x
    · subst hy
      have e : bit (y :: W) (tup (y :: W) v) y = decide (tup (y :: W) v % 2 = 1) := by simp [bit]
      rw [e, tup_mod]
    · have hx : x ∈ W := by
        cases h with
        | head => exact absurd rfl hy
        | tail _ h => exact h
      have e : bit (y :: W) (tup (y :: W) v) x = bit W (tup (y :: W) v / 2) x := by simp [bit, hy]
      rw [e, tup_div]; exact bit_tup W v x hx

theorem compat_tup (W W' : List Nat) (v : Val) : compat W (tup W v) W' (tup W' v) = true := by
  unfold compat
  rw [List.all_eq_true]
  intro x hx
  by_cases h : W'.contains x
  · have hx' : x ∈ W' := by simpa using h
    rw [bit_tup W v x hx, bit_tup W' v x hx']; simp
  · have hn : x ∉ W' := by simpa using h
    simp [hn]

theorem newtup_tup (W : List Nat) (v : Val) (u : List (Nat × Bool)) :
    newtup W (tup W v) u = tup W (upd u v) := by
  unfold newtup
  apply tup_congr
  intro x hx
  unfold upd
  cases u.lookup x with
  | none => exact bit_tup W v x hx
  | some b => rfl

theorem upd_not_mem (u : List (Nat × Bool)) (v : Val) (x : Nat) (h : ∀ p ∈ u, p.1 ≠ x) :
    upd u v x = v x := by
  unfold upd
  have : u.lookup x = none := by
    induction u with
    | nil => rfl
    | cons p u ih =>
      obtain ⟨a, b⟩ := p
      have ha : a ≠ x := h (a, b) List.mem_cons_self
      simp only [List.lookup]
      have : (x == a) = false := by simp; exact Ne.symm ha
      rw [this]; exact ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
  rw [this]

/-- **One move preserves the invariant**, given the checks for every window. -/
theorem inv_step (Ws : List (List Nat × List Nat)) (m : Move) (Rm : List Nat)
    (hm : (m.win, Rm) ∈ Ws) (heff : effOK m Rm = true)
    (hchk : ∀ p ∈ Ws, closeOK p.1 p.2 m Rm = true)
    (v : Val) (hv : Inv Ws v) (hen : m.en (tup m.win v) = true) : Inv Ws (post m v) := by
  intro p hp
  have hW := hv p hp
  have hmv := hv (m.win, Rm) hm
  simp only at hmv
  have hc := hchk p hp
  unfold closeOK at hc
  rcases Bool.or_eq_true_iff.1 hc with hno | hall
  · -- the move writes no variable of the window
    have : tup p.1 (post m v) = tup p.1 v := by
      apply tup_congr
      intro x hx
      unfold post
      apply upd_not_mem
      intro q hq hqx
      unfold effOK at heff
      have h2 := (List.all_eq_true.1 heff) _ hmv
      have h3 := (List.all_eq_true.1 h2) q hq
      have h4 := (List.all_eq_true.1 hno) x hx
      subst hqx
      simp_all
    rw [this]; exact hW
  · have h1 := (List.all_eq_true.1 hall) _ hW
    have h2 := (List.all_eq_true.1 h1) _ hmv
    rw [compat_tup, hen] at h2
    simp only [Bool.and_self, Bool.not_true, Bool.false_or] at h2
    rw [newtup_tup] at h2
    unfold post
    simpa using h2

/-- The machine's reachable states from `v0` under the moves `ms`. -/
inductive Reach (ms : List Move) (v0 : Val) : Val → Prop
  | init : Reach ms v0 v0
  | step {v : Val} (m : Move) : m ∈ ms → Reach ms v0 v → m.en (tup m.win v) = true →
      Reach ms v0 (post m v)

/-- **The invariant holds in every reachable state**, given the initial state and the checks. -/
theorem inv_reach (Ws : List (List Nat × List Nat)) (ms : List Move) (v0 : Val)
    (h0 : Inv Ws v0)
    (hm : ∀ m ∈ ms, ∃ Rm, (m.win, Rm) ∈ Ws ∧ effOK m Rm = true ∧ ∀ p ∈ Ws, closeOK p.1 p.2 m Rm = true)
    (v : Val) (hr : Reach ms v0 v) : Inv Ws v := by
  induction hr with
  | init => exact h0
  | step m hmem _ hen ih =>
    obtain ⟨Rm, hW, he, hc⟩ := hm m hmem
    exact inv_step Ws m Rm hW he hc _ ih hen

/-- **Persistence from the check**: in a state meeting the invariant, if moves `a` and `b` are
enabled and `persistOK a Ra b Rb`, then `a` is still enabled after `b`. -/
theorem persist_of_check (Ws : List (List Nat × List Nat)) (a b : Move) (Ra Rb : List Nat)
    (ha : (a.win, Ra) ∈ Ws) (hb : (b.win, Rb) ∈ Ws) (hchk : persistOK a Ra b Rb = true)
    (v : Val) (hv : Inv Ws v) (hea : a.en (tup a.win v) = true) (heb : b.en (tup b.win v) = true) :
    a.en (tup a.win (post b v)) = true := by
  have h1 := (List.all_eq_true.1 hchk) _ (hv _ ha)
  have h2 := (List.all_eq_true.1 h1) _ (hv _ hb)
  rw [compat_tup, hea, heb] at h2
  simp only [Bool.and_self, Bool.not_true, Bool.false_or] at h2
  rw [newtup_tup] at h2
  exact h2

end Formal.Net.WinInv
