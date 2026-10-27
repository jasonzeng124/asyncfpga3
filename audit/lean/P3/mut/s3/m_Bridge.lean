import Formal.Net.Prelim

/-!
# Probe 8d: from speed-independent interleavings to timed traces

Track 8/9 bridge. `Formal/Net/Ring.lean` (probe 9a) proves the ring theorems
under H_SI: "the ring evolves by firing one excited gate at a time". This file
discharges H_SI for a *generic* network of gates under a discrete-time
(`Nat` ps) timed semantics, for every *persistent* network.

## Model
* A network (`Net`) has gates `0 … n-1`; gate `i` drives node `i`, and its
  next-state function `f i : State → Bool` reads the current node values (for
  a LUT gate, `lutB INIT` of its real pins; its own output may be one of them:
  the feedback pin). Nodes `j ≥ n` do not exist (they never change: `frame`).
* SI semantics: `excited s i` iff `f i s ≠ s i`; `fire` flips one excited
  node; `Reach`, `Run` (a finite firing sequence), `Persistent` (every
  reachable SI state: an excited gate stays excited when another one fires).
* Timed semantics: a trace `x : Nat → State` (node values at each ps). Gate `i`
  is the zero-delay function `e_i t = f i (x t)` (the LUT's combinational
  value of its current pins) followed by a delay channel to node `i`. The
  channel is **inertial with bounds `[lo, hi]`** (`Inertial`):
  - cause: node `i` changes at `t → t+1` only to a value that `e_i` held on
    the whole window `[t+1-lo, t]` (`lo ≥ 1`), i.e. pulses of `e_i` shorter
    than `lo` are swallowed;
  - settle: if `e_i` held one value on `[t-hi, t]`, node `i` has it at `t`.
  The delay is a relation (every change may take any delay allowed by the
  window), not a function.
* **H_ISO** (isochronic forks): every reader of node `j` sees the value
  `x t j` at the same instant. This is built into `e_i t = f i (x t)`: wire
  delays are not modelled here. `BridgeWire.lean` drops it for chosen wires by
  making them buffer gates of their own (then the network is a different one,
  and the bridge applies iff THAT network is persistent).

## Which channel: no overtaking is enough, pulse filtering is not used
`BoundedDelay` (H_BOUNDED_DELAY) lets a change of the output copy any input
value from `[lo, hi]` ticks ago. That is a bounded *transport* channel with a
per-change delay; it can replay a stale value after a newer one (an output
pulse with no input pulse). We prove (`inertial_bounded`) that `Inertial` is a
refinement of `BoundedDelay`, and (`BridgeTransport.transport_breaks_si`) that
the bridge is FALSE for `BoundedDelay`: a 4-gate persistent network has a
`BoundedDelay 1 4` trace that reaches a state no SI run reaches.
The bridge is proved for the weaker channel `NoOvertake` (every output change
delivers a value the input had at some time after the previous output change;
plus the same `settle`), which inertial satisfies (`Inertial.noOvertake`) and
which also admits every FIFO transport behaviour that does not reorder edges.
The proof never uses that inertial channels swallow runts: in a persistent
network an excitation is never withdrawn, so the LUT output has no runt.
What the fabric must give is therefore: (1) H_NO_OVERTAKE, a LUT + route never
delivers an older edge after a newer one of the same node; (2) H_ISO; (3) the
gate is a single atomic Boolean function (`H_FB_SETTLED` for a feedback LUT:
see `BridgeWire.fb3_timed_token_lost` for what goes wrong without it).

## Results
* `step_run`: in a persistent network, the set of nodes that change at one
  tick, serialized in increasing index order (any order works: `run_of_excited`
  takes any duplicate-free list), is an SI run, and it ends in the next state.
* `timed_reach`: every timed state is SI-reachable. `timed_run`: the change
  points of a timed trace on `[0, T)`, concatenated, form one SI run from
  `x 0` to `x T`. `timed_invariant`: every SI state invariant holds of timed
  traces.
* `timed_frozen`: (no persistence needed) a state with no excited gate is
  never left.
* `fires_within`: an excited gate fires within `hi` ticks (liveness under the
  upper bound).
* `goodF`, `timed_reachF`, `step_runF`, `timed_runF`, `fires_withinF`: the
  same for no-overtaking channels (`TimedF`). `Timed.toF`: inertial ⇒ no-overtaking.
* `unit_timed`: `Timed` is satisfiable for every network (non-vacuity).
* `realize`: conversely every finite SI run ending in a deadlock is an inertial
  timed trace (bounds `[1, H]`), so SI deadlocks are timed deadlocks.
-/

namespace Formal.Net.Bridge
open Formal.Net

abbrev State := Nat → Bool

/-- A network of `n` gates; gate `i` drives node `i` with next-state function `f i`. -/
structure Net where
  n : Nat
  f : Nat → State → Bool

section SI
variable (N : Net)

def excited (s : State) (i : Nat) : Prop := i < N.n ∧ N.f i s ≠ s i

def fire (s : State) (i : Nat) : State := fun j => if j = i then !s i else s j

inductive Reach (s0 : State) : State → Prop
  | refl : Reach s0 s0
  | step {s : State} (i : Nat) : Reach s0 s → excited N s i → Reach s0 (fire s i)

/-- Persistence (semi-modularity) on the SI-reachable states from `s0`. -/
def Persistent (s0 : State) : Prop :=
  ∀ s, Reach N s0 s → ∀ i j, excited N s i → excited N s j → i ≠ j →
    excited N (fire s j) i

def Run : State → List Nat → Prop
  | _, [] => True
  | s, i :: is => excited N s i ∧ Run (fire s i) is

def final : State → List Nat → State
  | s, [] => s
  | s, i :: is => final (fire s i) is
end SI

variable {N : Net}

theorem run_reach {s0 s : State} (h0 : Reach N s0 s) :
    ∀ {is : List Nat}, Run N s is → Reach N s0 (final s is) := by
  intro is
  induction is generalizing s with
  | nil => intro _; exact h0
  | cons i is ih => intro ⟨he, hr⟩; exact ih (Reach.step i h0 he) hr

theorem final_append (s : State) (a b : List Nat) : final s (a ++ b) = final (final s a) b := by
  induction a generalizing s with
  | nil => rfl
  | cons i a ih => exact ih (fire s i)

theorem run_append {s : State} {a b : List Nat} :
    Run N s (a ++ b) ↔ Run N s a ∧ Run N (final s a) b := by
  induction a generalizing s with
  | nil => simp [Run, final]
  | cons i a ih =>
    show (excited N s i ∧ Run N (fire s i) (a ++ b)) ↔
      (excited N s i ∧ Run N (fire s i) a) ∧ Run N (final (fire s i) a) b
    rw [ih]; constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩

/-- An excited gate stays excited along any run that does not fire it. -/
theorem persist_run {s0 : State} (hp : Persistent N s0) {i : Nat} :
    ∀ {L : List Nat} {s : State}, Reach N s0 s → excited N s i → Run N s L → i ∉ L →
      excited N (final s L) i := by
  intro L
  induction L with
  | nil => intro s _ he _ _; exact he
  | cons j L ih =>
    intro s hr he ⟨hj, hrun⟩ hni
    have hij : i ≠ j := fun h => hni (h ▸ List.mem_cons_self ..)
    have hni' : i ∉ L := fun h => hni (List.mem_cons_of_mem _ h)
    exact ih (Reach.step j hr hj) (hp s hr i j he hj hij) hrun hni'

/-- Any duplicate-free list of gates excited in a reachable state is a run,
in whatever order it is listed (this is where persistence is used). -/
theorem run_of_excited {s0 : State} (hp : Persistent N s0) :
    ∀ {L : List Nat} {s : State}, Reach N s0 s → L.Nodup → (∀ i, i ∈ L → excited N s i) →
      Run N s L := by
  intro L
  induction L with
  | nil => intro _ _ _ _; trivial
  | cons j L ih =>
    intro s hr hnd hall
    have hj := hall j (List.mem_cons_self ..)
    have hnd' := (List.nodup_cons.1 hnd)
    refine ⟨hj, ih (Reach.step j hr hj) hnd'.2 ?_⟩
    intro i hi
    have hij : i ≠ j := fun h => hnd'.1 (h ▸ hi)
    exact hp s hr i j (hall i (List.mem_cons_of_mem _ hi)) hj hij

theorem final_flip : ∀ {L : List Nat} (s : State), L.Nodup → ∀ j,
    final s L j = if j ∈ L then !s j else s j := by
  intro L
  induction L with
  | nil => intro s _ j; simp [final]
  | cons i L ih =>
    intro s hnd j
    have hnd' := List.nodup_cons.1 hnd
    show final (fire s i) L j = _
    rw [ih _ hnd'.2 j]
    by_cases hji : j = i
    · subst hji; simp [fire, hnd'.1]
    · simp [fire, hji]

/-! ## Timed semantics -/

/-- Inertial channel with delay bounds `[lo, hi]`, input `e`, output `o`. -/
structure Inertial (lo hi : Nat) (e o : Trace) : Prop where
  lo_pos : 1 ≤ lo
  cause  : ∀ t, changes o t → lo ≤ t + 1 ∧ ∀ u, t + 1 - lo ≤ u → u ≤ t → e u = o (t + 1)
  settle : ∀ t, hi ≤ t → stableOn e (t - hi) t → o t = e t

/-- The inertial channel is a refinement of H_BOUNDED_DELAY (`Prelim`). -/
theorem inertial_bounded {lo hi : Nat} {e o : Trace} (h : Inertial lo hi e o) (hlh : lo ≤ hi) :
    BoundedDelay lo hi e o where
  cause t hc := by
    obtain ⟨h1, h2⟩ := h.cause t hc
    have := h.lo_pos
    exact ⟨lo, Nat.le_refl _, hlh, h1, (h2 (t + 1 - lo) (Nat.le_refl _) (by omega)).symm⟩
  settle := h.settle

/-- A timed trace of the network: each gate is an inertial channel (per-gate
bounds `lo i`, `hi i`) after its zero-delay function of the CURRENT node
values (H_ISO); non-gate nodes never change. -/
structure Timed (N : Net) (lo hi : Nat → Nat) (x : Nat → State) : Prop where
  gate  : ∀ i, i < N.n → Inertial (lo i) (hi i) (fun t => N.f i (x t)) (fun t => x t i)
  frame : ∀ t j, N.n ≤ j → x (t + 1) j = x t j

/-- The nodes that change at `t → t+1`, in increasing index order. -/
def chg (N : Net) (x : Nat → State) (t : Nat) : List Nat :=
  (List.range N.n).filter (fun i => x t i != x (t + 1) i)

theorem mem_chg {x : Nat → State} {t i : Nat} :
    i ∈ chg N x t ↔ i < N.n ∧ x t i ≠ x (t + 1) i := by
  unfold chg; simp [List.mem_filter, List.mem_range]

theorem chg_nodup (x : Nat → State) (t : Nat) : (chg N x t).Nodup :=
  List.Pairwise.filter _ List.nodup_range

variable {lo hi : Nat → Nat} {x : Nat → State}

/-- A change of a gate output at `t → t+1` is a firing of an excited gate. -/
theorem chg_excited (hx : Timed N lo hi x) {t i : Nat} (h : i ∈ chg N x t) :
    excited N (x t) i := by
  obtain ⟨hi, hc⟩ := mem_chg.1 h
  have g := hx.gate i hi
  obtain ⟨_, hw⟩ := g.cause t hc
  have := g.lo_pos
  have he : N.f i (x t) = x (t + 1) i := hw t (by omega) (Nat.le_refl _)
  refine ⟨hi, ?_⟩
  rw [he]; exact fun h' => hc h'.symm

theorem final_chg_frame (hf : ∀ t j, N.n ≤ j → x (t + 1) j = x t j) (t : Nat) :
    final (x t) (chg N x t) = x (t + 1) := by
  funext j
  rw [final_flip _ (chg_nodup x t) j]
  by_cases hj : j < N.n
  · by_cases hc : x t j = x (t + 1) j
    · have : j ∉ chg N x t := fun h => (mem_chg.1 h).2 hc
      simp [this, hc]
    · have : j ∈ chg N x t := mem_chg.2 ⟨hj, hc⟩
      simp only [this, ite_true]
      revert hc; cases x t j <;> cases x (t + 1) j <;> simp
  · have : j ∉ chg N x t := fun h => hj (mem_chg.1 h).1
    simp only [this, ite_false]
    exact (hf t j (by omega)).symm

theorem final_chg (hx : Timed N lo hi x) (t : Nat) : final (x t) (chg N x t) = x (t + 1) :=
  final_chg_frame hx.frame t

/-! ## The weakest channel the bridge needs: no overtaking

`NoOvertake hi e o`: every change of `o` delivers a value that `e` had at some
time `t'` AFTER the previous change of `o` (`o` constant on `[t', t]`): the
channel never delivers an edge older than one it already delivered. Bounded
pure delay with a per-edge delay (`Prelim.BoundedDelay`) can violate it
(`BridgeTransport`); the inertial channel satisfies it with `t' = t`
(`Inertial.noOvertake`). Pulse filtering is NOT needed: in a persistent
network an excitation is never withdrawn, so `e` has no runt to filter. -/

structure NoOvertake (hi : Nat) (e o : Trace) : Prop where
  fifo   : ∀ t, changes o t → ∃ t', t' ≤ t ∧ e t' = o (t + 1) ∧ ∀ u, t' ≤ u → u ≤ t → o u = o t
  settle : ∀ t, hi ≤ t → stableOn e (t - hi) t → o t = e t

theorem Inertial.noOvertake {lo hi : Nat} {e o : Trace} (h : Inertial lo hi e o) :
    NoOvertake hi e o where
  fifo t hc := by
    obtain ⟨_, hw⟩ := h.cause t hc
    have := h.lo_pos
    exact ⟨t, Nat.le_refl _, hw t (by omega) (Nat.le_refl _), fun u h1 h2 => by
      have : u = t := by omega
      rw [this]⟩
  settle := h.settle

/-- Timed traces with no-overtaking channels (weaker than `Timed`). -/
structure TimedF (N : Net) (hi : Nat → Nat) (x : Nat → State) : Prop where
  gate  : ∀ i, i < N.n → NoOvertake (hi i) (fun t => N.f i (x t)) (fun t => x t i)
  frame : ∀ t j, N.n ≤ j → x (t + 1) j = x t j

theorem Timed.toF (hx : Timed N lo hi x) : TimedF N hi x :=
  ⟨fun i h => (hx.gate i h).noOvertake, hx.frame⟩

theorem final_chgF (hx : TimedF N hi x) (t : Nat) : final (x t) (chg N x t) = x (t + 1) :=
  final_chg_frame hx.frame t

/-- The change points of `x` on `[t, t+m)`, concatenated. -/
def obs (N : Net) (x : Nat → State) (t : Nat) : Nat → List Nat
  | 0 => []
  | m + 1 => obs N x t m ++ chg N x (t + m)

theorem obs_run {s0 : State} (hp : Persistent N s0) (hx : TimedF N hi x) {t : Nat} :
    ∀ m, (∀ u, t ≤ u → u < t + m → Reach N s0 (x u) ∧ ∀ i, i ∈ chg N x u → excited N (x u) i) →
      Run N (x t) (obs N x t m) ∧ final (x t) (obs N x t m) = x (t + m) := by
  intro m
  induction m with
  | zero => intro _; exact ⟨trivial, rfl⟩
  | succ m ih =>
    intro hu
    obtain ⟨hr, hf⟩ := ih (fun u h1 h2 => hu u h1 (by omega))
    obtain ⟨hR, hE⟩ := hu (t + m) (by omega) (by omega)
    have hr2 := run_of_excited hp hR (chg_nodup x (t + m)) hE
    simp only [obs]
    refine ⟨run_append.2 ⟨hr, ?_⟩, ?_⟩
    · rw [hf]; exact hr2
    · rw [final_append, hf, final_chgF hx]; rfl

theorem not_mem_obs {x : Nat → State} {t i : Nat} :
    ∀ {m}, (∀ u, t ≤ u → u < t + m → x (u + 1) i = x u i) → i ∉ obs N x t m := by
  intro m
  induction m with
  | zero => intro _ h; simp [obs] at h
  | succ m ih =>
    intro hc h
    simp only [obs, List.mem_append] at h
    rcases h with h | h
    · exact ih (fun u h1 h2 => hc u h1 (by omega)) h
    · exact (mem_chg.1 h).2 (hc (t + m) (by omega) (by omega)).symm

/-- The induction behind the bridge (strong in time): every state up to `t` is
SI-reachable and every change before `t` is the firing of an excited gate. -/
theorem goodF {s0 : State} (hp : Persistent N s0) (hx : TimedF N hi x) (h0 : x 0 = s0) :
    ∀ t, (∀ u, u ≤ t → Reach N s0 (x u)) ∧
      (∀ u, u < t → ∀ i, i ∈ chg N x u → excited N (x u) i) := by
  intro t
  induction t with
  | zero =>
    refine ⟨fun u hu => ?_, fun u hu => absurd hu (Nat.not_lt_zero _)⟩
    have : u = 0 := by omega
    rw [this, h0]; exact .refl
  | succ t ih =>
    obtain ⟨hR, hE⟩ := ih
    -- the changes at `t` are firings of excited gates
    have hEt : ∀ i, i ∈ chg N x t → excited N (x t) i := by
      intro i hm
      obtain ⟨hi, hc⟩ := mem_chg.1 hm
      obtain ⟨t', ht', he, hconst⟩ := (hx.gate i hi).fifo t hc
      have ex' : excited N (x t') i := ⟨hi, by
        show N.f i (x t') ≠ x t' i
        rw [he, hconst t' (Nat.le_refl _) ht']; exact fun h => hc h.symm⟩
      obtain ⟨hrun, hfin⟩ := obs_run hp hx (t := t') (t - t') (fun u h1 h2 =>
        ⟨hR u (by omega), hE u (by omega)⟩)
      have hni : i ∉ obs N x t' (t - t') := not_mem_obs (fun u h1 h2 => by
        rw [hconst u h1 (by omega), hconst (u + 1) (by omega) (by omega)])
      have := persist_run hp (hR t' ht') ex' hrun hni
      rwa [hfin, show t' + (t - t') = t by omega] at this
    refine ⟨fun u hu => ?_, fun u hu => ?_⟩
    · by_cases e : u = t + 1
      · subst e
        have hr := hR t (Nat.le_refl _)
        rw [← final_chgF hx t]
        exact run_reach hr (run_of_excited hp hr (chg_nodup x t) hEt)
      · exact hR u (by omega)
    · by_cases e : u = t
      · subst e; exact hEt
      · exact hE u (by omega)

/-- **Every timed state is SI-reachable** (no-overtaking channels). -/
theorem timed_reachF {s0 : State} (hp : Persistent N s0) (hx : TimedF N hi x)
    (h0 : x 0 = s0) (t : Nat) : Reach N s0 (x t) :=
  (goodF hp hx h0 t).1 t (Nat.le_refl _)

/-- **One tick is an SI run.** In a persistent network, the simultaneous
changes at one tick, serialized (here by index; any order, `run_of_excited`),
are an SI run from `x t` to `x (t+1)`. -/
theorem step_runF {s0 : State} (hp : Persistent N s0) (hx : TimedF N hi x) (h0 : x 0 = s0)
    (t : Nat) : Run N (x t) (chg N x t) ∧ final (x t) (chg N x t) = x (t + 1) :=
  ⟨run_of_excited hp (timed_reachF hp hx h0 t) (chg_nodup x t)
    ((goodF hp hx h0 (t + 1)).2 t (Nat.lt_succ_self _)), final_chgF hx t⟩

/-- **The observed timed trace is one SI run** from `x t` to `x (t+m)`. -/
theorem timed_runF {s0 : State} (hp : Persistent N s0) (hx : TimedF N hi x)
    (h0 : x 0 = s0) (t m : Nat) :
    Run N (x t) (obs N x t m) ∧ final (x t) (obs N x t m) = x (t + m) :=
  obs_run hp hx m (fun u _ _ =>
    ⟨timed_reachF hp hx h0 u, (goodF hp hx h0 (u + 1)).2 u (Nat.lt_succ_self _)⟩)

/-- **Liveness under the upper bound**: an excited gate fires within `hi i`
ticks (persistence keeps its LUT value constant while it waits). -/
theorem fires_withinF {s0 : State} (hp : Persistent N s0) (hx : TimedF N hi x)
    (h0 : x 0 = s0) {t i : Nat} (he : excited N (x t) i) :
    ∃ u, t ≤ u ∧ u < t + hi i ∧ x (u + 1) i ≠ x u i := by
  apply Classical.byContradiction
  intro hno
  have still : ∀ u, t ≤ u → u < t + hi i → x (u + 1) i = x u i := by
    intro u h1 h2
    apply Classical.byContradiction; intro hc
    exact hno ⟨u, h1, h2, hc⟩
  have key : ∀ k, k ≤ hi i → x (t + k) i = x t i ∧ excited N (x (t + k)) i := by
    intro k
    induction k with
    | zero => intro _; exact ⟨rfl, he⟩
    | succ k ih =>
      intro hk
      obtain ⟨h1, h2⟩ := ih (by omega)
      have hs := still (t + k) (by omega) (by omega)
      refine ⟨by rw [← Nat.add_assoc, hs, h1], ?_⟩
      have hr := timed_reachF hp hx h0 (t + k)
      obtain ⟨hrun, hfin⟩ := step_runF hp hx h0 (t + k)
      have hni : i ∉ chg N x (t + k) := fun h => (mem_chg.1 h).2 hs.symm
      have := persist_run hp hr h2 hrun hni
      rw [hfin] at this; rw [← Nat.add_assoc]; exact this
  have hval : ∀ k, k ≤ hi i → N.f i (x (t + k)) = !x t i := by
    intro k hk
    obtain ⟨h1, ⟨_, h2⟩⟩ := key k hk
    rw [h1] at h2
    revert h2; cases N.f i (x (t + k)) <;> cases x t i <;> simp
  have hi' := he.1
  have g := (hx.gate i hi').settle (t + hi i) (by omega) (by
    intro u h1 h2
    have e1 := hval (u - (t + hi i - hi i)) (by omega)
    have e2 := hval (t + hi i - hi i - t) (by omega)
    have a1 : t + (u - (t + hi i - hi i)) = u := by omega
    have a2 : t + (t + hi i - hi i - t) = t + hi i - hi i := by omega
    rw [a1] at e1; rw [a2] at e2
    show N.f i (x u) = N.f i (x (t + hi i - hi i))
    rw [e1, e2])
  have e3 := hval (hi i) (Nat.le_refl _)
  have e4 := (key (hi i) (Nat.le_refl _)).1
  rw [e3, e4] at g
  revert g; cases x t i <;> simp

/-! ### The same, for inertial channels (`Timed`) -/

theorem step_run {s0 : State} (hp : Persistent N s0) (hx : Timed N lo hi x) {t : Nat}
    (hr : Reach N s0 (x t)) :
    Run N (x t) (chg N x t) ∧ final (x t) (chg N x t) = x (t + 1) :=
  ⟨run_of_excited hp hr (chg_nodup x t) (fun _ h => chg_excited hx h), final_chg hx t⟩

theorem timed_reach {s0 : State} (hp : Persistent N s0) (hx : Timed N lo hi x)
    (h0 : x 0 = s0) (t : Nat) : Reach N s0 (x t) := timed_reachF hp hx.toF h0 t

theorem timed_run {s0 : State} (hp : Persistent N s0) (hx : Timed N lo hi x)
    (h0 : x 0 = s0) (t m : Nat) :
    Run N (x t) (obs N x t m) ∧ final (x t) (obs N x t m) = x (t + m) :=
  timed_runF hp hx.toF h0 t m

/-- **Every SI state invariant holds of every timed trace.** -/
theorem timed_invariantF {s0 : State} (hp : Persistent N s0) (hx : TimedF N hi x)
    (h0 : x 0 = s0) {P : State → Prop} (hP : ∀ s, Reach N s0 s → P s) : ∀ t, P (x t) :=
  fun t => hP _ (timed_reachF hp hx h0 t)

theorem timed_invariant {s0 : State} (hp : Persistent N s0) (hx : Timed N lo hi x)
    (h0 : x 0 = s0) {P : State → Prop} (hP : ∀ s, Reach N s0 s → P s) : ∀ t, P (x t) :=
  timed_invariantF hp hx.toF h0 hP

theorem fires_within {s0 : State} (hp : Persistent N s0) (hx : Timed N lo hi x)
    (h0 : x 0 = s0) {t i : Nat} (he : excited N (x t) i) :
    ∃ u, t ≤ u ∧ u < t + hi i ∧ x (u + 1) i ≠ x u i :=
  fires_withinF hp hx.toF h0 he

/-- A state with no excited gate is never left (inertial; no persistence needed). -/
theorem timed_frozen (hx : Timed N lo hi x) {t : Nat} (hd : ∀ i, ¬ excited N (x t) i) :
    x (t + 1) = x t := by
  rw [← final_chg hx t]
  cases h : chg N x t with
  | nil => rfl
  | cons i _ =>
    have : i ∈ chg N x t := by rw [h]; exact List.mem_cons_self ..
    exact absurd (chg_excited hx this) (hd i)

/-! ## Non-vacuity and the converse direction -/

/-- Synchronous unit-delay execution: every excited gate fires at the next tick. -/
def stepAll (N : Net) (s : State) : State := fun j => if j < N.n then N.f j s else s j

def unitTrace (N : Net) (s0 : State) : Nat → State
  | 0 => s0
  | t + 1 => stepAll N (unitTrace N s0 t)

/-- `Timed` is satisfiable for every network and initial state (so the
theorems above are not vacuous): the unit-delay trace is an inertial
execution with `lo = hi = 1`. -/
theorem unit_timed (N : Net) (s0 : State) :
    Timed N (fun _ => 2) (fun _ => 2) (unitTrace N s0) where
  gate i hi := {
    lo_pos := Nat.le_refl _
    cause := by
      intro t _
      refine ⟨by omega, fun u h1 h2 => ?_⟩
      have : u = t := by omega
      subst this; simp [unitTrace, stepAll, hi]
    settle := by
      intro t ht hs
      obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
      have := hs (t' + 1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at this
      show unitTrace N s0 (t' + 1) i = N.f i (unitTrace N s0 (t' + 1))
      rw [this]; simp [unitTrace, stepAll, hi] }
  frame t j hj := by
    show stepAll N (unitTrace N s0 t) j = _
    simp [stepAll]; omega

/-- The trace that performs the run `L` one firing per tick, then stops. -/
def runTrace : State → List Nat → Nat → State
  | s, [], _ => s
  | s, _ :: _, 0 => s
  | s, i :: L, t + 1 => runTrace (fire s i) L t

theorem runTrace_step : ∀ {L : List Nat} {s : State}, Run N s L → ∀ t,
    runTrace s L (t + 1) = runTrace s L t ∨
    ∃ i, excited N (runTrace s L t) i ∧ runTrace s L (t + 1) = fire (runTrace s L t) i := by
  intro L
  induction L with
  | nil => intro s _ t; left; rfl
  | cons i L ih =>
    intro s ⟨he, hr⟩ t
    cases t with
    | zero =>
      right; refine ⟨i, he, ?_⟩
      show runTrace (fire s i) L 0 = fire s i
      cases L <;> rfl
    | succ t => exact ih hr t

theorem runTrace_late : ∀ {L : List Nat} {s : State} {t : Nat}, L.length ≤ t →
    runTrace s L t = final s L := by
  intro L
  induction L with
  | nil => intro s t _; rfl
  | cons i L ih =>
    intro s t h
    cases t with
    | zero => simp at h
    | succ t => exact ih (by simp at h; omega)

theorem runTrace_zero (s : State) (L : List Nat) : runTrace s L 0 = s := by
  cases L <;> rfl

/-- **Converse (deadlocks are real).** Every finite SI run that ends in a
state with no excited gate is a timed trace, one firing per tick, with every
gate an inertial channel with bounds `[1, H]` for any `H ≥` the run length. So
an SI deadlock (lost token, ...) is reachable in time, for those bounds. -/
theorem realize {s0 : State} {L : List Nat} (hr : Run N s0 L)
    (hd : ∀ i, ¬ excited N (final s0 L) i) {H : Nat} (hH : L.length ≤ H) :
    Timed N (fun _ => 1) (fun _ => H) (runTrace s0 L) where
  gate g hg := {
    lo_pos := Nat.le_refl _
    cause := by
      intro t hc
      refine ⟨by omega, fun u h1 h2 => ?_⟩
      have : u = t := by omega
      subst this
      rcases runTrace_step hr u with h | ⟨i, he, h⟩
      · exact absurd (by show runTrace s0 L u g = runTrace s0 L (u + 1) g; rw [h]) hc
      · by_cases hgi : g = i
        · subst hgi
          show N.f g (runTrace s0 L u) = runTrace s0 L (u + 1) g
          rw [h]; simp only [fire, ite_true]
          have := he.2; revert this
          cases N.f g (runTrace s0 L u) <;> cases runTrace s0 L u g <;> simp
        · exact absurd (by
            show runTrace s0 L u g = runTrace s0 L (u + 1) g
            rw [h]; simp [fire, hgi]) hc
    settle := by
      intro t ht _
      show runTrace s0 L t g = N.f g (runTrace s0 L t)
      rw [runTrace_late (by omega)]
      have := hd g
      apply Classical.byContradiction; intro hne
      exact this ⟨hg, fun h => hne h.symm⟩ }
  frame t j hj := by
    rcases runTrace_step hr t with h | ⟨i, he, h⟩
    · rw [h]
    · rw [h]; have : j ≠ i := by have := he.1; omega
      simp [fire, this]

theorem runTrace_final {s0 : State} {L : List Nat} {t : Nat} (h : L.length ≤ t) :
    runTrace s0 L t = final s0 L := runTrace_late h

end Formal.Net.Bridge
