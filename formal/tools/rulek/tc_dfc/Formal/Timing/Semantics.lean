import Formal.Net.Prelim

/-!
# Timing semantics of a routed netlist with delay intervals (probe C-10a)

Core Lean only. Time is `Nat` (1 tick = 1 ps), signals are `Formal.Net.Trace`.

A **netlist** is a list of arcs `src → dst` with a delay interval `[lo, hi]`.
Cell arcs (LUT pin → O, latch D → Q, ...) and routing arcs (wire, pip) are the
same kind of object; that is also how prjxray's timing model is shaped
(per-pin cell delays plus per-wire/per-pip delays).
Node `0` is the **launch** node (one transition of the launching element).

A **run** of a netlist (`Run`) is the conjunction of the arc and node relations:

* `H_LAUNCH`         node 0 changes at most once, at time 0.
* `H_BOUNDED_DELAY`  each arc `k : u → v` has its own pin trace `pin k`, related
  to `sig u` by `Formal.Net.BoundedDelay lo hi` (Prelim's channel, unchanged:
  every change of the pin copies a value `u` held `d ∈ [lo, hi]` ticks earlier,
  and a value held for `hi` ticks is copied). The delay may differ from event to
  event; short pulses pass (pure delay, no inertial filtering).
* `H_QUIESCENT`      each pin starts equal to its source (`pin k 0 = sig u 0`):
  the netlist was at rest before the launch.
* `H_LOCAL`          the node function of `v` reads only pins of arcs into `v`.
* `H_ZERO_DELAY_FN`  `sig v t = g v (pins at t)`: all delay of a cell is put on
  its input-pin arcs, the Boolean function itself is instantaneous. Any LUT
  (binary `Formal.Cells.lutB` on the pins) is an admissible `g v`; the theorems
  quantify over every local `g`, so they hold for every cell function at once.

`FixedRun` is the stricter semantics in which every arc has ONE delay
`d k ∈ [lo, hi]` for the whole run (a pin is an exact shift of its source):
the physically "one PVT corner, one wire, one delay" reading. Every fixed run is
a run (`FixedRun.toRun`), so everything proved for `Run` holds for it.
-/

namespace Formal.Timing
open Formal.Net

/-- One timing arc `src → dst` with delay interval `[lo, hi]` ps. -/
structure Arc where
  src : Nat
  dst : Nat
  lo : Nat
  hi : Nat
  deriving Repr, DecidableEq

/-- A netlist: a list of arcs. Node `0` is the launch node. -/
structure Netlist where
  arcs : List Arc
  deriving Repr

/-- Well-formed = arcs go from lower to higher node index (a DAG in which index
order is a topological order, and nothing drives the launch node), and every
interval is non-empty. -/
def Netlist.WF (net : Netlist) : Prop := ∀ a ∈ net.arcs, a.src < a.dst ∧ a.lo ≤ a.hi

instance (net : Netlist) : Decidable net.WF :=
  inferInstanceAs (Decidable (∀ a ∈ net.arcs, a.src < a.dst ∧ a.lo ≤ a.hi))

/-- H_LOCAL: `g` depends only on the pins of arcs into `v`. -/
def Local (net : Netlist) (v : Nat) (g : (Nat → Bool) → Bool) : Prop :=
  ∀ x y : Nat → Bool, (∀ k a, net.arcs[k]? = some a → a.dst = v → x k = y k) → g x = g y

/-- A run of `net` with node traces `sig`: witnesses (pins, node functions)
plus every hypothesis listed in the module doc. -/
structure Run (net : Netlist) (sig : Nat → Trace) where
  pin : Nat → Trace
  g : Nat → (Nat → Bool) → Bool
  launch : ∀ t, changes (sig 0) t → t = 0                                  -- H_LAUNCH
  bd : ∀ k a, net.arcs[k]? = some a → BoundedDelay a.lo a.hi (sig a.src) (pin k)  -- H_BOUNDED_DELAY
  quiet : ∀ k a, net.arcs[k]? = some a → pin k 0 = sig a.src 0               -- H_QUIESCENT
  local_ : ∀ v, Local net v (g v)                                           -- H_LOCAL
  node : ∀ v, v ≠ 0 → ∀ t, sig v t = g v (fun k => pin k t)                 -- H_ZERO_DELAY_FN

/-- A trace delayed by exactly `d` ticks (value before the launch = value at 0). -/
def shift (d : Nat) (i : Trace) : Trace := fun t => if t < d then i 0 else i (t - d)

/-- Pin `k` of a fixed-delay run: the source of arc `k` shifted by `d k`. -/
def fixedPin (net : Netlist) (d : Nat → Nat) (sig : Nat → Trace) (k : Nat) : Trace :=
  fun t => match net.arcs[k]? with
    | some a => shift (d k) (sig a.src) t
    | none => false

/-- Fixed-delay run: one delay per arc for the whole run. -/
structure FixedRun (net : Netlist) (sig : Nat → Trace) where
  d : Nat → Nat
  g : Nat → (Nat → Bool) → Bool
  launch : ∀ t, changes (sig 0) t → t = 0
  range : ∀ k a, net.arcs[k]? = some a → a.lo ≤ d k ∧ d k ≤ a.hi
  local_ : ∀ v, Local net v (g v)
  node : ∀ v, v ≠ 0 → ∀ t, sig v t = g v (fun k => fixedPin net d sig k t)

/-! ## Trace lemmas -/

/-- No change before `a` ⇒ constant on `[0, a]`. -/
theorem const_before {i : Trace} {a : Nat} (hw : ∀ s, changes i s → a ≤ s) :
    ∀ s, s ≤ a → i s = i 0 := by
  intro s
  induction s with
  | zero => intro _; rfl
  | succ s ih =>
    intro hs
    have h1 : i s = i (s + 1) := by
      apply Classical.byContradiction
      intro hc; have := hw s hc; omega
    rw [← h1]; exact ih (by omega)

/-- No change at or after `c` ⇒ constant from `c` on. -/
theorem const_from {i : Trace} {c : Nat} (hw : ∀ s, changes i s → s < c) :
    ∀ u, c ≤ u → i u = i c := by
  intro u hu
  obtain ⟨n, rfl⟩ : ∃ n, u = c + n := ⟨u - c, by omega⟩
  clear hu
  induction n with
  | zero => rfl
  | succ n ih =>
    have h1 : i (c + n) = i (c + n + 1) := by
      apply Classical.byContradiction
      intro hc; have := hw _ hc; omega
    rw [← Nat.add_assoc, ← h1]; exact ih

/-- **Arc window lemma.** Under H_BOUNDED_DELAY and H_QUIESCENT, if the input
changes only inside `[a, b]` then the output changes only inside
`[a + lo, b + hi]`. (If the input never changes, take any `a > t`: the output
never changes.) -/
theorem arc_window {lo hi a b t : Nat} {i o : Trace} (hbd : BoundedDelay lo hi i o)
    (h0 : o 0 = i 0) (hw : ∀ s, changes i s → a ≤ s ∧ s ≤ b) (ht : changes o t) :
    a + lo ≤ t ∧ t ≤ b + hi := by
  have ib : ∀ s, s ≤ a → i s = i 0 := const_before (fun s h => (hw s h).1)
  have ia : ∀ u, b + 1 ≤ u → i u = i (b + 1) :=
    const_from (fun s h => by have := (hw s h).2; omega)
  -- the output keeps the initial value up to a + lo
  have ob : ∀ s, s ≤ a + lo → o s = i 0 := by
    intro s
    induction s with
    | zero => intro _; exact h0
    | succ s ih =>
      intro hs
      by_cases hc : o s = o (s + 1)
      · rw [← hc]; exact ih (by omega)
      · obtain ⟨d, hld, _, hdt, heq⟩ := hbd.cause s hc
        rw [heq]; exact ib _ (by omega)
  constructor
  · apply Classical.byContradiction; intro hlt
    exact ht ((ob t (by omega)).trans (ob (t + 1) (by omega)).symm)
  · apply Classical.byContradiction; intro hlt
    have hset : ∀ u, b + 1 + hi ≤ u → o u = i (b + 1) := by
      intro u hu
      have hs : stableOn i (u - hi) u := by
        intro w h1 h2
        rw [ia w (by omega), ia (u - hi) (by omega)]
      rw [hbd.settle u (by omega) hs]; exact ia u (by omega)
    exact ht ((hset t (by omega)).trans (hset (t + 1) (by omega)).symm)

/-- A fixed delay `d ∈ [lo, hi]` is an H_BOUNDED_DELAY channel. -/
theorem shift_bd {lo hi d : Nat} (i : Trace) (hlo : lo ≤ d) (hhi : d ≤ hi) :
    BoundedDelay lo hi i (shift d i) where
  cause := by
    intro t ht
    have hdt : d ≤ t + 1 := by
      apply Classical.byContradiction; intro h
      apply ht; simp [shift]; rw [ite_eq_left (by omega), ite_eq_left (by omega)]
    refine ⟨d, hlo, hhi, hdt, ?_⟩
    simp only [shift]; rw [ite_eq_right (by omega)]
  settle := by
    intro t ht hs
    simp only [shift]; rw [ite_eq_right (by omega)]
    rw [hs (t - d) (by omega) (by omega), hs t (by omega) (by omega)]

theorem shift_zero (d : Nat) (i : Trace) : shift d i 0 = i 0 := by
  simp [shift]

/-- A shifted trace changes only `d` after a change of its source. -/
theorem shift_changes {d t : Nat} {i : Trace} (h : changes (shift d i) t) :
    d ≤ t ∧ changes i (t - d) := by
  have hdt : d ≤ t := by
    apply Classical.byContradiction; intro hc
    apply h; simp only [shift]
    rw [ite_eq_left (by omega)]
    by_cases h2 : t + 1 < d
    · rw [ite_eq_left h2]
    · rw [ite_eq_right h2, show t + 1 - d = 0 by omega]
  refine ⟨hdt, ?_⟩
  intro hc; apply h; simp only [shift]
  rw [ite_eq_right (by omega), ite_eq_right (by omega), show t + 1 - d = t - d + 1 by omega]; exact hc

/-- Every fixed-delay run is a run. -/
def FixedRun.toRun {net : Netlist} {sig : Nat → Trace} (r : FixedRun net sig) : Run net sig where
  pin := fixedPin net r.d sig
  g := r.g
  launch := r.launch
  bd := by
    intro k a hk
    have := r.range k a hk
    have e : fixedPin net r.d sig k = shift (r.d k) (sig a.src) := by
      funext t; simp only [fixedPin, hk]
    rw [e]; exact shift_bd _ this.1 this.2
  quiet := by intro k a hk; simp only [fixedPin, hk]; exact shift_zero _ _
  local_ := r.local_
  node := r.node

/-- A node other than the launch changes only when one of its input pins does. -/
theorem Run.node_changes {net : Netlist} {sig : Nat → Trace} (r : Run net sig) {v t : Nat}
    (hv : v ≠ 0) (h : changes (sig v) t) :
    ∃ k a, net.arcs[k]? = some a ∧ a.dst = v ∧ changes (r.pin k) t := by
  apply Classical.byContradiction; intro hn
  apply h
  rw [r.node v hv t, r.node v hv (t + 1)]
  apply r.local_ v
  intro k a hk hd
  apply Classical.byContradiction; intro hc
  exact hn ⟨k, a, hk, hd, hc⟩

end Formal.Timing

namespace Formal.Timing
open Formal.Net

/-- In a fixed-delay run a node other than the launch changes at `t` only if the
source of one of its arcs changed exactly `d k` earlier. -/
theorem FixedRun.node_changes {net : Netlist} {sig : Nat → Trace} (r : FixedRun net sig)
    {v t : Nat} (hv : v ≠ 0) (h : changes (sig v) t) :
    ∃ k a, net.arcs[k]? = some a ∧ a.dst = v ∧ r.d k ≤ t ∧ changes (sig a.src) (t - r.d k) := by
  obtain ⟨k, a, hk, hd, hc⟩ := r.toRun.node_changes hv h
  have e : r.toRun.pin k = shift (r.d k) (sig a.src) := by
    funext t; show fixedPin net r.d sig k t = _; simp only [fixedPin, hk]
  rw [e] at hc
  obtain ⟨h1, h2⟩ := shift_changes hc
  exact ⟨k, a, hk, hd, h1, h2⟩

end Formal.Timing
