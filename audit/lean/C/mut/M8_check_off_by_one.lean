import Formal.Net.Prelim
-- ==== verbatim: Formal/Timing/Semantics.lean (import lines removed) ====

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
-- ==== verbatim: Formal/Timing/Checker.lean (import lines removed) ====

/-!
# Interval timing checker, proved sound and per-node exact (probe C-10a)

`win net v` is the switching window `(earliest, latest)` of node `v`
(`none` = the node never switches): earliest = min over paths of the `lo`-sums,
latest = max over paths of the `hi`-sums, computed in one topological pass
(`table`, index order is topological by `Netlist.WF`).

`check net req data setup` is the bundling check: the request reaches the
capture point (latch enable) and every data input settles `setup` before the
request can arrive: `latest(d) + setup ≤ earliest(req)`.

Theorems:
* `changes_in_window`  soundness of the windows: in every `Run`, node `v` switches
  only inside `win net v`.
* `check_sound`, `check_stable` soundness of the check: in every run, every data
  change precedes every request change by `≥ setup`, so data is stable from
  `setup` ticks before any request edge on.
* `win_early_attained`, `win_late_attained`  the windows are exact: for every
  reachable node there is a run (a fixed-delay one, hence also a `FixedRun`)
  in which the node switches exactly at its earliest time, and one at its latest.
* `check_exact_disjoint`  the check itself is exact (complete) when the request
  and data cones share only the launch node (`Separated`): a failing check
  then has a fixed-delay run that really violates bundling (`mixRun`).
With shared arcs (correlated delays) see `CheckerToy.lean`: conservative for
fixed per-arc delays, exact on the example for per-event H_BOUNDED_DELAY.
-/

namespace Formal.Timing
open Formal.Net

/-- Switching window `(earliest, latest)`. -/
abbrev Win := Nat × Nat

def mergeW : Option Win → Win → Win
  | none, w => w
  | some (e, l), (e', l') => (min e e', max l l')

/-- Window of node `v` from the windows `L` of its sources, over arcs `as`. -/
def collect (L : Nat → Option Win) (v : Nat) : List Arc → Option Win
  | [] => none
  | a :: as =>
    if a.dst = v then
      match L a.src with
      | some (e, l) => some (mergeW (collect L v as) (e + a.lo, l + a.hi))
      | none => collect L v as
    else collect L v as

def nodeWin (net : Netlist) (L : Nat → Option Win) (v : Nat) : Option Win :=
  if v = 0 then some (0, 0) else collect L v net.arcs

/-- Windows of nodes `0 .. k-1`, computed in topological (index) order. -/
def table (net : Netlist) : Nat → List (Option Win)
  | 0 => []
  | k + 1 => let ws := table net k; ws ++ [nodeWin net (fun x => ws.getD x none) k]

def win (net : Netlist) (v : Nat) : Option Win := (table net (v + 1)).getD v none

/-- The bundling check. -/
def check (net : Netlist) (req : Nat) (data : List Nat) (setup : Nat) : Bool :=
  match win net req with
  | none => false
  | some (er, _) => data.all fun d =>
      match win net d with
      | none => true
      | some (_, ld) => decide (ld + setup ≤ er + 1) -- MUTANT M8

/-- Slack of the check (ps, may be negative), for reporting. -/
def slack (net : Netlist) (req : Nat) (data : List Nat) (setup : Nat) : Option Int :=
  match win net req with
  | none => none
  | some (er, _) => some (data.foldl (fun m d =>
      match win net d with
      | none => m
      | some (_, ld) => min m ((er : Int) - ld - setup)) (er : Int))

/-! ## The table computes the recurrence -/

theorem table_length (net : Netlist) : ∀ k, (table net k).length = k
  | 0 => rfl
  | k + 1 => by simp [table, table_length net k]

theorem table_get (net : Netlist) : ∀ k x, x < k → (table net k).getD x none = win net x
  | 0, x, h => absurd h (Nat.not_lt_zero _)
  | k + 1, x, h => by
    by_cases hx : x < k
    · simp only [table]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [table_length]; exact hx),
        ← List.getD_eq_getElem?_getD]
      exact table_get net k x hx
    · have : x = k := by omega
      subst this; rfl

theorem collect_congr (L L' : Nat → Option Win) (v : Nat) :
    ∀ as : List Arc, (∀ a ∈ as, a.dst = v → L a.src = L' a.src) →
      collect L v as = collect L' v as
  | [], _ => rfl
  | a :: as, h => by
    have ih := collect_congr L L' v as (fun b hb => h b (List.mem_cons_of_mem _ hb))
    simp only [collect]
    by_cases hd : a.dst = v
    · rw [ite_eq_left hd, ite_eq_left hd, h a (List.mem_cons_self) hd, ih]
    · rw [ite_eq_right hd, ite_eq_right hd, ih]

theorem win_zero (net : Netlist) : win net 0 = some (0, 0) := rfl

theorem win_eq (net : Netlist) (hwf : net.WF) {v : Nat} (hv : v ≠ 0) :
    win net v = collect (win net) v net.arcs := by
  show (table net (v + 1)).getD v none = _
  simp only [table]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [table_length]; exact Nat.le_refl _)]
  simp only [table_length, Nat.sub_self, nodeWin, ite_eq_right hv, List.getElem?_cons_zero,
    Option.getD_some]
  apply collect_congr
  intro a ha hd
  exact table_get net v a.src (hd ▸ (hwf a ha).1)

/-! ## What `collect` computes -/

theorem collect_upper (L : Nat → Option Win) (v : Nat) :
    ∀ (as : List Arc) (a : Arc) (e l : Nat), a ∈ as → a.dst = v → L a.src = some (e, l) →
      ∃ e' l', collect L v as = some (e', l') ∧ e' ≤ e + a.lo ∧ l + a.hi ≤ l'
  | [], _, _, _, h, _, _ => absurd h List.not_mem_nil
  | b :: as, a, e, l, hm, hd, hL => by
    simp only [collect]
    rcases List.mem_cons.1 hm with rfl | hm
    · rw [ite_eq_left hd, hL]
      cases hc : collect L v as with
      | none => exact ⟨_, _, rfl, Nat.le_refl _, Nat.le_refl _⟩
      | some w =>
        obtain ⟨e1, l1⟩ := w
        exact ⟨_, _, rfl, Nat.min_le_right _ _, Nat.le_max_right _ _⟩
    · obtain ⟨e', l', hc, h1, h2⟩ := collect_upper L v as a e l hm hd hL
      by_cases hb : b.dst = v
      · rw [ite_eq_left hb]
        cases hLb : L b.src with
        | none => exact ⟨e', l', hc, h1, h2⟩
        | some w =>
          obtain ⟨eb, lb⟩ := w
          rw [hc]
          exact ⟨_, _, rfl, Nat.le_trans (Nat.min_le_left _ _) h1,
                 Nat.le_trans h2 (Nat.le_max_left _ _)⟩
      · rw [ite_eq_right hb]; exact ⟨e', l', hc, h1, h2⟩

theorem collect_attain (L : Nat → Option Win) (v : Nat) :
    ∀ (as : List Arc) (e' l' : Nat), collect L v as = some (e', l') →
      (∃ a ∈ as, a.dst = v ∧ ∃ e l, L a.src = some (e, l) ∧ e' = e + a.lo) ∧
      (∃ a ∈ as, a.dst = v ∧ ∃ e l, L a.src = some (e, l) ∧ l' = l + a.hi)
  | [], _, _, h => by simp [collect] at h
  | b :: as, e', l', h => by
    simp only [collect] at h
    by_cases hb : b.dst = v
    · rw [ite_eq_left hb] at h
      cases hLb : L b.src with
      | none =>
        rw [hLb] at h
        obtain ⟨⟨a, ha, h1⟩, ⟨a', ha', h2⟩⟩ := collect_attain L v as e' l' h
        exact ⟨⟨a, List.mem_cons_of_mem _ ha, h1⟩, ⟨a', List.mem_cons_of_mem _ ha', h2⟩⟩
      | some w =>
        obtain ⟨eb, lb⟩ := w
        rw [hLb] at h
        cases hc : collect L v as with
        | none =>
          rw [hc] at h; simp only [mergeW, Option.some.injEq, Prod.mk.injEq] at h
          exact ⟨⟨b, List.mem_cons_self, hb, eb, lb, hLb, h.1.symm⟩,
                 ⟨b, List.mem_cons_self, hb, eb, lb, hLb, h.2.symm⟩⟩
        | some w1 =>
          obtain ⟨e1, l1⟩ := w1
          rw [hc] at h; simp only [mergeW, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨⟨a, ha, h1⟩, ⟨a', ha', h2⟩⟩ := collect_attain L v as e1 l1 hc
          obtain ⟨he, hl⟩ := h
          constructor
          · by_cases hle : e1 ≤ eb + b.lo
            · rw [Nat.min_eq_left hle] at he; subst he
              exact ⟨a, List.mem_cons_of_mem _ ha, h1⟩
            · rw [Nat.min_eq_right (by omega)] at he
              exact ⟨b, List.mem_cons_self, hb, eb, lb, hLb, he.symm⟩
          · by_cases hle : l1 ≤ lb + b.hi
            · rw [Nat.max_eq_right hle] at hl
              exact ⟨b, List.mem_cons_self, hb, eb, lb, hLb, hl.symm⟩
            · rw [Nat.max_eq_left (by omega)] at hl; subst hl
              exact ⟨a', List.mem_cons_of_mem _ ha', h2⟩
    · rw [ite_eq_right hb] at h
      obtain ⟨⟨a, ha, h1⟩, ⟨a', ha', h2⟩⟩ := collect_attain L v as e' l' h
      exact ⟨⟨a, List.mem_cons_of_mem _ ha, h1⟩, ⟨a', List.mem_cons_of_mem _ ha', h2⟩⟩

theorem win_lt (net : Netlist) (hwf : net.WF) {k : Nat} {a : Arc}
    (hk : net.arcs[k]? = some a) : a.src < a.dst :=
  (hwf a (List.mem_of_getElem? hk)).1

/-! ## Soundness -/

/-- **Window soundness.** In every run, a node switches only inside its window. -/
theorem changes_in_window {net : Netlist} (hwf : net.WF) {sig : Nat → Trace}
    (r : Run net sig) : ∀ v t, changes (sig v) t →
      ∃ e l, win net v = some (e, l) ∧ e ≤ t ∧ t ≤ l := by
  intro v
  induction v using Nat.strongRecOn with
  | ind v ih =>
  intro t ht
  by_cases hv : v = 0
  · subst hv
    have := r.launch t ht; subst this
    exact ⟨0, 0, win_zero net, Nat.le_refl _, Nat.le_refl _⟩
  · obtain ⟨k, a, hk, hd, hc⟩ := r.node_changes hv ht
    have hlt : a.src < v := hd ▸ win_lt net hwf hk
    -- the source switched (else its pin could not), so it has a window
    have hsrc : ∃ e l, win net a.src = some (e, l) ∧
        ∀ s, changes (sig a.src) s → e ≤ s ∧ s ≤ l := by
      by_cases hany : ∃ s, changes (sig a.src) s
      · obtain ⟨s, hs⟩ := hany
        obtain ⟨e, l, hw, _, _⟩ := ih a.src hlt s hs
        refine ⟨e, l, hw, fun s' hs' => ?_⟩
        obtain ⟨e2, l2, hw2, h1, h2⟩ := ih a.src hlt s' hs'
        rw [hw] at hw2; cases hw2; exact ⟨h1, h2⟩
      · have := arc_window (a := t + 1) (b := 0) (r.bd k a hk) (r.quiet k a hk)
          (fun s hs => absurd ⟨s, hs⟩ hany) hc
        omega
    obtain ⟨e, l, hw, hwin⟩ := hsrc
    have hat := arc_window (r.bd k a hk) (r.quiet k a hk) hwin hc
    obtain ⟨e', l', hcv, h1, h2⟩ :=
      collect_upper (win net) v net.arcs a e l (List.mem_of_getElem? hk) hd hw
    rw [← win_eq net hwf hv] at hcv
    exact ⟨e', l', hcv, by omega, by omega⟩

/-- **Check soundness.** If `check` passes, then in every run every change of a
data input precedes every change of the request by at least `setup` ticks. -/
theorem check_sound {net : Netlist} (hwf : net.WF) {req : Nat} {data : List Nat}
    {setup : Nat} (hc : check net req data setup = true) {sig : Nat → Trace}
    (r : Run net sig) : ∀ d ∈ data, ∀ s t, changes (sig d) s → changes (sig req) t →
      s + setup ≤ t := by
  intro d hd s t hs ht
  obtain ⟨er, lr, hwr, h1, _⟩ := changes_in_window hwf r req t ht
  obtain ⟨ed, ld, hwd, _, h2⟩ := changes_in_window hwf r d s hs
  simp only [check, hwr, List.all_eq_true] at hc
  have := hc d hd
  rw [hwd] at this
  simp only [decide_eq_true_eq] at this
  omega

/-- Corollary: when the request switches at `t` (new value at `t+1`), every data
input has been stable since `t + 1 - setup` and stays stable forever after
(single launch). -/
theorem check_stable {net : Netlist} (hwf : net.WF) {req : Nat} {data : List Nat}
    {setup : Nat} (hc : check net req data setup = true) {sig : Nat → Trace}
    (r : Run net sig) : ∀ d ∈ data, ∀ t, changes (sig req) t →
      ∀ T, stableOn (sig d) (t + 1 - setup) T := by
  intro d hd t ht T u h1 _
  have := const_from (i := sig d) (c := t + 1 - setup)
    (fun s hs => by have := check_sound hwf hc r d hd s t hs ht; omega) u h1
  exact this

/-! ## Exactness of the windows -/

/-- `bany n f` = some `k < n` with `f k`. -/
def bany (n : Nat) (f : Nat → Bool) : Bool := (List.range n).any f
def ball (n : Nat) (f : Nat → Bool) : Bool := (List.range n).all f

theorem bany_iff (n : Nat) (f : Nat → Bool) : bany n f = true ↔ ∃ k, k < n ∧ f k = true := by
  simp [bany]

theorem ball_iff (n : Nat) (f : Nat → Bool) : ball n f = true ↔ ∀ k, k < n → f k = true := by
  simp [ball]

/-- The `k`-th arc enters `v` (and is its index). -/
def into (net : Netlist) (v k : Nat) : Bool :=
  match net.arcs[k]? with
  | some a => a.dst == v
  | none => false

theorem into_iff (net : Netlist) (v k : Nat) :
    into net v k = true ↔ ∃ a, net.arcs[k]? = some a ∧ a.dst = v := by
  unfold into
  cases h : net.arcs[k]? with
  | none => simp
  | some a => simp

theorem getElem?_lt {net : Netlist} {k : Nat} {a : Arc} (h : net.arcs[k]? = some a) :
    k < net.arcs.length := by
  apply Classical.byContradiction; intro hk
  rw [List.getElem?_eq_none (by omega)] at h; cases h


/-- Arc `k` exists and its source is reachable from the launch. -/
def srcReach (net : Netlist) (k : Nat) : Bool :=
  match net.arcs[k]? with
  | some a => (win net a.src).isSome
  | none => false

theorem srcReach_iff (net : Netlist) (k : Nat) :
    srcReach net k = true ↔ ∃ a, net.arcs[k]? = some a ∧ ∃ e l, win net a.src = some (e, l) := by
  unfold srcReach
  cases h : net.arcs[k]? with
  | none => simp
  | some a =>
    simp only [Option.some.injEq, exists_eq_left', Option.isSome_iff_exists]
    constructor
    · rintro ⟨⟨e, l⟩, hw⟩; exact ⟨e, l, hw⟩
    · rintro ⟨e, l, hw⟩; exact ⟨_, hw⟩

/-- Earliest-arrival trace: node `v` steps 0 → 1 right after its earliest time. -/
def earlySig (net : Netlist) (v : Nat) : Trace := fun t =>
  match win net v with
  | some (e, _) => decide (e + 1 ≤ t)
  | none => false

/-- Latest-arrival trace. -/
def lateSig (net : Netlist) (v : Nat) : Trace := fun t =>
  match win net v with
  | some (_, l) => decide (l + 1 ≤ t)
  | none => false

def loD (net : Netlist) (k : Nat) : Nat := match net.arcs[k]? with | some a => a.lo | none => 0
def hiD (net : Netlist) (k : Nat) : Nat := match net.arcs[k]? with | some a => a.hi | none => 0

theorem early_pin (net : Netlist) {k : Nat} {a : Arc} (hk : net.arcs[k]? = some a) (t : Nat) :
    fixedPin net (loD net) (earlySig net) k t = true ↔
      ∃ e l, win net a.src = some (e, l) ∧ e + 1 + a.lo ≤ t := by
  simp only [fixedPin, loD, hk, shift, earlySig]
  cases hw : win net a.src with
  | none => simp
  | some w =>
    obtain ⟨e, l⟩ := w
    constructor
    · intro hp; refine ⟨e, l, rfl, ?_⟩
      by_cases h : t < a.lo <;> simp [h] at hp <;> omega
    · rintro ⟨e', l', he, hle⟩; cases he
      by_cases h : t < a.lo <;> simp [h] <;> omega

theorem late_pin (net : Netlist) {k : Nat} {a : Arc} (hk : net.arcs[k]? = some a) (t : Nat) :
    fixedPin net (hiD net) (lateSig net) k t = true ↔
      ∃ e l, win net a.src = some (e, l) ∧ l + 1 + a.hi ≤ t := by
  simp only [fixedPin, hiD, hk, shift, lateSig]
  cases hw : win net a.src with
  | none => simp
  | some w =>
    obtain ⟨e, l⟩ := w
    constructor
    · intro hp; refine ⟨e, l, rfl, ?_⟩
      by_cases h : t < a.hi <;> simp [h] at hp <;> omega
    · rintro ⟨e', l', he, hle⟩; cases he
      by_cases h : t < a.hi <;> simp [h] <;> omega

theorem launch_step (t e : Nat) (he : e = 0)
    (ht : changes (fun t => decide (e + 1 ≤ t)) t) : t = 0 := by
  subst he
  apply Classical.byContradiction; intro h0; apply ht
  show decide (0 + 1 ≤ t) = decide (0 + 1 ≤ t + 1)
  rw [decide_eq_decide]; omega

/-- All-`lo` fixed-delay run with OR node functions: node `v` steps exactly at
its earliest time. -/
def earlyRun (net : Netlist) (hwf : net.WF) : FixedRun net (earlySig net) where
  d := loD net
  g := fun v x => bany net.arcs.length (fun k => into net v k && x k)
  launch := by
    intro t ht
    have : earlySig net 0 = fun t => decide (0 + 1 ≤ t) := by
      funext t; simp only [earlySig, win_zero]
    rw [this] at ht; exact launch_step t 0 rfl ht
  range := by
    intro k a hk
    have := (hwf a (List.mem_of_getElem? hk)).2
    simp only [loD, hk]; omega
  local_ := by
    intro v x y hxy
    simp only [bany]; congr 1; funext k
    cases hi : into net v k with
    | false => simp
    | true =>
      obtain ⟨a, ha, hd⟩ := (into_iff net v k).1 hi
      simp [hxy k a ha hd]
  node := by
    intro v hv t
    apply Bool.eq_iff_iff.2
    rw [bany_iff]
    constructor
    · intro hs
      simp only [earlySig] at hs
      cases hw : win net v with
      | none => rw [hw] at hs; cases hs
      | some w =>
        obtain ⟨e, l⟩ := w
        rw [hw] at hs; simp only [decide_eq_true_eq] at hs
        rw [win_eq net hwf hv] at hw
        obtain ⟨⟨a, ha, hd, es, ls, hsw, hes⟩, _⟩ := collect_attain _ _ _ _ _ hw
        obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 ha
        refine ⟨k, getElem?_lt hk, ?_⟩
        rw [Bool.and_eq_true]
        exact ⟨(into_iff net v k).2 ⟨a, hk, hd⟩, (early_pin net hk t).2 ⟨es, ls, hsw, by omega⟩⟩
    · rintro ⟨k, _, hkk⟩
      rw [Bool.and_eq_true] at hkk
      obtain ⟨a, hk, hd⟩ := (into_iff net v k).1 hkk.1
      obtain ⟨es, ls, hsw, hle⟩ := (early_pin net hk t).1 hkk.2
      obtain ⟨e', l', hcv, h1, _⟩ :=
        collect_upper (win net) v net.arcs a es ls (List.mem_of_getElem? hk) hd hsw
      rw [← win_eq net hwf hv] at hcv
      simp only [earlySig, hcv, decide_eq_true_eq]; omega

/-- All-`hi` fixed-delay run with AND-over-reachable-inputs node functions: node
`v` steps exactly at its latest time. -/
def lateRun (net : Netlist) (hwf : net.WF) : FixedRun net (lateSig net) where
  d := hiD net
  g := fun v x => bany net.arcs.length (fun k => into net v k && srcReach net k) &&
                  ball net.arcs.length (fun k => !(into net v k && srcReach net k) || x k)
  launch := by
    intro t ht
    have : lateSig net 0 = fun t => decide (0 + 1 ≤ t) := by
      funext t; simp only [lateSig, win_zero]
    rw [this] at ht; exact launch_step t 0 rfl ht
  range := by
    intro k a hk
    have := (hwf a (List.mem_of_getElem? hk)).2
    simp only [hiD, hk]; omega
  local_ := by
    intro v x y hxy
    simp only [ball]; congr 2; funext k
    cases hi : into net v k with
    | false => simp
    | true =>
      obtain ⟨a, ha, hd⟩ := (into_iff net v k).1 hi
      simp [hxy k a ha hd]
  node := by
    intro v hv t
    apply Bool.eq_iff_iff.2
    rw [Bool.and_eq_true, bany_iff, ball_iff]
    constructor
    · intro hs
      simp only [lateSig] at hs
      cases hw : win net v with
      | none => rw [hw] at hs; cases hs
      | some w =>
        obtain ⟨e, l⟩ := w
        rw [hw] at hs; simp only [decide_eq_true_eq] at hs
        have hw' := hw
        rw [win_eq net hwf hv] at hw'
        obtain ⟨⟨a, ha, hd, es, ls, hsw, _⟩, _⟩ := collect_attain _ _ _ _ _ hw'
        obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 ha
        refine ⟨⟨k, getElem?_lt hk, ?_⟩, ?_⟩
        · rw [Bool.and_eq_true]
          exact ⟨(into_iff net v k).2 ⟨a, hk, hd⟩, (srcReach_iff net k).2 ⟨a, hk, es, ls, hsw⟩⟩
        · intro j _
          cases hj : (into net v j && srcReach net j) with
          | false => simp
          | true =>
            rw [Bool.and_eq_true] at hj
            obtain ⟨b, hb, hbd⟩ := (into_iff net v j).1 hj.1
            obtain ⟨b', hb', eb, lb, hbw⟩ := (srcReach_iff net j).1 hj.2
            rw [hb] at hb'; cases hb'
            obtain ⟨e', l', hcv, _, h2⟩ :=
              collect_upper (win net) v net.arcs b eb lb (List.mem_of_getElem? hb) hbd hbw
            rw [← win_eq net hwf hv, hw] at hcv
            cases hcv
            simp only [Bool.not_true, Bool.false_or]
            exact (late_pin net hb t).2 ⟨eb, lb, hbw, by omega⟩
    · rintro ⟨⟨k, _, hkk⟩, hall⟩
      rw [Bool.and_eq_true] at hkk
      obtain ⟨a, hk, hd⟩ := (into_iff net v k).1 hkk.1
      obtain ⟨a', hk', es, ls, hsw⟩ := (srcReach_iff net k).1 hkk.2
      rw [hk] at hk'; cases hk'
      obtain ⟨e', l', hcv, _, _⟩ :=
        collect_upper (win net) v net.arcs a es ls (List.mem_of_getElem? hk) hd hsw
      have hcv' := hcv
      rw [← win_eq net hwf hv] at hcv'
      obtain ⟨_, ⟨b, hb, hbd, eb, lb, hbw, hlb⟩⟩ := collect_attain _ _ _ _ _ hcv
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hb
      have hpj := hall j (getElem?_lt hj)
      rw [show (into net v j && srcReach net j) = true from by
        rw [Bool.and_eq_true]
        exact ⟨(into_iff net v j).2 ⟨b, hj, hbd⟩, (srcReach_iff net j).2 ⟨b, hj, eb, lb, hbw⟩⟩]
        at hpj
      simp only [Bool.not_true, Bool.false_or] at hpj
      obtain ⟨eb', lb', hbw', hle⟩ := (late_pin net hj t).1 hpj
      rw [hbw] at hbw'; cases hbw'
      simp only [lateSig, hcv', decide_eq_true_eq]; omega

/-- **Exactness, earliest.** The earliest time of every reachable node is
attained by some run (in fact a fixed-delay run). -/
theorem win_early_attained {net : Netlist} (hwf : net.WF) {v e l : Nat}
    (hw : win net v = some (e, l)) :
    ∃ sig, Nonempty (FixedRun net sig) ∧ Nonempty (Run net sig) ∧ changes (sig v) e :=
  ⟨earlySig net, ⟨earlyRun net hwf⟩, ⟨(earlyRun net hwf).toRun⟩, by
    simp only [changes, earlySig, hw]; simp⟩

/-- **Exactness, latest.** -/
theorem win_late_attained {net : Netlist} (hwf : net.WF) {v e l : Nat}
    (hw : win net v = some (e, l)) :
    ∃ sig, Nonempty (FixedRun net sig) ∧ Nonempty (Run net sig) ∧ changes (sig v) l :=
  ⟨lateSig net, ⟨lateRun net hwf⟩, ⟨(lateRun net hwf).toRun⟩, by
    simp only [changes, lateSig, hw]; simp⟩

/-- **Window exactness, summary.** `win` is the exact switching hull: unreachable
nodes never switch in any run; a reachable node switches only inside `[e, l]`
in every run, and both ends are attained by fixed-delay runs. -/
theorem win_exact {net : Netlist} (hwf : net.WF) (v : Nat) :
    (win net v = none → ∀ sig (_ : Run net sig) t, ¬ changes (sig v) t) ∧
    (∀ e l, win net v = some (e, l) →
      (∀ sig (_ : Run net sig) t, changes (sig v) t → e ≤ t ∧ t ≤ l) ∧
      (∃ sig, Nonempty (FixedRun net sig) ∧ changes (sig v) e) ∧
      (∃ sig, Nonempty (FixedRun net sig) ∧ changes (sig v) l)) := by
  constructor
  · intro hn sig r t ht
    obtain ⟨_, _, hw, _⟩ := changes_in_window hwf r v t ht
    rw [hn] at hw; cases hw
  · intro e l hw
    refine ⟨fun sig r t ht => ?_, ?_, ?_⟩
    · obtain ⟨e', l', hw', h1, h2⟩ := changes_in_window hwf r v t ht
      rw [hw] at hw'; cases hw'; exact ⟨h1, h2⟩
    · obtain ⟨sig, h1, _, h3⟩ := win_early_attained hwf hw; exact ⟨sig, h1, h3⟩
    · obtain ⟨sig, h1, _, h3⟩ := win_late_attained hwf hw; exact ⟨sig, h1, h3⟩

/-! ## Joint exactness when the two cones are disjoint -/

theorem lateSig_zero (net : Netlist) : lateSig net 0 = earlySig net 0 := by
  funext t; simp only [lateSig, earlySig, win_zero]

/-- Nodes with `P v` follow their latest time, the others their earliest. -/
def mixSig (net : Netlist) (P : Nat → Bool) (v : Nat) : Trace :=
  if P v then lateSig net v else earlySig net v

def mixD (net : Netlist) (P : Nat → Bool) (k : Nat) : Nat :=
  match net.arcs[k]? with
  | some a => if P a.dst then a.hi else a.lo
  | none => 0

/-- H_SEPARATED: no arc crosses between the `P` and the `¬P` part except from
the launch node. -/
def Separated (net : Netlist) (P : Nat → Bool) : Prop :=
  ∀ a ∈ net.arcs, a.src ≠ 0 → P a.src = P a.dst

instance (net : Netlist) (P : Nat → Bool) : Decidable (Separated net P) :=
  inferInstanceAs (Decidable (∀ a ∈ net.arcs, a.src ≠ 0 → P a.src = P a.dst))

/-- One fixed-delay run with the `P` part at its latest and the rest at its
earliest times. -/
def mixRun (net : Netlist) (hwf : net.WF) (P : Nat → Bool) (hP : Separated net P) :
    FixedRun net (mixSig net P) where
  d := mixD net P
  g := fun v => if P v then (lateRun net hwf).g v else (earlyRun net hwf).g v
  launch := by
    intro t ht
    simp only [mixSig, lateSig_zero, ite_self] at ht
    exact (earlyRun net hwf).launch t ht
  range := by
    intro k a hk
    have := (hwf a (List.mem_of_getElem? hk)).2
    simp only [mixD, hk]; split <;> omega
  local_ := by
    intro v
    by_cases h : P v = true
    · simp only [h, ite_true]; exact (lateRun net hwf).local_ v
    · simp only [h]; exact (earlyRun net hwf).local_ v
  node := by
    intro v hv t
    have src_mode : ∀ (k : Nat) (a : Arc), net.arcs[k]? = some a → a.dst = v →
        mixSig net P a.src = if P v then lateSig net a.src else earlySig net a.src := by
      intro k a hk hd
      by_cases h0 : a.src = 0
      · rw [h0]; simp only [mixSig, lateSig_zero, ite_self]
      · have := hP a (List.mem_of_getElem? hk) h0
        simp only [mixSig, this, hd]
    by_cases h : P v = true
    · simp only [h, ite_true, mixSig]
      rw [(lateRun net hwf).node v hv t]
      apply (lateRun net hwf).local_ v
      intro k a hk hd
      have := src_mode k a hk hd
      simp only [h, ite_true] at this
      show fixedPin net (hiD net) (lateSig net) k t = fixedPin net (mixD net P) (mixSig net P) k t
      simp only [fixedPin, mixD, hiD, hk, hd, h, ite_true, this]
    · have h' : P v = false := by cases hh : P v <;> simp_all
      simp only [h', mixSig, Bool.false_eq_true, ite_false]
      rw [(earlyRun net hwf).node v hv t]
      apply (earlyRun net hwf).local_ v
      intro k a hk hd
      have := src_mode k a hk hd
      simp only [h', Bool.false_eq_true, ite_false] at this
      show fixedPin net (loD net) (earlySig net) k t = fixedPin net (mixD net P) (mixSig net P) k t
      simp only [fixedPin, mixD, loD, hk, hd, h', this, Bool.false_eq_true, ite_false]

/-- **Joint exactness for separated cones.** If the check fails, the request
reaches the capture point, and request and data cones are separated (share
only the launch), then some fixed-delay run really violates the bundling
property. So for such netlists the check is exact (sound and complete). -/
theorem check_exact_disjoint {net : Netlist} (hwf : net.WF) {P : Nat → Bool}
    (hP : Separated net P) {req : Nat} {data : List Nat} {setup : Nat}
    (hreq : P req = false) (hdata : ∀ d ∈ data, P d = true)
    (hreach : (win net req).isSome = true)
    (hc : check net req data setup = false) :
    ∃ d ∈ data, ∃ sig, Nonempty (FixedRun net sig) ∧
      ∃ s t, changes (sig d) s ∧ changes (sig req) t ∧ t < s + setup := by
  obtain ⟨⟨er, lr⟩, hwr⟩ := Option.isSome_iff_exists.1 hreach
  simp only [check, hwr] at hc
  have : ∃ d ∈ data, (match win net d with
      | none => true
      | some (_, ld) => decide (ld + setup ≤ er)) = false := by
    apply Classical.byContradiction; intro hn
    apply Bool.false_ne_true; rw [← hc, List.all_eq_true]
    intro d hd
    apply Classical.byContradiction; intro hx
    exact hn ⟨d, hd, by simpa using hx⟩
  obtain ⟨d, hd, hx⟩ := this
  cases hwd : win net d with
  | none => rw [hwd] at hx; cases hx
  | some w =>
    obtain ⟨ed, ld⟩ := w
    rw [hwd] at hx; simp only [decide_eq_false_iff_not] at hx
    refine ⟨d, hd, mixSig net P, ⟨mixRun net hwf P hP⟩, ld, er, ?_, ?_, by omega⟩
    · simp only [changes, mixSig, hdata d hd, ite_true, lateSig, hwd]; simp
    · simp only [changes, mixSig, hreq, Bool.false_eq_true, ite_false, earlySig, hwr]; simp

end Formal.Timing
-- ==== verbatim: Formal/Timing/CheckerToy.lean (import lines removed) ====

/-!
# The checker on a toy one-link netlist, and the correlated-delay question

## 1. A `bd_link`-shaped toy (numbers are ILLUSTRATIVE, not prjxray data)

Launch node 0 = the upstream controller node `C_{i-1}` rising: it raises the
request and opens the upstream data latches. Request path to the capture latch
enable of stage `i`:

    0 →(wire 60..180)→ 1 →(delay element, 3 LUTs)→ 2 →(wire 60..180)→ 3
      →(C-element LUT arc 40..60)→ 4 →(wire 50..150)→ 5 = capture latch G

Data path, a 4-bit bus:

    0 →(G net 50..150)→ 6 →(latch G→Q 100..152, one per bit)→ 7,8,9,10
      →(D wires, four different routes)→ 11,12,13,14 = capture latch D pins

`toyLink` uses a 480..650 ps delay element and passes with setup 30 ps;
`toyShort` uses 330..450 ps and fails. The data bits share node 6 (one G net),
the request and data paths share only the launch node, so the check is exact
here (see section 2 for when it is not).

## 2. Is interval STA exact or only conservative?

`win_exact` (Checker.lean) says per-node windows are exact in both semantics.
The *bundling check* compares two windows at once. `corr` is the smallest
netlist where request and data share an arc with an interval (`0 → 1`, 1..3):

    0 →[1,3]→ 1 →[5,5]→ 2 = req      1 →[4,4]→ 3 = data,   setup 1

`check corr 2 [3] 1 = false` (latest data 7 + 1 > earliest req 6), and:
* `corr_fixed_safe`: in every **fixed-delay** run (one delay per arc) the data
  changes ≥ 1 tick before the request: the check is only CONSERVATIVE there
  (common-path pessimism: the shared arc cannot be both fast and slow);
* `corr_bd_violation`: under **H_BOUNDED_DELAY** (per-event delay, pulses pass)
  there is a run in which the shared node glitches (changes at 1, 2 and 3), the
  request takes the early edge and the data the late one: data changes at 7,
  after the request edge at 6. So the check is EXACT for Prelim's channel.
-/

namespace Formal.Timing
open Formal.Net

/-- The toy link (delay element 480..650 ps). -/
def toyLinkWith (dlo dhi : Nat) : Netlist where
  arcs := [
    ⟨0, 1, 60, 180⟩,  -- C_{i-1} → delay element input (wire)
    ⟨1, 2, dlo, dhi⟩, -- delay element (LUT chain)
    ⟨2, 3, 60, 180⟩,  -- delay element → C_i input (wire)
    ⟨3, 4, 40, 60⟩,   -- C_i LUT arc
    ⟨4, 5, 50, 150⟩,  -- C_i → capture latch G (wire)
    ⟨0, 6, 50, 150⟩,  -- C_{i-1} → upstream latch G pins (net)
    ⟨6, 7, 100, 152⟩, ⟨6, 8, 100, 152⟩, ⟨6, 9, 100, 152⟩, ⟨6, 10, 100, 152⟩, -- latch G→Q
    ⟨7, 11, 80, 220⟩, ⟨8, 12, 90, 260⟩, ⟨9, 13, 70, 200⟩, ⟨10, 14, 100, 300⟩ -- D wires
  ]

def toyLink : Netlist := toyLinkWith 480 650
def toyShort : Netlist := toyLinkWith 330 450

def toyReq : Nat := 5
def toyData : List Nat := [11, 12, 13, 14]
def toySetup : Nat := 30

/-- info: [some (0, 0),
 some (60, 180),
 some (540, 830),
 some (600, 1010),
 some (640, 1070),
 some (690, 1220),
 some (50, 150),
 some (150, 302),
 some (150, 302),
 some (150, 302),
 some (150, 302),
 some (230, 522),
 some (240, 562),
 some (220, 502),
 some (250, 602)] -/
#guard_msgs in
#eval (List.range 15).map (win toyLink)

/-- info: some 58 -/
#guard_msgs in
#eval slack toyLink toyReq toyData toySetup

/-- info: some (-92) -/
#guard_msgs in
#eval slack toyShort toyReq toyData toySetup

theorem toyLink_wf : toyLink.WF := by decide
theorem toyShort_wf : toyShort.WF := by decide

/-- The checker accepts the toy link (kernel evaluation, kernel `decide`, no native code). -/
theorem toyLink_check : check toyLink toyReq toyData toySetup = true := by decide

/-- ...and rejects the one with a short delay element. -/
theorem toyShort_check : check toyShort toyReq toyData toySetup = false := by decide

/-- End-to-end: in every run of the toy link (any delays inside the intervals,
any cell functions), every data bit at the capture latch is stable from 30 ps
before the request edge at its enable onwards. -/
theorem toyLink_bundled {sig : Nat → Trace} (r : Run toyLink sig) :
    ∀ d ∈ toyData, ∀ t, changes (sig toyReq) t → ∀ T, stableOn (sig d) (t + 1 - toySetup) T :=
  check_stable toyLink_wf toyLink_check r

/-- The short link really is broken in the model: a fixed-delay run in which a
data bit changes after the request has reached the enable. Request cone
(nodes 1..5) and data cone (6..14) are disjoint, so `check_exact_disjoint`
applies with `P v := 6 ≤ v`. -/
theorem toyShort_broken : ∃ d ∈ toyData, ∃ sig, Nonempty (FixedRun toyShort sig) ∧
    ∃ s t, changes (sig d) s ∧ changes (sig toyReq) t ∧ t < s + toySetup :=
  check_exact_disjoint toyShort_wf (P := fun v => decide (6 ≤ v)) (by decide) (by decide)
    (by decide) (by decide) toyShort_check

/-! ## 2. Correlated delays -/

def corr : Netlist where
  arcs := [⟨0, 1, 1, 3⟩, ⟨1, 2, 5, 5⟩, ⟨1, 3, 4, 4⟩]

theorem corr_wf : corr.WF := by decide

/-- The interval checker rejects `corr`. -/
theorem corr_check : check corr 2 [3] 1 = false := by decide

/-- info: [some (0, 0), some (1, 3), some (6, 8), some (5, 7)] -/
#guard_msgs in
#eval (List.range 4).map (win corr)

/-- Arcs into `v` in `corr`. -/
theorem corr_arc {k : Nat} {a : Arc} (hk : corr.arcs[k]? = some a) :
    (k = 0 ∧ a = ⟨0, 1, 1, 3⟩) ∨ (k = 1 ∧ a = ⟨1, 2, 5, 5⟩) ∨ (k = 2 ∧ a = ⟨1, 3, 4, 4⟩) := by
  match k, hk with
  | 0, hk => left; simp [corr] at hk; exact ⟨rfl, hk.symm⟩
  | 1, hk => right; left; simp [corr] at hk; exact ⟨rfl, hk.symm⟩
  | 2, hk => right; right; simp [corr] at hk; exact ⟨rfl, hk.symm⟩
  | k + 3, hk => simp [corr] at hk

/-- **Conservative under fixed delays.** In every fixed-delay run of `corr`, every
data change precedes every request change by at least the setup (1), although
the checker rejects it. -/
theorem corr_fixed_safe {sig : Nat → Trace} (r : FixedRun corr sig) :
    ∀ s t, changes (sig 3) s → changes (sig 2) t → s + 1 ≤ t := by
  have h1 : ∀ t, changes (sig 1) t → t = r.d 0 := by
    intro t ht
    obtain ⟨k, a, hk, hd, hle, hc⟩ := r.node_changes (by decide) ht
    rcases corr_arc hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have := r.launch _ hc; omega
    · cases hd
    · cases hd
  have hd1 : r.d 1 = 5 := by have := r.range 1 _ rfl; simp only at this; omega
  have hd2 : r.d 2 = 4 := by have := r.range 2 _ rfl; simp only at this; omega
  intro s t hs ht
  obtain ⟨k, a, hk, hd, hle, hc⟩ := r.node_changes (by decide) hs
  obtain ⟨k', a', hk', hd', hle', hc'⟩ := r.node_changes (by decide) ht
  rcases corr_arc hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> try cases hd
  rcases corr_arc hk' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> try cases hd'
  have := h1 _ hc; have := h1 _ hc'; omega

/-- The glitching pin of arc `0 → 1`: rises at 2, falls at 3, rises again at 4. -/
def glitch : Trace := fun t => decide (t = 2 ∨ 4 ≤ t)
def launchSig : Trace := fun t => decide (1 ≤ t)

def corrSig : Nat → Trace
  | 0 => launchSig
  | 1 => glitch
  | 2 => shift 5 glitch
  | 3 => shift 4 glitch
  | _ => fun _ => false

theorem glitch_bd : BoundedDelay 1 3 launchSig glitch where
  cause := by
    intro t ht
    match t with
    | 0 => exact absurd (by decide) ht
    | 1 => exact ⟨1, by decide, by decide, by decide, by decide⟩
    | 2 => exact ⟨3, by decide, by decide, by decide, by decide⟩
    | 3 => exact ⟨1, by decide, by decide, by decide, by decide⟩
    | t + 4 => exact absurd (show glitch (t + 4) = glitch (t + 4 + 1) by
        simp only [glitch, decide_eq_decide]; omega) ht
  settle := by
    intro t ht hs
    by_cases h3 : t = 3
    · subst h3
      have := hs 1 (by decide) (by decide)
      simp [launchSig] at this
    · simp only [glitch, launchSig, decide_eq_decide]; omega

/-- **Exact under H_BOUNDED_DELAY.** A run of `corr` (Prelim's bounded-delay
channel on every arc) in which the data changes at 7, after the request
changed at 6. -/
def corrRun : Run corr corrSig where
  pin := fun k => match k with
    | 0 => glitch
    | 1 => shift 5 glitch
    | 2 => shift 4 glitch
    | _ => fun _ => false
  g := fun v x => match v with
    | 1 => x 0
    | 2 => x 1
    | 3 => x 2
    | _ => false
  launch := by
    intro t ht
    apply Classical.byContradiction; intro h0; apply ht
    simp only [corrSig, launchSig, decide_eq_decide]; omega
  bd := by
    intro k a hk
    rcases corr_arc hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact glitch_bd
    · exact shift_bd glitch (by decide) (by decide)
    · exact shift_bd glitch (by decide) (by decide)
  quiet := by
    intro k a hk
    rcases corr_arc hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  local_ := by
    intro v x y hxy
    match v with
    | 1 => exact hxy 0 _ rfl rfl
    | 2 => exact hxy 1 _ rfl rfl
    | 3 => exact hxy 2 _ rfl rfl
    | 0 => rfl
    | v + 4 => rfl
  node := by
    intro v hv t
    match v with
    | 0 => exact absurd rfl hv
    | 1 => rfl
    | 2 => rfl
    | 3 => rfl
    | v + 4 => rfl

theorem corr_bd_violation :
    ∃ sig, Nonempty (Run corr sig) ∧ changes (sig 3) 7 ∧ changes (sig 2) 6 ∧ ¬ (7 + 1 ≤ 6) :=
  ⟨corrSig, ⟨corrRun⟩, by unfold changes; decide, by unfold changes; decide, by decide⟩

end Formal.Timing
