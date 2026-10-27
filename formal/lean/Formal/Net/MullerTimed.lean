import Formal.Net.Muller
import Formal.Net.MullerRun
import Formal.Net.Bridge

/-!
# Probe 8g: the gate-level Muller chain (`bd_pipe` control) under bounded delays

Probe 8c (`Muller.lean`) gives the real `bd_link` chain as an asynchronous
transition system over nodes `src, snk, c k, b k, w k, f k` and shows: with a
FREE feedback wire `f k` (O -> I2 route) the real LUT glitches already at
n = 1 (`free_hazard_n1`); with the relative-timing restriction
H_FB_BEFORE_INPUT (`Mode.rt`: a driver of an input pin of `c k` fires only
when `f k = c k`) it is hazard-free and obeys the protocol (`rt_good_1..3`).
Probe 8d (`Bridge.lean`) shows timed traces of PERSISTENT networks are SI
runs. The free-feedback network is not persistent, so 8d does not apply.

This file closes the gap: H_FB_BEFORE_INPUT is DERIVED from delay bounds.

## Timed semantics (`Timed`)
`x : Nat → Nat` (bitmask of node values at each ps). Every node `i` of the
chain (LUT or wire, environment included) is shard C's inertial channel
`Bridge.Inertial (lo i) (hi i)` from the zero-delay function
`nextVal .free n (x t) i` (the real LUT of its pins: `evalL INIT_bd_c2n`, the
LUT1 buffer, a wire's driver; the feedback pin reads the WIRE `f k`, i.e.
free mode, the physical network) to the node. Reset: `x 0 = 0`.

## The timing condition (`FbBound`, the exact form of 8c's inequality)
For every stage `k`, two "guards", one per input pin of `c k`; each is the
causal loop from `c k` back to the driver of that pin:
* pin I0 (req side): `c k → w k → c (k-1) → b (k-1)`, or `c 0 → w 0 → src`;
* pin I1 (ack side): `c k → b k → c (k+1) → w (k+1)`, or `c (n-1) → b (n-1) → snk`.
`FbBound` says `hi (f k) < Σ lo` over the nodes of each loop (`guards`).

## Bridge relative to the RT constraint
`timed_reach`: if `checkT n = true` (a kernel-checked certificate over the
rt-reachable states, below) and `FbBound`, then every timed state is
rt-reachable and the nodes that change at each ps, serialized in any order,
are an rt run. The proof is a strong induction on time; the timing part
(`fb_settled`) is a level argument: while `f k` is in flight, the loop's
progress `level` rises by one only when the next loop node fires, each node
fires at least `lo` after it became excited (inertial cause), so the pin
driver cannot fire before `Σ lo` after `c k`, while `f k` has caught up by
`hi (f k)` (inertial settle).

`checkT n` checks, on every rt-reachable state (BFS certificate, closure
checked): (EP) enabledness persistence (two enabled nodes stay enabled after
either fires, so a ps can be serialized in any order: "persistence relative to
the RT constraint"); (E) when `c k` is enabled no loop node is excited and the
level after `c k` fires is 0; (M) in flight, the level moves only by +1 and
only by the next loop node firing; (X) in flight, loop node `j` excited
implies level ≥ j; and statically that every pin driver restricted by
`Muller.allowed` ends a guard. All generic theorems hold for every `n` with
`checkT n = true`; the instances are in `MullerTimedInst.lean`.
-/

namespace Formal.Net.MullerTimed
open Formal.Net Formal.Net.Muller
open Formal.Net.Bridge (Inertial)

/-! ## Node functions -/

theorem nextVal_free_rt (n s i : Nat) : nextVal .free n s i = nextVal .rt n s i := by
  simp [nextVal, pinQ]

theorem excited_free_rt (n s i : Nat) : excited .free n s i = excited .rt n s i := by
  simp [excited, nextVal_free_rt]

/-- The feedback wire's driver is the C-element output. -/
theorem nextVal_f (n s k : Nat) : nextVal .free n s (f k) = get s (c k) := by
  have h1 : (f k - 2) / 4 = k := by unfold f; omega
  have h2 : (f k - 2) % 4 = 3 := by unfold f; omega
  have h3 : f k ≠ src := by unfold f src; omega
  have h4 : f k ≠ snk := by unfold f snk; omega
  simp only [nextVal, h3, h4, ite_false, h1, h2]
  rfl

theorem get_zero (i : Nat) : get 0 i = false := Nat.zero_testBit i

/-! ## Timed semantics -/

/-- A timed trace of the `n`-stage chain: every node is an inertial channel
`[lo i, hi i]` after its real gate function, feedback wire free. -/
structure Timed (n : Nat) (lo hi : Nat → Nat) (x : Nat → Nat) : Prop where
  init  : x 0 = 0
  gate  : ∀ i, i < numNodes n →
    Inertial (lo i) (hi i) (fun t => nextVal .free n (x t) i) (fun t => get (x t) i)
  frame : ∀ t j, numNodes n ≤ j → get (x t) j = false

/-- Nodes that change at `t → t+1`. -/
def chg (n : Nat) (x : Nat → Nat) (t : Nat) : List Nat :=
  (nodes n).filter (fun i => get (x t) i != get (x (t + 1)) i)

variable {n : Nat} {lo hi : Nat → Nat} {x : Nat → Nat}

theorem mem_chg {t i : Nat} :
    i ∈ chg n x t ↔ i < numNodes n ∧ get (x t) i ≠ get (x (t + 1)) i := by
  unfold chg nodes; simp [List.mem_filter, List.mem_range]

theorem chg_nodup (t : Nat) : (chg n x t).Nodup :=
  List.Pairwise.filter _ List.nodup_range

/-- A changing node was excited (inertial cause, `lo ≥ 1`). -/
theorem chg_exc (hT : Timed n lo hi x) {t i : Nat} (h : i ∈ chg n x t) :
    excited .rt n (x t) i = true := by
  obtain ⟨hi', hc⟩ := mem_chg.1 h
  have g := hT.gate i hi'
  obtain ⟨_, hw⟩ := g.cause t hc
  have := g.lo_pos
  have he : nextVal .free n (x t) i = get (x (t + 1)) i := hw t (by omega) (Nat.le_refl _)
  simp only [excited, ← nextVal_free_rt, he, bne_iff_ne, ne_eq]
  exact fun h' => hc h'.symm

theorem change_lt (hT : Timed n lo hi x) {t i : Nat} (h : get (x t) i ≠ get (x (t + 1)) i) :
    i < numNodes n := by
  apply Classical.byContradiction; intro hn
  exact h (by rw [hT.frame t i (by omega), hT.frame (t + 1) i (by omega)])

theorem no_change (hT : Timed n lo hi x) {t i : Nat} (h : excited .rt n (x t) i = false) :
    get (x (t + 1)) i = get (x t) i := by
  apply Classical.byContradiction; intro hc
  have hm : i ∈ chg n x t := mem_chg.2 ⟨change_lt hT (fun e => hc e.symm), fun e => hc e.symm⟩
  rw [chg_exc hT hm] at h; cases h

/-- First crossing of a predicate. -/
theorem crossing (P : Nat → Prop) (a : Nat) :
    ∀ b, a ≤ b → ¬ P a → P b → ∃ c, a ≤ c ∧ c < b ∧ ¬ P c ∧ P (c + 1) := by
  intro b
  induction b with
  | zero => intro h1 h2 h3; have : a = 0 := by omega
            subst this; exact absurd h3 h2
  | succ b ih =>
    intro h1 h2 h3
    by_cases hb : P b
    · have hab : a ≤ b := by
        apply Classical.byContradiction; intro h; have : a = b + 1 := by omega
        subst this; exact h2 h3
      obtain ⟨c, hc1, hc2, hc3, hc4⟩ := ih hab h2 hb
      exact ⟨c, hc1, by omega, hc3, hc4⟩
    · exact ⟨b, by
        apply Classical.byContradiction; intro h; have : a = b + 1 := by omega
        subst this; exact h2 h3, by omega, hb, h3⟩

/-- An inertial output is constant on the window before a change. -/
theorem win_const {l h : Nat} {e o : Trace} (g : Inertial l h e o) {t : Nat} (hc : changes o t) :
    ∀ u, t + 1 - l ≤ u → u ≤ t → o u = o t := by
  obtain ⟨_, hw⟩ := g.cause t hc
  intro u h1 h2
  apply Classical.byContradiction; intro hne
  obtain ⟨c, hc1, hc2, hc3, hc4⟩ := crossing (fun v => o v = o t) u t h2 hne rfl
  -- change at `c` to value `o t`, inside the window: `e c = o (c+1) = o t`
  have hcc : changes o c := fun e' => hc3 (e' ▸ hc4)
  obtain ⟨_, hw2⟩ := g.cause c hcc
  have e1 : e c = o (c + 1) := hw2 c (by omega) (Nat.le_refl _)
  have e2 : e c = o (t + 1) := hw c (by omega) (by omega)
  rw [e1, hc4] at e2
  exact hc e2

/-- A node that changes at `t` was excited on the whole window `[t+1-lo, t]`. -/
theorem exc_window (hT : Timed n lo hi x) {t i : Nat} (hi' : i < numNodes n)
    (hc : get (x t) i ≠ get (x (t + 1)) i) :
    lo i ≤ t + 1 ∧ ∀ u, t + 1 - lo i ≤ u → u ≤ t → excited .rt n (x u) i = true := by
  have g := hT.gate i hi'
  obtain ⟨h1, hw⟩ := g.cause t hc
  refine ⟨h1, fun u hu1 hu2 => ?_⟩
  have e1 : nextVal .free n (x u) i = get (x (t + 1)) i := hw u hu1 hu2
  have e2 : get (x u) i = get (x t) i := win_const g hc u hu1 hu2
  simp only [excited, ← nextVal_free_rt, e1, e2, bne_iff_ne, ne_eq]
  exact fun h' => hc h'.symm

/-! ## Serializing one ps: rt runs -/

def RunL (n : Nat) : Nat → List Nat → Prop
  | _, [] => True
  | s, i :: is => enabled .rt n s i = true ∧ RunL n (fire s i) is

def finalL : Nat → List Nat → Nat
  | s, [] => s
  | s, i :: is => finalL (fire s i) is

/-- Enabledness persistence (rt): firing one enabled node keeps every other
enabled node enabled. -/
def EP (n s : Nat) : Prop :=
  ∀ i j, i ≠ j → enabled .rt n s i = true → enabled .rt n s j = true →
    enabled .rt n (fire s j) i = true

theorem runL_of_enabled (hEP : ∀ s, Reach .rt n s → EP n s) :
    ∀ (L : List Nat) (s : Nat), Reach .rt n s → L.Nodup → (∀ i ∈ L, enabled .rt n s i = true) →
      RunL n s L ∧ Reach .rt n (finalL s L) := by
  intro L
  induction L with
  | nil => intro s hs _ _; exact ⟨trivial, hs⟩
  | cons j L ih =>
    intro s hs hnd hall
    have hj := hall j List.mem_cons_self
    have hnd' := List.nodup_cons.1 hnd
    have hs' : Reach .rt n (fire s j) := Reach.step hs ⟨j, hj, rfl⟩
    obtain ⟨h1, h2⟩ := ih (fire s j) hs' hnd'.2 (fun i hi => by
      have hij : i ≠ j := fun h => hnd'.1 (h ▸ hi)
      exact hEP s hs i j hij (hall i (List.mem_cons_of_mem _ hi)) hj)
    exact ⟨⟨hj, h1⟩, h2⟩

theorem get_finalL : ∀ (L : List Nat) (s : Nat), L.Nodup → ∀ j,
    get (finalL s L) j = (get s j ^^ decide (j ∈ L)) := by
  intro L
  induction L with
  | nil => intro s _ j; simp [finalL]
  | cons i L ih =>
    intro s hnd j
    have hnd' := List.nodup_cons.1 hnd
    show get (finalL (fire s i) L) j = _
    rw [ih _ hnd'.2 j, get_fire]
    by_cases hji : j = i
    · subst hji; simp [hnd'.1]
    · have : ¬ i = j := fun h => hji h.symm
      simp [hji, this]

theorem finalL_chg (hT : Timed n lo hi x) (t : Nat) : finalL (x t) (chg n x t) = x (t + 1) := by
  apply Nat.eq_of_testBit_eq; intro j
  show get (finalL (x t) (chg n x t)) j = get (x (t + 1)) j
  rw [get_finalL _ _ (chg_nodup t) j]
  by_cases hm : j ∈ chg n x t
  · have := (mem_chg.1 hm).2
    simp only [hm, decide_true, Bool.xor_true]
    revert this; cases get (x t) j <;> cases get (x (t + 1)) j <;> simp
  · simp only [hm, decide_false, Bool.xor_false]
    apply Classical.byContradiction; intro hne
    exact hm (mem_chg.2 ⟨change_lt hT hne, hne⟩)

/-! ## The loops (guards) and their level -/

def inflight (s k : Nat) : Bool := get s (f k) != get s (c k)

/-- Loop node `z` (with polarity) has fired since `c k` did. -/
def isDone (s k : Nat) (z : Nat × Bool) : Bool := (get s z.1 == get s (c k)) == z.2

/-- Number of loop nodes, from the start, that have fired since `c k` did. -/
def level (s k : Nat) : List (Nat × Bool) → Nat
  | [] => 0
  | z :: zs => if isDone s k z then level s k zs + 1 else 0

/-- Loop of pin I0 of `c k`: back through the predecessor (or the source). -/
def predG (k : Nat) : Nat × List (Nat × Bool) :=
  if k = 0 then (0, [(w 0, true), (src, false)])
  else (k, [(w k, true), (c (k - 1), false), (b (k - 1), false)])

/-- Loop of pin I1 of `c k`: forward through the successor (or the sink). -/
def succG (n k : Nat) : Nat × List (Nat × Bool) :=
  if k + 1 = n then (k, [(b k, true), (snk, true)])
  else (k, [(b k, true), (c (k + 1), true), (w (k + 1), true)])

def guards (n : Nat) : List (Nat × List (Nat × Bool)) :=
  (List.range n).flatMap (fun k => [predG k, succG n k])

/-- Sum of the lower delay bounds of the first `j` loop nodes. -/
def loSum (lo : Nat → Nat) (zs : List (Nat × Bool)) (j : Nat) : Nat :=
  ((zs.take j).map (fun z => lo z.1)).sum

theorem level_congr {s s' k : Nat} : ∀ {zs : List (Nat × Bool)},
    (∀ z ∈ zs, get s z.1 = get s' z.1) → get s (c k) = get s' (c k) →
    level s k zs = level s' k zs := by
  intro zs
  induction zs with
  | nil => intro _ _; rfl
  | cons z zs ih =>
    intro h hc
    simp only [level, isDone, h z List.mem_cons_self, hc,
      ih (fun z' hz => h z' (List.mem_cons_of_mem _ hz)) hc]
    rfl

/-! ## The certificate checker -/

def closedB (n B s : Nat) : Bool :=
  (nodes n).all fun y => !enabled .rt n s y || mem B (fire s y)

def epB (n s : Nat) : Bool :=
  (nodes n).all fun j => !enabled .rt n s j ||
    (nodes n).all fun i => i == j || !enabled .rt n s i || enabled .rt n (fire s j) i

def guardOkB (n s : Nat) (g : Nat × List (Nat × Bool)) : Bool :=
  (!enabled .rt n s (c g.1) ||
    (g.2.all (fun z => !excited .rt n s z.1) && level (fire s (c g.1)) g.1 g.2 == 0)) &&
  (!inflight s g.1 ||
    ((nodes n).all (fun y => !enabled .rt n s y || !inflight (fire s y) g.1 ||
        level (fire s y) g.1 g.2 == level s g.1 g.2 ||
        (level (fire s y) g.1 g.2 == level s g.1 g.2 + 1 &&
          (g.2[level s g.1 g.2]?).map Prod.fst == some y)) &&
     (List.range g.2.length).all (fun j => match g.2[j]? with
        | some z => !excited .rt n s z.1 || decide (j ≤ level s g.1 g.2)
        | none => true)))

/-- Static well-formedness: every guard is a nonempty loop of real nodes of a
real stage, and every pin driver restricted by `Muller.allowed` ends one. -/
def staticB (n : Nat) : Bool :=
  (guards n).all (fun g => decide (g.1 < n) && !g.2.isEmpty &&
    g.2.all (fun z => decide (z.1 < numNodes n) && z.1 != c g.1)) &&
  (nodes n).all fun i => match readerStage n i with
    | some k => (guards n).any (fun g => g.1 == k && (g.2.getLast?.map Prod.fst) == some i)
    | none => true

def checkT (n : Nat) : Bool :=
  let L := reachList .rt n
  let B := bitmap L
  mem B 0 && staticB n &&
    L.all (fun s => closedB n B s && epB n s && (guards n).all (guardOkB n s))

/-! ### Soundness of the checker -/

structure Cert (n : Nat) : Prop where
  ep    : ∀ s, Reach .rt n s → EP n s
  guard : ∀ s, Reach .rt n s → ∀ g ∈ guards n, guardOkB n s g = true
  wf    : ∀ g ∈ guards n, g.1 < n ∧ g.2 ≠ [] ∧ ∀ z ∈ g.2, z.1 < numNodes n ∧ z.1 ≠ c g.1
  cover : ∀ i, i < numNodes n → ∀ k, readerStage n i = some k →
    ∃ g ∈ guards n, g.1 = k ∧ g.2.getLast?.map Prod.fst = some i

theorem checkT_sound (h : checkT n = true) : Cert n := by
  simp only [checkT, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨h0, hst⟩, hall⟩ := h
  have hreach : ∀ s, Reach .rt n s → mem (bitmap (reachList .rt n)) s = true := by
    intro s hs
    induction hs with
    | init => exact h0
    | step hs' hst' ih =>
      obtain ⟨y, hy, rfl⟩ := hst'
      have := (hall _ (testBit_bitmap _ _ ih)).1.1
      simp only [closedB, List.all_eq_true] at this
      have := this y (mem_nodes (enabled_lt hy))
      simpa [hy] using this
  have hs : ∀ s, Reach .rt n s → _ := fun s hs' => hall s (testBit_bitmap _ _ (hreach s hs'))
  simp only [staticB, Bool.and_eq_true, List.all_eq_true] at hst
  obtain ⟨hwf, hcov⟩ := hst
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hr i j hij hi hj
    have := (hs s hr).1.2
    simp only [epB, List.all_eq_true] at this
    have := this j (mem_nodes (enabled_lt hj))
    simp only [hj, Bool.not_true, Bool.false_or, List.all_eq_true] at this
    have := this i (mem_nodes (enabled_lt hi))
    simpa [hij, hi] using this
  · intro s hr g hg
    exact (hs s hr).2 g hg
  · intro g hg
    have := hwf g hg
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.all_eq_true,
      bne_iff_ne, ne_eq] at this
    obtain ⟨⟨h1, h2⟩, h3⟩ := this
    refine ⟨h1, fun e => by simp [e] at h2, fun z hz => h3 z hz⟩
  · intro i hi k hk
    have := hcov i (mem_nodes hi)
    simp only [hk, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at this
    obtain ⟨g, hg, h1, h2⟩ := this
    exact ⟨g, hg, h1, h2⟩

/-! ### The per-state facts -/

section Facts
variable {s : Nat} {g : Nat × List (Nat × Bool)}

theorem gE (h : guardOkB n s g = true) (he : enabled .rt n s (c g.1) = true) :
    (∀ z ∈ g.2, excited .rt n s z.1 = false) ∧ level (fire s (c g.1)) g.1 g.2 = 0 := by
  simp only [guardOkB, Bool.and_eq_true, Bool.or_eq_true, he, Bool.not_true,
    Bool.false_or] at h
  obtain ⟨⟨h1, h2⟩, _⟩ := h
  simp only [List.all_eq_true, Bool.not_eq_true'] at h1
  exact ⟨h1, by simpa using h2⟩

theorem gM (h : guardOkB n s g = true) (hf : inflight s g.1 = true) {y : Nat}
    (hy : enabled .rt n s y = true) (hf' : inflight (fire s y) g.1 = true) :
    level (fire s y) g.1 g.2 = level s g.1 g.2 ∨
    (level (fire s y) g.1 g.2 = level s g.1 g.2 + 1 ∧
      (g.2[level s g.1 g.2]?).map Prod.fst = some y) := by
  simp only [guardOkB, Bool.and_eq_true, hf, Bool.not_true, Bool.false_or] at h
  have := h.2.1
  simp only [List.all_eq_true] at this
  have := this y (mem_nodes (enabled_lt hy))
  simp only [hy, hf', Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq,
    Bool.and_eq_true] at this
  exact this

theorem gX (h : guardOkB n s g = true) (hf : inflight s g.1 = true) {j : Nat} {z : Nat × Bool}
    (hz : g.2[j]? = some z) (he : excited .rt n s z.1 = true) : j ≤ level s g.1 g.2 := by
  simp only [guardOkB, Bool.and_eq_true, hf, Bool.not_true, Bool.false_or] at h
  have := h.2.2
  simp only [List.all_eq_true] at this
  have hj : j < g.2.length := by
    apply Classical.byContradiction; intro hj
    rw [List.getElem?_eq_none (by omega)] at hz; cases hz
  have := this j (List.mem_range.2 hj)
  simp only [hz, he, Bool.not_true, Bool.false_or, decide_eq_true_eq] at this
  exact this
end Facts

/-! ## The timing argument: the feedback has settled when a pin driver fires -/

theorem last_change (o : Trace) : ∀ t, (∀ u, u ≤ t → o u = o 0) ∨
    ∃ τ, τ < t ∧ o τ ≠ o (τ + 1) ∧ ∀ u, τ + 1 ≤ u → u ≤ t → o u = o (τ + 1) := by
  intro t
  induction t with
  | zero => left; intro u hu; have : u = 0 := by omega
            rw [this]
  | succ t ih =>
    by_cases hc : o t = o (t + 1)
    · rcases ih with h | ⟨τ, h1, h2, h3⟩
      · left; intro u hu
        by_cases e : u = t + 1
        · rw [e, ← hc]; exact h t (Nat.le_refl _)
        · exact h u (by omega)
      · right; refine ⟨τ, by omega, h2, fun u hu1 hu2 => ?_⟩
        by_cases e : u = t + 1
        · rw [e, ← hc]; exact h3 t (by omega) (Nat.le_refl _)
        · exact h3 u hu1 (by omega)
    · right; refine ⟨t, by omega, hc, fun u hu1 hu2 => ?_⟩
      have : u = t + 1 := by omega
      rw [this]

theorem take_succ_sum (lo : Nat → Nat) (zs : List (Nat × Bool)) (j : Nat) (z : Nat × Bool)
    (hz : zs[j]? = some z) : loSum lo zs (j + 1) = loSum lo zs j + lo z.1 := by
  simp only [loSum, List.take_add_one, hz, Option.toList, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]

/-- Along a serialized ps in flight, the level crosses `j` only by firing
loop node `j`. -/
theorem run_level (hC : Cert n) {k : Nat} {zs : List (Nat × Bool)} (hg : (k, zs) ∈ guards n)
    {j : Nat} : ∀ (L : List Nat) (s : Nat), Reach .rt n s → RunL n s L → inflight s k = true →
      f k ∉ L → c k ∉ L → level s k zs ≤ j → j < level (finalL s L) k zs →
      ∃ y ∈ L, (zs[j]?).map Prod.fst = some y := by
  intro L
  induction L with
  | nil => intro s _ _ _ _ _ h1 h2; simp [finalL] at h2; omega
  | cons y L ih =>
    intro s hs hr hf hnf hnc h1 h2
    obtain ⟨hy, hr'⟩ := hr
    have hyf : y ≠ f k := fun e => hnf (e ▸ List.mem_cons_self)
    have hyc : y ≠ c k := fun e => hnc (e ▸ List.mem_cons_self)
    have hf' : inflight (fire s y) k = true := by
      simp only [inflight, get_fire] at hf ⊢
      simp [hyf, hyc, hf]
    have hs' : Reach .rt n (fire s y) := Reach.step hs ⟨y, hy, rfl⟩
    rcases gM (hC.guard s hs _ hg) hf hy hf' with he | ⟨he1, he2⟩
    · obtain ⟨y', hy', h⟩ := ih (fire s y) hs' hr' hf' (fun h => hnf (List.mem_cons_of_mem _ h))
        (fun h => hnc (List.mem_cons_of_mem _ h)) (by simp only at he; omega) h2
      exact ⟨y', List.mem_cons_of_mem _ hy', h⟩
    · by_cases hj : level (fire s y) k zs ≤ j
      · obtain ⟨y', hy', h⟩ := ih (fire s y) hs' hr' hf' (fun h => hnf (List.mem_cons_of_mem _ h))
          (fun h => hnc (List.mem_cons_of_mem _ h)) hj h2
        exact ⟨y', List.mem_cons_of_mem _ hy', h⟩
      · have : level s k zs = j := by simp only at he1; omega
        exact ⟨y, List.mem_cons_self, by rw [← this]; exact he2⟩

/-- **H_FB_BEFORE_INPUT, derived.** If the pin driver `d` at the end of the
loop `zs` of stage `k` changes at `t`, and every earlier ps was an rt run,
then the feedback wire `f k` has caught up with `c k` at `t`, provided
`hi (f k) < Σ lo` over the loop. -/
theorem fb_settled (hT : Timed n lo hi x) (hC : Cert n) {t : Nat}
    (hR : ∀ u, u ≤ t → Reach .rt n (x u))
    (hTick : ∀ u, u < t → ∀ i ∈ chg n x u, enabled .rt n (x u) i = true)
    {k : Nat} {zs : List (Nat × Bool)} (hg : (k, zs) ∈ guards n)
    (hFB : hi (f k) < loSum lo zs zs.length)
    {d : Nat} {p : Bool} (hd : zs.getLast? = some (d, p)) (hdc : d ∈ chg n x t) :
    get (x t) (f k) = get (x t) (c k) := by
  obtain ⟨hk, hne, hzs⟩ := hC.wf _ hg
  simp only at hk hne hzs
  have hfN : f k < numNodes n := by unfold f numNodes; omega
  have gf := hT.gate (f k) hfN
  apply Classical.byContradiction; intro hfl
  -- Step 1: the last change of `c k` before `t`
  rcases last_change (fun u => get (x u) (c k)) t with hconst | ⟨τ, hτt, hτc, hcst⟩
  · -- `c k` never changed: then neither did `f k`
    have : ∀ u, u ≤ t → get (x u) (f k) = false := by
      intro u
      induction u with
      | zero => intro _; rw [hT.init]; exact get_zero _
      | succ u ih =>
        intro hu
        by_cases hch : get (x u) (f k) = get (x (u + 1)) (f k)
        · rw [← hch]; exact ih (by omega)
        · obtain ⟨_, hw⟩ := gf.cause u hch
          have := hw u (by have := gf.lo_pos; omega) (Nat.le_refl _)
          simp only [nextVal_f] at this
          rw [← this, hconst u (by omega), hT.init]; exact get_zero _
    apply hfl
    rw [this t (Nat.le_refl _), hconst t (Nat.le_refl _), hT.init, get_zero]
  · -- Step 2: `f k` is in flight on all of `[τ+1, t]`
    have hfl' : ∀ u, τ + 1 ≤ u → u ≤ t → get (x u) (f k) ≠ get (x u) (c k) := by
      intro u hu1 hu2 heq
      have : ∀ v, u ≤ v → v ≤ t → get (x v) (f k) = get (x v) (c k) := by
        intro v
        induction v with
        | zero => intro h1 _; have : u = 0 := by omega
                  subst this; exact heq
        | succ v ih =>
          intro h1 h2
          by_cases e : u = v + 1
          · subst e; exact heq
          · have ih' := ih (by omega) (by omega)
            rw [hcst (v + 1) (by omega) h2]
            by_cases hch : get (x v) (f k) = get (x (v + 1)) (f k)
            · rw [← hch, ih', hcst v (by omega) (by omega)]
            · obtain ⟨_, hw⟩ := gf.cause v hch
              have := hw v (by have := gf.lo_pos; omega) (Nat.le_refl _)
              simp only [nextVal_f] at this
              rw [← this, hcst v (by omega) (by omega)]
      exact hfl (this t hu2 (Nat.le_refl _))
    have hinf : ∀ u, τ + 1 ≤ u → u ≤ t → inflight (x u) k = true := by
      intro u h1 h2; simp only [inflight, bne_iff_ne, ne_eq]; exact hfl' u h1 h2
    -- Step 3: settle: `t ≤ τ + hi (f k)`
    have hset : t ≤ τ + hi (f k) := by
      apply Classical.byContradiction; intro hlt
      have := gf.settle (τ + 1 + hi (f k)) (by omega) (by
        intro u h1 h2
        show nextVal .free n (x u) (f k) = nextVal .free n (x (τ + 1 + hi (f k) - hi (f k))) (f k)
        simp only [nextVal_f]
        rw [hcst u (by omega) (by omega), hcst (τ + 1 + hi (f k) - hi (f k)) (by omega) (by omega)])
      simp only [nextVal_f] at this
      exact hfl' _ (by omega) (by omega) this
    -- Step 4: at `τ`, `c k` was enabled: no loop node excited; level 0 after
    have hcN : c k < numNodes n := by unfold c numNodes; omega
    have hcchg : c k ∈ chg n x τ := mem_chg.2 ⟨hcN, hτc⟩
    have hen := hTick τ hτt _ hcchg
    obtain ⟨hz0, hl0⟩ := gE (hC.guard _ (hR τ (by omega)) _ hg) hen
    simp only at hz0 hl0
    have hlev0 : level (x (τ + 1)) k zs = 0 := by
      rw [← hl0]
      apply level_congr
      · intro z hz
        rw [no_change hT (hz0 z hz), get_fire]
        have : ¬ c k = z.1 := fun e => (hzs z hz).2 e.symm
        simp [this]
      · rw [get_fire]; simp only [decide_true, Bool.xor_true]
        revert hτc; cases get (x τ) (c k) <;> cases get (x (τ + 1)) (c k) <;> simp
    -- the loop node `z` fired at `c'` (`τ+1 ≤ c' < t+1`): it was excited in flight from
    -- `c' + 1 - lo z ≥ τ + 1`
    have hwin : ∀ c' z, τ + 1 ≤ c' → c' ≤ t → z ∈ zs → z.1 ∈ chg n x c' →
        1 ≤ lo z.1 ∧ lo z.1 ≤ c' + 1 ∧ τ + 1 ≤ c' + 1 - lo z.1 ∧ excited .rt n (x (c' + 1 - lo z.1)) z.1 = true := by
      intro c' z h1 h2 hz hm
      obtain ⟨hzN, hzc⟩ := mem_chg.1 hm
      obtain ⟨hl, hex⟩ := exc_window hT hzN hzc
      have hl1 := (hT.gate z.1 hzN).lo_pos
      refine ⟨hl1, hl, ?_, hex _ (Nat.le_refl _) (by omega)⟩
      apply Classical.byContradiction; intro hlt
      have := hex τ (by omega) (by omega)
      rw [hz0 z hz] at this; cases this
    -- Step 5: the level argument
    have hP : ∀ j, ∀ u, τ + 1 ≤ u → u ≤ t → j ≤ level (x u) k zs → τ + 1 + loSum lo zs j ≤ u := by
      intro j
      induction j with
      | zero => intro u h1 _ _; simp [loSum]; omega
      | succ j ih =>
        intro u h1 h2 h3
        obtain ⟨c', hc1, hc2, hc3, hc4⟩ := crossing (fun v => j + 1 ≤ level (x v) k zs) (τ + 1) u
          h1 (by simp only [hlev0]; omega) h3
        have hTc := hTick c' (by omega)
        have hRc := hR c' (by omega)
        obtain ⟨hrun, _⟩ := runL_of_enabled hC.ep (chg n x c') (x c') hRc (chg_nodup c') hTc
        have hnf : f k ∉ chg n x c' := fun h => by
          have := (mem_chg.1 h).2
          apply this
          have e1 := hfl' c' (by omega) (by omega)
          have e2 := hfl' (c' + 1) (by omega) (by omega)
          rw [hcst c' (by omega) (by omega)] at e1
          rw [hcst (c' + 1) (by omega) (by omega)] at e2
          revert e1 e2; cases get (x c') (f k) <;> cases get (x (c' + 1)) (f k) <;>
            cases get (x (τ + 1)) (c k) <;> simp
        have hnc : c k ∉ chg n x c' := fun h => (mem_chg.1 h).2
          (by rw [hcst c' (by omega) (by omega), hcst (c' + 1) (by omega) (by omega)])
        obtain ⟨y, hy, hzj⟩ := run_level hC hg (j := j) (chg n x c') (x c') hRc hrun
          (hinf c' (by omega) (by omega)) hnf hnc (by omega)
          (by rw [finalL_chg hT]; omega)
        cases hz : zs[j]? with
        | none => rw [hz] at hzj; cases hzj
        | some z =>
          rw [hz] at hzj; simp only [Option.map_some, Option.some.injEq] at hzj
          subst hzj
          have hzm : z ∈ zs := List.mem_of_getElem? hz
          obtain ⟨hl0, hl, hge, hex⟩ := hwin c' z (by omega) (by omega) hzm hy
          have hlv := gX (hC.guard _ (hR _ (by omega)) _ hg)
            (hinf _ hge (by omega)) hz hex
          have := ih _ hge (by omega) hlv
          rw [take_succ_sum lo zs j z hz]
          omega
    -- Step 6: the pin driver itself
    have hlen : zs.length - 1 + 1 = zs.length := by
      have : zs.length ≠ 0 := fun e => hne (List.eq_nil_of_length_eq_zero e)
      omega
    have hdz : zs[zs.length - 1]? = some (d, p) := by
      rw [List.getLast?_eq_getElem?] at hd; exact hd
    have hdm : (d, p) ∈ zs := List.mem_of_getElem? hdz
    obtain ⟨hl0, hl, hge, hex⟩ := hwin t (d, p) (by omega) (Nat.le_refl _) hdm hdc
    have hlv := gX (hC.guard _ (hR _ (by omega)) _ hg) (hinf _ hge (by omega)) hdz hex
    have := hP _ _ hge (by omega) hlv
    have hs := take_succ_sum lo zs _ _ hdz
    rw [hlen, show loSum lo zs zs.length = loSum lo zs zs.length from rfl] at hs
    dsimp only at hs hl0 hl hge this
    omega

/-! ## The bridge -/

/-- The timing hypothesis, guard form: the feedback route of stage `k` is
faster than the lower-bound sum of each of its two loops. -/
def FbGuards (n : Nat) (lo hi : Nat → Nat) : Prop :=
  ∀ g ∈ guards n, hi (f g.1) < loSum lo g.2 g.2.length

/-- **Bridge relative to the RT constraint.** Every timed state is
rt-reachable, and at every ps the changing nodes are rt-enabled. -/
theorem timed_good (hT : Timed n lo hi x) (hC : Cert n) (hFB : FbGuards n lo hi) :
    ∀ t, (∀ u, u ≤ t → Reach .rt n (x u)) ∧
      (∀ u, u < t → ∀ i ∈ chg n x u, enabled .rt n (x u) i = true) := by
  intro t
  induction t with
  | zero =>
    refine ⟨fun u hu => ?_, fun u hu => absurd hu (Nat.not_lt_zero _)⟩
    have : u = 0 := by omega
    rw [this, hT.init]; exact Reach.init
  | succ t ih =>
    obtain ⟨hR, hE⟩ := ih
    have hEt : ∀ i ∈ chg n x t, enabled .rt n (x t) i = true := by
      intro i hm
      have hiN := (mem_chg.1 hm).1
      have hex := chg_exc hT hm
      simp only [enabled, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨hiN, hex⟩, ?_⟩
      unfold allowed
      cases hrs : readerStage n i with
      | none => rfl
      | some k =>
        obtain ⟨g, hg, hgk, hgl⟩ := hC.cover i hiN k hrs
        obtain ⟨k', zs⟩ := g
        simp only at hgk hgl; subst hgk
        cases hl : zs.getLast? with
        | none => rw [hl] at hgl; cases hgl
        | some z =>
          rw [hl] at hgl; simp only [Option.map_some, Option.some.injEq] at hgl
          obtain ⟨d, p⟩ := z; simp only at hgl; subst hgl
          have := fb_settled hT hC hR hE hg (hFB _ hg) hl hm
          simp [this]
    refine ⟨fun u hu => ?_, fun u hu => ?_⟩
    · by_cases e : u = t + 1
      · subst e
        rw [← finalL_chg hT t]
        exact (runL_of_enabled hC.ep _ _ (hR t (Nat.le_refl _)) (chg_nodup t) hEt).2
      · exact hR u (by omega)
    · by_cases e : u = t
      · subst e; exact hEt
      · exact hE u (by omega)

theorem timed_reach (hT : Timed n lo hi x) (hC : Cert n) (hFB : FbGuards n lo hi) (t : Nat) :
    Reach .rt n (x t) := (timed_good hT hC hFB t).1 t (Nat.le_refl _)

theorem timed_enabled (hT : Timed n lo hi x) (hC : Cert n) (hFB : FbGuards n lo hi) {t i : Nat}
    (h : i ∈ chg n x t) : enabled .rt n (x t) i = true :=
  (timed_good hT hC hFB (t + 1)).2 t (Nat.lt_succ_self _) i h

/-- One ps of a timed trace, serialized in index order, is an rt run. -/
theorem timed_step_run (hT : Timed n lo hi x) (hC : Cert n) (hFB : FbGuards n lo hi) (t : Nat) :
    RunL n (x t) (chg n x t) ∧ finalL (x t) (chg n x t) = x (t + 1) :=
  ⟨(runL_of_enabled hC.ep _ _ (timed_reach hT hC hFB t) (chg_nodup t)
    (fun _ h => timed_enabled hT hC hFB h)).1, finalL_chg hT t⟩

/-! ## Consequences for timed traces (given 8c's invariant `Good .rt n`) -/

/-- The four-phase protocol on every link of the chain, in time. -/
theorem timed_protocol (hT : Timed n lo hi x) (hC : Cert n) (hFB : FbGuards n lo hi)
    (hgood : ∀ s, Reach .rt n s → Good .rt n s) {X Y : Nat} (hp : (X, Y) ∈ pairs n) :
    Handshake.Protocol ⟨fun t => get (x t) X, fun t => get (x t) Y, fun _ => 0⟩ := by
  refine ⟨⟨by simp [hT.init, get_zero], by simp [hT.init, get_zero]⟩, fun t => ⟨?_, ?_⟩⟩
  · intro hch
    simp only at hch ⊢
    have hm : X ∈ chg n x t := mem_chg.2 ⟨change_lt hT (fun e => hch e.symm), fun e => hch e.symm⟩
    exact (pairOk_iff ((hgood _ (timed_reach hT hC hFB t)).2 X
      (timed_enabled hT hC hFB hm) _ hp)).1 rfl
  · intro hch
    simp only at hch ⊢
    have hm : Y ∈ chg n x t := mem_chg.2 ⟨change_lt hT (fun e => hch e.symm), fun e => hch e.symm⟩
    exact (pairOk_iff ((hgood _ (timed_reach hT hC hFB t)).2 Y
      (timed_enabled hT hC hFB hm) _ hp)).2 rfl

/-- Token order between consecutive stages, in time. -/
theorem timed_token_order (hT : Timed n lo hi x) (hC : Cert n) (hFB : FbGuards n lo hi)
    (hgood : ∀ s, Reach .rt n s → Good .rt n s) {k : Nat} (hk1 : 1 ≤ k) (hkn : k < n) (t : Nat) :
    tog (fun t => get (x t) (c k)) t ≤ tog (fun t => get (x t) (c (k - 1))) t ∧
    tog (fun t => get (x t) (c (k - 1))) t ≤ tog (fun t => get (x t) (c k)) t + 1 := by
  have hp : (c (k - 1), c k) ∈ pairs n := by
    simp only [pairs, List.mem_append, List.mem_flatMap, List.mem_filter, List.mem_range,
      List.mem_cons, decide_eq_true_eq]
    exact Or.inr ⟨k, ⟨hkn, hk1⟩, Or.inl rfl⟩
  have := protocol_tog (timed_protocol hT hC hFB hgood hp) t
  simp only at this
  by_cases he : get (x t) (c (k - 1)) = get (x t) (c k) <;>
    simp only [he, ite_true, ite_false] at this <;> omega

theorem runL_persist (hgood : ∀ s, Reach .rt n s → Good .rt n s) {i : Nat} (hiN : i < numNodes n) :
    ∀ (L : List Nat) (s : Nat), Reach .rt n s → RunL n s L → i ∉ L →
      excited .rt n s i = true → excited .rt n (finalL s L) i = true := by
  intro L
  induction L with
  | nil => intro s _ _ _ h; exact h
  | cons y L ih =>
    intro s hs hr hni he
    obtain ⟨hy, hr'⟩ := hr
    have hiy : i ≠ y := fun e => hni (e ▸ List.mem_cons_self)
    exact ih (fire s y) (Reach.step hs ⟨y, hy, rfl⟩) hr' (fun h => hni (List.mem_cons_of_mem _ h))
      ((hgood s hs).1 i y hiN hiy hy he)

/-- **No glitch anywhere, in time.** If the real gate function of any node
(LUT, wire, environment) differs from the node at `t` and the node does not
change at `t`, it still differs at `t+1`: no excitation is withdrawn, so no
LUT output and no route ever carries a runt. -/
theorem timed_hazard_free (hT : Timed n lo hi x) (hC : Cert n) (hFB : FbGuards n lo hi)
    (hgood : ∀ s, Reach .rt n s → Good .rt n s) {t i : Nat} (hiN : i < numNodes n)
    (he : nextVal .free n (x t) i ≠ get (x t) i) (hs : get (x (t + 1)) i = get (x t) i) :
    nextVal .free n (x (t + 1)) i ≠ get (x (t + 1)) i := by
  obtain ⟨hr, hfin⟩ := timed_step_run hT hC hFB t
  have hni : i ∉ chg n x t := fun h => (mem_chg.1 h).2 hs.symm
  have hex : excited .rt n (x t) i = true := by
    simp only [excited, ← nextVal_free_rt, bne_iff_ne, ne_eq]; exact he
  have := runL_persist hgood hiN _ _ (timed_reach hT hC hFB t) hr hni hex
  rw [hfin] at this
  simp only [excited, ← nextVal_free_rt, bne_iff_ne, ne_eq] at this
  exact this

/-! ## The timing hypothesis in explicit form -/

/-- **H_FB_DELAY** (the exact inequality): for every stage `k`, the feedback
route's maximum delay is below the lower-bound sum of both neighbour loops.
`lo (b k)` is the req path (route + LUT1 + route, lumped), `lo (w k)` the ack
route, `lo (c k)` the LUT6, `lo src` / `lo snk` the environment's response. -/
structure FbBound (n : Nat) (lo hi : Nat → Nat) : Prop where
  pred0 : hi (f 0) < lo (w 0) + lo src
  pred  : ∀ k, 1 ≤ k → k < n → hi (f k) < lo (w k) + lo (c (k - 1)) + lo (b (k - 1))
  succL : hi (f (n - 1)) < lo (b (n - 1)) + lo snk
  succ  : ∀ k, k + 1 < n → hi (f k) < lo (b k) + lo (c (k + 1)) + lo (w (k + 1))

theorem FbBound.guards {n : Nat} {lo hi : Nat → Nat} (h : FbBound n lo hi) : FbGuards n lo hi := by
  intro g hg
  simp only [MullerTimed.guards, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hg
  obtain ⟨k, hk, hg⟩ := hg
  rcases hg with rfl | rfl
  · unfold predG
    by_cases h0 : k = 0
    · simp only [h0, ite_true, loSum, List.length_cons, List.length_nil, List.take_succ_cons,
        List.take_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      have := h.pred0; omega
    · simp only [h0, ite_false, loSum, List.length_cons, List.length_nil, List.take_succ_cons,
        List.take_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      have := h.pred k (by omega) hk; omega
  · unfold succG
    by_cases h0 : k + 1 = n
    · simp only [h0, ite_true, loSum, List.length_cons, List.length_nil, List.take_succ_cons,
        List.take_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      have := h.succL; rw [show n - 1 = k by omega] at this; omega
    · simp only [h0, ite_false, loSum, List.length_cons, List.length_nil, List.take_succ_cons,
        List.take_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      have := h.succ k (by omega); omega

end Formal.Net.MullerTimed
