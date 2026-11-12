import Formal.Timing.Semantics

/-!
# Interval timing checker, proved sound, and per-node exact over free cell functions (probe C-10a)

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
* `win_early_attained`, `win_late_attained`  the windows are exact OVER THE CHOICE
  OF CELL FUNCTIONS: for every reachable node there is a run (a fixed-delay one,
  hence also a `FixedRun`) in which the node switches exactly at its earliest time,
  and one at its latest. The witness run picks the node functions itself (OR in
  `earlyRun`, AND-of-reachable-inputs in `lateRun`). For a netlist whose cell
  functions are FIXED (real LUT INITs) the window is only an upper bound:
  `Formal.Timing.FixedFn.win_exact_needs_free_fn` (CheckerFixedFn.lean, an XOR of
  two `[5,5]` arcs: window `(5,5)`, never switches). Soundness does not depend on
  this: it holds for every cell function.
* `check_exact_disjoint`  the check itself is exact (complete) when the request
  and data cones share only the launch node (`Separated`), again over the choice
  of cell functions: a failing check then has a fixed-delay run, with
  witness-chosen OR/AND node functions (`mixRun`), that really violates bundling.
  With fixed cell functions a failing check may be a false alarm.
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
      | some (_, ld) => decide (ld + setup ≤ er)

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
attained by some run (in fact a fixed-delay run). The run's node functions are
chosen by the witness (OR, `earlyRun`); with fixed cell functions this is not
claimed (see `FixedFn.win_exact_needs_free_fn`). -/
theorem win_early_attained {net : Netlist} (hwf : net.WF) {v e l : Nat}
    (hw : win net v = some (e, l)) :
    ∃ sig, Nonempty (FixedRun net sig) ∧ Nonempty (Run net sig) ∧ changes (sig v) e :=
  ⟨earlySig net, ⟨earlyRun net hwf⟩, ⟨(earlyRun net hwf).toRun⟩, by
    simp only [changes, earlySig, hw]; simp⟩

/-- **Exactness, latest.** The witness chooses the node functions (AND of the
reachable inputs, `lateRun`); with fixed cell functions this is not claimed. -/
theorem win_late_attained {net : Netlist} (hwf : net.WF) {v e l : Nat}
    (hw : win net v = some (e, l)) :
    ∃ sig, Nonempty (FixedRun net sig) ∧ Nonempty (Run net sig) ∧ changes (sig v) l :=
  ⟨lateSig net, ⟨lateRun net hwf⟩, ⟨(lateRun net hwf).toRun⟩, by
    simp only [changes, lateSig, hw]; simp⟩

/-- **Window exactness, summary.** `win` is the exact switching hull OVER ALL LOCAL
CELL FUNCTIONS: unreachable nodes never switch in any run; a reachable node
switches only inside `[e, l]` in every run with any cell functions (soundness);
and both ends are attained by fixed-delay runs whose node functions the witness
chooses (OR / AND). For a netlist with fixed cell functions only the soundness half
applies and `[e, l]` is an upper bound (`FixedFn.win_exact_needs_free_fn`). -/
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
property. So for such netlists the check is exact (sound and complete) over the
choice of cell functions: the violating run uses witness-chosen OR/AND node
functions (`mixRun`), so with fixed cell functions (real LUT INITs) a failing
check is only a possible violation, not a certain one. -/
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
