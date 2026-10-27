import Formal.Core.LutAudit

/-!
# Formal.Core.Env — mechanised environment model for the LUT hazard audit

Shard A. Notes: `formal/notes/A-env.md`.

`Formal.Core.LutAudit` classified every multi-input change (MIC) of every LUT
and then argued IN PROSE which MICs each cell's protocol can present. This file
replaces that prose by a state-graph exploration, checked by the kernel
(`decide +kernel`, no `native_decide`):

* a cell = its LUTs, taken verbatim from `Formal.Core.LutCells` (generated from
  `cells/rtl/*.v`), with the Boolean function `LutAudit.outB`, plus explicit
  WIRE elements for the fork branches whose delay matters (a wire is a buffer
  with its own unbounded delay);
* its environment = a small set of guarded toggles (four-phase handshake,
  bundled data held stable inside its window);
* the untimed speed-independent semantics: one signal changes per step, any
  excited element may fire, in any interleaving (unbounded element delays, the
  GMW model of `Formal.Core.Ternary`);
* the ONLY timing knowledge is an explicit list `prio` of relative-timing
  assumptions `(fast, slow)`: while `fast` is excited, `slow` does not fire.
  Each cell's assumptions are named fields of a configuration structure, so
  every theorem states which ones it uses, and for each one there is a
  theorem showing that dropping it produces a reachable hazard.

## What a "multi-input change at a LUT" is here

The state carries, per LUT and per pin, whether that pin's last change may
still be in flight inside the LUT's mux tree, and the set of transitions that
were enabled when it changed and have stayed enabled since (`pend`). A later
transition `t` meets an in-flight change `x` inside the LUT iff `t ∈ pend x`,
i.e. their excitation intervals overlapped; a transition enabled only AFTER
`x` happened arrives after `x` has settled. That is the named delay hypothesis

  **H_SETTLE**: a LUT's mux tree settles an input change faster than any
  element (gate, wire, environment) can respond to a transition that was not
  yet excited when that input changed.

and the convention of `LutAudit` for feedback,

  **H_FB_FUND** (fundamental mode of the cell's own loop): when a LUT's output
  fires, the input changes that excited it have settled; its in-flight set is
  cleared and its feedback pin changes together with its output.

Under those, the MIC a LUT sees at each step is `old → new` with
`old = new` with every in-flight pin flipped back, and the check is
LutAudit's `classify old new ∈ {sic, sHF, dHF}`, i.e. single input change or
Eichelberger/Unger function-hazard-free (`lutOK_sem`), plus: a LUT excited at
`old` is still excited at `new` (no withdrawal inside a MIC).

## Checks, per reachable transition (`stepOK`)

1. `lutOK`: every LUT that does not fire sees a hazard-free MIC (above).
2. `persistOK` (semi-modularity / output persistence): no excited gate or wire
   is disabled by another transition, and no gate disables an excited
   environment transition. Environment-vs-environment conflicts are the
   environment's own choices and allowed.
Per reachable state: liveness (some transition enabled) and, for bd_link, data
validity at the receiver.

## Soundness

`certify_sound`: a kernel-checked certificate (a set `T` of state codes that
contains the initial states, is closed under `succs` and satisfies the checks)
implies the checks on every reachable state (`Reach`). `T` is computed in Lean
by `reachTree` (a DFS with a BST); its correctness is never assumed — only the
certificate check is trusted. Negative controls (`witness_sound`) replay an
explicit trace and evaluate the failing check.
-/

namespace Formal.Core.Env

open Formal.Core.LutTree Formal.Core.LutTree.PhysTree Formal.Core.LutCells Formal.Core.LutAudit

/-! ## 1. Model -/

/-- A circuit element. `lut q L o pins`: output `o` of LUT instance `L` (from
`LutCells`) drives signal `q`; `pins` lists, ROOT FIRST and for the FREE pins
only (the order of `LutAudit.opins`), the signal on each pin. `wire q src`: a
fork branch with its own unbounded delay, `q` follows `src`. -/
inductive Gate where
  | lut (out : Nat) (L : LutInst) (o : OutSel) (pins : List Nat)
  | wire (out src : Nat)

def Gate.out : Gate → Nat
  | .lut q _ _ _ => q
  | .wire q _ => q

/-- A closed system: signals `0..n-1`, elements, environment toggles
`(signal, guard)`, relative-timing assumptions `(fast, slow)`, initial states.
A state is a `Nat`: bits `0..n-1` are the signal values, above them the
in-flight records (`slot`). -/
structure Model where
  n : Nat
  gates : List Gate
  env : List (Nat × (Nat → Bool))
  prio : List (Nat × Nat)
  inits : List Nat
  /-- `true`: H_SETTLE (the semantics described above). `false`: an in-flight pin
  stays in flight until its LUT fires (pure unbounded mux-tree delays); used
  only for the ablation `latch_needs_settle`. -/
  settle : Bool := true

def bit (s i : Nat) : Bool := s.testBit i

def pinVec (s : Nat) (pins : List Nat) : List Bool := pins.map (bit s)

/-- Boolean value an element is driving towards. -/
def Gate.val (s : Nat) : Gate → Bool
  | .lut _ L o pins => outB L o (pinVec s pins)
  | .wire _ src => bit s src

def Gate.exc (s : Nat) (g : Gate) : Bool := g.val s != bit s g.out

def setBit (m i : Nat) : Nat := if bit m i then m else m + 2 ^ i
def clrBit (m i : Nat) : Nat := if bit m i then m - 2 ^ i else m

/-- Excited signals (gates whose output differs from their function, and
environment toggles whose guard holds). -/
def excMask (M : Model) (s : Nat) : Nat :=
  M.env.foldl (fun m e => if e.2 s then setBit m e.1 else m)
    (M.gates.foldl (fun m g => if g.exc s then setBit m g.out else m) 0)

/-- Enabled = excited and not held back by an excited `fast` partner. -/
def enMask (M : Model) (s : Nat) : Nat :=
  let ex := excMask M s
  M.prio.foldl (fun m p => if bit ex p.1 && p.1 != p.2 then clrBit m p.2 else m) ex

/-- In-flight record of pin `j` of element `gi`: the `pend` mask (n bits);
0 = settled. -/
def off (M : Model) (gi j : Nat) : Nat := M.n * (1 + 6 * gi + j)
def slot (M : Model) (s gi j : Nat) : Nat := (s >>> off M gi j) % 2 ^ M.n

/-- After transition `t`, is pin `j` (signal `p`) of element `gi` in flight? -/
def inflight (M : Model) (s t gi j p : Nat) : Bool := p == t || bit (slot M s gi j) t

/-- New `pend` record (before dropping settled pins it is `inflight`). -/
def newPend (M : Model) (s t gi j p : Nat) : Nat :=
  if !M.settle then (if p == t || slot M s gi j != 0 then 2 ^ M.n - 1 else 0) else
  if p == t then clrBit (enMask M s) t &&& enMask M (s ^^^ 2 ^ t)
  else
    let pd := slot M s gi j
    if bit pd t then clrBit pd t &&& enMask M (s ^^^ 2 ^ t) else 0

/-- Index a list. -/
def idxd {α : Type} : List α → Nat → List (α × Nat)
  | [], _ => []
  | a :: as, i => (a, i) :: idxd as (i + 1)

def pinSlots (M : Model) (s t gi : Nat) (pins : List Nat) : Nat :=
  (idxd pins 0).foldl (fun acc pj => acc + (newPend M s t gi pj.2 pj.1 <<< off M gi pj.2)) 0

def slotsOf (M : Model) (s t : Nat) : Nat :=
  (idxd M.gates 0).foldl (fun acc ggi =>
    match ggi.1 with
    | .lut q _ _ pins => if q == t then acc else acc + pinSlots M s t ggi.2 pins
    | .wire _ _ => acc) 0

/-- Fire signal `t`. -/
def post (M : Model) (s t : Nat) : Nat := (s ^^^ 2 ^ t) % 2 ^ M.n + slotsOf M s t

def succs (M : Model) (s : Nat) : List (Nat × Nat) :=
  ((List.range M.n).filter (bit (enMask M s))).map fun t => (t, post M s t)

inductive Reach (M : Model) : Nat → Prop
  | init {s : Nat} : s ∈ M.inits → Reach M s
  | step {s : Nat} {p : Nat × Nat} : Reach M s → p ∈ succs M s → Reach M p.2

/-! ## 2. Checks -/

/-- The pin vector the LUT saw before the in-flight changes. -/
def oldVec (M : Model) (s t gi : Nat) (pins : List Nat) : List Bool :=
  (idxd pins 0).map fun pj => bit (s ^^^ 2 ^ t) pj.1 ^^ inflight M s t gi pj.2 pj.1

def okCls : Cls → Bool
  | .sic => true
  | .sHF => true
  | .dHF => true
  | _ => false

/-- The MIC a non-firing LUT sees on transition `t` is hazard-free and does not
withdraw an excitation. -/
def lutOK (M : Model) (s t : Nat) (g : Gate) (gi : Nat) : Bool :=
  match g with
  | .lut q L o pins =>
      q == t ||
        (okCls (classify L o (oldVec M s t gi pins) (pinVec (s ^^^ 2 ^ t) pins)) &&
          !(outB L o (oldVec M s t gi pins) != bit (s ^^^ 2 ^ t) q &&
            outB L o (pinVec (s ^^^ 2 ^ t) pins) == bit (s ^^^ 2 ^ t) q))
  | .wire _ _ => true

def isEnv (M : Model) (i : Nat) : Bool := M.env.any (·.1 == i)

/-- Output persistence (semi-modularity) of transition `t` from `s`. -/
def persistOK (M : Model) (s t : Nat) : Bool :=
  (List.range M.n).all fun u =>
    u == t || !bit (excMask M s) u || bit (excMask M (s ^^^ 2 ^ t)) u || (isEnv M t && isEnv M u)

def stepOK (M : Model) (s t : Nat) : Bool :=
  persistOK M s t && (idxd M.gates 0).all fun ggi => lutOK M s t ggi.1 ggi.2

/-- Liveness: some transition is enabled. -/
def live (M : Model) (s : Nat) : Bool := enMask M s != 0

/-- Everything checked on every reachable state and transition. -/
def Sound (M : Model) (Q : Nat → Bool) : Prop :=
  ∀ s, Reach M s → Q s = true ∧ ∀ p ∈ succs M s, stepOK M s p.1 = true

/-! ## 3. Certificates -/

inductive Tree where
  | leaf
  | node (l : Tree) (k : Nat) (r : Tree)

def Tree.contains : Tree → Nat → Bool
  | .leaf, _ => false
  | .node l k r, x => if x == k then true else if Nat.blt x k then l.contains x else r.contains x

def Tree.insert : Tree → Nat → Tree
  | .leaf, x => .node .leaf x .leaf
  | .node l k r, x =>
      if x == k then .node l k r
      else if Nat.blt x k then .node (l.insert x) k r else .node l k (r.insert x)

def Tree.toList : Tree → List Nat
  | .leaf => []
  | .node l k r => l.toList ++ k :: r.toList

theorem Tree.mem_of_contains : ∀ (t : Tree) (x : Nat), t.contains x = true → x ∈ t.toList
  | .leaf, _, h => by simp [Tree.contains] at h
  | .node l k r, x, h => by
      simp only [Tree.contains] at h
      simp only [Tree.toList, List.mem_append, List.mem_cons]
      by_cases hk : (x == k) = true
      · exact Or.inr (Or.inl (beq_iff_eq.1 hk))
      · simp only [hk, Bool.false_eq_true, ↓reduceIte] at h
        split at h
        · exact Or.inl (Tree.mem_of_contains l x h)
        · exact Or.inr (Or.inr (Tree.mem_of_contains r x h))

/-- Add the unseen states of a list. -/
def addNew (T : Tree) (todo : List Nat) : List Nat → Tree × List Nat
  | [] => (T, todo)
  | y :: ys => if T.contains y then addNew T todo ys else addNew (T.insert y) (y :: todo) ys

def explore (M : Model) : Nat → Tree → List Nat → Tree
  | 0, T, _ => T
  | _ + 1, T, [] => T
  | f + 1, T, x :: todo =>
      let r := addNew T todo ((succs M x).map Prod.snd)
      explore M f r.1 r.2

/-- The reachable set, computed (its correctness is NOT assumed). -/
def reachTree (M : Model) (fuel : Nat) : Tree :=
  explore M fuel (addNew .leaf [] M.inits).1 (addNew .leaf [] M.inits).2

/-- The certificate check. -/
def certify (M : Model) (Q : Nat → Bool) (T : Tree) : Bool :=
  M.inits.all T.contains &&
    T.toList.all fun s => Q s && (succs M s).all fun p => T.contains p.2 && stepOK M s p.1

theorem certify_sound {M : Model} {Q : Nat → Bool} {T : Tree} (h : certify M Q T = true) :
    Sound M Q := by
  simp only [certify, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hinit, hall⟩ := h
  have key : ∀ s, T.contains s = true →
      Q s = true ∧ ∀ p ∈ succs M s, T.contains p.2 = true ∧ stepOK M s p.1 = true := by
    intro s hs
    obtain ⟨hq, hp⟩ := hall s (Tree.mem_of_contains T s hs)
    exact ⟨hq, fun p hpm => hp p hpm⟩
  have inv : ∀ s, Reach M s → T.contains s = true := by
    intro s hs
    induction hs with
    | init h => exact hinit _ h
    | step _ hp ih => exact ((key _ ih).2 _ hp).1
  intro s hs
  obtain ⟨hq, hp⟩ := key s (inv s hs)
  exact ⟨hq, fun p hpm => (hp p hpm).2⟩

/-- Number of states in a certificate. -/
def Tree.size (T : Tree) : Nat := T.toList.length

/-! ### Witness traces (negative controls) -/

def runTrace (M : Model) : Nat → List Nat → Option Nat
  | s, [] => some s
  | s, t :: ts => if decide (t < M.n) && bit (enMask M s) t then runTrace M (post M s t) ts else none

theorem mem_succs {M : Model} {s t : Nat} (ht : t < M.n) (he : bit (enMask M s) t = true) :
    (t, post M s t) ∈ succs M s := by
  simp only [succs, List.mem_map, List.mem_filter, List.mem_range]
  exact ⟨t, ⟨ht, he⟩, rfl⟩

theorem reach_run {M : Model} : ∀ (ts : List Nat) {s s' : Nat}, Reach M s →
    runTrace M s ts = some s' → Reach M s'
  | [], _, _, hs, h => by simp [runTrace] at h; exact h ▸ hs
  | t :: ts, s, s', hs, h => by
      simp only [runTrace] at h
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        exact reach_run ts (Reach.step (p := (t, post M s t)) hs (mem_succs hc.1 hc.2)) h
      · cases h

/-- A trace from an initial state, then a transition `t` on which `bad` holds. -/
def witness (M : Model) (s0 : Nat) (ts : List Nat) (t : Nat) (bad : Nat → Nat → Bool) : Bool :=
  match runTrace M s0 ts with
  | some s => decide (t < M.n) && bit (enMask M s) t && bad s t
  | none => false

theorem witness_sound {M : Model} {s0 : Nat} {ts : List Nat} {t : Nat} {bad : Nat → Nat → Bool}
    (h0 : s0 ∈ M.inits) (h : witness M s0 ts t bad = true) :
    ∃ s, Reach M s ∧ (t, post M s t) ∈ succs M s ∧ bad s t = true := by
  unfold witness at h
  split at h
  · rename_i s hr
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨s, reach_run ts (Reach.init h0) hr, mem_succs h.1.1 h.1.2, h.2⟩
  · cases h

/-- A witnessed bad transition refutes `Sound`. -/
theorem not_sound_of_witness {M : Model} {Q : Nat → Bool} {s0 : Nat} {ts : List Nat} {t : Nat}
    (h0 : s0 ∈ M.inits) (h : witness M s0 ts t (fun s t => !stepOK M s t) = true) :
    ¬ Sound M Q := by
  intro hS
  obtain ⟨s, hs, hm, hb⟩ := witness_sound h0 h
  have := (hS s hs).2 _ hm
  simp only at this
  simp [this] at hb

/-! ### Semantic reading of `lutOK` -/

theorem classify_sic {L : LutInst} {o : OutSel} {a b : List Bool} (h : classify L o a b = .sic) :
    ndiff a b ≤ 1 := by
  unfold classify at h
  split at h
  · assumption
  · split at h <;> split at h <;> cases h

/-- **What `lutOK` means.** On a transition that does not fire the LUT, the MIC
`old → new` it sees is a single-input change, or static function-hazard-free
(Eichelberger), or dynamic function-hazard-free (Unger / Nowick–Dill), in the
sense of `LutAudit`. -/
theorem lutOK_sem {M : Model} {s t q gi : Nat} {L : LutInst} {o : OutSel} {pins : List Nat}
    (h : lutOK M s t (.lut q L o pins) gi = true) (hq : q ≠ t) :
    ndiff (oldVec M s t gi pins) (pinVec (s ^^^ 2 ^ t) pins) ≤ 1 ∨
      StaticHF L o (oldVec M s t gi pins) (pinVec (s ^^^ 2 ^ t) pins) ∨
      DynHF L o (oldVec M s t gi pins) (pinVec (s ^^^ 2 ^ t) pins) := by
  have hq' : (q == t) = false := by simpa using hq
  simp only [lutOK, hq', Bool.false_or, Bool.and_eq_true] at h
  have hc := h.1
  generalize hcl : classify L o (oldVec M s t gi pins) (pinVec (s ^^^ 2 ^ t) pins) = c at hc
  cases c with
  | sic => exact Or.inl (classify_sic hcl)
  | sHF => exact Or.inr (Or.inl (classify_sHF hcl))
  | dHF => exact Or.inr (Or.inr (classify_dHF hcl))
  | sHZ => cases hc
  | dHZ => cases hc

/-- Reachable form: in a `Sound` model, every non-firing LUT on every reachable
transition sees a hazard-free MIC. -/
theorem reach_mic_hazard_free {M : Model} {Q : Nat → Bool} (hS : Sound M Q) {s : Nat}
    (hs : Reach M s) {p : Nat × Nat} (hp : p ∈ succs M s) {q gi : Nat} {L : LutInst}
    {o : OutSel} {pins : List Nat} (hg : (Gate.lut q L o pins, gi) ∈ idxd M.gates 0)
    (hq : q ≠ p.1) :
    ndiff (oldVec M s p.1 gi pins) (pinVec (s ^^^ 2 ^ p.1) pins) ≤ 1 ∨
      StaticHF L o (oldVec M s p.1 gi pins) (pinVec (s ^^^ 2 ^ p.1) pins) ∨
      DynHF L o (oldVec M s p.1 gi pins) (pinVec (s ^^^ 2 ^ p.1) pins) := by
  have h := (hS s hs).2 p hp
  simp only [stepOK, Bool.and_eq_true, List.all_eq_true] at h
  exact lutOK_sem (h.2 _ hg) hq

/-! ### MIC catalogue: the distinct `(old, new)` with ≥ 2 changed pins a LUT
sees over a certificate (for comparison with LutAudit's prose). -/

def micsAt (M : Model) (T : Tree) (gi : Nat) : List (List Bool × List Bool) :=
  match M.gates[gi]? with
  | some (.lut q _ _ pins) =>
      T.toList.foldl (fun acc s => (succs M s).foldl (fun acc p =>
        if p.1 == q then acc else
          let mic := (oldVec M s p.1 gi pins, pinVec (s ^^^ 2 ^ p.1) pins)
          if 2 ≤ ndiff mic.1 mic.2 && !acc.contains mic then acc ++ [mic] else acc) acc) []
  | _ => []

/-! ## 4. bd_c2 under a two-party four-phase environment

Signals: `a = 0`, `b = 1`, `q = 2`, `rst = 3`. LUT `bd_c2_u` (bd_ce.v:34), free
pins root first `[rst, q, b, a]`. Environment: two four-phase senders sharing
the acknowledge `q` (the join): `a` toggles while `a = q`, `b` while `b = q`,
both only after reset; `rst` is released once `q = 0` (**H_RST_LONG**: reset is
held until the loop has cleared; the LUT's power-up value is either). -/

def c2Model : Model where
  n := 4
  gates := [.lut 2 bd_c2_u .O [3, 2, 1, 0]]
  env := [(0, fun s => !bit s 3 && bit s 0 != bit s 2),
          (1, fun s => !bit s 3 && bit s 1 == bit s 2),
          (3, fun s => bit s 3 && !bit s 2)]
  prio := []
  inits := [8, 12]

/-- Negative-control environment: `b` is unconstrained (a misused merge
acknowledge, `c2_opposite_direction_hazard`). -/
def c2FreeB : Model := { c2Model with env := [(0, fun s => !bit s 3 && bit s 0 == bit s 2),
    (1, fun s => !bit s 3), (3, fun s => bit s 3 && !bit s 2)] }

/-! ## 5. bd_latch (one LUT6_2 pair) behind its controller

Signals: `e = 0` (the controller node), `en = 1` (the enable branch, a wire with
its own delay), `d0 = 2`, `d1 = 3`, `q0 = 4`, `q1 = 5`, `rdy = 6` (the sender's
private "data is out" event). LUT `bd_latch_u_L38` (bd_latch.v:38), O5 = q0,
O6 = q1, free pins root first `[q1, d1, q0, en, d0]`, feedback zero-delay.
Environment: data may move only while `e = 0` and before `rdy`; `e` rises
after `rdy` (**bundling, H_BUNDLE**: data before request, encoded causally:
under H_SETTLE the data change has settled in the LUT before `e`'s rise
arrives), falls after `rdy` is withdrawn. Power-up `d`, `q` arbitrary. -/

structure LatchAsm where
  /-- Rule H (DACK): the enable branch settles before the sender moves data or
  its request again. -/
  ruleH : Bool
  /-- Rule L: the latch outputs have followed `D` before the enable branch falls. -/
  ruleL : Bool

def latchModel (A : LatchAsm) : Model where
  n := 7
  gates := [.wire 1 0, .lut 4 bd_latch_u_L38 .O5 [5, 3, 4, 1, 2],
            .lut 5 bd_latch_u_L38 .O6 [5, 3, 4, 1, 2]]
  env := [(2, fun s => !bit s 0 && !bit s 6),
          (3, fun s => !bit s 0 && !bit s 6),
          (6, fun s => bit s 0 == bit s 6),
          (0, fun s => bit s 0 != bit s 6)]
  prio := (if A.ruleH then [(1, 2), (1, 3), (1, 6)] else []) ++
          (if A.ruleL then [(4, 1), (5, 1)] else [])
  inits := (List.range 16).map (· * 4)

/-! ## 6. bd_link (Muller stage): `bd_c2n` controller + one latch bit

W = 1 (the odd-bit LUT `bd_latch_u_L44`, bd_latch.v:44, free pins root first
`[q, en, d]`); the LUT6_2 pair is §5. (A W = 2 link, 1048 states, exhausted
6 GB of kernel memory: see notes and `Wip/Env.lean`.)
Signals: `req = 0` (req_in), `c = 1` (the node: req_out and ack_in, isochronic
with the controller), `ack = 2` (ack_out = c_next), `en = 3` (the enable
branch to the latch, a wire), `d = 4`, `q = 5`, `rdy = 6` (sender private),
`rst = 7` (held 0). Controller `bd_c2n_u` (bd_ce.v:49), free pins
`[rst, c, c_next, req_in]`. Sender: four-phase on `req`/`c`, data moves only
while `req = c = 0` (the hold window ends at ack-fall) and before `rdy`;
receiver: any four-phase partner on `c`/`ack`. Power-up `d`, `q` arbitrary. -/

structure LinkAsm where
  /-- Rule H (DACK): the enable branch settles before the sender, having seen
  ack fall, moves data or request again. -/
  ruleH : Bool
  /-- Rule L: the latch output follows `D` before the enable branch falls. -/
  ruleL : Bool
  /-- Isochronic enable branch: the enable branch settles before the receiver
  acknowledges (`c` reaches the latch before the round trip through the
  receiver returns). -/
  isoEn : Bool
  /-- Receiver bundling ("req_out leads data_out"): the latch output settles
  before the receiver acknowledges. Needed only for `linkData`. -/
  rxBundle : Bool

def linkModel (A : LinkAsm) : Model where
  n := 8
  gates := [.lut 1 bd_c2n_u .O [7, 1, 2, 0], .wire 3 1,
            .lut 5 bd_latch_u_L44 .O [5, 3, 4]]
  env := [(4, fun s => !bit s 6 && !bit s 0 && !bit s 1),
          (6, fun s => (!bit s 6 && !bit s 0 && !bit s 1) || (bit s 6 && bit s 0)),
          (0, fun s => (!bit s 0 && bit s 6 && !bit s 1) || (bit s 0 && bit s 1)),
          (2, fun s => bit s 2 != bit s 1)]
  prio := (if A.ruleH then [(3, 4), (3, 6)] else []) ++
          (if A.ruleL then [(5, 3)] else []) ++
          (if A.isoEn then [(3, 2)] else []) ++
          (if A.rxBundle then [(5, 2)] else [])
  inits := (List.range 4).map (· * 16)

/-- Data validity at the receiver: whenever the receiver may raise `ack`, the
latch holds the sender's bit and is not excited. -/
def linkData (M : Model) (s : Nat) : Bool :=
  !(bit (enMask M s) 2 && !bit s 2) || (bit s 5 == bit s 4 && !bit (excMask M s) 5)

def linkQ (M : Model) (s : Nat) : Bool := live M s && linkData M s

/-! ## 7. Results -/

/-! ### bd_c2 -/

theorem c2_cert : certify c2Model (live c2Model) (reachTree c2Model 100) = true := by
  decide +kernel

/-- **bd_c2 under the two-party four-phase (join) environment is speed-independent
and every MIC its LUT sees is function-hazard-free**; no deadlock. -/
theorem c2_sound : Sound c2Model (live c2Model) := certify_sound c2_cert

theorem c2_states : (reachTree c2Model 100).size = 10 := by decide +kernel

/-- The only MICs: both requests rising together (q = 0), both falling (q = 1).
Free pins `[rst, q, b, a]`. Both are dynamic hazard-free in LutAudit's sense. -/
theorem c2_mics :
    micsAt c2Model (reachTree c2Model 100) 0 =
      [([false, false, false, false], [false, false, true, true]),
       ([false, true, true, true], [false, true, false, false])] ∧
    classify bd_c2_u .O [false, false, false, false] [false, false, true, true] = .dHF ∧
    classify bd_c2_u .O [false, true, true, true] [false, true, false, false] = .dHF := by
  decide +kernel

/-- Negative control: with `b` unconstrained the checker finds a reachable
hazard (the opposite-direction MIC of `c2_opposite_direction_hazard`, and a
withdrawn excitation). -/
theorem c2_freeB_hazard :
    ∃ s, Reach c2FreeB s ∧ (1, post c2FreeB s 1) ∈ succs c2FreeB s ∧
      (!lutOK c2FreeB s 1 (.lut 2 bd_c2_u .O [3, 2, 1, 0]) 0 && !persistOK c2FreeB s 1) = true :=
  witness_sound (M := c2FreeB) (s0 := 8) (ts := [3, 1, 0]) (t := 1)
    (bad := fun s t => !lutOK c2FreeB s t (.lut 2 bd_c2_u .O [3, 2, 1, 0]) 0 && !persistOK c2FreeB s t)
    (by decide) (by decide +kernel)

theorem c2_freeB_not_sound : ¬ Sound c2FreeB (live c2FreeB) :=
  not_sound_of_witness (s0 := 8) (ts := [3, 1, 0]) (t := 1) (by decide) (by decide +kernel)

/-! ### bd_latch -/

theorem latch_cert : certify (latchModel ⟨true, true⟩) (live (latchModel ⟨true, true⟩))
    (reachTree (latchModel ⟨true, true⟩) 1000) = true := by
  decide +kernel

/-- **bd_latch pair, with rules H and L as the only timing assumptions, is
hazard-free and persistent**; no deadlock. -/
theorem latch_sound : Sound (latchModel ⟨true, true⟩) (live (latchModel ⟨true, true⟩)) :=
  certify_sound latch_cert

theorem latch_states : (reachTree (latchModel ⟨true, true⟩) 1000).size = 208 := by decide +kernel

/-- The MICs the pair's O5 (q0) sees: 16, all with `en = 0` before and after
(free pins `[q1, d1, q0, en, d0]`): data moving while closed, which is
`latch_closed_data_free`. The enable never takes part in a MIC. -/
theorem latch_mics :
    (micsAt (latchModel ⟨true, true⟩) (reachTree (latchModel ⟨true, true⟩) 1000) 1).length = 16 ∧
    (micsAt (latchModel ⟨true, true⟩) (reachTree (latchModel ⟨true, true⟩) 1000) 1).all
      (fun m => !m.1.getD 3 true && !m.2.getD 3 true) = true := by
  decide +kernel

/-- **Rule H is necessary**: without it the enable branch can still be falling
when the sender moves `d0`, a static function hazard on q0
(`latch_close_while_d_moves`). -/
theorem latch_needs_H :
    ∃ s, Reach (latchModel ⟨false, true⟩) s ∧
      (2, post (latchModel ⟨false, true⟩) s 2) ∈ succs (latchModel ⟨false, true⟩) s ∧
      (!lutOK (latchModel ⟨false, true⟩) s 2 (.lut 4 bd_latch_u_L38 .O5 [5, 3, 4, 1, 2]) 1 &&
        !stepOK (latchModel ⟨false, true⟩) s 2) = true :=
  witness_sound (M := latchModel ⟨false, true⟩) (s0 := 0) (ts := [6, 0, 1, 6, 0, 1]) (t := 2)
    (bad := fun s t => !lutOK (latchModel ⟨false, true⟩) s t (.lut 4 bd_latch_u_L38 .O5 [5, 3, 4, 1, 2]) 1 &&
      !stepOK (latchModel ⟨false, true⟩) s t)
    (by decide) (by decide +kernel)

/-- **Rule L is necessary**: without it the enable falls while q0 is still
following D: an excited LUT is disabled (non-persistence, `latch_close_while_q_settles`). -/
theorem latch_needs_L :
    ∃ s, Reach (latchModel ⟨true, false⟩) s ∧
      (1, post (latchModel ⟨true, false⟩) s 1) ∈ succs (latchModel ⟨true, false⟩) s ∧
      (!persistOK (latchModel ⟨true, false⟩) s 1) = true :=
  witness_sound (M := latchModel ⟨true, false⟩) (s0 := 4) (ts := [6, 0, 1, 6, 0]) (t := 1)
    (bad := fun s t => !persistOK (latchModel ⟨true, false⟩) s t) (by decide) (by decide +kernel)

/-- **H_SETTLE is necessary** (ablation): with pure unbounded mux-tree delays,
a data change made while the latch was closed may still be in flight when the
enable rises, a function hazard on q0 although every protocol rule holds.
This is the setup half of bundled data at LUT level. -/
theorem latch_needs_settle :
    ∃ s, Reach { latchModel ⟨true, true⟩ with settle := false } s ∧
      (1, post { latchModel ⟨true, true⟩ with settle := false } s 1) ∈
        succs { latchModel ⟨true, true⟩ with settle := false } s ∧
      (!lutOK { latchModel ⟨true, true⟩ with settle := false } s 1
        (.lut 4 bd_latch_u_L38 .O5 [5, 3, 4, 1, 2]) 1) = true :=
  witness_sound (M := { latchModel ⟨true, true⟩ with settle := false }) (s0 := 4) (ts := [2, 6, 0]) (t := 1)
    (bad := fun s t => !lutOK { latchModel ⟨true, true⟩ with settle := false } s t
      (.lut 4 bd_latch_u_L38 .O5 [5, 3, 4, 1, 2]) 1) (by decide) (by decide +kernel)

/-! ### bd_link -/

/-- One kernel run: certificate, state count, and the controller's MIC list
(the reachable set is computed once). -/
theorem link_cert : certify (linkModel ⟨true, true, true, false⟩)
      (live (linkModel ⟨true, true, true, false⟩))
      (reachTree (linkModel ⟨true, true, true, false⟩) 1000) = true ∧
    (reachTree (linkModel ⟨true, true, true, false⟩) 1000).size = 142 ∧
    micsAt (linkModel ⟨true, true, true, false⟩)
      (reachTree (linkModel ⟨true, true, true, false⟩) 1000) 0 =
      [([false, true, false, true], [false, true, true, false]),
       ([false, false, true, false], [false, false, false, true])] := by
  decide +kernel

/-- **bd_link (controller + latch) is hazard-free and persistent under rules H,
L and the isochronic enable branch**, with an arbitrary four-phase receiver;
no deadlock. -/
theorem link_sound : Sound (linkModel ⟨true, true, true, false⟩)
    (live (linkModel ⟨true, true, true, false⟩)) := certify_sound link_cert.1

/-- The controller LUT's MICs are exactly LutAudit's two (`link_mic_hazard_free`:
`req_in↓ ∥ c_next↑` with c = 1, `req_in↑ ∥ c_next↓` with c = 0), now derived
rather than argued; the hazardous `req_in↑ ∥ c_next↑` never occurs. -/
theorem link_ctl_mics :
    micsAt (linkModel ⟨true, true, true, false⟩)
      (reachTree (linkModel ⟨true, true, true, false⟩) 1000) 0 =
      [([false, true, false, true], [false, true, true, false]),
       ([false, false, true, false], [false, false, false, true])] := link_cert.2.2

theorem link_data_cert : certify (linkModel ⟨true, true, true, true⟩)
    (linkQ (linkModel ⟨true, true, true, true⟩))
    (reachTree (linkModel ⟨true, true, true, true⟩) 1000) = true := by
  decide +kernel

/-- With receiver bundling added, the receiver always acknowledges the sender's
bit (data validity), on top of hazard freedom. -/
theorem link_data_sound : Sound (linkModel ⟨true, true, true, true⟩)
    (linkQ (linkModel ⟨true, true, true, true⟩)) := certify_sound link_data_cert

theorem link_noL_cert : certify (linkModel ⟨true, false, true, true⟩)
    (linkQ (linkModel ⟨true, false, true, true⟩))
    (reachTree (linkModel ⟨true, false, true, true⟩) 1000) = true := by
  decide +kernel

/-- With a receiver that waits for the data (rxBundle), rule L is implied:
`c` falls only after `ack` rises, which waits for the latch. In a pipe the
receiver is the next controller, which does not wait for this latch, so rule
L stands there (`link_needs_L`). -/
theorem link_L_implied_by_rx : Sound (linkModel ⟨true, false, true, true⟩)
    (linkQ (linkModel ⟨true, false, true, true⟩)) := certify_sound link_noL_cert

/-- **Rule H is necessary**: the sender moves `d` while the enable branch is
still falling: function hazard on q (`latch_close_while_d_moves`). -/
theorem link_needs_H :
    ∃ s, Reach (linkModel ⟨false, true, true, false⟩) s ∧
      (4, post (linkModel ⟨false, true, true, false⟩) s 4) ∈ succs (linkModel ⟨false, true, true, false⟩) s ∧
      (!lutOK (linkModel ⟨false, true, true, false⟩) s 4 (.lut 5 bd_latch_u_L44 .O [5, 3, 4]) 2) = true :=
  witness_sound (M := linkModel ⟨false, true, true, false⟩) (s0 := 0) (ts := [6, 0, 1, 3, 2, 6, 0, 1, 3])
    (t := 4) (bad := fun s t => !lutOK (linkModel ⟨false, true, true, false⟩) s t
      (.lut 5 bd_latch_u_L44 .O [5, 3, 4]) 2) (by decide) (by decide +kernel)

/-- **Rule L is necessary** (receiver not waiting for data): the enable falls
while q is still following D; the latch LUT's excitation is withdrawn. -/
theorem link_needs_L :
    ∃ s, Reach (linkModel ⟨true, false, true, false⟩) s ∧
      (3, post (linkModel ⟨true, false, true, false⟩) s 3) ∈ succs (linkModel ⟨true, false, true, false⟩) s ∧
      (!persistOK (linkModel ⟨true, false, true, false⟩) s 3) = true :=
  witness_sound (M := linkModel ⟨true, false, true, false⟩) (s0 := 16) (ts := [6, 0, 1, 0, 3, 2, 1])
    (t := 3) (bad := fun s t => !persistOK (linkModel ⟨true, false, true, false⟩) s t)
    (by decide) (by decide +kernel)

/-- **The isochronic enable branch is necessary**: `c` can rise and fall again
before the enable branch follows; the enable wire's excitation is withdrawn (a
runt, or a token never written). -/
theorem link_needs_isoEn :
    ∃ s, Reach (linkModel ⟨true, true, false, false⟩) s ∧
      (1, post (linkModel ⟨true, true, false, false⟩) s 1) ∈ succs (linkModel ⟨true, true, false, false⟩) s ∧
      (!persistOK (linkModel ⟨true, true, false, false⟩) s 1) = true :=
  witness_sound (M := linkModel ⟨true, true, false, false⟩) (s0 := 0) (ts := [6, 0, 1, 0, 2])
    (t := 1) (bad := fun s t => !persistOK (linkModel ⟨true, true, false, false⟩) s t)
    (by decide) (by decide +kernel)

/-- "req_out LEADS data_out" (bd_link.v header), derived: without receiver
bundling the receiver may acknowledge while q has not yet followed D. -/
theorem link_req_leads_data :
    ∃ s, Reach (linkModel ⟨true, true, true, false⟩) s ∧
      (2, post (linkModel ⟨true, true, true, false⟩) s 2) ∈ succs (linkModel ⟨true, true, true, false⟩) s ∧
      (!linkData (linkModel ⟨true, true, true, false⟩) s) = true :=
  witness_sound (M := linkModel ⟨true, true, true, false⟩) (s0 := 16) (ts := [6, 0, 1, 3]) (t := 2)
    (bad := fun s _ => !linkData (linkModel ⟨true, true, true, false⟩) s) (by decide) (by decide +kernel)

end Formal.Core.Env
