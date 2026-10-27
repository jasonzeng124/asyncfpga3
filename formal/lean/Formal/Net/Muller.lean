import Formal.Net.CoreLut
import Formal.Core.LutCells

/-!
# Track 8, probe 8c: the `bd_pipe` control chain at gate level, speed-independence

Probe 8c asks for composition at GATE level: the project's real C-element
(`bd_c2n` of `cells/rtl/bd_ce.v`, one LUT6 whose output feeds its own pin I2,
INIT `0x00B200B200B200B2`, evaluated with shard A's Core `Lut.eval`, i.e.
`Formal.Net.CoreLut.evalL`; probe 11e moved it off shard B's Prelim `lutB`,
equal by `Formal.Net.CoreLutPrelim.lutB_eq_evalL`) connected into the
control chain the cells really form.

## The chain (from `cells/rtl/bd_link.v`, default build, no `BD_LINK_DC`)

`bd_pipe` (N stages) chains `bd_link`s: `r[0]=req_in`, `a[N]=ack_out`, and
stage `k` is

    bd_link_ctl:  c_k = bd_c2n(a = r[k], b = a[k+1], rst)  = C(r[k], ~a[k+1])
    rdly       :  r[k+1] = bd_delay(c_k)   (SDELAY=1 internally: one LUT1, INIT 2'h2)
    uack       :  a[k]   = bd_delay(c_k)   (DACK=0: N=0 bypass, a wire)

This is the classic Muller pipeline: `c_k = C(c_{k-1}, ~c_{k+1})` through
buffers/wires. The net `c_k` forks to four loads: its own pin I2 (feedback),
the LUT1 `b_k` (req to stage k+1, or `req_out`), the wire `w_k` (ack to
stage k-1's pin I1, or `ack_in` to the source), and the latch enable (data
path, not modelled here).

## Model: asynchronous gate-level transition system (finite-state)

The trace-level alternative (every LUT and wire a `BoundedDelay` relation of
`Formal.Net.Prelim`, chain of n stages, four-phase protocol for all traces) was
judged too heavy for the time box; see `formal/notes/C-8c-muller.md`. This file
does the finite-state, speed-independent level instead:

* State: one bit per NODE (bitmask `Nat`). Nodes, for an `n`-stage chain:
  `0 = src` (environment req, four-phase active source),
  `1 = snk` (environment ack, passive sink: ack follows req),
  and per stage `k`: `c k = 2+4k` (the `bd_c2n` LUT output),
  `b k = 3+4k` (the LUT1 of `rdly`, which also carries the req wire),
  `w k = 4+4k` (the ack wire from `c_k` to its reader),
  `f k = 5+4k` (the feedback wire from O back to pin I2).
* Every node is a gate (LUT) or a wire with an UNBOUNDED, unknown, positive
  delay: in any state, ANY excited node may fire (flip to its next value),
  one at a time (interleaving). This is speed-independent / delay-insensitive
  semantics: no assumption at all on gate or wire delays. Each node's next
  value is the real LUT applied to the bits at its pins (`evalL INIT_bd_c2n` for
  `c`, `evalL 2` for the LUT1).
* `Mode`: how the feedback wire is treated.
  - `free`: feedback wire is an ordinary wire with arbitrary delay. EXPECTED
    to fail, and it does (`free_hazard_n1`, `free_hazard_n2`): this is the
    C-element's timing condition, seen as a hazard.
  - `iso`: the feedback wire is isochronic with the LUT (pin I2 reads O
    directly; node `f` is inert). This is the textbook SI assumption.
  - `rt`: the feedback wire is a free wire, plus ONE relative-timing
    hypothesis **H_FB_BEFORE_INPUT**: a node that drives an input pin of `c_k`
    does not fire while `c_k`'s feedback wire is still in flight
    (`f_k ≠ c_k`). This is the discrete form of shard B's
    `H_ENV_LATENCY` (`Formal/Cells/CElemTiming.lean`, `c2_four_phase`):
    the inputs of the loop must not move until the loop has captured its own
    new value. On the chain, every input change of `c_k` is CAUSED by `c_k`'s
    own transition through at least one other LUT, so it reduces to
    `dfb_max < min loop path` (see the notes).

## Properties checked, every reachable state, every transition

* `hazardFree`: (semi-modularity / output persistence) if node `x` is excited
  and a different node `y` fires, `x` is still excited. A violation is a gate
  whose excitation is withdrawn before it fired: a glitch on a LUT, a runt on a
  wire. Applied to ALL nodes, environment included.
* `followOk`: for each pair `(X, Y)` of `pairs n`, `X` fires only when
  `X = Y` and `Y` fires only when `Y ≠ X`. For `(req, ack)` pairs this is
  exactly the four-phase protocol of `Formal/Net/Handshake.lean`
  (`SendStep` / `RecvStep`); for `(c_{k-1}, c_k)` it is token order
  (`follow_count`: `#c_k ≤ #c_{k-1} ≤ #c_k + 1` along every execution).

## Method and trust

`check mode n` is a Boolean function that runs a BFS (computing a candidate
reachable set `L` and its bitmap) and then checks, for every `s ∈ L` and
every enabled transition, that the successor is in the bitmap, the hazard
condition and the pair conditions. `check_sound` proves (no computation)
that `check mode n = true` implies the properties on every reachable state.
`check mode n = true` for concrete `mode, n` is closed by `decide +kernel`
(kernel reduction; no native code, no extra axiom). The BFS itself needs
no proof: it is only a certificate generator, and the closure check is what
the soundness proof uses.
-/

namespace Formal.Net.Muller
open Formal.Net.CoreLut

/-! ## Nodes -/

def src : Nat := 0
def snk : Nat := 1
def c (k : Nat) : Nat := 2 + 4 * k
def b (k : Nat) : Nat := 3 + 4 * k
def w (k : Nat) : Nat := 4 + 4 * k
def f (k : Nat) : Nat := 5 + 4 * k

/-- Number of nodes of an `n`-stage chain. -/
def numNodes (n : Nat) : Nat := 2 + 4 * n

inductive Mode where
  | free | iso | rt
  deriving DecidableEq, Repr

def get (s i : Nat) : Bool := s.testBit i

/-- The `bd_c2n` INIT, as shard A's `Formal.Core.LutCells` extracts it from
`cells/rtl/bd_ce.v` (= shard B's `CElemFn.INIT_c2n` and the yosys netlist's:
`Formal.Gen.ProofsCE.bd_c2n_lut`, `ce_inits_lutcells`). -/
def INIT_bd_c2n : Nat := Formal.Core.LutCells.bd_c2n_u.init

theorem INIT_bd_c2n_val : INIT_bd_c2n = 0x00B200B200B200B2 := rfl

/-- The LUT1 of `bd_delay` (`INIT 2'h2`): a buffer. -/
def INIT_buf : Nat := 2

/-- Pin `I0` (req side) of stage `k`'s C-element. -/
def pinA (s k : Nat) : Bool := if k = 0 then get s src else get s (b (k - 1))
/-- Pin `I1` (ack side, bubbled) of stage `k`'s C-element. -/
def pinB (n s k : Nat) : Bool := if k + 1 = n then get s snk else get s (w (k + 1))
/-- Pin `I2` (feedback) of stage `k`'s C-element. -/
def pinQ (m : Mode) (s k : Nat) : Bool := if m = .iso then get s (c k) else get s (f k)

/-- Next value of node `i`: the gate's function of the values at its pins
(for a wire: its driver). `rst` is held at 0 (after reset, all nodes 0). -/
def nextVal (m : Mode) (n s i : Nat) : Bool :=
  if i = src then !get s (w 0)
  else if i = snk then get s (b (n - 1))
  else
    let k := (i - 2) / 4
    match (i - 2) % 4 with
    | 0 => evalL INIT_bd_c2n [pinA s k, pinB n s k, pinQ m s k, false, false, false]
    | 1 => evalL INIT_buf [get s (c k)]
    | 2 => get s (c k)
    | _ => if m = .iso then get s i else get s (c k)

def excited (m : Mode) (n s i : Nat) : Bool := nextVal m n s i != get s i

/-- Stage whose C-element reads node `i` on pin I0 or I1 (if any). -/
def readerStage (n i : Nat) : Option Nat :=
  if i = src then some 0
  else if i = snk then some (n - 1)
  else if i < 2 then none
  else
    let k := (i - 2) / 4
    match (i - 2) % 4 with
    | 1 => if k + 1 < n then some (k + 1) else none
    | 2 => if 1 ≤ k then some (k - 1) else none
    | _ => none

/-- **H_FB_BEFORE_INPUT** (mode `rt` only): a driver of an input pin of `c_k`
may fire only when `c_k`'s feedback wire has caught up (`f_k = c_k`). -/
def allowed (m : Mode) (n s i : Nat) : Bool :=
  match m with
  | .rt => match readerStage n i with
    | some k => get s (f k) == get s (c k)
    | none => true
  | _ => true

def fire (s i : Nat) : Nat := s ^^^ 2 ^ i

/-- Node `i` may fire in state `s`. -/
def enabled (m : Mode) (n s i : Nat) : Bool :=
  decide (i < numNodes n) && excited m n s i && allowed m n s i

/-- One transition: an enabled node fires. -/
def Step (m : Mode) (n s s' : Nat) : Prop := ∃ i, enabled m n s i = true ∧ s' = fire s i

/-- Reachable from reset (`rst` pulse leaves every node at 0: `bd_c2n` is a
clearing cell, `c2n_rst_forced` of shard B's `CElemFn`, and the buffers/wires follow). -/
inductive Reach (m : Mode) (n : Nat) : Nat → Prop
  | init : Reach m n 0
  | step {s s'} : Reach m n s → Step m n s s' → Reach m n s'

/-! ## The properties -/

/-- Semi-modularity: firing `y` never disables a different excited `x`. -/
def HazardFree (m : Mode) (n s : Nat) : Prop :=
  ∀ x y, x < numNodes n → x ≠ y → enabled m n s y = true →
    excited m n s x = true → excited m n (fire s y) x = true

/-- `(X, Y)`: `X` moves only when `X = Y`, `Y` only when `Y ≠ X`. -/
def pairs (n : Nat) : List (Nat × Nat) :=
  [(src, c 0), (src, w 0), (c (n - 1), snk), (b (n - 1), snk)] ++
  (List.range n).flatMap (fun k => [(c k, b k), (c k, w k)]) ++
  ((List.range n).filter (1 ≤ ·)).flatMap
    (fun k => [(c (k - 1), c k), (b (k - 1), c k), (b (k - 1), w k)])

def pairOk (s y : Nat) (p : Nat × Nat) : Bool :=
  (y != p.1 || get s p.1 == get s p.2) && (y != p.2 || get s p.2 != get s p.1)

def FollowOk (m : Mode) (n s : Nat) : Prop :=
  ∀ y, enabled m n s y = true → ∀ p ∈ pairs n, pairOk s y p = true

/-! ## The checker -/

def nodes (n : Nat) : List Nat := List.range (numNodes n)

/-- Bitmap of a list of states. -/
def bitmap : List Nat → Nat
  | [] => 0
  | a :: l => 2 ^ a ||| bitmap l

def mem (B s : Nat) : Bool := B.testBit s

def succs (m : Mode) (n s : Nat) : List Nat :=
  ((nodes n).filter (enabled m n s)).map (fire s)

/-- BFS with fuel: `(visited list, visited bitmap, frontier)`. Certificate
generator only; nothing is proved about it. -/
def bfs (m : Mode) (n : Nat) : Nat → List Nat → Nat → List Nat → List Nat
  | 0, vis, _, _ => vis
  | _ + 1, vis, _, [] => vis
  | fuel + 1, vis, B, fr =>
    let (vis', B', fr') := fr.foldl (fun (acc : List Nat × Nat × List Nat) s =>
      (succs m n s).foldl (fun (acc : List Nat × Nat × List Nat) t =>
        if mem acc.2.1 t then acc else (t :: acc.1, acc.2.1 ||| 2 ^ t, t :: acc.2.2)) acc)
      (vis, B, [])
    bfs m n fuel vis' B' fr'

def reachList (m : Mode) (n : Nat) : List Nat := bfs m n 100000 [0] 1 [0]

/-- The per-state check, against a candidate invariant `inv`: every enabled
successor is in `inv`, no hazard, every pair condition. -/
def stateOk (m : Mode) (n : Nat) (inv : Nat → Bool) (s : Nat) : Bool :=
  (nodes n).all fun y =>
    !enabled m n s y ||
      (inv (fire s y) &&
       (nodes n).all (fun x => x == y || !excited m n s x || excited m n (fire s y) x) &&
       (pairs n).all (pairOk s y))

/-! ## Soundness of the checker -/

theorem mem_nodes {n x : Nat} (h : x < numNodes n) : x ∈ nodes n := List.mem_range.mpr h

theorem enabled_lt {m n s y} (h : enabled m n s y = true) : y < numNodes n := by
  simp only [enabled, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1.1

theorem enabled_exc {m n s y} (h : enabled m n s y = true) : excited m n s y = true := by
  simp only [enabled, Bool.and_eq_true] at h; exact h.1.2

theorem stateOk_spec {m n inv s} (h : stateOk m n inv s = true) {y}
    (hy : enabled m n s y = true) :
    inv (fire s y) = true ∧
    (∀ x, x < numNodes n → x ≠ y → excited m n s x = true → excited m n (fire s y) x = true) ∧
    (∀ p ∈ pairs n, pairOk s y p = true) := by
  simp only [stateOk, List.all_eq_true] at h
  have h1 := h y (mem_nodes (enabled_lt hy))
  simp only [hy, Bool.not_true, Bool.false_or, Bool.and_eq_true, List.all_eq_true] at h1
  obtain ⟨⟨hm, hx⟩, hp⟩ := h1
  refine ⟨hm, ?_, hp⟩
  intro x hxn hne he
  have := hx x (mem_nodes hxn)
  simp only [Bool.or_eq_true, beq_iff_eq, hne, false_or, he, Bool.not_true] at this
  simpa using this

/-- Everything the checker certifies, as one invariant. -/
def Good (m : Mode) (n s : Nat) : Prop := HazardFree m n s ∧ FollowOk m n s

/-- Generic soundness: an inductive invariant `inv` containing reset, every
state of which passes `stateOk`, contains every reachable state, and every
reachable state is `Good`. -/
theorem inv_sound {m n} {inv : Nat → Bool} (h0 : inv 0 = true)
    (hall : ∀ s, inv s = true → stateOk m n inv s = true) :
    ∀ s, Reach m n s → inv s = true ∧ Good m n s := by
  have hinv : ∀ s, Reach m n s → inv s = true := by
    intro s hs
    induction hs with
    | init => exact h0
    | step _ hst ih =>
      obtain ⟨y, hy, rfl⟩ := hst
      exact (stateOk_spec (hall _ ih) hy).1
  intro s hs
  have hL := hinv s hs
  refine ⟨hL, ?_, ?_⟩
  · intro x y hx hne hy he
    exact (stateOk_spec (hall _ hL) hy).2.1 x hx hne he
  · intro y hy p hp
    exact (stateOk_spec (hall _ hL) hy).2.2 p hp

/-! ### Checker 1: in-kernel BFS + bitmap (fine up to ~1000 states) -/

theorem testBit_bitmap (L : List Nat) (s : Nat) : mem (bitmap L) s = true → s ∈ L := by
  induction L with
  | nil => simp [mem, bitmap]
  | cons a l ih =>
    intro h
    simp only [mem, bitmap, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true,
      decide_eq_true_eq] at h
    rcases h with h | h
    · exact h ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

def checkWith (m : Mode) (n : Nat) (L : List Nat) : Bool :=
  let B := bitmap L
  mem B 0 && L.all (stateOk m n (mem B))

def check (m : Mode) (n : Nat) : Bool := checkWith m n (reachList m n)

theorem check_sound {m n} (h : check m n = true) : ∀ s, Reach m n s → Good m n s := by
  simp only [check, checkWith, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨h0, hall⟩ := h
  exact fun s hs => (inv_sound h0 (fun s hs => hall s (testBit_bitmap _ s hs)) s hs).2

/-! ### Checker 2: a literal certificate in hash buckets, checked in chunks

For large instances the in-kernel BFS runs out of memory, so the reachable
set is supplied as a literal (`Wip/C8c/MullerCert.lean`, printed by
`#eval` from `reachList`; its correctness is NOT assumed, only checked).
`cert` is a list of `K` packed buckets; bucket `j` packs states with
`s % K = j` as base-`2^19` digits `s+1`. Membership looks only in bucket
`s % K`, so a state that is a member is always in the bucket that is
iterated for it, which is all the soundness proof needs. -/

def digit : Nat := 2 ^ 19

def unpack : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, P => if P = 0 then [] else (P % digit - 1) :: unpack fuel (P / digit)

def bucket (cert : List Nat) (j : Nat) : List Nat := unpack 4096 (cert.getD j 0)

def memC (cert : List Nat) (K s : Nat) : Bool := (bucket cert (s % K)).contains s

def bucketOk (m : Mode) (n : Nat) (cert : List Nat) (K j : Nat) : Bool :=
  (bucket cert j).all (stateOk m n (memC cert K))

/-- One chunk of buckets `[lo, lo + len)`. -/
def chunkOk (m : Mode) (n : Nat) (cert : List Nat) (K lo len : Nat) : Bool :=
  (List.range' lo len).all (bucketOk m n cert K)

theorem chunkOk_spec {m n cert K lo len} (h : chunkOk m n cert K lo len = true) :
    ∀ j, lo ≤ j → j < lo + len → bucketOk m n cert K j = true := by
  intro j h1 h2
  simp only [chunkOk, List.all_eq_true] at h
  exact h j (List.mem_range'_1.mpr ⟨h1, h2⟩)

theorem cert_sound {m n cert K} (hK : 0 < K) (h0 : memC cert K 0 = true)
    (hb : ∀ j, j < K → bucketOk m n cert K j = true) :
    ∀ s, Reach m n s → Good m n s := by
  refine fun s hs => (inv_sound h0 (fun s hs => ?_) s hs).2
  have hj := hb (s % K) (Nat.mod_lt _ hK)
  simp only [bucketOk, List.all_eq_true] at hj
  simp only [memC, List.contains_iff_mem] at hs
  exact hj s hs

end Formal.Net.Muller
