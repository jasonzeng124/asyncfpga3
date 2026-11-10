import Formal.Timing.ChunkCM
import Formal.Timing.SpecSettleSym

/-!
# Formal.Cells.StartBound — bounding every collapsed gate's start time by a kernel computation (shard B, 2026-11-10)

**Problem, plainly.** Several theorems about THE target (C's `quiet_PS`, `settle_PS`; B's `target_reads_slice`)
carry the premise "every logic gate's collapsed start time `cStart p g pcs` is at most `H`" (or every route's
`sumMax` at most `M`). Evaluating `cStart` needs every pin's copy chain (up to 26 routing hops), and fetching a gate
from the chunked gate list costs a linear walk, too slow for ~100k chain hops in the kernel.

**Proved (generic).**
* `chainStart_le_m`, `cStart_le_m` (from C's `dmax_le_scale`, `start_le_scale`): with `m = ⌈(1+κ)·g⌉`, every `dmax`, gate start,
  chain start and collapsed start is at most `m` times its slow-max (g = 1, κ = 0) Nat value (`stN`, `chainN`,
  `cStartN'`).
* `chainN_walk`: the Nat chain start equals a walk sum along the copy map (`wsum`), so it needs only per-node
  values.
* `fOf_eq`: per-node values stored as chunked perfect binary trees (C's `BT`), checked chunk by chunk against the
  gate list (`FChunkFact`), give `stN (gate) + smax(arc0)` at every node, in O(log) kernel steps.

**Not shown here:** the instance (`Formal/Cells/StartBoundPS/`).
-/

namespace Formal.Cells.StartBound
open Formal.Target Formal.Timing.SpecSettle Formal.Timing.SpecChain Formal.Timing.SpecChainM Formal.Timing.ChunkCM

/-- A gate's start at g = 1, κ = 0: its largest slow-max arc delay. -/
def stN (g : Gate) : Nat := (g.arcs.map fun e => e.smax).foldr max 0

/-- A chain's start at g = 1, κ = 0. -/
def chainN : List Gate → Nat
  | [] => 0
  | c :: cs => stN c + (arc0 c).smax + chainN cs

/-- The collapsed start at g = 1, κ = 0. -/
def cStartN' (g : Gate) (pcs : List PinChain) : Nat :=
  stN g + ((List.range g.k).map fun i => chainN (pcs.getD i ⟨0, []⟩).chain + (g.arcs.getD i default).smax).sum

/-- The scale factor of the delay parameters (C's `SpecSettle.cScale`, file SpecSettleSym). -/
abbrev mOf (p : DelayPar) : Nat := Formal.Timing.SpecSettle.cScale p

theorem dmax_le_m {p : DelayPar} (hp : Sane p) (e : Arc) : dmax p e ≤ mOf p * e.smax :=
  Formal.Timing.SpecSettle.dmax_le_scale hp e

theorem start_le_m {p : DelayPar} (hp : Sane p) (g : Gate) : g.start p ≤ mOf p * stN g :=
  Formal.Timing.SpecSettle.start_le_scale hp g

theorem chainStart_le_m {p : DelayPar} (hp : Sane p) : ∀ cs : List Gate, chainStart p cs ≤ mOf p * chainN cs
  | [] => by simp [chainStart, chainN]
  | c :: cs => by
    have h1 := start_le_m hp c
    have h2 := dmax_le_m hp (arc0 c)
    have h3 := chainStart_le_m hp cs
    simp only [chainStart, chainN, Nat.mul_add]
    omega

theorem sum_le_m {k : Nat} {f g : Nat → Nat} {m : Nat} (h : ∀ i, f i ≤ m * g i) :
    ((List.range k).map f).sum ≤ m * ((List.range k).map g).sum := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
      List.sum_nil, Nat.add_zero, Nat.mul_add]
    have := h k
    omega

theorem cStart_le_m {p : DelayPar} (hp : Sane p) (g : Gate) (pcs : List PinChain) :
    cStart p g pcs ≤ mOf p * cStartN' g pcs := by
  unfold cStart cStartN'
  rw [Nat.mul_add]
  have h1 := start_le_m hp g
  have h2 := sum_le_m (k := g.k) (m := mOf p)
    (f := fun i => chainStart p (pcs.getD i ⟨0, []⟩).chain + dmax p (g.arcs.getD i default))
    (g := fun i => chainN (pcs.getD i ⟨0, []⟩).chain + (g.arcs.getD i default).smax)
    (fun i => by
      have := chainStart_le_m hp (pcs.getD i ⟨0, []⟩).chain
      have := dmax_le_m hp (g.arcs.getD i default)
      simp only [Nat.mul_add]; omega)
  omega

/-- A walk sum along the copy map, mirroring `chainGates`. -/
def wsum (cm : Nat → Option Nat) (F : Nat → Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | v, r + 1 => F v + (match cm v with | some y => wsum cm F y r | none => 0)

theorem chainN_walk (cm : Nat → Option Nat) (ga : Nat → Gate) :
    ∀ (v r : Nat), chainN (chainGates cm ga v r) = wsum cm (fun u => stN (ga u) + (arc0 (ga u)).smax) v r
  | _, 0 => by simp [chainGates, chainN, wsum]
  | v, r + 1 => by
    simp only [chainGates, chainN, wsum]
    cases cm v with
    | none => simp [chainN]
    | some y => simp only; rw [chainN_walk cm ga y r]

/-- The per-node value a tree leaf stores. -/
def fS (g : Gate) : Option Nat := some (stN g + (arc0 g).smax)

/-- What is checked per chunk for the value trees. -/
def FChunkFact (tf : List BT) (cs : List (List Gate)) (d c : Nat) : Prop :=
  (tf.getD c (.lf none)).perf d = true ∧
  (tf.getD c (.lf none)).toList = (cs.getD c []).map fS ++ List.replicate (2 ^ d - (cs.getD c []).length) none

/-- The per-node value read from the trees (0 where there is none). -/
def fOf (tf : List BT) (C d : Nat) (u : Nat) : Nat := ((tf.getD (u / C) (.lf none)).get d (u % C)).getD 0

theorem fOf_eq {tf : List BT} {cs : List (List Gate)} {C d : Nat} (hC : 0 < C) (hCd : C ≤ 2 ^ d)
    (hlen : tf.length = cs.length) (hf : ∀ c, c < cs.length → FChunkFact tf cs d c) (u : Nat) :
    fOf tf C d u = stN (gaOf cs C u) + (arc0 (gaOf cs C u)).smax := by
  unfold fOf gaOf
  by_cases hc : u / C < cs.length
  · obtain ⟨hp, ht⟩ := hf _ hc
    have hmod : u % C < C := Nat.mod_lt _ hC
    rw [BT.get_eq _ _ _ hp (by omega), ht, getD_map_rep]
    split
    · simp [fS]
    · rename_i hlt
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      have hd : (default : Gate).arcs = [] := rfl
      have ha : (default : Arc).smax = 0 := rfl
      simp [stN, arc0, hd, ha]
  · rw [List.getD_eq_getElem?_getD (l := tf), List.getElem?_eq_none (by omega),
      List.getD_eq_getElem?_getD (l := cs), List.getElem?_eq_none (by omega)]
    have hd : (default : Gate).arcs = [] := rfl
    have ha : (default : Arc).smax = 0 := rfl
    simp [BT.get, stN, arc0, hd, ha]

end Formal.Cells.StartBound
