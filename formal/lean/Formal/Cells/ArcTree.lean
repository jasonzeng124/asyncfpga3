import Formal.Cells.StartBound
import Formal.Cells.CornerSlice

/-!
# Formal.Cells.ArcTree — per-node routing arcs in chunk trees, and route sums as walks (shard B, 2026-11-10)

**Problem, plainly.** A certificate checked by `decide` on THE target's slice net evaluates every pin's `lo`/`hi`,
a sum over the pin's routing chain (up to 26 hops), each hop a gate fetched from the chunked gate list (a linear
walk) with ℚ ceilings. Can the same numbers be computed with tree lookups and Nat arithmetic, provably equal?

**Proved (generic).**
* `encA`/`decA`: an arc packed into one Nat (12 bits per field) and unpacked; `AChunkFact` (per chunk: the tree's
  leaves are the packed `arc0` of the chunk's gates, and every packing round-trips) gives `aOf_eq`: the tree
  lookup `aOf tf C d u` is `arc0` of the gate driving `u` (default arc outside the chunks).
* `sum_chain_walk`: a function summed over a chain's `arc0`s equals a walk sum along the copy map (`wsum`).

**Not shown here:** the instance (`Formal/Cells/ArcTreePS/`).
-/

namespace Formal.Cells.ArcTree
open Formal.Target Formal.Timing.SpecChain Formal.Timing.SpecChainM Formal.Timing.ChunkCM Formal.Cells.StartBound

def encA (a : Arc) : Nat := a.fmin + 4096 * (a.fmax + 4096 * (a.smin + 4096 * a.smax))

def decA (n : Nat) : Arc := ⟨n % 4096, n / 4096 % 4096, n / 4096 / 4096 % 4096, n / 4096 / 4096 / 4096⟩

/-- What is checked per chunk for the arc trees. -/
def AChunkFact (tf : List BT) (cs : List (List Gate)) (d c : Nat) : Prop :=
  (tf.getD c (.lf none)).perf d = true ∧
  (tf.getD c (.lf none)).toList =
    (cs.getD c []).map (fun g => some (encA (arc0 g))) ++ List.replicate (2 ^ d - (cs.getD c []).length) none ∧
  (cs.getD c []).all (fun g => decA (encA (arc0 g)) == arc0 g) = true

/-- The arc read from the trees. -/
def aOf (tf : List BT) (C d : Nat) (u : Nat) : Arc := decA (((tf.getD (u / C) (.lf none)).get d (u % C)).getD 0)

theorem aOf_eq {tf : List BT} {cs : List (List Gate)} {C d : Nat} (hC : 0 < C) (hCd : C ≤ 2 ^ d)
    (hlen : tf.length = cs.length) (hf : ∀ c, c < cs.length → AChunkFact tf cs d c) (u : Nat) :
    aOf tf C d u = arc0 (gaOf cs C u) := by
  unfold aOf gaOf
  have hd : arc0 (default : Gate) = default := rfl
  have h0 : decA 0 = default := rfl
  by_cases hc : u / C < cs.length
  · obtain ⟨hp, ht, hrt⟩ := hf _ hc
    have hmod : u % C < C := Nat.mod_lt _ hC
    rw [BT.get_eq _ _ _ hp (by omega), ht, getD_map_rep]
    split
    · rename_i hlt
      simp only [Option.getD_some]
      have := List.all_eq_true.1 hrt ((cs.getD (u / C) []).getD (u % C) default) (getD_mem_of_lt hlt)
      simpa using this
    · rename_i hlt
      rw [List.getD_eq_getElem?_getD (l := cs.getD (u / C) []), List.getElem?_eq_none (by omega)]
      exact h0.trans hd.symm
  · rw [List.getD_eq_getElem?_getD (l := tf), List.getElem?_eq_none (by omega),
      List.getD_eq_getElem?_getD (l := cs), List.getElem?_eq_none (by omega)]
    exact h0.trans hd.symm

theorem sum_chain_walk (cm : Nat → Option Nat) (ga : Nat → Gate) (f : Arc → Nat) :
    ∀ (v r : Nat), (((chainGates cm ga v r).map arc0).map f).sum = wsum cm (fun u => f (arc0 (ga u))) v r
  | _, 0 => by simp [chainGates, wsum]
  | v, r + 1 => by
    simp only [chainGates, wsum, List.map_cons, List.sum_cons]
    cases cm v with
    | none => simp
    | some y => simp only; rw [sum_chain_walk cm ga f y r]

end Formal.Cells.ArcTree
