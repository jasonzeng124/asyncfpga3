import Formal.Cells.StartBound
import Formal.Net.CViewPS.Base

/-!
# Formal.Cells.StartBoundPS.Defs — the per-chunk start-time check for THE target (shard B, 2026-11-10)

`boundN cm F g pv`: a logic gate's collapsed start at g = 1, κ = 0, with each pin's chain summed by `wsum` along
the copy map `cm` and per-node values `F`. `chunkStartOK`: every logic gate of one chunk has `boundN ≤ HB`.
-/

namespace Formal.Cells.StartBoundPS
open Formal.Target Formal.Timing.SpecChain Formal.Timing.SpecChainM Formal.Timing.ChunkCM Formal.Cells.StartBound
  Formal.Net.CViewPS

def boundN (cm : Nat → Option Nat) (F : Nat → Nat) (g : Gate) (pv : PinData) : Nat :=
  stN g + ((List.range g.k).map fun i =>
    wsum cm F (g.ins.getD i 0) (pv.getD i (0, 0)).2 + (g.arcs.getD i default).smax).sum

def chunkStartOK (cm : Nat → Option Nat) (F : Nat → Nat) (HB : Nat) (gs : List Gate) (vs : List PinData) : Bool :=
  (gs.zip vs).all fun e => !(keepPS e.1) || (cpIn e.1).isSome || decide (boundN cm F e.1 e.2 ≤ HB)

theorem cStartN'_eq (cm : Nat → Option Nat) (ga : Nat → Gate) (g : Gate) (pv : PinData) :
    cStartN' g (toPCs cm ga g pv) = boundN cm (fun u => stN (ga u) + (arc0 (ga u)).smax) g pv := by
  unfold cStartN' boundN
  congr 1
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [toPCs_getD cm ga g pv (List.mem_range.1 hi), chainN_walk]

end Formal.Cells.StartBoundPS
