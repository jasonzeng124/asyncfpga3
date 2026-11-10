import Formal.Cells.SliceNet
import Formal.Net.CViewPS.Base

/-!
# Formal.Cells.SliceNetPS.Defs — what the per-chunk checks of THE target's slice net compute (shard B, 2026-11-10)

`constOf`: constant nodes (per chunk: offset, value); `constChunkOK` checks one chunk's list against its gates. `keepL`: a gate's kept pins (not dead by `deadB`, source not a
listed constant). `cstL`: the others' constants (dead pins: none). `chunkSelOK`: on one chunk of THE target's gates
and pin data, every logic gate's kept pin sources are distinct and each kept pin's own arc has fmin ≥ 1 ps. Generated data: `Data.lean` (`cl`), per-chunk
theorems `S000`..`S074` (`decide +kernel`), `Chunks.lean`.
-/

namespace Formal.Cells.SliceNetPS
open Formal.Target Formal.Timing.SpecChainM Formal.Timing.ChunkCM Formal.Cells.SliceReads Formal.Net.CViewPS

/-- Constant nodes stored per chunk (offset in chunk, value); `constOf cl s` looks node `s` up. -/
def constOf (cl : List (List (Nat × Bool))) (s : Nat) : Option Bool :=
  ((cl.getD (s / 2500) []).find? fun e => e.1 == s % 2500).map Prod.snd

/-- Per chunk: every listed constant is, in the chunk's gate list, a kept non-copy k = 0 gate with that value. -/
def constChunkOK (gs : List Gate) (l : List (Nat × Bool)) : Bool :=
  l.all fun e => decide (e.1 < gs.length) && keepPS (gs.getD e.1 default) && (cpIn (gs.getD e.1 default)).isNone &&
    (gs.getD e.1 default).k == 0 && (gs.getD e.1 default).init.testBit 0 == e.2

/-- The source of pin `i` in the pin data. -/
def srcD (pv : PinData) (i : Nat) : Nat := (pv.getD i (0, 0)).1

def keepL (t : Nat → Option Bool) (g : Gate) (pv : PinData) : List Nat :=
  (List.range g.k).filter fun i => !deadB g i && (t (srcD pv i)).isNone

def cstL (t : Nat → Option Bool) (g : Gate) (pv : PinData) (i : Nat) : Option Bool :=
  if deadB g i then none else t (srcD pv i)

def chunkSelOK (t : Nat → Option Bool) (gs : List Gate) (vs : List PinData) : Bool :=
  (gs.zip vs).all fun e => !(keepPS e.1) || (cpIn e.1).isSome ||
    (decide (((keepL t e.1 e.2).map (srcD e.2)).Nodup) &&
      (keepL t e.1 e.2).all fun i => decide (1 ≤ (e.1.arcs.getD i default).fmin))

end Formal.Cells.SliceNetPS
