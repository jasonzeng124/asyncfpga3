import Formal.Net.CViewPS.RIslData
import Formal.Net.CViewPS.BoundaryReset
import Formal.Timing.Island

/-! Shard C: the per-entry check of the reset island (used by RIslChk*.lean and RIslPS.lean).
Membership, value, forcing pins and rank of a node are read from the search tree `rIsl`; the
reset node `rstPS` is the only root, with value `true`. -/

namespace Formal.Net.CViewPS
open Formal.Target Formal.Target.DecodedPS Formal.Timing.SpecSettle Formal.Timing.SpecChain
  Formal.Timing.SpecChainM Formal.Timing.ChunkCM Formal.Timing.Huffman Formal.Timing.SpecLoop
  Formal.Timing.Island

/-- Look a node up in a search tree. -/
def RTree.find : RTree → Nat → Option (Nat × Bool × List Nat × Nat)
  | .blk es, w => es.find? fun e => e.1 == w
  | .br k l r, w => if Nat.blt w k then l.find w else r.find w

/-- Every entry of a tree passes `f`. -/
def RTree.all (f : Nat × Bool × List Nat × Nat → Bool) : RTree → Bool
  | .blk es => es.all f
  | .br _ l r => l.all f && r.all f

theorem RTree.find_all {f : Nat × Bool × List Nat × Nat → Bool} :
    ∀ (t : RTree) (w : Nat) (e : Nat × Bool × List Nat × Nat), t.find w = some e → t.all f = true →
      e.1 = w ∧ f e = true
  | .blk es, w, e, h, ha => by
    simp only [RTree.find] at h
    have h1 := List.find?_some h
    have h2 := List.mem_of_find?_eq_some h
    simp only [RTree.all, List.all_eq_true] at ha
    exact ⟨by simpa using h1, ha e h2⟩
  | .br k l r, w, e, h, ha => by
    simp only [RTree.all, Bool.and_eq_true] at ha
    simp only [RTree.find] at h
    split at h
    · exact RTree.find_all l w e h ha.1
    · exact RTree.find_all r w e h ha.2

def lookR (w : Nat) : Option (Nat × Bool × List Nat × Nat) := rIsl.find w
/-- Member of the reset island. -/
def memR (w : Nat) : Bool := (lookR w).isSome
/-- Value during reset: `true` for the reset node, the listed value for a member. -/
def valR (w : Nat) : Bool := if w == rstPS then true else ((lookR w).map fun e => e.2.1).getD false
/-- Forcing pins of a member. -/
def psR (w : Nat) : List Nat := ((lookR w).map fun e => e.2.2.1).getD []
/-- Rank of a member (`ρ ≤ 14`). -/
def rhoR (w : Nat) : Nat := ((lookR w).map fun e => e.2.2.2).getD 0

def rEntryOK (e : Nat × Bool × List Nat × Nat) : Bool :=
  logicB e.1 && (e.1 != rstPS) && decide (e.2.2.2 ≤ 14) &&
  (e.2.2.1.all fun j => decide (j < (gAt cs 2500 e.1).k) &&
    ((srcPS e.1 j == rstPS) || (memR (srcPS e.1 j) && decide (rhoR (srcPS e.1 j) < e.2.2.2)))) &&
  ForcesP (gAt cs 2500 e.1).k (gAt cs 2500 e.1).init (asgOf srcPS valR e.1 e.2.2.1) e.2.1

end Formal.Net.CViewPS
