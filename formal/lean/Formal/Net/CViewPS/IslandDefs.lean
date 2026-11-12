import Formal.Net.CViewPS.IslandData

/-! Shard C: the checks of the idle island (used by IslandChk*.lean and IslandPS.lean). -/

namespace Formal.Net.CViewPS
open Formal.Target Formal.Target.DecodedPS Formal.Timing.SpecSettle Formal.Timing.SpecChain
  Formal.Timing.SpecChainM Formal.Timing.ChunkCM Formal.Timing.Huffman Formal.Timing.SpecLoop
  Formal.Timing.Island

def memI (w : Nat) : Bool := islandList.any fun e => e.1 == w
def envI (e : Nat) : Bool := e == 186985 || e == 104477
def psI (w : Nat) : List Nat := ((islandList.find? fun e => e.1 == w).map fun e => e.2.2).getD []
def valI : Nat → Bool := fun _ => false
def storI (w : Nat) : Bool := isStor (gAt cs 2500 w) (pvAt vss 2500 w)

def entryOK (e : Nat × Bool × List Nat) : Bool :=
  logicB e.1 && (e.2.1 == false) && (psI e.1 == e.2.2) &&
  (e.2.2.all fun j => decide (j < (gAt cs 2500 e.1).k) && (memI (srcPS e.1 j) || envI (srcPS e.1 j))) &&
  ForcesP (gAt cs 2500 e.1).k (gAt cs 2500 e.1).init (asgOf srcPS valI e.1 e.2.2) false &&
  (if storI e.1 then resetList.any (fun r => r.1 == e.1 && r.2.2 == false)
   else (decide ((rkPS e.1).getD 0 ≤ 85)) && e.2.2.all fun j =>
     !(memI (srcPS e.1 j) && !storI (srcPS e.1 j)) || decide ((rkPS (srcPS e.1 j)).getD 0 < (rkPS e.1).getD 0))

end Formal.Net.CViewPS
