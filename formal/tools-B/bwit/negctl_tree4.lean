import Formal.Cells.BWit4NDefs
open Formal.Cells Formal.Cells.BWit4 Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Cells.FiniteNetWit2 (Gf2 Gf4 celB)
open Formal.Cells.FiniteNetBoundT (treeOuts)
open Formal.Cells.AssumeGuaranteeEndsCap (d0)
def bump0 : List Nat → List Nat | a :: t => (a + 1) :: t | [] => []
-- control: the real checks on the three trees (ops 67, 88: N = 5; 143: N = 6)
#eval [67, 88, 143].map fun n => if h : n < NO then treeChk ⟨n, h⟩ else false
-- mutant 1: op 67's chunk C4 node with its first edge one tick late
#eval match treeOuts (opAt ⟨67, by decide⟩) with
  | some os => celB Gf4 (fun i : Fin 4 => (cdB (os.getD i.val d0)).ak) (bump0 (lstN (.tn ⟨67, by decide⟩ 0)))
  | none => true
-- mutant 2: op 67's top C2 read without the chunk node (leaf 3 in its place)
#eval match treeOuts (opAt ⟨67, by decide⟩) with
  | some os => celB Gf2 (fun i : Fin 2 => if i.val = 0 then (cdB (os.getD 3 d0)).ak else (cdB (os.getD 4 d0)).ak)
      (lstN (.tr ⟨67, by decide⟩))
  | none => true
-- mutant 3: op 143's top C2 with the two chunk inputs as C4 over leaves 0..3 (skipping leaves 4, 5)
#eval match treeOuts (opAt ⟨143, by decide⟩) with
  | some os => celB Gf4 (fun i : Fin 4 => (cdB (os.getD i.val d0)).ak) (lstN (.tr ⟨143, by decide⟩))
  | none => true
