import Formal.Cells.BWit3NDefs
open Formal.Cells Formal.Cells.BWit3 Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Cells.FiniteNetBoundA (qF r0F gF)
open Formal.Cells.BWit2 (maB)
def o : Fin NO := ⟨171, by decide⟩
#eval (ameC (opAt o)).isSome
#eval tabA o
#eval (lstN (.aq o)).take 6
-- control: the real check
#eval arbChk o
-- mutant 1: winner table with entry 0 flipped
def flip0 : List Bool → List Bool | b :: t => (!b) :: t | [] => []
#eval match ameC (opAt o) with
  | some (_, _, z) => (maB false (lstN (.ag o false)) (cdB z).ak (flip0 (tabA o)) (lstN (.aa o false)),
                       maB true (lstN (.ag o true)) (cdB z).ak (flip0 (tabA o)) (lstN (.aa o true)))
  | none => (true, true)
-- mutant 2: q's first edge one tick late
def bump0 : List Nat → List Nat | a :: t => (a + 1) :: t | [] => []
#eval match ameC (opAt o) with
  | some (x, y, z) => combB qF [(cdB x).rq, (cdB y).rq, lstN (.aq o), (cdB z).ak] (bump0 (lstN (.aq o)))
  | none => true
-- mutant 3: g1 checked against g2's LUT
#eval match ameC (opAt o) with
  | some (x, y, _) => combB (gF true) [(cdB x).rq, (cdB y).rq, lstN (.aq o)] (lstN (.ag o false))
  | none => true
