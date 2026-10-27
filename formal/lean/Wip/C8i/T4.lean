import Formal.Net.GcdHwSeg
open Formal.Net.GcdHw Formal.Net.GcdHw.Gcd
def absd (a b : Nat) : Nat :=
  Ops.select (Ops.cmpi .sgt 32 (Ops.subi 32 a b) 4294967295) (Ops.subi 32 a b)
    (Ops.subi 32 0 (Ops.subi 32 a b))
def gSc (x : Nat) : Nat :=
  Ops.ori 1 (Ops.cmpi .ne 1 (Ops.andi 1 (Ops.trunci 1 x) 1) 0) (Ops.cmpi .slt 32 x 1)
example (x m k : Nat) : sig17.map (E.eval [x, m, Ops.cmpi .eq 32 x 0, k]) =
    [absd x m, k, x, m, gSc (absd x m), Ops.shrsi 32 (absd x m) 1] := by
  simp only [sig17, List.map, E.eval, BOp.ev, UOp.ev, List.getD, List.getElem?_cons_succ,
    List.getElem?_cons_zero, Option.getD_some, absd, gSc]
