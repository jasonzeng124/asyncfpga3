import Wip.C9c.Local

namespace Formal.Net.MullerAll
open Formal.Net.Muller

/-! ## Five-position windows for the loop (guard) certificate of probe 8g -/

def wv (ws : List Nat) (i : Nat) : Nat := ws.getD i 48
def wexc (ws : List Nat) (off t : Nat) : Bool := lexc .rt (wv ws (off - 1)) (wv ws off) (wv ws (off + 1)) t
def wen (ws : List Nat) (off t : Nat) : Bool := lenabled .rt (wv ws (off - 1)) (wv ws off) (wv ws (off + 1)) t
def wfire (ws : List Nat) (off t : Nat) : List Nat := ws.set off (flip (wv ws off) t)

def ldone (ws : List Nat) (z : Nat × Nat × Bool) : Bool := (bt (wv ws z.1) z.2.1 == bt (wv ws 2) 0) == z.2.2

def llevel (ws : List Nat) : List (Nat × Nat × Bool) → Nat
  | [] => 0
  | z :: zs => if ldone ws z then llevel ws zs + 1 else 0

def linfl (ws : List Nat) : Bool := bt (wv ws 2) 3 != bt (wv ws 2) 0

def lguardOk (ws : List Nat) (zs : List (Nat × Nat × Bool)) (offs : List Nat) : Bool :=
  (!wen ws 2 0 || (zs.all (fun z => !wexc ws z.1 z.2.1) && llevel (wfire ws 2 0) zs == 0)) &&
  (!linfl ws ||
    ((offs.all fun off => types.all fun t => !valid (wv ws off) t || !wen ws off t ||
        !linfl (wfire ws off t) || llevel (wfire ws off t) zs == llevel ws zs ||
        (llevel (wfire ws off t) zs == llevel ws zs + 1 &&
          (zs[llevel ws zs]?).map (fun z => (z.1, z.2.1)) == some (off, t))) &&
     (List.range zs.length).all fun j => match zs[j]? with
        | some z => !wexc ws z.1 z.2.1 || decide (j ≤ llevel ws zs)
        | none => true))

def predL (ws : List Nat) : List (Nat × Nat × Bool) :=
  if isSrc (wv ws 1) then [(2, 2, true), (1, 0, false)] else [(2, 2, true), (1, 0, false), (1, 1, false)]
def succL (ws : List Nat) : List (Nat × Nat × Bool) :=
  if isSnk (wv ws 3) then [(2, 1, true), (3, 0, true)] else [(2, 1, true), (3, 0, true), (3, 2, true)]

/-- Pred-side loops: window `[Q-2, Q-1, Q, Q+1, -]`, the moving nodes at `Q-1, Q`. -/
def chkPredW (v2 : Nat) : Bool :=
  dom.all fun v0 => (adj .rt v0).all fun v1 => !(adj .rt v1).contains v2 ||
    (adj .rt v2).all fun v3 =>
      lguardOk [v0, v1, v2, v3, 48] (predL [v0, v1, v2, v3, 48]) [1, 2]

/-- Succ-side loops: window `[-, Q-1, Q, Q+1, Q+2]`, the moving nodes at `Q, Q+1`. -/
def chkSuccW (v2 : Nat) : Bool :=
  dom.all fun v1 => !(adj .rt v1).contains v2 ||
    (adj .rt v2).all fun v3 => (adj .rt v3).all fun v4 =>
      lguardOk [48, v1, v2, v3, v4] (succL [48, v1, v2, v3, v4]) [2, 3]

end Formal.Net.MullerAll
