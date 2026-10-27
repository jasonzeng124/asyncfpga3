import Formal.Net.Muller
import Formal.Net.MullerRun

namespace Formal.Net.MullerAll
open Formal.Net.Muller Formal.Net.CoreLut

def cfun (a b q : Bool) : Bool := (a && !b) || (q && (a || !b))

theorem evalL_c2n (a b q : Bool) :
    evalL INIT_bd_c2n [a, b, q, false, false, false] = cfun a b q := by
  cases a <;> cases b <;> cases q <;> decide

theorem evalL_buf (a : Bool) : evalL INIT_buf [a] = a := by cases a <;> decide

def bt (v j : Nat) : Bool := v.testBit j
def isSt (v : Nat) : Bool := decide (v < 16)
def isSrc (v : Nat) : Bool := v == 16 || v == 17
def isSnk (v : Nat) : Bool := v == 32 || v == 33

def lnext (m : Mode) (l v r t : Nat) : Bool :=
  if isSrc v then !bt r 2
  else if isSnk v then bt l 1
  else match t with
    | 0 => cfun (if isSrc l then bt l 0 else bt l 1) (if isSnk r then bt r 0 else bt r 2)
             (if m = .iso then bt v 0 else bt v 3)
    | 1 => bt v 0
    | 2 => bt v 0
    | _ => if m = .iso then bt v 3 else bt v 0

def lexc (m : Mode) (l v r t : Nat) : Bool := lnext m l v r t != bt v t

def lallowed (m : Mode) (l v r t : Nat) : Bool :=
  match m with
  | .rt => if isSrc v then bt r 3 == bt r 0
           else if isSnk v then bt l 3 == bt l 0
           else if t = 1 then (if isSt r then bt r 3 == bt r 0 else true)
           else if t = 2 then (if isSt l then bt l 3 == bt l 0 else true)
           else true
  | _ => true

def valid (v t : Nat) : Bool := (isSt v && decide (t < 4)) || ((isSrc v || isSnk v) && t == 0)

def lenabled (m : Mode) (l v r t : Nat) : Bool :=
  valid v t && lexc m l v r t && lallowed m l v r t

def adjIso : Nat → List Nat
  | 0 => [0, 2, 4, 5, 6, 7, 32, 33]
  | 1 => [0, 2, 32]
  | 2 => [5, 7, 33]
  | 3 => [0, 1, 2, 3, 5, 7, 32, 33]
  | 4 => [0, 2, 4, 5, 6, 7, 32, 33]
  | 5 => [0, 2, 32]
  | 6 => [5, 7, 33]
  | 7 => [0, 1, 2, 3, 5, 7, 32, 33]
  | 16 => [0, 2, 4, 5, 6, 7]
  | 17 => [0, 1, 2, 3, 5, 7]
  | 32 => [48]
  | 33 => [48]
  | 48 => [16, 17]
  | _ => []

def adjRt : Nat → List Nat
  | 0 => [0, 2, 4, 6, 8, 10, 12, 13, 14, 15, 32, 33]
  | 1 => [0, 2, 8, 10, 32]
  | 2 => [5, 7, 13, 15, 33]
  | 3 => [0, 1, 2, 3, 9, 11, 32]
  | 4 => [0, 2, 4, 6, 8, 10, 12, 13, 14, 15, 32, 33]
  | 5 => [0, 2, 8, 10, 32]
  | 6 => [5, 7, 13, 15, 33]
  | 7 => [0, 1, 2, 3, 9, 11, 32]
  | 8 => [4, 6, 12, 13, 14, 15, 33]
  | 9 => [0, 2, 8, 10, 32]
  | 10 => [5, 7, 13, 15, 33]
  | 11 => [0, 1, 2, 3, 5, 7, 9, 11, 13, 15, 32, 33]
  | 12 => [4, 6, 12, 13, 14, 15, 33]
  | 13 => [0, 2, 8, 10, 32]
  | 14 => [5, 7, 13, 15, 33]
  | 15 => [0, 1, 2, 3, 5, 7, 9, 11, 13, 15, 32, 33]
  | 16 => [0, 2, 4, 6, 8, 10, 12, 13, 14, 15]
  | 17 => [0, 1, 2, 3, 5, 7, 9, 11, 13, 15]
  | 32 => [48]
  | 33 => [48]
  | 48 => [16, 17]
  | _ => []

def adj : Mode → Nat → List Nat
  | .iso => adjIso
  | .rt => adjRt
  | .free => fun _ => []

def adm (m : Mode) (a b : Nat) : Bool := (adj m a).contains b

def dom : List Nat := List.range 16 ++ [16, 17, 32, 33, 48]
def types : List Nat := [0, 1, 2, 3]
def flip (v t : Nat) : Nat := v ^^^ 2 ^ t

def lpair (v1 v2 : Nat) (same : Bool) (t1 t2 : Nat) : Bool :=
  if same then isSt v1 && t1 == 0 && (t2 == 1 || t2 == 2)
  else (isSrc v1 && isSt v2 && t1 == 0 && (t2 == 0 || t2 == 2)) ||
       (isSt v1 && isSnk v2 && (t1 == 0 || t1 == 1) && t2 == 0) ||
       (isSt v1 && isSt v2 && ((t1 == 0 && t2 == 0) || (t1 == 1 && t2 == 0) || (t1 == 1 && t2 == 2)))

def followL (a b c t : Nat) : Bool :=
  types.all fun u =>
    (!lpair b b true t u || bt b t == bt b u) &&
    (!lpair b c false t u || bt b t == bt c u) &&
    (!lpair b b true u t || bt b t != bt b u) &&
    (!lpair a b false u t || bt b t != bt a u)

def persist (m : Mode) (l v v' r u : Nat) : Bool :=
  (!lexc m l v r u || lexc m l v' r u) && (!lenabled m l v r u || lenabled m l v' r u)

def chkMid (m : Mode) : Bool :=
  dom.all fun a => (adj m a).all fun b => (adj m b).all fun c => types.all fun t =>
    !lenabled m a b c t ||
      (adm m a (flip b t) && adm m (flip b t) c && followL a b c t &&
        types.all fun u => u == t || persist m a b (flip b t) c u)

def chkLeft (m : Mode) : Bool :=
  dom.all fun z => (adj m z).all fun a => (adj m a).all fun b => (adj m b).all fun c =>
    types.all fun t => !lenabled m a b c t || types.all fun u =>
      (!lexc m z a b u || lexc m z a (flip b t) u) &&
      (!lenabled m z a b u || lenabled m z a (flip b t) u)

def chkRight (m : Mode) : Bool :=
  dom.all fun a => (adj m a).all fun b => (adj m b).all fun c => (adj m c).all fun d =>
    types.all fun t => !lenabled m a b c t || types.all fun u =>
      (!lexc m b c d u || lexc m (flip b t) c d u) &&
      (!lenabled m b c d u || lenabled m (flip b t) c d u)

def chkInit (m : Mode) : Bool :=
  adm m 48 16 && adm m 16 0 && adm m 0 0 && adm m 0 32 && adm m 32 48 && adm m 16 32

#eval [chkMid .iso, chkLeft .iso, chkRight .iso, chkInit .iso]
#eval [chkMid .rt, chkLeft .rt, chkRight .rt, chkInit .rt]

end Formal.Net.MullerAll
