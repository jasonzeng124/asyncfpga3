import Formal.Net.CapstoneCut
open Formal.Net Formal.Net.Kahn Formal.Net.GcdHw Formal.Net.CapSafe Formal.Net.CapNet Formal.Net.CapNet.Gcd

namespace AuditP5
def x0 (a b : Nat) : TS := ⟨GcdHw.Gcd.init a b, fun _ => [], fun _ => []⟩

def firstEn (x : TS) : Option Nat := (List.range GcdHw.Gcd.rules.length).find? (fun l => (tstep x l).isSome)

def sched : Nat → TS → List Nat → List Nat
  | 0, _, acc => acc.reverse
  | f+1, x, acc => match firstEn x with
    | none => acc.reverse
    | some l => match tstep x l with
      | some x' => sched f x' (l :: acc)
      | none => acc.reverse

def walkLen (σ : Fin NC → Nat → Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | f+1, p => if (walk σ p).cur = none then some p else walkLen σ f (p+1)

def walkChk (σ : Fin NC → Nat → Nat) (om : Nat → Nat → Bool) (P : Nat) : Bool :=
  (List.range P).all fun p => match (walk σ p).cur with
    | none => true
    | some d => match opAt (consOf d) with
      | .amerge _ y z w => om w ((walk σ p).W z) == decide (d = y)
      | _ => true

def test (a b : Nat) : String :=
  let ls := sched 100000 (x0 a b) []
  match texec (x0 a b) ls with
  | none => "texec none"
  | some y =>
    let σ := σY a b y
    let wl := walkLen σ 5000 0
    s!"a={a} b={b} |ls|={ls.length} out={y.s 250} end={y.s 3} walkLen={wl} walkOK={walkChk σ (omOf a b y) (wl.getD 0)} arbVisits={(List.range (wl.getD 0)).countP (fun p => match (walk σ p).cur with | some d => (match opAt (consOf d) with | .amerge .. => true | _ => false) | none => false)}"

#eval test 0 0
#eval test 1 1
#eval test 12 18
end AuditP5
namespace AuditP5
#eval IO.println (toString (sched 100000 (x0 0 0) []))
#eval IO.println (toString (sched 100000 (x0 1 1) []))
#eval IO.println (toString (sched 100000 (x0 12 18) []))
end AuditP5
