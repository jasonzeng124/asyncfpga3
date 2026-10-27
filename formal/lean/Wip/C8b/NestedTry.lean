import Formal.Net.KahnGcd
namespace Formal.Net.Kahn.GcdN
open Formal.Net.Kahn Formal.Net.Kahn.Gcd

inductive Ch
  | inA | inB | sA | sB | backA | backB | hA | hB | hA1 | hA2 | cnd | cA | cB
  | aT | aF | bT | out | a1 | a2 | b1 | b2
  | d | sD | dBack | hD | hD1 | hD2 | ce | cE | dT
  deriving DecidableEq

inductive Nd
  | muxA | muxB | forkA | isnz | forkC | brA | brB | snkA | forkAT | forkBT | sub | mn
  | muxD | forkD | evn | forkE | brD | shr
  deriving DecidableEq

/-- inner-loop condition `a > 0 && (a & 1) == 0` as a token -/
def ev (x : Nat) : Nat := if 0 < x ∧ x % 2 = 0 then 1 else 0

def G3 : Nd → Node Ch Nat
  | .muxA   => mux .sA .inA .backA .hA tst (by decide) (by decide)
  | .muxB   => mux .sB .inB .backB .hB tst (by decide) (by decide)
  | .forkA  => fork .hA [.hA1, .hA2]
  | .isnz   => op1 .hA1 .cnd (fun x => if x == 0 then 0 else 1)
  | .forkC  => fork .cnd [.cA, .cB, .sA, .sB]
  | .brA    => branch .cA .hA2 .aT .aF tst
  | .brB    => branch .cB .hB .bT .out tst
  | .snkA   => sink .aF
  | .forkAT => fork .aT [.a1, .a2]
  | .forkBT => fork .bT [.b1, .b2]
  | .sub    => op2 .a1 .b1 .d absdiff
  | .mn     => op2 .a2 .b2 .backB min
  | .muxD   => mux .sD .d .dBack .hD tst (by decide) (by decide)
  | .forkD  => fork .hD [.hD1, .hD2]
  | .evn    => op1 .hD1 .ce ev
  | .forkE  => fork .ce [.cE, .sD]
  | .brD    => branch .cE .hD2 .dT .backA tst
  | .shr    => op1 .dT .dBack (· / 2)

/-- inner loop header has fired on `x`; `m` waits on backB -/
def imid (x m : Nat) : Store Ch Nat := fun
  | .hD => [x] | .sA => [1] | .sB => [1] | .backB => [m] | _ => []

def itop (x m : Nat) : Store Ch Nat := fun
  | .dBack => [x] | .sD => [1] | .sA => [1] | .sB => [1] | .backB => [m] | _ => []

theorem inner_iter (x m : Nat) (h : ev x = 1) : Run (step G3) (imid x m) 5 (itop (x / 2) m) := by
  apply exec_run (ls := [.forkD, .evn, .forkE, .brD, .shr]) (t := itop (x / 2) m) _ (fun _ => rfl)
  simp [exec, step, G3, fork, op1, branch, strict, heads, applyF, imid, h, tst]
  funext c; cases c <;> rfl

end Formal.Net.Kahn.GcdN
