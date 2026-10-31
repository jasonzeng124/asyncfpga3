import Formal.Net.Compute.GcdJoin
import Formal.Net.Compute.XsFn
import Formal.Net.Compute.XsXor
/-! Auditor P15bc, item 1: statement shapes, axioms, and an independent check of the capstone's
20 join functions `jgAt p` against the auditor's own reading of bdc's cf.mlir
(/root/wt-r14/build/frontend/gcd/comp/cf.mlir), in 32-bit two's complement written from scratch. -/
open Formal.Net Formal.Net.Compute Formal.Net.GcdHw Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Gen.Compute.GcdD Formal.Net.Compute.GcdD Formal.Net.Compute.GcdJoin

#check @j117
#check @j162
#check @j27
#check @j66
#check @ushli0_fn
#check @uselect0_fn
#check @uselect1_fn
#check @uori2_fn
#check @Formal.Net.Compute.Xs.xs_ucmpi0_fn
#check @Formal.Net.Compute.Xs.xs_uxori1_fn
#print axioms j2
#print axioms j27
#print axioms j66
#print axioms j117
#print axioms j135
#print axioms j162
#print axioms joins_listed
#print axioms ushli0_fn
#print axioms uselect1_fn
#print axioms uori3_fn
#print axioms uori4_fn
#print axioms Formal.Net.Compute.Xs.xs_uaddi0_fn
#print axioms Formal.Net.Compute.Xs.xs_ucmpi0_fn
#print axioms Formal.Net.Compute.Xs.xs_ucmpi1_fn
#print axioms Formal.Net.Compute.Xs.xs_uxori1_fn
#print axioms Formal.Net.Compute.Xs.xs_uxori2_fn

namespace Aud
def M : Nat := 2 ^ 32
def s32 (x : Nat) : Int := if x % M < 2 ^ 31 then (x % M : Nat) else ((x % M : Nat) : Int) - (M : Int)
def u32 (i : Int) : Nat := (i % (M : Int)).toNat
def b (p : Bool) : Nat := if p then 1 else 0
/-- The auditor's reading of cf.mlir, per capstone join (unit pairing as in GcdJoin):
uori0/1: a|b; ucmpi0/1/8/10: x == 0; ucmpi2 (bb2 %4): ((a|b) & 1) == 0; ucmpi3 (bb3 %13): same on
the shifted or; ushrsi*: x >>s 1; uaddi0: k + 1; uori2/3/4 (bb5/7/11): (x&1 != 0) | (x <s 1);
uselect0 (bb9): (p <s q) ? p : q; uselect1 (bb10): d = p - q; d >s -1 ? d : 0 - d;
ushli0 (bb12): x << k. -/
def spec : Nat → List Nat → Nat
  | 2, [v] | 13, [v] | 104, [v] | 118, [v] => b (v % M = 0)
  | 26, [v, w] | 46, [v, w] => (v ||| w) % M
  | 27, [v, _] => b (v % 2 = 0)
  | 47, [v] => b (v % 2 = 0)
  | 41, [v] | 43, [v] | 68, [v] | 89, [v] | 144, [v] => u32 ((s32 v).fdiv 2)
  | 45, [v] => (v + 1) % M
  | 66, [v, w] | 87, [v, w] | 142, [v, w] => b (w % 2 ≠ 0 ∨ s32 v < 1)
  | 117, [v, w] => if s32 v < s32 w then v % M else w % M
  | 135, [v, w] => let d := s32 v - s32 w; let d' := s32 (u32 d); if d' > -1 then u32 d' else u32 (- d')
  | 162, [v, k] => (v * 2 ^ k) % M
  | _, _ => 1000000
def arity : Nat → Nat
  | 26 | 46 | 27 | 66 | 87 | 142 | 117 | 135 | 162 => 2
  | _ => 1
def vals : List Nat := [0, 1, 2, 3, 5, 6, 7, 31, 2^31 - 1, 2^31, 2^31 + 1, 2^32 - 1, 2^32 - 2,
  123456789, 3735928559, 2863311530, 1431655765, 4096, 12, 18]
def ks : List Nat := [0, 1, 2, 5, 17, 30, 31]
def cases : List (Nat × List Nat) :=
  [2, 13, 26, 27, 41, 43, 45, 46, 47, 66, 68, 87, 89, 104, 117, 118, 135, 142, 144, 162].flatMap fun p =>
    if p = 162 then vals.flatMap fun v => ks.map fun k => (p, [v, k])
    else if arity p = 2 then vals.flatMap fun v => vals.map fun w => (p, [v, w])
    else vals.map fun v => (p, [v])
def bad : List (Nat × List Nat × Nat × Nat) :=
  (cases.filter fun (p, xs) => jgAt p xs != spec p xs).map fun (p, xs) => (p, xs, jgAt p xs, spec p xs)
end Aud
#eval Aud.cases.length
#eval Aud.bad.length
#eval Aud.bad.take 10
