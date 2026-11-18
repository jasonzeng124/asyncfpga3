import Formal.Rewrite.PlainPass
import Formal.Rewrite.Ring.CountloopHw
import Formal.Rewrite.Ring.HornerHw
import Formal.Rewrite.Ring.QuadrecHw
import Formal.Rewrite.Ring.VarshiftHw
import Formal.Rewrite.Ring.XorshiftHw
import Formal.Rewrite.Plain.CountloopPlainGen
import Formal.Rewrite.Plain.HornerPlainGen
import Formal.Rewrite.Plain.QuadrecPlainGen
import Formal.Rewrite.Plain.VarshiftPlainGen
import Formal.Rewrite.Plain.XorshiftPlainGen

/-!
# Formal.Rewrite.Plain.PassInst -- the plain-test pass (`PlainPass`) applied to the five ring kernels (shard A, 2026-11-18)

**Problem, plainly.** `PlainPass.plain_forward` / `plain_backward` hold for any graph whose certificate passes
`check`. Does `check` pass on research's five ring fixtures, and is the rewritten graph the one already tied to
`out/<k>_plain.mlir`?

**Proved:** for each kernel K, `K_check : check K.rules cK = true` (`decide +kernel`), so `K_forward` /
`K_backward` are the pass theorem on K. `K_rs2p` says that `rs2p K.rules cK` is `<K>PlainGen.rs2p`, the graph that
`<K>PlainTie` (and CountloopPlainGenTie) ties to the import of `formal/tools-A/rewrite/out/<k>_plain.mlir`. The
certificates are printed by `formal/tools-A/rewrite/gen_plain_gen.py NAME RS2_EVAL --cert` (untrusted; checked here).

**Not covered:** token level only.
-/

namespace Formal.Rewrite.Plain.PassInst

open Formal.Net.Kahn Formal.Net.GcdHw Formal.Rewrite.PlainPass

def cCountloop : Cert where
  M := 20
  F := 21
  B := 35
  S := 36
  C := 28
  sel := 41
  ne := 24
  ne' := 67
  r := 43
  r0 := 44
  k := 45
  nb := 42
  nx := 62
  cnd := 55
  y := 52
  c := 53
  iw := 1
  lb := 26
  ld := 27
  e := 31
  s := 50
  s0 := 51
  e0 := 68
  e1 := 69
  gF := 1
  gC := 3
  gK := 4
  gB := 12
  ge := 1
  gd := 7
  gx := 8
  gc := 10
  gcb := 13
  gk := 9
  gt := 24
  gf := 25
  gos := [11, 12, 13, 14]
  tK := 29
  tB := 30
  tcb := 58
  tt := 29
  tf := 59
  tos := [54, 55, 56, 57, 58]
  c1 := [19, 20, 29, 30, 31, 42, 43, 44, 45, 67, 69]
  c2 := [24]

theorem countloop_check : check Formal.Rewrite.Ring.CountloopHw.rules cCountloop = true := by decide +kernel

theorem countloop_rs2p : rs2p Formal.Rewrite.Ring.CountloopHw.rules cCountloop = Formal.Rewrite.Plain.CountloopPlainGen.rs2p := by decide +kernel

theorem countloop_forward {σ0 t : Store Nat Nat} {n : Nat} (h0 : ∀ ch, ch ≠ 0 → ch ≠ 1 → ch ≠ 2 → σ0 ch = [])
    (hr : Run (step (graph Formal.Rewrite.Ring.CountloopHw.rules)) σ0 n t) (ht : Terminal (step (graph Formal.Rewrite.Ring.CountloopHw.rules)) t) :
    ∃ t' m, Run (step (graph (rs2p Formal.Rewrite.Ring.CountloopHw.rules cCountloop))) σ0 m t' ∧ Terminal (step (graph (rs2p Formal.Rewrite.Ring.CountloopHw.rules cCountloop))) t' ∧
      ∀ ch, ch ∉ changed cCountloop → t' ch = t ch :=
  plain_forward countloop_check h0 hr ht

theorem countloop_backward {σ0 t' : Store Nat Nat} {n : Nat} (h0 : ∀ ch, ch ≠ 0 → ch ≠ 1 → ch ≠ 2 → σ0 ch = [])
    (hr : Run (step (graph (rs2p Formal.Rewrite.Ring.CountloopHw.rules cCountloop))) σ0 n t') (ht : Terminal (step (graph (rs2p Formal.Rewrite.Ring.CountloopHw.rules cCountloop))) t') :
    ∃ t m, Run (step (graph Formal.Rewrite.Ring.CountloopHw.rules)) σ0 m t ∧ Terminal (step (graph Formal.Rewrite.Ring.CountloopHw.rules)) t ∧
      ∀ ch, ch ∉ changed cCountloop → t ch = t' ch :=
  plain_backward countloop_check h0 hr ht

def cHorner : Cert where
  M := 20
  F := 21
  B := 35
  S := 36
  C := 28
  sel := 41
  ne := 24
  ne' := 67
  r := 43
  r0 := 44
  k := 45
  nb := 42
  nx := 62
  cnd := 55
  y := 52
  c := 53
  iw := 1
  lb := 26
  ld := 27
  e := 31
  s := 50
  s0 := 51
  e0 := 68
  e1 := 69
  gF := 1
  gC := 3
  gK := 4
  gB := 12
  ge := 1
  gd := 7
  gx := 8
  gc := 10
  gcb := 13
  gk := 9
  gt := 24
  gf := 25
  gos := [11, 12, 13, 14]
  tK := 29
  tB := 30
  tcb := 58
  tt := 29
  tf := 59
  tos := [54, 55, 56, 57, 58]
  c1 := [19, 20, 29, 30, 31, 42, 43, 44, 45, 67, 69]
  c2 := [24]

theorem horner_check : check Formal.Rewrite.Ring.HornerHw.rules cHorner = true := by decide +kernel

theorem horner_rs2p : rs2p Formal.Rewrite.Ring.HornerHw.rules cHorner = Formal.Rewrite.Plain.HornerPlainGen.rs2p := by decide +kernel

theorem horner_forward {σ0 t : Store Nat Nat} {n : Nat} (h0 : ∀ ch, ch ≠ 0 → ch ≠ 1 → ch ≠ 2 → σ0 ch = [])
    (hr : Run (step (graph Formal.Rewrite.Ring.HornerHw.rules)) σ0 n t) (ht : Terminal (step (graph Formal.Rewrite.Ring.HornerHw.rules)) t) :
    ∃ t' m, Run (step (graph (rs2p Formal.Rewrite.Ring.HornerHw.rules cHorner))) σ0 m t' ∧ Terminal (step (graph (rs2p Formal.Rewrite.Ring.HornerHw.rules cHorner))) t' ∧
      ∀ ch, ch ∉ changed cHorner → t' ch = t ch :=
  plain_forward horner_check h0 hr ht

theorem horner_backward {σ0 t' : Store Nat Nat} {n : Nat} (h0 : ∀ ch, ch ≠ 0 → ch ≠ 1 → ch ≠ 2 → σ0 ch = [])
    (hr : Run (step (graph (rs2p Formal.Rewrite.Ring.HornerHw.rules cHorner))) σ0 n t') (ht : Terminal (step (graph (rs2p Formal.Rewrite.Ring.HornerHw.rules cHorner))) t') :
    ∃ t m, Run (step (graph Formal.Rewrite.Ring.HornerHw.rules)) σ0 m t ∧ Terminal (step (graph Formal.Rewrite.Ring.HornerHw.rules)) t ∧
      ∀ ch, ch ∉ changed cHorner → t ch = t' ch :=
  plain_backward horner_check h0 hr ht

def cQuadrec : Cert where
  M := 35
  F := 36
  B := 51
  S := 52
  C := 43
  sel := 69
  ne := 44
  ne' := 109
  r := 71
  r0 := 72
  k := 73
  nb := 70
  nx := 94
  cnd := 83
  y := 80
  c := 81
  iw := 1
  lb := 41
  ld := 42
  e := 50
  s := 78
  s0 := 79
  e0 := 110
  e1 := 111
  gF := 1
  gC := 4
  gK := 5
  gB := 24
  ge := 1
  gd := 10
  gx := 11
  gc := 14
  gcb := 19
  gk := 12
  gt := 44
  gf := 45
  gos := [15, 16, 17, 18, 19, 20, 21]
  tK := 44
  tB := 45
  tcb := 88
  tt := 49
  tf := 89
  tos := [82, 83, 84, 85, 86, 87, 88]
  c1 := [25, 49, 50, 70, 71, 72, 73, 109, 111]
  c2 := [44]

theorem quadrec_check : check Formal.Rewrite.Ring.QuadrecHw.rules cQuadrec = true := by decide +kernel

theorem quadrec_rs2p : rs2p Formal.Rewrite.Ring.QuadrecHw.rules cQuadrec = Formal.Rewrite.Plain.QuadrecPlainGen.rs2p := by decide +kernel

theorem quadrec_forward {σ0 t : Store Nat Nat} {n : Nat} (h0 : ∀ ch, ch ≠ 0 → ch ≠ 1 → ch ≠ 2 → σ0 ch = [])
    (hr : Run (step (graph Formal.Rewrite.Ring.QuadrecHw.rules)) σ0 n t) (ht : Terminal (step (graph Formal.Rewrite.Ring.QuadrecHw.rules)) t) :
    ∃ t' m, Run (step (graph (rs2p Formal.Rewrite.Ring.QuadrecHw.rules cQuadrec))) σ0 m t' ∧ Terminal (step (graph (rs2p Formal.Rewrite.Ring.QuadrecHw.rules cQuadrec))) t' ∧
      ∀ ch, ch ∉ changed cQuadrec → t' ch = t ch :=
  plain_forward quadrec_check h0 hr ht

theorem quadrec_backward {σ0 t' : Store Nat Nat} {n : Nat} (h0 : ∀ ch, ch ≠ 0 → ch ≠ 1 → ch ≠ 2 → σ0 ch = [])
    (hr : Run (step (graph (rs2p Formal.Rewrite.Ring.QuadrecHw.rules cQuadrec))) σ0 n t') (ht : Terminal (step (graph (rs2p Formal.Rewrite.Ring.QuadrecHw.rules cQuadrec))) t') :
    ∃ t m, Run (step (graph Formal.Rewrite.Ring.QuadrecHw.rules)) σ0 m t ∧ Terminal (step (graph Formal.Rewrite.Ring.QuadrecHw.rules)) t ∧
      ∀ ch, ch ∉ changed cQuadrec → t ch = t' ch :=
  plain_backward quadrec_check h0 hr ht

def cVarshift : Cert where
  M := 24
  F := 25
  B := 46
  S := 47
  C := 39
  sel := 48
  ne := 28
  ne' := 83
  r := 50
  r0 := 51
  k := 52
  nb := 49
  nx := 78
  cnd := 71
  y := 68
  c := 69
  iw := 1
  lb := 37
  ld := 38
  e := 35
  s := 66
  s0 := 67
  e0 := 84
  e1 := 85
  gF := 1
  gC := 3
  gK := 4
  gB := 15
  ge := 1
  gd := 8
  gx := 9
  gc := 11
  gcb := 15
  gk := 10
  gt := 28
  gf := 29
  gos := [12, 13, 14, 15, 16]
  tK := 40
  tB := 41
  tcb := 74
  tt := 33
  tf := 75
  tos := [70, 71, 72, 73, 74]
  c1 := [20, 33, 34, 35, 49, 50, 51, 52, 83, 85]
  c2 := [28]

theorem varshift_check : check Formal.Rewrite.Ring.VarshiftHw.rules cVarshift = true := by decide +kernel

theorem varshift_rs2p : rs2p Formal.Rewrite.Ring.VarshiftHw.rules cVarshift = Formal.Rewrite.Plain.VarshiftPlainGen.rs2p := by decide +kernel

theorem varshift_forward {σ0 t : Store Nat Nat} {n : Nat} (h0 : ∀ ch, ch ≠ 0 → ch ≠ 1 → ch ≠ 2 → σ0 ch = [])
    (hr : Run (step (graph Formal.Rewrite.Ring.VarshiftHw.rules)) σ0 n t) (ht : Terminal (step (graph Formal.Rewrite.Ring.VarshiftHw.rules)) t) :
    ∃ t' m, Run (step (graph (rs2p Formal.Rewrite.Ring.VarshiftHw.rules cVarshift))) σ0 m t' ∧ Terminal (step (graph (rs2p Formal.Rewrite.Ring.VarshiftHw.rules cVarshift))) t' ∧
      ∀ ch, ch ∉ changed cVarshift → t' ch = t ch :=
  plain_forward varshift_check h0 hr ht

theorem varshift_backward {σ0 t' : Store Nat Nat} {n : Nat} (h0 : ∀ ch, ch ≠ 0 → ch ≠ 1 → ch ≠ 2 → σ0 ch = [])
    (hr : Run (step (graph (rs2p Formal.Rewrite.Ring.VarshiftHw.rules cVarshift))) σ0 n t') (ht : Terminal (step (graph (rs2p Formal.Rewrite.Ring.VarshiftHw.rules cVarshift))) t') :
    ∃ t m, Run (step (graph Formal.Rewrite.Ring.VarshiftHw.rules)) σ0 m t ∧ Terminal (step (graph Formal.Rewrite.Ring.VarshiftHw.rules)) t ∧
      ∀ ch, ch ∉ changed cVarshift → t ch = t' ch :=
  plain_backward varshift_check h0 hr ht

def cXorshift : Cert where
  M := 15
  F := 16
  B := 29
  S := 30
  C := 24
  sel := 31
  ne := 21
  ne' := 56
  r := 33
  r0 := 34
  k := 35
  nb := 32
  nx := 51
  cnd := 46
  y := 43
  c := 44
  iw := 1
  lb := 22
  ld := 23
  e := 27
  s := 41
  s0 := 42
  e0 := 57
  e1 := 58
  gF := 1
  gC := 3
  gK := 4
  gB := 10
  ge := 1
  gd := 7
  gx := 8
  gc := 10
  gcb := 13
  gk := 9
  gt := 21
  gf := 22
  gos := [11, 12, 13, 14]
  tK := 25
  tB := 26
  tcb := 48
  tt := 26
  tf := 49
  tos := [45, 46, 47, 48]
  c1 := [18, 26, 27, 32, 33, 34, 35, 56, 58]
  c2 := [21]

theorem xorshift_check : check Formal.Rewrite.Ring.XorshiftHw.rules cXorshift = true := by decide +kernel

theorem xorshift_rs2p : rs2p Formal.Rewrite.Ring.XorshiftHw.rules cXorshift = Formal.Rewrite.Plain.XorshiftPlainGen.rs2p := by decide +kernel

theorem xorshift_forward {σ0 t : Store Nat Nat} {n : Nat} (h0 : ∀ ch, ch ≠ 0 → ch ≠ 1 → ch ≠ 2 → σ0 ch = [])
    (hr : Run (step (graph Formal.Rewrite.Ring.XorshiftHw.rules)) σ0 n t) (ht : Terminal (step (graph Formal.Rewrite.Ring.XorshiftHw.rules)) t) :
    ∃ t' m, Run (step (graph (rs2p Formal.Rewrite.Ring.XorshiftHw.rules cXorshift))) σ0 m t' ∧ Terminal (step (graph (rs2p Formal.Rewrite.Ring.XorshiftHw.rules cXorshift))) t' ∧
      ∀ ch, ch ∉ changed cXorshift → t' ch = t ch :=
  plain_forward xorshift_check h0 hr ht

theorem xorshift_backward {σ0 t' : Store Nat Nat} {n : Nat} (h0 : ∀ ch, ch ≠ 0 → ch ≠ 1 → ch ≠ 2 → σ0 ch = [])
    (hr : Run (step (graph (rs2p Formal.Rewrite.Ring.XorshiftHw.rules cXorshift))) σ0 n t') (ht : Terminal (step (graph (rs2p Formal.Rewrite.Ring.XorshiftHw.rules cXorshift))) t') :
    ∃ t m, Run (step (graph Formal.Rewrite.Ring.XorshiftHw.rules)) σ0 m t ∧ Terminal (step (graph Formal.Rewrite.Ring.XorshiftHw.rules)) t ∧
      ∀ ch, ch ∉ changed cXorshift → t ch = t' ch :=
  plain_backward xorshift_check h0 hr ht

/-! ## Negative controls: `check` can fail -/

/-- countloop with its loop guard `n > 0` replaced by `n != 0`: then `n = INT_MIN` enters the loop, `n - 1` wraps to
INT_MAX, and the plain test is wrong on the first trip (original `1 < INT_MIN` is false, plain `0 < INT_MAX` is
true). `check` refuses it. -/
theorem control_guard_ne : check ((Formal.Rewrite.Ring.CountloopHw.rules).set 3
    (.comp [8, 9] 10 (.bin (.cmpi .ne) 32 (.var 0) (.var 1)))) cCountloop = false := by decide +kernel

/-- The arithmetic behind `control_guard_ne`: at n = INT_MIN (2147483648), first trip (i = 0), the original test
`slt(i + 1, n)` is false and the plain test `slt(i, n - 1)` is true. -/
theorem control_guard_ne_values :
    Formal.Rewrite.IncCmp.fSlt.eval [Formal.Rewrite.IncCmp.fInc.eval [0], 2147483648] = 0 ∧
    Formal.Rewrite.IncCmp.fSlt.eval [0, Formal.Rewrite.IncCmp.gDec.eval [2147483648]] = 1 := by decide

/-- countloop's certificate without the NotMin class on `n`: the `n - 1` rule is then not safe. -/
theorem control_no_class2 : check Formal.Rewrite.Ring.CountloopHw.rules { cCountloop with c2 := [] } = false := by
  decide +kernel

end Formal.Rewrite.Plain.PassInst
