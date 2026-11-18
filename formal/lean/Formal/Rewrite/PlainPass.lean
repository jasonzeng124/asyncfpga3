import Formal.Rewrite.RingMap
import Formal.Rewrite.IncCmp2
import Formal.Rewrite.IncCmpArith
import Formal.Rewrite.ChanInv
import Formal.Rewrite.Swap
import Formal.Rewrite.PlainArith

/-!
# Formal.Rewrite.PlainPass -- the PLAIN loop-test rewrite as a pass: one theorem for every graph whose certificate checks (shard A, 2026-11-18)

**Problem, plainly.** The auditor's T156 asks for each rewrite of the automatic path as a PASS: a pattern, side
conditions, and a proof for every program that matches. The plain loop-test rewrite (`i + 1 < n` -> `i < n - 1`,
the ring carries `n - 1`) is false as a local pattern (i = INT_MAX, n = 0), so its side condition has to be a fact
about the loop. Is there one statement, for ANY imported graph, with a side condition a machine can check?

**Proved** (`plain_forward`, `plain_backward`): for every rule list `rules` and every certificate `X` (the channel
and label numbers of the pattern, the two branch pairs, and the channel classes) with `check rules X = true`, from
any store holding tokens only on the input channels (those below `X.na`: the arguments and the start token): every complete run of `rules` is matched by a complete run of the
rewritten graph `rs2p rules X` ending in the same store outside `changed X`, and vice versa.

The certificate is untrusted (a script finds it: `formal/tools-A/rewrite/gen_plain_gen.py`); `check` is a Bool
function evaluated on the program, and this theorem says that its `true` is enough. In words, `check` asks:
- the ring pattern (RingMap.Pat) and the moved-test pattern (IncCmp2.Pat2) are where the certificate says, and no
  other rule touches their internal channels;
- the loop guard: `n` enters the ring only through a cond_br on `sgt(n, .)` of a fork of the same token, and the
  loop test's back edge only carries `i + 1` whose test was true (ChanInv.PairOK, as data);
- every other rule copies a channel's class or leaves its output unconstrained; a 1-bit extui may start a NotMax
  channel; `n - 1` of a NotMin channel is NotMax (ChanInv.RuleSafe, checked rule by rule);
- the counter and the bound read by the test are in the NotMax class, the arguments are unconstrained.

**Not covered:** token level only. The tie of `rs2p rules X` to a rewritten MLIR file is per program
(`Rename`, `renCheck`, decidable too).
-/

namespace Formal.Rewrite.PlainPass

open Formal.Net.Kahn Formal.Net.GcdHw Formal.Rewrite.IncCmp Formal.Rewrite.ChanInv

/-- Everything the pass needs to know about one program; found by an untrusted script, checked by `check`. -/
structure Cert where
  /-- The input channels are `0 .. na - 1` (dfimport: the arguments, then the start token). -/
  na : Nat
  M : Nat
  F : Nat
  B : Nat
  S : Nat
  C : Nat
  sel : Nat
  ne : Nat
  ne' : Nat
  r : Nat
  r0 : Nat
  k : Nat
  nb : Nat
  nx : Nat
  cnd : Nat
  y : Nat
  c : Nat
  iw : Nat
  lb : Nat
  ld : Nat
  e : Nat
  s : Nat
  s0 : Nat
  e0 : Nat
  e1 : Nat
  gF : Nat
  gC : Nat
  gK : Nat
  gB : Nat
  ge : Nat
  gd : Nat
  gx : Nat
  gc : Nat
  gcb : Nat
  gk : Nat
  gt : Nat
  gf : Nat
  gos : List Nat
  tK : Nat
  tB : Nat
  tcb : Nat
  tt : Nat
  tf : Nat
  tos : List Nat
  c1 : List Nat
  c2 : List Nat

variable (rules : List Rule) (X : Cert)

/-! ## The rewrite -/

/-- The ring carries `n - 1` (RingMap). -/
def rs1 : List Rule :=
  ((rules.set X.M (.mux X.sel [X.ne', X.nb] X.r X.iw)).set X.C (.comp [X.y, X.k] X.c fSltInc)) ++
    [.comp [X.ne] X.ne' gDec]

/-- The test moved before the increment, corrected (IncCmp2). -/
def rs2 : List Rule :=
  (((rs1 rules X).set X.lb (.fork X.e [X.e0, X.e1])).set X.ld (.comp [X.e0] X.s0 fInc)).set X.C
    (.comp [X.e1, X.k] X.c fSltXor)

/-- The plain test `slt(i, m)`: what `ring_dec.py --plain` emits. -/
def rs2p : List Rule := (rs2 rules X).set X.C (.comp [X.e1, X.k] X.c fSlt)

/-- The channels the rewrite may leave different. -/
def changed : List Nat := [X.ne, X.ne', X.r, X.r0, X.k, X.nb, X.nx, X.s, X.y, X.e0, X.e1]

/-! ## Classes -/

def cls (ch : Nat) : Nat := if ch ∈ X.c1 then 1 else if ch ∈ X.c2 then 2 else 0

def Q (ch v : Nat) : Prop := if cls X ch = 1 then NotMax v else if cls X ch = 2 then NotMin v else True

variable {X}

theorem Q_cls {a b : Nat} (h : cls X a = cls X b) (v : Nat) (hv : Q X a v) : Q X b v := by
  unfold Q at *; rw [← h]; exact hv

theorem Q_zero {a : Nat} (h : cls X a = 0) (v : Nat) : Q X a v := by
  unfold Q; rw [h]; simp

theorem Q_one {a : Nat} (h : cls X a = 1) (v : Nat) : Q X a v ↔ NotMax v := by
  unfold Q; rw [h]; simp

theorem Q_two {a : Nat} (h : cls X a = 2) (v : Nat) : Q X a v ↔ NotMin v := by
  unfold Q; rw [h]; simp

variable (X)

/-! ## The two branch pairs -/

def pG : Pair where
  lF := X.gF
  lA := 0
  lC := X.gC
  lK := X.gK
  lB := X.gB
  e := X.ge
  d0 := X.gd
  d := X.gd
  x := X.gx
  c := X.gc
  cb := X.gcb
  k := X.gk
  t := X.gt
  f := X.gf
  os := X.gos
  hasA := false
  fA := E.var 0
  F := E.bin (BOp.cmpi Pred.sgt) 32 (E.var 0) (E.var 1)

def pT : Pair where
  lF := X.lb
  lA := X.ld
  lC := X.C
  lK := X.tK
  lB := X.tB
  e := X.e
  d0 := X.e0
  d := X.s0
  x := X.e1
  c := X.c
  cb := X.tcb
  k := X.k
  t := X.tt
  f := X.tf
  os := X.tos
  hasA := true
  fA := fInc
  F := fSltXor

/-! ## The checker -/

/-- A per-label Bool check over a whole rule list. -/
def allL (rs : List Rule) (p : Nat → Rule → Bool) : Bool :=
  (List.range rs.length).all (fun l => match rs[l]? with | some r => p l r | none => true)

theorem of_allL {rs : List Rule} {p : Nat → Rule → Bool} (h : allL rs p = true) :
    ∀ l r, rs[l]? = some r → p l r = true := by
  intro l r hr
  have hl : l < rs.length := by
    rcases Nat.lt_or_ge l rs.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hr; cases hr
  have := List.all_eq_true.mp h l (List.mem_range.mpr hl)
  simp only [hr] at this; exact this

def sameL (rs rs' : List Rule) (ex : Nat → Bool) : Bool :=
  (List.range (max rs.length rs'.length)).all (fun l => ex l || decide (rs'[l]? = rs[l]?))

theorem of_sameL {rs rs' : List Rule} {ex : Nat → Bool} (h : sameL rs rs' ex = true) :
    ∀ l, ex l = false → rs'[l]? = rs[l]? := by
  intro l hl
  rcases Nat.lt_or_ge l (max rs.length rs'.length) with h1 | h1
  · have := List.all_eq_true.mp h l (List.mem_range.mpr h1)
    simp only [hl, Bool.false_or, decide_eq_true_eq] at this; exact this
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

def notIn (ch : Nat) (L : List Nat) : Bool := !decide (ch ∈ L)

theorem of_notIn {ch : Nat} {L : List Nat} (h : notIn ch L = true) : ch ∉ L := by
  simpa [notIn] using h

/-- RingMap.Pat on (rules, rs1). -/
def chkRing : Bool :=
  decide (rules[X.M]? = some (.mux X.sel [X.ne, X.nb] X.r X.iw) ∧
    (rs1 rules X)[X.M]? = some (.mux X.sel [X.ne', X.nb] X.r X.iw) ∧
    rules[X.F]? = some (.fork X.r [X.r0, X.k]) ∧ (rs1 rules X)[X.F]? = some (.fork X.r [X.r0, X.k]) ∧
    rules[X.B]? = some (.branch X.cnd X.r0 X.nb X.nx) ∧ (rs1 rules X)[X.B]? = some (.branch X.cnd X.r0 X.nb X.nx) ∧
    rules[X.S]? = some (.sink X.nx) ∧ (rs1 rules X)[X.S]? = some (.sink X.nx) ∧
    rules[X.C]? = some (.comp [X.y, X.k] X.c fSlt) ∧ (rs1 rules X)[X.C]? = some (.comp [X.y, X.k] X.c fSltInc) ∧
    (rs1 rules X)[rules.length]? = some (.comp [X.ne] X.ne' gDec) ∧
    [X.ne, X.ne', X.r, X.r0, X.k, X.nb, X.nx].Nodup ∧
    (∀ ch ∈ [X.sel, X.cnd, X.y, X.c], ch ∉ [X.ne, X.ne', X.r, X.r0, X.k, X.nb, X.nx])) &&
  sameL rules (rs1 rules X) (fun l => l == X.M || l == X.F || l == X.B || l == X.S || l == X.C ||
    l == rules.length) &&
  allL rules (fun l r => l == X.M || l == X.F || l == X.B || l == X.S || l == X.C ||
    r.insL.all (fun ch => notIn ch [X.ne, X.ne', X.r, X.r0, X.k, X.nb, X.nx])) &&
  allL rules (fun l r => l == X.M || l == X.F || l == X.B || l == X.S || l == X.C ||
    r.outsL.all (fun ch => notIn ch [X.ne', X.r, X.r0, X.k, X.nb, X.nx]))

theorem patRing (h : chkRing rules X = true) :
    RingMap.Pat rules (rs1 rules X) X.M X.F X.B X.S X.C rules.length X.sel X.ne X.ne' X.r X.r0 X.k X.nb X.nx
      X.cnd X.y X.c X.iw fSlt fSltInc gDec := by
  simp only [chkRing, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hM, hM', hF, hF', hB, hB', hS, hS', hC, hC', hD', hnd, hext⟩, hsame⟩, hins⟩, houts⟩ := h
  exact {
    hM := hM, hM' := hM', hF := hF, hF' := hF', hB := hB, hB' := hB', hS := hS, hS' := hS', hC := hC, hC' := hC'
    hD := List.getElem?_eq_none (Nat.le_refl _)
    hD' := hD'
    hsame := by
      intro l h1 h2 h3 h4 h5 h6
      exact of_sameL hsame l (by simp [h1, h2, h3, h4, h5, h6])
    hins := by
      intro l ru h1 h2 h3 h4 h5 hr ch hch
      have := of_allL hins l ru hr
      simp only [Bool.or_eq_true, beq_iff_eq, h1, h2, h3, h4, h5, false_or, List.all_eq_true] at this
      exact of_notIn (this ch hch)
    houts := by
      intro l ru h1 h2 h3 h4 h5 hr ch hch
      have := of_allL houts l ru hr
      simp only [Bool.or_eq_true, beq_iff_eq, h1, h2, h3, h4, h5, false_or, List.all_eq_true] at this
      exact of_notIn (this ch hch)
    hnd := hnd
    hext := hext
    hH := ring_T2_id }

/-- IncCmp2.Pat2 on (rs1, rs2). -/
def chkTest : Bool :=
  decide ((rs1 rules X)[X.lb]? = some (.comp [X.e] X.s fInc) ∧
    (rs2 rules X)[X.lb]? = some (.fork X.e [X.e0, X.e1]) ∧
    (rs1 rules X)[X.ld]? = some (.fork X.s [X.s0, X.y]) ∧ (rs2 rules X)[X.ld]? = some (.comp [X.e0] X.s0 fInc) ∧
    (rs1 rules X)[X.C]? = some (.comp [X.y, X.k] X.c fSltInc) ∧
    (rs2 rules X)[X.C]? = some (.comp [X.e1, X.k] X.c fSltXor) ∧
    [X.k, X.e, X.s, X.s0, X.y, X.c, X.e0, X.e1].Nodup ∧ X.lb ≠ X.ld ∧ X.lb ≠ X.C ∧ X.ld ≠ X.C) &&
  sameL (rs1 rules X) (rs2 rules X) (fun l => l == X.lb || l == X.ld || l == X.C) &&
  allL (rs1 rules X) (fun l r => l == X.lb || l == X.ld || l == X.C ||
    r.insL.all (fun ch => notIn ch [X.e, X.s, X.y, X.e0, X.e1, X.k])) &&
  allL (rs1 rules X) (fun l r => l == X.lb || l == X.ld || l == X.C ||
    r.outsL.all (fun ch => notIn ch [X.s, X.y, X.e0, X.e1, X.s0, X.c]))

theorem patTest (h : chkTest rules X = true) :
    Pat2 (rs1 rules X) (rs2 rules X) X.lb X.ld X.C X.e X.s X.s0 X.y X.c X.k X.e0 X.e1 fInc fSltInc fSltXor := by
  simp only [chkTest, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hb, hb', hd, hd', hf, hf', hnd, hbd, hbf, hdf⟩, hsame⟩, hins⟩, houts⟩ := h
  exact {
    hb := hb, hb' := hb', hd := hd, hd' := hd', hf := hf, hf' := hf'
    hsame := by
      intro l h1 h2 h3
      exact of_sameL hsame l (by simp [h1, h2, h3])
    hins := by
      intro l ru h1 h2 h3 hr ch hch
      have := of_allL hins l ru hr
      simp only [Bool.or_eq_true, beq_iff_eq, h1, h2, h3, false_or, List.all_eq_true] at this
      have := of_notIn (this ch hch)
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this
      exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2⟩
    houts := by
      intro l ru h1 h2 h3 hr ch hch
      have := of_allL houts l ru hr
      simp only [Bool.or_eq_true, beq_iff_eq, h1, h2, h3, false_or, List.all_eq_true] at this
      have := of_notIn (this ch hch)
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this
      exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2⟩
    hnd := hnd, hbd := hbd, hbf := hbf, hdf := hdf
    hH := ring_T1_id }

/-! ## The pairs, as data -/

def privB (p : Pair) (l : Nat) (r : Rule) : Bool :=
  l == p.lF || (p.hasA && l == p.lA) || l == p.lC || l == p.lK || l == p.lB ||
  (r.insL ++ r.outsL).all (fun ch => !decide (ch ∈ [p.d0, p.d, p.x, p.c, p.cb]))

theorem priv_of {rs : List Rule} (p : Pair) (h : allL rs (privB p) = true) :
    ∀ l r, rs[l]? = some r → l ≠ p.lF → (p.hasA = true → l ≠ p.lA) → l ≠ p.lC → l ≠ p.lK → l ≠ p.lB →
      ∀ ch, ch ∈ r.insL ∨ ch ∈ r.outsL → ch ≠ p.d0 ∧ ch ≠ p.d ∧ ch ≠ p.x ∧ ch ≠ p.c ∧ ch ≠ p.cb := by
  intro l r hr h1 h2 h3 h4 h5 ch hch
  have := of_allL h l r hr
  simp only [privB, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, List.all_eq_true, h1, h3, h4, h5,
    false_or, or_false] at this
  rcases this with ⟨hA, hl⟩ | hall
  · exact absurd hl (h2 hA)
  · have := hall ch (List.mem_append.mpr hch)
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, List.mem_cons, List.not_mem_nil, or_false,
      not_or] at this
    exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2⟩

/-- The structural part of `PairOK` (everything but the two value obligations). -/
def chkPair (rs : List Rule) (p : Pair) : Bool :=
  decide (rs[p.lF]? = some (.fork p.e [p.d0, p.x]) ∧
    (p.hasA = true → rs[p.lA]? = some (.comp [p.d0] p.d p.fA)) ∧
    (p.hasA = false → p.d0 = p.d) ∧
    rs[p.lC]? = some (.comp [p.x, p.k] p.c p.F) ∧
    rs[p.lK]? = some (.fork p.c p.os) ∧
    p.cb ∈ p.os ∧
    (∀ ch ∈ p.os, ch ≠ p.d0 ∧ ch ≠ p.d ∧ ch ≠ p.x ∧ ch ≠ p.c) ∧
    rs[p.lB]? = some (.branch p.cb p.d p.t p.f) ∧
    [p.e, p.d, p.x, p.c, p.cb, p.k, p.t, p.f].Nodup ∧
    (p.hasA = true → p.d0 ∉ [p.e, p.d, p.x, p.c, p.cb, p.k, p.t, p.f])) &&
  allL rs (privB p)

theorem pairOK_of {rs : List Rule} {Q : Nat → Nat → Prop} {p : Pair} (h : chkPair rs p = true)
    (hP : ∀ v w, p.F.eval [v, w] % 2 = 1 → Q p.t (p.g v)) (hfalse : ∀ v, Q p.f v) : PairOK rs Q p := by
  simp only [chkPair, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hF, hA, hA0, hC, hK, hcb, hos, hB, hnd, hnd0⟩, hpriv⟩ := h
  exact { hF := hF, hA := hA, hA0 := hA0, hC := hC, hK := hK, hcb := hcb, hos := hos, hB := hB, hnd := hnd,
          hnd0 := hnd0, priv := priv_of p hpriv, hP := hP, hfalse := hfalse }

/-! ## Rule safety, checked rule by rule -/

def safeR (r : Rule) : Bool :=
  match r with
  | .fork i os => os.all (fun o => cls X o == 0 || cls X o == cls X i)
  | .mux _ ds o _ => cls X o == 0 || ds.all (fun d => cls X d == cls X o)
  | .branch _ d t f => (cls X t == 0 || cls X t == cls X d) && (cls X f == 0 || cls X f == cls X d)
  | .comp ins o e => cls X o == 0 ||
      (cls X o == 1 && ins.length == 1 && decide (e = .un .extui 1 (.var 0))) ||
      (cls X o == 1 && decide (e = gDec) && (match ins with | [i] => cls X i == 2 | _ => false))
  | .cm _ res idx _ => cls X res == 0 && cls X idx == 0
  | .sink _ => true

theorem safeR_ok (r : Rule) (h : safeR X r = true) : RuleSafe (Q X) r := by
  cases r with
  | fork i os =>
    refine fork_safe (fun o ho v hv => ?_)
    simp only [safeR, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    rcases h o ho with h0 | h1
    · exact Q_zero h0 v
    · exact Q_cls h1.symm v hv
  | mux s ds o iw =>
    refine mux_safe (fun d hd v hv => ?_)
    simp only [safeR, Bool.or_eq_true, beq_iff_eq, List.all_eq_true] at h
    rcases h with h0 | h1
    · exact Q_zero h0 v
    · exact Q_cls (h1 d hd) v hv
  | branch c d t f =>
    refine branch_safe (fun v hv => ⟨?_, ?_⟩)
    all_goals simp only [safeR, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    · rcases h.1 with h0 | h1
      · exact Q_zero h0 v
      · exact Q_cls h1.symm v hv
    · rcases h.2 with h0 | h1
      · exact Q_zero h0 v
      · exact Q_cls h1.symm v hv
  | comp ins o e =>
    simp only [safeR, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    rcases h with (h0 | ⟨⟨h1, hl⟩, he⟩) | ⟨⟨h1, he⟩, hi⟩
    · exact comp_safe_triv (fun v => Q_zero h0 v)
    · subst he
      match ins, hl with
      | [i], _ =>
        refine comp1_safe (fun v _ => ?_)
        rw [Q_one h1]
        simp only [E.eval, UOp.ev, List.getD_cons_zero]
        exact extui_notmax v
    · subst he
      match ins, hi with
      | [i], hi =>
        simp only [beq_iff_eq] at hi
        refine comp1_safe (fun v hv => ?_)
        rw [Q_one h1]; rw [Q_two hi] at hv
        exact dec_notmax v hv
  | cm i res idx k =>
    simp only [safeR, Bool.and_eq_true, beq_iff_eq] at h
    exact cm_safe (fun v _ => Q_zero h.1 v) (Q_zero h.2 k)
  | sink i => exact sink_safe

/-! ## The whole check -/

def check : Bool :=
  chkRing rules X && chkTest rules X && chkPair (rs2 rules X) (pG X) && chkPair (rs2 rules X) (pT X) &&
  allL (rs2 rules X) (fun l r => l == X.gB || l == X.tB || safeR X r) &&
  -- value obligations of the pairs, as class facts
  (cls X X.gt == 0 || cls X X.gt == 2) && cls X X.gf == 0 &&
  (cls X X.tt == 0 || cls X X.tt == 1) && cls X X.tf == 0 &&
  -- the plain test reads two NotMax channels
  cls X X.e1 == 1 && cls X X.k == 1 &&
  -- the arguments carry no constraint
  (List.range X.na).all (fun ch => cls X ch == 0) &&
  -- internal channels start empty
  [X.ne, X.ne', X.r, X.r0, X.k, X.nb, X.nx, X.s, X.y, X.e0, X.e1, X.gd, X.gx, X.gc, X.gcb,
    X.s0, X.c, X.tcb].all (fun ch => decide (X.na ≤ ch))

/-! ## The theorem -/

theorem len_rs1 : (rs1 rules X).length = rules.length + 1 := by simp [rs1]

/-- The internal channels that must start empty. -/
def internal : List Nat := [X.ne, X.ne', X.r, X.r0, X.k, X.nb, X.nx, X.s, X.y, X.e0, X.e1, X.gd, X.gx, X.gc, X.gcb,
    X.s0, X.c, X.tcb]

/-- `check`, read as named facts. -/
structure Parts : Prop where
  ring : chkRing rules X = true
  test : chkTest rules X = true
  pg : chkPair (rs2 rules X) (pG X) = true
  pt : chkPair (rs2 rules X) (pT X) = true
  safe : allL (rs2 rules X) (fun l r => l == X.gB || l == X.tB || safeR X r) = true
  gt : cls X X.gt = 0 ∨ cls X X.gt = 2
  gf : cls X X.gf = 0
  tt : cls X X.tt = 0 ∨ cls X X.tt = 1
  tf : cls X X.tf = 0
  e1 : cls X X.e1 = 1
  k : cls X X.k = 1
  args : ∀ ch, ch < X.na → cls X ch = 0
  emp : ∀ ch ∈ internal X, X.na ≤ ch

theorem parts (h : check rules X = true) : Parts rules X := by
  simp only [check, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, fun ch hch => ?_, fun ch hch => ?_⟩
  · have := List.all_eq_true.mp h12 ch (List.mem_range.mpr hch)
    simpa using this
  · have := List.all_eq_true.mp h13 ch hch
    simpa using this

variable {rules X}

theorem emp0 (P : Parts rules X) {σ0 : Store Nat Nat} (h0 : ∀ ch, X.na ≤ ch → σ0 ch = []) :
    ∀ ch ∈ internal X, σ0 ch = [] := fun ch hc => h0 ch (P.emp ch hc)

theorem inv_rs2 (P : Parts rules X) {σ0 : Store Nat Nat} (h0 : ∀ ch, X.na ≤ ch → σ0 ch = []) :
    ∀ m s, Run (step (graph (rs2 rules X))) σ0 m s → SInvS (Q X) s := by
  intro m s hr
  have hS : SInv (Q X) σ0 := by
    intro ch v hv
    by_cases a : ch < X.na
    · exact Q_zero (P.args ch a) v
    rw [h0 ch (by omega)] at hv; cases hv
  have hsafe : ∀ l r, (rs2 rules X)[l]? = some r → (∀ p ∈ [pG X, pT X], l ≠ p.lB) → RuleSafe (Q X) r := by
    intro l r hr hl
    have := of_allL P.safe l r hr
    have h1 : l ≠ X.gB := hl (pG X) (by simp)
    have h2 : l ≠ X.tB := hl (pT X) (by simp)
    simp only [Bool.or_eq_true, beq_iff_eq, h1, h2, false_or] at this
    exact safeR_ok X r this
  have okG : PairOK (rs2 rules X) (Q X) (pG X) := by
    refine pairOK_of P.pg (fun v w h => ?_) (fun v => Q_zero P.gf v)
    change E.eval [v, w] (E.bin (BOp.cmpi Pred.sgt) 32 (E.var 0) (E.var 1)) % 2 = 1 at h
    change Q X X.gt v
    simp only [E.eval, BOp.ev, List.getD_cons_zero, List.getD_cons_succ] at h
    rcases P.gt with g0 | g2
    · exact Q_zero g0 v
    · exact (Q_two g2 v).mpr (sgt_true v w h)
  have okT : PairOK (rs2 rules X) (Q X) (pT X) := by
    refine pairOK_of P.pt (fun v w h => ?_) (fun v => Q_zero P.tf v)
    change fSltXor.eval [v, w] % 2 = 1 at h
    change Q X X.tt (fInc.eval [v])
    rcases P.tt with t0 | t1
    · exact Q_zero t0 _
    · exact (Q_one t1 _).mpr (test_true_inc v w h)
  have he := emp0 P h0
  have := chan_inv hsafe (by
      intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact okG
      · exact okT) hS (by
      intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact ⟨he _ (by simp [internal, pG]), he _ (by simp [internal, pG]), he _ (by simp [internal, pG]),
          he _ (by simp [internal, pG]), he _ (by simp [internal, pG])⟩
      · exact ⟨he _ (by simp [internal, pT]), he _ (by simp [internal, pT]), he _ (by simp [internal, pT]),
          he _ (by simp [internal, pT]), he _ (by simp [internal, pT])⟩) hr
  exact this.1

theorem agree (P : Parts rules X) (a b : Nat) (ha : Q X X.e1 a) (hb : Q X X.k b) :
    fSltXor.eval [a, b] = fSlt.eval [a, b] :=
  xor_eq_plain a b ((Q_one P.e1 a).mp ha) ((Q_one P.k b).mp hb)

theorem hC2 (P : Parts rules X) : (rs2 rules X)[X.C]? = some (.comp [X.e1, X.k] X.c fSltXor) :=
  (patTest rules X P.test).hf'

theorem hC2p (P : Parts rules X) : (rs2p rules X)[X.C]? = some (.comp [X.e1, X.k] X.c fSlt) := by
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp (hC2 P)
  simp only [rs2p]; rw [List.getElem?_set_self hlt]

theorem hsame2 : ∀ l, l ≠ X.C → (rs2p rules X)[l]? = (rs2 rules X)[l]? := by
  intro l hl; simp only [rs2p]; rw [List.getElem?_set_ne (by omega)]

/-- **The pass, forward.** Every complete run of `rules` is matched by a complete run of `rs2p rules X`. -/
theorem plain_forward (h : check rules X = true) {σ0 t : Store Nat Nat} {n : Nat}
    (h0 : ∀ ch, X.na ≤ ch → σ0 ch = [])
    (hr : Run (step (graph rules)) σ0 n t) (ht : Terminal (step (graph rules)) t) :
    ∃ t' m, Run (step (graph (rs2p rules X))) σ0 m t' ∧ Terminal (step (graph (rs2p rules X))) t' ∧
      ∀ ch, ch ∉ changed X → t' ch = t ch := by
  have P := parts rules X h
  have he := emp0 P h0
  obtain ⟨t1, m1, r1, ht1, o1⟩ := RingMap.forward (patRing rules X P.ring)
    (fun ch hc => he ch (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      simp only [internal, List.mem_cons, List.not_mem_nil, or_false]
      rcases hc with h | h | h | h | h | h <;> simp [h])) hr ht
  obtain ⟨t2, m2, r2, ht2, o2⟩ := forward2 (patTest rules X P.test)
    ⟨he _ (by simp [internal]), he _ (by simp [internal]), he _ (by simp [internal]), he _ (by simp [internal])⟩
    r1 ht1
  have hinv := inv_rs2 P h0
  refine ⟨t2, m2, swap_run (hC2 P) (hC2p P) hsame2 (agree P) hinv r2,
    (swap_terminal (hC2 P) (hC2p P) hsame2 (agree P) (hinv m2 t2 r2)).mpr ht2, fun ch hc => ?_⟩
  simp only [changed, List.mem_cons, List.not_mem_nil, or_false, not_or] at hc
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hc
  rw [o2 ch h8 h9 h10 h11, o1 ch (by simp [h1, h2, h3, h4, h5, h6, h7])]

/-- **The pass, backward.** Every complete run of `rs2p rules X` is matched by a complete run of `rules`. -/
theorem plain_backward (h : check rules X = true) {σ0 t' : Store Nat Nat} {n : Nat}
    (h0 : ∀ ch, X.na ≤ ch → σ0 ch = [])
    (hr : Run (step (graph (rs2p rules X))) σ0 n t') (ht : Terminal (step (graph (rs2p rules X))) t') :
    ∃ t m, Run (step (graph rules)) σ0 m t ∧ Terminal (step (graph rules)) t ∧
      ∀ ch, ch ∉ changed X → t ch = t' ch := by
  have P := parts rules X h
  have he := emp0 P h0
  have hinv := inv_rs2 P h0
  have r2 := swap_run_back (hC2 P) (hC2p P) hsame2 (agree P) hinv hr
  have ht2 := (swap_terminal (hC2 P) (hC2p P) hsame2 (agree P) (hinv n t' r2)).mp ht
  obtain ⟨t1, m1, r1, ht1, o1⟩ := backward2 (patTest rules X P.test)
    ⟨he _ (by simp [internal]), he _ (by simp [internal]), he _ (by simp [internal]), he _ (by simp [internal])⟩
    r2 ht2
  obtain ⟨t0, m0, r0, ht0, o0⟩ := RingMap.backward (patRing rules X P.ring)
    (fun ch hc => he ch (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      simp only [internal, List.mem_cons, List.not_mem_nil, or_false]
      rcases hc with h | h | h | h | h | h <;> simp [h])) r1 ht1
  refine ⟨t0, m0, r0, ht0, fun ch hc => ?_⟩
  simp only [changed, List.mem_cons, List.not_mem_nil, or_false, not_or] at hc
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hc
  rw [o0 ch (by simp [h1, h2, h3, h4, h5, h6, h7]), o1 ch h8 h9 h10 h11]

end Formal.Rewrite.PlainPass
