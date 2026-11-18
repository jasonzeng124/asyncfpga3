import Formal.Rewrite.CountloopHw
import Formal.Rewrite.RingMap
import Formal.Rewrite.IncCmp2
import Formal.Rewrite.IncCmpArith

/-!
# Formal.Rewrite.CountloopRewrite — the general loop-test rewrite, applied to countloop's imported graph (shard A, 2026-11-18)

**Problem, plainly.** countloop (`for (i = 0; i < n; i++) s = (s + i) ^ a`) is where research's automatic flow is
furthest behind Dynamatic (3.00x). Its loop test is `slt(i + 1, n)`, `n` circulating on a ring. Do `RingMap` and
`IncCmp2` actually apply to the graph bdc builds for it, and what do they then prove?

**Proved** (`same_forward`, `same_backward`): with `rules` = dfimport's export of research's frontend fixture
(`CountloopHw`, md5 edcfff62 of the MLIR), `rs1` = `rules` with the ring carrying `m = n - 1` (a new `addi n, -1` on
the ring's entry, the compare reading `m + 1`), and `rs2` = `rs1` with the test moved before the increment
(`slt(i, m) xor (i = INT_MAX) xor (m = INT_MAX)`): from any store whose ring and internal channels are empty, every
complete run of `rules` is matched by a complete run of `rs2` ending in the same store outside the ring and the
pattern's internal channels (in particular the same output token on `chOut`), and vice versa. Every pattern
hypothesis is discharged by `decide` on the concrete rule lists.

**Not covered:** that a rewrite tool's MLIR output imports to exactly `rs2` (here `rs2` is built in Lean from
`rules`); gates and delays.
-/

namespace Formal.Rewrite.CountloopRewrite

open Formal.Net.Kahn Formal.Net.GcdHw Formal.Rewrite.IncCmp Formal.Rewrite.CountloopHw

/-- The ring rewrite (RingMap): mux3's entry reads the new channel 67, the compare reads `m + 1`, rule 42 decrements. -/
def rs1 : List Rule :=
  (rules.set 20 (.mux 41 [67, 42] 43 1)).set 28 (.comp [52, 45] 53 fSltInc) ++ [.comp [24] 67 gDec]

/-- The test rewrite (IncCmp2): fork the counter (31) to 68 / 69, increment from 68, test from 69. -/
def rs2 : List Rule :=
  ((rs1.set 26 (.fork 31 [68, 69])).set 27 (.comp [68] 51 fInc)).set 28 (.comp [69, 45] 53 fSltXor)

theorem len_rules : rules.length = 42 := by decide +kernel
theorem len_rs1 : rs1.length = 43 := by decide +kernel
theorem len_rs2 : rs2.length = 43 := by decide +kernel

/-- Check a per-label property on every label of a list. -/
theorem of_check {rs : List Rule} (p : Nat → Rule → Bool)
    (h : (List.range rs.length).all (fun l => match rs[l]? with | some r => p l r | none => true) = true) :
    ∀ l r, rs[l]? = some r → p l r = true := by
  intro l r hr
  have hl : l < rs.length := by
    rcases Nat.lt_or_ge l rs.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hr; cases hr
  have := List.all_eq_true.mp h l (List.mem_range.mpr hl)
  rw [hr] at this; exact this

theorem same_of_check {rs rs' : List Rule} (n : Nat) (hn : rs.length ≤ n) (hn' : rs'.length ≤ n) (ex : Nat → Bool)
    (h : (List.range n).all (fun l => ex l || decide (rs'[l]? = rs[l]?)) = true) :
    ∀ l, ex l = false → rs'[l]? = rs[l]? := by
  intro l hl
  rcases Nat.lt_or_ge l n with h1 | h1
  · have := List.all_eq_true.mp h l (List.mem_range.mpr h1)
    simp only [hl, Bool.false_or, decide_eq_true_eq] at this; exact this
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

def ring : List Nat := [24, 67, 43, 44, 45, 42, 62]

theorem patRing : RingMap.Pat rules rs1 20 21 35 36 28 42 41 24 67 43 44 45 42 62 55 52 53 1 fSlt fSltInc gDec where
  hM := by decide +kernel
  hM' := by decide +kernel
  hF := by decide +kernel
  hF' := by decide +kernel
  hB := by decide +kernel
  hB' := by decide +kernel
  hS := by decide +kernel
  hS' := by decide +kernel
  hC := by decide +kernel
  hC' := by decide +kernel
  hD := by decide +kernel
  hD' := by decide +kernel
  hsame := by
    intro l h1 h2 h3 h4 h5 h6
    refine same_of_check 43 (by rw [len_rules]; omega) (by rw [len_rs1]; exact Nat.le_refl _)
      (fun l => l == 20 || l == 21 || l == 35 || l == 36 || l == 28 || l == 42) (by decide +kernel) l ?_
    simp [h1, h2, h3, h4, h5, h6]
  hins := by
    intro l ru h1 h2 h3 h4 h5 hr ch hch
    have := of_check (rs := rules)
      (fun l r => l == 20 || l == 21 || l == 35 || l == 36 || l == 28 || r.insL.all (fun ch => !decide (ch ∈ ring)))
      (by decide +kernel) l ru hr
    simp only [Bool.or_eq_true, beq_iff_eq, h1, h2, h3, h4, h5, false_or, List.all_eq_true] at this
    have := this ch hch
    simpa [ring] using this
  houts := by
    intro l ru h1 h2 h3 h4 h5 hr ch hch
    have := of_check (rs := rules)
      (fun l r => l == 20 || l == 21 || l == 35 || l == 36 || l == 28 ||
        r.outsL.all (fun ch => !decide (ch ∈ ring.tail)))
      (by decide +kernel) l ru hr
    simp only [Bool.or_eq_true, beq_iff_eq, h1, h2, h3, h4, h5, false_or, List.all_eq_true] at this
    have := this ch hch
    simpa [ring] using this
  hnd := by decide +kernel
  hext := by decide +kernel
  hH := ring_T2_id

theorem patTest : Pat2 rs1 rs2 26 27 28 31 50 51 52 53 45 68 69 fInc fSltInc fSltXor where
  hb := by decide +kernel
  hb' := by decide +kernel
  hd := by decide +kernel
  hd' := by decide +kernel
  hf := by decide +kernel
  hf' := by decide +kernel
  hsame := by
    intro l h1 h2 h3
    refine same_of_check 43 (by rw [len_rs1]; exact Nat.le_refl _) (by rw [len_rs2]; exact Nat.le_refl _)
      (fun l => l == 26 || l == 27 || l == 28) (by decide +kernel) l ?_
    simp [h1, h2, h3]
  hins := by
    intro l ru h1 h2 h3 hr ch hch
    have := of_check (rs := rs1)
      (fun l r => l == 26 || l == 27 || l == 28 ||
        r.insL.all (fun ch => !decide (ch ∈ [31, 50, 52, 68, 69, 45])))
      (by decide +kernel) l ru hr
    simp only [Bool.or_eq_true, beq_iff_eq, h1, h2, h3, false_or, List.all_eq_true] at this
    have := this ch hch
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, List.mem_cons, List.not_mem_nil, or_false,
      not_or] at this
    omega
  houts := by
    intro l ru h1 h2 h3 hr ch hch
    have := of_check (rs := rs1)
      (fun l r => l == 26 || l == 27 || l == 28 ||
        r.outsL.all (fun ch => !decide (ch ∈ [50, 52, 68, 69, 51, 53])))
      (by decide +kernel) l ru hr
    simp only [Bool.or_eq_true, beq_iff_eq, h1, h2, h3, false_or, List.all_eq_true] at this
    have := this ch hch
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, List.mem_cons, List.not_mem_nil, or_false,
      not_or] at this
    omega
  hnd := by decide +kernel
  hbd := by decide
  hbf := by decide
  hdf := by decide
  hH := ring_T1_id

/-- The channels the two rewrites may leave different: the ring, its new entry, and the test's internal channels. -/
def changed : List Nat := [24, 67, 43, 44, 45, 42, 62, 50, 52, 68, 69]

/-- Original -> rewritten: every complete run of countloop's graph is matched by one of the rewritten graph. -/
theorem same_forward {σ0 t : Store Nat Nat} {n : Nat} (h0 : ∀ ch ∈ changed.tail, σ0 ch = [])
    (hr : Run (step (graph rules)) σ0 n t) (ht : Terminal (step (graph rules)) t) :
    ∃ t' m, Run (step (graph rs2)) σ0 m t' ∧ Terminal (step (graph rs2)) t' ∧
      ∀ ch, ch ∉ changed → t' ch = t ch := by
  obtain ⟨t1, m1, r1, ht1, o1⟩ := RingMap.forward patRing
    (fun ch hc => h0 ch (by simp [changed] at hc ⊢; omega)) hr ht
  obtain ⟨t2, m2, r2, ht2, o2⟩ := forward2 patTest
    ⟨h0 50 (by simp [changed]), h0 52 (by simp [changed]), h0 68 (by simp [changed]), h0 69 (by simp [changed])⟩ r1 ht1
  refine ⟨t2, m2, r2, ht2, fun ch hc => ?_⟩
  simp only [changed, List.mem_cons, List.not_mem_nil, or_false, not_or] at hc
  rw [o2 ch (by omega) (by omega) (by omega) (by omega), o1 ch (by simp; omega)]

/-- Rewritten -> original. -/
theorem same_backward {σ0 t' : Store Nat Nat} {n : Nat} (h0 : ∀ ch ∈ changed.tail, σ0 ch = [])
    (hr : Run (step (graph rs2)) σ0 n t') (ht : Terminal (step (graph rs2)) t') :
    ∃ t m, Run (step (graph rules)) σ0 m t ∧ Terminal (step (graph rules)) t ∧
      ∀ ch, ch ∉ changed → t ch = t' ch := by
  obtain ⟨t1, m1, r1, ht1, o1⟩ := backward2 patTest
    ⟨h0 50 (by simp [changed]), h0 52 (by simp [changed]), h0 68 (by simp [changed]), h0 69 (by simp [changed])⟩ hr ht
  obtain ⟨t2, m2, r2, ht2, o2⟩ := RingMap.backward patRing
    (fun ch hc => h0 ch (by simp [changed] at hc ⊢; omega)) r1 ht1
  refine ⟨t2, m2, r2, ht2, fun ch hc => ?_⟩
  simp only [changed, List.mem_cons, List.not_mem_nil, or_false, not_or] at hc
  rw [o2 ch (by simp; omega), o1 ch (by omega) (by omega) (by omega) (by omega)]

/-- The output channel is not among the changed ones. -/
theorem out_kept : chOut ∉ changed := by decide

end Formal.Rewrite.CountloopRewrite
