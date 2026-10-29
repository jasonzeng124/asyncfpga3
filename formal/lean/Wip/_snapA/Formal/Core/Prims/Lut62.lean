import Formal.Core.Lut
import Formal.Core.Prims.Muxf

/-!
# Formal.Core.Prims.Lut62 — LUT6_2: O5 and O6 as one shared mux tree

Shard A, probe PrimsComb (north star 1). Core Lean only (no Mathlib).
Notes: `formal/notes/A-prims-comb.md`.

## Model

A 7-series 6-input LUT is one 64-cell mux tree. Its last rank is a 2:1 mux on
`A6` (`I5`) between two 32-cell sub-trees over `A1..A5`; `O5` is the output of
the LOWER sub-tree (`INIT[31:0]`), `O6` the output of the `A6` mux (UG474,
"Look-Up Table"; the fractured mode ties `A6` high so that `O6` reads
`INIT[63:32]`). Here:

* `lo5 L`, `hi5 L` : the two 5-input sub-trees (`Lut 5` on `INIT[31:0]`,
  `INIT[63:32]`), Kleene-evaluated as Core's mux tree (`Lut.keval`).
* `o6Tree L v = mux2 (v 5) (lo5.keval ..) (hi5.keval ..)`: the physical order,
  `A6` at the root. `o5Tree L v = lo5.keval ..` is the SAME sub-tree value
  (`o5_is_o6_branch`): there is one tree, not two LUTs.

## Results

* `o6Tree_eq_keval` : the A6-rooted tree equals Core's `Lut62.o6.keval` (whose
  mux tree has `A1` at the root), for every INIT and every Kleene input. So the
  physical rank order is irrelevant to the static Kleene value, and shard C's
  `o6KL` reading is the physical one.
* `o5Tree_eq_keval` : `o5Tree = Lut62.o5.keval` (definitional).
* `o6_tied` : with `A6 = 1` (fractured), `O6` is `hi5` exactly (no merge), and
  `o6_A6_X` : an `A6` in transit gives `merge O5 O6hi` (hazard-free iff the two
  halves agree).
* `shared_X` : the shared read. An `X` on one of `A1..A5` reaches BOTH outputs
  whenever each half depends on that pin there (example `latch_pair`: the
  bd_latch W=32 pair cell). Timing of the two outputs is per-output
  (`XrayData.lut5Arc` / `lut6Arc`), see `Hops.lean`.

## Not covered
Timing inside the tree (per-rank skew, `Formal.Core.LutTree`), charge sharing,
and whether the silicon's tree is exactly this (H_KLEENE_LUT, as for every LUT).
-/

namespace Formal.Core.Prims

open Formal.Core K3

namespace L62

/-- The first five pins `A1..A5` of a 6-pin vector. -/
def first5 {α : Type} (v : Fin 6 → α) : Fin 5 → α := fun i => v ⟨i.val, by omega⟩

/-- Lower 5-input sub-tree (`INIT[31:0]`): Core's `Lut62.o5`. -/
def lo5 (L : Lut62) : Lut 5 := L.o5

/-- Upper 5-input sub-tree (`INIT[63:32]`). -/
def hi5 (L : Lut62) : Lut 5 := ⟨(L.init >>> 32).setWidth 32⟩

/-- `O6` as the physical tree: the `A6` mux over the two sub-trees. -/
def o6Tree (L : Lut62) (v : Fin 6 → K3) : K3 :=
  mux2 (v 5) ((lo5 L).keval (first5 v)) ((hi5 L).keval (first5 v))

/-- `O5`: the lower sub-tree's output. -/
def o5Tree (L : Lut62) (v : Fin 6 → K3) : K3 := (lo5 L).keval (first5 v)

/-- One tree: `O5` is the `A6 = 0` branch of the `O6` mux. -/
theorem o5_is_o6_branch (L : Lut62) (v : Fin 6 → K3) :
    o6Tree L v = mux2 (v 5) (o5Tree L v) ((hi5 L).keval (first5 v)) := rfl

theorem o5Tree_eq_keval (L : Lut62) (v : Fin 6 → K3) : o5Tree L v = L.o5.keval (first5 v) := rfl

/-! ### Address and entry lemmas -/

/-- `x` from its first five pins and `A6`. -/
def snoc5 {α : Type} (y : Fin 5 → α) (b : α) : Fin 6 → α := fun i =>
  if h : i.val < 5 then y ⟨i.val, h⟩ else b

theorem first5_snoc5 {α : Type} (y : Fin 5 → α) (b : α) : first5 (snoc5 y b) = y := by
  funext i; simp [first5, snoc5, i.isLt]

theorem snoc5_5 {α : Type} (y : Fin 5 → α) (b : α) : snoc5 y b 5 = b := rfl

theorem snoc5_eta {α : Type} (x : Fin 6 → α) : snoc5 (first5 x) (x 5) = x := by
  funext i
  unfold snoc5 first5
  split
  · rfl
  · next h => congr 1; ext; simp; omega

theorem addr_split : ∀ x : Fin 6 → Bool, addr x = addr (first5 x) + 32 * (x 5).toNat := by
  decide

theorem lo5_entry (L : Lut62) {a : Nat} (h : a < 32) : (lo5 L).entry a = L.init.getLsbD a := by
  simp [lo5, Lut62.o5, Lut.entry, BitVec.getLsbD_setWidth, h]

theorem hi5_entry (L : Lut62) {a : Nat} (h : a < 32) : (hi5 L).entry a = L.init.getLsbD (32 + a) := by
  simp [hi5, Lut.entry, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, h]

/-- Boolean `O6` splits on `A6`. -/
theorem o6_eval_split (L : Lut62) (x : Fin 6 → Bool) :
    L.o6.eval x = bmux (x 5) ((lo5 L).eval (first5 x)) ((hi5 L).eval (first5 x)) := by
  have ha := addr_lt (first5 x)
  simp only [Lut.eval, Lut62.o6, Lut.entry, addr_split x]
  cases x 5
  · simp [bmux, ← lo5_entry L ha, Lut.entry]
  · simp only [bmux, Bool.toNat_true, ite_true]
    rw [← Lut.entry, ← Lut.entry, hi5_entry L ha]
    · show L.init.getLsbD _ = _
      congr 1; omega

theorem consistent_split {v : Fin 6 → K3} {x : Fin 6 → Bool} :
    Consistent v x ↔ Consistent (first5 v) (first5 x) ∧ v 5 ⊑ ofBool (x 5) := by
  constructor
  · intro h; exact ⟨fun i => h _, h 5⟩
  · intro ⟨h1, h2⟩ i
    by_cases hi : i.val < 5
    · have := h1 ⟨i.val, hi⟩
      simp only [first5] at this
      have e : (⟨i.val, by omega⟩ : Fin 6) = i := Fin.ext rfl
      rw [e] at this; exact this
    · have e : i = 5 := Fin.ext (by have := i.isLt; simp; omega)
      rw [e]; exact h2

/-- A Kleene value is determined by which Booleans it equals. -/
theorem K3_ext {a b : K3} (h : ∀ c : Bool, a = ofBool c ↔ b = ofBool c) : a = b := by
  cases a <;> cases b <;> first | rfl | (have := h false; simp_all) | (have := h true; simp_all)

theorem mux2_eq_ofBool_iff (s a b : K3) (c : Bool) :
    mux2 s a b = ofBool c ↔ (s ⊑ ofBool false → a = ofBool c) ∧ (s ⊑ ofBool true → b = ofBool c) := by
  cases s <;> cases a <;> cases b <;> cases c <;> decide

/-- **The A6-rooted physical tree equals Core's (A1-rooted) Kleene LUT6.** -/
theorem o6Tree_eq_keval (L : Lut62) (v : Fin 6 → K3) : o6Tree L v = L.o6.keval v := by
  apply K3_ext; intro c
  rw [Lut.keval_eq_ofBool_iff, o6Tree, mux2_eq_ofBool_iff, Lut.keval_eq_ofBool_iff,
    Lut.keval_eq_ofBool_iff]
  constructor
  · intro ⟨h0, h1⟩ x hx
    rw [consistent_split] at hx
    rw [o6_eval_split]
    cases e : x 5
    · rw [e] at hx; exact h0 hx.2 _ hx.1
    · rw [e] at hx; exact h1 hx.2 _ hx.1
  · intro h
    refine ⟨fun hs y hy => ?_, fun hs y hy => ?_⟩
    · have := h (snoc5 y false) (consistent_split.mpr ⟨by rw [first5_snoc5]; exact hy, hs⟩)
      rw [o6_eval_split, first5_snoc5, snoc5_5] at this; exact this
    · have := h (snoc5 y true) (consistent_split.mpr ⟨by rw [first5_snoc5]; exact hy, hs⟩)
      rw [o6_eval_split, first5_snoc5, snoc5_5] at this; exact this

/-- Fractured use (`A6` tied 1): `O6` is the upper sub-tree, exactly. -/
theorem o6_tied (L : Lut62) (v : Fin 6 → K3) (h : v 5 = .one) :
    L.o6.keval v = (hi5 L).keval (first5 v) := by
  rw [← o6Tree_eq_keval, o6Tree, h]; rfl

/-- `A6` in transit: `O6` is `merge` of the two halves (hazard-free exactly when
they agree). -/
theorem o6_A6_X (L : Lut62) (v : Fin 6 → K3) (h : v 5 = .X) :
    L.o6.keval v = merge (o5Tree L v) ((hi5 L).keval (first5 v)) := by
  rw [← o6Tree_eq_keval, o6Tree, h]; rfl

/-! ### The shared read: one input X reaches both outputs -/

/-- The library's bd_latch W=32 pair cell (`Init.latch_pair`, INIT
`0xFF33CC00B8B8B8B8`): pins `I0..I4` = `di, en, qi, dj, qj`, `I5` tied 1.
With `en = X` and the data pins disagreeing with the held values, BOTH outputs
are `X`: one buffered pin feeds both halves. -/
theorem shared_X :
    let v : Fin 6 → K3 := kvec [.one, .X, .zero, .one, .zero, .one] 6
    o5Tree Init.latch_pair v = .X ∧ Init.latch_pair.o6.keval v = .X := by
  decide

end L62

end Formal.Core.Prims
