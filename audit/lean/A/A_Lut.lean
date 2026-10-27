import Formal.Core.Kleene
import Formal.Core.Lut
import Formal.Core.LutTree
import Formal.Core.Ternary

/-!
# Audit shard A: LUT / Kleene / LutTree / Ternary (core-Lean modules)

Non-vacuity witnesses, hypothesis-dropping checks and axiom prints for the
headline theorems in Formal/Core/{Lut,LutTree,Ternary}.lean.
-/

namespace Audit.A

open Formal.Core

/-! ## Lut.no_static_hazard_single: concrete instance on bd_c2 -/

-- a falls 1 -> 0 with b = 0, q = 0, rst = 0: output 0 before and after.
example : Init.bd_c2.keval (setAt (K3.ofBoolVec (bvec [true, false, false, false, false, false] 6)) 0 K3.X)
    = K3.ofBool (Init.bd_c2.eval (bvec [true, false, false, false, false, false] 6)) :=
  Init.bd_c2.no_static_hazard_single _ 0 (by decide)

-- and the hypothesis is satisfiable but not trivial: the opposite (b rises
-- with a = 1, q = 0) changes the output and the Kleene value is X.
example : Init.bd_c2.keval (setAt (K3.ofBoolVec (bvec [true, false, false, false, false, false] 6)) 1 K3.X)
    = K3.X :=
  Init.bd_c2.single_change_visible _ 1 (by decide)

/-! ## LutTree.sic_glitch_free: a concrete PhysTree satisfying ALL hypotheses -/

section Tree
open Formal.Core.LutTree

/-- AND2 tree, root pin A (level 0) steady 0; leaf pin B (level 1) falls
1 -> X -> 0 (slowly, through a mid-rail dwell). -/
def pinsW : Nat → Time → LutTree.K3
  | 0, _ => .zero
  | _, τ => if τ < 5 then .one else if τ < 8 then .X else .zero

def W : PhysTree 2 := exactTree 2 andInit pinsW (fun _ => 3) (fun _ _ => 2)

theorem W_abs : W.Abstracts (PhysTree.mergeK [false, true] [false, false]) := by
  refine ⟨rfl, ?_⟩
  intro i h τ
  match i, h with
  | 0, _ => exact Or.inr rfl
  | 1, _ => exact Or.inl rfl

/-- All hypotheses of `sic_glitch_free` hold at once for `W`. -/
theorem W_sic (τ : Time) : W.y [] τ = LutTree.K3.ofBool false :=
  W.sic_glitch_free (exact_H_sram _ _ _ _ _) (exact_H_mux _ _ _ _ _)
    [false, true] [false, false] rfl (by decide) W_abs false rfl rfl τ

/-- The pin really moves (the witness is not a static input). -/
example : pinsW 1 0 = .one ∧ pinsW 1 6 = .X ∧ pinsW 1 9 = .zero := by decide

/-- Dropping `H_mux_kleene`: a tree with SRAM leaves and the same pin
abstraction but an arbitrary root waveform violates the conclusion. -/
def Bad : PhysTree 2 where
  init := andInit
  pin := pinsW
  dsel := fun _ => 0
  ddat := fun _ _ => 0
  y := fun p τ => if p.length = 2 then LutTree.K3.ofBool (andInit p)
                  else if τ = 0 then .one else .zero

example : Bad.H_sram := by
  intro p hp τ; simp [Bad, hp]

example : Bad.Abstracts (PhysTree.mergeK [false, true] [false, false]) := by
  refine ⟨rfl, ?_⟩
  intro i h τ
  match i, h with
  | 0, _ => exact Or.inr rfl
  | 1, _ => exact Or.inl rfl

example : Bad.y [] 0 ≠ LutTree.K3.ofBool false := by decide

end Tree

/-! ## Ternary: all hypotheses of settleResultB / noGlitchA at once -/

section Tern
open Formal.Core.Ternary

/-- Inputs: (a,b,rst) = (1,0,0) until t = 2, then b rises. -/
def cIn (t : Nat) : Fin 3 → Bool :=
  if t < 2 then inp true false false else flip (inp true false false) 1

/-- Unit-delay GMW run of bd_c2 from q = 0. -/
def sig : Nat → Unit → Bool
  | 0 => fun _ => false
  | t + 1 => fun i => bdc2Net.fb (cIn t) (sig t) i

theorem cIn_hc (t : Nat) (x : Fin 3) :
    cIn t x = inp true false false x ∨ cIn t x = flip (inp true false false) 1 x := by
  unfold cIn; split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem sig_causal : Causal bdc2Net cIn sig :=
  gmw_causal _ _ _ (fun _ _ => Or.inr rfl)

theorem sig_stale : Stale bdc2Net cIn sig 1 := by
  intro t i ht
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
  exact ⟨fun _ => u, fun _ => u, fun _ => ⟨by simp, by simp⟩,
    fun _ => ⟨by simp, by simp⟩, rfl⟩

theorem sig_settles : ∀ t, 2 + 1 * 1 ≤ t → sig t () = true :=
  bdc2_settles true false false false 1 true (by decide) cIn sig cIn_hc 2
    (fun t ht => by unfold cIn; rw [ite_eq_right_iff.mpr (by omega)]) sig_causal 1 sig_stale rfl

-- the run really moves: q is 0 early and 1 later.
example : sig 2 () = false ∧ sig 4 () = true := by decide

/-- noGlitchA / bdc2_no_static_hazard witness: a falls (a,b,rst = 1,0,0 -> 0,0,0)
with q = 0; the stable-state hypothesis and `hsame` both hold. -/
def cIn2 (t : Nat) : Fin 3 → Bool :=
  if t < 3 then inp true false false else flip (inp true false false) 0
def sig2 : Nat → Unit → Bool
  | 0 => fun _ => false
  | t + 1 => fun i => bdc2Net.fb (cIn2 t) (sig2 t) i

theorem sig2_ok : ∀ t, sig2 t () = false :=
  bdc2_no_static_hazard true false false false 0 (by decide) (by decide) cIn2 sig2
    (fun t x => by unfold cIn2; split <;> simp)
    (gmw_causal _ _ _ (fun _ _ => Or.inr rfl)) rfl

end Tern

/-! ## Axioms -/

#print axioms Formal.Core.Lut.keval_eq_kevalSpec
#print axioms Formal.Core.Lut.no_static_hazard_single
#print axioms Formal.Core.Init.bd_c2_two_change_hazard
#print axioms Formal.Core.Init.bd_c2_eval
#print axioms Formal.Core.Init.arb_state_q
#print axioms Formal.Core.Init.datamux_pair_zj
#print axioms Formal.Core.LutTree.evalTree_eq_tableEval
#print axioms Formal.Core.LutTree.PhysTree.sic_glitch_free
#print axioms Formal.Core.Ternary.soundA
#print axioms Formal.Core.Ternary.settleB
#print axioms Formal.Core.Ternary.bdc2_single_input_ok
#print axioms Formal.Core.Ternary.bdc2_no_static_hazard
#print axioms W_sic
#print axioms sig_settles
#print axioms sig2_ok

end Audit.A
