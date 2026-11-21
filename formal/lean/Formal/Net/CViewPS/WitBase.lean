import Formal.Net.CViewPS.P1Defs

/-!
# Witness behaviours with at most one transition per node (shard C)

**Problem.** The zero-pair theorems are implications from `Behaves`. Are their hypotheses satisfiable
for THE target? A witness is a concrete behaviour. Here: every node is described by an `Option Nat`
code (`sig1`): `none` is constant 0; `some b` with `b < 2` is constant `b`; `some (2·(T+1) + b)` is
`b` before `T` and `¬b` from `T` on. Every pin is read at its `FAST_MIN` (read time `t - fmin`,
admissible at `p1`, corner 0). `gateW` checks a gate's equation at its start and at every
breakpoint (its output's transition, each input transition shifted by the pin delay);
`gateOK_of_gateW` proves that this finite check gives `Spec.GateOK p1 0` for all time.
-/

namespace Formal.Net.CViewPS
open Formal.Target Formal.Timing.SpecSettle Formal.Timing.SpecChain Formal.Timing.SpecLoop

def sig1 : Option Nat → Sig
  | none => fun _ => false
  | some k => fun t => if k < 2 then k == 1 else (k % 2 == 1) != decide (k / 2 - 1 ≤ t)

/-- The transition time, if any. -/
def thr : Option Nat → Option Nat
  | some k => if k < 2 then none else some (k / 2 - 1)
  | none => none

theorem sig1_eq (e : Option Nat) (s s' : Nat) (h : ∀ θ, thr e = some θ → (θ ≤ s ↔ θ ≤ s')) :
    sig1 e s = sig1 e s' := by
  cases e with
  | none => rfl
  | some k =>
    simp only [sig1]
    split
    · rfl
    · rename_i hk
      have := h (k / 2 - 1) (by simp [thr, hk])
      by_cases h1 : k / 2 - 1 ≤ s
      · simp [h1, this.mp h1]
      · have h2 : ¬ k / 2 - 1 ≤ s' := fun h' => h1 (this.mpr h')
        simp [h1, h2]

/-- The breakpoints of a gate: its output's transition and each input transition plus the pin's
`fmin`. -/
def bps (enc : Nat → Option Nat) (g : Gate) : List Nat :=
  ((thr (enc g.out)).toList) ++
  (List.range g.k).flatMap fun i => ((thr (enc (g.ins.getD i 0))).map (· + (g.arcs.getD i default).fmin)).toList

/-- The gate equation at time `τ` with reads at `τ - fmin`. -/
def eqAt (enc : Nat → Option Nat) (g : Gate) (τ : Nat) : Bool :=
  sig1 (enc g.out) τ == g.init.testBit (addr g.k fun i => sig1 (enc (g.ins.getD i 0)) (τ - (g.arcs.getD i default).fmin))

/-- The finite check: at the gate's start and at every breakpoint past it. -/
def gateW (enc : Nat → Option Nat) (g : Gate) : Bool :=
  (startN g :: bps enc g).all fun τ => decide (τ < startN g) || eqAt enc g τ

/-- The last checkpoint not after `t`. -/
def lastBp (st t : Nat) : List Nat → Nat
  | [] => st
  | θ :: Θ => if θ ≤ t then max θ (lastBp st t Θ) else lastBp st t Θ

theorem lastBp_spec (st t : Nat) (hst : st ≤ t) : ∀ Θ : List Nat,
    st ≤ lastBp st t Θ ∧ lastBp st t Θ ≤ t ∧ (lastBp st t Θ = st ∨ lastBp st t Θ ∈ Θ) ∧
      ∀ θ ∈ Θ, (θ ≤ t ↔ θ ≤ lastBp st t Θ)
  | [] => by simp [lastBp, hst]
  | θ :: Θ => by
    obtain ⟨a, b, c, d⟩ := lastBp_spec st t hst Θ
    simp only [lastBp]
    split
    · rename_i h
      refine ⟨le_trans a (le_max_right _ _), max_le h b, ?_, ?_⟩
      · rcases le_total θ (lastBp st t Θ) with hl | hl
        · rw [max_eq_right hl]; rcases c with c | c
          · exact Or.inl c
          · exact Or.inr (List.mem_cons_of_mem _ c)
        · rw [max_eq_left hl]; exact Or.inr List.mem_cons_self
      · intro θ' hθ'
        rcases List.mem_cons.mp hθ' with rfl | hm
        · exact ⟨fun _ => le_max_left _ _, fun _ => h⟩
        · rw [d θ' hm]; constructor
          · intro h'; exact le_trans h' (le_max_right _ _)
          · intro h'; rcases le_total θ (lastBp st t Θ) with hl | hl
            · rw [max_eq_right hl] at h'; exact h'
            · rw [max_eq_left hl] at h'
              exact (d θ' hm).mp (le_trans h' h)
    · rename_i h
      refine ⟨a, b, ?_, ?_⟩
      · rcases c with c | c
        · exact Or.inl c
        · exact Or.inr (List.mem_cons_of_mem _ c)
      · intro θ' hθ'
        rcases List.mem_cons.mp hθ' with rfl | hm
        · exact ⟨fun h' => absurd h' h, fun h' => absurd (le_trans h' b) h⟩
        · exact d θ' hm

theorem gateOK_of_gateW (enc : Nat → Option Nat) (g : Gate)
    (harc : ∀ i, i < g.k → (g.arcs.getD i default).fmin ≤ (g.arcs.getD i default).fmax)
    (hd : ∀ i, i < g.k → (g.arcs.getD i default).fmin ≤ startN g)
    (hc : gateW enc g = true) : GateOK p1 0 g (fun n => sig1 (enc n)) := by
  refine ⟨fun i t => t - (g.arcs.getD i default).fmin, fun i _ a b hab => by dsimp only; omega, fun t ht => ?_⟩
  rw [start_p1] at ht
  change startN g ≤ t at ht
  refine ⟨fun i hi => ⟨by dsimp only; omega, ?_⟩, ?_⟩
  all_goals dsimp only
  · have hdi := hd i hi
    rw [show t - (t - (g.arcs.getD i default).fmin) = (g.arcs.getD i default).fmin by omega]
    simp only [Adm, p1, sub_zero, add_zero, one_mul, div_one, mul_one, lerp, zero_mul, add_zero]
    refine ⟨by simp, ?_⟩
    exact_mod_cast harc i hi
  · obtain ⟨a, b, c, d⟩ := lastBp_spec (startN g) t ht (bps enc g)
    set τ := lastBp (startN g) t (bps enc g)
    have hτ : eqAt enc g τ = true := by
      have hm : τ ∈ startN g :: bps enc g := by
        rcases c with c | c
        · rw [c]; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ c
      have := List.all_eq_true.mp hc τ hm
      simp only [Bool.or_eq_true, decide_eq_true_eq] at this
      rcases this with h | h
      · omega
      · exact h
    simp only [eqAt, beq_iff_eq] at hτ
    have hout : sig1 (enc g.out) t = sig1 (enc g.out) τ := by
      apply sig1_eq; intro θ hθ
      exact d θ (by simp [bps, hθ])
    rw [hout, hτ]
    congr 1
    apply addr_congr
    intro i hi
    apply sig1_eq
    intro θ hθ
    have hdi := hd i hi
    have := d (θ + (g.arcs.getD i default).fmin) (by
      simp only [bps, List.mem_append, List.mem_flatMap, List.mem_range]
      refine Or.inr ⟨i, hi, ?_⟩
      rw [hθ]; simp)
    constructor
    · intro h; have := this.mp (by omega); omega
    · intro h; have := this.mpr (by omega); omega

end Formal.Net.CViewPS
