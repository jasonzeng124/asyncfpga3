import Formal.Net.Compute.Shift

/-!
# H_COMPUTE_FN, part 11: units whose output bits each depend on a few input bits

`BitFnOK cells outs need f`: for each output bit `i`, its cone is checked exhaustively over its
computed support (deduplicated) against `f i` (a Boolean function of the port-0 bits, read through
the leaf list), and the bits `need i` that `f i` reads are in the support. `bitFn_bit`: if `f i`
reads only `need i` (`hloc`), the output bit is `f i` of the input bits, for every environment.
-/

namespace Formal.Net.Compute

def BitFnOK (cells : List Cell) (outs : List W) (need : Nat → List Nat)
    (f : Nat → (Nat → Bool) → Bool) : Prop :=
  outs.length = 32 ∧ ∀ i, i < 32 →
    LocalOK [] (coneW cells (outs.getD i .c0)) (outs.getD i .c0)
      (dedup (swOf [] (coneW cells (outs.getD i .c0)) (outs.getD i .c0)))
      (fun l => f i (fun j => l.getD
        ((dedup (swOf [] (coneW cells (outs.getD i .c0)) (outs.getD i .c0))).idxOf (.inp 0 j)) false)) ∧
    (need i).all (fun j => decide
      (Leaf.inp 0 j ∈ dedup (swOf [] (coneW cells (outs.getD i .c0)) (outs.getD i .c0)))) = true

instance (cells : List Cell) (outs : List W) (need : Nat → List Nat)
    (f : Nat → (Nat → Bool) → Bool) : Decidable (BitFnOK cells outs need f) := by
  unfold BitFnOK; exact inferInstance

theorem bitFn_bit {cells : List Cell} {outs : List W} {need : Nat → List Nat}
    {f : Nat → (Nat → Bool) → Bool} (h : BitFnOK cells outs need f)
    (hloc : ∀ i g1 g2, (∀ j ∈ need i, g1 j = g2 j) → f i g1 = f i g2)
    (env : Leaf → Bool) (i : Nat) (hi : i < 32) :
    eval env [] cells (outs.getD i .c0) = f i (fun j => env (.inp 0 j)) := by
  obtain ⟨_, hb⟩ := h
  obtain ⟨hok, hneed⟩ := hb i hi
  rw [eval_coneW]
  rw [local_sound hok (nodup_dedup _) (fun l hl => (mem_dedup _ _).mpr hl) env]
  apply hloc
  intro j hj
  have hm := List.all_eq_true.mp hneed j hj
  simp only [decide_eq_true_eq] at hm
  exact getD_idxOf_map hm

end Formal.Net.Compute
