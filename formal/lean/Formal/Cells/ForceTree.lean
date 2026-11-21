import Formal.Timing.Island

/-!
# Formal.Cells.ForceTree — a node's value window through a forcing tree (shard B, 2026-11-15)

**Problem, plainly.** Research's select race (PROGRAM.md, 2026-11-15, item 4): a latch captures the output of a
data mux whose select may change while the latch is open. Research's rules H (the next value must not reach a
data pin before the latch's slowest bit has closed) and I (the current value must reach every data pin before the
fastest bit closes) are inequalities between a launch-to-capture path and the close. In the gate model a LUT may
glitch whenever any pin it reads moves, so the claim to prove is: the latch's data pin shows the captured value on
a window `[a, b]` that starts before the earliest close (setup, rule I) and ends after the latest close (hold,
rule H). The data pin is driven through combinational LUTs (the datamux, comparators) whose inputs are other
nodes: select, both data inputs, constants. A LUT keeps its output fixed while SOME of its pins hold values that
force its INIT (`Island.ForcesP`), e.g. a mux with its select and its selected input held, whatever the other
input does. This file proves the timed version with a separate window per node.

**Proved.**
* `force_tree`: in the Spec gate model (`CGateOK`: each pin reads its source at a monotone read time whose
  distance lies in the pin's admissible composite band), for any per-pin bounds `L ≤ distance ≤ U` implied by
  that band: if every non-root node `w` is forced to `val w` by pins `ps w` whose sources are roots or lower-rank
  nodes, and each such pin satisfies `a src + U ≤ a w` and `b w ≤ b src + L`, and every root shows its value on
  its window, then every node `w` shows `val w` at every `t ∈ [a w, b w]` (and `S w ≤ a w`, the gate's start).
  No glitch can occur: the other pins of each LUT are unconstrained.
* `force_tree_minmax`: the same with the corner-free bounds `sumMin`/`sumMax` (`SpecLoop.sumAdm_bounds`).

**Use.** For a select race, the roots are the select node and the selected data source, each held on a window
from a chain certificate (cause: the controller event that releases them, as `LatchHoldCert`) or from quietness;
the conclusion at the latch's data pin source is the data window `LatchHoldPin.latch_close_pin` needs. The window
end `b` carries rule H, the start `a` rule I. **Not shown here:** any certificate for a real build; completeness
(that every capture of a netlist has such a tree).
-/

namespace Formal.Cells.ForceTree
open Formal.Target Formal.Timing.SpecSettle Formal.Timing.SpecChain Formal.Timing.SpecLoop Formal.Timing.Island

/-- **Value windows through a forcing tree.** -/
theorem force_tree {p : DelayPar} {c : ℚ} {x : Beh}
    (comb root : Nat → Prop) (ρ : Nat → Nat) (gate : Nat → Gate) (src : Nat → Nat → Nat)
    (arcs : Nat → Nat → List Arc) (S : Nat → Nat) (val : Nat → Bool) (ps : Nat → List Nat)
    (L U : Nat → Nat → Nat) (a b : Nat → Nat)
    (hg : ∀ w, comb w → (gate w).out = w ∧ CGateOK p c (gate w) (src w) (arcs w) (S w) x)
    (hLU : ∀ w, comb w → ∀ j, j < (gate w).k → ∀ D, SumAdm p c (arcs w j) D → L w j ≤ D ∧ D ≤ U w j)
    (hF : ∀ w, comb w → ForcesP (gate w).k (gate w).init (asgOf src val w (ps w)) (val w) = true)
    (hps : ∀ w, comb w → ∀ j ∈ ps w, j < (gate w).k ∧
      (root (src w j) ∨ (comb (src w j) ∧ ρ (src w j) < ρ w)))
    (hwin : ∀ w, comb w → ∀ j ∈ ps w, a (src w j) + U w j ≤ a w ∧ b w ≤ b (src w j) + L w j)
    (hS : ∀ w, comb w → S w ≤ a w)
    (hroot : ∀ r, root r → ∀ t, a r ≤ t → t ≤ b r → x r t = val r) :
    ∀ w, comb w → ∀ t, a w ≤ t → t ≤ b w → x w t = val w := by
  intro w
  induction hr : ρ w using Nat.strong_induction_on generalizing w with
  | _ n ih =>
    intro hw t h1 h2
    obtain ⟨hout, F, -, hFt⟩ := hg w hw
    obtain ⟨hrd, ho⟩ := hFt t (le_trans (hS w hw) h1)
    suffices hv : ∀ e ∈ asgOf src val w (ps w), e.1 < (gate w).k ∧ x (src w e.1) (F e.1 t) = e.2 by
      have := forcesP_sound (hF w hw) (fun i => x (src w i) (F i t)) hv
      rw [hout] at ho; rw [ho]; exact this
    intro e he
    simp only [asgOf, List.mem_map] at he
    obtain ⟨j, hj, rfl⟩ := he
    dsimp only
    obtain ⟨hjk, hsrc⟩ := hps w hw j hj
    refine ⟨hjk, ?_⟩
    obtain ⟨r1, r2⟩ := hrd j hjk
    obtain ⟨b1, b2⟩ := hLU w hw j hjk _ r2
    obtain ⟨w1, w2⟩ := hwin w hw j hj
    have i1 : a (src w j) ≤ F j t := by omega
    have i2 : F j t ≤ b (src w j) := by omega
    rcases hsrc with hrt | ⟨hc, hlt⟩
    · exact hroot _ hrt _ i1 i2
    · exact ih _ (hr ▸ hlt) _ rfl hc _ i1 i2

/-- **The same with the corner-free composite bounds.** -/
theorem force_tree_minmax {p : DelayPar} {c : ℚ} {x : Beh} (hp : Sane p) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (comb root : Nat → Prop) (ρ : Nat → Nat) (gate : Nat → Gate) (src : Nat → Nat → Nat)
    (arcs : Nat → Nat → List Arc) (S : Nat → Nat) (val : Nat → Bool) (ps : Nat → List Nat) (a b : Nat → Nat)
    (hg : ∀ w, comb w → (gate w).out = w ∧ CGateOK p c (gate w) (src w) (arcs w) (S w) x)
    (hord : ∀ w, comb w → ∀ i, i < (gate w).k → ArcsOrd (arcs w i))
    (hF : ∀ w, comb w → ForcesP (gate w).k (gate w).init (asgOf src val w (ps w)) (val w) = true)
    (hps : ∀ w, comb w → ∀ j ∈ ps w, j < (gate w).k ∧
      (root (src w j) ∨ (comb (src w j) ∧ ρ (src w j) < ρ w)))
    (hwin : ∀ w, comb w → ∀ j ∈ ps w,
      a (src w j) + sumMax p (arcs w j) ≤ a w ∧ b w ≤ b (src w j) + sumMin p (arcs w j))
    (hS : ∀ w, comb w → S w ≤ a w)
    (hroot : ∀ r, root r → ∀ t, a r ≤ t → t ≤ b r → x r t = val r) :
    ∀ w, comb w → ∀ t, a w ≤ t → t ≤ b w → x w t = val w :=
  force_tree comb root ρ gate src arcs S val ps (fun w j => sumMin p (arcs w j)) (fun w j => sumMax p (arcs w j))
    a b hg (fun w hw j hj D hD => sumAdm_bounds hp hc0 hc1 _ D (hord w hw j hj) hD) hF hps hwin hS hroot

end Formal.Cells.ForceTree
