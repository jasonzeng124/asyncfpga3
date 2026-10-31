import Formal.Net.Compute.Word

/-!
# H_COMPUTE_FN, part 8: a cell's equation over the final net values

`run_cell`: in a netlist with no net driven twice, a cell whose input nets are not driven by
itself or a later cell (topological order at that cell) satisfies its own equation over the
FINAL net values: output `j` = `vals` of its inputs. This turns structural facts (e.g. "the
carry-out of this CARRY4 position is `S ? carry-in : DI`") into equations without exhaustive
checks.
-/

namespace Formal.Net.Compute

theorem run_append (env : Leaf → Bool) (C : List Nat) :
    ∀ (l1 l2 : List Cell) (v : Nat → Bool), run env C (l1 ++ l2) v = run env C l2 (run env C l1 v)
  | [], _, _ => rfl
  | c :: l1, l2, v => run_append env C l1 l2 (step env C v c)

theorem idxOf_getElem_of_nodup : ∀ (l : List Nat) (j : Nat) (hj : j < l.length), l.Nodup →
    l.idxOf l[j] = j
  | [], _, hj, _ => absurd hj (by simp)
  | x :: l, 0, _, _ => by simp
  | x :: l, j + 1, hj, hnd => by
    simp only [List.nodup_cons] at hnd
    have hj' : j < l.length := by simp at hj; omega
    have hne : l[j] ≠ x := fun h => hnd.1 (h ▸ List.getElem_mem _)
    have ih := idxOf_getElem_of_nodup l j hj' hnd.2
    rw [List.getElem_cons_succ, List.idxOf_cons]
    simp [Ne.symm hne, ih]

/-- **A cell's equation over the final values.** -/
theorem run_cell (env : Leaf → Bool) (cells : List Cell)
    (hnd : (cells.flatMap Cell.outs).Nodup) (i : Nat) (c : Cell) (hc : cells[i]? = some c)
    (htopo : ∀ n ∈ insNets c, n ∉ (cells.drop i).flatMap Cell.outs) (j : Nat)
    (hj : j < c.outs.length) :
    run env [] cells (fun _ => false) (c.outs[j]) =
      (c.vals (wv env (run env [] cells (fun _ => false)))).getD j false := by
  have hi : i < cells.length := by
    rcases Nat.lt_or_ge i cells.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hc; cases hc
  have hci : cells[i] = c := by rw [List.getElem?_eq_getElem hi] at hc; injection hc
  have hdrop : cells.drop i = c :: cells.drop (i + 1) := by
    rw [← hci]; exact List.drop_eq_getElem_cons hi
  have hsplit : cells = cells.take i ++ c :: cells.drop (i + 1) := by
    rw [← hdrop, List.take_append_drop]
  have hnd2 : ((c :: cells.drop (i + 1)).flatMap Cell.outs).Nodup := by
    rw [← hdrop]
    exact (List.nodup_append.mp (by rw [← List.flatMap_append, List.take_append_drop]; exact hnd)).2.1
  simp only [List.flatMap_cons, List.nodup_append] at hnd2
  obtain ⟨hndc, hndp, hdis⟩ := hnd2
  let V := run env [] (cells.take i) (fun _ => false)
  have hR : run env [] cells (fun _ => false) =
      run env [] (cells.drop (i + 1)) (step env [] V c) := by
    conv => lhs; rw [hsplit]
    rw [run_append]; rfl
  have hm : c.outs[j] ∈ c.outs := List.getElem_mem _
  have hmp : c.outs[j] ∉ (cells.drop (i + 1)).flatMap Cell.outs :=
    fun h => hdis _ hm _ h rfl
  have hin : ∀ w ∈ c.ins, wv env V w = wv env (run env [] cells (fun _ => false)) w := by
    intro w hw
    cases w with
    | net n =>
      have hn : n ∈ insNets c := by
        simp only [insNets, List.mem_filterMap]; exact ⟨.net n, hw, rfl⟩
      have hnot := htopo n hn
      rw [hdrop] at hnot
      simp only [List.flatMap_cons, List.mem_append, not_or] at hnot
      show V n = run env [] cells (fun _ => false) n
      rw [hR, run_preserve _ _ n hnot.2]
      simp [step, hnot.1]
    | inp p k => rfl
    | c0 => rfl
    | c1 => rfl
  have e1 : run env [] cells (fun _ => false) (c.outs[j]) = step env [] V c (c.outs[j]) := by
    rw [hR, run_preserve _ _ _ hmp]
  rw [e1]
  simp only [step, hm, if_true, cutv, List.not_mem_nil, if_false]
  rw [idxOf_getElem_of_nodup _ _ hj hndc, vals_congr c hin rfl]

end Formal.Net.Compute
