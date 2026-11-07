import Formal.Cells.CertSwitchAll

/-!
# Formal.Cells.CertSplit — checking a large certificate in pieces

Shard B, 2026-11-07. A certificate whose rows touch more netlist chunks than one kernel `decide` fits in memory is
checked by row ranges in separate files; these lemmas reassemble `certOK` and `raceOK` from the pieces.

* `all_range'_append`: a Boolean `all` over `range' a (m + n)` from the two halves.
* `certOK_of_split`: `certOK` from the rows' `krowOK` (by ranges) and the labels (cheap: literal data).
* `sFmin_pathArcs` / `sSmin_pathArcs`: the path arc sums are sums of per-row sums.
* `raceOK_of_split`: `raceOK` from the cheap parts and the per-row path sums.
-/

namespace Formal.Cells.CertSplit
open Formal.Target Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll
  Formal.Cells.RaceCornersPS

theorem all_range'_append (f : Nat → Bool) (a m n : Nat) (h1 : (List.range' a m).all f = true)
    (h2 : (List.range' (a + m) n).all f = true) : (List.range' a (m + n)).all f = true := by
  rw [← List.range'_append, List.all_append, h1, Nat.one_mul, h2]; rfl

theorem certOK_of_split (P : Prem) (rows : List CRow)
    (hk : (List.range' 0 rows.length).all (fun i => krowOK (rows.getD i default).r) = true)
    (hl : (List.range rows.length).all (fun i => labOK P rows i (rows.getD i default)) = true) :
    certOK P rows = true := by
  simp only [certOK, List.all_eq_true, List.mem_range, Bool.and_eq_true] at hk hl ⊢
  intro i hi
  refine ⟨hk i ?_, hl i hi⟩
  simp only [List.mem_range'_1]; omega

theorem sum_map_range'_append (f : Nat → Nat) (a m n : Nat) :
    ((List.range' a (m + n)).map f).sum = ((List.range' a m).map f).sum + ((List.range' (a + m) n).map f).sum := by
  rw [← List.range'_append, List.map_append, List.sum_append, Nat.one_mul]

theorem sum_block (f : Nat → Nat) (a m n V W : Nat) (h1 : ((List.range' a m).map f).sum = V)
    (h2 : ((List.range' (a + m) n).map f).sum = W) : ((List.range' a (m + n)).map f).sum = V + W := by
  rw [sum_map_range'_append, h1, h2]

theorem sF_flatten (s : Arc → Nat) : ∀ (n : Nat) (f : Nat → List Arc),
    ((((List.range n).map f).flatten).map s).sum = ((List.range' 0 n).map fun i => ((f i).map s).sum).sum
  | 0, _ => by simp
  | n + 1, f => by
    rw [List.range_succ, List.map_append, List.flatten_append, List.map_append, List.sum_append, sF_flatten s n f,
      show n + 1 = n + 1 from rfl, sum_map_range'_append _ 0 n 1]
    simp

theorem sFmin_pathArcs (rows : List CRow) :
    sFmin (pathArcs rows) = ((List.range' 0 rows.length).map fun i =>
      sFmin ((rows.getD i default).r.arcs (pathPin (rows.getD i default)))).sum :=
  sF_flatten Arc.fmin rows.length _

theorem sSmin_pathArcs (rows : List CRow) :
    sSmin (pathArcs rows) = ((List.range' 0 rows.length).map fun i =>
      sSmin ((rows.getD i default).r.arcs (pathPin (rows.getD i default)))).sum :=
  sF_flatten Arc.smin rows.length _

/-- `raceOK` from its cheap parts and the per-row path sums `F`, `S` (computed in pieces). -/
theorem raceOK_of_split (r : RaceRow) (F S : Nat)
    (hF : ((List.range' 0 r.pc.2.length).map fun i =>
      sFmin ((r.pc.2.getD i default).r.arcs (pathPin (r.pc.2.getD i default)))).sum = F)
    (hS : ((List.range' 0 r.pc.2.length).map fun i =>
      sSmin ((r.pc.2.getD i default).r.arcs (pathPin (r.pc.2.getD i default)))).sum = S)
    (hc : (singlePath r.pc.2 && chainShape r.pc.2 && decide (1 ≤ r.pc.2.length) &&
      Formal.Cells.ViewPS.viewOK r.node.q r.node.pins && r.node.q == r.pc.1.cn &&
      (r.node.pins.getD r.ja ([], 0)).2 == (r.pc.2.getD (r.pc.2.length - 1) default).r.q &&
      (r.node.pins.getD r.jf ([], 0)).2 == r.node.q &&
      decide (283 * sFmax (r.node.arcs r.jf) ≤ 117 * (F + sFmin (r.node.arcs r.ja))) &&
      decide (283 * sSmax (r.node.arcs r.jf) ≤ 117 * (S + sSmin (r.node.arcs r.ja)))) = true) :
    raceOK r = true := by
  have e1 : sFmin (pathArcs r.pc.2 ++ r.node.arcs r.ja) = F + sFmin (r.node.arcs r.ja) := by
    rw [← hF, ← sFmin_pathArcs]; simp [sFmin, List.map_append, List.sum_append]
  have e2 : sSmin (pathArcs r.pc.2 ++ r.node.arcs r.ja) = S + sSmin (r.node.arcs r.ja) := by
    rw [← hS, ← sSmin_pathArcs]; simp [sSmin, List.map_append, List.sum_append]
  simp only [raceOK, e1, e2]
  exact hc

end Formal.Cells.CertSplit
