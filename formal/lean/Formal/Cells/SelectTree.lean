import Formal.Cells.LatchHoldCert

/-!
# Formal.Cells.SelectTree — hold windows through a tree of forcing rows on THE target (shard B, 2026-11-15)

**Problem, plainly.** `SelectHold.select_hold_row` covers a latch whose data pin reads ONE mux whose controlling
pins read chain-certified nodes. On THE target 137 select captures (`uselect*`, `ushrsi*`, `ushli*`) reach the latch
through cones of combinational LUTs up to 13 deep (`tools-B/select/`). The generic `ForceTree.force_tree` handles
such cones in the abstract; this file states it for THE target's checked forcing rows (`KRow`, `krowOK`), so rows
can be emitted and kernel-checked.

**Proved.**
* `krow_tree`: given `n` checked non-memory forcing rows `m 0 … m (n-1)` of THE circuit (each with its collapsed
  gate relation), roots with value windows `[rs r, B]`, and start times `st i` such that each controlling pin of
  row `i` reads either a root `r` (its value = the pin's forcing value, `rs r + hi ≤ st i`) or an EARLIER row
  `k < i` (its value, `st k + hi ≤ st i`), and the row's gate start `S ≤ st i`: every row `i` shows its value on
  `[st i, B]`. Glitches on non-controlling pins are harmless (not constrained).

**Not shown.** Row emission for the deep cones; the roots' windows (chain certificates, as in `SelectHold`).
-/

namespace Formal.Cells.SelectTree
open Formal.Target Formal.Target.DecodedPS Formal.Timing.SpecChain Formal.Cells.CertPS Formal.Cells.RaceCertPS
  Formal.Cells.SpecCElemFact

/-- **Value windows through a tree of checked forcing rows.** -/
theorem krow_tree {p : DelayPar} {c : ℚ} {x : Beh} (hb : Behaves p (circuit net boundary) x)
    (n : Nat) (m : Nat → KRow) (hm : ∀ i, i < n → krowOK (m i) = true ∧ (m i).mem = false)
    (G : ∀ i, i < n → CGateOK p c (m i).g (m i).src (m i).arcs ((m i).S p) x)
    (root : Nat → Prop) (rq : Nat → Nat) (rw : Nat → Bool) (rs : Nat → Nat) (B : Nat)
    (hroot : ∀ r, root r → ∀ u, rs r ≤ u → u ≤ B → x (rq r) u = rw r)
    (st : Nat → Nat) (hS : ∀ i, i < n → (m i).S p ≤ st i)
    (hsrc : ∀ i, i < n → ∀ j ∈ (m i).P,
      (∃ r, root r ∧ (m i).src j = rq r ∧ fl (m i).bv j = rw r ∧ rs r + (m i).hi p c j ≤ st i) ∨
      (∃ k, k < i ∧ (m i).src j = (m k).q ∧ fl (m i).bv j = (m k).w ∧ st k + (m i).hi p c j ≤ st i)) :
    ∀ i, i < n → ∀ u, st i ≤ u → u ≤ B → x (m i).q u = (m i).w := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro hi u hu1 hu2
  obtain ⟨hok, hmem⟩ := hm i hi
  have key := krow_set hb hok hmem (G i hi) (fun j => st i - (m i).hi p c j) (fun _ => B)
    (by
      intro j hj t ht1 ht2
      rcases hsrc i hi j hj with ⟨r, hr, hq, hv, hle⟩ | ⟨k, hk, hq, hv, hle⟩
      · rw [hq, hv]; exact hroot r hr t (by omega) ht2
      · rw [hq, hv]; exact ih k hk (by omega) t (by omega) ht2)
  refine key u (le_trans (hS i hi) hu1) (fun j hj => ⟨?_, by omega⟩)
  rcases hsrc i hi j hj with ⟨r, -, -, -, hle⟩ | ⟨k, -, -, -, hle⟩ <;> omega

end Formal.Cells.SelectTree
