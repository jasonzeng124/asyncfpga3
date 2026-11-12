import Formal.Cells.FiniteRunsWit

/-!
# Probe Bfin (shard B): the kernel checks of `FiniteRunsWit` on C's run `Wit.chW`

Note: `formal/notes/B-finite-runs.md`. See `FiniteRunsWit` for the assumed / proved /
NOT covered block; this file holds the `decide +kernel` checks (175 links) and the joint
witness of `FiniteRuns.gcd_hw_safe_fin_links`. Core Lean only.
-/

namespace Formal.Cells.FiniteRunsWit
open Formal.Cells
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapSafe
open Formal.Net.CapNet.Wit (CD chW cdA)
open Formal.Cells.LutFbBridge2Env (PhysLink isLink)
open Formal.Cells.FiniteRuns (FPhysLink)

/-! ## 4. C's witness run -/

def lkChk : K NC → Bool
  | .link i o => linkB (cdA i) (cdA o)
  | _ => true

set_option maxRecDepth 100000

theorem lk1 : (ops.take 90).all lkChk = true := by decide +kernel
theorem lk2 : ((ops.drop 90).take 90).all lkChk = true := by decide +kernel
theorem lk3 : (((ops.drop 90).drop 90).take 90).all lkChk = true := by decide +kernel
theorem lk4 : (((ops.drop 90).drop 90).drop 90).all lkChk = true := by decide +kernel

theorem lk_all : ops.all lkChk = true := by
  rw [← List.take_append_drop 90 ops, List.all_append, lk1, ← List.take_append_drop 90 (ops.drop 90),
    List.all_append, lk2, ← List.take_append_drop 90 ((ops.drop 90).drop 90), List.all_append, lk3,
    lk4]; rfl

/-- **C's witness run meets B's finite physical link model on every one of the 175 links.** -/
theorem chW_fin_links :
    ∀ (o : Fin NO) (i o' : Fin NC), opAt o = .link i o' → FPhysLink (chW i) (chW o') := by
  intro o i o' e
  have := List.all_eq_true.mp lk_all _ (getD_mem (o := o))
  rw [e] at this
  exact linkB_sound this

/-- 34 of the 175 links never see a request in this run (`nr = 0`). -/
theorem idle_links : ((List.finRange NO).filter (fun o => match opAt o with
    | .link i _ => (cdA i).rq.isEmpty | _ => false)).length = 34 := by decide +kernel

/-- On the same run, the infinite form fails on every channel pair. -/
theorem chW_fin_not_phys :
    (∀ (o : Fin NO) (i o' : Fin NC), opAt o = .link i o' → FPhysLink (chW i) (chW o')) ∧
    ∀ i o : Fin NC, ¬ PhysLink (chW i) (chW o) :=
  ⟨chW_fin_links, SelfAuditB8.chW_not_physLink⟩

open Formal.Net.CapNet.Wit (w_cells w_held w_start_once yW yW_good yW_walk w_out0 out0Close
  gcd_12_18)

/-- **Joint non-vacuity of `FiniteRuns.gcd_hw_safe_fin_links`** on C's terminating run
(a = 12, b = 18): every hypothesis holds together, and out0 latches a token carrying 6. -/
theorem gcd_hw_fin_links_witness :
    ∃ ch : Fin NC → Chan,
      (∀ (o : Fin NO) (i o' : Fin NC), opAt o = .link i o' → FPhysLink (ch i) (ch o')) ∧
      (∀ o : Fin NO, isLink (opAt o) = false → Cell ch (srcV 12 18) (opAt o)) ∧
      (∀ c, Held (ch c)) ∧
      (∃ y, Good 12 18 y ∧ ∀ o : Fin NO, Forced ch (omOf 12 18 y) (opAt o)) ∧
      (∃ k e, TokAt (ch out0) k e ∧ (ch out0).dat e = 6) :=
  ⟨chW, chW_fin_links, fun o _ => w_cells o, w_held,
    ⟨yW, yW_good, gcd_hw_forced 12 18 chW yW yW_good w_cells w_held w_start_once yW_walk⟩,
    ⟨0, out0Close, w_out0⟩⟩

/-- The finite link theorem applied to the witness gives the value it latches. -/
theorem gcd_hw_fin_links_consistent :
    (∀ k e, TokAt (chW out0) k e → (chW out0).dat e = 6) ∧ TokAt (chW out0) 0 out0Close := by
  have h := FiniteRuns.gcd_hw_safe_fin_links 12 18 chW chW_fin_links (fun o _ => w_cells o)
    w_held ⟨yW, yW_good, gcd_hw_forced 12 18 chW yW yW_good w_cells w_held w_start_once yW_walk⟩
  rw [gcd_12_18] at h
  exact ⟨h.1, w_out0.1⟩

end Formal.Cells.FiniteRunsWit
