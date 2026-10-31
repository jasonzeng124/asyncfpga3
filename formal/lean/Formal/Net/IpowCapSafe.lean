import Formal.Net.IpowCapNetChk
import Formal.Net.Capstone

/-!
# INSTANTIATED for ipow_ps by formal/tools/capnet/instantiate.py -- DO NOT EDIT

Source: `Formal/Net/CapstoneSafe.lean` (the gcd_hw proof), rewritten by the substitution table in
instantiate.py (namespace, the kernel's graph module, out/end channels 57/4, the spec
`IpowHw.ipowSpec a b` in place of `Nat.gcd a b`, theorem prefix `ipow_hw_`). Everything else is the gcd text;
its comments below still speak of gcd_hw where they describe the shared argument.
-/

namespace Formal.Net.IpowCap
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.GcdHw
open Formal.Net.CapNet hiding R Hh Hh_pr Hh_cn NoEnd JOK FoldOK OpChk
open Formal.Net.CapSafe (cntL perL cntL_zero cntL_cons_succ cnt_take cnt_add cnt_periodic perL_ne perL_mod len_pos cnt_per filter_rank filter_len sel tst sel_rank sel_len)

/-- The oracle of arbiter stage `w`: the labels of the complete token run `y`. -/
def omOf (a b : Nat) (y : TS) (w : Nat) : Nat → Bool := (tab.w w).om (Hh a b y)

theorem dist_of (k : K NC) (h : OpChk tab k) : Dist k := by
  cases k with
  | amerge x y z w => exact h.2
  | _ => trivial

theorem out0_hist {a b : Nat} {y : TS} (hy : Good a b y) : Hh a b y 57 = [IpowHw.ipowSpec a b] := by
  have hf := hy.fifo 57
  rw [hy.fin, hy.nc 57 (by decide), List.nil_append] at hf
  have hi : IpowHw.init a b 57 = [] := init_empty a b 57 (by decide)
  rw [hi, List.nil_append] at hf
  rw [Hh_pr (by decide), hf]
  exact (IpowHw.final_store (IpowHw.ipowSpec a b)).1

theorem cm_oracle_exists (a : Nat) {b : Nat} (hb : b < 2 ^ 32) : ∃ y, Good a b y :=
  good_exists a hb

/-- **Circuit-level safety of gcd_hw** (modulo H_CM_FORCED, obligation O1). -/
theorem ipow_hw_circuit_safe (a b : Nat) (ch : Fin NC → Chan)
    (H_CELLS : ∀ o : Fin NO, Cell ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_CM_FORCED : ∃ y, Good a b y ∧ ∀ o : Fin NO, Forced ch (omOf a b y) (opAt o)) :
    (∀ k e, TokAt (ch out0) k e → (ch out0).dat e = IpowHw.ipowSpec a b) ∧
    (∀ t, closedVals (ch out0) t = List.replicate (cnt (fallB (ch out0).ack) t) (IpowHw.ipowSpec a b)) := by
  obtain ⟨y, hy, hF⟩ := H_CM_FORCED
  have hop := fun o => cell_op ch (omOf a b y) (srcV a b) (opAt o) (H_CELLS o) (hF o)
    (dist_of _ (ops_ok o))
  refine Capstone.latched_const net ch (fun o => Eqn ch (omOf a b y) (srcV a b) (opAt o))
    (fun o => (hop o).1) H_BUNDLE (fun o => (hop o).2) out0 (IpowHw.ipowSpec a b)
    ⟨fun c i => refT tab (Hh a b y) c.val i, fun o => eqn_sound hy rank_ok nf_pos ch (opAt o) (ops_ok o),
      fun k => ?_⟩
  show refT tab (Hh a b y) out0.val k = IpowHw.ipowSpec a b
  rw [ref_hist tab _ out0_desc nf_pos, out0_hist hy]
  simp [perL, Nat.mod_one]

end Formal.Net.IpowCap
