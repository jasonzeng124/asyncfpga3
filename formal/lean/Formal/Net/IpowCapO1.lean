import Formal.Net.IpowCapSafe
import Formal.Net.CapstoneO1Stage

/-!
# INSTANTIATED for ipow_ps by formal/tools/capnet/instantiate.py -- DO NOT EDIT

Source: `Formal/Net/CapstoneO1.lean` (the gcd_hw proof), rewritten by the substitution table in
instantiate.py (namespace, the kernel's graph module, out/end channels 57/4, the spec
`IpowHw.ipowSpec a b` in place of `Nat.gcd a b`, theorem prefix `ipow_hw_`). Everything else is the gcd text;
its comments below still speak of gcd_hw where they describe the shared argument.
-/

namespace Formal.Net.IpowCap
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.GcdHw
open Formal.Net.CapNet hiding R Hh Hh_pr Hh_cn NoEnd JOK FoldOK OpChk
open Formal.Net.CapSafe (cntL perL cntL_zero cntL_cons_succ cnt_take cnt_add cnt_periodic perL_ne perL_mod len_pos cnt_per filter_rank filter_len sel tst sel_rank sel_len)
open Formal.Net.Capstone.O1

variable {n : Nat}

/-- H_CUT, per arbiter stage. -/
def CutOp (ch : Fin n → Chan) (om : Nat → Nat → Bool) : K n → Prop
  | .amerge x y z w => CutBound (ch x) (ch y) (ch z) (om w)
  | _ => True

/-- The protocol half of `cell_op` needs no forcing. -/
theorem cell_proto (ch : Fin n → Chan) (sv : Nat → Nat) (k : K n) (hc : Cell ch sv k) (hd : Dist k) :
    OpProto ch k.insC k.outsC := by
  cases k with
  | amerge x y z w =>
    obtain ⟨g1, g2, M⟩ := hc
    exact (CM.amerge_op ch x y z g1 g2 M).1
  | forkG => exact (cell_op ch (fun _ _ => false) sv _ hc trivial hd).1
  | forkH => exact (cell_op ch (fun _ _ => false) sv _ hc trivial hd).1
  | join => exact (cell_op ch (fun _ _ => false) sv _ hc trivial hd).1
  | bjoin => exact (cell_op ch (fun _ _ => false) sv _ hc trivial hd).1
  | steerC => exact (cell_op ch (fun _ _ => false) sv _ hc trivial hd).1
  | steerD => exact (cell_op ch (fun _ _ => false) sv _ hc trivial hd).1
  | mux => exact (cell_op ch (fun _ _ => false) sv _ hc trivial hd).1
  | muxn => exact (cell_op ch (fun _ _ => false) sv _ hc trivial hd).1
  | link => exact (cell_op ch (fun _ _ => false) sv _ hc trivial hd).1
  | src => exact (cell_op ch (fun _ _ => false) sv _ hc trivial hd).1
  | sink => exact (cell_op ch (fun _ _ => false) sv _ hc trivial hd).1

/-- Per operator: the cut bound forces the stage (`O1.stage_forced`). -/
theorem forced_of_cut (ch : Fin n → Chan) (om : Nat → Nat → Bool) (sv : Nat → Nat) (k : K n)
    (hc : Cell ch sv k) (hcut : CutOp ch om k) (hp : ∀ c, Protocol (ch c)) : Forced ch om k := by
  cases k with
  | amerge x y z w =>
    obtain ⟨g1, g2, M⟩ := hc
    exact stage_forced M (hp x) (hp y) (hp z) (om w) hcut
  | _ => trivial

/-- Every channel of the concrete network obeys the four-phase protocol (no forcing used). -/
theorem ipow_hw_protocol (a b : Nat) (ch : Fin NC → Chan)
    (H_CELLS : ∀ o : Fin NO, Cell ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c)) : ∀ c, Protocol (ch c) :=
  net_protocol net ch (fun o => cell_proto ch (srcV a b) (opAt o) (H_CELLS o) (dist_of _ (ops_ok o)))
    H_BUNDLE

/-- **Circuit-level safety of gcd_hw, with H_CM_FORCED replaced by the count bound H_CUT.** -/
theorem ipow_hw_circuit_safe' (a b : Nat) (ch : Fin NC → Chan)
    (H_CELLS : ∀ o : Fin NO, Cell ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_CUT : ∃ y, Good a b y ∧ ∀ o : Fin NO, CutOp ch (omOf a b y) (opAt o)) :
    (∀ k e, TokAt (ch out0) k e → (ch out0).dat e = IpowHw.ipowSpec a b) ∧
    (∀ t, closedVals (ch out0) t = List.replicate (cnt (fallB (ch out0).ack) t) (IpowHw.ipowSpec a b)) := by
  obtain ⟨y, hy, hc⟩ := H_CUT
  have hp := ipow_hw_protocol a b ch H_CELLS H_BUNDLE
  exact ipow_hw_circuit_safe a b ch H_CELLS H_BUNDLE
    ⟨y, hy, fun o => forced_of_cut ch (omOf a b y) (srcV a b) (opAt o) (H_CELLS o) (hc o) hp⟩

/-- H_CUT implies H_CM_FORCED (so `ipow_hw_circuit_safe'` is 8m's theorem with a hypothesis
that implies its H_CM_FORCED, given H_CELLS and H_BUNDLE). -/
theorem cm_forced_of_cut (a b : Nat) (ch : Fin NC → Chan)
    (H_CELLS : ∀ o : Fin NO, Cell ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c)) (y : TS)
    (hc : ∀ o : Fin NO, CutOp ch (omOf a b y) (opAt o)) :
    ∀ o : Fin NO, Forced ch (omOf a b y) (opAt o) :=
  fun o => forced_of_cut ch (omOf a b y) (srcV a b) (opAt o) (H_CELLS o) (hc o)
    (ipow_hw_protocol a b ch H_CELLS H_BUNDLE)

/-- **No free contention at any arbiter stage.** Under the same hypotheses, for every arbiter
stage `.amerge x y z w` and every grant pair meeting its gate model, whenever both requests
are high one grant is already held. -/
theorem ipow_hw_arbiters_uncontended (a b : Nat) (ch : Fin NC → Chan)
    (H_CELLS : ∀ o : Fin NO, Cell ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c)) (y : TS)
    (hc : ∀ o : Fin NO, CutOp ch (omOf a b y) (opAt o))
    (o : Fin NO) (x u z : Fin NC) (w : Nat) (ho : opAt o = .amerge x u z w)
    (g1 g2 : Trace) (M : CM.AMerge (ch x) (ch u) (ch z) g1 g2) :
    ∀ t, (ch x).req t = true → (ch u).req t = true → g1 t = true ∨ g2 t = true := by
  have hp := ipow_hw_protocol a b ch H_CELLS H_BUNDLE
  have h := hc o
  rw [ho] at h
  exact stage_uncontended M (hp x) (hp u) (hp z) _ h

end Formal.Net.IpowCap
