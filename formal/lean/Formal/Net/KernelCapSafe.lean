import Formal.Net.KernelCapSound
import Formal.Net.Capstone
import Formal.Net.CapstoneO1Stage

/-!
# Kernel-parametric: safety modulo H_CM_FORCED / H_CUT (from C-8m/8q's CapstoneSafe, CapstoneO1)
-/


namespace Formal.Net.KCap
open Formal.Net Formal.Net.Kahn Formal.Net.GcdHw Formal.Net.Handshake Formal.Net.Ops
open Formal.Net.CapNet hiding R Hh Hh_pr Hh_cn NoEnd JOK FoldOK OpChk
open Formal.Net.CapSafe (cntL perL cntL_zero cntL_cons_succ cnt_take cnt_add cnt_periodic perL_ne perL_mod len_pos cnt_per filter_rank filter_len sel tst sel_rank sel_len)
open KD KP

set_option linter.unusedSectionVars false

variable [KD] [KP]

/-- The network (Ops `Net`). -/
def net : Ops.Net (Fin NC) (Fin NO) where
  ins o := (opAt o).insC
  outs o := (opAt o).outsC
  prod := prodOf
  cons := consOf
  prod_iff c o := ⟨fun h => prod_out o c h, fun h => h ▸ prod_mem c⟩
  cons_iff c o := ⟨fun h => cons_in o c h, fun h => h ▸ cons_mem c⟩

/-- The oracle of arbiter stage `w`: the labels of the complete token run `y`. -/
def omOf (a b : Nat) (y : TS) (w : Nat) : Nat → Bool := (tab.w w).om (Hh a b y)

theorem dist_of (k : K NC) (h : OpChk tab k) : Dist k := by
  cases k with
  | amerge x y z w => exact h.2
  | _ => trivial

theorem out0_hist {a b : Nat} {y : TS} (hy : Good a b y) : Hh a b y chOut = [spec a b] := by
  have hf := hy.fifo chOut
  rw [hy.fin, hy.nc chOut out_nc, List.nil_append] at hf
  have hi : init a b chOut = [] := init_empty a b chOut out_ge
  rw [hi, List.nil_append] at hf
  rw [Hh_pr out_ge, hf]
  exact final_out (spec a b)

theorem cm_oracle_exists {a b : Nat} (hd : dom a b) : ∃ y, Good a b y :=
  good_exists hd

/-- **Circuit-level safety of the kernel** (modulo H_CM_FORCED, obligation O1). -/
theorem kernel_circuit_safe_cm (a b : Nat) (ch : Fin NC → Chan)
    (H_CELLS : ∀ o : Fin NO, Cell ch (srcVal a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_CM_FORCED : ∃ y, Good a b y ∧ ∀ o : Fin NO, Forced ch (omOf a b y) (opAt o)) :
    (∀ k e, TokAt (ch out0) k e → (ch out0).dat e = spec a b) ∧
    (∀ t, closedVals (ch out0) t = List.replicate (cnt (fallB (ch out0).ack) t) (spec a b)) := by
  obtain ⟨y, hy, hF⟩ := H_CM_FORCED
  have hop := fun o => cell_op ch (omOf a b y) (srcVal a b) (opAt o) (H_CELLS o) (hF o)
    (dist_of _ (ops_ok o))
  refine Capstone.latched_const net ch (fun o => Eqn ch (omOf a b y) (srcVal a b) (opAt o))
    (fun o => (hop o).1) H_BUNDLE (fun o => (hop o).2) out0 (spec a b)
    ⟨fun c i => refT tab (Hh a b y) c.val i, fun o => eqn_sound hy rank_ok nf_pos ch (opAt o) (ops_ok o),
      fun k => ?_⟩
  show refT tab (Hh a b y) out0.val k = spec a b
  rw [ref_hist tab _ out0_desc nf_pos, out0_hist hy]
  simp [perL, Nat.mod_one]

section o1
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
theorem kernel_protocol (a b : Nat) (ch : Fin NC → Chan)
    (H_CELLS : ∀ o : Fin NO, Cell ch (srcVal a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c)) : ∀ c, Protocol (ch c) :=
  net_protocol net ch (fun o => cell_proto ch (srcVal a b) (opAt o) (H_CELLS o) (dist_of _ (ops_ok o)))
    H_BUNDLE

/-- **Circuit-level safety of the kernel, with H_CM_FORCED replaced by the count bound H_CUT.** -/
theorem kernel_circuit_safe' (a b : Nat) (ch : Fin NC → Chan)
    (H_CELLS : ∀ o : Fin NO, Cell ch (srcVal a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_CUT : ∃ y, Good a b y ∧ ∀ o : Fin NO, CutOp ch (omOf a b y) (opAt o)) :
    (∀ k e, TokAt (ch out0) k e → (ch out0).dat e = spec a b) ∧
    (∀ t, closedVals (ch out0) t = List.replicate (cnt (fallB (ch out0).ack) t) (spec a b)) := by
  obtain ⟨y, hy, hc⟩ := H_CUT
  have hp := kernel_protocol a b ch H_CELLS H_BUNDLE
  exact kernel_circuit_safe_cm a b ch H_CELLS H_BUNDLE
    ⟨y, hy, fun o => forced_of_cut ch (omOf a b y) (srcVal a b) (opAt o) (H_CELLS o) (hc o) hp⟩

/-- H_CUT implies H_CM_FORCED (so `kernel_circuit_safe'` is 8m's theorem with a hypothesis
that implies its H_CM_FORCED, given H_CELLS and H_BUNDLE). -/
theorem cm_forced_of_cut (a b : Nat) (ch : Fin NC → Chan)
    (H_CELLS : ∀ o : Fin NO, Cell ch (srcVal a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c)) (y : TS)
    (hc : ∀ o : Fin NO, CutOp ch (omOf a b y) (opAt o)) :
    ∀ o : Fin NO, Forced ch (omOf a b y) (opAt o) :=
  fun o => forced_of_cut ch (omOf a b y) (srcVal a b) (opAt o) (H_CELLS o) (hc o)
    (kernel_protocol a b ch H_CELLS H_BUNDLE)

/-- **No free contention at any arbiter stage.** Under the same hypotheses, for every arbiter
stage `.amerge x y z w` and every grant pair meeting its gate model, whenever both requests
are high one grant is already held. -/
theorem kernel_arbiters_uncontended (a b : Nat) (ch : Fin NC → Chan)
    (H_CELLS : ∀ o : Fin NO, Cell ch (srcVal a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c)) (y : TS)
    (hc : ∀ o : Fin NO, CutOp ch (omOf a b y) (opAt o))
    (o : Fin NO) (x u z : Fin NC) (w : Nat) (ho : opAt o = .amerge x u z w)
    (g1 g2 : Trace) (M : CM.AMerge (ch x) (ch u) (ch z) g1 g2) :
    ∀ t, (ch x).req t = true → (ch u).req t = true → g1 t = true ∨ g2 t = true := by
  have hp := kernel_protocol a b ch H_CELLS H_BUNDLE
  have h := hc o
  rw [ho] at h
  exact stage_uncontended M (hp x) (hp u) (hp z) _ h


end o1

end Formal.Net.KCap
