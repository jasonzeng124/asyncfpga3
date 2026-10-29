import Formal.Cells.SelfAuditB9
import Formal.Cells.FiniteNetWit
import Formal.Cells.FiniteNetSrc
import Formal.Cells.FiniteOrN
import Formal.Cells.AssumeGuaranteeMuxNNet
import Formal.Cells.ArbCounterRunsAM
import Formal.Cells.ArbAMergeRunWit
import Formal.Cells.AssumeGuaranteeCap

/-! Independent audit P12b of shard B commits 14484c29..1fd99ef0 (auditor's own file). -/

namespace AuditP12b
open Formal.Cells

/-! ## A. INITs used by the arbiter models = INITs in cells/rtl (extracted by the auditor:
bd_arb.v ustate 64'hFFF0_FFB2_ACAC_ACAC, ugrant 64'h0C0C_0C0C_A0A0_A0A0;
bd_ce.v bd_c2 64'h00E8_00E8_00E8_00E8, bd_c2n_set 64'hFFB2_FFB2_FFB2_FFB2). -/
example : ArbHeldTimed.INIT_HELD = 0xFFF0FFB2ACACACAC := rfl
example : ArbHeldTimed.INIT_GRANTS = 0x0C0C0C0CA0A0A0A0 := rfl
example : ArbHeldTimed.INIT_C2 = 0x00E800E800E800E8 := rfl
example : ArbHandover.INIT_C2N_SET = 0xFFB2FFB2FFB2FFB2 := rfl
example : ArbHandover.INIT_GRANTS = 0x0C0C0C0CA0A0A0A0 := rfl

/-! ## B. The rt1 counter-run really overlaps, and only for 1 ps. -/
open ArbCounterRuns in
theorem w1v_overlap_exactly_1634 :
    ∀ t : Int, (W1V.g1 t && W1V.g2 t) = true ↔ t = 1634 := by
  intro t; simp [W1V]; omega

open ArbCounterRuns in
theorem w1s_no_overlap : ∀ t : Int, (W1S.g1 t && W1S.g2 t) = false := by
  intro t; simp [W1S] <;> omega

/-! ## C. Segment-form (infinite-run) contracts have the same hole as SelfAuditB9's
truncated ones: a pinless cell's `Contract` is the bare claim that its node's segments
are clean. So Bseg's `GcdNetOK` / Bmux2's / Bmn's segment-form network theorems
(`gcd_hw_safe_net`, `_net2`, `_net3`) are affected by the same driver freedom, not only the
finite forms that SelfAuditB9 proves it for. -/
open AssumeGuaranteeEndsNet AssumeGuaranteeLinks in
theorem contract_nil_iff {ι : Type} (D : GD ι) (c : ι) (hnil : D.pins c = []) :
    Contract D c ↔ ∀ k, SegK (D.O c) (D.τ c) k := by
  constructor
  · intro h k
    exact h.1 k (by intro p hp; rw [hnil] at hp; simp at hp)
  · intro h
    exact ⟨fun k _ => h k, by intro p hp; rw [hnil] at hp; simp at hp⟩

/-! ## D. Bnet's / Bfin2's chain-end contracts are of the same "conclusion-only" shape:
any end node that is clean meets its SRC_SEG regardless of the acknowledge. -/
theorem fchain_src_seg_of_clean (D : AssumeGuaranteeLinks.ChainData) (L : Nat → Nat → Prop)
    (h : FiniteNet.GPh (D.O 0) (D.τ 0) (L 0)) :
    ∀ T, FiniteNet.GPhT (D.ack 0) (D.εB 0) (L 1) T →
      FiniteNet.GPhT (D.O 0) (D.τ 0) (L 0) (T + D.lo 0) :=
  fun T _ => h (T + D.lo 0)

end AuditP12b

/-! ## E. Axioms of the audited headline theorems and of this file. -/
#print axioms Formal.Cells.FiniteNet.gcd_hw_safe_fin_chains
#print axioms Formal.Cells.FiniteNetWit.gcd_hw_fin_chains_witness
#print axioms Formal.Cells.FiniteNetWit.gcd_hw_fin_chains_consistent
#print axioms Formal.Cells.FiniteNet.ag_trunc
#print axioms Formal.Cells.FiniteNet.ag_trunc_zero_cex
#print axioms Formal.Cells.FiniteNet.gcd_hw_safe_fin_net
#print axioms Formal.Cells.FiniteNetWit2.gcd_hw_fin_net_witness
#print axioms Formal.Cells.FiniteNetSrc.chW_steer_unwired
#print axioms Formal.Cells.FiniteNetSrc.chW_src_unwired
#print axioms Formal.Cells.FiniteNetSrc.steer_fires
#print axioms Formal.Cells.FiniteOrN.or3_init_unique
#print axioms Formal.Cells.FiniteOrN.gcd_hw_safe_fin_net3'
#print axioms Formal.Cells.SelfAuditB9.fcellOK_nil_iff
#print axioms Formal.Cells.SelfAuditB9.flink_env1_local
#print axioms Formal.Cells.AssumeGuaranteeMuxNNet.gcd_hw_safe_fin_net3
#print axioms Formal.Cells.ArbCounterRuns.rt1_counter_run
#print axioms Formal.Cells.ArbCounterRuns.rt1_boundary_run
#print axioms Formal.Cells.ArbCounterRuns.ho_counter_run
#print axioms Formal.Cells.ArbCounterRuns.ho_boundary_run
#print axioms Formal.Cells.ArbCounterRunsAM.rereqQ_counter_run
#print axioms Formal.Cells.ArbCounterRunsAM.rereqR_counter_run
#print axioms Formal.Cells.ArbCounterRunsAM.rereqGf_counter_run
#print axioms Formal.Cells.ArbCounterRunsAM.rereqQ2_counter_run
#print axioms Formal.Cells.ArbCounterRunsAM.rereqR2_counter_run
#print axioms Formal.Cells.ArbCounterRunsAM.rereqG2_counter_run
#print axioms Formal.Cells.ArbAMergeRun.amerge_of_plan
#print axioms Formal.Cells.ArbAMergeRun.amerge_witness
#print axioms Formal.Cells.ArbAMergeRun.sep_cex_run
#print axioms Formal.Cells.AssumeGuaranteeCap.gcd_hw_safe_chains
#print axioms AuditP12b.w1v_overlap_exactly_1634
#print axioms AuditP12b.w1s_no_overlap
#print axioms AuditP12b.contract_nil_iff
#print axioms AuditP12b.fchain_src_seg_of_clean
