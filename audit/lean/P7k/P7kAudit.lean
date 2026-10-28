import Formal.Cells.ConstraintsKappa
import Formal.Cells.OnNetlistArbKappa
import Formal.Cells.OnGcdArbKappa
import Formal.Core.Delay.CornerCode
import Formal.Core.Delay.InvolutionTransfer
import Formal.Core.Delay.InvolutionDMin
import Formal.Core.TernaryChannels
import Formal.Cells.RigContract

/-! Auditor P7k: axioms + non-vacuity witnesses for 861de85, 6763571, 66d94fa/2f0994e,
065a361, 807448a/21b1b7c. -/

open Formal.Core.Substrate

set_option maxRecDepth 20000

/-! ## 1. Axioms -/
#print axioms Formal.Cells.ConstraintsKappa.allOK_of_gen
#print axioms Formal.Cells.ConstraintsKappa.allOK_iff_gen
#print axioms Formal.Cells.ConstraintsKappa.sandwich
#print axioms Formal.Cells.ConstraintsKappa.box_unsound_with_kappa
#print axioms Formal.Cells.ConstraintsKappa.slow_only_unsound
#print axioms Formal.Cells.ConstraintsKappa.endpointNat_not_sufficient
#print axioms Formal.Cells.OnNetlistArbKappa.safe_s1c2_cons
#print axioms Formal.Cells.OnNetlistArbKappa.unsafe_s1c2_cons
#print axioms Formal.Cells.OnNetlistArbKappa.verdict_s1c2_cons_κE
#print axioms Formal.Cells.OnNetlistArbKappa.verdict_s4c1_cons_κA
#print axioms Formal.Cells.OnNetlistArbKappa.tie_s1c1
#print axioms Formal.Cells.OnNetlistArbKappa.nonvacuous_lit
#print axioms Formal.Cells.OnGcdArbKappa.rows_ok
#print axioms Formal.Cells.OnGcdArbKappa.row_verdict
#print axioms Formal.Cells.OnGcdArbKappa.lit_min
#print axioms Formal.Cells.OnGcdArbKappa.design_lit_safe
#print axioms Formal.Cells.OnGcdArbKappa.design_lit_tight
#print axioms Formal.Cells.OnGcdArbKappa.cons_neg
#print axioms Formal.Cells.OnGcdArbKappa.design_gate_lit
#print axioms Formal.Cells.OnGcdArbKappa.lit_holds_srv
#print axioms Formal.Cells.OnGcdArbKappa.design_gate_nonvacuous
#print axioms Formal.Core.CornerCode.ruleA_code_iff
#print axioms Formal.Core.CornerCode.ruleA_code_model_iff
#print axioms Formal.Core.CornerCode.ruleA_slack_sound
#print axioms Formal.Core.CornerCode.ruleA_slack_tight
#print axioms Formal.Core.DelayInvolutionTransfer.transfer_sep
#print axioms Formal.Core.DelayInvolutionTransfer.chan_sigOf
#print axioms Formal.Core.DelayInvolutionTransfer.sep_threshold_sharp
#print axioms Formal.Core.DelayInvolutionTransfer.rat_transfer_example
#print axioms Formal.Core.DelayInvolution.InvolutionPair.exists_dmin
#print axioms Formal.Core.DelayInvolution.InvolutionPair.sep_threshold_exact
#print axioms Formal.Core.DelayInvolution.InvolutionPair.sep_transfer_exact
#print axioms Formal.Core.DelayInvolution.InvolutionPair.transfer_sep'
#print axioms Formal.Core.TernaryChannels.rcausal_of_nodeChan
#print axioms Formal.Core.TernaryChannels.ternary_noGlitch_channels
#print axioms Formal.Core.TernaryChannels.ternary_settle_channels
#print axioms Formal.Core.TernaryChannels.zero_delay_chan_unsound
#print axioms Formal.Core.TernaryChannels.zero_delay_inertial_unsound
#print axioms Formal.Core.TernaryChannels.sample_not_causal
#print axioms Formal.Cells.RigContract.stale_window
#print axioms Formal.Cells.RigContract.stale_nonvacuous
#print axioms Formal.Cells.RigContract.verdict_current
#print axioms Formal.Cells.RigContract.verdict_attrib
#print axioms Formal.Cells.RigContract.idx_setup

/-! ## 2. Witnesses -/

namespace P7kAudit
open Formal.Cells.ConstraintsKappa

/-- κ = 1/11. -/
def k11 : Kappa := ⟨1, 11, by decide, by decide⟩

/-- Own two-arc model: data [10, 33], request [20, 44] at κ = 1/11. -/
def Mown : CornerModel Bool := ⟨fun e => if e then ⟨20, 44, by decide⟩ else ⟨10, 33, by decide⟩, k11⟩

theorem own_gen : GenOK Mown.κ (Mown.path [false]) (Mown.path [true]) 0 0 := by decide
theorem own_allOK : AllOK Mown [false] [true] 0 0 := allOK_of_gen Mown _ _ own_gen

/-- A nontrivial realization at an interior corner (w0 = 2, w1 = 1, c = 1/3):
nominal data 53/3 ≈ 17.7, request 84/3 = 28; delays 19 and 26 are within 1/11. -/
theorem own_real : Mown.RealizesAt ⟨2, 1, by decide⟩ (fun e => if e then 26 else 19) := by
  intro e; cases e <;> decide

/-- OnNetlistArbKappa: the safe hypothesis is met by a realization at the SLOW corner
at κ = 1/11 with nonzero scatter on the late arc (wAC S = 955 → 1000 ≤ 12/11·955 = 1041.8). -/
theorem s1c2_scat_slow :
    ∀ e, Scat k11 Corner.slow (Formal.Cells.OnNetlistArbKappa.A_s1c2_cons e)
      ((fun e => if e = Formal.Cells.OnNetlistArbKappa.Arc.wAC then 1000 else
        (Formal.Cells.OnNetlistArbKappa.A_s1c2_cons e).S) e) := by
  intro e; cases e <;> decide

/-- The undecided gap is real: at κ = 200/1103 (strictly between the proved safe bound
197/1103 and the proved unsafe bound 203/1103), the FAST endpoint already admits a violating
assignment: late ⌊(1+κ)·453⌋ = 535 > early Σ⌈(1-κ)F⌉ = 215+37+100+37+145 = 534. -/
def k200 : Kappa := ⟨200, 1103, by decide, by decide⟩
theorem s1c2_gap_unsafe_at_200 :
    let d : Formal.Cells.OnNetlistArbKappa.Arc → Nat := fun e =>
      match e with
      | .wAC => 535 | .wSt => 215 | .aSt => 37 | .wQG => 100 | .aG => 37 | .wGC => 145
      | e => (Formal.Cells.OnNetlistArbKappa.A_s1c2_cons e).F
    (∀ e, Scat k200 Corner.fast (Formal.Cells.OnNetlistArbKappa.A_s1c2_cons e) (d e)) ∧
      d .wSt + d .aSt + d .wQG + d .aG + d .wGC < d .wAC ∧
      ¬ Formal.Cells.ArbA0Fork.Safe Formal.Cells.ArbA0Fork.F2 Formal.Cells.ArbA0Fork.G2 true
        (Formal.Cells.OnNetlistArbKappa.dlOf d) := by
  intro d
  refine ⟨?_, by decide, Formal.Cells.OnNetlistArbKappa.not_safe2 (by decide) (by decide) (by decide)⟩
  intro e; cases e <;> decide

open Formal.Cells.OnGcdArbKappa in
/-- OnGcdArbKappa: an interior-corner realization of the lit model with nonzero κ
(c = 1/2, κ = 1/30: every arc at its rounded-down nominal) for the minimising arbiter. -/
theorem gcd_real_mid :
    let k : Kappa := ⟨1, 30, by decide, by decide⟩
    (litModel k v_g3_merge12_uarb1).RealizesAt ⟨1, 1, by decide⟩
      (fun e => (nom ⟨1, 1, by decide⟩ ((litModel k v_g3_merge12_uarb1).arc e)) / 2) := by
  intro k e; cases e <;> decide

open Formal.Cells.OnGcdArbKappa in
/-- Mutation (data): +1 ps on rg2's FAST_MIN of the minimising arbiter breaks the design
certificate at 16587/374773 (the threshold is data-sensitive at the binding row). -/
def vMut : E → Quad := fun e =>
  if e = .rg2 then ((v_g3_merge12_uarb1 e).1 + 1000, (v_g3_merge12_uarb1 e).2) else v_g3_merge12_uarb1 e
open Formal.Cells.OnGcdArbKappa in
theorem gcd_mut_breaks : certFor .lit F_rt1b vMut 16587 374773 = false := by decide +kernel
open Formal.Cells.OnGcdArbKappa in
theorem gcd_orig_ok : certFor .lit F_rt1b v_g3_merge12_uarb1 16587 374773 = true := by decide +kernel

/-! CornerCode: `pass` is the code's predicate; spot values. -/
open Formal.Core.CornerCode in
theorem cc_spot : pass 0 1204 1004 ∧ ¬ pass 0 1203 1004 ∧ pass 0 1206 1005 ∧ ¬ pass 0 1205 1005 := by
  decide

/-! Involution: δmin of ratPair is 1 (dmin unique), and a concrete Chan instance. -/
open Formal.Core.DelayInvolution Formal.Core.DelayInvolutionTransfer in
theorem rat_dmin_eq : ratPair.dmin = 1 := (ratPair.isDMin_iff.mp rat_dmin).symm

open Formal.Core.DelayInvolution Formal.Core.DelayInvolutionTransfer Formal.Core.DelayPure in
theorem rat_chan_2n (N : ℕ) :
    Chan (4 / 3) 2 (sigOf N (fun n => 2 * (n : ℝ))) (sigOf N (ratPair.tent (fun n => 2 * (n : ℝ)))) :=
  rat_transfer_example _ (fun n => by push_cast; linarith) N

/-! Ternary: a nontrivial instance of `ternary_settle_channels`: a buffer of a step input
(false before 1, true from 1), node = input delayed by 3/2 (transport Chan 1 2). -/
open Formal.Core.TernaryChannels Formal.Core.Ternary in
theorem tern_settle_witness :
    let c : ℝ → Unit → Bool := fun s _ => decide (1 ≤ s)
    let σ : ℝ → Unit → Bool := fun s _ => decide (1 ≤ s - 3 / 2)
    (∀ i, NodeChan 1 2 (exc bufNet c σ i) (node σ i)) ∧
    resultB bufNet [()] (fun _ => false) (fun _ => true) (fun _ => false) () = K3.one ∧
    (∀ s, (1 : ℝ) + ([()] : List Unit).length * 2 ≤ s → σ s () = true) := by
  intro c σ
  have hch : ∀ i, NodeChan 1 2 (exc bufNet c σ i) (node σ i) := fun i =>
    chan_nodeChan (lo := 1) (hi := 2) le_rfl le_rfl
      (Formal.Core.DelayPure.chan_shift (lo := 1) (hi := 2) (d := 3 / 2) (by norm_num) (by norm_num)
        (fun s => decide (1 ≤ s)))
  have hB : resultB bufNet [()] (fun _ => false) (fun _ => true) (fun _ => false) () = K3.one := by
    decide
  refine ⟨hch, hB, ?_⟩
  exact ternary_settle_channels bufNet [()] (fun i => by cases i; simp) (fun _ => false)
    (fun _ => true) (fun _ => false) c σ
    (fun s x => by by_cases h : 1 ≤ s <;> simp [c, h]) 1
    (fun s hs => by funext x; simp [c, hs]) (δ := 1) one_pos hch
    (fun s hs => by funext x; simp only [σ, decide_eq_false_iff_not, not_le]; linarith) () true hB

end P7kAudit
