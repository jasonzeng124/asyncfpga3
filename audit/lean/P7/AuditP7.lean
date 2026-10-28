import Formal.Net.CapstoneWitness
import Formal.Net.CapstoneWitness3
import Formal.Net.CapstoneLiveNdWalk
import Formal.Net.IpowCapMain
import Formal.Net.CapstoneRig
import Formal.Cells.RigSrc
import Formal.Cells.ResetGcdNetRe

/-! Auditor P7 (formal head 6863284): statements, axioms, consistency, and negative probes. -/

namespace AuditP7
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd

set_option maxRecDepth 100000

/-! ## Statements as elaborated -/
#check @Formal.Net.CapNet.Wit.gcd_hw_joint_witness
#check @Formal.Net.CapNet.Gcd.gcd_hw_circuit_safe''
#check @Formal.Net.CapNet.Live.Nd.gcd_hw_live_final
#check @Formal.Net.IpowCap.ipow_circuit_safe3
#check @Formal.Net.IpowHw.ipowSpec
#check @Formal.Net.CapNet.Gcd.gcd_rig_first
#check @Formal.Net.CapNet.Gcd.H_ENV
#check @Formal.Cells.RigSrc.gcd_rig_first_env
#check @Formal.Cells.ResetGcdRe.re_matches
#check @Formal.Cells.ResetGcdRe.re_reset_ternary

/-! ## Axioms -/
#print axioms Formal.Net.CapNet.Wit.gcd_hw_joint_witness
#print axioms Formal.Net.CapNet.Wit.gcd_hw_witness_consistent
#print axioms Formal.Net.CapNet.Wit.gcd_hw_joint_witness3
#print axioms Formal.Net.CapNet.Gcd.gcd_hw_circuit_safe''
#print axioms Formal.Net.CapNet.Gcd.gcd_hw_circuit_safe3
#print axioms Formal.Net.CapNet.Live.Nd.gcd_hw_live_final
#print axioms Formal.Net.CapNet.Live.Nd.walk_ends
#print axioms Formal.Net.IpowCap.ipow_circuit_safe3
#print axioms Formal.Net.IpowCap.ipow_circuit_safe
#print axioms Formal.Net.CapNet.Gcd.gcd_rig_first
#print axioms Formal.Cells.RigSrc.gcd_rig_first_env
#print axioms Formal.Cells.ResetGcdRe.re_matches
#print axioms Formal.Cells.ResetGcdRe.re_reset_ternary
#print axioms Formal.Cells.ResetGcdRe.re_reset_binary
#print axioms Formal.Cells.ResetGcdRe.re_reset_release
#print axioms Formal.Cells.ResetGcdRe.re_census

/-! ## 8t: the witness's hypotheses are literally the safety theorem's (it applies) -/

/-- The joint witness, destructured and fed to `gcd_hw_circuit_safe''` directly: the run latches
its first out0 token, the value is 6, and the safety theorem (same constants) gives gcd 12 18. -/
theorem joint_feeds_safety : ∃ ch : Fin NC → Chan, ∃ e,
    TokAt (ch out0) 0 e ∧ (ch out0).dat e = 6 ∧ (ch out0).dat e = Nat.gcd 12 18 := by
  obtain ⟨ch, h1, h2, h3, h4, k, e, hk, hv⟩ := Formal.Net.CapNet.Wit.gcd_hw_joint_witness
  refine ⟨Formal.Net.CapNet.Wit.chW, Formal.Net.CapNet.Wit.out0Close,
    Formal.Net.CapNet.Wit.w_out0.1, Formal.Net.CapNet.Wit.w_out0.2, ?_⟩
  exact (gcd_hw_circuit_safe'' 12 18 _ Formal.Net.CapNet.Wit.w_cells Formal.Net.CapNet.Wit.w_held
    Formal.Net.CapNet.Wit.w_start_once ⟨_, Formal.Net.CapNet.Wit.yW_good, Formal.Net.CapNet.Wit.yW_walk⟩).1
    0 _ Formal.Net.CapNet.Wit.w_out0.1

/-- The run is the generated 465-channel network's: `opAt` is CapstoneNetChk's (`ops.getD`). -/
example : (Formal.Net.CapNet.Gcd.ops).length = 367 := by decide
example : NC = 465 := rfl
example : out0 = (416 : Fin NC) := rfl
example : Formal.Net.CapNet.Wit.out0Close = 473 := rfl
#print axioms joint_feeds_safety

/-! ## Mutation tests on the 8t witness (expected: the kernel checker REJECTS) -/

/-- M1: the same run claimed for b = 24 instead of 18 (sources' buses no longer match). -/
theorem mut_src : (Formal.Net.CapNet.Gcd.ops.drop 186).all
    (fun k => Formal.Net.CapNet.Wit.kChk Formal.Net.CapNet.Wit.cdA (srcV 12 24) k) = false := by
  decide +kernel

/-- M2: channel 7's request toggles one tick early ([3,101] -> [2,101]). -/
def cdsM : List Formal.Net.CapNet.Wit.CD := Formal.Net.CapNet.Wit.cds.set 7 ⟨[2, 101], [99, 197], 0, [(2, 12)], [[2, 100]]⟩
def cdM (c : Fin NC) : Formal.Net.CapNet.Wit.CD := cdsM.getD c.val ⟨[], [], 0, [], []⟩
theorem mut_toggle : Formal.Net.CapNet.Gcd.ops.all
    (fun k => Formal.Net.CapNet.Wit.kChk cdM (srcV 12 18) k) = false := by decide +kernel

/-! ## 8z: the 8t witness does NOT meet gcd_hw_live_final's H_BOUNDED_DELAY' -/

theorem src_a_op : opAt (187 : Fin NO) = .src 0 0 0 := by decide
theorem src_a_ne : (187 : Fin NO) ≠ prodOf start := by decide
theorem cdA0 : Formal.Net.CapNet.Wit.cdA 0 = ⟨[0, 41], [40, 138], 12, [], []⟩ := by decide +kernel

theorem a_quiet (t : Nat) (h : 139 ≤ t) :
    (Formal.Net.CapNet.Wit.chW 0).req t = false ∧ (Formal.Net.CapNet.Wit.chW 0).ack t = false := by
  simp only [Formal.Net.CapNet.Wit.chW, Formal.Net.CapNet.Wit.wch, Formal.Net.CapNet.Wit.CD.ch, cdA0,
    Formal.Net.CapNet.Wit.bv, Formal.Net.CapNet.Wit.cntLt]
  have h1 : (0 : Nat) < t := by omega
  have h2 : (41 : Nat) < t := by omega
  have h3 : (40 : Nat) < t := by omega
  have h4 : (138 : Nat) < t := by omega
  simp [h1, h2, h3, h4]

/-- After tick 138 the `a` source has request and acknowledge low for ever, so its LUT
(`req` follows `¬ack`) is excited towards 1 on every window: no finite `H` bounds it. -/
theorem witness_not_bounded (H : Nat) (itr : Formal.Net.CapNet.Live.Itr) :
    ¬ (∀ p, p ≠ prodOf start → ∀ g ∈ Formal.Net.CapNet.Live.gatesK p (opAt p),
        Formal.Net.CapNet.Live.BndG H (Formal.Net.CapNet.Live.gsAt Formal.Net.CapNet.Wit.chW itr) g) := by
  intro hB
  have hg : Formal.Net.CapNet.Live.gw (fun s => s.rq 0) (fun s => !s.ak 0) ∈
      Formal.Net.CapNet.Live.gatesK 187 (opAt 187) := by
    rw [src_a_op]; simp [Formal.Net.CapNet.Live.gatesK]
  have := hB 187 src_a_ne _ hg true 139 (by
    intro u h1 _
    simp [Formal.Net.CapNet.Live.gw, Formal.Net.CapNet.Live.gsAt, (a_quiet u h1).2])
  obtain ⟨u, h1, _, hu⟩ := this
  simp [Formal.Net.CapNet.Live.gw, Formal.Net.CapNet.Live.gsAt, (a_quiet u h1).1] at hu
#print axioms witness_not_bounded

/-! ## 8s2: the 8t run does not meet gcd_rig_first's H_ENV (start rises at 0 with out0.ack low);
an all-low-at-0 run can never meet H_ENV and offer out0 (start must rise first). -/
theorem witness_not_env : ¬ Formal.Net.CapNet.Gcd.H_ENV Formal.Net.CapNet.Wit.chW := by
  intro h
  have := h 0 (by decide +kernel)
  revert this; decide +kernel


/-- Facts for the (prose) rig witness X = chW shifted by one tick: only the three source requests
toggle at step 0, so every non-source reset field of X (= chW at tick 1) holds, and start's request
list is [0, 99] (in X: high at 0, falls at 98, never rises: H_ENV vacuous). -/
theorem step0_only_src : (List.range 465).all (fun c =>
    let x := Formal.Net.CapNet.Wit.cds.getD c ⟨[], [], 0, [], []⟩
    (decide (c < 3) == (x.rq.head? == some 0)) && !(x.rq.drop 1).contains 0 && !x.ak.contains 0 &&
      !(x.dt.map Prod.fst).contains 0 && x.ax.all (fun l => !l.contains 0)) = true := by decide +kernel

end AuditP7
