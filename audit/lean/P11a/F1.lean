import Formal.Net.CapstoneLiveWitCex
import Formal.Net.CapstoneLiveWit
/-! P11a item 1 (formal 9df5915, C-8z2): gcd_hw_live_final / gcd_hw_live_final2. -/
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapNet.Live Formal.Net.CapNet.Live.Nd Formal.Net.CapNet.Wit Formal.Net.CapNet.LiveWit

#print axioms Formal.Net.CapNet.Live.Nd.gcd_hw_live_final
#print axioms Formal.Net.CapNet.Live.Nd2.gcd_hw_live_final2
#print axioms Formal.Net.CapNet.LiveWit.nd_counterexample
#print axioms Formal.Net.CapNet.LiveWit.x_not_rel
#print axioms Formal.Net.CapNet.LiveWit.gcd_hw_live_joint_witness
#print axioms Formal.Net.CapNet.LiveWit.gcd_hw_live2_joint_witness
#print axioms Formal.Net.CapNet.LiveWit.gcd_hw_live2_witness_consistent

namespace P11a
set_option maxRecDepth 100000

/-- Own certificate: the counterexample run is non-quiescent at every tick 0..98 (the first 99
entries of the WITNESS run's certificate also certify the counterexample run). -/
theorem xnd_chk : ndChk cdX 0 (certL.take 99) = true := by decide +kernel

/-- Own: the counterexample run ALSO satisfies H_NO_DEADLOCK'' (for t <= 98 by the certificate,
for t >= 99 because start's req and ack are both high, which H_NO_DEADLOCK'' exempts). -/
theorem x_nd2 : Live.Nd2.NoDeadlock2 chX (itrW cdX) := by
  intro t _ hq
  obtain ⟨hq2, _, hnra⟩ := hq
  by_cases ht : t ≤ 98
  · have hl : t < (certL.take 99).length := by
      rw [List.length_take, lcert_len]; simp [closeL]; omega
    have := ndChk_get (certL.take 99) 0 xnd_chk t hl
    rw [Nat.zero_add] at this
    exact not_quiet_of this hq2
  · apply hnra
    constructor
    · show bv (cdX start).rq t = true
      rw [xstart_rq]; exact bv_one (by omega)
    · show bv (cdX start).ak t = true
      rw [xstart_ak]; exact bv_one (by omega)

/-- MUTATION (own): `gcd_hw_live_final2` with H_START_REL deleted is FALSE (at a=12, b=18, H=1).
So H_START_REL is genuinely necessary (the journal's "shown necessary" was not a Lean theorem). -/
theorem final2_without_start_rel_false :
    ¬ (∀ (ch : Fin NC → Chan) (itr : Itr),
      (∀ p : Fin NO, CellI ch (srcV 12 18) itr p (opAt p)) →
      (∀ c, Held (ch c)) →
      (∀ t, cnt (riseB (ch start).req) t ≤ 1) →
      (∀ p, p ≠ prodOf start → ∀ g ∈ gatesK p (opAt p), BndG 1 (gsAt ch itr) g) →
      StartEnv 1 (ch start) →
      (∀ p x u z w, opAt p = .amerge x u z w → ArbUnc 1 (ch x) (ch u) (ch z) (itr p 0) (itr p 1)) →
      Live.Nd2.NoDeadlock2 ch itr →
      ∃ e, TokAt (ch out0) 0 e) := by
  intro h
  obtain ⟨e, hT⟩ := h chX (itrW cdX) x_cells x_held x_start_once x_bnd x_start_env x_arb x_nd2
  have h1 := x_never (e + 1)
  simp [cnt, hT.1] at h1

#print axioms xnd_chk
#print axioms x_nd2
#print axioms final2_without_start_rel_false

end P11a
