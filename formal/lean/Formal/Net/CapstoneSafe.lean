import Formal.Net.CapstoneNetChk
import Formal.Net.Capstone

/-!
# Probe C-8m: circuit-level safety of gcd_hw

`gcd_hw_circuit_safe`: for every run `ch` of the concrete circuit network of gcd_hw
(`CapstoneNet`, generated from bdc's graph and link placement: 465 channels, 367 operators)
* whose operators all meet their gate models (`H_CELLS`, the 8f/8j/8l cell models, which
  carry the §2 primitive hypotheses of `C-gcd_hw-hypotheses.md`),
* whose channels are all bundled (`H_BUNDLE`, the §3 per-channel timing obligations),
* and whose 9 arbiter stages pick, on every token they offer, the label of some complete
  token run of the GcdHw graph from `init a b` (`H_CM_FORCED`, obligation O1: NOT proved),

every value ever latched on `out0` is `Nat.gcd a b`, and the latched list at every time is
`gcd a b` repeated.

O2 (the total stream solution) and O7 (the concrete network, zero-delay comps folded) are
discharged here: `eqn_sound` + the kernel checks of `CapstoneNetChk`.
`cm_oracle_exists`: for `a, b < 2^31` a complete token run exists (so H_CM_FORCED asks for
something that exists at token level); for other inputs none does and the theorem is vacuous.
-/

namespace Formal.Net.CapNet.Gcd
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.GcdHw Formal.Net.CapSafe

/-- The oracle of arbiter stage `w`: the labels of the complete token run `y`. -/
def omOf (a b : Nat) (y : TS) (w : Nat) : Nat → Bool := (tab.w w).om (Hh a b y)

theorem dist_of (k : K NC) (h : OpChk tab k) : Dist k := by
  cases k with
  | amerge x y z w => exact h.2
  | _ => trivial

theorem out0_hist {a b : Nat} {y : TS} (hy : Good a b y) : Hh a b y 250 = [Nat.gcd a b] := by
  have hf := hy.fifo 250
  rw [hy.fin, hy.nc 250 (by decide), List.nil_append] at hf
  have hi : GcdHw.Gcd.init a b 250 = [] := init_empty a b 250 (by decide)
  rw [hi, List.nil_append] at hf
  rw [Hh_pr (by decide), hf]
  exact (GcdHw.Gcd.final_store (Nat.gcd a b)).1

theorem cm_oracle_exists {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) : ∃ y, Good a b y :=
  good_exists ha hb

/-- **Circuit-level safety of gcd_hw** (modulo H_CM_FORCED, obligation O1). -/
theorem gcd_hw_circuit_safe (a b : Nat) (ch : Fin NC → Chan)
    (H_CELLS : ∀ o : Fin NO, Cell ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_CM_FORCED : ∃ y, Good a b y ∧ ∀ o : Fin NO, Forced ch (omOf a b y) (opAt o)) :
    (∀ k e, TokAt (ch out0) k e → (ch out0).dat e = Nat.gcd a b) ∧
    (∀ t, closedVals (ch out0) t = List.replicate (cnt (fallB (ch out0).ack) t) (Nat.gcd a b)) := by
  obtain ⟨y, hy, hF⟩ := H_CM_FORCED
  have hop := fun o => cell_op ch (omOf a b y) (srcV a b) (opAt o) (H_CELLS o) (hF o)
    (dist_of _ (ops_ok o))
  refine Capstone.latched_const net ch (fun o => Eqn ch (omOf a b y) (srcV a b) (opAt o))
    (fun o => (hop o).1) H_BUNDLE (fun o => (hop o).2) out0 (Nat.gcd a b)
    ⟨fun c i => refT tab (Hh a b y) c.val i, fun o => eqn_sound hy rank_ok nf_pos ch (opAt o) (ops_ok o),
      fun k => ?_⟩
  show refT tab (Hh a b y) out0.val k = Nat.gcd a b
  rw [ref_hist tab _ out0_desc nf_pos, out0_hist hy]
  simp [perL, Nat.mod_one]

end Formal.Net.CapNet.Gcd
