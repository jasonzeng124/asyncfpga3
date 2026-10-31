import Formal.Net.CapstoneRefine2Strict
import Formal.Net.CapstoneRefineFinWit

/-!
# Audit P12a row 18: a DAG-row certificate, over a HAND-MADE obligation netlist, on a channel of
# C-8t's gcd_hw witness run (a satisfiability check of the repaired route, not a derivation)

Problem statement. The audit showed that, with the old `TxWin`, no channel of a terminating
gcd_hw run could carry a `dag`/`cert` bundling certificate, so on C-8t's run `chW` (a = 12,
b = 18, out0 closes at tick 473 with 6) every root certificate had to be `exempt`, and "a routed
witness is the job of probe cap" could not succeed. With `TxWin` indexed by the transactions
that occur, this file builds a DAG-row certificate for `out0` ON `chW` itself:

* `out0` is offered exactly once in `chW` (`o_hasOff_iff`: offer `k` exists iff `k = 0`);
* `oNet` is a 5-node obligation netlist (launch 0; data nodes 1, 2, 3 = the three low bus bits
  at the capture pins, arcs of delay [2,2]; request node 4, arc [5,5]); `checkArr oNet 4 [1,2,3] 0`
  holds by `decide` (data settles before the request changes);
* `oX : TxWin (chW out0) oSig [1,2,3] _` windows `chW`'s out0 into that netlist's run launched at
  tick 424 (offer at 429, bus 0 → 6 at 427);
* `out0_dag_cert`: the hypotheses of `BCert.dag` hold for `chW out0` (stated as an existential,
  since `BCert` is a `Prop` and would hide which constructor was used);
* `out0_dag_witness`: from that row alone (not from `w_held`), out0 of `chW` is `Held` and every
  in-transaction sample is the zero-delay value, `6 = Nat.gcd 12 18`.

Audit P14 row 10 (OVERSTATED, accepted): the certificate is a relabelling. `oNet`'s data
bits are 0, 1, 1 (= 6) by construction, and `BCert.dag` quantifies over arbitrary netlists, so
nothing here ties the row to the routed design.

What this does NOT show. `oNet` is a hand-made obligation netlist with fixed delays whose data
nodes reproduce the observed bus; it is NOT the routed gcd_hw netlist, and its delays are not
prjxray's. It shows that the repaired `TxWin`/`BCert.dag` route is satisfiable on a terminating
gcd_hw run, not that tcheck's real rows discharge it. Only out0 is certified this way; the other
25 roots of `phys4` and all `Row` hypotheses of `phys5` are untouched, and the gcd_hw witnesses
of `phys4`/`phys5` still use `exempt`/ghost fields. Three bus bits (out0's value here is 6 < 8).
-/

namespace Formal.Net.CapstoneRefine.Out0Wit
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Timing Formal.Net.CapstoneRefine
open Formal.Net.CapNet Formal.Net.CapNet.Gcd Formal.Net.CapNet.Wit

theorem o_req (u : Nat) : (chW out0).req u = decide (430 ≤ u ∧ u ≤ 472) := by
  show Formal.Net.CapNet.Wit.bv [429, 472] u = _
  simp only [Formal.Net.CapNet.Wit.bv, cntLt]
  by_cases h1 : 429 < u <;> by_cases h2 : 472 < u <;> simp [h1, h2] <;> omega

theorem o_ack (u : Nat) : (chW out0).ack u = decide (431 ≤ u ∧ u ≤ 473) := by
  show Formal.Net.CapNet.Wit.bv [430, 473] u = _
  simp only [Formal.Net.CapNet.Wit.bv, cntLt]
  by_cases h1 : 430 < u <;> by_cases h2 : 473 < u <;> simp [h1, h2] <;> omega

theorem o_dat (u : Nat) : (chW out0).dat u = if 426 < u then 6 else 0 := by
  show nv 0 [(426, 6)] u = _
  rfl

theorem o_riseB (u : Nat) : riseB (chW out0).req u = (u == 429) := by
  simp only [riseB, o_req]
  by_cases h : u = 429
  · subst h; decide
  · have hb : (u == 429) = false := by simp [h]
    rw [hb]
    cases hq : decide (430 ≤ u ∧ u ≤ 472) with
    | true => simp
    | false =>
      have h' : ¬(430 ≤ u ∧ u ≤ 472) := by simpa using hq
      simp
      omega

theorem o_cnt (u : Nat) : cnt (riseB (chW out0).req) u = if 429 < u then 1 else 0 := by
  induction u with
  | zero => rfl
  | succ u ih =>
    simp only [cnt, ih, o_riseB]
    by_cases h : u = 429
    · subst h; decide
    · have hb : (u == 429) = false := by simp [h]
      rw [hb]
      simp only [show (429 < u + 1) = (429 < u) from propext (by omega), Bool.false_eq_true,
        ite_false, Nat.add_zero]

theorem o_offAt {k r : Nat} (ho : OffAt (chW out0) k r) : k = 0 ∧ r = 429 := by
  obtain ⟨h1, h2⟩ := ho
  rw [o_riseB] at h1
  have hr : r = 429 := by simpa using h1
  subst hr
  rw [o_cnt] at h2
  simp at h2
  exact ⟨h2.symm, rfl⟩

/-- out0 is offered exactly once in `chW`. -/
theorem o_hasOff_iff (k : Nat) : HasOff (chW out0) k ↔ k = 0 := by
  constructor
  · rintro ⟨r, ho⟩; exact (o_offAt ho).1
  · rintro rfl; exact ⟨429, by rw [o_riseB]; rfl, by rw [o_cnt]; rfl⟩

/-! ## The obligation netlist and its run -/

def oNet : Netlist := ⟨[⟨0, 1, 2, 2⟩, ⟨0, 2, 2, 2⟩, ⟨0, 3, 2, 2⟩, ⟨0, 4, 5, 5⟩]⟩

theorem oNet_wf : oNet.WF := by decide

theorem oCheck : checkArr oNet 4 [1, 2, 3] 0 = true := by decide

/-- The run (every transaction index uses the same run; only `k = 0` occurs): launch rises at
0 → 1, bus bits 1, 2 (value 6) rise at 2 → 3, bit 0 stays 0, the request rises at 5 → 6. -/
def oSig (_k : Nat) : Nat → Trace := fun v t =>
  if v = 0 then decide (1 ≤ t) else if v = 1 then false
  else if v = 2 then decide (3 ≤ t) else if v = 3 then decide (3 ≤ t)
  else if v = 4 then decide (6 ≤ t) else false

def oD (i : Nat) : Nat := if i = 3 then 5 else 2

def oG : Nat → (Nat → Bool) → Bool := fun v p =>
  if v = 1 then false else if v = 2 then p 1 else if v = 3 then p 2
  else if v = 4 then p 3 else false

theorem o_shift {k : Nat} (d t : Nat) : shift d (oSig k 0) t = decide (d + 1 ≤ t) := by
  simp only [shift, oSig, ite_true]
  by_cases h : t < d
  · rw [if_pos h]; simp; omega
  · rw [if_neg h]; simp; omega

def ofrun (k : Nat) : FixedRun oNet (oSig k) where
  d := oD
  g := oG
  launch := by
    intro t h
    simp only [changes, oSig, ite_true] at h
    apply Classical.byContradiction; intro h0
    apply h; simp; omega
  range := by
    intro i a h
    match i with
    | 0 => simp [oNet] at h; subst h; decide
    | 1 => simp [oNet] at h; subst h; decide
    | 2 => simp [oNet] at h; subst h; decide
    | 3 => simp [oNet] at h; subst h; decide
    | n + 4 => simp [oNet] at h
  local_ := by
    intro v x y h
    simp only [oG]
    by_cases h1 : v = 1
    · simp [h1]
    by_cases h2 : v = 2
    · subst h2; simp only [ite_true]; exact h 1 ⟨0, 2, 2, 2⟩ rfl rfl
    by_cases h3 : v = 3
    · subst h3; simp only [ite_true]; exact h 2 ⟨0, 3, 2, 2⟩ rfl rfl
    by_cases h4 : v = 4
    · subst h4; simp only [ite_true]; exact h 3 ⟨0, 4, 5, 5⟩ rfl rfl
    simp [h1, h2, h3, h4]
  node := by
    intro v hv t
    have e1 : fixedPin oNet oD (oSig k) 1 t = shift 2 (oSig k 0) t := rfl
    have e2 : fixedPin oNet oD (oSig k) 2 t = shift 2 (oSig k 0) t := rfl
    have e3 : fixedPin oNet oD (oSig k) 3 t = shift 5 (oSig k 0) t := rfl
    by_cases h1 : v = 1
    · subst h1; simp [oSig, oG]
    by_cases h2 : v = 2
    · subst h2; simp only [oG, e1, o_shift]; simp [oSig]
    by_cases h3 : v = 3
    · subst h3; simp only [oG, e2, o_shift]; simp [oSig]
    by_cases h4 : v = 4
    · subst h4; simp only [oG, e3, o_shift]; simp [oSig]
    simp [oSig, oG, hv, h1, h2, h3, h4]

def orun (k : Nat) : Run oNet (oSig k) := (ofrun k).toRun

/-! ## H_TXWIN for out0 of `chW` -/

def oX : TxWin (chW out0) oSig [1, 2, 3] (fun k v => changes (oSig k 4) v) where
  τ _ := 424
  idle k _ := by rw [o_req, o_ack]; decide
  count k hk := by
    rw [(o_hasOff_iff k).1 hk, o_cnt]; rfl
  reqIn k r ho := by
    obtain ⟨-, hr⟩ := o_offAt ho
    subst hr
    simp [changes, oSig]
  win k u hk h1 h2 := by
    rw [o_dat]
    show _ = 0 + (if oSig k 1 (u - 424) = true then 2 ^ 0 else 0) +
      (if oSig k 2 (u - 424) = true then 2 ^ 1 else 0) +
      (if oSig k 3 (u - 424) = true then 2 ^ 2 else 0)
    simp only [oSig, show (3 ≤ u - 424) = (426 < u) from propext (by omega)]
    by_cases h : 426 < u
    · simp [h]
    · simp [h]

/-- The hypotheses of `BCert.dag` hold for out0 of C-8t's gcd_hw run. -/
theorem out0_dag_cert : ∃ (net : Netlist) (req : Nat) (data : List Nat) (setup : Nat)
    (sig : Nat → Nat → Trace), net.WF ∧ checkArr net req data setup = true ∧
    ∃ runs : ∀ k, Run net (sig k),
      Nonempty (TxWin (chW out0) sig data (fun k v => changes (sig k req) v)) :=
  ⟨oNet, 4, [1, 2, 3], 0, oSig, oNet_wf, oCheck, orun, ⟨oX⟩⟩

theorem o_zdBus : zdBus orun [1, 2, 3] 0 = 6 := by
  have z1 : zdEval oNet (orun 0).g (oSig 0 0 1) 1 = false := by
    rw [zdEval_ne _ _ _ (by decide)]; rfl
  have z2 : zdEval oNet (orun 0).g (oSig 0 0 1) 2 = true := by
    rw [zdEval_ne _ _ _ (by decide)]
    rw [show (orun 0).g = oG from rfl]
    simp [oG, oNet, zdEval_zero, oSig]
  have z3 : zdEval oNet (orun 0).g (oSig 0 0 1) 3 = true := by
    rw [zdEval_ne _ _ _ (by decide)]
    rw [show (orun 0).g = oG from rfl]
    simp [oG, oNet, zdEval_zero, oSig]
  show 0 + (if zdEval oNet (orun 0).g (oSig 0 0 1) 1 = true then 2 ^ 0 else 0) +
    (if zdEval oNet (orun 0).g (oSig 0 0 1) 2 = true then 2 ^ 1 else 0) +
    (if zdEval oNet (orun 0).g (oSig 0 0 1) 3 = true then 2 ^ 2 else 0) = 6
  rw [z1, z2, z3]; rfl

/-- **The repaired route's hypotheses are satisfiable on C-8t's gcd_hw run `chW`, with the
hand-made `oNet` (a relabelling; it does not tie the row to the routed netlist, audit P14 row 10).** From the DAG-row
certificate alone (reset and the receiver rule of `chW`'s out0, both from the run), out0 of
C-8t's run is bundled (`Held`) and every sample inside its transaction is the zero-delay value
of the obligation run, which is `6 = Nat.gcd 12 18`. -/
theorem out0_dag_witness :
    BCert (chW out0) ∧ Held (chW out0) ∧
    (∀ k r t, OffAt (chW out0) k r → r < t → (∀ s, r < s → s ≤ t → inTx (chW out0) s = true) →
      (chW out0).dat t = Nat.gcd 12 18) := by
  have B : BCert (chW out0) := BCert.dag oNet 4 [1, 2, 3] 0 oSig oNet_wf oCheck orun oX
  refine ⟨B, held_of_bcert B (w_proto out0).1 (fun t => ((w_proto out0).2 t).2), ?_⟩
  intro k r t ho hrt hb
  have hk := (o_offAt ho).1
  subst hk
  rw [sampled_eq_zd_dag oNet_wf oCheck orun oX ho hrt hb, o_zdBus]
  decide

end Formal.Net.CapstoneRefine.Out0Wit
