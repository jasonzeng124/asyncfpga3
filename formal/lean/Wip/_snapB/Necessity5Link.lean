import Formal.Cells.RulesKL

/-!
# Necessity5Link: `bd_link_dc` corrected rules K' and L' are tight to 1 tick

Probe Bnx5 (shard B). Rows `bd_link_dc.rule_K_corrected` (`RuleK'`) and
`bd_link_dc.rule_L_corrected` (`RuleL'`) were "sufficient", backed by
`RulesKL.dc_capture` (corrected K' and L', the causal hypotheses H_LAUNCH,
H_LT_FALL_K/L, the SDF window bounds H_ELO/H_EHI/H_DHI/H_FHI and H_HOLD give
the token in the latch bit).

`KClaim s` / `LClaim s` is `dc_capture` with `RuleK'` / `RuleL'` weakened by
`s` ticks, every other hypothesis verbatim. `k0`, `l0`: slack 0 is the
shipped theorem. `k1_false : ¬ KClaim 1`, `l1_false : ¬ LClaim 1`.

* **Assumed (the runs):** a WHOLE `bd_link_dc` stage (W = 1, odd latch bit,
  BROAD = 1, LDN = 0, DELAY = DACK = 0), every LUT its REAL INIT (`ub`
  `0000F320..`, `ua` `0000FA80..`, `uld` `00000F08..`, `ult` `0101..`,
  latch `ODD` `B8B8..`) as a fixed transport gate (one corner), gate
  equations for ALL `t`, four-phase-legal environment, guard 0, feedback-pin
  arc 1.
  - K run: Bk's `counter_K` trace verbatim. `RuleK'` fails by exactly 1
    (`4 = 3 + 1`), `RuleL'` holds, every other `dc_capture` hypothesis holds
    (`k_hyps`); the bit sees D = 1 from 8, and holds 0 at 11.
  - L run: Bk's `counter_L` trace with the sender raising its second
    request at 4 instead of 5 (`a` fell at 3, so this is four-phase legal)
    and `req_in -> ub` 3 instead of 2, so that `RuleK'` now HOLDS (with
    equality, 5 ≤ 5) while `RuleL'` fails by exactly 1 (`5 = 4 + 1`). The
    controller outputs b, a, ld, lt and the latch bit are Bk's signals
    unchanged (`lB'_tr`, `lA'_tr` re-proved; `lLd_tr`, `lLt_tr`, `lQ_tr`
    reused). The bit sees D = 1 from 3 and holds 0 at 9.
* **Proved:** necessary at the boundary (one parameter point per rule) for
  the Lean `≤` form at guard 0. Not an iff.
* **NOT covered:** guards `> 0` (the JSON form with `guard ≥ 1` is strict,
  Bs; a run at guard 0 off by 1 is off by `g + 1` against guard `g`), wider
  delay windows, the coded rules (already refuted by `counter_K`/`counter_L`),
  the causal hypotheses H_LT_FALL_K/L themselves (stated, not derived).

Core Lean only.
-/

namespace Formal.Cells.Necessity5Link
open Formal.Cells Formal.Cells.Bundling Formal.Cells.RulesKL

/-- `dc_capture`'s conclusion, with `RuleK'` weakened by `sK` and `RuleL'` by `sL`. -/
def Claim (sK sL : Nat) : Prop :=
  ∀ (d en q : Sig) (dlo dhi elo ehi flo fhi : Nat),
    LatchRel d en q dlo dhi elo ehi flo fhi →
    dlo ≤ dhi → elo ≤ ehi → flo ≤ fhi → 1 ≤ flo →
    ∀ (n : KNums) (L : LNums) (p : LPin), p ∈ L.pins → ∀ (fbArc g : Nat)
    (Ton Toff Tnext T0 Td Tnew : Nat) (v : Bool),
    (∀ t, Ton ≤ t → t < Toff → en t = true) →
    (∀ t, Toff ≤ t → t < Tnext → en t = false) →
    (∀ t, Td ≤ t → t < Tnew → d t = v) →
    Td ≤ T0 →
    T0 + n.tReq + n.dCtl ≤ Toff →
    Ton + L.tLd + L.tB + p.dCtl ≤ Toff →
    n.dFan + n.enArcMin ≤ elo → p.dFan + p.enArcMin ≤ elo →
    ehi ≤ p.lateWire + p.enArcMax →
    dhi ≤ n.dWire + n.dArcMax →
    fhi ≤ n.loopWire + fbArc → fhi ≤ p.loopWire + fbArc →
    n.data + fbArc + g ≤ n.close + sK →
    (∀ p ∈ L.pins, ∀ p' ∈ L.pins, p.follow + fbArc + g ≤ L.tLd + L.tB + p'.close + sL) →
    Toff + ehi ≤ Tnew + dlo →
    ∀ t, max (Ton + ehi) (Td + dhi) ≤ t → t < Tnext + elo → q t = v

theorem claim0 : Claim 0 0 := by
  intro d en q dlo dhi elo ehi flo fhi hLat hdw hew hfw hl n L p hp fbArc g Ton Toff Tnext T0 Td
    Tnew v h_on h_off h_d hLa hK1 hL1 hE1 hE2 hE3 hD hF1 hF2 hK hL hH
  exact dc_capture d en q dlo dhi elo ehi flo fhi hLat hdw hew hfw hl n L p hp fbArc g
    Ton Toff Tnext T0 Td Tnew v h_on h_off h_d hLa hK1 hL1 hE1 hE2 hE3 hD hF1 hF2
    (by unfold RuleK'; omega) (fun p hp p' hp' => by have := hL p hp p' hp'; omega) hH

/-! ## K run (Bk's `counter_K`) -/

def pK : LPin := ⟨1, 0, 1, 0, 1, 2⟩

theorem k_viol : kK.data + 1 + 0 = kK.close + 1 := by decide
theorem k_L_ok : ∀ p ∈ kL.pins, ∀ p' ∈ kL.pins, p.follow + 1 + 0 ≤ kL.tLd + kL.tB + p'.close := by
  intro p hp p' hp'; simp [kL] at hp hp'; subst hp; subst hp'; decide

theorem k1_false : ¬ Claim 1 0 := by
  intro h
  obtain ⟨-, -, -, -, -, hLat, -, -, -, -, -, -, hq⟩ := counter_K
  have := h kD kLt caQ 1 1 1 1 3 3 hLat (by decide) (by decide) (by decide) (by decide)
    kK kL pK (by simp [kL, pK]) 1 0 0 10 100 8 8 100 true
    (fun t _ h2 => by simp [kLt]; omega) (fun t h1 _ => by simp [kLt]; omega)
    (fun t h1 _ => by simp [kD, kReq]; omega)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
    (by decide) (fun p hp p' hp' => by have := k_L_ok p hp p' hp'; omega) (by decide)
    11 (by decide) (by decide)
  have h11 := hq 0
  simp at h11; rw [h11] at this; exact absurd this (by decide)

/-! ## L run: Bk's `counter_L` with the request re-raised at 4, `req_in -> ub` 3 -/

def lReq' : Sig := fun t => decide (t < 2 ∨ 4 ≤ t)

theorem lB'_tr : Transport UB [(lReq', 3), (lAck, 1), (lLd, 1), (lB, 1), (zero, 0), (zero, 0)] lB := by
  intro t
  show lB t = lutB UB [lReq' (t - 3), lAck (t - 1), lLd (t - 1), lB (t - 1), false, false]
  by_cases ht : t < 14
  · revert t; decide
  · have h1 : lReq' (t - 3) = true := by simp [lReq']; omega
    have h2 : lAck (t - 1) = false := by simp [lAck]; omega
    have h3 : lLd (t - 1) = false := by simp [lLd]; omega
    have h4 : lB (t - 1) = true := by simp [lB]; omega
    have h5 : lB t = true := by simp [lB]; omega
    rw [h1, h2, h3, h4, h5]; decide

theorem lA'_tr : Transport UA [(lReq', 1), (lB, 1), (lLd, 1), (lA, 1), (zero, 0), (zero, 0)] lA := by
  intro t
  show lA t = lutB UA [lReq' (t - 1), lB (t - 1), lLd (t - 1), lA (t - 1), false, false]
  by_cases ht : t < 14
  · revert t; decide
  · have h1 : lReq' (t - 1) = true := by simp [lReq']; omega
    have h2 : lB (t - 1) = true := by simp [lB]; omega
    have h3 : lLd (t - 1) = false := by simp [lLd]; omega
    have h4 : lA (t - 1) = true := by simp [lA]; omega
    have h5 : lA t = true := by simp [lA]; omega
    rw [h1, h2, h3, h4, h5]; decide

/-- Four-phase legality of the new sender: it raises `req_in` (at 4) only
after `ack_in = a` fell (at 3), and withdrew it (at 2) only after `a` rose. -/
theorem lReq'_legal : lA 3 = false ∧ lReq' 3 = false ∧ lReq' 4 = true ∧ lA 1 = true ∧
    lReq' 2 = false := by decide

/-- Rule K's numbers on the new trace: `req_in -> ub` is 3. -/
def lK' : KNums := ⟨3, 1, 0, 1, 0, 1, 3⟩
def pL : LPin := ⟨1, 0, 1, 0, 1, 3⟩

/-- `RuleK'` holds (with equality), `RuleL'` fails by exactly 1. -/
theorem l_k_ok : lK'.data + 1 + 0 ≤ lK'.close := by decide
theorem l_viol : pL.follow + 1 + 0 = lL.tLd + lL.tB + pL.close + 1 := by decide

theorem l1_false : ¬ Claim 0 1 := by
  intro h
  have hLat : LatchRel lD lLt lQ 1 1 1 1 4 4 :=
    odd_latch (transport_gate ODD [(lD, 1, 1, 1), (lLt, 1, 1, 1), (lQ, 4, 4, 4),
      (zero, 0, 0, 0), (zero, 0, 0, 0), (zero, 0, 0, 0)] lQ (by simp) lQ_tr)
  have := h lD lLt lQ 1 1 1 1 4 4 hLat (by decide) (by decide) (by decide) (by decide)
    lK' lL pL (by simp [lL, pL]) 1 0 5 8 100 4 3 100 true
    (fun t h1 h2 => by simp [lLt]; omega) (fun t h1 _ => by simp [lLt]; omega)
    (fun t h1 _ => by simp [lD]; omega)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
    (by decide)
    (fun p hp p' hp' => by
      simp [lL] at hp hp'; subst hp; subst hp'; decide)
    (by decide)
    9 (by decide) (by decide)
  have h9 : lQ 9 = false := by decide
  rw [h9] at this; exact absurd this (by decide)

/-- The whole L stage: every controller LUT and the latch bit at their real
INITs (gate equations for all `t`). -/
theorem l_stage :
    Transport UB [(lReq', 3), (lAck, 1), (lLd, 1), (lB, 1), (zero, 0), (zero, 0)] lB ∧
    Transport UA [(lReq', 1), (lB, 1), (lLd, 1), (lA, 1), (zero, 0), (zero, 0)] lA ∧
    Transport ULD [(lLt, 1), (one, 0), (lA, 1), (lLd, 1), (zero, 0), (zero, 0)] lLd ∧
    Transport ULT [(lB, 1), (lA, 1), (lAck, 1), (zero, 0), (zero, 0), (zero, 0)] lLt ∧
    Transport ODD [(lD, 1), (lLt, 1), (lQ, 4), (zero, 0), (zero, 0), (zero, 0)] lQ :=
  ⟨lB'_tr, lA'_tr, lLd_tr, lLt_tr, lQ_tr⟩

/-! ## Non-vacuity of the slack-0 side: the K stage with a 2-tick loop

`counter_K`'s controller signals, the latch loop 2 (= loop wire 1 + I2
arc 1) instead of 3: corrected K holds with equality, L' holds, and the bit
captures the token (`q = 1` from 9 on, for all `t`). -/

def qW : Sig := fun t => decide (9 ≤ t)

theorem qW_tr : Transport ODD [(kD, 1), (kLt, 1), (qW, 2), (zero, 0), (zero, 0), (zero, 0)] qW := by
  intro t
  show qW t = lutB ODD [kD (t - 1), kLt (t - 1), qW (t - 2), false, false, false]
  rw [odd_bin]
  by_cases ht : t < 14
  · revert t; decide
  · have hen : kLt (t - 1) = false := by simp [kLt]; omega
    rw [hen]; simp [qW]; omega

def kKw : KNums := ⟨1, 1, 0, 1, 0, 1, 1⟩
def kLw : LNums := ⟨1, 1, [⟨1, 0, 1, 0, 1, 1⟩]⟩

theorem witness :
    LatchRel kD kLt qW 1 1 1 1 2 2 ∧ RuleK' kKw 1 0 ∧ RuleL' kLw 1 0 ∧
    (∀ t, 9 ≤ t → t < 101 → qW t = true) := by
  have hLat : LatchRel kD kLt qW 1 1 1 1 2 2 :=
    odd_latch (transport_gate ODD [(kD, 1, 1, 1), (kLt, 1, 1, 1), (qW, 2, 2, 2),
      (zero, 0, 0, 0), (zero, 0, 0, 0), (zero, 0, 0, 0)] qW (by simp) qW_tr)
  have hK : RuleK' kKw 1 0 := by unfold RuleK'; decide
  have hL : RuleL' kLw 1 0 := by
    intro p hp p' hp'; simp [kLw] at hp hp'; subst hp; subst hp'; decide
  refine ⟨hLat, hK, hL, ?_⟩
  -- every hypothesis of the shipped theorem, discharged on this run
  have := claim0 kD kLt qW 1 1 1 1 2 2 hLat (by decide) (by decide) (by decide) (by decide)
    kKw kLw ⟨1, 0, 1, 0, 1, 1⟩ (by simp [kLw]) 1 0 0 10 100 8 8 100 true
    (fun t _ h2 => by simp [kLt]; omega) (fun t h1 _ => by simp [kLt]; omega)
    (fun t h1 _ => by simp [kD, kReq]; omega)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
    (by unfold RuleK' at hK; exact hK)
    (fun p hp p' hp' => by have := hL p hp p' hp'; omega) (by decide)
  intro t h1 h2; exact this t (by simpa using h1) (by simpa using h2)

end Formal.Cells.Necessity5Link
