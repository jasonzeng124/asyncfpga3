import Formal.Cells.ZeroDelayTokChain
import Formal.Cells.ZeroDelayNetWit
open Formal.Core.LutList

/-!
# ZeroDelayTokWit: non-vacuity of the `k`-token closed-loop chain (two stages, two tokens)

Probe Bzd3 (shard B); note `formal/notes/B-zero-delay-tok.md`. Two `bd_link` stages wired in a
closed loop (`ZeroDelayNetWit`'s loop, every read a nonzero transport delay 380..900 ps), the
source sending TWO tokens (values 1 then 0) 3000 ps apart, the sink answering both. The coupled
traces come from `ZeroDelayNetWit`'s joint simulator `jr`. Every hypothesis of `chain_specK`
holds (`chain2_cell`, `chain2_beh`), so both stages meet the two-token spec (`chain2_witness`).
Core Lean only.
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace Formal.Cells.ZeroDelayTok
open Formal.Cells
open Formal.Cells.CElemFn
open Formal.Cells.LibGapSteer (Rd Rd.const)
open Formal.Cells.LibGapLatch
open Formal.Cells.LinkExact
open Formal.Cells.ZeroDelayNet (Rds jr tr rdN tr_eq rdN_eq tn)

/-- Two-token parameter: token 0's value, then token 1's. -/
def tk (a b : Int) : Nat → Int := fun j => if j = 0 then a else b

/-- Stage 0 (token 0 = `ZeroDelayNetWit.Pw0`; token 1 three microseconds later). -/
def Q0 : ParK :=
  { k := 2, W := 2000, W1 := 2001,
    Ra := tk 3000 6000, Ra1 := tk 3001 6001, Fa := tk 4500 7500, Fa1 := tk 4501 7501,
    Rb := tk 3800 6800, Rb1 := tk 4041 7041, Fb := tk 5300 8300, Fb1 := tk 5541 8541,
    Td := tk 2500 5600, Tn := tk 5500 20000,
    Alo := 400, Ahi := 520, Blo := 380, Bhi := 500, Qlo := 300, Qhi := 420,
    Rlo := 600, Rhi := 900, Dlo := 350, Dhi := 480, Elo := 450, Ehi := 700,
    Flo := 280, Fhi := 400 }
/-- Stage 1 (request windows = stage 0's node windows; data from stage 0's latch). -/
def Q1 : ParK :=
  { k := 2, W := 2000, W1 := 2001,
    Ra := tk 3400 6400, Ra1 := tk 3521 6521, Fa := tk 4900 7900, Fa1 := tk 5021 8021,
    Rb := tk 4300 7300, Rb1 := tk 4301 7301, Fb := tk 6000 9000, Fb1 := tk 6001 9001,
    Td := tk 4221 7221, Tn := tk 6850 20000,
    Alo := 400, Ahi := 520, Blo := 380, Bhi := 500, Qlo := 300, Qhi := 420,
    Rlo := 600, Rhi := 900, Dlo := 350, Dhi := 480, Elo := 450, Ehi := 700,
    Flo := 280, Fhi := 400 }
def Qw (i : Nat) : ParK := if i = 0 then Q0 else Q1

theorem two_all {k : Nat} (hk : k = 2) {p : Nat → Prop} (h0 : p 0) (h1 : p 1) : ∀ j < k, p j := by
  intro j hj; subst hk
  rcases j with _ | _ | j
  · exact h0
  · exact h1
  · omega

theorem two_one {k : Nat} (hk : k = 2) {p : Nat → Prop} (h0 : p 0) : ∀ j, j + 1 < k → p j := by
  intro j hj; subst hk
  rcases j with _ | j
  · exact h0
  · omega

theorem stage_all {p : Nat → Prop} (h0 : p 0) (h1 : p 1) : ∀ i < 2, p i := two_all rfl h0 h1

theorem wfQ0 : WfK Q0 :=
  ⟨by decide, two_all rfl (wf_of _ (by decide)) (wf_of _ (by decide)), two_one rfl (by decide)⟩
theorem wfQ1 : WfK Q1 :=
  ⟨by decide, two_all rfl (wf_of _ (by decide)) (wf_of _ (by decide)), two_one rfl (by decide)⟩
theorem rowsQ0 : RowsK Q0 :=
  ⟨two_all rfl ((conj_iff _).2 (by decide)) ((conj_iff _).2 (by decide)),
   two_one rfl (by unfold Rearm; decide)⟩
theorem rowsQ1 : RowsK Q1 :=
  ⟨two_all rfl ((conj_iff _).2 (by decide)) ((conj_iff _).2 (by decide)),
   two_one rfl (by unfold Rearm; decide)⟩

theorem one_st {p : Nat → Prop} (h0 : p 0) : ∀ i, i + 1 < 2 → p i := two_one rfl h0

theorem chain2_cell : ChainCellK 2 Qw :=
  ⟨by decide, stage_all rfl rfl, stage_all wfQ0 wfQ1, stage_all rowsQ0 rowsQ1,
    one_st (two_all rfl (by decide) (by decide)), one_st (two_all rfl (by decide) (by decide)),
    one_st (by decide), one_st (by decide), one_st (two_all rfl (by decide) (by decide))⟩

/-- Source request: pulses `[3001, 4500)` and `[6001, 7500)`. -/
def srcA (x : Int) : K3 := if (3001 ≤ x ∧ x < 4500) ∨ (6001 ≤ x ∧ x < 7500) then .t else .f
/-- Sink acknowledge: pulses `[4301, 6000)` and `[7301, 9000)`. -/
def snkB (x : Int) : K3 := if (4301 ≤ x ∧ x < 6000) ∨ (7301 ≤ x ∧ x < 9000) then .t else .f

/-- The coupled simulator: traces 0, 1 = the two nodes, 2, 3 = the two latch bits. -/
def F2 (n : Nat) (g : Nat → Nat → K3) : Nat → K3
  | 0 => c2nK (srcA ((n : Int) - 520)) (rdN g n 500 1) (rdN g n 420 0) (win 0 2000 ((n : Int) - 900))
  | 1 => c2nK (rdN g n 520 0) (snkB ((n : Int) - 500)) (rdN g n 420 1) (win 0 2000 ((n : Int) - 900))
  | 2 => latM (dW ((n : Int) - 480)) (rdN g n 700 0) (rdN g n 400 2)
  | 3 => latM (rdN g n 480 2) (rdN g n 700 1) (rdN g n 400 3)
  | _ => .f

def A2 (i : Nat) : Int → K3 := if i = 0 then srcA else tr F2 0
def B2 (i : Nat) : Int → K3 := if i = 0 then tr F2 1 else snkB
def D2 (i : Nat) : Int → K3 := if i = 0 then dW else tr F2 2
def C2 (i : Nat) : Int → K3 := tr F2 i
def Q2 (i : Nat) : Int → K3 := tr F2 (i + 2)

/-- Every pin at its slowest box value. -/
def rd2 : Rds :=
  ⟨Rd.const 520, Rd.const 500, Rd.const 420, Rd.const 900, Rd.const 480, Rd.const 700,
   Rd.const 400⟩

theorem chain2_beh :
    ChainBehK 2 Qw (fun j => decide (j = 0)) (fun _ => rd2) (win 0 2000) A2 B2 D2 C2 Q2 := by
  refine ⟨stage_all ?_ ?_, stage_all (fun x h1 h2 => win_t h1 h2) (fun x h1 h2 => win_t h1 h2),
    stage_all (fun x h => win_f2 (by simp [Qw, Q0] at h; omega))
      (fun x h => win_f2 (by simp [Qw, Q1] at h; omega)),
    stage_all ?_ ?_, stage_all ?_ ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_,
    fun x h => ?_, two_all rfl ?_ ?_, two_all rfl ?_ ?_, fun x h => ?_, two_all rfl ?_ ?_,
    two_all rfl ?_ ?_, two_all rfl ?_ ?_⟩
  · refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> decide
  · refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> decide
  · intro t ht
    show tr F2 0 t = c2nK (srcA (t - 520)) (tr F2 1 (t - 500)) (tr F2 0 (t - 420))
      (win 0 2000 (t - 900))
    rw [tr_eq _ _ ht]
    simp only [F2]
    rw [rdN_eq _ _ _ _ (by decide), rdN_eq _ _ _ _ (by decide), tn t ht]
    rfl
  · intro t ht
    show tr F2 1 t = c2nK (tr F2 0 (t - 520)) (snkB (t - 500)) (tr F2 1 (t - 420))
      (win 0 2000 (t - 900))
    rw [tr_eq _ _ ht]
    simp only [F2]
    rw [rdN_eq _ _ _ _ (by decide), rdN_eq _ _ _ _ (by decide), tn t ht]
    rfl
  · intro t ht
    show tr F2 2 t = latM (dW (t - 480)) (tr F2 0 (t - 700)) (tr F2 2 (t - 400))
    rw [tr_eq _ _ ht]
    simp only [F2]
    rw [rdN_eq _ _ _ _ (by decide), rdN_eq _ _ _ _ (by decide), tn t ht]
    rfl
  · intro t ht
    show tr F2 3 t = latM (tr F2 2 (t - 480)) (tr F2 1 (t - 700)) (tr F2 3 (t - 400))
    rw [tr_eq _ _ ht]
    simp only [F2]
    rw [rdN_eq _ _ _ _ (by decide), rdN_eq _ _ _ _ (by decide), rdN_eq _ _ _ _ (by decide),
      tn t ht]
    rfl
  · rcases i with _ | i
    · rfl
    · omega
  · rcases i with _ | i
    · rfl
    · omega
  · rcases i with _ | i
    · rfl
    · omega
  all_goals simp only [Qw, Q0, Q1, tk, A2, B2, D2, srcA, snkB, if_true, Nat.add_one_ne_zero,
    if_false, show (2 : Nat) - 1 = 1 from rfl] at *
  all_goals first
    | (intro x h1 h2; rw [if_pos (by omega)])
    | (intro x h1 h2; simp only [dW]; rw [if_pos (by omega)]; rfl)
    | (intro x h1 h2; simp only [dW]; rw [if_neg (by omega)]; rfl)
    | (intro x h1 h2; simp only [show (1 : Nat) = 0 ↔ False from by decide, if_false] at h1 h2;
       rw [if_pos (by omega)])
    | (intro x h1; simp only [show (1 : Nat) = 0 ↔ False from by decide, if_false] at h1;
       rw [if_neg (by omega)])
    | (intro x h1 h2; rw [if_neg (by omega)])
    | (rw [if_neg (by omega)])
    | skip

/-- **Non-vacuity (two stages, two tokens).** The closed loop meets every hypothesis of
`chain_specK` with nonzero delays everywhere and two tokens of different values; a coupled
behaviour exists, and both stages meet the two-token spec on it. -/
theorem chain2_witness :
    ChainCellK 2 Qw ∧ ∃ rd r A B D C Q,
      ChainBehK 2 Qw (fun j => decide (j = 0)) rd r A B D C Q ∧
      ∀ i < 2, SpecK (Qw i) (fun j => decide (j = 0)) (rd i).pd (rd i).pe (C i) (Q i) :=
  ⟨chain2_cell, _, _, _, _, _, _, _, chain2_beh, chain_specK chain2_cell chain2_beh⟩

end Formal.Cells.ZeroDelayTok
