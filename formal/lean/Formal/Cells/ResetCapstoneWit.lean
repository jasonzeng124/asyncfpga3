import Formal.Cells.ResetGcdVec2
open Formal.Core.LutList

/-!
# Probe Brz (shard B): a non-degenerate witness for gcd_hw's network reset theorems

Bfw's `nonvac_net` witnesses `gcd_reset_vec_net` / `cellRunW_clean` / `gcd_reset_vec_of_net`
with the unit-delay run, `D = W = 0`, `F = 23`, `E = 57`: H_STEER_HOLD is vacuous there
(`(F + 34, E] = (57, 57]` is empty). Audit P8 flagged it as degenerate.

`wRun` here is a GMW run of the real `gNet` (all 3322 nodes, real INITs) with

    D = 40, W = 1, F = 967 (= 23·(D+W+1) + W, H_HOLD_LONG tight), E = F + 40 = 1007,

so H_STEER_HOLD constrains the six steer outputs on the 6 steps `(1001, 1007]`. The run:
* power-up state = the reset state (every node at its reset value `gR`, data 0);
* rst 1 on `[0, F]`, 0 after; data 0;
* up to `E` every gate HOLDS (GMW allows it); every pin reads its source one step late
  (`rd k = k - 1`, so the wire bound `W = 1` is used);
* from `E` on, the unit-delay simulation.

It is a run because the reset state is a binary fixed point of every LUT under rst = 1 and
data 0 (`fix_ok`, decided over all 3322 nodes); it is `Bounded 40 1` because the only gates
excited in `(F, E]` are released at `E + 1`, at most `D + 1` steps after they became excited.

`wit_frontier_held`: the gate bound is really used: `ulink_n1__1`'s controller (node 1696)
sees LUT value 1 at every step of `[F + 2, E]` and still shows 0 (a gate delayed by 39 steps).

What this does NOT show: an intermediate-delay run (the witness is the slow extreme: every
gate uses its whole budget), or anything about the board.
-/

namespace Formal.Cells.ResetCapstoneWit
open Formal.Cells Formal.Cells.TernarySound Formal.Cells.ResetContract Formal.Cells.ResetGcd

theorem ite_t {α : Type} {c : Prop} [Decidable c] (h : c) (a b : α) : (if c then a else b) = a := by
  simp [h]
theorem ite_f {α : Type} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) : (if c then a else b) = b := by
  simp [h]

/-! ## The reset state is a binary fixed point (rst = 1, data 0) -/

def fixAt (n : Nat) : Bool :=
  match gNode n with
  | .gate init pins => lutB init (pinsB (fun _ i => gR i) pins 0) == gR n
  | .input => true

def fixChunk (lo k : Nat) : Bool := (List.range' lo k).all fixAt

theorem fx0 : fixChunk 0 400 = true := by decide +kernel
theorem fx1 : fixChunk 400 400 = true := by decide +kernel
theorem fx2 : fixChunk 800 400 = true := by decide +kernel
theorem fx3 : fixChunk 1200 400 = true := by decide +kernel
theorem fx4 : fixChunk 1600 400 = true := by decide +kernel
theorem fx5 : fixChunk 2000 400 = true := by decide +kernel
theorem fx6 : fixChunk 2400 400 = true := by decide +kernel
theorem fx7 : fixChunk 2800 400 = true := by decide +kernel
theorem fx8 : fixChunk 3200 122 = true := by decide +kernel

theorem fix_mem {lo k : Nat} (h : fixChunk lo k = true) {n : Nat} (h1 : lo ≤ n) (h2 : n < lo + k) :
    fixAt n = true :=
  List.all_eq_true.1 h n (List.mem_range'_1.2 ⟨h1, h2⟩)

theorem fix_ok (n : Nat) : fixAt n = true := by
  by_cases h : n < gM
  · have hM : gM = 3322 := rfl
    rcases Nat.lt_or_ge n 400 with h0 | h0
    · exact fix_mem fx0 (by omega) (by omega)
    rcases Nat.lt_or_ge n 800 with h1 | h1
    · exact fix_mem fx1 (by omega) (by omega)
    rcases Nat.lt_or_ge n 1200 with h2 | h2
    · exact fix_mem fx2 (by omega) (by omega)
    rcases Nat.lt_or_ge n 1600 with h3 | h3
    · exact fix_mem fx3 (by omega) (by omega)
    rcases Nat.lt_or_ge n 2000 with h4 | h4
    · exact fix_mem fx4 (by omega) (by omega)
    rcases Nat.lt_or_ge n 2400 with h5 | h5
    · exact fix_mem fx5 (by omega) (by omega)
    rcases Nat.lt_or_ge n 2800 with h6 | h6
    · exact fix_mem fx6 (by omega) (by omega)
    rcases Nat.lt_or_ge n 3200 with h7 | h7
    · exact fix_mem fx7 (by omega) (by omega)
    · exact fix_mem fx8 (by omega) (by omega)
  · unfold fixAt gNode; rw [ite_f h]

theorem fix_gate {n init : Nat} {pins : List Src} (hn : gNode n = .gate init pins) :
    lutB init (pinsB (fun _ i => gR i) pins 0) = gR n := by
  have := fix_ok n; unfold fixAt at this; rw [hn] at this; simpa using this

theorem gR0 : gR 0 = true := by decide

/-! ## The run -/

def F : Nat := 967
def E : Nat := 1007
def D : Nat := 40
def W : Nat := 1

/-- The state at `E` (rst released). -/
def cE (i : Nat) : Bool := if i = 0 then false else gR i
/-- Inputs after `E`: rst 0, data 0. -/
def inpE (_ _ : Nat) : Bool := false

/-- The frozen part. -/
def frz (k i : Nat) : Bool := if i = 0 then decide (k ≤ F) else gR i

def wv (k i : Nat) : Bool := if k ≤ E then frz k i else simB gNet inpE cE (k - E) i

def wrd (k _ _ : Nat) : Nat := if k < E then k - 1 else k

theorem wv_ge {k : Nat} (h : E ≤ k) (i : Nat) : wv k i = simB gNet inpE cE (k - E) i := by
  unfold wv
  by_cases hk : k ≤ E
  · have : k = E := by omega
    subst this; rw [ite_t (Nat.le_refl _), Nat.sub_self]
    show frz E i = cE i
    unfold frz cE
    by_cases h0 : i = 0
    · rw [ite_t h0, ite_t h0]; decide
    · rw [ite_f h0, ite_f h0]
  · rw [ite_f hk]

theorem wv_lt {k : Nat} (h : k ≤ E) (i : Nat) : wv k i = frz k i := by simp [wv, h]

theorem gate_ne0 {j init : Nat} {pins : List Src} (h : gNet.node j = .gate init pins) : j ≠ 0 := by
  intro h0; subst h0; cases h

theorem sim_succ (k j init : Nat) (pins : List Src) (h : gNet.node j = .gate init pins) :
    simB gNet inpE cE (k + 1) j = lutB init (pinsB (fun _ i => simB gNet inpE cE k i) pins 0) := by
  show (match gNet.node j with
    | .input => inpE (k + 1) j
    | .gate init pins => lutB init (pinsB (fun _ i => simB gNet inpE cE k i) pins 0)) = _
  rw [h]

theorem pinsB_congr (f g : Nat → Nat → Bool) (h : ∀ p i, f p i = g p i) :
    ∀ (pins : List Src) (q : Nat), pinsB f pins q = pinsB g pins q := by
  intro pins
  induction pins with
  | nil => intro _; rfl
  | cons s ss ih =>
    intro q; simp only [pinsB, ih]; cases s <;> simp [srcB, h]

/-- In the frozen region, every gate's LUT value is its reset value while its rst pin reads 1. -/
theorem eF : F = 967 := rfl
theorem eE : E = 1007 := rfl
theorem eD : D = 40 := rfl

theorem frz_gate {k j : Nat} (h0 : j ≠ 0) : frz k j = gR j := by
  unfold frz; rw [ite_f h0]

theorem frz_rst (k : Nat) : frz k 0 = decide (k ≤ F) := rfl

theorem exc_frozen {k j init : Nat} {pins : List Src} (h : gNet.node j = .gate init pins)
    (hk : k ≤ F) :
    lutB init (pinsB (fun _ i => wv (wrd k j 0) i) pins 0) = gR j := by
  rw [← fix_gate h]
  refine congrArg (lutB init) (pinsB_congr _ _ ?_ pins 0)
  intro _ i
  have hr : wrd k j 0 ≤ k := by unfold wrd; split <;> omega
  have := eF; have := eE
  rw [wv_lt (by omega)]
  by_cases h0 : i = 0
  · subst h0; rw [gR0, frz_rst]; exact decide_eq_true (by omega)
  · rw [frz_gate h0]

def wRun : Run gNet wv where
  rd := wrd
  rd_le k _ _ := by unfold wrd; split <;> omega
  gate k j init pins h := by
    by_cases hk : k < E
    · left
      rw [wv_lt (by omega), wv_lt (by omega), frz_gate (gate_ne0 h), frz_gate (gate_ne0 h)]
    · right
      rw [wv_ge (by omega), show k + 1 - E = (k - E) + 1 by omega, sim_succ _ _ _ _ h]
      refine congrArg (lutB init) (pinsB_congr _ _ ?_ pins 0)
      intro q i
      show _ = wv (wrd k j q) i
      have e : wrd k j q = k := by unfold wrd; rw [ite_f hk]
      rw [e, wv_ge (by omega)]

theorem exc_eq (k j init : Nat) (pins : List Src) :
    wRun.exc init pins k j = lutB init (pinsB (fun _ i => wv (wrd k j 0) i) pins 0) := by
  unfold Run.exc
  congr 1

theorem wBounded : Bounded gNet wv wRun D W where
  wire k j p := by show k ≤ wrd k j p + 1; unfold wrd; split <;> omega
  gate k j init pins b h hb := by
    have := eF; have := eE; have := eD
    by_cases hkE : E ≤ k + D
    · -- release at E+1 or later: the unit-delay part updates at once
      refine ⟨max k E + 1, by omega, by omega, ?_⟩
      have hx := hb (max k E) (by omega) (by omega)
      rw [← hx, wv_ge (by omega), show max k E + 1 - E = (max k E - E) + 1 by omega,
        sim_succ _ _ _ _ h, exc_eq]
      refine congrArg (lutB init) (pinsB_congr _ _ ?_ pins 0)
      intro q i
      have e : wrd (max k E) j 0 = max k E := by unfold wrd; rw [ite_f (by omega)]
      rw [e, wv_ge (by omega)]
    · -- the window lies in the reset hold: the LUT value is the reset value
      have hkF : k ≤ F := by omega
      refine ⟨k, Nat.le_refl _, by omega, ?_⟩
      have hx := hb k (Nat.le_refl _) (by omega)
      rw [exc_eq, exc_frozen h hkF] at hx
      rw [← hx, wv_lt (by omega), frz_gate (gate_ne0 h)]

/-! ## The hypotheses of `gcd_reset_vec_net` -/

theorem w_rst_clean : ∀ k, 0 < k → k ≤ F → TernaryPhases.InputsIn gNet wv gA k := by
  intro k _ hk n hn
  have := eF; have := eE
  rw [wv_lt (by omega)]
  by_cases h0 : n = 0
  · subst h0; rw [frz_rst, decide_eq_true hk]; rfl
  · unfold gA; rw [ite_f h0]; rfl

theorem w_hold_long : (maxRank + 2) * (D + W + 1) + W ≤ F := by decide

theorem w_rst_low : ∀ k, F < k → k ≤ E → wv k 0 = false := by
  intro k h1 h2
  rw [wv_lt h2, frz_rst]; exact decide_eq_false (by omega)

theorem zL_cold : ResetGcdWave.zL.all (fun z => !gR z && z != 0) = true := by decide +kernel

theorem w_steer_hold : ∀ k z, z ∈ ResetGcdWave.zL → F + 34 < k → k ≤ E → wv k z = false := by
  intro k z hz _ h2
  have := List.all_eq_true.1 zL_cold z hz
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at this
  rw [wv_lt h2, frz_gate this.2, this.1]

/-- The steer window is not empty: H_STEER_HOLD constrains 6 steps. -/
theorem w_steer_window : F + 34 + 6 = E := by decide

/-- The LUT value of node 1696 at the released, reset-valued state. -/
theorem n1696_excited : ∃ init pins, gNode 1696 = .gate init pins ∧
    lutB init (pinsB (fun _ i => cE i) pins 0) = true ∧ gR 1696 = false :=
  ⟨_, _, rfl, by decide +kernel, by decide⟩

/-- The gate bound is used: node 1696 (`ulink_n1__1.ctl`) sees LUT value 1 at every step of
`[F + 2, E]` and still shows its reset value 0 there. -/
theorem wit_frontier_held : ∀ k, F + 2 ≤ k → k ≤ E →
    (∃ init pins, gNode 1696 = .gate init pins ∧ wRun.exc init pins k 1696 = true) ∧
    wv k 1696 = false := by
  intro k h1 h2
  have := eF; have := eE
  obtain ⟨init, pins, hg, hx, hr⟩ := n1696_excited
  refine ⟨⟨init, pins, hg, ?_⟩, ?_⟩
  · rw [exc_eq, ← hx]
    refine congrArg (lutB init) (pinsB_congr _ _ ?_ pins 0)
    intro _ i
    have hw : F < wrd k 1696 0 ∧ wrd k 1696 0 ≤ E := by unfold wrd; split <;> omega
    rw [wv_lt hw.2]
    by_cases h0 : i = 0
    · subst h0; rw [frz_rst]; unfold cE; simp only [ite_true]; exact decide_eq_false (by omega)
    · rw [frz_gate h0]; unfold cE; rw [ite_f h0]
  · rw [wv_lt h2, frz_gate (by decide), hr]

/-- The pin lag is used: every pin read before `E` is one step old. -/
theorem wit_wire_lag : ∀ k j p, 0 < k → k < E → wRun.rd k j p + 1 = k := by
  intro k j p h1 h2; show wrd k j p + 1 = k; unfold wrd; rw [ite_t h2]; omega

/-- **Non-degenerate non-vacuity** of Bfw's `cellRunW_clean`, `gcd_reset_vec_net` and
`gcd_reset_vec_of_net`: a bounded GMW run of the real `gNet` with `D = 40 > 0`, `W = 1 > 0`,
`F = 967`, `E = 1007` meets H_RST_CLEAN, H_HOLD_LONG, H_RST_LOW and H_STEER_HOLD, the last on
the 6-step window `(1001, 1007]`. -/
theorem nonvac_net2 :
    ∃ (v : Nat → Nat → Bool) (Rn : Run gNet v), Bounded gNet v Rn 40 1 ∧
      (∀ k, 0 < k → k ≤ 967 → TernaryPhases.InputsIn gNet v gA k) ∧
      (maxRank + 2) * (40 + 1 + 1) + 1 ≤ 967 ∧
      (∀ k, 967 < k → k ≤ 1007 → v k 0 = false) ∧
      (∀ k z, z ∈ ResetGcdWave.zL → 967 + 34 < k → k ≤ 1007 → v k z = false) ∧
      967 + 34 < 1007 :=
  ⟨wv, wRun, wBounded, w_rst_clean, w_hold_long, w_rst_low, w_steer_hold, by decide⟩

/-- The network theorem applies to the witness (nothing per-cell supplied). -/
example : True := by
  have _h := ResetGcdVec2.gcd_reset_vec_net wRun wBounded F E w_rst_clean
    w_hold_long w_rst_low w_steer_hold
  trivial

end Formal.Cells.ResetCapstoneWit
