import Formal.Core.Delay.GLSResolve
import Formal.Cells.ArbHandover

/-!
# `FID_RESOLVE` on ANY single-cell feedback LUT; bd_c2n and the arbiter's q loop

Probe GLSResolve2, shard A (notes: `formal/notes/A-gls-resolve.md`, second part). Core Lean
only. Builds on `GLSResolve.lean` (unchanged): the resolver `St`/`eval`/`nba`/`step` there is
cell-independent; only its `Run` fixed bd_c2's function. Here:

* `GRun p F v0`: a resolver run of a single-cell loop whose sampled LUT value at step `t` is
  `F t (o (t - TLOOP))` (`R:gen.py:661-682`: a LUT output routed back into one of its own
  pins). `lutF INIT k P` is the fid mux tree (`GLSFid.lut6`) of the cell's INIT with pin `k`
  the feedback and the other pins the traces `P t i` the mux sees. `Run` (bd_c2) is `GRun` at
  `c2F` (`run_iff_grun`, `c2F_lut`).
* generic segment theorems for a set event from a quiet state (`seg_wide`, `seg_runt_pre`,
  `seg_runt`, `seg_window_end`), for ANY cell function that, along the run, reads
  `F t false = x t` and `F t true = true` (the cell is being set by a pulse `x`);
  `run_runt_gen'` re-derives GLSResolve's `run_runt_gen` (same statement) from them.
* instances: bd_c2n (INIT `00B2…`, `bd_ce.v:49`), the arbiter's state node `ustate` O6
  (INIT `FFF0_FFB2_ACAC_ACAC`, `bd_arb.v:245-247`, feedback pin I2).
* the arbiter near tie under the resolver (`arb_near_tie`), and the composed counterexample
  `arb_double_ack`: after a committed near tie whose resolution time exceeds the server's
  response, BOTH ack C-elements are high under one A0 pulse.
* the late runt (`late_runt_lost`): a pulse still present when the ignore window ends is
  applied at `ign_until`, and its end, less than TLOOP later, is a new runt; when that draw
  does not commit, a pulse of width `≥ TLOOP` ends with `q = 0`.
-/

namespace Formal.Core.GLSResolveGen

open Formal.Core.GLSResolve
open Formal.Core.GLSFid (Res resolve lut6)

/-! ## 1. Any single-cell loop -/

/-- The closed loop's step function for a cell whose sampled value at `t` is `F t qfb`. -/
def GG (p : Prm) (F : Nat → Bool → Bool) (v0 : Bool) : Nat → (Nat → St) → St
  | 0, _ => St.init v0
  | t + 1, h => step p (t + 1) (F (t + 1) (h (t + 1 - p.L)).o) (h t)

/-- **A resolver run of a single-cell feedback loop** with cell function `F`. -/
def GRun (p : Prm) (F : Nat → Bool → Bool) (v0 : Bool) (st : Nat → St) : Prop :=
  ∀ t, st t = GG p F v0 t st

theorem GG_causal (p : Prm) (F : Nat → Bool → Bool) (v0 : Bool) (hL : 1 ≤ p.L) :
    Causal (GG p F v0) := by
  intro t h h' e
  cases t with
  | zero => rfl
  | succ t => simp only [GG]; rw [e t (by omega), e (t + 1 - p.L) (by omega)]

theorem grun_exists (p : Prm) (F : Nat → Bool → Bool) (v0 : Bool) (hL : 1 ≤ p.L) :
    GRun p F v0 (cr (GG p F v0)) := cr_eq (GG_causal p F v0 hL)

theorem grun_unique {p : Prm} {F : Nat → Bool → Bool} {v0 : Bool} (hL : 1 ≤ p.L)
    {x y : Nat → St} (hx : GRun p F v0 x) (hy : GRun p F v0 y) : ∀ t, x t = y t :=
  cr_unique (GG_causal p F v0 hL) hx hy

theorem GRun.zero {p : Prm} {F : Nat → Bool → Bool} {v0 : Bool} {st : Nat → St}
    (h : GRun p F v0 st) : st 0 = St.init v0 := h 0

theorem GRun.succ {p : Prm} {F : Nat → Bool → Bool} {v0 : Bool} {st : Nat → St}
    (h : GRun p F v0 st) (t : Nat) :
    st (t + 1) = step p (t + 1) (F (t + 1) (st (t + 1 - p.L)).o) (st t) := h (t + 1)

/-- The LUT form: INIT `init`, feedback on pin `k` (0-based, `I0 = 0`), the other pins the
traces `P t i` the fid mux sees (already delayed by their arcs). -/
def lutF (init k : Nat) (P : Nat → Nat → Bool) : Nat → Bool → Bool :=
  fun t q => lut6 init (fun i => if i = k then q else P t i)

/-- bd_c2's cell function as used by `GLSResolve.Run`. -/
def c2F (a b rst : Sig) : Nat → Bool → Bool := fun t q => fC2 (a t) (b t) q (rst t)

/-- `c2F` is the LUT form of bd_c2's INIT with feedback pin I2. -/
theorem c2F_lut (a b rst : Sig) :
    c2F a b rst = lutF INIT_c2 2 (fun t => pins (a t) (b t) false (rst t)) := by
  funext t q
  simp only [c2F, fC2, lutF]
  congr 1
  funext i
  rcases i with _ | _ | _ | _ | n <;> simp [pins]

/-- **GLSResolve's `Run` is the bd_c2 instance of `GRun`** (so every theorem there is a
theorem about `GRun p (c2F a b rst)`). -/
theorem run_iff_grun (p : Prm) (a b rst : Sig) (v0 : Bool) (st : Nat → St) :
    Run p a b rst v0 st ↔ GRun p (c2F a b rst) v0 st := by
  constructor
  · intro h t; exact (h t).trans (by cases t <;> rfl)
  · intro h t; exact (h t).trans (by cases t <;> rfl)

/-! ## 2. Generic segments: a set event from a quiet state -/

/-- The state after the first edge at `s` from a quiet state `Q` (`:112-115`). -/
def Q1 (Q : St) (s : Nat) : St := ⟨true, false, false, s, Q.ign, Q.pt, Q.pv⟩

/-- Closed form of a set-runt segment from `Q` at `s - 1`: edge at `s`, decision at `s + w`
with outcome `resolve w L win (nz (s + w))`, resolution time `T = R δ`. -/
def Sseg (p : Prm) (Q : St) (s w : Nat) (t : Nat) : St :=
  if t < s then Q
  else if t < s + w then Q1 Q s
  else match resolve (w : Int) (p.L : Int) p.win (p.nz (s + w)) with
    | .reject => ⟨false, false, false, 0, s + w + p.L + 1, Q.pt, Q.pv⟩
    | .commit => ⟨decide (s + w + p.R (p.delta w (s + w)) ≤ t),
        decide (t < s + w + p.R (p.delta w (s + w))), false, 0,
        s + w + p.R (p.delta w (s + w)) + p.L + 1, s + w + p.R (p.delta w (s + w)), true⟩
    | .back => ⟨false, decide (t < s + w + p.R (p.delta w (s + w))), false, 0,
        s + w + p.R (p.delta w (s + w)) + p.L + 1, s + w + p.R (p.delta w (s + w)), false⟩

/-- A quiet state: output `0`, not busy, window over by `s`, no last edge. -/
structure Quiet (L : Nat) (Q : St) (s : Nat) : Prop where
  o : Q.o = false
  busy : Q.busy = false
  ign : Q.ign ≤ s
  /-- no last edge, or the last edge at least one loop delay before `s` (so the edge at `s`
  is not a runt, `:78`) -/
  tl : Q.tl = 0 ∨ Q.tl + L ≤ s

theorem quiet_init (L s : Nat) : Quiet L (St.init false) s := ⟨rfl, rfl, Nat.zero_le _, Or.inl rfl⟩

/-- An edge at `s` from a quiet state is never a runt. -/
theorem quiet_noRunt {p : Prm} {Q : St} {s : Nat} (hq : Quiet p.L Q s) (f : Bool) :
    isRunt p s f Q = false := by
  unfold isRunt
  rcases hq.tl with h | h
  · simp [h]
  · have : ¬ (s - Q.tl < p.L) := by omega
    simp [this]

/-- Quiet prefix: if the cell reads `F t false = false` up to `s`, a run from `0` stays in
the reset state. -/
theorem grun_quiet {p : Prm} {F : Nat → Bool → Bool} {st : Nat → St} {s : Nat}
    (hL : 1 ≤ p.L) (h : GRun p F false st) (hF : ∀ t, 1 ≤ t → t < s → F t false = false) :
    ∀ t, t < s → st t = St.init false := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    intro ht
    cases t with
    | zero => exact h.zero
    | succ t =>
      rw [h.succ t, ih t (by omega) (by omega), ih (t + 1 - p.L) (by omega) (by omega)]
      simp only [St.init]
      rw [hF (t + 1) (by omega) ht]
      simp [step, eval, nba, blocked]

/-- **Wide set** (`x = 1` for at least one loop delay): a clean set at `s`, never a runt. -/
theorem seg_wide {p : Prm} {F : Nat → Bool → Bool} {v0 : Bool} {st : Nat → St} {Q : St}
    {s : Nat} (hL : 1 ≤ p.L) (hs : 1 ≤ s) (h : GRun p F v0 st)
    (hQ : st (s - 1) = Q) (hq : Quiet p.L Q s)
    (hpre : ∀ t, s ≤ t → t - p.L < s → (st (t - p.L)).o = false)
    (hF0 : ∀ t, s ≤ t → t < s + p.L → F t false = true)
    (hF1 : ∀ t, s ≤ t → F t true = true) :
    ∀ t, s ≤ t → st t = Q1 Q s := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    intro ht
    cases t with
    | zero => omega
    | succ t =>
      rw [h.succ t]
      by_cases h1 : t + 1 = s
      · have hst : st t = Q := by rw [← hQ]; congr 1; omega
        rw [hst, hpre (t + 1) (by omega) (by omega), hF0 (t + 1) (by omega) (by omega)]
        have hb : blocked (t + 1) Q = false := by
          simp [blocked, hq.busy]; have := hq.ign; omega
        have hr : isRunt p (t + 1) true Q = false := by rw [h1]; exact quiet_noRunt hq _
        unfold step
        rw [eval_edge hb (by simp [hq.o]) hr, nba_idle (by simp [hq.busy])]
        simp [Q1, hq.o, hq.busy, h1]
      · rw [ih t (by omega) (by omega)]
        have hf : F (t + 1) (st (t + 1 - p.L)).o = true := by
          by_cases h2 : t + 1 - p.L < s
          · rw [hpre (t + 1) (by omega) h2]; exact hF0 (t + 1) (by omega) (by omega)
          · rw [ih (t + 1 - p.L) (by omega) (by omega)]; exact hF1 (t + 1) (by omega)
        rw [hf]; unfold step; rw [eval_same (by simp [Q1]), nba_idle rfl]

/-- The value of `Sseg` before the decision. -/
theorem Sseg_pre (p : Prm) (Q : St) (s w t : Nat) (h1 : s ≤ t) (h2 : t < s + w) :
    Sseg p Q s w t = Q1 Q s := by
  simp [Sseg, show ¬ t < s by omega, h2]

theorem Sseg_lt (p : Prm) (Q : St) (s w t : Nat) (h1 : t < s) : Sseg p Q s w t = Q := by
  simp [Sseg, h1]

/-- The resolution time scheduled at the segment's decision (`0` for a rejection). -/
def trpS (p : Prm) (s w : Nat) : Nat :=
  match resolve (w : Int) (p.L : Int) p.win (p.nz (s + w)) with
  | .reject => 0 | _ => p.R (p.delta w (s + w))

theorem Iend_eq (p : Prm) (s w : Nat) : Iend p s w = s + w + trpS p s w + p.L + 1 := by
  unfold Iend trpS; cases resolve (w : Int) (p.L : Int) p.win (p.nz (s + w)) <;> rfl

/-- The output of a segment after its first edge. -/
theorem Sseg_o (p : Prm) (Q : St) (s w t : Nat) (h1 : s ≤ t) :
    (Sseg p Q s w t).o = decide (t < s + w ∨
      (resolve (w : Int) (p.L : Int) p.win (p.nz (s + w)) = .commit ∧ s + w + trpS p s w ≤ t)) := by
  unfold Sseg trpS
  by_cases h2 : t < s + w
  · simp [show ¬ t < s by omega, h2, Q1]
  · cases hres : resolve (w : Int) (p.L : Int) p.win (p.nz (s + w)) <;>
      simp [show ¬ t < s by omega, h2]

/-- **A set runt from a quiet state, up to the end of the ignore window.** The cell reads
`F t false = x t` with `x` the pulse `[s, s + w)` up to the decision (ANYTHING inside the
window), and `F t true = true` from `s` on. Then the run is `Sseg` up to `ign_until`. -/
theorem seg_runt_pre {p : Prm} {F : Nat → Bool → Bool} {v0 : Bool} {st : Nat → St} {Q : St}
    {s w : Nat} (hL : 1 ≤ p.L) (hs : 1 ≤ s) (hw1 : 1 ≤ w) (hw : w < p.L)
    (h : GRun p F v0 st) (hQ : st (s - 1) = Q) (hq : Quiet p.L Q s)
    (hpre : ∀ t, s ≤ t → t - p.L < s → (st (t - p.L)).o = false)
    (hF0 : ∀ t, s ≤ t → t ≤ s + w → F t false = decide (t < s + w))
    (hF1 : ∀ t, s ≤ t → F t true = true) :
    ∀ t, s - 1 ≤ t → t < Iend p s w → st t = Sseg p Q s w t := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    intro ht hte
    by_cases h0 : t = s - 1
    · subst h0; rw [hQ, Sseg_lt _ _ _ _ _ (by omega)]
    cases t with
    | zero => omega
    | succ t =>
      rw [h.succ t]
      have hIe := Iend_eq p s w
      by_cases h1 : t + 1 = s
      · -- the first edge
        have hst : st t = Q := by rw [← hQ]; congr 1; omega
        rw [hst, hpre (t + 1) (by omega) (by omega), hF0 (t + 1) (by omega) (by omega)]
        have hb : blocked (t + 1) Q = false := by
          simp [blocked, hq.busy]; have := hq.ign; omega
        have hr : isRunt p (t + 1) (decide (t + 1 < s + w)) Q = false := by
          rw [h1]; exact quiet_noRunt hq _
        unfold step
        rw [eval_edge hb (by simp [hq.o]; omega) hr, nba_idle (by simp [hq.busy])]
        rw [Sseg_pre _ _ _ _ _ (by omega) (by omega)]
        simp [Q1, hq.o, hq.busy, h1, show 0 < w by omega]
      · rw [ih t (by omega) (by omega) (by omega)]
        by_cases h4 : t + 1 < s + w
        · -- inside the pulse
          have h3 : t + 1 - p.L < s := by omega
          rw [hpre (t + 1) (by omega) h3, hF0 (t + 1) (by omega) (by omega),
            Sseg_pre _ _ _ _ _ (by omega) (by omega), Sseg_pre _ _ _ _ _ (by omega) h4]
          simp only [h4, decide_true]
          unfold step; rw [eval_same (by simp [Q1]), nba_idle rfl]
        · by_cases h5 : t + 1 = s + w
          · -- the decision step
            have h3 : t + 1 - p.L < s := by omega
            rw [hpre (t + 1) (by omega) h3, hF0 (t + 1) (by omega) (by omega),
              Sseg_pre _ _ _ _ _ (by omega) (by omega)]
            simp only [show ¬ t + 1 < s + w by omega, decide_false]
            have e1 : 0 < s := by omega
            have e2 : t + 1 - s < p.L := by omega
            have e3 : ¬ t + 1 < Q.ign := by have := hq.ign; omega
            have hr : isRunt p (t + 1) false (Q1 Q s) = true := by
              simp [isRunt, Q1, e1, e2]
            have hwe : t + 1 - (Q1 Q s).tl = w := by simp [Q1]; omega
            unfold step
            rw [eval_runt (by simp [blocked, Q1, e3]) (by simp [Q1]) hr, hwe, h5]
            unfold Sseg
            simp only [show ¬ s + w < s by omega, show ¬ s + w < s + w by omega, ite_false]
            cases hres : resolve (w : Int) (p.L : Int) p.win (p.nz (s + w)) with
            | reject => simp [nba, Q1]
            | commit =>
              by_cases hz : p.R (p.delta w (s + w)) = 0
              · simp [nba, Q1, hz]
              · simp [nba, Q1, hz]; omega
            | back =>
              by_cases hz : p.R (p.delta w (s + w)) = 0
              · simp [nba, Q1, hz]
              · simp [nba, Q1, hz]; omega
          · -- after the decision, inside the window: blocked
            have h6 : s + w < t + 1 := by omega
            cases hres : resolve (w : Int) (p.L : Int) p.win (p.nz (s + w)) with
            | reject =>
              have hT : trpS p s w = 0 := by simp [trpS, hres]
              have hS : ∀ u, s + w ≤ u → Sseg p Q s w u =
                  ⟨false, false, false, 0, s + w + p.L + 1, Q.pt, Q.pv⟩ := by
                intro u hu
                simp [Sseg, hres, show ¬ u < s by omega, show ¬ u < s + w by omega]
              rw [hS t (by omega), hS (t + 1) (by omega)]
              unfold step
              rw [eval_blocked (by simp [blocked]; omega)]
              simp [nba]
            | commit =>
              have hT : trpS p s w = p.R (p.delta w (s + w)) := by simp [trpS, hres]
              generalize hTT : p.R (p.delta w (s + w)) = T at hT
              have hS : ∀ u, s + w ≤ u → Sseg p Q s w u =
                  ⟨decide (s + w + T ≤ u), decide (u < s + w + T), false, 0,
                    s + w + T + p.L + 1, s + w + T, true⟩ := by
                intro u hu
                simp [Sseg, hres, hTT, show ¬ u < s by omega, show ¬ u < s + w by omega]
              rw [hS t (by omega), hS (t + 1) (by omega)]
              unfold step
              rw [eval_blocked (by simp [blocked]; omega)]
              exact nba_c t _ _
            | back =>
              have hT : trpS p s w = p.R (p.delta w (s + w)) := by simp [trpS, hres]
              generalize hTT : p.R (p.delta w (s + w)) = T at hT
              have hS : ∀ u, s + w ≤ u → Sseg p Q s w u =
                  ⟨false, decide (u < s + w + T), false, 0,
                    s + w + T + p.L + 1, s + w + T, false⟩ := by
                intro u hu
                simp [Sseg, hres, hTT, show ¬ u < s by omega, show ¬ u < s + w by omega]
              rw [hS t (by omega), hS (t + 1) (by omega)]
              unfold step
              rw [eval_blocked (by simp [blocked]; omega)]
              exact nba_b t _ _

/-- The decided state is constant from `s + w + trp` on. -/
theorem Sseg_const (p : Prm) (Q : St) (s w t : Nat) (ht : s + w + trpS p s w ≤ t) :
    Sseg p Q s w (t + 1) = Sseg p Q s w t := by
  unfold Sseg trpS at *
  cases hres : resolve (w : Int) (p.L : Int) p.win (p.nz (s + w)) <;> simp [hres] at ht ⊢ <;>
    simp [show ¬ t < s by omega, show ¬ t + 1 < s by omega, show ¬ t < s + w by omega,
      show ¬ t + 1 < s + w by omega] <;> omega

/-- The final value after the decision (`1` iff the draw committed). -/
def finalS (p : Prm) (s w : Nat) : Bool :=
  decide (resolve (w : Int) (p.L : Int) p.win (p.nz (s + w)) = .commit)

theorem Sseg_final (p : Prm) (Q : St) (s w t : Nat) (ht : s + w + trpS p s w ≤ t) :
    (Sseg p Q s w t).o = finalS p s w := by
  rw [Sseg_o p Q s w t (by omega)]; unfold finalS
  by_cases hc : resolve (w : Int) (p.L : Int) p.win (p.nz (s + w)) = .commit <;> simp [hc] <;> omega

/-- **At `ign_until` the cell's CURRENT value is applied (late, not lost), exactly once**:
the output at `Iend` is `F Iend final`. A change of the cell's function that is still
present at `ign_until` is applied there; one that is gone by then leaves no trace
(`seg_runt_pre` takes the window's inputs arbitrary). -/
theorem seg_window_end {p : Prm} {F : Nat → Bool → Bool} {v0 : Bool} {st : Nat → St} {Q : St}
    {s w : Nat} (hL : 1 ≤ p.L) (hs : 1 ≤ s) (hw1 : 1 ≤ w) (hw : w < p.L)
    (h : GRun p F v0 st) (hQ : st (s - 1) = Q) (hq : Quiet p.L Q s)
    (hpre : ∀ t, s ≤ t → t - p.L < s → (st (t - p.L)).o = false)
    (hF0 : ∀ t, s ≤ t → t ≤ s + w → F t false = decide (t < s + w))
    (hF1 : ∀ t, s ≤ t → F t true = true) :
    (st (Iend p s w)).o = F (Iend p s w) (finalS p s w) ∧
    (st (Iend p s w - 1)).o = finalS p s w := by
  have pre := seg_runt_pre hL hs hw1 hw h hQ hq hpre hF0 hF1
  have hIe := Iend_eq p s w
  have hlast : st (Iend p s w - 1) = Sseg p Q s w (Iend p s w - 1) := pre _ (by omega) (by omega)
  have hfb : (st (Iend p s w - p.L)).o = finalS p s w := by
    rw [pre _ (by omega) (by omega)]; exact Sseg_final _ _ _ _ _ (by omega)
  refine ⟨?_, by rw [hlast]; exact Sseg_final _ _ _ _ _ (by omega)⟩
  have e := h.succ (Iend p s w - 1)
  rw [show Iend p s w - 1 + 1 = Iend p s w by omega] at e
  rw [e, hlast, hfb]
  -- the decided state: not busy, window over, no last edge
  have hd : ∀ u, s + w + trpS p s w ≤ u → (Sseg p Q s w u).busy = false ∧
      (Sseg p Q s w u).tl = 0 ∧ (Sseg p Q s w u).ign = Iend p s w := by
    intro u hu
    rw [hIe]; unfold Sseg trpS at *
    cases hres : resolve (w : Int) (p.L : Int) p.win (p.nz (s + w)) <;> simp [hres] at hu ⊢ <;>
      simp [show ¬ u < s by omega, show ¬ u < s + w by omega] <;> omega
  obtain ⟨hb, htl, hig⟩ := hd (Iend p s w - 1) (by omega)
  generalize hS : Sseg p Q s w (Iend p s w - 1) = S at hb htl hig
  have ho : S.o = finalS p s w := by rw [← hS]; exact Sseg_final _ _ _ _ _ (by omega)
  unfold step
  by_cases hfe : F (Iend p s w) (finalS p s w) = S.o
  · rw [eval_same hfe, nba_idle hb, ho]; rw [ho] at hfe; exact hfe.symm
  · rw [eval_edge (by simp [blocked, hb, hig]) hfe (by simp [isRunt, htl]), nba_idle (by simp [hb])]

/-- **A set runt from a quiet state, the whole run**: with `x = 0` from `ign_until` on. -/
theorem seg_runt {p : Prm} {F : Nat → Bool → Bool} {v0 : Bool} {st : Nat → St} {Q : St}
    {s w : Nat} (hL : 1 ≤ p.L) (hs : 1 ≤ s) (hw1 : 1 ≤ w) (hw : w < p.L)
    (h : GRun p F v0 st) (hQ : st (s - 1) = Q) (hq : Quiet p.L Q s)
    (hpre : ∀ t, s ≤ t → t - p.L < s → (st (t - p.L)).o = false)
    (hF0 : ∀ t, s ≤ t → t ≤ s + w → F t false = decide (t < s + w))
    (hF0' : ∀ t, Iend p s w ≤ t → F t false = false)
    (hF1 : ∀ t, s ≤ t → F t true = true) :
    ∀ t, s - 1 ≤ t → st t = Sseg p Q s w t := by
  have pre := seg_runt_pre hL hs hw1 hw h hQ hq hpre hF0 hF1
  have hIe := Iend_eq p s w
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    intro ht
    by_cases hlt : t < Iend p s w
    · exact pre t ht hlt
    cases t with
    | zero => omega
    | succ t =>
      rw [h.succ t, ih t (by omega) (by omega), ih (t + 1 - p.L) (by omega) (by omega),
        Sseg_final _ _ _ _ _ (by omega)]
      have hf : F (t + 1) (finalS p s w) = finalS p s w := by
        unfold finalS
        by_cases hc : resolve (w : Int) (p.L : Int) p.win (p.nz (s + w)) = .commit
        · simp [hc]; exact hF1 (t + 1) (by omega)
        · simp [hc]; exact hF0' (t + 1) (by omega)
      rw [hf]
      have hd : (Sseg p Q s w t).busy = false := by
        unfold Sseg trpS at *
        cases hres : resolve (w : Int) (p.L : Int) p.win (p.nz (s + w)) <;> simp [hres] at hIe ⊢ <;>
          simp [show ¬ t < s by omega, show ¬ t < s + w by omega] <;> omega
      unfold step
      rw [eval_same (Sseg_final _ _ _ _ _ (by omega)).symm, nba_idle hd,
        Sseg_const _ _ _ _ _ (by omega)]

/-- From the reset state at time 0: quiet before `s`, then a set runt. -/
theorem grun_runt {p : Prm} {F : Nat → Bool → Bool} {st : Nat → St} {s w : Nat}
    (hL : 1 ≤ p.L) (hs : 1 ≤ s) (hw1 : 1 ≤ w) (hw : w < p.L) (h : GRun p F false st)
    (hq0 : ∀ t, 1 ≤ t → t < s → F t false = false)
    (hF0 : ∀ t, s ≤ t → t ≤ s + w → F t false = decide (t < s + w))
    (hF0' : ∀ t, Iend p s w ≤ t → F t false = false)
    (hF1 : ∀ t, s ≤ t → F t true = true) :
    ∀ t, st t = Sseg p (St.init false) s w t := by
  have hq := grun_quiet hL h hq0
  intro t
  by_cases ht : t < s - 1
  · rw [hq t (by omega), Sseg_lt _ _ _ _ _ (by omega)]
  · exact seg_runt hL hs hw1 hw h (hq (s - 1) (by omega)) (quiet_init p.L s)
      (fun u _ hu => by rw [hq _ hu]; rfl) hF0 hF0' hF1 t (by omega)

/-- From the reset state: quiet before `s`, then a wide set. -/
theorem grun_wide {p : Prm} {F : Nat → Bool → Bool} {st : Nat → St} {s : Nat}
    (hL : 1 ≤ p.L) (hs : 1 ≤ s) (h : GRun p F false st)
    (hq0 : ∀ t, 1 ≤ t → t < s → F t false = false)
    (hF0 : ∀ t, s ≤ t → t < s + p.L → F t false = true)
    (hF1 : ∀ t, s ≤ t → F t true = true) :
    ∀ t, (st t).o = decide (s ≤ t) := by
  have hq := grun_quiet hL h hq0
  intro t
  by_cases ht : t < s
  · rw [hq t ht]; simp [St.init]; omega
  · rw [seg_wide hL hs h (hq (s - 1) (by omega)) (quiet_init p.L s)
      (fun u _ hu => by rw [hq _ hu]; rfl) hF0 hF1 t (by omega)]
    simp [Q1]; omega

/-- The output of the reset-state runt run. -/
theorem grun_runt_o {p : Prm} {F : Nat → Bool → Bool} {st : Nat → St} {s w : Nat}
    (hL : 1 ≤ p.L) (hs : 1 ≤ s) (hw1 : 1 ≤ w) (hw : w < p.L) (h : GRun p F false st)
    (hq0 : ∀ t, 1 ≤ t → t < s → F t false = false)
    (hF0 : ∀ t, s ≤ t → t ≤ s + w → F t false = decide (t < s + w))
    (hF0' : ∀ t, Iend p s w ≤ t → F t false = false)
    (hF1 : ∀ t, s ≤ t → F t true = true) (t : Nat) :
    (st t).o = decide (s ≤ t ∧ (t < s + w ∨
      (resolve (w : Int) (p.L : Int) p.win (p.nz (s + w)) = .commit ∧ s + w + trpS p s w ≤ t))) := by
  rw [grun_runt hL hs hw1 hw h hq0 hF0 hF0' hF1 t]
  by_cases h1 : t < s
  · rw [Sseg_lt _ _ _ _ _ h1]; simp [St.init]; omega
  · rw [Sseg_o _ _ _ _ _ (by omega)]; simp [show s ≤ t by omega]

/-! ### bd_c2 again, from the generic theorems (statement of `GLSResolve.run_runt_gen`) -/

theorem Srunt_eq_Sseg (p : Prm) (t0 w t : Nat) : Srunt p t0 w t = Sseg p (St.init false) t0 w t := by
  unfold Srunt Sseg
  by_cases h1 : t < t0
  · simp [h1]
  · by_cases h2 : t < t0 + w
    · simp [h1, h2, S1, Q1, St.init]
    · cases resolve (w : Int) (p.L : Int) p.win (p.nz (t0 + w)) <;> simp [h1, h2, St.init]

/-- `GLSResolve.run_runt_gen`, word for word, re-proved as an instance of `grun_runt`. -/
theorem run_runt_gen' {p : Prm} {t0 w : Nat} {b : Sig} {st : Nat → St} (hL : 1 ≤ p.L)
    (ht0 : 1 ≤ t0) (hw1 : 1 ≤ w) (hw : w < p.L)
    (hb1 : ∀ t, t ≤ t0 + w → b t = bPulse t0 w t) (hb2 : ∀ t, Iend p t0 w ≤ t → b t = false)
    (h : Run p aOne b rstZero false st) :
    ∀ t, st t = Srunt p t0 w t := by
  have hg := (run_iff_grun p aOne b rstZero false st).1 h
  intro t
  rw [Srunt_eq_Sseg]
  refine grun_runt hL ht0 hw1 hw hg ?_ ?_ ?_ ?_ t
  · intro u _ hu; simp only [c2F, aOne, rstZero, fC2_or, Bool.or_false]
    rw [hb1 u (by omega)]; simp [bPulse]; omega
  · intro u h1 h2; simp only [c2F, aOne, rstZero, fC2_or, Bool.or_false]
    rw [hb1 u h2]; simp [bPulse]; omega
  · intro u hu; simp only [c2F, aOne, rstZero, fC2_or, Bool.or_false]; exact hb2 u hu
  · intro u _; simp only [c2F, aOne, rstZero, fC2_or, Bool.or_true]

end Formal.Core.GLSResolveGen
