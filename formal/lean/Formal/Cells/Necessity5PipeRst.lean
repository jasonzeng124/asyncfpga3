import Formal.Cells.Necessity3PipeCtl

/-!
# Necessity5PipeRst: `bd_pipe.rst_lines`, the DACK and guard terms are tight

Probe Bnx5 (shard B). Bsx3 (`Necessity3PipeCtl`) showed H_RST_LONG and the
request-line term `L(b-1).hi + Rq_b.hi ≤ R` of H_RST_LINES tight to 1 tick,
and left the DACK term `L_b.hi + ahi_b ≤ R` and the guard term `Ag_b ≤ R`
open ("a stray ack at release delays stage b-1's first rise and the
deviation propagates; no closed-form run built"). This file builds that run.

`CtlClaimA sAk sAg` is `PipeTimedN.nodes_clean` with the DACK term weakened
by `sAk` and the guard term by `sAg` (`TimingA`, a verbatim copy of
`TimingN` with those slacks; `GatesN`, `EnvN` verbatim). `ctlA0` is the
shipped theorem; `dack_false : ¬ CtlClaimA 1 0`, `guard_false : ¬ CtlClaimA 0 1`.

* **Assumed (the runs):** two stages, the real `bd_c2n` INIT `00B2..` as a
  FIFO LUT with arc 1 (one corner), feedback window `[1, 1]`, request line a
  1-tick shift, `R = 4`, sender edges `4 + 4j`, receiver edges `10 + 4j`
  (the derived event times are `PipeTimedN.Wit`'s: `τ 0 j = 5 + 4j`,
  `τ 1 j = 7 + 4j`).
  - **RDack:** boundary 1's DACK line is one FIFO copy with window `[1, 4]`
    (`Necessity3PipeCtl.RqG`: it reads stage 1's node at instant 0 until 4),
    so `L 1 .hi + ahi 1 = 5 = R + 1`; stage 1's node is 1 at power-up
    (instant 0, before its LUT relation is in force).
  - **RGuard:** the DACK line is a 1-tick shift but its relation is in force
    only from `Ag = 5 = R + 1`; before that stage 0's I1 is free and reads 1.
  In both, stage 0's acknowledge pin still reads 1 at release (4) when the
  sender's first request is up, so stage 0 cannot rise at 5: it rises at 6,
  and the whole run is the nominal one delayed by one tick, for ever (closed
  forms `sq 6`, `sq 8`, every gate relation for ALL `t`). Every other
  hypothesis holds (`timingD`, `timingG`); the weakened term is off by
  exactly 1 (`dack_viol`, `guard_viol`).
* **Proved:** `nodes_clean`'s phase claim fails at stage 0, `t = 5`
  (`τ 0 0 = 5`, node still 0). Not degenerate: the run is live and serves
  every token, one tick late (`run_live`).
* **Result:** with Bsx3's two terms, every term of H_RST_LONG / H_RST_LINES
  is necessary at the boundary (one parameter point each, binary, Lean `≤`
  form). H_RST_SEL (PipePerPin per-pin model) is still not covered; the
  JSON's strict +1 on the loop terms is Bs's X window, not these runs.

Core Lean only.
-/

namespace Formal.Cells.Necessity5PipeRst
open Formal.Cells Formal.Cells.PipeTimed Formal.Cells.PipeTimedN
open Formal.Cells.Necessity3PipeCtl (RqG fstG fst1)

/-- `TimingN` with the DACK term weakened by `sAk` and the guard term by `sAg`. -/
structure TimingA (P : PN) (wh : Nat → Nat) (Es Er sAk sAg : Nat) : Prop where
  H_N_POS : 1 ≤ P.N
  H_R_POS : 1 ≤ P.R
  H_RST_LONG : ∀ i, i < P.N → (P.L i).hi + wh i ≤ P.R
  H_RST_LINES : ∀ i, i + 1 < P.N →
    (P.L i).hi + (P.Rq (i + 1)).hi ≤ P.R ∧ (P.L (i + 1)).hi + P.ahi (i + 1) ≤ P.R + sAk ∧
    P.Ag (i + 1) ≤ P.R + sAg
  H_LAT : ∀ i, i < P.N → (P.L i).hi + wh i ≤ (P.L i).lo + min (P.ER Es i) (P.EA Er i)
  H_ACK_FLUSH : ∀ i, i + 1 < P.N →
    P.ahi (i + 1) ≤ (P.L (i + 1)).lo + max (P.ER Es (i + 1)) (P.EA Er (i + 1)) + P.alo (i + 1)

theorem TimingA.toN {P : PN} {wh : Nat → Nat} {Es Er : Nat} (T : TimingA P wh Es Er 0 0) :
    TimingN P wh Es Er where
  H_N_POS := T.H_N_POS
  H_R_POS := T.H_R_POS
  H_RST_LONG := T.H_RST_LONG
  H_RST_LINES i h := by have := T.H_RST_LINES i h; omega
  H_LAT := T.H_LAT
  H_ACK_FLUSH := T.H_ACK_FLUSH

/-- `nodes_clean` with the DACK / guard terms of H_RST_LINES weakened. -/
def CtlClaimA (sAk sAg : Nat) : Prop :=
  ∀ (P : PN) (rst : Trace) (r a O q : Nat → Trace) (wl wh : Nat → Nat) (Es Er : Nat),
    GatesN P rst r a O q wl wh → EnvN P (r 0) (a (P.N - 1)) Es Er → TimingA P wh Es Er sAk sAg →
    ∀ i, i < P.N →
      (∀ t, (P.L i).hi ≤ t → t < P.τ i 0 → O i t = false) ∧
      (∀ j t, P.τ i j ≤ t → t < P.τ i (j + 1) → O i t = Vph j)

theorem ctlA0 : CtlClaimA 0 0 := by
  intro P rst r a O q wl wh Es Er G E T i hi
  exact nodes_clean G E T.toN i hi

/-! ## The two delay realisations -/

def Pd : PN where
  N := 2
  R := 4
  L _ := Ret.shift 1
  Rq _ := Ret.shift 1
  m _ := 0
  Ap _ _ := RqG
  Ag _ := 1
  ρ j := 4 + 4 * j
  γ j := 10 + 4 * j

def Pg : PN where
  N := 2
  R := 4
  L _ := Ret.shift 1
  Rq _ := Ret.shift 1
  m _ := 0
  Ap _ _ := Ret.shift 1
  Ag _ := 5
  ρ j := 4 + 4 * j
  γ j := 10 + 4 * j

theorem ccd (j : Nat) : Pd.cc j 0 = 4 + 4 * j ∧ Pd.cc j 1 = 6 + 4 * j := by
  induction j with
  | zero =>
    have e0 : Pd.cc 0 0 = 4 := rfl
    refine ⟨e0, ?_⟩
    show max ((Ret.shift 1).fst ((Ret.shift 1).fst (Pd.cc 0 0))) 4 = 6 + 4 * 0
    rw [e0, fst1 4 (by omega), fst1 5 (by omega)]; rfl
  | succ j ih =>
    have e0 : Pd.cc (j + 1) 0 = 4 + 4 * (j + 1) := by
      show max (4 + 4 * (j + 1)) (if 0 + 1 < 2 then
        (if j % 2 = 0 then RqG.fst ((Ret.shift 1).fst (Pd.cc j 1))
          else RqG.fst ((Ret.shift 1).fst (Pd.cc j 1))) else 10 + 4 * j) = _
      rw [ih.2, fst1 _ (by omega), fstG _ (by omega)]; simp; omega
    refine ⟨e0, ?_⟩
    show max ((Ret.shift 1).fst ((Ret.shift 1).fst (Pd.cc (j + 1) 0)))
      (if 1 + 1 < 2 then Pd.ackT 2 j ((Ret.shift 1).fst (Pd.cc j 2)) else 10 + 4 * j) = _
    rw [e0, fst1 (4 + 4 * (j + 1)) (by omega), fst1 (4 + 4 * (j + 1) + 1) (by omega)]; simp; omega

theorem ccg (j : Nat) : Pg.cc j 0 = 4 + 4 * j ∧ Pg.cc j 1 = 6 + 4 * j := by
  induction j with
  | zero =>
    have e0 : Pg.cc 0 0 = 4 := rfl
    refine ⟨e0, ?_⟩
    show max ((Ret.shift 1).fst ((Ret.shift 1).fst (Pg.cc 0 0))) 4 = 6 + 4 * 0
    rw [e0, fst1 4 (by omega), fst1 5 (by omega)]; rfl
  | succ j ih =>
    have e0 : Pg.cc (j + 1) 0 = 4 + 4 * (j + 1) := by
      show max (4 + 4 * (j + 1)) (if 0 + 1 < 2 then
        (if j % 2 = 0 then (Ret.shift 1).fst ((Ret.shift 1).fst (Pg.cc j 1))
          else (Ret.shift 1).fst ((Ret.shift 1).fst (Pg.cc j 1))) else 10 + 4 * j) = _
      rw [ih.2, fst1 (6 + 4 * j) (by omega), fst1 (6 + 4 * j + 1) (by omega)]; simp; omega
    refine ⟨e0, ?_⟩
    show max ((Ret.shift 1).fst ((Ret.shift 1).fst (Pg.cc (j + 1) 0)))
      (if 1 + 1 < 2 then Pg.ackT 2 j ((Ret.shift 1).fst (Pg.cc j 2)) else 10 + 4 * j) = _
    rw [e0, fst1 (4 + 4 * (j + 1)) (by omega), fst1 (4 + 4 * (j + 1) + 1) (by omega)]; simp; omega

theorem τd (i j : Nat) (hi : i < 2) : Pd.τ i j = 5 + 2 * i + 4 * j := by
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · show (Ret.shift 1).fst (Pd.cc j 0) = _; rw [(ccd j).1, fst1 _ (by omega)]; omega
  · show (Ret.shift 1).fst (Pd.cc j 1) = _; rw [(ccd j).2, fst1 _ (by omega)]; omega

theorem τg (i j : Nat) (hi : i < 2) : Pg.τ i j = 5 + 2 * i + 4 * j := by
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · show (Ret.shift 1).fst (Pg.cc j 0) = _; rw [(ccg j).1, fst1 _ (by omega)]; omega
  · show (Ret.shift 1).fst (Pg.cc j 1) = _; rw [(ccg j).2, fst1 _ (by omega)]; omega

/-! ## The delayed run (closed forms) -/

open Wit in
def O0 (t : Nat) : Bool := sq 6 t
open Wit in
def q0 (t : Nat) : Bool := sq 7 t
open Wit in
/-- Stage 0's acknowledge pin: the stray 1 up to release, then stage 1's node. -/
def a0 (t : Nat) : Bool := decide (t ≤ 4) || sq 9 t
open Wit in
def r1 (t : Nat) : Bool := sq 7 t
open Wit in
/-- RDack: stage 1's node, 1 at power-up (instant 0). -/
def O1d (t : Nat) : Bool := sq 8 t || decide (t = 0)
open Wit in
def q1d (t : Nat) : Bool := sq 9 t || decide (t = 1)

macro "n5p_omega" : tactic =>
  `(tactic| (rw [Bool.eq_iff_iff]; simp; first | omega | (constructor <;> intro h <;> omega)))

theorem ctl0 : Ctl (Wit.sq 4) a0 Wit.rstW O0 q0 (Ret.shift 1) 1 1 where
  H_LUT_FIFO t ht := by
    have ht' : 1 ≤ t := ht
    show O0 t = CElemTiming.exc CElemTiming.INIT_c2n (Wit.sq 4 (t - 1)) (a0 (t - 1))
      (q0 (t - 1)) (Wit.rstW (t - 1))
    rw [CElemTiming.c2n_eq]
    simp only [O0, q0, a0, Wit.rstW, Wit.sq]
    n5p_omega
  H_FB t ht := ⟨t - 1, by omega, by omega, by simp only [O0, q0, Wit.sq]; n5p_omega⟩
  H_LOOP_POS := by show 1 ≤ 1 + 1; decide

theorem ctl1d : Ctl r1 (Wit.sq 10) Wit.rstW O1d q1d (Ret.shift 1) 1 1 where
  H_LUT_FIFO t ht := by
    have ht' : 1 ≤ t := ht
    show O1d t = CElemTiming.exc CElemTiming.INIT_c2n (r1 (t - 1)) (Wit.sq 10 (t - 1))
      (q1d (t - 1)) (Wit.rstW (t - 1))
    rw [CElemTiming.c2n_eq]
    simp only [O1d, q1d, r1, Wit.rstW, Wit.sq]
    n5p_omega
  H_FB t ht := ⟨t - 1, by omega, by omega, by simp only [O1d, q1d, Wit.sq]; n5p_omega⟩
  H_LOOP_POS := by show 1 ≤ 1 + 1; decide

theorem ctl1g : Ctl r1 (Wit.sq 10) Wit.rstW (Wit.sq 8) (Wit.sq 9) (Ret.shift 1) 1 1 where
  H_LUT_FIFO t ht := by
    have ht' : 1 ≤ t := ht
    show Wit.sq 8 t = CElemTiming.exc CElemTiming.INIT_c2n (r1 (t - 1)) (Wit.sq 10 (t - 1))
      (Wit.sq 9 (t - 1)) (Wit.rstW (t - 1))
    rw [CElemTiming.c2n_eq]
    simp only [r1, Wit.rstW, Wit.sq]
    n5p_omega
  H_FB t ht := ⟨t - 1, by omega, by omega, by simp only [Wit.sq]; n5p_omega⟩
  H_LOOP_POS := by show 1 ≤ 1 + 1; decide

def rr : Nat → Trace | 0 => Wit.sq 4 | _ => r1
def aa : Nat → Trace | 0 => a0 | _ => Wit.sq 10
def Od : Nat → Trace | 0 => O0 | _ => O1d
def qd : Nat → Trace | 0 => q0 | _ => q1d
def Og : Nat → Trace | 0 => O0 | _ => Wit.sq 8
def qg : Nat → Trace | 0 => q0 | _ => Wit.sq 9

theorem gatesD : GatesN Pd Wit.rstW rr aa Od qd (fun _ => 1) (fun _ => 1) where
  H_RST _ := rfl
  H_CTL i hi := by
    match i, hi with
    | 0, _ => exact ctl0
    | 1, _ => exact ctl1d
  H_REQ_LINE i hi t ht := by
    have : i = 0 := by simp [Pd] at hi; omega
    subst this
    show r1 t = O0 (t - 1)
    have ht' : 1 ≤ t := ht
    simp only [r1, O0, Wit.sq]; n5p_omega
  H_ACK_LINE i hi t ht := by
    have : i = 0 := by simp [Pd] at hi; omega
    subst this
    show a0 t = O1d (if t ≤ 4 then 0 else t - 1)
    simp only [a0, O1d, Wit.sq]; split <;> n5p_omega

theorem gatesG : GatesN Pg Wit.rstW rr aa Og qg (fun _ => 1) (fun _ => 1) where
  H_RST _ := rfl
  H_CTL i hi := by
    match i, hi with
    | 0, _ => exact ctl0
    | 1, _ => exact ctl1g
  H_REQ_LINE i hi t ht := by
    have : i = 0 := by simp [Pg] at hi; omega
    subst this
    show r1 t = O0 (t - 1)
    have ht' : 1 ≤ t := ht
    simp only [r1, O0, Wit.sq]; n5p_omega
  H_ACK_LINE i hi t ht := by
    have : i = 0 := by simp [Pg] at hi; omega
    subst this
    have ht' : 5 ≤ t := ht
    show a0 t = Wit.sq 8 (t - 1)
    simp only [a0, Wit.sq]; n5p_omega

theorem envD : EnvN Pd (rr 0) (aa (Pd.N - 1)) 3 3 where
  H_REQ_LOW0 t h1 h2 := by simp only [Pd] at h1 h2; omega
  H_REQ j t h1 h2 := Wit.sq_phase 4 j t h1 (by simp only [Pd] at h2; omega)
  H_ACK_LOW0 t h1 h2 := Wit.sq_pre 10 t (by simpa [Pd] using h2)
  H_ACK j t h1 h2 := Wit.sq_phase 10 j t (by simpa [Pd] using h1) (by simp [Pd] at h2; omega)
  H_SND j := by rw [τd 0 j (by omega)]; show 5 + 2 * 0 + 4 * j + 3 ≤ 4 + 4 * (j + 1); omega
  H_RCV j := by
    show Pd.τ 1 j + 3 ≤ 10 + 4 * j
    rw [τd 1 j (by omega)]; omega
  H_RST_EARLY := by show 4 ≤ 4 + 4 * 0; omega

theorem envG : EnvN Pg (rr 0) (aa (Pg.N - 1)) 3 3 where
  H_REQ_LOW0 t h1 h2 := by simp only [Pg] at h1 h2; omega
  H_REQ j t h1 h2 := Wit.sq_phase 4 j t h1 (by simp only [Pg] at h2; omega)
  H_ACK_LOW0 t h1 h2 := Wit.sq_pre 10 t (by simpa [Pg] using h2)
  H_ACK j t h1 h2 := Wit.sq_phase 10 j t (by simpa [Pg] using h1) (by simp [Pg] at h2; omega)
  H_SND j := by rw [τg 0 j (by omega)]; show 5 + 2 * 0 + 4 * j + 3 ≤ 4 + 4 * (j + 1); omega
  H_RCV j := by
    show Pg.τ 1 j + 3 ≤ 10 + 4 * j
    rw [τg 1 j (by omega)]; omega
  H_RST_EARLY := by show 4 ≤ 4 + 4 * 0; omega

/-- RDack: the DACK term `L 1 .hi + ahi 1 = 1 + 4 = R + 1`. -/
theorem dack_viol : (Pd.L 1).hi + Pd.ahi 1 = Pd.R + 1 := rfl
/-- RGuard: the guard term `Ag 1 = 5 = R + 1`. -/
theorem guard_viol : Pg.Ag 1 = Pg.R + 1 := rfl

theorem timingD : TimingA Pd (fun _ => 1) 3 3 1 0 where
  H_N_POS := by decide
  H_R_POS := by decide
  H_RST_LONG _ _ := by show 1 + 1 ≤ 4; decide
  H_RST_LINES i h := by
    have : i = 0 := by simp [Pd] at h; omega
    subst this
    show 1 + 1 ≤ 4 ∧ 1 + 4 ≤ 4 + 1 ∧ 1 ≤ 4 + 0
    decide
  H_LAT i h := by
    have hi : i = 0 ∨ i = 1 := by simp [Pd] at h; omega
    rcases hi with rfl | rfl
    · show 1 + 1 ≤ 1 + min 3 (1 + 1 + 1); decide
    · show 1 + 1 ≤ 1 + min (1 + 1 + 1) 3; decide
  H_ACK_FLUSH i h := by
    have : i = 0 := by simp [Pd] at h; omega
    subst this
    show 4 ≤ 1 + max (1 + 1 + 1) 3 + 1; decide

theorem timingG : TimingA Pg (fun _ => 1) 3 3 0 1 where
  H_N_POS := by decide
  H_R_POS := by decide
  H_RST_LONG _ _ := by show 1 + 1 ≤ 4; decide
  H_RST_LINES i h := by
    have : i = 0 := by simp [Pg] at h; omega
    subst this
    show 1 + 1 ≤ 4 ∧ 1 + 1 ≤ 4 + 0 ∧ 5 ≤ 4 + 1
    decide
  H_LAT i h := by
    have hi : i = 0 ∨ i = 1 := by simp [Pg] at h; omega
    rcases hi with rfl | rfl
    · show 1 + 1 ≤ 1 + min 3 (1 + 1 + 1); decide
    · show 1 + 1 ≤ 1 + min (1 + 1 + 1) 3; decide
  H_ACK_FLUSH i h := by
    have : i = 0 := by simp [Pg] at h; omega
    subst this
    show 1 ≤ 1 + max (1 + 1 + 1) 3 + 1; decide

/-- The run is live: stage 0 serves every token, one tick late
(`O0 = sq 6`: rises at `6 + 8k`, falls at `10 + 8k`); stage 1 likewise
(`sq 8`); the stray is only stage 0's I1 on `[0, 4]`. -/
theorem run_live (k : Nat) : O0 (6 + 8 * k) = true ∧ O0 (10 + 8 * k) = false ∧
    Wit.sq 8 (8 + 8 * k) = true ∧ Wit.sq 8 (12 + 8 * k) = false := by
  simp only [O0, Wit.sq]; refine ⟨?_, ?_, ?_, ?_⟩ <;> (simp; try omega)

theorem dack_false : ¬ CtlClaimA 1 0 := by
  intro h
  have := (h _ _ _ _ _ _ _ _ _ _ gatesD envD timingD 0 (by decide)).2 0 5
    (by rw [τd 0 0 (by decide)]; decide) (by rw [τd 0 1 (by decide)]; decide)
  exact absurd this (by decide)

theorem guard_false : ¬ CtlClaimA 0 1 := by
  intro h
  have := (h _ _ _ _ _ _ _ _ _ _ gatesG envG timingG 0 (by decide)).2 0 5
    (by rw [τg 0 0 (by decide)]; decide) (by rw [τg 0 1 (by decide)]; decide)
  exact absurd this (by decide)

/-! Non-vacuity at slack 0: `PipeTimedN.Wit.witness` (Bsx3's note). -/

end Formal.Cells.Necessity5PipeRst
