import Formal.Cells.PipeTimedN
open Formal.Core.LutList

/-!
# Necessity3Pipe: the data-side `bd_pipe` rows are tight to 1 tick

Probe Bsx3 (shard B). Rows `bd_pipe.boundary_I` (H_I), `bd_pipe.boundary_H`
(H_H), `bd_pipe.data_lead` (H_DATA_LEAD) and `bd_pipe.output`
(`Dl (N-1) b ≤ Er`) of `formal/out/cell_constraints.json` were "sufficient".
Their theorems are `PipeTimedN.token` and `PipeTimedN.pipe_forward` (the
`N`-stage pipe: FIFO controllers with the real `bd_c2n` INIT, request lines,
DACK OR lines, open-loop sender/receiver, and every latch bit 6c's Kleene
`LatchRel` over its pin windows).

## Method ("Claim slack")

`TokClaim sI sH sL` is `token` with H_I weakened by `sI`, H_H by `sH` and
H_DATA_LEAD by `sL` ticks (`DataS`, a verbatim copy of `DataN` with those
three slacks); every other hypothesis (`GatesN`, `EnvN`, `TimingN`, the
other `DataN` fields) is kept word for word. `OutClaim s` is the second half
of `pipe_forward` with its premise `Dl (N-1) b ≤ Er` weakened by `s`.

* `tok0 : TokClaim 0 0 0`, `out0 : OutClaim 0` are the existing theorems.
* `I_false : ¬ TokClaim 1 0 0`, `H_false : ¬ TokClaim 0 1 0`,
  `L_false : ¬ TokClaim 0 0 1`, `out_false : ¬ OutClaim 1`.

Every counter-run uses the unit-delay CONTROL run of `PipeTimedN.Wit` with
`N = 2` (`Wit.gates_w`, `Wit.env_w`, `Wit.timing_w`: every control
hypothesis holds at every instant, stage `i`'s node is `sq (5 + 2i)`), and
one-bit latches that are the real `ODD` INIT as transport LUTs with a fixed
delay on every pin (point windows, so one corner): `latch_tr`. The latch
outputs are given in closed form and checked against the gate equation for
ALL `t` (`*_rel`). Token values alternate (`valW k = (k even)`), so a stale
value is a wrong value. In each run exactly the weakened hypothesis is off
by exactly 1 (`*_viol`); every other `DataN` field holds (`dataS_*`).

| run | pin delays (d, en, loop) stage 0 / stage 1 | sender | violated |
|---|---|---|---|
| `RH` | (1,1,1) / (1,5,1) | Wit (token k on [2+8k,10+8k)) | H_H: ehi1 = 5 = aslow + L.lo + elo0 + dlo1 + 1 |
| `RI` | (1,6,1) / (1,1,1) | token k on [6+8k,14+8k), Erel 5, Sdr 0, Lag 2 | H_I: Dl0 + dhi1 + fhi1 = 8 = Won + Rq.lo + L1.lo + elo1 + 1 |
| `RL` | (5,1,1) / (1,1,1) | token k on [5+8k,13+8k), Sdr = Lag = 0 | H_DATA_LEAD: dS k + Sdr = ρ(2k) + Lag + 1 |
| `RO` | (1,1,1) / (1,4,1) | Wit | `Dl 1 = 4 = Er + 1` |

Failures (k = 0, token value 1): `RH` stage 1 shows token 1's value at 15
(stage 0's next token reaches stage 1 while stage 1's closing enable is
still in flight); `RI` stage 1 still holds the reset value on [12, 16)
(stage 1 closed before stage 0's late value went through D + loop); `RL`
stage 0 holds the stale value at 10 (the latch closed one tick before the
new data's loop settled); `RO` the last stage shows the stale value at the
receiver's acknowledge rise `γ 0 = 10`.

All binary: the Lean `≤` forms cannot be weakened by 1 ps. One parameter
point per row (N = 2, unit control), not an iff.

Core Lean only.
-/

namespace Formal.Cells.Necessity3Pipe
open Formal.Cells Formal.Cells.PipeTimed Formal.Cells.PipeTimedN

/-! ## 1. The claims -/

/-- `DataN` with H_I, H_H, H_DATA_LEAD weakened by `sI`, `sH`, `sL`
(every other field verbatim). -/
structure DataS (P : PN) (O : Nat → Trace) (d : Nat → Bundling.Sig) (x : Nat → Nat → Bundling.Sig)
    (val : Nat → Nat → Bool) (dS dE : Nat → Nat) (V : Nat → Win)
    (W Es Er Erel Sdr Lag sI sH sL : Nat) : Prop where
  H_LATCH : ∀ i b, i < P.N → b < W → Bundling.LatchRel (din d x i b) (O i) (x i b)
    ((V i).dlo b) ((V i).dhi b) ((V i).elo b) ((V i).ehi b) ((V i).flo b) ((V i).fhi b)
  H_WIN : ∀ i b, i < P.N → b < W → (V i).dlo b ≤ (V i).dhi b ∧ (V i).elo b ≤ (V i).ehi b ∧
    (V i).flo b ≤ (V i).fhi b ∧ 1 ≤ (V i).flo b
  H_DATA_VALID : ∀ k b t, b < W → dS k ≤ t → t < dE k → d b t = val k b
  H_DATA_LEAD : ∀ k, dS k + Sdr ≤ P.ρ (2 * k) + Lag + sL
  H_DATA_REL : ∀ k, P.τ 0 (2 * k + 1) + Erel ≤ dE k
  H_HOLD0 : ∀ b, b < W → (V 0).ehi b ≤ Erel + (V 0).dlo b
  H_PW : ∀ i b, i < P.N → b < W → (V i).ehi b + (V i).fhi b ≤ P.Won Es Er i + (V i).elo b
  H_SETUP0 : ∀ b, b < W →
    (V 0).dhi b + (V 0).fhi b + Lag ≤ Sdr + (P.L 0).lo + P.Won Es Er 0 + (V 0).elo b
  H_I : ∀ i b, i + 1 < P.N → b < W →
    Dl P V Sdr Lag i b + (V (i + 1)).dhi b + (V (i + 1)).fhi b ≤
      ((P.Won Es Er i + (P.Rq (i + 1)).lo + (P.L (i + 1)).lo + (V (i + 1)).elo b : Nat) : Int) +
        (sI : Int)
  H_H : ∀ i b, i + 1 < P.N → b < W →
    (V (i + 1)).ehi b ≤ P.aslow (i + 1) + (P.L i).lo + (V i).elo b +
      (V (i + 1)).dlo b + sH

theorem DataS.toN {P : PN} {O : Nat → Trace} {d : Nat → Bundling.Sig}
    {x : Nat → Nat → Bundling.Sig} {val : Nat → Nat → Bool} {dS dE : Nat → Nat} {V : Nat → Win}
    {W Es Er Erel Sdr Lag : Nat}
    (D : DataS P O d x val dS dE V W Es Er Erel Sdr Lag 0 0 0) :
    DataN P O d x val dS dE V W Es Er Erel Sdr Lag where
  H_LATCH := D.H_LATCH
  H_WIN := D.H_WIN
  H_DATA_VALID := D.H_DATA_VALID
  H_DATA_LEAD k := by have := D.H_DATA_LEAD k; omega
  H_DATA_REL := D.H_DATA_REL
  H_HOLD0 := D.H_HOLD0
  H_PW := D.H_PW
  H_SETUP0 := D.H_SETUP0
  H_I i b h1 h2 := by have := D.H_I i b h1 h2; simpa using this
  H_H i b h1 h2 := by have := D.H_H i b h1 h2; omega

/-- `PipeTimedN.token` with H_I / H_H / H_DATA_LEAD weakened by `sI` / `sH` / `sL`. -/
def TokClaim (sI sH sL : Nat) : Prop :=
  ∀ (P : PN) (rst : Trace) (r a O q : Nat → Trace) (wl wh : Nat → Nat) (Es Er : Nat)
    (d : Nat → Bundling.Sig) (x : Nat → Nat → Bundling.Sig) (val : Nat → Nat → Bool)
    (dS dE : Nat → Nat) (V : Nat → Win) (W Erel Sdr Lag : Nat),
    GatesN P rst r a O q wl wh → EnvN P (r 0) (a (P.N - 1)) Es Er → TimingN P wh Es Er →
    DataS P O d x val dS dE V W Es Er Erel Sdr Lag sI sH sL →
    ∀ k b, b < W → ∀ i, i < P.N →
      ∀ t, P.Sx V dS k b i ≤ t → t < P.τ i (2 * k + 1 + 1) + (V i).elo b → x i b t = val k b

/-- The second half of `PipeTimedN.pipe_forward` with its premise
`Dl (N-1) b ≤ Er` weakened by `s`. -/
def OutClaim (s : Nat) : Prop :=
  ∀ (P : PN) (rst : Trace) (r a O q : Nat → Trace) (wl wh : Nat → Nat) (Es Er : Nat)
    (d : Nat → Bundling.Sig) (x : Nat → Nat → Bundling.Sig) (val : Nat → Nat → Bool)
    (dS dE : Nat → Nat) (V : Nat → Win) (W Erel Sdr Lag : Nat),
    GatesN P rst r a O q wl wh → EnvN P (r 0) (a (P.N - 1)) Es Er → TimingN P wh Es Er →
    DataN P O d x val dS dE V W Es Er Erel Sdr Lag →
    ∀ k b, b < W → Dl P V Sdr Lag (P.N - 1) b ≤ (Er : Int) + (s : Int) →
      ∀ t, P.γ (2 * k) ≤ t → t < P.γ (2 * k + 1) → x (P.N - 1) b t = val k b

/-- Slack 0 is the existing theorem `token`. -/
theorem tok0 : TokClaim 0 0 0 := by
  intro P rst r a O q wl wh Es Er d x val dS dE V W Erel Sdr Lag G E T D k b hb i hi t h1 h2
  exact token G E T D.toN k b hb i hi t h1 h2

/-- Slack 0 is the existing theorem `pipe_forward`. -/
theorem out0 : OutClaim 0 := by
  intro P rst r a O q wl wh Es Er d x val dS dE V W Erel Sdr Lag G E T D k b hb hdl t h1 h2
  exact (pipe_forward G E T D k b hb).2 (by simpa using hdl) t h1 h2

/-! ## 2. Transport latches with any fixed pin delays -/

/-- A transport `ODD` latch (the real INIT `B8B8...`) whose D, enable and
feedback pins are read exactly `a`, `e`, `f` ticks ago is a 6c `LatchRel`
with point windows `[a,a]`, `[e,e]`, `[f,f]`. -/
theorem latch_tr (dd en q : Bundling.Sig) (a e f : Nat)
    (h : ∀ t, q t = (if en (t - e) then dd (t - a) else q (t - f))) :
    Bundling.LatchRel dd en q a a e e f f := by
  apply Bundling.odd_latch
  apply Bundling.transport_gate Bundling.ODD
    [(dd, a, a, a), (en, e, e, e), (q, f, f, f), (Bundling.zero, 0, 0, 0),
     (Bundling.zero, 0, 0, 0), (Bundling.zero, 0, 0, 0)] q (by simp)
  intro t
  show q t = lutB Bundling.ODD [dd (t - a), en (t - e), q (t - f), false, false, false]
  rw [Bundling.odd_bin]; exact h t

/-- Point windows: D arc `a`, enable arc `e`, loop `f`. -/
def pw (a e f : Nat) : Win := ⟨fun _ => a, fun _ => a, fun _ => e, fun _ => e, fun _ => f, fun _ => f⟩

/-- Two stages' windows. -/
def V2 (w0 w1 : Win) : Nat → Win
  | 0 => w0
  | _ => w1

/-- Two stages' latch outputs (bit index ignored, W = 1). -/
def X2 (x0 x1 : Bundling.Sig) : Nat → Nat → Bundling.Sig
  | 0 => fun _ => x0
  | _ => fun _ => x1

abbrev PP : PN := PipeTimedN.Wit.Pw 2

theorem G2 : GatesN PP PipeTimed.Wit.rstW PipeTimedN.Wit.rW PipeTimedN.Wit.aW
    PipeTimedN.Wit.OW PipeTimedN.Wit.qW (fun _ => 1) (fun _ => 1) := PipeTimedN.Wit.gates_w 2
theorem E2 : EnvN PP (PipeTimedN.Wit.rW 0) (PipeTimedN.Wit.aW (PP.N - 1)) 3 3 :=
  PipeTimedN.Wit.env_w 2 (by decide)
theorem T2 : TimingN PP (fun _ => 1) 3 3 := PipeTimedN.Wit.timing_w 2 (by decide)

theorem τ2 (i j : Nat) : PP.τ i j = 5 + 2 * i + 4 * j := PipeTimedN.Wit.τ_w 2 i j
theorem Won2 (i : Nat) : PP.Won 3 3 i = 4 := PipeTimedN.Wit.Won_w 2 i
theorem aslow2 (b : Nat) : PP.aslow b = 1 := rfl
theorem lo2 (i : Nat) : (PP.L i).lo = 1 ∧ (PP.Rq i).lo = 1 := ⟨rfl, rfl⟩

/-- Stage 0's and stage 1's nodes in the control run. -/
theorem OW0 : PipeTimedN.Wit.OW 0 = PipeTimed.Wit.sq 5 := rfl
theorem OW1 : PipeTimedN.Wit.OW 1 = PipeTimed.Wit.sq 7 := rfl

/-- Generic `DataS` for the two-stage control run: the latch relations and the
data validity are given, every inequality is a numeral check. -/
theorem mkDataS (d x0 x1 : Bundling.Sig) (dS dE : Nat → Nat) (w0 w1 : Win)
    (Erel Sdr Lag sI sH sL : Nat)
    (hL0 : Bundling.LatchRel d (PipeTimed.Wit.sq 5) x0
      (w0.dlo 0) (w0.dhi 0) (w0.elo 0) (w0.ehi 0) (w0.flo 0) (w0.fhi 0))
    (hL1 : Bundling.LatchRel x0 (PipeTimed.Wit.sq 7) x1
      (w1.dlo 0) (w1.dhi 0) (w1.elo 0) (w1.ehi 0) (w1.flo 0) (w1.fhi 0))
    (hw : ∀ w : Win, (w = w0 ∨ w = w1) → w.dlo 0 ≤ w.dhi 0 ∧ w.elo 0 ≤ w.ehi 0 ∧
      w.flo 0 ≤ w.fhi 0 ∧ 1 ≤ w.flo 0)
    (hvalid : ∀ k t, dS k ≤ t → t < dE k → d t = PipeTimed.Wit.valW k 0)
    (hlead : ∀ k, dS k + Sdr ≤ 4 + 4 * (2 * k) + Lag + sL)
    (hrel : ∀ k, 5 + 4 * (2 * k + 1) + Erel ≤ dE k)
    (hhold : w0.ehi 0 ≤ Erel + w0.dlo 0)
    (hpw : ∀ w : Win, (w = w0 ∨ w = w1) → w.ehi 0 + w.fhi 0 ≤ 4 + w.elo 0)
    (hsu : w0.dhi 0 + w0.fhi 0 + Lag ≤ Sdr + 1 + 4 + w0.elo 0)
    (hI : max ((w0.ehi 0 : Nat) : Int) ((Lag : Int) - Sdr - 1 + w0.dhi 0) + w1.dhi 0 + w1.fhi 0 ≤
      ((4 + 1 + 1 + w1.elo 0 : Nat) : Int) + (sI : Int))
    (hH : w1.ehi 0 ≤ 1 + 1 + w0.elo 0 + w1.dlo 0 + sH) :
    DataS PP PipeTimedN.Wit.OW (fun _ => d) (X2 x0 x1) PipeTimed.Wit.valW dS dE (V2 w0 w1)
      1 3 3 Erel Sdr Lag sI sH sL where
  H_LATCH i b hi hb := by
    have hb0 : b = 0 := by omega
    subst hb0
    match i, hi with
    | 0, _ => exact hL0
    | 1, _ => exact hL1
  H_WIN i b hi hb := by
    have hb0 : b = 0 := by omega
    subst hb0
    match i, hi with
    | 0, _ => exact hw w0 (Or.inl rfl)
    | 1, _ => exact hw w1 (Or.inr rfl)
  H_DATA_VALID k b t hb h1 h2 := by
    have hb0 : b = 0 := by omega
    subst hb0; exact hvalid k t h1 h2
  H_DATA_LEAD k := hlead k
  H_DATA_REL k := by rw [τ2]; exact hrel k
  H_HOLD0 b hb := by have hb0 : b = 0 := by omega
                     subst hb0; exact hhold
  H_PW i b hi hb := by
    have hb0 : b = 0 := by omega
    subst hb0
    rw [Won2]
    match i, hi with
    | 0, _ => exact hpw w0 (Or.inl rfl)
    | 1, _ => exact hpw w1 (Or.inr rfl)
  H_SETUP0 b hb := by
    have hb0 : b = 0 := by omega
    subst hb0
    rw [Won2]
    show w0.dhi 0 + w0.fhi 0 + Lag ≤ Sdr + 1 + 4 + w0.elo 0
    exact hsu
  H_I i b hi hb := by
    have hb0 : b = 0 := by omega
    have hi0 : i = 0 := by simp only [PP, PipeTimedN.Wit.Pw] at hi; omega
    subst hb0; subst hi0
    show max ((w0.ehi 0 : Nat) : Int) ((Lag : Int) - Sdr - ((1 : Nat) : Int) + (w0.dhi 0 : Nat))
        + ((w1.dhi 0 : Nat) : Int) + ((w1.fhi 0 : Nat) : Int) ≤
      ((PP.Won 3 3 0 + 1 + 1 + w1.elo 0 : Nat) : Int) + (sI : Int)
    rw [Won2]; omega
  H_H i b hi hb := by
    have hb0 : b = 0 := by omega
    have hi0 : i = 0 := by simp only [PP, PipeTimedN.Wit.Pw] at hi; omega
    subst hb0; subst hi0
    show w1.ehi 0 ≤ 1 + 1 + w0.elo 0 + w1.dlo 0 + sH
    exact hH

theorem sx0 (dS : Nat → Nat) (w0 w1 : Win) (k : Nat) :
    PP.Sx (V2 w0 w1) dS k 0 0 = max (5 + 4 * (2 * k) + w0.ehi 0) (dS k + w0.dhi 0) := by
  simp only [PN.Sx, τ2, V2]
theorem sx1 (dS : Nat → Nat) (w0 w1 : Win) (k : Nat) :
    PP.Sx (V2 w0 w1) dS k 0 1 =
      max (7 + 4 * (2 * k) + w1.ehi 0) (max (5 + 4 * (2 * k) + w0.ehi 0) (dS k + w0.dhi 0) + w1.dhi 0) := by
  simp only [PN.Sx, τ2, V2]

/-! ## 3. Run RH: H_H off by one (stage 1's enable arc 5) -/

def x1H (t : Nat) : Bool := decide ((12 ≤ t ∧ t < 15) ∨ (23 ≤ t ∧ (t - 23) % 16 < 8))

theorem x1H_rel (t : Nat) :
    x1H t = (if PipeTimed.Wit.sq 7 (t - 5) then PipeTimed.Wit.x0W (t - 1) else x1H (t - 1)) := by
  split
  · next h =>
    unfold PipeTimed.Wit.sq at h; simp at h
    unfold x1H PipeTimed.Wit.x0W; simp only [decide_eq_decide]; omega
  · next h =>
    unfold PipeTimed.Wit.sq at h; simp at h
    unfold x1H; simp only [decide_eq_decide]; omega

theorem x0W_rel1 (t : Nat) :
    PipeTimed.Wit.x0W t = (if PipeTimed.Wit.sq 5 (t - 1) then PipeTimed.Wit.dW (t - 1)
      else PipeTimed.Wit.x0W (t - 1)) := PipeTimed.Wit.x0_rel t

theorem validW (k t : Nat) (h1 : PipeTimed.Wit.dSW k ≤ t) (h2 : t < PipeTimed.Wit.dEW k) :
    PipeTimed.Wit.dW t = PipeTimed.Wit.valW k 0 := by
  unfold PipeTimed.Wit.dSW at h1; unfold PipeTimed.Wit.dEW at h2
  unfold PipeTimed.Wit.dW PipeTimed.Wit.valW; simp only [decide_eq_decide]; omega

/-- The weakened H_H holds with slack 1 and the original fails by exactly 1. -/
theorem H_viol : (pw 1 5 1).ehi 0 = 1 + 1 + (pw 1 1 1).elo 0 + (pw 1 5 1).dlo 0 + 1 := rfl

theorem dataS_H : DataS PP PipeTimedN.Wit.OW (fun _ => PipeTimed.Wit.dW)
    (X2 PipeTimed.Wit.x0W x1H) PipeTimed.Wit.valW PipeTimed.Wit.dSW PipeTimed.Wit.dEW
    (V2 (pw 1 1 1) (pw 1 5 1)) 1 3 3 1 2 0 0 1 0 :=
  mkDataS _ _ _ _ _ _ _ 1 2 0 0 1 0
    (latch_tr _ _ _ 1 1 1 x0W_rel1) (latch_tr _ _ _ 1 5 1 x1H_rel)
    (fun w hw => by rcases hw with rfl | rfl <;> decide) validW
    (fun k => by unfold PipeTimed.Wit.dSW; omega)
    (fun k => by unfold PipeTimed.Wit.dEW; omega)
    (by decide) (fun w hw => by rcases hw with rfl | rfl <;> decide) (by decide)
    (by decide) (by decide)

/-- **H_H cannot be weakened by 1.** On run RH every hypothesis of `token`
holds except H_H, which holds with slack 1; stage 1 shows token 1's value
(0) at 15, inside token 0's window `[Sx 1 = 12, τ 1 2 + elo = 20)`. -/
theorem H_false : ¬ TokClaim 0 1 0 := by
  intro h
  have := h PP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G2 E2 T2 dataS_H 0 0 (by decide) 1 (by decide)
    15 (by rw [sx1]; decide) (by rw [τ2]; decide)
  exact absurd this (by decide)

/-! ## 4. Run RI: H_I off by one (stage 0's enable arc 6, data late into stage 1) -/

def dI (t : Nat) : Bool := decide (6 ≤ t ∧ (t - 6) % 16 < 8)
def x0I (t : Nat) : Bool := decide (11 ≤ t ∧ (t - 11) % 16 < 8)
def x1I (t : Nat) : Bool := decide (16 ≤ t ∧ (t - 16) % 16 < 8)

theorem x0I_rel (t : Nat) :
    x0I t = (if PipeTimed.Wit.sq 5 (t - 6) then dI (t - 1) else x0I (t - 1)) := by
  split
  · next h =>
    unfold PipeTimed.Wit.sq at h; simp at h
    unfold x0I dI; simp only [decide_eq_decide]; omega
  · next h =>
    unfold PipeTimed.Wit.sq at h; simp at h
    unfold x0I; simp only [decide_eq_decide]; omega

theorem x1I_rel (t : Nat) :
    x1I t = (if PipeTimed.Wit.sq 7 (t - 1) then x0I (t - 1) else x1I (t - 1)) := by
  split
  · next h =>
    unfold PipeTimed.Wit.sq at h; simp at h
    unfold x1I x0I; simp only [decide_eq_decide]; omega
  · next h =>
    unfold PipeTimed.Wit.sq at h; simp at h
    unfold x1I; simp only [decide_eq_decide]; omega

def dSI (k : Nat) : Nat := 6 + 8 * k
def dEI (k : Nat) : Nat := 14 + 8 * k

theorem validI (k t : Nat) (h1 : dSI k ≤ t) (h2 : t < dEI k) : dI t = PipeTimed.Wit.valW k 0 := by
  unfold dSI at h1; unfold dEI at h2
  unfold dI PipeTimed.Wit.valW; simp only [decide_eq_decide]; omega

/-- H_I with slack 1 holds and fails by exactly 1 without it:
`Dl 0 + dhi1 + fhi1 = max 6 (2 - 0 - 1 + 1) + 1 + 1 = 8 = 4 + 1 + 1 + 1 + 1`. -/
theorem I_viol :
    max ((6 : Nat) : Int) ((2 : Int) - 0 - 1 + 1) + 1 + 1 = ((4 + 1 + 1 + 1 : Nat) : Int) + 1 := by
  decide

theorem dataS_I : DataS PP PipeTimedN.Wit.OW (fun _ => dI) (X2 x0I x1I) PipeTimed.Wit.valW dSI dEI
    (V2 (pw 1 6 1) (pw 1 1 1)) 1 3 3 5 0 2 1 0 0 :=
  mkDataS _ _ _ _ _ _ _ 5 0 2 1 0 0
    (latch_tr _ _ _ 1 6 1 x0I_rel) (latch_tr _ _ _ 1 1 1 x1I_rel)
    (fun w hw => by rcases hw with rfl | rfl <;> decide) validI
    (fun k => by unfold dSI; omega) (fun k => by unfold dEI; omega)
    (by decide) (fun w hw => by rcases hw with rfl | rfl <;> decide) (by decide)
    (by decide) (by decide)

/-- **H_I cannot be weakened by 1.** On run RI stage 1 still shows the
reset value at 12, inside token 0's window `[Sx 1 = 12, τ 1 2 + elo = 16)`. -/
theorem I_false : ¬ TokClaim 1 0 0 := by
  intro h
  have := h PP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G2 E2 T2 dataS_I 0 0 (by decide) 1 (by decide)
    12 (by rw [sx1]; decide) (by rw [τ2]; decide)
  exact absurd this (by decide)

/-! ## 5. Run RL: H_DATA_LEAD off by one (data 1 tick later than the lead allows) -/

def dL (t : Nat) : Bool := decide (5 ≤ t ∧ (t - 5) % 16 < 8)
def x0L (t : Nat) : Bool := decide (14 ≤ t ∧ (t - 14) % 16 < 8)
def x1L (t : Nat) : Bool := decide (16 ≤ t ∧ (t - 16) % 16 < 8)

theorem x0L_rel (t : Nat) :
    x0L t = (if PipeTimed.Wit.sq 5 (t - 1) then dL (t - 5) else x0L (t - 1)) := by
  split
  · next h =>
    unfold PipeTimed.Wit.sq at h; simp at h
    unfold x0L dL; simp only [decide_eq_decide]; omega
  · next h =>
    unfold PipeTimed.Wit.sq at h; simp at h
    unfold x0L; simp only [decide_eq_decide]; omega

theorem x1L_rel (t : Nat) :
    x1L t = (if PipeTimed.Wit.sq 7 (t - 1) then x0L (t - 1) else x1L (t - 1)) := by
  split
  · next h =>
    unfold PipeTimed.Wit.sq at h; simp at h
    unfold x1L x0L; simp only [decide_eq_decide]; omega
  · next h =>
    unfold PipeTimed.Wit.sq at h; simp at h
    unfold x1L; simp only [decide_eq_decide]; omega

def dSL (k : Nat) : Nat := 5 + 8 * k
def dEL (k : Nat) : Nat := 13 + 8 * k

theorem validL (k t : Nat) (h1 : dSL k ≤ t) (h2 : t < dEL k) : dL t = PipeTimed.Wit.valW k 0 := by
  unfold dSL at h1; unfold dEL at h2
  unfold dL PipeTimed.Wit.valW; simp only [decide_eq_decide]; omega

/-- The lead with slack 1 holds and fails by exactly 1 without it:
`dS k + Sdr = 5 + 8k = ρ (2k) + Lag + 1`; H_SETUP0 is tight (`5 + 1 + 0 = 0 + 1 + 4 + 1`). -/
theorem L_viol (k : Nat) : dSL k + 0 = (PipeTimedN.Wit.Pw 2).ρ (2 * k) + 0 + 1 := by
  show 5 + 8 * k + 0 = 4 + 4 * (2 * k) + 0 + 1; omega

theorem dataS_L : DataS PP PipeTimedN.Wit.OW (fun _ => dL) (X2 x0L x1L) PipeTimed.Wit.valW dSL dEL
    (V2 (pw 5 1 1) (pw 1 1 1)) 1 3 3 1 0 0 0 0 1 :=
  mkDataS _ _ _ _ _ _ _ 1 0 0 0 0 1
    (latch_tr _ _ _ 5 1 1 x0L_rel) (latch_tr _ _ _ 1 1 1 x1L_rel)
    (fun w hw => by rcases hw with rfl | rfl <;> decide) validL
    (fun k => by unfold dSL; omega) (fun k => by unfold dEL; omega)
    (by decide) (fun w hw => by rcases hw with rfl | rfl <;> decide) (by decide)
    (by decide) (by decide)

/-- **H_DATA_LEAD cannot be weakened by 1.** On run RL stage 0 shows the
stale value at 10, inside token 0's window `[Sx 0 = 10, τ 0 2 + elo = 14)`. -/
theorem L_false : ¬ TokClaim 0 0 1 := by
  intro h
  have := h PP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G2 E2 T2 dataS_L 0 0 (by decide) 0 (by decide)
    10 (by rw [sx0]; decide) (by rw [τ2]; decide)
  exact absurd this (by decide)

/-! ## 6. Run RO: the output rule `Dl (N-1) ≤ Er` off by one -/

def x1O (t : Nat) : Bool := decide (11 ≤ t ∧ (t - 11) % 16 < 8)

theorem x1O_rel (t : Nat) :
    x1O t = (if PipeTimed.Wit.sq 7 (t - 4) then PipeTimed.Wit.x0W (t - 1) else x1O (t - 1)) := by
  split
  · next h =>
    unfold PipeTimed.Wit.sq at h; simp at h
    unfold x1O PipeTimed.Wit.x0W; simp only [decide_eq_decide]; omega
  · next h =>
    unfold PipeTimed.Wit.sq at h; simp at h
    unfold x1O; simp only [decide_eq_decide]; omega

theorem dataN_O : DataN PP PipeTimedN.Wit.OW (fun _ => PipeTimed.Wit.dW)
    (X2 PipeTimed.Wit.x0W x1O) PipeTimed.Wit.valW PipeTimed.Wit.dSW PipeTimed.Wit.dEW
    (V2 (pw 1 1 1) (pw 1 4 1)) 1 3 3 1 2 0 :=
  DataS.toN (mkDataS _ _ _ _ _ _ _ 1 2 0 0 0 0
    (latch_tr _ _ _ 1 1 1 x0W_rel1) (latch_tr _ _ _ 1 4 1 x1O_rel)
    (fun w hw => by rcases hw with rfl | rfl <;> decide) validW
    (fun k => by unfold PipeTimed.Wit.dSW; omega)
    (fun k => by unfold PipeTimed.Wit.dEW; omega)
    (by decide) (fun w hw => by rcases hw with rfl | rfl <;> decide) (by decide)
    (by decide) (by decide))

/-- `Dl 1 = 4 = Er + 1` on run RO (H_H tight there: `4 = 1 + 1 + 1 + 1`). -/
theorem O_viol : Dl PP (V2 (pw 1 1 1) (pw 1 4 1)) 2 0 (PP.N - 1) 0 = (3 : Int) + 1 := by
  simp only [Dl, V2, pw, PP, PipeTimedN.Wit.Pw, Ret.shift]; decide

/-- **The output rule cannot be weakened by 1.** On run RO the last stage
shows the stale value at the receiver's acknowledge rise `γ 0 = 10`. -/
theorem out_false : ¬ OutClaim 1 := by
  intro h
  have := h PP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G2 E2 T2 dataN_O 0 0 (by decide)
    (by rw [O_viol]; decide) 10 (by decide) (by decide)
  exact absurd this (by decide)

/-! ## 7. Non-vacuity at slack 0

The claims at slack 0 are the shipped theorems; `PipeTimedN.Wit.witness_data`
is their non-vacuity witness (every hypothesis at every instant, every token
delivered). -/

end Formal.Cells.Necessity3Pipe
