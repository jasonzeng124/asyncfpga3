import Formal.Cells.AssumeGuaranteeLinks

/-!
# Probe Bedge (shard B): the chain's edge-time equations have a solution, every `N`

Bnet's `AssumeGuaranteeLinks` closes the assume-guarantee circle for a chain of `N` links
between a source and a sink, for EVERY solution of its edge-time equations (`Chain.H_TIMES`:
each link's edge `τ (m+1) j` is read off its own node after its pins' phase starts, the pin
edges `ε` of the drivers' edges). Existence of a solution was shown only on the hand-built
uniform witness `wD N` (all delays 1). This file CONSTRUCTS the solution for every delay
assignment inside the bands: the run is defined by strong recursion on time, its edge times
by the event-graph recurrence (recursion on `(j, i)` lexicographically), and every field of
`Chain` and `ChainT` is proved for it.

## Assumed / proved / NOT covered

**Assumed** (`Dly`, `Band`, and `ChainT` on the bands): a chain length `N`; bands
`[lo i, hi i]` (LUTs, cells `0 .. N+1`), `[fl, fh]` (feedback), `[wl, wh]`, `[vl, vh]`
(forward/backward wires), `lo, wl, vl ≥ 1`; ONE realised constant delay per gate inside its
band (`d, f, w, v`), so each gate of the run is a fixed transport delay (a legal behaviour
of every `Win`/`WinDelay` channel of the band); the reset `R`; a source start `T0` with
`R ≤ T0 + wl 0`, `wh 0 ≤ T0`; and B's timing rows `ChainT` (H_RST_LONG, H_LAT, H_WIRE_R,
H_RT) on the BANDS. The source is modelled as a cell that raises its request at `T0` and
then answers each acknowledge edge after `d 0` (`nd_src`), the sink as a cell that copies
its request after `d (N+1)` (`nd_snk`); the links are the real `bd_c2n` INIT (`nd_link`).

**Proved:**
* `chain_c`, `chainT_c`: the run with every band DEGENERATE at its realised delay satisfies
  `Chain`/`ChainT` (all gate relations, H_TIMES by construction, both end contracts
  `SRC_SEG`/`SNK_SEG` proved for the modelled ends);
* `chain_b`: the same run with the given BANDS satisfies `Chain` (H_NO_REVERT of each band
  from the cleanness of the excitation / driver with spacing above the spread; H_TIMES of
  the bands from `nt_phase`: a wider band's `nt` finds the same edge);
* `schedule` / `chain_solution`: the edge times are the max-plus schedule
  `τ (m+1) j = max (τ m j + w m) (ash R (τ (m+2) · + v (m+1)) j) + d (m+1)`,
  `τ 0 (j+1) = τ 1 j + v 0 + d 0`, `τ (N+1) j = τ N j + w N + d (N+1)`;
* `chain_exists`, `chain_env1_solution`: `chain_env1` (every link's `Env1`, `Timing1`) holds
  on a solution for every such assignment; `chain_solution_witness`: the hypotheses are
  jointly satisfiable for every `N` with non-uniform delays (`1 + i % 3` in band `[1, 3]`),
  H_LAT met with equality.

**NOT covered:** delays that vary from edge to edge inside the band (the run uses one
constant per gate; the theorems of `AssumeGuaranteeLinks` cover those runs too, but their
existence is not constructed here); uniqueness (the bands admit many runs); the source and
sink are concrete models, not arbitrary contracts. Core Lean only.
-/

namespace Formal.Cells.EdgeTimes
open Formal.Cells
open Formal.Cells.WinFifo (Win win_le Clean Spread)
open Formal.Cells.WinFifoCausal (NoRevertI nt nt_lo nt_eq nt_before node_win Stage Env1 Timing1
  cph τs cW vW)
open Formal.Cells.PipeTimed (Vph ex Ret)
open Formal.Cells.LutFbBridge (Phases)
open Formal.Cells.LutFbBridge2Env (Wire ε ε_lo ash)
open Formal.Cells.AssumeGuaranteeLinks

/-- A delay assignment for a chain: the bands of `ChainData` and one realised constant
delay inside each band. -/
structure Dly where
  N : Nat
  R : Nat
  T0 : Nat
  lo : Nat → Nat
  hi : Nat → Nat
  fl : Nat → Nat
  fh : Nat → Nat
  wl : Nat → Nat
  wh : Nat → Nat
  vl : Nat → Nat
  vh : Nat → Nat
  d : Nat → Nat
  f : Nat → Nat
  w : Nat → Nat
  v : Nat → Nat

/-- A wire with constant delay `d`: `0` before `d`. -/
def pin (d : Nat) (x : Nat → Bool) (t : Nat) : Bool := if d ≤ t then x (t - d) else false

/-- **The run** (by strong recursion on time; every LUT delay is `≥ 1`). -/
def nd (P : Dly) (i t : Nat) : Bool :=
  if i = 0 then
    decide (P.T0 ≤ t) && (if _h : 1 ≤ P.d 0 ∧ P.d 0 ≤ t then
      !(if P.v 0 ≤ t - P.d 0 then nd P 1 (t - P.d 0 - P.v 0) else false) else true)
  else if i ≤ P.N then
    if _h : 1 ≤ P.d i ∧ P.d i ≤ t then
      CElemTiming.exc CElemTiming.INIT_c2n
        (if P.w (i - 1) ≤ t - P.d i then nd P (i - 1) (t - P.d i - P.w (i - 1)) else false)
        (if P.v i ≤ t - P.d i then nd P (i + 1) (t - P.d i - P.v i) else false)
        (if P.f i ≤ t - P.d i then nd P i (t - P.d i - P.f i) else false)
        (decide (t - P.d i < P.R))
    else false
  else if i = P.N + 1 then
    if _h : 1 ≤ P.d i ∧ P.d i ≤ t then
      (if P.w (i - 1) ≤ t - P.d i then nd P (i - 1) (t - P.d i - P.w (i - 1)) else false)
    else false
  else false
termination_by t
decreasing_by all_goals omega

def rq (P : Dly) : Nat → Nat → Bool
  | 0 => fun _ => false
  | i + 1 => pin (P.w i) (nd P i)

def ak (P : Dly) (i : Nat) : Nat → Bool := pin (P.v i) (nd P (i + 1))
def qf (P : Dly) (i : Nat) : Nat → Bool := pin (P.f i) (nd P i)
def rs (P : Dly) (t : Nat) : Bool := decide (t < P.R)

theorem nd_src (P : Dly) (t : Nat) : nd P 0 t =
    (decide (P.T0 ≤ t) && (if 1 ≤ P.d 0 ∧ P.d 0 ≤ t then !(ak P 0 (t - P.d 0)) else true)) := by
  rw [nd]; simp only [↓reduceIte, ak, pin, dite_eq_ite, Nat.zero_add]

theorem nd_link (P : Dly) (m t : Nat) (hm : m < P.N) : nd P (m + 1) t =
    (if 1 ≤ P.d (m + 1) ∧ P.d (m + 1) ≤ t then
      ex (rq P (m + 1)) (ak P (m + 1)) (qf P (m + 1)) (rs P) (t - P.d (m + 1)) else false) := by
  rw [nd]
  simp only [Nat.add_one_ne_zero, ite_false, show m + 1 ≤ P.N by omega, ite_true,
    Nat.add_sub_cancel, dite_eq_ite, ex, rq, ak, qf, rs, pin]

theorem nd_snk (P : Dly) (t : Nat) : nd P (P.N + 1) t =
    (if 1 ≤ P.d (P.N + 1) ∧ P.d (P.N + 1) ≤ t then rq P (P.N + 1) (t - P.d (P.N + 1))
      else false) := by
  rw [nd]
  simp only [Nat.add_one_ne_zero, show ¬ (P.N + 1 ≤ P.N) by omega, ↓reduceIte,
    Nat.add_sub_cancel, dite_eq_ite, rq, pin]


/-- **The edge times** (the max-plus / event-graph schedule, read off the run exactly as
`Chain.H_TIMES` reads them, with every band degenerate at its realised delay). Defined by
recursion on `(j, i)` lexicographically: event `(i, j)` needs `(i - 1, j)` and
`(i + 1, j - 1)`. -/
def tau (P : Dly) (i j : Nat) : Nat :=
  if i = 0 then
    match j with
    | 0 => P.T0
    | k + 1 => nt (ak P 0) (P.v 0) (P.v 0) (tau P 1 k) (Vph k) + P.d 0
  else if i ≤ P.N then
    nt (nd P i) (P.d i) (P.d i)
      (max (nt (rq P i) (P.w (i - 1)) (P.w (i - 1)) (tau P (i - 1) j) (Vph j))
        (match j with
         | 0 => P.R
         | k + 1 => nt (ak P i) (P.v i) (P.v i) (tau P (i + 1) k) (Vph k))) (Vph j)
  else if i = P.N + 1 then
    nt (rq P i) (P.w (i - 1)) (P.w (i - 1)) (tau P (i - 1) j) (Vph j) + P.d i
  else 0
termination_by (j, i)


/-- The run as `ChainData` with every band DEGENERATE at its realised delay. -/
def cD (P : Dly) : ChainData where
  N := P.N
  R := P.R
  O := nd P
  req := rq P
  ack := ak P
  qp := qf P
  rst := rs P
  lo := P.d
  hi := P.d
  fl := P.f
  fh := P.f
  wl := P.w
  wh := P.w
  vl := P.v
  vh := P.v
  τ := tau P

/-- The same run as `ChainData` with the given BANDS. -/
def bD (P : Dly) : ChainData where
  N := P.N
  R := P.R
  O := nd P
  req := rq P
  ack := ak P
  qp := qf P
  rst := rs P
  lo := P.lo
  hi := P.hi
  fl := P.fl
  fh := P.fh
  wl := P.wl
  wh := P.wh
  vl := P.vl
  vh := P.vh
  τ := tau P

theorem tau_src0 (P : Dly) : tau P 0 0 = P.T0 := by unfold tau; rfl

theorem tau_srcS (P : Dly) (k : Nat) : tau P 0 (k + 1) = (cD P).εB 0 k + P.d 0 := by
  unfold tau; rfl

theorem tau_link (P : Dly) (m j : Nat) (hm : m < P.N) :
    tau P (m + 1) j = τs (nd P (m + 1)) (P.d (m + 1)) (P.d (m + 1)) ((cD P).ρL m)
      ((cD P).αL m) j := by
  unfold tau
  simp only [Nat.add_one_ne_zero, ↓reduceIte, show m + 1 ≤ P.N by omega, Nat.add_sub_cancel]
  cases j <;> rfl

theorem tau_snk (P : Dly) (j : Nat) : tau P (P.N + 1) j = (cD P).εF P.N j + P.d (P.N + 1) := by
  unfold tau
  simp only [Nat.add_one_ne_zero, ↓reduceIte, show ¬ (P.N + 1 ≤ P.N) by omega,
    Nat.add_sub_cancel]
  rfl

/-- Positivity of the realised delays and the source's start. -/
structure Pos (P : Dly) : Prop where
  H_D : ∀ i, i ≤ P.N + 1 → 1 ≤ P.d i
  H_W : ∀ i, i ≤ P.N → 1 ≤ P.w i
  H_V : ∀ i, i ≤ P.N → 1 ≤ P.v i
  H_T0 : P.R ≤ P.T0 + P.w 0 ∧ P.w 0 ≤ P.T0

section pos
variable {P : Dly} (H : Pos P)
include H
set_option linter.unusedSectionVars false

theorem tau_fwd (i : Nat) (hi : i ≤ P.N) (j : Nat) : tau P i j + P.w i + P.d (i + 1) ≤ tau P (i + 1) j := by
  rcases Nat.lt_or_ge i P.N with h | h
  · rw [tau_link P i j h]
    have := nt_lo (nd P (i + 1)) (cph ((cD P).ρL i) ((cD P).αL i) j) (Vph j)
      (Nat.le_refl (P.d (i + 1))) (hi := P.d (i + 1))
    have : (cD P).ρL i j ≤ cph ((cD P).ρL i) ((cD P).αL i) j := Nat.le_max_left _ _
    have : tau P i j + P.w i ≤ (cD P).ρL i j :=
      nt_lo (rq P (i + 1)) (tau P i j) (Vph j) (Nat.le_refl (P.w i)) (hi := P.w i)
    unfold τs; omega
  · have e : i = P.N := by omega
    subst e; rw [tau_snk]
    have : tau P P.N j + P.w P.N ≤ (cD P).εF P.N j :=
      nt_lo (rq P (P.N + 1)) (tau P P.N j) (Vph j) (Nat.le_refl (P.w P.N)) (hi := P.w P.N)
    omega

theorem tau_src_mono : ∀ j, P.T0 ≤ tau P 0 j := by
  intro j
  induction j with
  | zero => rw [tau_src0]; exact Nat.le_refl _
  | succ k ih =>
    rw [tau_srcS]
    have := tau_fwd H 0 (Nat.zero_le _) k
    simp only [Nat.zero_add] at this
    have : tau P 1 k + P.v 0 ≤ (cD P).εB 0 k :=
      nt_lo (ak P 0) (tau P 1 k) (Vph k) (Nat.le_refl (P.v 0)) (hi := P.v 0)
    omega

theorem src_seg (k : Nat) (hk : ∀ k', k' < k → SegK (ak P 0) ((cD P).εB 0) k') :
    SegK (nd P 0) (tau P 0) k := by
  have hd := H.H_D 0 (by omega)
  match k with
  | 0 =>
    intro t _ ht
    rw [tau_src0] at ht
    show nd P 0 t = false
    rw [nd_src]; simp only [show ¬ P.T0 ≤ t by omega, decide_false, Bool.false_and]
  | j + 1 =>
    intro t h1 h2
    show nd P 0 t = Vph j
    have hT := tau_src_mono H j
    have h1' : tau P 0 j ≤ t := h1
    cases j with
    | zero =>
      rw [tau_srcS] at h2
      rw [nd_src]
      simp only [show P.T0 ≤ t by omega, decide_true, Bool.true_and]
      split
      · have := hk 0 (by omega) (t - P.d 0) (Nat.zero_le _) (by omega)
        rw [this]; rfl
      · rfl
    | succ k =>
      rw [tau_srcS] at hT h1' h2
      rw [nd_src]
      simp only [show P.T0 ≤ t by omega, decide_true, Bool.true_and,
        show 1 ≤ P.d 0 ∧ P.d 0 ≤ t by omega]
      have := hk (k + 1) (by omega) (t - P.d 0) (by show (cD P).εB 0 k ≤ _; omega) (by omega)
      rw [this, PipeTimed.Vph_succ]; rfl

theorem snk_seg (k : Nat) (hk : ∀ k', k' ≤ k → SegK (rq P (P.N + 1)) ((cD P).εF P.N) k') :
    SegK (nd P (P.N + 1)) (tau P (P.N + 1)) k := by
  have hd := H.H_D (P.N + 1) (Nat.le_refl _)
  match k with
  | 0 =>
    intro t _ ht
    rw [tau_snk] at ht
    show nd P (P.N + 1) t = false
    rw [nd_snk]; split
    · exact hk 0 (Nat.le_refl _) (t - P.d (P.N + 1)) (Nat.zero_le _) (by omega)
    · rfl
  | j + 1 =>
    intro t h1 h2
    have h1' : tau P (P.N + 1) j ≤ t := h1
    rw [tau_snk] at h1' h2
    show nd P (P.N + 1) t = Vph j
    rw [nd_snk, if_pos (by omega)]
    exact hk (j + 1) (Nat.le_refl _) (t - P.d (P.N + 1)) (by show (cD P).εF P.N j ≤ _; omega)
      (by omega)


end pos

/-- A constant-delay wire is a `Wire` of the degenerate band. -/
theorem wire_pin (x : Nat → Bool) {d : Nat} (hd : 1 ≤ d) : Wire d d x (pin d x) :=
  ⟨CElemTiming.transport_winDelay (Nat.le_refl d) (Nat.le_refl d)
      (fun t => by simp [pin]),
    WinFifoCausal.noRevertI_shift (fun t ht => by simp [pin, ht]),
    hd, fun t ht => by simp [pin]; omega⟩

theorem nd_link_tr (P : Dly) (m : Nat) (hm : m < P.N) (hd : 1 ≤ P.d (m + 1)) :
    ∀ t, P.d (m + 1) ≤ t → nd P (m + 1) t =
      ex (rq P (m + 1)) (ak P (m + 1)) (qf P (m + 1)) (rs P) (t - P.d (m + 1)) := by
  intro t ht; rw [nd_link P m t hm, if_pos ⟨hd, ht⟩]

theorem stage_c (P : Dly) (m : Nat) (hm : m < P.N) (hd : 1 ≤ P.d (m + 1)) :
    Stage (rq P (m + 1)) (ak P (m + 1)) (rs P) (nd P (m + 1)) (qf P (m + 1))
      (P.d (m + 1)) (P.d (m + 1)) (P.f (m + 1)) (P.f (m + 1)) where
  H_LUT_WIN t ht := ⟨t - P.d (m + 1), by omega, by omega, nd_link_tr P m hm hd t ht⟩
  H_NO_REVERT := WinFifoCausal.noRevertI_shift (nd_link_tr P m hm hd)
  H_FB := CElemTiming.transport_winDelay (Nat.le_refl _) (Nat.le_refl _)
    (fun t => by simp [qf, pin])
  H_LOOP_POS := by omega

/-- **The degenerate-band run is a solution of `Chain`** (all gate relations, H_TIMES,
both end contracts), for every `N` and every positive delay assignment. -/
theorem chain_c {P : Dly} (H : Pos P) : Chain (cD P) where
  H_RST _ := rfl
  H_STAGE m hm := stage_c P m hm (H.H_D (m + 1) (by show m + 1 ≤ P.N + 1; have : m < P.N := hm; omega))
  H_PWR m hm t ht := by
    show nd P (m + 1) t = false
    rw [nd_link P m t hm, if_neg (by have : t < P.d (m + 1) := ht; omega)]
  H_LUT_POS i hi := H.H_D i hi
  H_WF i hi := wire_pin (nd P i) (H.H_W i hi)
  H_WB i hi := wire_pin (nd P (i + 1)) (H.H_V i hi)
  H_TIMES m hm j := tau_link P m j hm
  SRC_WAIT j := by
    show _ ≤ tau P 0 (j + 1); rw [tau_srcS]; exact Nat.le_refl _
  SRC_T0 := by show P.R ≤ tau P 0 0 + P.w 0 ∧ P.w 0 ≤ tau P 0 0; rw [tau_src0]; exact H.H_T0
  SRC_SEG k hk := src_seg H k hk
  SNK_WAIT j := by
    show _ ≤ tau P (P.N + 1) j; rw [tau_snk]; exact Nat.le_refl _
  SNK_SEG k hk := snk_seg H k hk

/-! ## The bands -/

/-- **The realised delays lie in the bands**, the bands' positivity, and the source's start. -/
structure Band (P : Dly) : Prop where
  H_D : ∀ i, i ≤ P.N + 1 → P.lo i ≤ P.d i ∧ P.d i ≤ P.hi i
  H_F : ∀ m, m < P.N → P.fl (m + 1) ≤ P.f (m + 1) ∧ P.f (m + 1) ≤ P.fh (m + 1)
  H_W : ∀ i, i ≤ P.N → P.wl i ≤ P.w i ∧ P.w i ≤ P.wh i
  H_V : ∀ i, i ≤ P.N → P.vl i ≤ P.v i ∧ P.v i ≤ P.vh i
  H_LUT_POS : ∀ i, i ≤ P.N + 1 → 1 ≤ P.lo i
  H_WIRE_POS : ∀ i, i ≤ P.N → 1 ≤ P.wl i ∧ 1 ≤ P.vl i
  H_T0 : P.R ≤ P.T0 + P.wl 0 ∧ P.wh 0 ≤ P.T0

theorem pos_of_band {P : Dly} (B : Band P) : Pos P where
  H_D i hi := by have := B.H_D i hi; have := B.H_LUT_POS i hi; omega
  H_W i hi := by have := B.H_W i hi; have := B.H_WIRE_POS i hi; omega
  H_V i hi := by have := B.H_V i hi; have := B.H_WIRE_POS i hi; omega
  H_T0 := by have := B.H_T0; have := B.H_W 0 (Nat.zero_le _); omega

/-- The timing rows on the bands imply them on the realised delays. -/
theorem chainT_c {P : Dly} (B : Band P) (T : ChainT (bD P)) : ChainT (cD P) where
  H_RST_LONG m hm := by
    have h0 : P.hi (m + 1) + P.fh (m + 1) ≤ P.R := T.H_RST_LONG m hm
    have := B.H_D (m + 1) (by show m + 1 ≤ P.N + 1; have : m < P.N := hm; omega)
    have := B.H_F m hm
    show P.d (m + 1) + P.f (m + 1) ≤ P.R
    omega
  H_LAT m hm := by
    have hm' : m < P.N := hm
    have h := T.H_LAT m hm
    have := B.H_D (m + 1) (by omega); have := B.H_D m (by omega); have := B.H_D (m + 2) (by omega)
    have := B.H_F m hm; have := B.H_W m (by omega); have := B.H_W (m + 1) (by omega)
    have := B.H_V m (by omega); have := B.H_V (m + 1) (by omega)
    have h' : P.hi (m + 1) + P.fh (m + 1) ≤ P.lo (m + 1) + min (P.vl m + P.lo m + P.wl m)
      (P.wl (m + 1) + P.lo (m + 2) + P.vl (m + 1)) := h
    show P.d (m + 1) + P.f (m + 1) ≤ P.d (m + 1) + min (P.v m + P.d m + P.w m)
      (P.w (m + 1) + P.d (m + 2) + P.v (m + 1))
    omega
  H_WIRE_R i hi := by
    have h0 : P.wh i ≤ P.R ∧ P.vh i ≤ P.R := T.H_WIRE_R i hi
    have := B.H_W i hi; have := B.H_V i hi
    show P.w i ≤ P.R ∧ P.v i ≤ P.R
    omega
  H_RT i _ := by
    show P.w i ≤ P.w i + P.d (i + 1) + P.v i + P.d i ∧ P.v i ≤ P.w i + P.d (i + 1) + P.v i + P.d i
    omega

/-- A node read through `nt` with any band containing its actual delay: if the trace is a
clean step signal with edges `e`, edge `j` is at `c + dd`, and the previous edge is no later
than `c + lo`, then `nt` finds exactly `c + dd`. -/
theorem nt_phase {x : Nat → Bool} {e : Nat → Nat} (hx : Phases x e) {lo hi dd c j : Nat}
    (h1 : lo ≤ dd) (h2 : dd ≤ hi) (he : e j = c + dd) (hinc : e j < e (j + 1))
    (hprev : ∀ k, j = k + 1 → e k ≤ c + lo) : nt x lo hi c (Vph j) = c + dd := by
  unfold nt
  apply WinFifoCausal.lfind_eq _ _ _ (by omega)
  · have := hx.ph j (e j) (Nat.le_refl _) hinc
    rw [← he, this]; simp; omega
  · intro t ht
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
    by_cases hl : c + lo ≤ t
    · right
      cases j with
      | zero => rw [hx.pre t (by omega)]; decide
      | succ k =>
        have := hprev k rfl
        rw [hx.ph k t (by omega) (by omega), PipeTimed.Vph_succ]; cases Vph k <;> decide
    · left; exact hl

/-- A transport read of band `[lo, hi]`. -/
def bRet (lo hi d : Nat) (h1 : lo ≤ d) (h2 : d ≤ hi) : Ret where
  σ t := t - d
  lo := lo
  hi := hi
  mono a b h := by omega
  ge t := by omega
  le t := by omega

/-- A constant-delay wire of delay `w` in the band `[wl, wh]`, driven by a clean step
signal whose edges are more than the spread apart, is a `Wire wl wh`. -/
theorem wire_band {x : Nat → Bool} {e : Nat → Nat} (hx : Phases x e) {wl w wh : Nat}
    (hp : 1 ≤ wl) (h1 : wl ≤ w) (h2 : w ≤ wh) (h0 : wh ≤ e 0)
    (hsp : ∀ j, e j + wh < e (j + 1) + wl) : Wire wl wh x (pin w x) := by
  have hc := WinFifoCausal.clean_of_phases (by omega) hx.pre hx.ph hsp (by omega)
  refine ⟨CElemTiming.transport_winDelay h1 h2 (fun t => by simp [pin]),
    WinFifoCausal.noRevertI_of_ret hc.1 hc.2 (bRet wl wh w h1 h2) rfl rfl
      (fun t ht => by simp [pin, bRet]; omega), hp, fun t ht => ?_⟩
  unfold pin; split
  · exact hx.pre _ (by omega)
  · rfl

section band
variable {P : Dly} (B : Band P) (T : ChainT (bD P))
include B T
set_option linter.unusedSectionVars false

theorem cC : Chain (cD P) := chain_c (pos_of_band B)
theorem cT : ChainT (cD P) := chainT_c B T

theorem nodes (i : Nat) (hi : i ≤ P.N + 1) : Phases (nd P i) (tau P i) :=
  chain_nodes (cC B T) (cT B T) i hi

theorem inc (i : Nat) (hi : i ≤ P.N + 1) (j : Nat) : tau P i j < tau P i (j + 1) :=
  c_inc (cC B T) i hi j

/-- Forward pin edges: the node's edge plus the wire delay. -/
theorem εF_c (i : Nat) (hi : i ≤ P.N) (j : Nat) : (cD P).εF i j = tau P i j + P.w i := by
  show nt (rq P (i + 1)) (P.w i) (P.w i) (tau P i j) (Vph j) = _
  apply nt_eq _ (Nat.le_refl _)
  show pin (P.w i) (nd P i) _ = _
  simp only [pin, Nat.le_add_left, ↓reduceIte, Nat.add_sub_cancel]
  exact (nodes B T i (by omega)).ph j _ (Nat.le_refl _) (inc B T i (by omega) j)

theorem εB_c (i : Nat) (hi : i ≤ P.N) (j : Nat) : (cD P).εB i j = tau P (i + 1) j + P.v i := by
  show nt (ak P i) (P.v i) (P.v i) (tau P (i + 1) j) (Vph j) = _
  apply nt_eq _ (Nat.le_refl _)
  show pin (P.v i) (nd P (i + 1)) _ = _
  simp only [pin, Nat.le_add_left, ↓reduceIte, Nat.add_sub_cancel]
  exact (nodes B T (i + 1) (by omega)).ph j _ (Nat.le_refl _) (inc B T (i + 1) (by omega) j)

theorem εF_b (i : Nat) (hi : i ≤ P.N) (j : Nat) : (bD P).εF i j = (cD P).εF i j := by
  rw [εF_c B T i hi j]
  show nt (rq P (i + 1)) (P.wl i) (P.wh i) (tau P i j) (Vph j) = _
  have hw := (B.H_W i hi)
  have hph := chain_reqPin (cC B T) (cT B T) i hi
  apply nt_phase hph hw.1 hw.2 (εF_c B T i hi j)
  · rw [εF_c B T i hi j, εF_c B T i hi (j + 1)]; have := inc B T i (by omega) j; omega
  · intro k hk; subst hk; rw [εF_c B T i hi k]
    have : tau P i k + (cD P).RT i ≤ tau P i (k + 1) := c_spL (cC B T) i hi k
    have : (cD P).RT i = P.w i + P.d (i + 1) + P.v i + P.d i := rfl
    show _ ≤ tau P i (k + 1) + P.wl i
    omega

theorem εB_b (i : Nat) (hi : i ≤ P.N) (j : Nat) : (bD P).εB i j = (cD P).εB i j := by
  rw [εB_c B T i hi j]
  show nt (ak P i) (P.vl i) (P.vh i) (tau P (i + 1) j) (Vph j) = _
  have hv := (B.H_V i hi)
  have hph := chain_ackPin (cC B T) (cT B T) i hi
  apply nt_phase hph hv.1 hv.2 (εB_c B T i hi j)
  · rw [εB_c B T i hi j, εB_c B T i hi (j + 1)]; have := inc B T (i + 1) (by omega) j; omega
  · intro k hk; subst hk; rw [εB_c B T i hi k]
    have : tau P (i + 1) k + (cD P).RT i ≤ tau P (i + 1) (k + 1) := c_spR (cC B T) i hi k
    have : (cD P).RT i = P.w i + P.d (i + 1) + P.v i + P.d i := rfl
    show _ ≤ tau P (i + 1) (k + 1) + P.vl i
    omega

theorem ρL_b (m : Nat) (hm : m < P.N) : (bD P).ρL m = (cD P).ρL m :=
  funext fun j => εF_b B T m (by omega) j

theorem αL_b (m : Nat) (hm : m < P.N) : (bD P).αL m = (cD P).αL m := by
  funext j
  cases j with
  | zero => rfl
  | succ k => exact εB_b B T (m + 1) (by omega) k

theorem env_c (m : Nat) (hm : m < P.N) :
    Env1 (rq P (m + 1)) (ak P (m + 1)) (rs P) (nd P (m + 1)) (P.d (m + 1)) (P.d (m + 1)) P.R
      ((cD P).ρL m) ((cD P).αL m) ((cD P).Es m) ((cD P).Ea m) ∧
    Timing1 (P.d (m + 1)) (P.d (m + 1)) (P.f (m + 1)) P.R ((cD P).Es m) ((cD P).Ea m) :=
  chain_env1 (cC B T) (cT B T) m hm

theorem hd1 (m : Nat) (hm : m < P.N) : 1 ≤ P.d (m + 1) := (pos_of_band B).H_D (m + 1) (by omega)

/-- **The max-plus form of a link's edge**: phase start (last arrival) plus the LUT's
realised delay. -/
theorem tau_cph (m : Nat) (hm : m < P.N) (j : Nat) :
    tau P (m + 1) j = cph ((cD P).ρL m) ((cD P).αL m) j + P.d (m + 1) := by
  obtain ⟨E, Tm⟩ := env_c B T m hm
  have S := stage_c P m hm (hd1 B T m hm)
  rw [tau_link P m j hm]; unfold τs
  apply nt_eq _ (Nat.le_refl _)
  rw [nd_link_tr P m hm (hd1 B T m hm) _ (by omega), Nat.add_sub_cancel]
  have := WinFifoCausal.s_gap S E Tm j
  have := hd1 B T m hm
  exact WinFifoCausal.s_phase S E Tm j _ (Nat.le_refl _) (by omega)

theorem gap_c (m : Nat) (hm : m < P.N) (j : Nat) :
    cph ((cD P).ρL m) ((cD P).αL m) j + P.d (m + 1) + min ((cD P).Es m) ((cD P).Ea m) ≤
      cph ((cD P).ρL m) ((cD P).αL m) (j + 1) := by
  obtain ⟨E, Tm⟩ := env_c B T m hm
  exact WinFifoCausal.s_gap (stage_c P m hm (hd1 B T m hm)) E Tm j

/-- The link LUT's band read: `Win` and H_NO_REVERT of band `[lo, hi]` hold for the run
(the excitation is clean with spacing above the spread, so the transport read of delay
`d ∈ [lo, hi]` cannot revert). -/
theorem stage_b (m : Nat) (hm : m < P.N) :
    Stage (rq P (m + 1)) (ak P (m + 1)) (rs P) (nd P (m + 1)) (qf P (m + 1))
      (P.lo (m + 1)) (P.hi (m + 1)) (P.fl (m + 1)) (P.fh (m + 1)) := by
  obtain ⟨E, Tm⟩ := env_c B T m hm
  have hm' : m < P.N := hm
  have S := stage_c P m hm (hd1 B T m hm)
  have hcl := (WinFifoCausal.stage_fifo S E Tm).1
  have hb := B.H_D (m + 1) (by omega)
  have hf := B.H_F m hm
  have hlp := B.H_LUT_POS (m + 1) (by omega)
  have hsp : Spread (P.lo (m + 1)) (P.hi (m + 1)) (cW (cph ((cD P).ρL m) ((cD P).αL m))) := by
    intro j hj
    match j, hj with
    | k + 1, _ =>
      show cph _ _ k + _ < cph _ _ (k + 1) + _
      have g := gap_c B T m hm k
      have hl : P.hi (m + 1) + P.fh (m + 1) ≤ P.lo (m + 1) + min (P.vl m + P.lo m + P.wl m)
        (P.wl (m + 1) + P.lo (m + 2) + P.vl (m + 1)) := T.H_LAT m hm
      have e1 : (cD P).Es m = P.v m + P.d m + P.w m := rfl
      have e2 : (cD P).Ea m = P.w (m + 1) + P.d (m + 2) + P.v (m + 1) := rfl
      have := B.H_D m (by omega); have := B.H_D (m + 2) (by omega)
      have := B.H_W m (by omega); have := B.H_W (m + 1) (by omega)
      have := B.H_V m (by omega); have := B.H_V (m + 1) (by omega)
      omega
  exact { H_LUT_WIN := fun t ht => ⟨t - P.d (m + 1), by omega, by omega,
            nd_link_tr P m hm (hd1 B T m hm) t (by omega)⟩
          H_NO_REVERT := WinFifoCausal.noRevertI_of_ret hcl hsp
            (bRet (P.lo (m + 1)) (P.hi (m + 1)) (P.d (m + 1)) hb.1 hb.2) rfl rfl
            (fun t ht => nd_link_tr P m hm (hd1 B T m hm) t (by omega))
          H_FB := CElemTiming.transport_winDelay hf.1 hf.2 (fun t => by simp [qf, pin])
          H_LOOP_POS := by omega }

/-- **The run with the given bands is a solution of `Chain`.** -/
theorem chain_b : Chain (bD P) where
  H_RST _ := rfl
  H_STAGE m hm := stage_b B T m hm
  H_PWR m hm t ht := by
    have hm' : m < P.N := hm
    have h1 : P.R < tau P (m + 1) 0 := c_geR (cC B T) m (by show m ≤ P.N; omega) 0
    have h2 : P.hi (m + 1) + P.fh (m + 1) ≤ P.R := T.H_RST_LONG m hm
    exact (nodes B T (m + 1) (by omega)).pre t (by have : t < P.hi (m + 1) := ht; omega)
  H_LUT_POS i hi := B.H_LUT_POS i hi
  H_WF i hi := by
    have hi' : i ≤ P.N := hi
    have hw := B.H_W i hi
    refine wire_band (nodes B T i (by omega)) (B.H_WIRE_POS i hi).1 hw.1 hw.2 ?_ (fun j => ?_)
    · cases i with
      | zero => rw [tau_src0]; exact B.H_T0.2
      | succ m =>
        have h1 : P.R < tau P (m + 1) 0 := c_geR (cC B T) m (by show m ≤ P.N; omega) 0
        have h2 : P.wh (m + 1) ≤ P.R ∧ P.vh (m + 1) ≤ P.R := T.H_WIRE_R (m + 1) hi
        show P.wh (m + 1) ≤ tau P (m + 1) 0
        omega
    · have h1 : tau P i j + (cD P).RT i ≤ tau P i (j + 1) := c_spL (cC B T) i hi j
      have h2 : P.wh i ≤ (bD P).RT i ∧ P.vh i ≤ (bD P).RT i := T.H_RT i hi
      have e1 : (cD P).RT i = P.w i + P.d (i + 1) + P.v i + P.d i := rfl
      have e2 : (bD P).RT i = P.wl i + P.lo (i + 1) + P.vl i + P.lo i := rfl
      have := B.H_D i (by omega); have := B.H_D (i + 1) (by omega); have := B.H_V i hi
      have := (B.H_WIRE_POS i hi).1
      show tau P i j + P.wh i < tau P i (j + 1) + P.wl i
      omega
  H_WB i hi := by
    have hi' : i ≤ P.N := hi
    have hv := B.H_V i hi
    refine wire_band (nodes B T (i + 1) (by omega)) (B.H_WIRE_POS i hi).2 hv.1 hv.2 ?_ (fun j => ?_)
    · have h1 : P.R < tau P (i + 1) 0 := c_geR (cC B T) i hi 0
      have h2 : P.wh i ≤ P.R ∧ P.vh i ≤ P.R := T.H_WIRE_R i hi
      show P.vh i ≤ tau P (i + 1) 0
      omega
    · have h1 : tau P (i + 1) j + (cD P).RT i ≤ tau P (i + 1) (j + 1) := c_spR (cC B T) i hi j
      have h2 : P.wh i ≤ (bD P).RT i ∧ P.vh i ≤ (bD P).RT i := T.H_RT i hi
      have e1 : (cD P).RT i = P.w i + P.d (i + 1) + P.v i + P.d i := rfl
      have e2 : (bD P).RT i = P.wl i + P.lo (i + 1) + P.vl i + P.lo i := rfl
      have := B.H_D i (by omega); have := B.H_D (i + 1) (by omega); have := B.H_W i hi
      have := (B.H_WIRE_POS i hi).2
      show tau P (i + 1) j + P.vh i < tau P (i + 1) (j + 1) + P.vl i
      omega
  H_TIMES m hm j := by
    have hm' : m < P.N := hm
    show tau P (m + 1) j = τs (nd P (m + 1)) (P.lo (m + 1)) (P.hi (m + 1)) ((bD P).ρL m)
      ((bD P).αL m) j
    rw [ρL_b B T m hm, αL_b B T m hm]; unfold τs
    have hb := B.H_D (m + 1) (by omega)
    rw [nt_phase (nodes B T (m + 1) (by omega)) hb.1 hb.2 (tau_cph B T m hm j)
      (inc B T (m + 1) (by omega) j) (fun k hk => ?_)]
    · exact tau_cph B T m hm j
    · subst hk; rw [tau_cph B T m hm k]; have := gap_c B T m hm k; omega
  SRC_WAIT j := by
    show (bD P).εB 0 j + P.lo 0 ≤ tau P 0 (j + 1)
    rw [εB_b B T 0 (Nat.zero_le _) j, tau_srcS]
    have := B.H_D 0 (by omega); omega
  SRC_T0 := by
    show P.R ≤ tau P 0 0 + P.wl 0 ∧ P.wh 0 ≤ tau P 0 0; rw [tau_src0]; exact B.H_T0
  SRC_SEG k _ := segK_of_phases (nodes B T 0 (by omega)) k
  SNK_WAIT j := by
    show (bD P).εF P.N j + P.lo (P.N + 1) ≤ tau P (P.N + 1) j
    rw [εF_b B T P.N (Nat.le_refl _) j, tau_snk]
    have := B.H_D (P.N + 1) (by omega); omega
  SNK_SEG k _ := segK_of_phases (nodes B T (P.N + 1) (Nat.le_refl _)) k

/-- **The schedule in closed max-plus form**: source `T0`, then each source edge is the
acknowledge edge plus wire plus its own delay; each link edge is the later of its request
arrival and (from `j = 1`) its acknowledge arrival, plus its LUT delay; the sink follows its
request. -/
theorem schedule :
    tau P 0 0 = P.T0 ∧
    (∀ j, tau P 0 (j + 1) = tau P 1 j + P.v 0 + P.d 0) ∧
    (∀ m, m < P.N → ∀ j, tau P (m + 1) j =
      max (tau P m j + P.w m) (ash P.R (fun k => tau P (m + 2) k + P.v (m + 1)) j) +
        P.d (m + 1)) ∧
    (∀ j, tau P (P.N + 1) j = tau P P.N j + P.w P.N + P.d (P.N + 1)) := by
  refine ⟨tau_src0 P, fun j => ?_, fun m hm j => ?_, fun j => ?_⟩
  · rw [tau_srcS, εB_c B T 0 (Nat.zero_le _) j]
  · rw [tau_cph B T m hm j]
    unfold cph ChainData.ρL ChainData.αL
    rw [εF_c B T m (by omega) j]
    cases j with
    | zero => rfl
    | succ k => show _ = max _ (tau P (m + 2) k + P.v (m + 1)) + _
                rw [← εB_c B T (m + 1) (by omega) k]; rfl
  · rw [tau_snk, εF_c B T P.N (Nat.le_refl _) j]

end band

/-! ## Headline theorems -/

/-- **Existence of solutions of the chain's edge-time equations, every `N`.** For every
chain length `N`, every assignment of realised constant delays inside the bands
(`Band`: LUTs `d i ∈ [lo i, hi i]`, feedback `f ∈ [fl, fh]`, wires `w ∈ [wl, wh]`,
`v ∈ [vl, vh]`, `lo, wl, vl ≥ 1`, source start `T0` with `R ≤ T0 + wl 0`, `wh 0 ≤ T0`) that
satisfies the timing rows `ChainT` on the BANDS, the run `nd P` (real `bd_c2n` INIT, each
gate a transport delay of its realised value) with the edge times `tau P` satisfies EVERY
field of `Chain` (gate relations of the bands, H_TIMES, both end contracts) and `ChainT`,
and the edge times are the max-plus schedule. -/
theorem chain_solution (P : Dly) (B : Band P) (T : ChainT (bD P)) :
    Chain (bD P) ∧ ChainT (bD P) ∧
    tau P 0 0 = P.T0 ∧
    (∀ j, tau P 0 (j + 1) = tau P 1 j + P.v 0 + P.d 0) ∧
    (∀ m, m < P.N → ∀ j, tau P (m + 1) j =
      max (tau P m j + P.w m) (ash P.R (fun k => tau P (m + 2) k + P.v (m + 1)) j) +
        P.d (m + 1)) ∧
    (∀ j, tau P (P.N + 1) j = tau P P.N j + P.w P.N + P.d (P.N + 1)) :=
  ⟨chain_b B T, T, schedule B T⟩

/-- **The same, as an existence statement over `ChainData`**: the chain with the given
bands has a solution of `Chain`/`ChainT` (traces and edge times). -/
theorem chain_exists (P : Dly) (B : Band P) (T : ChainT (bD P)) :
    ∃ D : ChainData, D.N = P.N ∧ D.R = P.R ∧ D.lo = P.lo ∧ D.hi = P.hi ∧ D.fl = P.fl ∧
      D.fh = P.fh ∧ D.wl = P.wl ∧ D.wh = P.wh ∧ D.vl = P.vl ∧ D.vh = P.vh ∧
      Chain D ∧ ChainT D :=
  ⟨bD P, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, chain_b B T, T⟩

/-- **`chain_env1` is non-vacuous for every such delay assignment**: every link of the run
has B's `Env1` and `Timing1` with the derived slacks. -/
theorem chain_env1_solution (P : Dly) (B : Band P) (T : ChainT (bD P)) (m : Nat)
    (hm : m < P.N) :
    Env1 (rq P (m + 1)) (ak P (m + 1)) (rs P) (nd P (m + 1)) (P.lo (m + 1)) (P.hi (m + 1))
      P.R ((bD P).ρL m) ((bD P).αL m) ((bD P).Es m) ((bD P).Ea m) ∧
    Timing1 (P.lo (m + 1)) (P.hi (m + 1)) (P.fh (m + 1)) P.R ((bD P).Es m) ((bD P).Ea m) :=
  chain_env1 (chain_b B T) T m hm

/-! ## Non-vacuity of `chain_solution`: non-uniform delays strictly inside wide bands -/

/-- Witness: LUT band `[1, 3]`, realised LUT delays `1 + i % 3` (all three values occur),
feedback and wires 1, reset 4. -/
def wP (N : Nat) : Dly where
  N := N
  R := 4
  T0 := 4
  lo _ := 1
  hi _ := 3
  fl _ := 1
  fh _ := 1
  wl _ := 1
  wh _ := 1
  vl _ := 1
  vh _ := 1
  d i := 1 + i % 3
  f _ := 1
  w _ := 1
  v _ := 1

theorem wP_band (N : Nat) : Band (wP N) where
  H_D i _ := by show 1 ≤ 1 + i % 3 ∧ 1 + i % 3 ≤ 3; omega
  H_F _ _ := ⟨Nat.le_refl 1, Nat.le_refl 1⟩
  H_W _ _ := ⟨Nat.le_refl 1, Nat.le_refl 1⟩
  H_V _ _ := ⟨Nat.le_refl 1, Nat.le_refl 1⟩
  H_LUT_POS _ _ := Nat.le_refl 1
  H_WIRE_POS _ _ := ⟨Nat.le_refl 1, Nat.le_refl 1⟩
  H_T0 := by show 4 ≤ 4 + 1 ∧ 1 ≤ 4; decide

theorem wP_T (N : Nat) : ChainT (bD (wP N)) where
  H_RST_LONG _ _ := by show 3 + 1 ≤ 4; decide
  H_LAT _ _ := by show 3 + 1 ≤ 1 + min (1 + 1 + 1) (1 + 1 + 1); decide
  H_WIRE_R _ _ := by show 1 ≤ 4 ∧ 1 ≤ 4; decide
  H_RT _ _ := by show 1 ≤ 1 + 1 + 1 + 1 ∧ 1 ≤ 1 + 1 + 1 + 1; decide

/-- **Non-vacuity, every `N`**: the hypotheses of `chain_solution` hold jointly, with
H_LAT met with equality on the bands, and with realised delays at the low end, inside and
at the high end of the LUT band. -/
theorem chain_solution_witness (N : Nat) :
    Band (wP N) ∧ ChainT (bD (wP N)) ∧
    (∀ m, (bD (wP N)).hi (m + 1) + (bD (wP N)).fh (m + 1) =
      (bD (wP N)).lo (m + 1) + min ((bD (wP N)).Es m) ((bD (wP N)).Ea m)) ∧
    (wP N).d 0 = 1 ∧ (wP N).d 1 = 2 ∧ (wP N).d 2 = 3 :=
  ⟨wP_band N, wP_T N, fun _ => rfl, rfl, rfl, rfl⟩

end Formal.Cells.EdgeTimes
