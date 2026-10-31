import Formal.Cells.PipeTimedN

/-!
# Necessity3PipeCtl: `bd_pipe` H_LAT, H_RST_LONG, H_RST_LINES(req) are tight

Probe Bsx3 (shard B). Rows `bd_pipe.lat_lumped` (H_LAT) and
`bd_pipe.rst_lines` (H_RST_LONG, H_RST_LINES) were "sufficient". Their
theorem is `PipeTimedN.pipe_ctl` / `nodes_clean` (FIFO controllers with the
real `bd_c2n` INIT `00B2..`, feedback wire a window channel `[wl, wh]`,
FIFO request lines, DACK OR lines, open-loop sender/receiver).

`CtlClaim sLat sLong sLn` is `nodes_clean` with H_LAT weakened by `sLat`,
H_RST_LONG by `sLong` and the request-line term of H_RST_LINES
(`L i .hi + Rq (i+1) .hi ≤ R`) by `sLn` (`TimingS`, a verbatim copy of
`TimingN` with those slacks; `GatesN`, `EnvN` and every other field verbatim).

* `ctl0 : CtlClaim 0 0 0` is the shipped theorem.
* `lat_false : ¬ CtlClaim 1 0 0`, `long_false : ¬ CtlClaim 0 1 0`,
  `lines_false : ¬ CtlClaim 0 0 1`.

Counter-runs (controller arc 1 = one corner, every relation for ALL t):

* **RLat** (`N = 1`, feedback window `[1, 3]`): the sender drops its request
  exactly `Es = 2` after the node's rise, the receiver acknowledges `Er = 3`
  after it, so `L.hi + wh = 4 = L.lo + min Es Er + 1`. At 7 the request is
  low, the acknowledge not yet high, and the feedback pin still shows the node
  as it was at 4 (inside the window): the C-element's hold reads 0, and the
  node drops for one tick at 8 inside its high phase `[5, 9)`.
* **RLong** (`N = 1`, window `[1, 3]`): reset released at `R = 3`,
  `L.hi + wh = 4 = R + 1`; H_LAT holds with equality. At 3 the feedback pin
  still shows the node's power-up value (instant 0, before the LUT relation
  is in force, here 1): the node rises at 4, before its first edge 5.
* **RLines** (`N = 2`, the unit run of `PipeTimedN.Wit` with boundary 1's
  request line a FIFO channel of window `[1, 4]`): see section RLines.

The feedback pins avoid the stray values afterwards, so each run is otherwise
the nominal one. One parameter point per row. The JSON forms' extra +1 (Bs,
Kleene X window) is not this binary run.

Not covered: the DACK and guard terms of H_RST_LINES (`L(b).hi + ahi b ≤ R`,
`Ag b ≤ R`: a stray ack at release delays stage b-1's first rise and the
deviation propagates; no closed-form run built), H_RST_SEL (PipePerPin's
per-pin model), H_ACK_FLUSH (FASTRISE `ack_flush`).

Core Lean only.
-/

namespace Formal.Cells.Necessity3PipeCtl
open Formal.Cells Formal.Cells.PipeTimed Formal.Cells.PipeTimedN

/-- `TimingN` with H_LAT and H_RST_LONG weakened by `sLat`, `sLong`. -/
structure TimingS (P : PN) (wh : Nat → Nat) (Es Er sLat sLong sLn : Nat) : Prop where
  H_N_POS : 1 ≤ P.N
  H_R_POS : 1 ≤ P.R
  H_RST_LONG : ∀ i, i < P.N → (P.L i).hi + wh i ≤ P.R + sLong
  H_RST_LINES : ∀ i, i + 1 < P.N →
    (P.L i).hi + (P.Rq (i + 1)).hi ≤ P.R + sLn ∧ (P.L (i + 1)).hi + P.ahi (i + 1) ≤ P.R ∧
    P.Ag (i + 1) ≤ P.R
  H_LAT : ∀ i, i < P.N →
    (P.L i).hi + wh i ≤ (P.L i).lo + min (P.ER Es i) (P.EA Er i) + sLat
  H_ACK_FLUSH : ∀ i, i + 1 < P.N →
    P.ahi (i + 1) ≤ (P.L (i + 1)).lo + max (P.ER Es (i + 1)) (P.EA Er (i + 1)) + P.alo (i + 1)

theorem TimingS.toN {P : PN} {wh : Nat → Nat} {Es Er : Nat} (T : TimingS P wh Es Er 0 0 0) :
    TimingN P wh Es Er where
  H_N_POS := T.H_N_POS
  H_R_POS := T.H_R_POS
  H_RST_LONG i h := by have := T.H_RST_LONG i h; omega
  H_RST_LINES i h := by have := T.H_RST_LINES i h; omega
  H_LAT i h := by have := T.H_LAT i h; omega
  H_ACK_FLUSH := T.H_ACK_FLUSH

/-- `nodes_clean` with H_LAT / H_RST_LONG / H_RST_LINES (request-line term) weakened. -/
def CtlClaim (sLat sLong sLn : Nat) : Prop :=
  ∀ (P : PN) (rst : Trace) (r a O q : Nat → Trace) (wl wh : Nat → Nat) (Es Er : Nat),
    GatesN P rst r a O q wl wh → EnvN P (r 0) (a (P.N - 1)) Es Er → TimingS P wh Es Er sLat sLong sLn →
    ∀ i, i < P.N →
      (∀ t, (P.L i).hi ≤ t → t < P.τ i 0 → O i t = false) ∧
      (∀ j t, P.τ i j ≤ t → t < P.τ i (j + 1) → O i t = Vph j)

theorem ctl0 : CtlClaim 0 0 0 := by
  intro P rst r a O q wl wh Es Er G E T i hi
  exact nodes_clean G E T.toN i hi

/-! ## One-stage runs -/

/-- One stage, controller arc 1, reset released at `R`, request edges `ρ`,
acknowledge edges `8 + 4j`. -/
def P1 (R : Nat) (ρ : Nat → Nat) : PN where
  N := 1
  R := R
  L _ := Ret.shift 1
  Rq _ := Ret.shift 1
  m _ := 0
  Ap _ _ := Ret.shift 1
  Ag _ := 1
  ρ := ρ
  γ j := 8 + 4 * j

/-- The event times: `c 0 j = 4 + 4j`, `τ 0 j = 5 + 4j`, whenever
`ρ 0 = 4`, `R ≤ 4` and `ρ (j+1) ≤ 8 + 4j`. -/
theorem c1 (R : Nat) (ρ : Nat → Nat) (hR : R ≤ 4) (h0 : ρ 0 = 4) (hs : ∀ j, ρ (j + 1) ≤ 8 + 4 * j)
    (j : Nat) : (P1 R ρ).c 0 j = 4 + 4 * j := by
  cases j with
  | zero => show max (ρ 0) R = 4 + 4 * 0; omega
  | succ j =>
    show max (ρ (j + 1)) (if 0 + 1 < 1 then _ else 8 + 4 * j) = 4 + 4 * (j + 1)
    have := hs j; simp; omega

theorem τ1 (R : Nat) (ρ : Nat → Nat) (hR : R ≤ 4) (h0 : ρ 0 = 4) (hs : ∀ j, ρ (j + 1) ≤ 8 + 4 * j)
    (j : Nat) : (P1 R ρ).τ 0 j = 5 + 4 * j := by
  show (Ret.shift 1).fst ((P1 R ρ).c 0 j) = _
  rw [c1 R ρ hR h0 hs, Ret.fst_shift 1 _ (by omega)]; omega

/-! ## Run RLat: H_LAT off by one -/

def ρL (j : Nat) : Nat := 4 + 4 * j - j % 2
def rL (t : Nat) : Bool := decide (4 ≤ t ∧ (t - 4) % 8 < 3)
def aL (t : Nat) : Bool := Wit.sq 8 t
def OL (t : Nat) : Bool := Wit.sq 5 t && decide (t ≠ 8)
def qL (t : Nat) : Bool := Wit.sq 6 t && decide (t ≠ 7)
def rstL (t : Nat) : Bool := decide (t < 4)

theorem lut_L (t : Nat) (ht : 1 ≤ t) :
    OL t = ex rL aL qL rstL ((Ret.shift 1).σ t) := by
  show OL t = CElemTiming.exc CElemTiming.INIT_c2n (rL (t - 1)) (aL (t - 1)) (qL (t - 1)) (rstL (t - 1))
  rw [CElemTiming.c2n_eq]
  simp only [OL, rL, aL, qL, rstL, Wit.sq]
  rw [Bool.eq_iff_iff]; simp; omega

theorem fb_L : CElemTiming.WinDelay 1 3 OL qL := by
  intro t ht
  by_cases h7 : t = 7
  · subst h7; exact ⟨4, by omega, by omega, by decide⟩
  by_cases h9 : t = 9
  · subst h9; exact ⟨7, by omega, by omega, by decide⟩
  refine ⟨t - 1, by omega, by omega, ?_⟩
  simp only [OL, qL, Wit.sq]
  rw [Bool.eq_iff_iff]; simp; omega

theorem gates_L : GatesN (P1 4 ρL) rstL (fun _ => rL) (fun _ => aL) (fun _ => OL) (fun _ => qL)
    (fun _ => 1) (fun _ => 3) where
  H_RST _ := rfl
  H_CTL _ _ := { H_LUT_FIFO := lut_L, H_FB := fb_L, H_LOOP_POS := by show 1 ≤ 1 + 1; decide }
  H_REQ_LINE i h := absurd h (by simp [P1])
  H_ACK_LINE i h := absurd h (by simp [P1])

theorem ρL_ok : ρL 0 = 4 ∧ ∀ j, ρL (j + 1) ≤ 8 + 4 * j :=
  ⟨rfl, fun j => by unfold ρL; omega⟩

theorem τL (j : Nat) : (P1 4 ρL).τ 0 j = 5 + 4 * j := τ1 4 ρL (by omega) ρL_ok.1 ρL_ok.2 j

theorem env_L : EnvN (P1 4 ρL) rL aL 2 3 where
  H_REQ_LOW0 t h1 h2 := by simp [P1, ρL] at h1 h2; omega
  H_REQ j t h1 h2 := by
    simp only [P1, ρL] at h1 h2
    simp only [rL, Vph, LinkTimed.Vph]; rw [Bool.eq_iff_iff]; simp; omega
  H_ACK_LOW0 t h1 h2 := Wit.sq_pre 8 t (by simpa [P1] using h2)
  H_ACK j t h1 h2 := Wit.sq_phase 8 j t (by simpa [P1] using h1) (by simp [P1] at h2; omega)
  H_SND j := by rw [τL]; show 5 + 4 * j + 2 ≤ ρL (j + 1); unfold ρL; omega
  H_RCV j := by
    show (P1 4 ρL).τ 0 j + 3 ≤ 8 + 4 * j
    rw [τL]; omega
  H_RST_EARLY := by show 4 ≤ ρL 0; decide

/-- H_LAT holds with slack 1, fails without: `1 + 3 = 1 + min 2 3 + 1`. -/
theorem lat_viol : (Ret.shift 1).hi + 3 = (Ret.shift 1).lo + min 2 3 + 1 := rfl

theorem timing_L : TimingS (P1 4 ρL) (fun _ => 3) 2 3 1 0 0 where
  H_N_POS := by decide
  H_R_POS := by decide
  H_RST_LONG _ _ := by show 1 + 3 ≤ 4 + 0; decide
  H_RST_LINES i h := absurd h (by simp [P1])
  H_LAT i h := by
    have : i = 0 := by simp [P1] at h; omega
    subst this; show 1 + 3 ≤ 1 + min 2 3 + 1; decide
  H_ACK_FLUSH i h := absurd h (by simp [P1])

/-- The excitation itself reads 0 at 7, inside phase 0 `[c 0 0, c 0 1) = [4, 8)`. -/
theorem lat_exc : ex rL aL qL rstL 7 = false := by decide

/-- **H_LAT cannot be weakened by 1.** On run RLat the node is low at 8,
inside its high phase `[τ 0 0, τ 0 1) = [5, 9)`. -/
theorem lat_false : ¬ CtlClaim 1 0 0 := by
  intro h
  have := (h _ _ _ _ _ _ _ _ _ _ gates_L env_L timing_L 0 (by decide)).2 0 8
    (by rw [τL]; decide) (by rw [τL]; decide)
  exact absurd this (by decide)

/-! ## Run RLong: H_RST_LONG off by one -/

def ρW (j : Nat) : Nat := 4 + 4 * j
def OR3 (t : Nat) : Bool := Wit.sq 5 t || decide (t = 0) || decide (t = 4)
def qR3 (t : Nat) : Bool := Wit.sq 6 t || decide (t = 3)
def rst3 (t : Nat) : Bool := decide (t < 3)

theorem lut_R (t : Nat) (ht : 1 ≤ t) :
    OR3 t = ex (Wit.sq 4) (Wit.sq 8) qR3 rst3 ((Ret.shift 1).σ t) := by
  show OR3 t = CElemTiming.exc CElemTiming.INIT_c2n (Wit.sq 4 (t - 1)) (Wit.sq 8 (t - 1))
    (qR3 (t - 1)) (rst3 (t - 1))
  rw [CElemTiming.c2n_eq]
  simp only [OR3, qR3, rst3, Wit.sq]
  rw [Bool.eq_iff_iff]; simp; omega

theorem fb_R : CElemTiming.WinDelay 1 3 OR3 qR3 := by
  intro t ht
  by_cases h3 : t = 3
  · subst h3; exact ⟨0, by omega, by omega, by decide⟩
  by_cases h5 : t = 5
  · subst h5; exact ⟨3, by omega, by omega, by decide⟩
  refine ⟨t - 1, by omega, by omega, ?_⟩
  simp only [OR3, qR3, Wit.sq]
  rw [Bool.eq_iff_iff]; simp; omega

theorem gates_R : GatesN (P1 3 ρW) rst3 (fun _ => Wit.sq 4) (fun _ => Wit.sq 8) (fun _ => OR3)
    (fun _ => qR3) (fun _ => 1) (fun _ => 3) where
  H_RST _ := rfl
  H_CTL _ _ := { H_LUT_FIFO := lut_R, H_FB := fb_R, H_LOOP_POS := by show 1 ≤ 1 + 1; decide }
  H_REQ_LINE i h := absurd h (by simp [P1])
  H_ACK_LINE i h := absurd h (by simp [P1])

theorem τR (j : Nat) : (P1 3 ρW).τ 0 j = 5 + 4 * j :=
  τ1 3 ρW (by omega) rfl (fun j => by unfold ρW; omega) j

theorem env_R : EnvN (P1 3 ρW) (Wit.sq 4) (Wit.sq 8) 3 3 where
  H_REQ_LOW0 t h1 h2 := Wit.sq_pre 4 t (by simpa [P1, ρW] using h2)
  H_REQ j t h1 h2 := Wit.sq_phase 4 j t (by simpa [P1, ρW] using h1)
    (by simp [P1, ρW] at h2; omega)
  H_ACK_LOW0 t h1 h2 := Wit.sq_pre 8 t (by simpa [P1] using h2)
  H_ACK j t h1 h2 := Wit.sq_phase 8 j t (by simpa [P1] using h1) (by simp [P1] at h2; omega)
  H_SND j := by rw [τR]; show 5 + 4 * j + 3 ≤ ρW (j + 1); unfold ρW; omega
  H_RCV j := by
    show (P1 3 ρW).τ 0 j + 3 ≤ 8 + 4 * j
    rw [τR]; omega
  H_RST_EARLY := by show 3 ≤ ρW 0; decide

/-- H_RST_LONG holds with slack 1, fails without: `1 + 3 = 3 + 1`; H_LAT
holds with equality: `1 + 3 = 1 + min 3 3`. -/
theorem long_viol : (Ret.shift 1).hi + 3 = 3 + 1 ∧ (Ret.shift 1).hi + 3 = (Ret.shift 1).lo + min 3 3 :=
  ⟨rfl, rfl⟩

theorem timing_R : TimingS (P1 3 ρW) (fun _ => 3) 3 3 0 1 0 where
  H_N_POS := by decide
  H_R_POS := by decide
  H_RST_LONG _ _ := by show 1 + 3 ≤ 3 + 1; decide
  H_RST_LINES i h := absurd h (by simp [P1])
  H_LAT i h := by
    have : i = 0 := by simp [P1] at h; omega
    subst this; show 1 + 3 ≤ 1 + min 3 3 + 0; decide
  H_ACK_FLUSH i h := absurd h (by simp [P1])

/-- The excitation reads 1 at 3, before the first phase start `c 0 0 = 4`. -/
theorem long_exc : ex (Wit.sq 4) (Wit.sq 8) qR3 rst3 3 = true := by decide

/-- **H_RST_LONG cannot be weakened by 1.** On run RLong the node is high at
4, before its first edge `τ 0 0 = 5`. -/
theorem long_false : ¬ CtlClaim 0 1 0 := by
  intro h
  have := (h _ _ _ _ _ _ _ _ _ _ gates_R env_R timing_R 0 (by decide)).1 4
    (by decide) (by rw [τR]; decide)
  exact absurd this (by decide)

/-! ## Run RLines: H_RST_LINES' request-line term off by one (two stages)

The unit-delay two-stage run of `PipeTimedN.Wit` (`R = 4`), except that
boundary 1's request line is a FIFO channel with `lo = 1`, `hi = 4` that
reads stage 0's node at instant 0 until 4 and is a 1-tick delay after
(`RqG`). Then `L 0 .hi + Rq 1 .hi = 5 = R + 1`. Stage 0's node is 1 at
instant 0 (power-up value: the LUT relation holds from `L.hi = 1` on). So
stage 1's request pin is 1 at 4, right at release, and stage 1's node
rises at 5, before its first edge `τ 1 0 = 7`. Everything else is the
nominal run: the stray ack pulse it sends back (stage 0's I1 at 6) is masked
because stage 0 is already high (`r && q`), and stage 1's own feedback sees
its stray 1 at 6, when its request is up anyway. Derived event times are
the nominal ones (`ccq`), since `RqG.fst c = c + 1` for `c ≥ 4`. -/

def RqG : Ret where
  σ t := if t ≤ 4 then 0 else t - 1
  lo := 1
  hi := 4
  mono a b h := by split <;> split <;> omega
  ge t := by split <;> omega
  le t := by split <;> omega

theorem fstG (c : Nat) (hc : 4 ≤ c) : RqG.fst c = c + 1 := by
  have h1 := Ret.fst_lo RqG (c := c) (by omega)
  have h2 : RqG.fst c ≤ c + 1 := by
    apply Classical.byContradiction; intro h
    have := Ret.fst_before RqG (c := c) (t := c + 1) (by omega)
    simp only [RqG] at this; split at this <;> omega
  have : RqG.lo = 1 := rfl
  omega

def Pq : PN where
  N := 2
  R := 4
  L _ := Ret.shift 1
  Rq _ := RqG
  m _ := 0
  Ap _ _ := Ret.shift 1
  Ag _ := 1
  ρ j := 4 + 4 * j
  γ j := 10 + 4 * j

theorem fst1 (c : Nat) (h : 1 ≤ c) : (Ret.shift 1).fst c = c + 1 := Ret.fst_shift 1 c h

theorem ackT_q (b j τ : Nat) (h : 1 ≤ τ) : Pq.ackT b j τ = τ + 1 := by
  show (if j % 2 = 0 then (Ret.shift 1).fst τ else (Ret.shift 1).fst τ) = _
  rw [fst1 τ h]; split <;> rfl

theorem ccq (j : Nat) : Pq.cc j 0 = 4 + 4 * j ∧ Pq.cc j 1 = 6 + 4 * j := by
  induction j with
  | zero =>
    have e0 : Pq.cc 0 0 = 4 := rfl
    refine ⟨e0, ?_⟩
    show max (RqG.fst ((Ret.shift 1).fst (Pq.cc 0 0))) 4 = 6 + 4 * 0
    rw [e0, fst1 4 (by omega), fstG 5 (by omega)]; rfl
  | succ j ih =>
    have e0 : Pq.cc (j + 1) 0 = 4 + 4 * (j + 1) := by
      show max (4 + 4 * (j + 1)) (if 0 + 1 < 2 then Pq.ackT 1 j ((Ret.shift 1).fst (Pq.cc j 1))
        else 10 + 4 * j) = _
      rw [ih.2, fst1 _ (by omega), ackT_q _ _ _ (by omega)]; simp; omega
    refine ⟨e0, ?_⟩
    show max (RqG.fst ((Ret.shift 1).fst (Pq.cc (j + 1) 0)))
      (if 1 + 1 < 2 then Pq.ackT 2 j ((Ret.shift 1).fst (Pq.cc j 2)) else 10 + 4 * j) = _
    rw [e0, fst1 _ (by omega), fstG _ (by omega)]; simp; omega

theorem τq0 (j : Nat) : Pq.τ 0 j = 5 + 4 * j := by
  show (Ret.shift 1).fst (Pq.cc j 0) = _
  rw [(ccq j).1, fst1 _ (by omega)]; omega
theorem τq1 (j : Nat) : Pq.τ 1 j = 7 + 4 * j := by
  show (Ret.shift 1).fst (Pq.cc j 1) = _
  rw [(ccq j).2, fst1 _ (by omega)]; omega

open Wit in
def O0q (t : Nat) : Bool := sq 5 t || decide (t = 0)
open Wit in
def q0q (t : Nat) : Bool := sq 6 t || decide (t = 1)
open Wit in
def a0q (t : Nat) : Bool := sq 8 t || decide (t = 6)
open Wit in
def r1q (t : Nat) : Bool := sq 6 t || decide (t = 4)
open Wit in
def O1q (t : Nat) : Bool := sq 7 t || decide (t = 5)
open Wit in
def q1q (t : Nat) : Bool := sq 8 t || decide (t = 6)

def rq : Nat → Trace | 0 => Wit.sq 4 | _ => r1q
def aq : Nat → Trace | 0 => a0q | _ => Wit.sq 10
def Oq : Nat → Trace | 0 => O0q | _ => O1q
def qq : Nat → Trace | 0 => q0q | _ => q1q

theorem ctl0q : Ctl (Wit.sq 4) a0q Wit.rstW O0q q0q (Ret.shift 1) 1 1 where
  H_LUT_FIFO t ht := by
    have ht' : 1 ≤ t := ht
    show O0q t = CElemTiming.exc CElemTiming.INIT_c2n (Wit.sq 4 (t - 1)) (a0q (t - 1))
      (q0q (t - 1)) (Wit.rstW (t - 1))
    rw [CElemTiming.c2n_eq]
    simp only [O0q, q0q, a0q, Wit.rstW, Wit.sq]
    rw [Bool.eq_iff_iff]; simp; first | omega | (constructor <;> intro h <;> omega)
  H_FB t ht := ⟨t - 1, by omega, by omega, by
    simp only [O0q, q0q, Wit.sq]; rw [Bool.eq_iff_iff]; simp; first | omega | (constructor <;> intro h <;> omega)⟩
  H_LOOP_POS := by show 1 ≤ 1 + 1; decide

theorem ctl1q : Ctl r1q (Wit.sq 10) Wit.rstW O1q q1q (Ret.shift 1) 1 1 where
  H_LUT_FIFO t ht := by
    have ht' : 1 ≤ t := ht
    show O1q t = CElemTiming.exc CElemTiming.INIT_c2n (r1q (t - 1)) (Wit.sq 10 (t - 1))
      (q1q (t - 1)) (Wit.rstW (t - 1))
    rw [CElemTiming.c2n_eq]
    simp only [O1q, q1q, r1q, Wit.rstW, Wit.sq]
    rw [Bool.eq_iff_iff]; simp; first | omega | (constructor <;> intro h <;> omega)
  H_FB t ht := ⟨t - 1, by omega, by omega, by
    simp only [O1q, q1q, Wit.sq]; rw [Bool.eq_iff_iff]; simp; first | omega | (constructor <;> intro h <;> omega)⟩
  H_LOOP_POS := by show 1 ≤ 1 + 1; decide

theorem gates_q : GatesN Pq Wit.rstW rq aq Oq qq (fun _ => 1) (fun _ => 1) where
  H_RST _ := rfl
  H_CTL i hi := by
    match i, hi with
    | 0, _ => exact ctl0q
    | 1, _ => exact ctl1q
  H_REQ_LINE i hi t ht := by
    have : i = 0 := by simp [Pq] at hi; omega
    subst this
    show r1q t = O0q (if t ≤ 4 then 0 else t - 1)
    have ht' : 4 ≤ t := ht
    simp only [r1q, O0q, Wit.sq]; split <;> (rw [Bool.eq_iff_iff]; simp; first | omega | (constructor <;> intro h <;> omega))
  H_ACK_LINE i hi t ht := by
    have : i = 0 := by simp [Pq] at hi; omega
    subst this
    show a0q t = O1q (t - 1)
    simp only [a0q, O1q, Wit.sq]; rw [Bool.eq_iff_iff]; simp; first | omega | (constructor <;> intro h <;> omega)

theorem env_q : EnvN Pq (rq 0) (aq (Pq.N - 1)) 3 3 where
  H_REQ_LOW0 t h1 h2 := by simp only [Pq] at h1 h2; omega
  H_REQ j t h1 h2 := Wit.sq_phase 4 j t h1 (by simp only [Pq] at h2; omega)
  H_ACK_LOW0 t h1 h2 := Wit.sq_pre 10 t (by simpa [Pq] using h2)
  H_ACK j t h1 h2 := Wit.sq_phase 10 j t (by simpa [Pq] using h1) (by simp [Pq] at h2; omega)
  H_SND j := by rw [τq0]; show 5 + 4 * j + 3 ≤ 4 + 4 * (j + 1); omega
  H_RCV j := by
    show Pq.τ 1 j + 3 ≤ 10 + 4 * j
    rw [τq1]; omega
  H_RST_EARLY := by show 4 ≤ 4 + 4 * 0; omega

/-- The request-line term holds with slack 1 and fails by exactly 1:
`L 0 .hi + Rq 1 .hi = 1 + 4 = R + 1`; the DACK and guard terms hold. -/
theorem lines_viol : (Pq.L 0).hi + (Pq.Rq 1).hi = Pq.R + 1 := rfl

theorem timing_q : TimingS Pq (fun _ => 1) 3 3 0 0 1 where
  H_N_POS := by decide
  H_R_POS := by decide
  H_RST_LONG _ _ := by show 1 + 1 ≤ 4 + 0; decide
  H_RST_LINES i h := by
    have : i = 0 := by simp [Pq] at h; omega
    subst this
    show 1 + 4 ≤ 4 + 1 ∧ 1 + Pq.ahi 1 ≤ 4 ∧ 1 ≤ 4
    have : Pq.ahi 1 = 1 := rfl
    rw [this]; decide
  H_LAT i h := by
    have hi : i = 0 ∨ i = 1 := by simp [Pq] at h; omega
    rcases hi with rfl | rfl
    · show 1 + 1 ≤ 1 + min 3 (1 + 1 + 1) + 0; decide
    · show 1 + 1 ≤ 1 + min (1 + 1 + 1) 3 + 0; decide
  H_ACK_FLUSH i h := by
    have : i = 0 := by simp [Pq] at h; omega
    subst this
    show 1 ≤ 1 + max (1 + 1 + 1) 3 + 1; decide

/-- Stage 1's excitation reads 1 at 4, before its first phase start `c 1 0 = 6`. -/
theorem lines_exc : ex r1q (Wit.sq 10) q1q Wit.rstW 4 = true := by decide

/-- **The request-line flush term cannot be weakened by 1.** On run RLines
stage 1's node is high at 5, before its first edge `τ 1 0 = 7`. -/
theorem lines_false : ¬ CtlClaim 0 0 1 := by
  intro h
  have := (h _ _ _ _ _ _ _ _ _ _ gates_q env_q timing_q 1 (by decide)).1 5
    (by decide) (by rw [τq1]; decide)
  exact absurd this (by decide)

/-! Non-vacuity at slack 0: `PipeTimedN.Wit.witness`. -/

end Formal.Cells.Necessity3PipeCtl
