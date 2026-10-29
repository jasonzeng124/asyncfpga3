-- Bsa5 mutant M05 of Formal/Cells/Necessity6PipeSel.lean: one change, a_false at slack 0 (claim0 is the shipped theorem). Expected: FAIL.
import Formal.Cells.PipePerPin

/-!
# Necessity6PipeSel: the per-pin `H_RST_SEL` terms of `bd_pipe.rst_lines`

Probe Bnx6 (shard B). Bsx3 and Bnx5 showed every PipeTimedN (lumped) term of
the row `bd_pipe.rst_lines` necessary at the boundary; the row stayed
`sufficient` because its representative form, the per-pin startup obligation
`H_RST_SEL` of `PipePerPin.TimingP` (probe 6g), had no necessity result:

    H_RST_SEL i :  (a) R0 + pr.hi ≤ R + ps.lo              request select flushed at release
                   (b) out.hi + wh + pq.hi ≤ R + ps.lo     loop flushed at release
                   (c) R + ps.hi ≤ ρ 0 + pr.lo             released before the first request
                   (d) R0 + pa.hi ≤ ρ 0 + pr.lo            ack select flushed by then

## Result

* `TimingS P wh Es Er sa sb sc sd`: `TimingP` with term (a) weakened by
  `sa`, (b) by `sb`, (c) by `sc`, (d) by `sd`; every other field verbatim.
  `Claim sa sb sc sd`: `PipePerPin.nodes_clean`'s conclusion (every node low
  from `out.hi` to its first edge, then `Vph j` on `[τ i j, τ i (j+1))`) from
  `GatesP + EnvP + TimingS`. `claim0 : Claim 0 0 0 0` is the shipped theorem.
* Four counter-runs, `N = 1`, unit output map and feedback wire, every pin
  a fixed transport delay, real `bd_c2n` INIT (`CtlP`, every gate relation
  for all `t`), open-loop four-phase environment; in each, ONE term is off by
  exactly one, the other three and every other field of `TimingS`, `GatesP`,
  `EnvP` hold, and the conclusion fails:
  - `a_false : ¬ Claim 1 0 0 0`: request pin 4 ticks, request garbage 1
    before `R0` (allowed: `EnvP` constrains `r 0` only from `R0`). The stale
    1 reaches the request select at 5, when reset has just released there:
    the node rises at 6, before its first edge `τ 0 0 = 12`.
  - `b_false : ¬ Claim 0 1 0 0`: feedback pin 4 ticks, node power-up value
    1 at `t = 0` (allowed: `CtlP` constrains the node only from `out.hi`).
    The stale feedback reaches its select at 5: the node rises at 6, before
    `τ 0 0 = 9`.
  - `c_false : ¬ Claim 0 0 1 0`: reset pin 5 ticks. The first request reaches
    its select at 8 while the reset select still reads 1: the node rises at
    10, not at `τ 0 0 = 9` (it is 0 at 9 inside `[9, 17)`). A one-tick delay,
    not a corruption; the event-time conclusion is false.
  - `d_false : ¬ Claim 0 0 0 1`: `R0 = R = 4`, first request at 4, ack pin
    2 ticks. `τ 0 0 = 7` is computed from the ack select's flush at
    `R0 + pa = 6`; the acknowledge pin happens to read 0 before `R0` as well
    (allowed), so the node rises at 6, one tick BEFORE `τ 0 0`. Also not a
    corruption; the conclusion is false.

So every term of H_RST_SEL is **necessary at the boundary** (one parameter
point per term, binary `≤` form) for `nodes_clean` as stated. With Bsx3 / Bnx5
this covers every term of `bd_pipe.rst_lines`. Terms (a), (b) protect against
a real early fire from power-up garbage; (c), (d) protect only the derived
event times (a one-tick shift, either way).

## Which form

These refute the Lean `≤` forms at slack 1. The JSON row carries a strict
`+1` on the two loop terms (`out.hi + wh + pq.hi + 1 ≤ R + ps.lo` and the
lumped loop term): for (b) the refuted point is 2 ticks from the JSON form;
(a), (c), (d) are not strict in the JSON, so the JSON and Lean forms agree
there.

## Assumed / proved / NOT covered

Assumed: PipePerPin's model (H_PIN_FIFO per-pin site-pin maps, H_TREE_FIFO
output map, window feedback wire, `rst` an exact step at its pin), N = 1.
Proved: as above.
NOT covered: N ≥ 2 (the boundary lines' `H_FLUSH` terms are vacuous here);
an iff over the box; Kleene X at the selects.
-/

namespace Formal.Cells.Necessity6PipeSel
open Formal.Cells Formal.Cells.PipeTimed Formal.Cells.PipePerPin

/-- `TimingP` with the four H_RST_SEL terms weakened by `sa sb sc sd`. -/
structure TimingS (P : PP) (wh : Nat → Nat) (Es Er sa sb sc sd : Nat) : Prop where
  H_N_POS : 1 ≤ P.N
  H_R0_POS : 1 ≤ P.R0
  H_R0_LE : P.R0 ≤ P.R
  H_RST_SEL : ∀ i, i < P.N →
    P.R0 + (P.pr i).hi ≤ P.R + (P.ps i).lo + sa ∧
    (P.out i).hi + wh i + (P.pq i).hi ≤ P.R + (P.ps i).lo + sb ∧
    P.R + (P.ps i).hi ≤ P.ρ 0 + (P.pr i).lo + sc ∧
    P.R0 + (P.pa i).hi ≤ P.ρ 0 + (P.pr i).lo + sd
  H_FLUSH : ∀ i, i + 1 < P.N →
    (P.out i).hi + (P.Rq (i + 1)).hi ≤ P.R0 ∧ (P.out (i + 1)).hi + P.ahi (i + 1) ≤ P.R0 ∧
    P.Ag (i + 1) ≤ P.R0
  H_SELORD : ∀ i, i < P.N →
    wh i + (P.pq i).hi ≤ P.ER Es i + (P.pr i).lo ∧ wh i + (P.pq i).hi ≤ P.EA Er i + (P.pa i).lo
  H_ACK_FLUSH : ∀ i, i + 1 < P.N →
    P.ahi (i + 1) ≤ P.Won Es Er (i + 1) + P.alo (i + 1)

theorem timingP_of {P : PP} {wh : Nat → Nat} {Es Er : Nat} (T : TimingS P wh Es Er 0 0 0 0) :
    TimingP P wh Es Er :=
  ⟨T.H_N_POS, T.H_R0_POS, T.H_R0_LE, fun i hi => by
    have := T.H_RST_SEL i hi; simp only [Nat.add_zero] at this; exact this,
    T.H_FLUSH, T.H_SELORD, T.H_ACK_FLUSH⟩

/-- `nodes_clean`'s conclusion for every stage. -/
def Concl (P : PP) (O : Nat → Trace) : Prop :=
  ∀ i, i < P.N → (∀ t, (P.out i).hi ≤ t → t < P.τ i 0 → O i t = false) ∧
    (∀ j t, P.τ i j ≤ t → t < P.τ i (j + 1) → O i t = Vph j)

def Claim (sa sb sc sd : Nat) : Prop :=
  ∀ (P : PP) (rst : Trace) (r a O q : Nat → Trace) (wl wh : Nat → Nat) (Es Er : Nat),
    GatesP P rst r a O q wl wh → EnvP P (r 0) (a (P.N - 1)) Es Er →
    TimingS P wh Es Er sa sb sc sd → Concl P O

theorem claim0 : Claim 0 0 0 0 := by
  intro P rst r a O q wl wh Es Er G E T i hi
  exact nodes_clean G E (timingP_of T) i hi

/-! ## The runs: one stage, fixed pin delays, square-wave environment -/
namespace Runs
open Formal.Cells.PipePerPin.Wit (sq8 sq8_pre sq8_phase fstd)

/-- One stage: request pin `p`, acknowledge pin `a`, feedback pin `qd`,
reset pin `s` ticks; output map and feedback wire 1 tick; first request at
`ρo`, receiver's first edge at `γo`, phases of 8 ticks. -/
def Q (R R0 p a qd s ρo γo : Nat) : PP where
  N := 1
  R := R
  R0 := R0
  pr _ := Ret.shift p
  pa _ := Ret.shift a
  pq _ := Ret.shift qd
  ps _ := Ret.shift s
  out _ := Ret.shift 1
  Rq _ := Ret.shift 1
  m _ := 0
  Ap _ _ := Ret.shift 1
  Ag _ := 1
  ρ j := ρo + 8 * j
  γ j := γo + 8 * j

theorem τ0 (R R0 p a qd s ρo γo : Nat) (h1 : 1 ≤ ρo) (h2 : 1 ≤ R0) :
    (Q R R0 p a qd s ρo γo).τ 0 0 = max (ρo + p) (R0 + a) + 1 := by
  show (Ret.shift 1).fst (max ((Ret.shift p).fst ρo) ((Ret.shift a).fst R0)) = _
  rw [fstd p ρo h1, fstd a R0 h2, fstd 1 _ (by omega)]

theorem τS (R R0 p a qd s ρo γo j : Nat) (h1 : 1 ≤ ρo) (h2 : 1 ≤ γo) :
    (Q R R0 p a qd s ρo γo).τ 0 (j + 1) = max (ρo + 8 * (j + 1) + p) (γo + 8 * j + a) + 1 := by
  show (Ret.shift 1).fst (max ((Ret.shift p).fst (ρo + 8 * (j + 1))) ((Ret.shift a).fst (γo + 8 * j))) = _
  rw [fstd p _ (by omega), fstd a _ (by omega), fstd 1 _ (by omega)]

def rst (t : Nat) : Bool := decide (t < 4)
def c2n (a b q r : Bool) : Bool := CElemTiming.exc CElemTiming.INIT_c2n a b q r

/-- The four-phase environment (square waves), plus power-up garbage. -/
theorem sq_env (o : Nat) : ∀ j t, o + 8 * j ≤ t → t < o + 8 * (j + 1) → sq8 o t = Vph j :=
  fun j t h1 h2 => sq8_phase o j t h1 h2

/-! ### (a) request select not flushed at release: `R0 + pr.hi = R + ps.lo + 1` -/
abbrev Pa : PP := Q 4 2 4 2 3 1 7 16
/-- The request pin carries power-up garbage 1 before `R0 = 2`. -/
def ra (t : Nat) : Bool := decide (t < 2) || sq8 7 t
def aa (t : Nat) : Bool := sq8 16 t
/-- The node: `O t = c2n (r (t-1-4)) (a (t-1-2)) (q (t-1-3)) (rst (t-1-1))`, `q t = O (t-1)`. -/
def Oa : Nat → Bool
  | t + 5 => c2n (ra t) (aa (t + 2)) (Oa t) (rst (t + 3))
  | _ => false

theorem gates_a : GatesP Pa rst (fun _ => ra) (fun _ => aa) (fun _ => Oa) (fun _ t => Oa (t - 1))
    (fun _ => 1) (fun _ => 1) where
  H_RST _ := rfl
  H_CTL i hi := by
    have : i = 0 := by have : i < 1 := hi; omega
    subst this
    exact {
    H_OUT := fun t ht => by
      match t, ht with
      | 1, _ => decide
      | 2, _ => decide
      | 3, _ => decide
      | 4, _ => decide
      | t + 5, _ => rfl
    H_FB := fun t ht => ⟨t - 1, by omega, by omega, rfl⟩
    H_LOOP_POS := by decide }
  H_REQ_LINE i h := by have : i + 1 < 1 := h; omega
  H_ACK_LINE i h := by have : i + 1 < 1 := h; omega

theorem env_a : EnvP Pa ra aa 3 4 where
  H_REQ_LOW0 t h1 h2 := by
    have h1 : 2 ≤ t := h1; have h2 : t < 7 + 8 * 0 := h2
    have e : decide (t < 2) = false := decide_eq_false (by omega)
    show (decide (t < 2) || sq8 7 t) = false
    rw [e, sq8_pre 7 t (by omega)]; rfl
  H_REQ j t h1 h2 := by
    have h1' : 7 + 8 * j ≤ t := h1
    have e : decide (t < 2) = false := decide_eq_false (by omega)
    show (decide (t < 2) || sq8 7 t) = Vph j
    rw [e, sq_env 7 j t h1 h2]; rfl
  H_ACK_LOW0 t _ h2 := sq8_pre 16 t (by have h2 : t < 16 + 8 * 0 := h2; omega)
  H_ACK j t h1 h2 := sq_env 16 j t h1 h2
  H_SND j := by
    cases j with
    | zero => rw [τ0 _ _ _ _ _ _ _ _ (by omega) (by omega)]; show 12 + 3 ≤ 7 + 8 * 1; omega
    | succ j => rw [τS _ _ _ _ _ _ _ _ _ (by omega) (by omega)]; show _ ≤ 7 + 8 * (j + 1 + 1); omega
  H_RCV j := by
    show Pa.τ 0 j + 4 ≤ 16 + 8 * j
    cases j with
    | zero => rw [τ0 _ _ _ _ _ _ _ _ (by omega) (by omega)]; omega
    | succ j => rw [τS _ _ _ _ _ _ _ _ _ (by omega) (by omega)]; omega
  H_RST_EARLY := by show 4 ≤ 7 + 8 * 0; omega

theorem timing_a : TimingS Pa (fun _ => 1) 3 4 1 0 0 0 where
  H_N_POS := by decide
  H_R0_POS := by decide
  H_R0_LE := by decide
  H_RST_SEL _ _ := by
    show 2 + 4 ≤ 4 + 1 + 1 ∧ 1 + 1 + 3 ≤ 4 + 1 + 0 ∧ 4 + 1 ≤ 7 + 8 * 0 + 4 + 0 ∧ 2 + 2 ≤ 7 + 8 * 0 + 4 + 0
    omega
  H_FLUSH i h := by have : i + 1 < 1 := h; omega
  H_SELORD i hi := by
    have : i = 0 := by have : i < 1 := hi; omega
    subst this; exact ⟨by decide, by decide⟩
  H_ACK_FLUSH i h := by have : i + 1 < 1 := h; omega

/-- (a)'s term is off by exactly one; the stale request fires the node at 6. -/
theorem a_viol : ¬ (Pa.R0 + (Pa.pr 0).hi ≤ Pa.R + (Pa.ps 0).lo) ∧
    Pa.R0 + (Pa.pr 0).hi = Pa.R + (Pa.ps 0).lo + 1 ∧ Pa.τ 0 0 = 12 ∧ Oa 5 = false ∧ Oa 6 = true := by
  refine ⟨by decide, by decide, by rw [τ0 _ _ _ _ _ _ _ _ (by omega) (by omega)] <;> decide, by decide, by decide⟩

theorem a_false : ¬ Claim 0 0 0 0 := by
  intro h
  have := (h Pa rst _ _ _ _ _ _ 3 4 gates_a env_a timing_a 0 (by decide)).1 6 (by decide)
    (by have := a_viol.2.2.1; omega)
  rw [a_viol.2.2.2.2] at this; exact absurd this (by decide)

/-! ### (b) loop not flushed at release: `out.hi + wh + pq.hi = R + ps.lo + 1` -/
abbrev Pb : PP := Q 4 2 1 2 4 1 7 13
def rb (t : Nat) : Bool := sq8 7 t
def ab (t : Nat) : Bool := sq8 13 t
/-- The node, power-up value 1 at `t = 0`: `O t = c2n (r (t-2)) (a (t-3)) (q (t-5)) (rst (t-2))`. -/
def Ob : Nat → Bool
  | 0 => true
  | t + 6 => c2n (rb (t + 4)) (ab (t + 3)) (Ob t) (rst (t + 4))
  | _ => false

theorem gates_b : GatesP Pb rst (fun _ => rb) (fun _ => ab) (fun _ => Ob) (fun _ t => Ob (t - 1))
    (fun _ => 1) (fun _ => 1) where
  H_RST _ := rfl
  H_CTL i hi := by
    have : i = 0 := by have : i < 1 := hi; omega
    subst this
    exact {
    H_OUT := fun t ht => by
      match t, ht with
      | 1, _ => decide
      | 2, _ => decide
      | 3, _ => decide
      | 4, _ => decide
      | 5, _ => decide
      | t + 6, _ => rfl
    H_FB := fun t ht => ⟨t - 1, by omega, by omega, rfl⟩
    H_LOOP_POS := by decide }
  H_REQ_LINE i h := by have : i + 1 < 1 := h; omega
  H_ACK_LINE i h := by have : i + 1 < 1 := h; omega

theorem env_b : EnvP Pb rb ab 6 4 where
  H_REQ_LOW0 t _ h2 := sq8_pre 7 t (by have h2 : t < 7 + 8 * 0 := h2; omega)
  H_REQ j t h1 h2 := sq_env 7 j t h1 h2
  H_ACK_LOW0 t _ h2 := sq8_pre 13 t (by have h2 : t < 13 + 8 * 0 := h2; omega)
  H_ACK j t h1 h2 := sq_env 13 j t h1 h2
  H_SND j := by
    cases j with
    | zero => rw [τ0 _ _ _ _ _ _ _ _ (by omega) (by omega)]; show 9 + 6 ≤ 7 + 8 * 1; omega
    | succ j => rw [τS _ _ _ _ _ _ _ _ _ (by omega) (by omega)]; show _ ≤ 7 + 8 * (j + 1 + 1); omega
  H_RCV j := by
    show Pb.τ 0 j + 4 ≤ 13 + 8 * j
    cases j with
    | zero => rw [τ0 _ _ _ _ _ _ _ _ (by omega) (by omega)]; omega
    | succ j => rw [τS _ _ _ _ _ _ _ _ _ (by omega) (by omega)]; omega
  H_RST_EARLY := by show 4 ≤ 7 + 8 * 0; omega

theorem timing_b : TimingS Pb (fun _ => 1) 6 4 0 1 0 0 where
  H_N_POS := by decide
  H_R0_POS := by decide
  H_R0_LE := by decide
  H_RST_SEL _ _ := by
    show 2 + 1 ≤ 4 + 1 + 0 ∧ 1 + 1 + 4 ≤ 4 + 1 + 1 ∧ 4 + 1 ≤ 7 + 8 * 0 + 1 + 0 ∧ 2 + 2 ≤ 7 + 8 * 0 + 1 + 0
    omega
  H_FLUSH i h := by have : i + 1 < 1 := h; omega
  H_SELORD i hi := by
    have : i = 0 := by have : i < 1 := hi; omega
    subst this; exact ⟨by decide, by decide⟩
  H_ACK_FLUSH i h := by have : i + 1 < 1 := h; omega

/-- (b)'s term is off by exactly one; the stale feedback fires the node at 6. -/
theorem b_viol : ¬ ((Pb.out 0).hi + 1 + (Pb.pq 0).hi ≤ Pb.R + (Pb.ps 0).lo) ∧
    (Pb.out 0).hi + 1 + (Pb.pq 0).hi = Pb.R + (Pb.ps 0).lo + 1 ∧ Pb.τ 0 0 = 9 ∧
    Ob 5 = false ∧ Ob 6 = true := by
  refine ⟨by decide, by decide, by rw [τ0 _ _ _ _ _ _ _ _ (by omega) (by omega)] <;> decide, by decide, by decide⟩

theorem b_false : ¬ Claim 0 1 0 0 := by
  intro h
  have := (h Pb rst _ _ _ _ _ _ 6 4 gates_b env_b timing_b 0 (by decide)).1 6 (by decide)
    (by have := b_viol.2.2.1; omega)
  rw [b_viol.2.2.2.2] at this; exact absurd this (by decide)

/-! ### (c) reset not released at its select before the first request:
`R + ps.hi = ρ 0 + pr.lo + 1` -/
abbrev Pc : PP := Q 4 2 1 2 3 5 7 13
/-- The node: `O t = c2n (r (t-2)) (a (t-3)) (q (t-4)) (rst (t-6))`. -/
def Oc : Nat → Bool
  | t + 5 => c2n (rb (t + 3)) (ab (t + 2)) (Oc t) (rst (t - 1))
  | _ => false

theorem gates_c : GatesP Pc rst (fun _ => rb) (fun _ => ab) (fun _ => Oc) (fun _ t => Oc (t - 1))
    (fun _ => 1) (fun _ => 1) where
  H_RST _ := rfl
  H_CTL i hi := by
    have : i = 0 := by have : i < 1 := hi; omega
    subst this
    exact {
    H_OUT := fun t ht => by
      match t, ht with
      | 1, _ => decide
      | 2, _ => decide
      | 3, _ => decide
      | 4, _ => decide
      | t + 5, _ => rfl
    H_FB := fun t ht => ⟨t - 1, by omega, by omega, rfl⟩
    H_LOOP_POS := by decide }
  H_REQ_LINE i h := by have : i + 1 < 1 := h; omega
  H_ACK_LINE i h := by have : i + 1 < 1 := h; omega

theorem env_c : EnvP Pc rb ab 6 4 where
  H_REQ_LOW0 t _ h2 := sq8_pre 7 t (by have h2 : t < 7 + 8 * 0 := h2; omega)
  H_REQ j t h1 h2 := sq_env 7 j t h1 h2
  H_ACK_LOW0 t _ h2 := sq8_pre 13 t (by have h2 : t < 13 + 8 * 0 := h2; omega)
  H_ACK j t h1 h2 := sq_env 13 j t h1 h2
  H_SND j := by
    cases j with
    | zero => rw [τ0 _ _ _ _ _ _ _ _ (by omega) (by omega)]; show 9 + 6 ≤ 7 + 8 * 1; omega
    | succ j => rw [τS _ _ _ _ _ _ _ _ _ (by omega) (by omega)]; show _ ≤ 7 + 8 * (j + 1 + 1); omega
  H_RCV j := by
    show Pc.τ 0 j + 4 ≤ 13 + 8 * j
    cases j with
    | zero => rw [τ0 _ _ _ _ _ _ _ _ (by omega) (by omega)]; omega
    | succ j => rw [τS _ _ _ _ _ _ _ _ _ (by omega) (by omega)]; omega
  H_RST_EARLY := by show 4 ≤ 7 + 8 * 0; omega

theorem timing_c : TimingS Pc (fun _ => 1) 6 4 0 0 1 0 where
  H_N_POS := by decide
  H_R0_POS := by decide
  H_R0_LE := by decide
  H_RST_SEL _ _ := by
    show 2 + 1 ≤ 4 + 5 + 0 ∧ 1 + 1 + 3 ≤ 4 + 5 + 0 ∧ 4 + 5 ≤ 7 + 8 * 0 + 1 + 1 ∧ 2 + 2 ≤ 7 + 8 * 0 + 1 + 0
    omega
  H_FLUSH i h := by have : i + 1 < 1 := h; omega
  H_SELORD i hi := by
    have : i = 0 := by have : i < 1 := hi; omega
    subst this; exact ⟨by decide, by decide⟩
  H_ACK_FLUSH i h := by have : i + 1 < 1 := h; omega

/-- (c)'s term is off by exactly one; the node rises one tick late (0 at
`τ 0 0 = 9`, 1 from 10). -/
theorem c_viol : ¬ (Pc.R + (Pc.ps 0).hi ≤ Pc.ρ 0 + (Pc.pr 0).lo) ∧
    Pc.R + (Pc.ps 0).hi = Pc.ρ 0 + (Pc.pr 0).lo + 1 ∧ Pc.τ 0 0 = 9 ∧ Pc.τ 0 1 = 17 ∧
    Oc 9 = false ∧ Oc 10 = true := by
  refine ⟨by decide, by decide, by rw [τ0 _ _ _ _ _ _ _ _ (by omega) (by omega)] <;> decide,
    by rw [τS _ _ _ _ _ _ _ _ 0 (by omega) (by omega)] <;> decide, by decide, by decide⟩

theorem c_false : ¬ Claim 0 0 1 0 := by
  intro h
  have := (h Pc rst _ _ _ _ _ _ 6 4 gates_c env_c timing_c 0 (by decide)).2 0 9
    (by have := c_viol.2.2.1; omega) (by show 9 < Pc.τ 0 1; have := c_viol.2.2.2.1; omega)
  rw [c_viol.2.2.2.2.1] at this; exact absurd this (by decide)

/-! ### (d) ack select not flushed by the first request:
`R0 + pa.hi = ρ 0 + pr.lo + 1` -/
abbrev Pd : PP := Q 4 4 1 2 3 1 4 10
def rd (t : Nat) : Bool := sq8 4 t
def ad (t : Nat) : Bool := sq8 10 t
/-- The node: `O t = c2n (r (t-2)) (a (t-3)) (q (t-5)) (rst (t-2))`. -/
def Od : Nat → Bool
  | t + 5 => c2n (rd (t + 3)) (ad (t + 2)) (Od t) (rst (t + 3))
  | _ => false

theorem gates_d : GatesP Pd rst (fun _ => rd) (fun _ => ad) (fun _ => Od) (fun _ t => Od (t - 1))
    (fun _ => 1) (fun _ => 1) where
  H_RST _ := rfl
  H_CTL i hi := by
    have : i = 0 := by have : i < 1 := hi; omega
    subst this
    exact {
    H_OUT := fun t ht => by
      match t, ht with
      | 1, _ => decide
      | 2, _ => decide
      | 3, _ => decide
      | 4, _ => decide
      | t + 5, _ => rfl
    H_FB := fun t ht => ⟨t - 1, by omega, by omega, rfl⟩
    H_LOOP_POS := by decide }
  H_REQ_LINE i h := by have : i + 1 < 1 := h; omega
  H_ACK_LINE i h := by have : i + 1 < 1 := h; omega

theorem env_d : EnvP Pd rd ad 5 3 where
  H_REQ_LOW0 t h1 h2 := by
    have h1 : 4 ≤ t := h1; have h2 : t < 4 + 8 * 0 := h2; omega
  H_REQ j t h1 h2 := sq_env 4 j t h1 h2
  H_ACK_LOW0 t _ h2 := sq8_pre 10 t (by have h2 : t < 10 + 8 * 0 := h2; omega)
  H_ACK j t h1 h2 := sq_env 10 j t h1 h2
  H_SND j := by
    cases j with
    | zero => rw [τ0 _ _ _ _ _ _ _ _ (by omega) (by omega)]; show 7 + 5 ≤ 4 + 8 * 1; omega
    | succ j => rw [τS _ _ _ _ _ _ _ _ _ (by omega) (by omega)]; show _ ≤ 4 + 8 * (j + 1 + 1); omega
  H_RCV j := by
    show Pd.τ 0 j + 3 ≤ 10 + 8 * j
    cases j with
    | zero => rw [τ0 _ _ _ _ _ _ _ _ (by omega) (by omega)]; omega
    | succ j => rw [τS _ _ _ _ _ _ _ _ _ (by omega) (by omega)]; omega
  H_RST_EARLY := by show 4 ≤ 4 + 8 * 0; omega

theorem timing_d : TimingS Pd (fun _ => 1) 5 3 0 0 0 1 where
  H_N_POS := by decide
  H_R0_POS := by decide
  H_R0_LE := by decide
  H_RST_SEL _ _ := by
    show 4 + 1 ≤ 4 + 1 + 0 ∧ 1 + 1 + 3 ≤ 4 + 1 + 0 ∧ 4 + 1 ≤ 4 + 8 * 0 + 1 + 0 ∧ 4 + 2 ≤ 4 + 8 * 0 + 1 + 1
    omega
  H_FLUSH i h := by have : i + 1 < 1 := h; omega
  H_SELORD i hi := by
    have : i = 0 := by have : i < 1 := hi; omega
    subst this; exact ⟨by decide, by decide⟩
  H_ACK_FLUSH i h := by have : i + 1 < 1 := h; omega

/-- (d)'s term is off by exactly one; `τ 0 0 = 7` (from the ack select's
flush at `R0 + pa = 6`), but the node rises at 6. -/
theorem d_viol : ¬ (Pd.R0 + (Pd.pa 0).hi ≤ Pd.ρ 0 + (Pd.pr 0).lo) ∧
    Pd.R0 + (Pd.pa 0).hi = Pd.ρ 0 + (Pd.pr 0).lo + 1 ∧ Pd.τ 0 0 = 7 ∧ Od 5 = false ∧ Od 6 = true := by
  refine ⟨by decide, by decide, by rw [τ0 _ _ _ _ _ _ _ _ (by omega) (by omega)] <;> decide, by decide, by decide⟩

theorem d_false : ¬ Claim 0 0 0 1 := by
  intro h
  have := (h Pd rst _ _ _ _ _ _ 5 3 gates_d env_d timing_d 0 (by decide)).1 6 (by decide)
    (by have := d_viol.2.2.1; omega)
  rw [d_viol.2.2.2.2] at this; exact absurd this (by decide)

end Runs

/-- **Every H_RST_SEL term is necessary at the boundary** (binary `≤`, one
point each, N = 1): the shipped claim holds, and weakening any ONE of the
four terms by one tick, the other three and every other hypothesis kept,
is unsound. -/
theorem rst_sel_boundary :
    Claim 0 0 0 0 ∧ ¬ Claim 1 0 0 0 ∧ ¬ Claim 0 1 0 0 ∧ ¬ Claim 0 0 1 0 ∧ ¬ Claim 0 0 0 1 :=
  ⟨claim0, Runs.a_false, Runs.b_false, Runs.c_false, Runs.d_false⟩

end Formal.Cells.Necessity6PipeSel
