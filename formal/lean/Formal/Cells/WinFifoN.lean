import Formal.Cells.WinFifoCausal
import Formal.Cells.PipeTimedN

/-!
# Probe Bex2: Win request and acknowledge LINES, any number of stages

Probe Bex (`WinFifoCausal`) put the two controller LUTs of the 2-stage pipe on
shard A's window channel `Win` (plus `H_NO_REVERT`) but kept the request line
and the OR-of-copies acknowledge line FIFO. This file

* makes EVERY channel of the `N`-stage pipe (`PipeTimedN`) a `Win` channel:
  the `N` controller LUTs (`Stage`, as in Bex), the `N - 1` request lines, and
  the `m b + 1` copies whose OR is boundary `b`'s acknowledge pin. Every
  event time is read off a trace (`nt`): node edges off the nodes, request
  edges off the request pins, acknowledge edges off the copies;
* states the no-revert property a LINE needs (`NoRevertFrom R`: Bex's
  intrinsic form, for input stretches that start after reset release), and
  answers the wire question (section 5): a routed wire in the digital model
  is a pure delay line `y t = x (t - d t)`, `d t ∈ [lo, hi]`, which IS `Win`
  (`delay_line_iff_win`), so Win alone lets a wire glitch
  (`WinFifo.win_glitch_not_fifo`); no-revert is NOT a consequence of `Win`.
  It IS a consequence of `Win` + monotone read (`t - d t` nondecreasing,
  i.e. FIFO) on a clean input that the wire delivers before the input's
  next edge (`H_CATCH`, `wire_noRevert`), with no spacing condition; the
  handshake loop guarantees `H_CATCH` by causality. Monotone read composes
  along a buffer chain (`PipeTimed.fifo_comp`);
* proves PipeTimedN's control theorems on the all-Win pipe directly
  (`pipe_ctl_w`, `nodes_clean_w`, `pins_clean_w`), and lifts the run to a
  `PipeTimedN.PN` with FIFO maps for every LUT and line whose derived event
  times are the traces' (`lift`), so every PipeTimedN theorem (data path
  `token`, `pipe_forward` included) applies (`pipe_forward_w`);
* non-vacuity for every `N ≥ 1` with every LUT and line delay STRICTLY
  inside its band (`Wn.witness`: LUTs, lines and copies at 2 ticks in
  `[1, 3]`), and the counter-run for the line hypothesis (`Wg.line_nr_needed`:
  one in-zone glitch on an acknowledge copy, masked from the excitation, so
  every other hypothesis holds; the acknowledge pin is then not clean).
* FIFO is a special case for the lines: in every PipeTimedN run the FIFO
  request lines and acknowledge copies satisfy `H_REQ_WIN`/`H_REQ_NR` and
  `H_AP_WIN`/`H_AP_NR` (`fifo_req_nr`, `fifo_copy_nr`). The one timing
  change is `H_ACK_FLUSH_W`, one tick stricter than 6e's `H_ACK_FLUSH`.

Core Lean only.
-/

namespace Formal.Cells.WinFifoN
open Formal.Cells
open Formal.Cells.PipeTimed (Ret Trace ex Ctl Vph lfind lfind_le lfind_spec lfind_min Vph_succ
  Vph_even Vph_odd)
open Formal.Cells.WinFifo (Win Clean Spread win_le)
open Formal.Cells.WinFifoCausal (NoRevertI nt nt_lo nt_before lfind_eq node_win exc_phase_w
  exc_pre_w Stage ret_of_clean fst_eq_nt clean_of_phases noRevertI_of_ret not_eq_of_ne)
open Formal.Cells.PipeTimedN (fmin fmax orAll fmin_le_of le_fmin le_fmax_of fmax_le fmin_eq
  fmax_eq orAll_true orAll_false orAll_congr PN GatesN EnvN TimingN)

/-! ## 1. Generic lemmas -/

/-- **H_NO_REVERT for a line** (Bex's `NoRevertI`, restricted to input
stretches that start at or after `g`, the reset release): if the input holds
`v` on `[a, b)` with `a ≥ g`, and the output shows `v` at some
`t1 ≥ a + lo`, it keeps `v` until `b + lo`. -/
def NoRevertFrom (g lo hi : Nat) (x y : Trace) : Prop :=
  ∀ (a b : Nat) (v : Bool) (t1 t2 : Nat), g ≤ a → (∀ s, a ≤ s → s < b → x s = v) →
    hi ≤ t1 → a + lo ≤ t1 → t1 ≤ t2 → t2 < b + lo → y t1 = v → y t2 = v

theorem noRevertFrom_of_I {g lo hi : Nat} {x y : Trace} (h : NoRevertI lo hi x y) :
    NoRevertFrom g lo hi x y :=
  fun a b v t1 t2 _ hx h0 h1 h12 h2 hv => h a b v t1 t2 hx h0 h1 h12 h2 hv

/-- `nt` either finds the value inside the window or is the default `c + hi + 1`. -/
theorem nt_cases (O : Trace) (lo hi c : Nat) (v : Bool) :
    (c + lo ≤ nt O lo hi c v ∧ nt O lo hi c v ≤ c + hi ∧ O (nt O lo hi c v) = v) ∨
      nt O lo hi c v = c + hi + 1 := by
  unfold nt
  by_cases hl : lfind (fun t => decide (c + lo ≤ t) && (O t == v)) (c + hi + 1) < c + hi + 1
  · left
    have := lfind_spec _ _ hl
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact ⟨this.1, by omega, this.2⟩
  · right; have := lfind_le (fun t => decide (c + lo ≤ t) && (O t == v)) (c + hi + 1); omega

theorem nt_ge (O : Trace) (lo hi c : Nat) (v : Bool) : c ≤ nt O lo hi c v := by
  rcases nt_cases O lo hi c v with h | h <;> omega

theorem nt_le1 (O : Trace) (lo hi c : Nat) (v : Bool) : nt O lo hi c v ≤ c + hi + 1 := by
  rcases nt_cases O lo hi c v with h | h <;> omega

/-- **Upper bound of a channel edge.** If the input holds `v` on `[τ, τ')`
and the edge time found is at most `τ' + lo` (in particular under the
spacing `τ + hi < τ' + lo`, or when causality makes the input's next edge
wait for this one), the output edge lies inside the window. -/
theorem nt_hi_of {lo hi τ τ' : Nat} {v : Bool} {x y : Trace} (hW : Win lo hi x y)
    (hx : ∀ s, τ ≤ s → s < τ' → x s = v) (h : nt y lo hi τ v ≤ τ' + lo) :
    nt y lo hi τ v ≤ τ + hi := by
  rcases nt_cases y lo hi τ v with e | e
  · exact e.2.1
  · exfalso
    have hlh := win_le hW
    obtain ⟨s, s1, s2, s3⟩ := hW (τ + hi) (by omega)
    have hv : y (τ + hi) = v := by rw [s3]; exact hx s (by omega) (by omega)
    have := lfind_min (fun t => decide (τ + lo ≤ t) && (y t == v)) (τ + hi + 1) (τ + hi)
      (by unfold nt at e; omega)
    simp only [hv, beq_self_eq_true, Bool.and_true, decide_eq_false_iff_not] at this
    omega

/-- **One phase of a `Win` + no-revert line**: if the input holds `v` on
`[τ, τ')` (with `τ ≥ g`), the output holds `v` from its edge `nt` until
`τ' + lo`. No spacing condition: if the edge is not found inside the
window, the interval is empty. -/
theorem line_hold {lo hi g τ τ' : Nat} {v : Bool} {x y : Trace}
    (hW : Win lo hi x y) (hnr : NoRevertFrom g lo hi x y) (hg : g ≤ τ) (hh : hi ≤ τ + lo)
    (hx : ∀ s, τ ≤ s → s < τ' → x s = v) :
    ∀ t, nt y lo hi τ v ≤ t → t < τ' + lo → y t = v := by
  intro t h1 h2
  have hle := nt_hi_of hW hx (by omega)
  rcases nt_cases y lo hi τ v with e | e
  · exact hnr τ τ' v _ t hg hx (by omega) e.1 h1 h2 e.2.2
  · omega

/-- **A line segment**: input `Vph j` on `[τ, τ')` gives output `Vph j`
between the output's `j`-th and `(j+1)`-th edges. -/
theorem line_seg {lo hi g τ τ' : Nat} {j : Nat} {x y : Trace}
    (hW : Win lo hi x y) (hnr : NoRevertFrom g lo hi x y) (hg : g ≤ τ) (hh : hi ≤ τ + lo)
    (hx : ∀ s, τ ≤ s → s < τ' → x s = Vph j) :
    ∀ t, nt y lo hi τ (Vph j) ≤ t → t < nt y lo hi τ' (Vph (j + 1)) → y t = Vph j := by
  intro t h1 h2
  by_cases h : t < τ' + lo
  · exact line_hold hW hnr hg hh hx t h1 h
  · have := nt_before y lo hi τ' (Vph (j + 1)) t (by omega) h2
    rw [this, Vph_succ, Bool.not_not]

/-- **A line before its first edge**: the input low on `[gx, τ)` gives the
output low on `[gx + hi, nt)`. -/
theorem line_pre {lo hi gx τ : Nat} {x y : Trace} (hW : Win lo hi x y)
    (hx : ∀ s, gx ≤ s → s < τ → x s = false) :
    ∀ t, gx + hi ≤ t → t < nt y lo hi τ true → y t = false := by
  intro t h1 h2
  by_cases h : t < τ + lo
  · obtain ⟨s, s1, s2, s3⟩ := hW t (by omega); rw [s3]; exact hx s (by omega) (by omega)
  · have := nt_before y lo hi τ true t (by omega) h2; simpa using this

/-- OR of copies, low stretch. -/
theorem or_false_of (m : Nat) (Y : Nat → Trace) (A B : Nat → Nat)
    (h : ∀ k, k ≤ m → ∀ t, A k ≤ t → t < B k → Y k t = false) :
    ∀ t, fmax A m ≤ t → t < fmin B m → orAll (fun k => Y k t) m = false := by
  intro t h1 h2
  apply orAll_false
  intro k hk
  have e1 := le_fmax_of A (A k) m k hk (Nat.le_refl _)
  have e2 := fmin_le_of B (B k) m k hk (Nat.le_refl _)
  exact h k hk t (by omega) (by omega)

/-- OR of copies, high stretch, when every copy rises before any falls. -/
theorem or_true_of (m : Nat) (Y : Nat → Trace) (A B : Nat → Nat)
    (h : ∀ k, k ≤ m → ∀ t, A k ≤ t → t < B k → Y k t = true)
    (hov : fmax A m ≤ fmin B m) :
    ∀ t, fmin A m ≤ t → t < fmax B m → orAll (fun k => Y k t) m = true := by
  intro t h1 h2
  by_cases hc : fmax A m ≤ t
  · obtain ⟨k, hk, e⟩ := fmax_eq B m
    have e1 := le_fmax_of A (A k) m k hk (Nat.le_refl _)
    exact orAll_true _ m k hk (h k hk t (by omega) (by omega))
  · obtain ⟨k, hk, e⟩ := fmin_eq A m
    have e2 := fmin_le_of B (B k) m k hk (Nat.le_refl _)
    exact orAll_true _ m k hk (h k hk t (by omega) (by omega))

theorem fmin_congr (f g : Nat → Nat) : ∀ m, (∀ k, k ≤ m → f k = g k) → fmin f m = fmin g m := by
  intro m; induction m with
  | zero => intro h; exact h 0 (Nat.le_refl 0)
  | succ m ih =>
    intro h; show min (fmin f m) (f (m + 1)) = min (fmin g m) (g (m + 1))
    rw [ih (fun k hk => h k (by omega)), h (m + 1) (Nat.le_refl _)]

theorem fmax_congr (f g : Nat → Nat) : ∀ m, (∀ k, k ≤ m → f k = g k) → fmax f m = fmax g m := by
  intro m; induction m with
  | zero => intro h; exact h 0 (Nat.le_refl 0)
  | succ m ih =>
    intro h; show max (fmax f m) (f (m + 1)) = max (fmax g m) (g (m + 1))
    rw [ih (fun k hk => h k (by omega)), h (m + 1) (Nat.le_refl _)]


/-! ## 2. The all-Win `N`-stage pipe: event times read off the traces -/

/-- One run of the `N`-stage pipe with every channel a window channel: the
bands of each LUT, request line and acknowledge copy, the environment's
times, and the traces the edge times are read from (node `O i`, request pin
`r i`, acknowledge copy `Y b k` of boundary `b = i + 1`). -/
structure PW where
  N : Nat
  R : Nat
  /-- stage `i`'s controller LUT band -/
  lo : Nat → Nat
  hi : Nat → Nat
  /-- boundary `b`'s request line band (`O (b-1) → r b`) -/
  qlo : Nat → Nat
  qhi : Nat → Nat
  /-- boundary `b`'s acknowledge pin is the OR of `m b + 1` copies -/
  m : Nat → Nat
  plo : Nat → Nat → Nat
  phi : Nat → Nat → Nat
  /-- guard of the OR relation -/
  Ag : Nat → Nat
  ρ : Nat → Nat
  γ : Nat → Nat
  O : Nat → Trace
  r : Nat → Trace
  Y : Nat → Nat → Trace

namespace PW

/-- Node edge of stage `i` for phase `j` starting at `c`. -/
def tn (W : PW) (i c j : Nat) : Nat := nt (W.O i) (W.lo i) (W.hi i) c (Vph j)
/-- Request-pin edge at boundary `b` for the node edge at `τ`. -/
def rn (W : PW) (b τ j : Nat) : Nat := nt (W.r b) (W.qlo b) (W.qhi b) τ (Vph j)
/-- Copy `k`'s edge at boundary `b` for the node edge at `τ`. -/
def yn (W : PW) (b k τ j : Nat) : Nat := nt (W.Y b k) (W.plo b k) (W.phi b k) τ (Vph j)

/-- Acknowledge pin edge: a rise by the first copy, a fall by the last. -/
def ackT (W : PW) (b j τ : Nat) : Nat :=
  if j % 2 = 0 then fmin (fun k => W.yn b k τ j) (W.m b) else fmax (fun k => W.yn b k τ j) (W.m b)

def row (W : PW) (j : Nat) (α : Nat → Nat) : Nat → Nat
  | 0 => max (W.ρ j) (α 0)
  | i + 1 => max (W.rn (i + 1) (W.tn i (row W j α i) j) j) (α (i + 1))

def ackIn (W : PW) (j : Nat) (τn : Nat → Nat) (i : Nat) : Nat :=
  if i + 1 < W.N then W.ackT (i + 1) j (τn (i + 1)) else W.γ j

def cc (W : PW) : Nat → Nat → Nat
  | 0 => W.row 0 (fun _ => W.R)
  | j + 1 => W.row (j + 1) (W.ackIn j (fun i => W.tn i (cc W j i) j))

def c (W : PW) (i j : Nat) : Nat := W.cc j i
def τ (W : PW) (i j : Nat) : Nat := W.tn i (W.c i j) j
def Rin (W : PW) : Nat → Nat → Nat
  | 0, j => W.ρ j
  | i + 1, j => W.rn (i + 1) (W.τ i j) j
def Ain (W : PW) (i : Nat) : Nat → Nat
  | 0 => W.R
  | j + 1 => W.ackIn j (fun k => W.τ k j) i

def alo (W : PW) (b : Nat) : Nat := fmin (fun k => W.plo b k) (W.m b)
def ahi (W : PW) (b : Nat) : Nat := fmax (fun k => W.phi b k) (W.m b)
def aslow (W : PW) (b : Nat) : Nat := fmax (fun k => W.plo b k) (W.m b)

def ER (W : PW) (Es : Nat) : Nat → Nat
  | 0 => Es
  | i + 1 => W.alo (i + 1) + W.lo i + W.qlo (i + 1)
def EA (W : PW) (Er : Nat) (i : Nat) : Nat :=
  if i + 1 < W.N then W.qlo (i + 1) + W.lo (i + 1) + W.alo (i + 1) else Er
def Won (W : PW) (Es Er i : Nat) : Nat := W.lo i + max (W.ER Es i) (W.EA Er i)

theorem c_eq (W : PW) (i j : Nat) : W.c i j = max (W.Rin i j) (W.Ain i j) := by
  cases i <;> cases j <;> rfl

theorem Ain_in (W : PW) (i j : Nat) (h : i + 1 < W.N) :
    W.Ain i (j + 1) = W.ackT (i + 1) j (W.τ (i + 1) j) := by
  simp only [Ain, ackIn, h, ite_true]

theorem Ain_last (W : PW) (i j : Nat) (h : ¬ i + 1 < W.N) : W.Ain i (j + 1) = W.γ j := by
  simp only [Ain, ackIn, h, ite_false]

theorem EA_in (W : PW) (Er i : Nat) (h : i + 1 < W.N) :
    W.EA Er i = W.qlo (i + 1) + W.lo (i + 1) + W.alo (i + 1) := by simp only [EA, h, ite_true]

theorem EA_last (W : PW) (Er i : Nat) (h : ¬ i + 1 < W.N) : W.EA Er i = Er := by
  simp only [EA, h, ite_false]

theorem ackT_ge' (W : PW) (b j τ : Nat) : τ ≤ W.ackT b j τ := by
  unfold ackT; split
  · exact le_fmin _ _ _ (fun k _ => nt_ge _ _ _ _ _)
  · exact le_fmax_of _ _ _ 0 (Nat.zero_le _) (nt_ge _ _ _ _ _)

end PW

/-- **Gate relations, every channel a window channel.** `a i`, `q i`:
stage `i`'s acknowledge and feedback pins (`W.r i`, `W.O i` are in `W`). -/
structure GatesNW (W : PW) (rst : Trace) (a q : Nat → Trace) (wl wh : Nat → Nat) : Prop where
  H_RST : ∀ t, rst t = decide (t < W.R)
  /-- **H_ST i**: controller LUT `Win` + H_NO_REVERT (Bex's `Stage`, real `bd_c2n`). -/
  H_ST : ∀ i, i < W.N → Stage (W.r i) (a i) rst (W.O i) (q i) (W.lo i) (W.hi i) (wl i) (wh i)
  /-- **H_REQ_WIN b**: boundary `b`'s request line is a window channel. -/
  H_REQ_WIN : ∀ i, i + 1 < W.N → Win (W.qlo (i + 1)) (W.qhi (i + 1)) (W.O i) (W.r (i + 1))
  /-- **H_REQ_NR b**: and does not revert inside an edge's zone (after reset release). -/
  H_REQ_NR : ∀ i, i + 1 < W.N → NoRevertFrom W.R (W.qlo (i + 1)) (W.qhi (i + 1)) (W.O i) (W.r (i + 1))
  /-- **H_AP_WIN b k**: each acknowledge copy is a window channel of stage `b`'s node. -/
  H_AP_WIN : ∀ i, i + 1 < W.N → ∀ k, k ≤ W.m (i + 1) →
    Win (W.plo (i + 1) k) (W.phi (i + 1) k) (W.O (i + 1)) (W.Y (i + 1) k)
  /-- **H_AP_NR b k** -/
  H_AP_NR : ∀ i, i + 1 < W.N → ∀ k, k ≤ W.m (i + 1) →
    NoRevertFrom W.R (W.plo (i + 1) k) (W.phi (i + 1) k) (W.O (i + 1)) (W.Y (i + 1) k)
  /-- **H_ACK_LINE b**: stage `b-1`'s acknowledge pin is the OR of the copies. -/
  H_ACK_LINE : ∀ i, i + 1 < W.N → ∀ t, W.Ag (i + 1) ≤ t →
    a i t = orAll (fun k => W.Y (i + 1) k t) (W.m (i + 1))

/-- **Environment**, as `PipeTimedN.EnvN`, departures measured from the
node edges read off the traces. -/
structure EnvNW (W : PW) (aN : Trace) (Es Er : Nat) : Prop where
  H_REQ_LOW0 : ∀ t, W.R ≤ t → t < W.ρ 0 → W.r 0 t = false
  H_REQ : ∀ j t, W.ρ j ≤ t → t < W.ρ (j + 1) → W.r 0 t = Vph j
  H_ACK_LOW0 : ∀ t, W.R ≤ t → t < W.γ 0 → aN t = false
  H_ACK : ∀ j t, W.γ j ≤ t → t < W.γ (j + 1) → aN t = Vph j
  H_SND : ∀ j, W.τ 0 j + Es ≤ W.ρ (j + 1)
  H_RCV : ∀ j, W.τ (W.N - 1) j + Er ≤ W.γ j
  H_RST_EARLY : W.R ≤ W.ρ 0

/-- **Timing**, as `PipeTimedN.TimingN` with the window bands; the only
change is `H_ACK_FLUSH_W`, one tick stricter than 6e's `H_ACK_FLUSH`. -/
structure TimingNW (W : PW) (wh : Nat → Nat) (Es Er : Nat) : Prop where
  H_N_POS : 1 ≤ W.N
  H_R_POS : 1 ≤ W.R
  H_RST_LONG : ∀ i, i < W.N → W.hi i + wh i ≤ W.R
  H_RST_LINES : ∀ i, i + 1 < W.N →
    W.hi i + W.qhi (i + 1) ≤ W.R ∧ W.hi (i + 1) + W.ahi (i + 1) ≤ W.R ∧ W.Ag (i + 1) ≤ W.R
  H_LAT : ∀ i, i < W.N → W.hi i + wh i ≤ W.lo i + min (W.ER Es i) (W.EA Er i)
  /-- **H_ACK_FLUSH_W b**: every acknowledge copy's spread is below stage
  `b`'s node spacing `Won b` (so no copy can swallow a node phase), with the
  fastest copy's credit. Implies 6e's `H_ACK_FLUSH`. -/
  H_ACK_FLUSH_W : ∀ i, i + 1 < W.N → W.ahi (i + 1) < W.Won Es Er (i + 1) + W.alo (i + 1)

/-! ## 3. Derived timing (as PipeTimedN §3) -/

section chain
variable {W : PW} {rst : Trace} {a q : Nat → Trace} {wl wh : Nat → Nat} {Es Er : Nat}
variable (G : GatesNW W rst a q wl wh) (E : EnvNW W (a (W.N - 1)) Es Er) (T : TimingNW W wh Es Er)
include G E T
set_option linter.unusedSectionVars false

theorem lh (i : Nat) (hi : i < W.N) : W.lo i ≤ W.hi i := win_le (G.H_ST i hi).H_LUT_WIN
theorem qlh (i : Nat) (hi : i + 1 < W.N) : W.qlo (i + 1) ≤ W.qhi (i + 1) := win_le (G.H_REQ_WIN i hi)
theorem plh (i : Nat) (hi : i + 1 < W.N) (k : Nat) (hk : k ≤ W.m (i + 1)) :
    W.plo (i + 1) k ≤ W.phi (i + 1) k := win_le (G.H_AP_WIN i hi k hk)
theorem wlh (i : Nat) (hi : i < W.N) : wl i ≤ wh i := by
  obtain ⟨s, h1, h2, _⟩ := (G.H_ST i hi).H_FB (wh i) (Nat.le_refl _); omega

theorem alo_le (i : Nat) (k : Nat) (hk : k ≤ W.m (i + 1)) : W.alo (i + 1) ≤ W.plo (i + 1) k :=
  fmin_le_of _ _ _ k hk (Nat.le_refl _)
theorem phi_le (i : Nat) (k : Nat) (hk : k ≤ W.m (i + 1)) : W.phi (i + 1) k ≤ W.ahi (i + 1) :=
  le_fmax_of _ _ _ k hk (Nat.le_refl _)

theorem yn_lo (i : Nat) (hi : i + 1 < W.N) (k : Nat) (hk : k ≤ W.m (i + 1)) (τ j : Nat) :
    τ + W.plo (i + 1) k ≤ W.yn (i + 1) k τ j := nt_lo _ _ _ (plh G E T i hi k hk)

theorem ackT_ge (i : Nat) (hi : i + 1 < W.N) (j τ : Nat) :
    τ + W.alo (i + 1) ≤ W.ackT (i + 1) j τ := by
  unfold PW.ackT; split
  · exact le_fmin _ _ _ (fun k hk => by
      have := yn_lo G E T i hi k hk τ j; have := alo_le G E T i k hk; omega)
  · exact le_fmax_of _ _ _ 0 (Nat.zero_le _) (by
      have := yn_lo G E T i hi 0 (Nat.zero_le _) τ j; have := alo_le G E T i 0 (Nat.zero_le _)
      omega)

theorem ackT_odd (i : Nat) (hi : i + 1 < W.N) (j τ : Nat) (hj : j % 2 = 1) :
    τ + W.aslow (i + 1) ≤ W.ackT (i + 1) j τ := by
  unfold PW.ackT; simp only [show ¬ (j % 2 = 0) by omega, ite_false]
  obtain ⟨k, hk, e⟩ := fmax_eq (fun k => W.plo (i + 1) k) (W.m (i + 1))
  have := yn_lo G E T i hi k hk τ j
  have := le_fmax_of (fun k => W.yn (i + 1) k τ j) (W.yn (i + 1) k τ j) (W.m (i + 1)) k hk
    (Nat.le_refl _)
  unfold PW.aslow; omega

theorem ge_R : ∀ j i, W.R ≤ W.c i j := by
  intro j
  induction j with
  | zero => intro i; rw [W.c_eq]; simp only [PW.Ain]; omega
  | succ j ih =>
    intro i; rw [W.c_eq]
    by_cases h : i + 1 < W.N
    · rw [W.Ain_in i j h]
      have := W.ackT_ge' (i + 1) j (W.τ (i + 1) j)
      have := nt_ge (W.O (i + 1)) (W.lo (i + 1)) (W.hi (i + 1)) (W.c (i + 1) j) (Vph j)
      have := ih (i + 1); unfold PW.τ PW.tn at *; omega
    · rw [W.Ain_last i j h]
      have := E.H_RCV j
      have := nt_ge (W.O (W.N - 1)) (W.lo (W.N - 1)) (W.hi (W.N - 1)) (W.c (W.N - 1) j) (Vph j)
      have := ih (W.N - 1); unfold PW.τ PW.tn at *; omega

theorem tau_lo (i j : Nat) (hi : i < W.N) : W.c i j + W.lo i ≤ W.τ i j :=
  nt_lo _ _ _ (lh G E T i hi)

theorem tau_ge (i j : Nat) : W.c i j ≤ W.τ i j := nt_ge _ _ _ _ _

theorem Rin_lo (i j : Nat) (hi : i + 1 < W.N) : W.τ i j + W.qlo (i + 1) ≤ W.Rin (i + 1) j :=
  nt_lo _ _ _ (qlh G E T i hi)

theorem Ain_lo (i j : Nat) (h : i + 1 < W.N) :
    W.τ (i + 1) j + W.alo (i + 1) ≤ W.Ain i (j + 1) := by
  rw [W.Ain_in i j h]; exact ackT_ge G E T i h _ _

theorem depR (i j : Nat) (hi : i < W.N) : W.τ i j + W.ER Es i ≤ W.Rin i (j + 1) := by
  cases i with
  | zero => exact E.H_SND j
  | succ i =>
    have h1 := Rin_lo G E T i (j + 1) hi; have h2 := tau_lo G E T i (j + 1) (by omega)
    have h3 := W.c_eq i (j + 1); have h4 := Ain_lo G E T i j hi
    simp only [PW.ER]; omega

theorem depA (i j : Nat) (hi : i < W.N) : W.τ i j + W.EA Er i ≤ W.Ain i (j + 1) := by
  by_cases h : i + 1 < W.N
  · rw [W.EA_in Er i h]
    have h1 := Ain_lo G E T i j h; have h2 := tau_lo G E T (i + 1) j h
    have h3 := W.c_eq (i + 1) j; have h4 := Rin_lo G E T i j h
    omega
  · rw [W.EA_last Er i h, W.Ain_last i j h]
    have e : i = W.N - 1 := by omega
    subst e; exact E.H_RCV j

theorem dep_c (i j : Nat) (hi : i < W.N) :
    W.c i j + W.lo i + W.ER Es i ≤ W.Rin i (j + 1) ∧
    W.c i j + W.lo i + W.EA Er i ≤ W.Ain i (j + 1) := by
  have := depR G E T i j hi; have := depA G E T i j hi; have := tau_lo G E T i j hi; omega

theorem gap (i j : Nat) (hi : i < W.N) : W.τ i j + W.Won Es Er i ≤ W.τ i (j + 1) := by
  have := depR G E T i j hi; have := depA G E T i j hi; have := tau_lo G E T i (j + 1) hi
  have := W.c_eq i (j + 1); unfold PW.Won; omega

/-- **H_SPREAD_PULSE of each controller's excitation, derived** (H_LAT + H_LOOP_POS). -/
theorem spread (i j : Nat) (hi : i < W.N) : W.c i j + W.hi i < W.c i (j + 1) + W.lo i := by
  have ⟨d1, d2⟩ := dep_c G E T i j hi; have := W.c_eq i (j + 1); have := T.H_LAT i hi
  have := (G.H_ST i hi).H_LOOP_POS; have := wlh G E T i hi; omega

theorem fwd (i j : Nat) (hi : i + 1 < W.N) :
    W.τ i j + W.qlo (i + 1) + W.lo (i + 1) ≤ W.τ (i + 1) j := by
  have := Rin_lo G E T i j hi; have := tau_lo G E T (i + 1) j hi; have := W.c_eq (i + 1) j; omega

theorem back_odd (i j : Nat) (h : i + 1 < W.N) (hj : j % 2 = 1) :
    W.τ (i + 1) j + W.aslow (i + 1) + W.lo i ≤ W.τ i (j + 1) := by
  have h1 := tau_lo G E T i (j + 1) (by omega); have h2 := W.c_eq i (j + 1)
  have h3 := ackT_odd G E T i h j (W.τ (i + 1) j) hj
  rw [W.Ain_in i j h] at h2; omega

/-- **Causality of a request line**: the request pin's `j`-th edge comes
before stage `i`'s next phase starts (the acknowledge it triggers comes back
first). -/
theorem Rin_le_c (i j : Nat) (h : i + 1 < W.N) : W.Rin (i + 1) j ≤ W.c i (j + 1) := by
  have := W.c_eq i (j + 1); rw [W.Ain_in i j h] at this
  have := W.ackT_ge' (i + 1) j (W.τ (i + 1) j); have := tau_ge G E T (i + 1) j
  have := W.c_eq (i + 1) j; omega

theorem live (i j : Nat) (hi : i < W.N) : W.τ i j < W.τ i (j + 1) := by
  have g := gap G E T i j hi; have l := T.H_LAT i hi
  have := (G.H_ST i hi).H_LOOP_POS; have := wlh G E T i hi; unfold PW.Won at g; omega

end chain


/-! ## 4. Every node and pin is clean: the causal induction, all-Win -/

section ctl
variable {W : PW} {rst : Trace} {a q : Nat → Trace} {wl wh : Nat → Nat} {Es Er : Nat}
variable (G : GatesNW W rst a q wl wh) (E : EnvNW W (a (W.N - 1)) Es Er) (T : TimingNW W wh Es Er)
include G E T
set_option linter.unusedSectionVars false

theorem rst_hi : ∀ t, t < W.R → rst t = true := by
  intro t h; rw [G.H_RST]; simp [h]

theorem rst_lo : ∀ t, W.R ≤ t → rst t = false := by
  intro t h; rw [G.H_RST]; simp; omega

theorem node_pre_of (i : Nat) (hi : i < W.N)
    (h : ∀ s, s < W.c i 0 → ex (W.r i) (a i) (q i) rst s = false) :
    ∀ t, W.hi i ≤ t → t < W.τ i 0 → W.O i t = false := by
  intro t t1 t2
  by_cases ht : t < W.c i 0 + W.lo i
  · obtain ⟨s, s1, s2, s3⟩ := (G.H_ST i hi).H_LUT_WIN t t1
    rw [s3]; exact h s (by omega)
  · have := nt_before (W.O i) (W.lo i) (W.hi i) (W.c i 0) (Vph 0) t (by omega) t2
    rw [this, Vph_even 0]; rfl

/-- **Before the first phase, every stage** (Win LUTs, Win request lines). -/
theorem pre : ∀ i, i < W.N →
    (∀ s, s < W.c i 0 → ex (W.r i) (a i) (q i) rst s = false) ∧
    (∀ t, W.hi i ≤ t → t < W.τ i 0 → W.O i t = false) := by
  intro i
  induction i with
  | zero =>
    intro hi
    have hc : W.c 0 0 = W.ρ 0 := by
      rw [W.c_eq]; simp only [PW.Rin, PW.Ain]; have := E.H_RST_EARLY; omega
    have h1 : ∀ s, s < W.c 0 0 → ex (W.r 0) (a 0) (q 0) rst s = false := by
      rw [hc]
      exact exc_pre_w (G.H_ST 0 hi).H_LUT_WIN (G.H_ST 0 hi).H_FB (G.H_ST 0 hi).H_LOOP_POS W.R
        (W.ρ 0) (rst_hi G E T) E.H_REQ_LOW0 (T.H_RST_LONG 0 hi)
    exact ⟨h1, node_pre_of G E T 0 hi h1⟩
  | succ i ih =>
    intro hi
    have hprev := (ih (by omega)).2
    have h1 : ∀ s, s < W.c (i + 1) 0 → ex (W.r (i + 1)) (a (i + 1)) (q (i + 1)) rst s = false := by
      apply exc_pre_w (G.H_ST (i + 1) hi).H_LUT_WIN (G.H_ST (i + 1) hi).H_FB
        (G.H_ST (i + 1) hi).H_LOOP_POS W.R (W.c (i + 1) 0) (rst_hi G E T) _ (T.H_RST_LONG (i + 1) hi)
      intro t t1 t2
      have hc := W.c_eq (i + 1) 0; simp only [PW.Rin, PW.Ain] at hc
      have hr := (T.H_RST_LINES i hi).1
      have := line_pre (G.H_REQ_WIN i hi) hprev t (by omega)
        (by unfold PW.rn at hc; rw [Vph_even 0] at hc; omega)
      exact this
    exact ⟨h1, node_pre_of G E T (i + 1) hi h1⟩

/-- Stage `i`, phase `j`, given clean pins for the phase (`exc_phase_w`). -/
theorem phase_of (i j : Nat) (hi : i < W.N)
    (hreq : ∀ t, W.Rin i j ≤ t → t < W.Rin i (j + 1) → W.r i t = Vph j)
    (hack : ∀ t, W.Ain i j ≤ t → t < W.Ain i (j + 1) → a i t = !Vph j) :
    ∀ s, W.c i j ≤ s → s < W.c i (j + 1) → ex (W.r i) (a i) (q i) rst s = Vph j := by
  have hR := ge_R G E T j i
  have hlat := T.H_LAT i hi
  have ⟨d1, d2⟩ := dep_c G E T i j hi
  have hc := W.c_eq i j
  have hb := T.H_RST_LONG i hi
  have res := exc_phase_w (G.H_ST i hi).H_LUT_WIN (G.H_ST i hi).H_FB (G.H_ST i hi).H_LOOP_POS
    (Vph j) (W.Rin i j) (W.Rin i (j + 1)) (W.Ain i j) (W.Ain i (j + 1))
    (min (W.ER Es i) (W.EA Er i)) hreq hack
    (fun t ht => rst_lo G E T t (by omega)) (by omega) (by omega) hlat (by omega)
  intro s h1 h2
  rw [W.c_eq] at h1 h2; exact res s h1 h2

/-- A stage's node is `Vph j` between its `j`-th and `(j+1)`-th edges
(Bex's `node_win`: `Win` + H_NO_REVERT of the LUT). -/
theorem node_of (i j : Nat) (hi : i < W.N)
    (h : ∀ s, W.c i j ≤ s → s < W.c i (j + 1) → ex (W.r i) (a i) (q i) rst s = Vph j) :
    ∀ t, W.τ i j ≤ t → t < W.τ i (j + 1) → W.O i t = Vph j := by
  have nw := node_win (G.H_ST i hi).H_LUT_WIN (G.H_ST i hi).H_NO_REVERT h
    (by have := ge_R G E T j i; have := T.H_RST_LONG i hi; omega) (spread G E T i j hi)
  intro t t1 t2
  by_cases ht : t < W.c i (j + 1) + W.lo i
  · exact nw.2.2.1 t t1 ht
  · have := nt_before (W.O i) (W.lo i) (W.hi i) (W.c i (j + 1)) (Vph (j + 1)) t (by omega) t2
    rw [this, Vph_succ, Bool.not_not]

/-- Stage `i+1`'s request pin, phase `j`, through the Win request line
(`line_seg`: `Win` + H_REQ_NR, no spacing condition). -/
theorem req_of (i j : Nat) (hi : i + 1 < W.N)
    (h : ∀ s, W.c i j ≤ s → s < W.c i (j + 1) → ex (W.r i) (a i) (q i) rst s = Vph j) :
    ∀ t, W.Rin (i + 1) j ≤ t → t < W.Rin (i + 1) (j + 1) → W.r (i + 1) t = Vph j := by
  have hO := node_of G E T i j (by omega) h
  have := ge_R G E T j i; have := tau_ge G E T i j
  have := (T.H_RST_LINES i hi).1
  exact line_seg (G.H_REQ_WIN i hi) (G.H_REQ_NR i hi) (by omega) (by omega) hO

omit G in
theorem ack_last (j : Nat) :
    ∀ t, W.Ain (W.N - 1) j ≤ t → t < W.Ain (W.N - 1) (j + 1) → a (W.N - 1) t = !Vph j := by
  have hn := T.H_N_POS
  intro t t1 t2
  rw [W.Ain_last _ j (by omega)] at t2
  cases j with
  | zero => simp only [PW.Ain] at t1; rw [E.H_ACK_LOW0 t t1 t2]; rfl
  | succ j =>
    rw [W.Ain_last _ j (by omega)] at t1
    rw [E.H_ACK j t t1 t2, Vph_succ, Bool.not_not]

/-- Stage `i`'s acknowledge pin for phase 0: every copy still low. -/
theorem ack_zero (i : Nat) (hi : i + 1 < W.N) :
    ∀ t, W.Ain i 0 ≤ t → t < W.Ain i 1 → a i t = !Vph 0 := by
  intro t t1 t2
  rw [W.Ain_in i 0 hi] at t2
  simp only [PW.Ain] at t1
  simp only [PW.ackT, show (0 : Nat) % 2 = 0 from rfl, ite_true] at t2
  have hl := T.H_RST_LINES i hi
  have hpre := (pre G E T (i + 1) hi).2
  have f1 := fmax_le (fun k => W.hi (i + 1) + W.phi (i + 1) k) (W.hi (i + 1) + W.ahi (i + 1))
    (W.m (i + 1)) (fun k hk => by have := phi_le G E T i k hk; omega)
  have := or_false_of (W.m (i + 1)) (W.Y (i + 1)) (fun k => W.hi (i + 1) + W.phi (i + 1) k)
    (fun k => W.yn (i + 1) k (W.τ (i + 1) 0) 0)
    (fun k hk t a1 a2 => line_pre (G.H_AP_WIN i hi k hk) hpre t a1
      (by unfold PW.yn at a2; rw [Vph_even 0] at a2; exact a2)) t (by omega) t2
  rw [G.H_ACK_LINE i hi t (by omega), this]; rfl

/-- Stage `i`'s acknowledge pin for phase `j+1`, from stage `i+1`'s phase
`j` through the Win copies (rise: first copy, H_ACK_FLUSH_W keeps every
copy's rise before any copy's fall; fall: last copy). -/
theorem ack_succ (i j : Nat) (hi : i + 1 < W.N)
    (h : ∀ s, W.c (i + 1) j ≤ s → s < W.c (i + 1) (j + 1) →
      ex (W.r (i + 1)) (a (i + 1)) (q (i + 1)) rst s = Vph j) :
    ∀ t, W.Ain i (j + 1) ≤ t → t < W.Ain i (j + 1 + 1) → a i t = !Vph (j + 1) := by
  have hO := node_of G E T (i + 1) j hi h
  have hR := ge_R G E T j (i + 1)
  have hl := T.H_RST_LINES i hi
  have ht := tau_ge G E T (i + 1) j
  have hseg : ∀ k, k ≤ W.m (i + 1) → ∀ t, W.yn (i + 1) k (W.τ (i + 1) j) j ≤ t →
      t < W.yn (i + 1) k (W.τ (i + 1) (j + 1)) (j + 1) → W.Y (i + 1) k t = Vph j := by
    intro k hk
    have := phi_le G E T i k hk
    exact line_seg (G.H_AP_WIN i hi k hk) (G.H_AP_NR i hi k hk) (by omega) (by omega) hO
  rw [Vph_succ, Bool.not_not]
  intro t t1 t2
  rw [W.Ain_in i j hi] at t1; rw [W.Ain_in i (j + 1) hi] at t2
  have hgd : W.Ag (i + 1) ≤ t := by have := W.ackT_ge' (i + 1) j (W.τ (i + 1) j); omega
  rw [G.H_ACK_LINE i hi t hgd]
  simp only [PW.ackT] at t1 t2
  rcases Nat.mod_two_eq_zero_or_one j with hj | hj
  · have hv : Vph j = true := by unfold Vph LinkTimed.Vph; simp [hj]
    rw [hv] at hseg ⊢
    simp only [hj, ite_true] at t1
    simp only [show ¬ ((j + 1) % 2 = 0) by omega, ite_false] at t2
    have g := gap G E T (i + 1) j hi; have fl := T.H_ACK_FLUSH_W i hi
    have hov : fmax (fun k => W.yn (i + 1) k (W.τ (i + 1) j) j) (W.m (i + 1)) ≤
        fmin (fun k => W.yn (i + 1) k (W.τ (i + 1) (j + 1)) (j + 1)) (W.m (i + 1)) := by
      have a1 := fmax_le (fun k => W.yn (i + 1) k (W.τ (i + 1) j) j)
        (W.τ (i + 1) j + W.ahi (i + 1)) (W.m (i + 1)) (fun k hk => by
          have p1 := phi_le G E T i k hk; have p2 := alo_le G E T i k hk
          have p3 := nt_le1 (W.Y (i + 1) k) (W.plo (i + 1) k) (W.phi (i + 1) k) (W.τ (i + 1) j) (Vph j)
          have := nt_hi_of (G.H_AP_WIN i hi k hk) hO (by unfold PW.yn at *; omega)
          unfold PW.yn at *; omega)
      have a2 := le_fmin (fun k => W.yn (i + 1) k (W.τ (i + 1) (j + 1)) (j + 1))
        (W.τ (i + 1) (j + 1) + W.alo (i + 1)) (W.m (i + 1)) (fun k hk => by
          have := yn_lo G E T i hi k hk (W.τ (i + 1) (j + 1)) (j + 1)
          have := alo_le G E T i k hk; omega)
      omega
    exact or_true_of (W.m (i + 1)) (W.Y (i + 1)) _ _ hseg hov t t1 t2
  · have hv : Vph j = false := by unfold Vph LinkTimed.Vph; simp [hj]
    rw [hv] at hseg ⊢
    simp only [show ¬ (j % 2 = 0) by omega, ite_false] at t1
    simp only [show (j + 1) % 2 = 0 by omega, ite_true] at t2
    exact or_false_of (W.m (i + 1)) (W.Y (i + 1)) _ _ hseg t t1 t2

/-- The excitation of stage `i` in phase `j` is `Vph j` over the phase. -/
def PhaseOK (i j : Nat) : Prop :=
  ∀ s, W.c i j ≤ s → s < W.c i (j + 1) → ex (W.r i) (a i) (q i) rst s = Vph j

/-- **(1) The all-Win `N`-stage pipe's control is clean, phase by phase**
(PipeTimedN's `pipe_ctl`, with every LUT, request line and acknowledge copy
a window channel). Outer induction on `j`, inner on `i`. -/
theorem pipe_ctl_w : ∀ j i, i < W.N →
    PhaseOK (W := W) (a := a) (q := q) (rst := rst) i j := by
  intro j
  induction j with
  | zero =>
    intro i
    induction i with
    | zero =>
      intro hi
      apply phase_of G E T 0 0 hi (fun t h1 h2 => E.H_REQ 0 t h1 h2)
      by_cases hl : 0 + 1 < W.N
      · exact ack_zero G E T 0 hl
      · have e : W.N - 1 = 0 := by omega
        have := ack_last E T 0; rw [e] at this; exact this
    | succ i ih =>
      intro hi
      apply phase_of G E T (i + 1) 0 hi (req_of G E T i 0 hi (ih (by omega)))
      by_cases hl : i + 1 + 1 < W.N
      · exact ack_zero G E T (i + 1) hl
      · have e : W.N - 1 = i + 1 := by omega
        have := ack_last E T 0; rw [e] at this; exact this
  | succ j ihj =>
    intro i
    induction i with
    | zero =>
      intro hi
      apply phase_of G E T 0 (j + 1) hi (fun t h1 h2 => E.H_REQ (j + 1) t h1 h2)
      by_cases hl : 0 + 1 < W.N
      · exact ack_succ G E T 0 j hl (ihj 1 hl)
      · have e : W.N - 1 = 0 := by omega
        have := ack_last E T (j + 1); rw [e] at this; exact this
    | succ i ih =>
      intro hi
      apply phase_of G E T (i + 1) (j + 1) hi (req_of G E T i (j + 1) hi (ih (by omega)))
      by_cases hl : i + 1 + 1 < W.N
      · exact ack_succ G E T (i + 1) j hl (ihj (i + 1 + 1) hl)
      · have e : W.N - 1 = i + 1 := by omega
        have := ack_last E T (j + 1); rw [e] at this; exact this

/-- **(1') Every node is a clean step signal** (all-Win pipe). -/
theorem nodes_clean_w (i : Nat) (hi : i < W.N) :
    (∀ t, W.hi i ≤ t → t < W.τ i 0 → W.O i t = false) ∧
    (∀ j t, W.τ i j ≤ t → t < W.τ i (j + 1) → W.O i t = Vph j) :=
  ⟨(pre G E T i hi).2, fun j => node_of G E T i j hi (pipe_ctl_w G E T j i hi)⟩

/-- **(1'') Every internal pin is a clean four-phase signal** (all-Win pipe). -/
theorem pins_clean_w (i : Nat) (hi : i + 1 < W.N) :
    (∀ j t, W.Rin (i + 1) j ≤ t → t < W.Rin (i + 1) (j + 1) → W.r (i + 1) t = Vph j) ∧
    (∀ j t, W.Ain i j ≤ t → t < W.Ain i (j + 1) → a i t = !Vph j) := by
  refine ⟨fun j => req_of G E T i j hi (pipe_ctl_w G E T j i (by omega)), fun j => ?_⟩
  cases j with
  | zero => exact ack_zero G E T i hi
  | succ j => exact ack_succ G E T i j hi (pipe_ctl_w G E T j (i + 1) hi)

end ctl


/-! ## 5. Lifting the all-Win run to PipeTimedN: FIFO maps for every channel

The traces of the run determine FIFO read maps for every LUT, request line
and acknowledge copy (the output edges lie in the windows of the input
edges, in order), whose `fst` are exactly the edge times read off the traces.
No spacing condition is needed for the lines: the request line's upper edge
bound comes from causality (`Rin_le_c`), the copies' from `H_ACK_FLUSH_W`. -/

open Formal.Cells.FifoFidelity (idx idx_spec idx_mono)

/-- `0, f 0, f 1, …` -/
def sh0 (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => f j

theorem idx_eq (e : Nat → Nat) (he0 : e 0 = 0) (hm : ∀ i j, i < j → e i < e j) {k t : Nat}
    (h1 : e k ≤ t) (h2 : t < e (k + 1)) : idx e t = k := by
  have s := idx_spec e he0 hm t
  rcases Nat.lt_trichotomy (idx e t) k with h | h | h
  · have : e (idx e t + 1) ≤ e k := by
      rcases Nat.lt_or_ge (idx e t + 1) k with h' | h'
      · exact Nat.le_of_lt (hm _ _ h')
      · have : idx e t + 1 = k := by omega
        rw [this]; exact Nat.le_refl _
    omega
  · exact h
  · have : e (k + 1) ≤ e (idx e t) := by
      rcases Nat.lt_or_ge (k + 1) (idx e t) with h' | h'
      · exact Nat.le_of_lt (hm _ _ h')
      · have : k + 1 = idx e t := by omega
        rw [this]; exact Nat.le_refl _
    omega

/-- **A FIFO read from matched step signals.** Input `x` low on `[gx, τ 0)`
then `Vph j` on `[τ j, τ (j+1))`; output `y` low on `[gx + hi, e 0)` then
`Vph j` on `[e j, e (j+1))`; each output edge in its input edge's window.
Then there is a FIFO read of band `[lo, hi]` valid from `gx + hi`, whose
`fst` at every input edge is the output edge. -/
theorem ret_steps {lo hi gx : Nat} {x y : Trace} {τ e : Nat → Nat} (hlh : lo ≤ hi)
    (hτ1 : 1 ≤ τ 0) (hτ : ∀ j, τ j < τ (j + 1)) (he : ∀ j, e j < e (j + 1))
    (hlo : ∀ j, τ j + lo ≤ e j) (hhi : ∀ j, e j ≤ τ j + hi)
    (hx0 : ∀ s, gx ≤ s → s < τ 0 → x s = false)
    (hx : ∀ j s, τ j ≤ s → s < τ (j + 1) → x s = Vph j)
    (hy0 : ∀ t, gx + hi ≤ t → t < e 0 → y t = false)
    (hy : ∀ j t, e j ≤ t → t < e (j + 1) → y t = Vph j) :
    ∃ r : Ret, r.lo = lo ∧ r.hi = hi ∧ (∀ t, gx + hi ≤ t → y t = x (r.σ t)) ∧
      (∀ j, r.fst (τ j) = e j) := by
  have hEm : ∀ i j, i < j → sh0 e i < sh0 e j := WinFifo.smono_of_succ _ (fun j => by
    cases j with
    | zero => show 0 < e 0; have := hlo 0; omega
    | succ j => exact he j)
  have hCm : ∀ i j, i < j → sh0 τ i < sh0 τ j := WinFifo.smono_of_succ _ (fun j => by
    cases j with
    | zero => show 0 < τ 0; omega
    | succ j => exact hτ j)
  have hE0 : sh0 e 0 = 0 := rfl
  have hCle : ∀ i j, i ≤ j → sh0 τ i ≤ sh0 τ j := fun i j h => by
    rcases Nat.lt_or_ge i j with h' | h'
    · exact Nat.le_of_lt (hCm _ _ h')
    · have : i = j := by omega
      rw [this]; exact Nat.le_refl _
  let r : Ret :=
    { σ := fun t => max (sh0 τ (idx (sh0 e) t)) (t - hi), lo := lo, hi := hi
      mono := fun a b h => by
        have := hCle _ _ (idx_mono (sh0 e) hE0 hEm h)
        show max (sh0 τ (idx (sh0 e) a)) (a - hi) ≤ max (sh0 τ (idx (sh0 e) b)) (b - hi); omega
      ge := fun t => Nat.le_max_right _ _
      le := fun t => by
        show max (sh0 τ (idx (sh0 e) t)) (t - hi) ≤ t - lo
        have s := idx_spec (sh0 e) hE0 hEm t
        generalize idx (sh0 e) t = k at s
        cases k with
        | zero => show max 0 (t - hi) ≤ t - lo; omega
        | succ k => show max (τ k) (t - hi) ≤ t - lo; have := hlo k; simp only [sh0] at s; omega }
  refine ⟨r, rfl, rfl, ?_, ?_⟩
  · intro t ht
    show y t = x (max (sh0 τ (idx (sh0 e) t)) (t - hi))
    have s := idx_spec (sh0 e) hE0 hEm t
    generalize idx (sh0 e) t = k at s
    cases k with
    | zero =>
      simp only [sh0] at s ⊢
      have := hhi 0
      rw [hy0 t ht s.2, show max 0 (t - hi) = t - hi by omega, hx0 _ (by omega) (by omega)]
    | succ k =>
      simp only [sh0] at s ⊢
      have := hhi (k + 1); have := hτ k
      rw [hy k t s.1 s.2, hx k _ (Nat.le_max_left _ _) (by omega)]
  · intro j
    have hl := hhi j
    unfold Ret.fst
    apply lfind_eq _ _ _ (by show e j < τ j + hi + 1; omega)
    · show decide (τ j ≤ max (sh0 τ (idx (sh0 e) (e j))) (e j - hi)) = true
      rw [idx_eq (sh0 e) hE0 hEm (k := j + 1) (t := e j) (show sh0 e (j + 1) ≤ e j from
        Nat.le_refl _) (he j)]
      show decide (τ j ≤ max (τ j) (e j - hi)) = true
      exact decide_eq_true (Nat.le_max_left _ _)
    · intro t ht
      show decide (τ j ≤ max (sh0 τ (idx (sh0 e) t)) (t - hi)) = false
      have s := idx_spec (sh0 e) hE0 hEm t
      have hk : idx (sh0 e) t ≤ j := by
        apply Classical.byContradiction; intro hn
        have h3 : sh0 e (j + 1) ≤ sh0 e (idx (sh0 e) t) := by
          rcases Nat.lt_or_ge (j + 1) (idx (sh0 e) t) with h' | h'
          · exact Nat.le_of_lt (hEm _ _ h')
          · have : idx (sh0 e) t = j + 1 := by omega
            rw [this]; exact Nat.le_refl _
        have h4 : sh0 e (j + 1) = e j := rfl
        omega
      have c1 := hCle _ _ hk
      have c2 : sh0 τ j < τ j := by
        cases j with
        | zero => show 0 < τ 0; omega
        | succ j => exact hτ j
      simp only [decide_eq_false_iff_not]; omega

section lift
variable {W : PW} {rst : Trace} {a q : Nat → Trace} {wl wh : Nat → Nat} {Es Er : Nat}
variable (G : GatesNW W rst a q wl wh) (E : EnvNW W (a (W.N - 1)) Es Er) (T : TimingNW W wh Es Er)
include G E T
set_option linter.unusedSectionVars false

/-- Copy `k` of boundary `i+1`, phase `j`. -/
theorem copy_seg (i j : Nat) (hi : i + 1 < W.N) (k : Nat) (hk : k ≤ W.m (i + 1)) :
    ∀ t, W.yn (i + 1) k (W.τ (i + 1) j) j ≤ t →
      t < W.yn (i + 1) k (W.τ (i + 1) (j + 1)) (j + 1) → W.Y (i + 1) k t = Vph j := by
  have hO := (nodes_clean_w G E T (i + 1) hi).2 j
  have hR := ge_R G E T j (i + 1); have ht := tau_ge G E T (i + 1) j
  have hl := T.H_RST_LINES i hi; have := phi_le G E T i k hk
  exact line_seg (G.H_AP_WIN i hi k hk) (G.H_AP_NR i hi k hk) (by omega) (by omega) hO

theorem copy_hi (i j : Nat) (hi : i + 1 < W.N) (k : Nat) (hk : k ≤ W.m (i + 1)) :
    W.yn (i + 1) k (W.τ (i + 1) j) j ≤ W.τ (i + 1) j + W.phi (i + 1) k := by
  have hO := (nodes_clean_w G E T (i + 1) hi).2 j
  have g := gap G E T (i + 1) j hi; have fl := T.H_ACK_FLUSH_W i hi
  have p1 := phi_le G E T i k hk; have p2 := alo_le G E T i k hk
  have p3 := nt_le1 (W.Y (i + 1) k) (W.plo (i + 1) k) (W.phi (i + 1) k) (W.τ (i + 1) j) (Vph j)
  exact nt_hi_of (G.H_AP_WIN i hi k hk) hO (by omega)

/-- `Rin_le_c` with the round trip credited. -/
theorem Rin_le_c' (i j : Nat) (h : i + 1 < W.N) :
    W.Rin (i + 1) j + W.lo (i + 1) + W.alo (i + 1) ≤ W.c i (j + 1) := by
  have := W.c_eq i (j + 1); rw [W.Ain_in i j h] at this
  have := ackT_ge G E T i h j (W.τ (i + 1) j); have := tau_lo G E T (i + 1) j h
  have := W.c_eq (i + 1) j; omega

/-- **Each controller LUT is a FIFO read** of its excitation (Bex's bridge,
`ret_of_clean`), with `fst` at the phase starts = the node edges. -/
theorem lut_ret (i : Nat) : ∃ L : Ret, i < W.N → L.lo = W.lo i ∧ L.hi = W.hi i ∧
    (∀ t, W.hi i ≤ t → W.O i t = ex (W.r i) (a i) (q i) rst (L.σ t)) ∧
    ∀ j, L.fst (W.c i j) = W.τ i j := by
  by_cases hi : i < W.N
  · have hR := ge_R G E T
    have hp := T.H_R_POS; have hb := T.H_RST_LONG i hi
    have cc := clean_of_phases (by have := hR 0 i; omega) (pre G E T i hi).1
      (fun j => pipe_ctl_w G E T j i hi) (spread G E T i · hi) (lh G E T i hi)
    obtain ⟨L, hl, hh, hr⟩ := ret_of_clean (G.H_ST i hi).H_LUT_WIN (G.H_ST i hi).H_NO_REVERT cc.1 cc.2
    refine ⟨L, fun _ => ⟨hl, hh, hr, fun j => ?_⟩⟩
    have h := hR j i
    cases j with
    | zero =>
      exact fst_eq_nt L hl hh hr (cp := 0) (c' := W.c i 1)
        (fun s _ h => by rw [(pre G E T i hi).1 s h, Vph_even 0]; rfl) (pipe_ctl_w G E T 0 i hi)
        (by omega) (spread G E T i 0 hi) (by omega)
    | succ j =>
      have hs := spread G E T i j hi
      exact fst_eq_nt L hl hh hr (cp := W.c i j) (c' := W.c i (j + 2))
        (fun s a b => by rw [pipe_ctl_w G E T j i hi s a b, Vph_succ, Bool.not_not])
        (pipe_ctl_w G E T (j + 1) i hi) (by omega) (spread G E T i (j + 1) hi) (by omega)
  · exact ⟨Ret.shift 0, fun h => absurd h hi⟩

/-- **Each request line is a FIFO read** of the node, valid after reset
release, `fst` = the request-pin edges. No spacing hypothesis: the
upper bound comes from causality. -/
theorem req_ret (i : Nat) : ∃ Q : Ret, i + 1 < W.N → Q.lo = W.qlo (i + 1) ∧
    Q.hi = W.qhi (i + 1) ∧ (∀ t, W.hi i + W.qhi (i + 1) ≤ t → W.r (i + 1) t = W.O i (Q.σ t)) ∧
    ∀ j, Q.fst (W.τ i j) = W.Rin (i + 1) j := by
  by_cases hi : i + 1 < W.N
  · have nc := nodes_clean_w G E T i (by omega)
    have pc := (pins_clean_w G E T i hi).1
    have hlat := T.H_LAT i (by omega); have lp := (G.H_ST i (by omega)).H_LOOP_POS
    have wl' := wlh G E T i (by omega)
    obtain ⟨Q, a1, a2, a3, a4⟩ := ret_steps (x := W.O i) (y := W.r (i + 1)) (τ := W.τ i)
      (e := W.Rin (i + 1)) (gx := W.hi i) (qlh G E T i hi)
      (by have := ge_R G E T 0 i; have := tau_ge G E T i 0; have := T.H_R_POS; omega)
      (fun j => live G E T i j (by omega))
      (fun j => by
        have := Rin_le_c' G E T i j hi; have := Rin_lo G E T i (j + 1) hi
        have := tau_lo G E T i (j + 1) (by omega); rw [W.EA_in Er i hi] at hlat; omega)
      (fun j => Rin_lo G E T i j hi)
      (fun j => nt_hi_of (G.H_REQ_WIN i hi) (nc.2 j) (by
        have := Rin_le_c G E T i j hi; have := tau_ge G E T i (j + 1)
        show W.Rin (i + 1) j ≤ _; omega))
      nc.1 nc.2
      (fun t h1 h2 => line_pre (G.H_REQ_WIN i hi) nc.1 t h1
        (by show t < nt _ _ _ _ _; have e : W.Rin (i + 1) 0 = nt (W.r (i + 1)) (W.qlo (i + 1))
              (W.qhi (i + 1)) (W.τ i 0) (Vph 0) := rfl
            rw [Vph_even 0] at e; rw [← e]; exact h2))
      pc
    exact ⟨Q, fun _ => ⟨a1, a2, a3, a4⟩⟩
  · exact ⟨Ret.shift 0, fun h => absurd h hi⟩

/-- **Each acknowledge copy is a FIFO read** of stage `i+1`'s node. -/
theorem copy_ret (i k : Nat) : ∃ A : Ret, i + 1 < W.N → k ≤ W.m (i + 1) →
    A.lo = W.plo (i + 1) k ∧ A.hi = W.phi (i + 1) k ∧
    (∀ t, W.hi (i + 1) + W.phi (i + 1) k ≤ t → W.Y (i + 1) k t = W.O (i + 1) (A.σ t)) ∧
    ∀ j, A.fst (W.τ (i + 1) j) = W.yn (i + 1) k (W.τ (i + 1) j) j := by
  by_cases hi : i + 1 < W.N
  · by_cases hk : k ≤ W.m (i + 1)
    · have nc := nodes_clean_w G E T (i + 1) hi
      have fl := T.H_ACK_FLUSH_W i hi
      have p1 := phi_le G E T i k hk; have p2 := alo_le G E T i k hk
      obtain ⟨A, a1, a2, a3, a4⟩ := ret_steps (x := W.O (i + 1)) (y := W.Y (i + 1) k)
        (τ := W.τ (i + 1)) (e := fun j => W.yn (i + 1) k (W.τ (i + 1) j) j) (gx := W.hi (i + 1))
        (plh G E T i hi k hk)
        (by have := ge_R G E T 0 (i + 1); have := tau_ge G E T (i + 1) 0; have := T.H_R_POS; omega)
        (fun j => live G E T (i + 1) j hi)
        (fun j => by
          have := copy_hi G E T i j hi k hk; have := gap G E T (i + 1) j hi
          have := yn_lo G E T i hi k hk (W.τ (i + 1) (j + 1)) (j + 1)
          show W.yn (i + 1) k (W.τ (i + 1) j) j < W.yn (i + 1) k (W.τ (i + 1) (j + 1)) (j + 1)
          omega)
        (fun j => yn_lo G E T i hi k hk _ _) (fun j => copy_hi G E T i j hi k hk)
        nc.1 nc.2
        (fun t h1 h2 => line_pre (G.H_AP_WIN i hi k hk) nc.1 t h1
          (by have e : W.yn (i + 1) k (W.τ (i + 1) 0) 0 = nt (W.Y (i + 1) k) (W.plo (i + 1) k)
                (W.phi (i + 1) k) (W.τ (i + 1) 0) (Vph 0) := rfl
              rw [Vph_even 0] at e; rw [← e]; exact h2))
        (fun j => copy_seg G E T i j hi k hk)
      exact ⟨A, fun _ _ => ⟨a1, a2, a3, a4⟩⟩
    · exact ⟨Ret.shift 0, fun _ h => absurd h hk⟩
  · exact ⟨Ret.shift 0, fun h => absurd h hi⟩

end lift


theorem choice_fn {α : Type} {p : Nat → α → Prop} (h : ∀ i, ∃ x, p i x) :
    ∃ f : Nat → α, ∀ i, p i (f i) :=
  ⟨fun i => Classical.choose (h i), fun i => Classical.choose_spec (h i)⟩

theorem choice_fn2 {α : Type} {p : Nat → Nat → α → Prop} (h : ∀ i k, ∃ x, p i k x) :
    ∃ f : Nat → Nat → α, ∀ i k, p i k (f i k) :=
  ⟨fun i k => Classical.choose (h i k), fun i k => Classical.choose_spec (h i k)⟩

/-- The controller's excitation does not see its pins while reset is high. -/
theorem ex_congr {r r' a a' q rst : Trace} {R : Nat} (hrst : ∀ s, s < R → rst s = true)
    (hr : ∀ s, R ≤ s → r' s = r s) (ha : ∀ s, R ≤ s → a' s = a s) :
    ∀ s, ex r' a' q rst s = ex r a q rst s := by
  intro s
  by_cases h : s < R
  · unfold ex; rw [CElemTiming.c2n_eq, CElemTiming.c2n_eq, hrst s h]; rfl
  · unfold ex; rw [hr s (by omega), ha s (by omega)]

section lift2
variable {W : PW} {rst : Trace} {a q : Nat → Trace} {wl wh : Nat → Nat} {Es Er : Nat}
variable (G : GatesNW W rst a q wl wh) (E : EnvNW W (a (W.N - 1)) Es Er) (T : TimingNW W wh Es Er)
include G E T
set_option linter.unusedSectionVars false

/-- **Probe Bex2, the lift.** Every all-Win run (`GatesNW`, `EnvNW`,
`TimingNW`) IS a run of PipeTimedN: there is a `PN` with the same stages,
reset, environment times and bands, with FIFO read maps for every
controller LUT, request line and acknowledge copy, whose derived phase
starts and node edges are the ones read off the traces, and pin traces
`r'`, `a'` that agree with the real pins from reset release on (before it,
reset masks the pins: `ex_congr`), such that `PipeTimedN.GatesN`, `EnvN`,
`TimingN` hold. So every PipeTimedN theorem holds for the run. -/
theorem lift : ∃ P : PN, P.N = W.N ∧ P.R = W.R ∧ P.ρ = W.ρ ∧ P.γ = W.γ ∧ P.m = W.m ∧
    (∀ i, i < W.N → (P.L i).lo = W.lo i ∧ (P.L i).hi = W.hi i) ∧
    (∀ i, i + 1 < W.N → (P.Rq (i + 1)).lo = W.qlo (i + 1) ∧ (P.Rq (i + 1)).hi = W.qhi (i + 1)) ∧
    (∀ i k, i + 1 < W.N → k ≤ W.m (i + 1) →
      (P.Ap (i + 1) k).lo = W.plo (i + 1) k ∧ (P.Ap (i + 1) k).hi = W.phi (i + 1) k) ∧
    (∀ i j, i < W.N → P.c i j = W.c i j ∧ P.τ i j = W.τ i j) ∧
    (∀ i, i < W.N → P.ER Es i = W.ER Es i ∧ P.EA Er i = W.EA Er i ∧
      P.Won Es Er i = W.Won Es Er i) ∧
    (∀ i, i + 1 < W.N → P.alo (i + 1) = W.alo (i + 1) ∧ P.ahi (i + 1) = W.ahi (i + 1) ∧
      P.aslow (i + 1) = W.aslow (i + 1)) ∧
    ∃ r' a' : Nat → Trace, r' 0 = W.r 0 ∧ a' (W.N - 1) = a (W.N - 1) ∧
      (∀ i t, W.R ≤ t → r' i t = W.r i t ∧ a' i t = a i t) ∧
      GatesN P rst r' a' W.O q wl wh ∧ EnvN P (r' 0) (a' (P.N - 1)) Es Er ∧ TimingN P wh Es Er := by
  have hRp := T.H_R_POS
  obtain ⟨Lf, hLf⟩ := choice_fn (lut_ret G E T)
  obtain ⟨Qf, hQf⟩ := choice_fn (req_ret G E T)
  obtain ⟨Af, hAf⟩ := choice_fn2 (copy_ret G E T)
  obtain ⟨P, hPN, hPR, hPL, hPRq, hPm, hPAp, hPAg, hPρ, hPγ⟩ : ∃ P : PN, P.N = W.N ∧ P.R = W.R ∧
      P.L = Lf ∧ (∀ i, P.Rq (i + 1) = Qf i) ∧ P.m = W.m ∧ (∀ i k, P.Ap (i + 1) k = Af i k) ∧
      P.Ag = (fun _ => 0) ∧ P.ρ = W.ρ ∧ P.γ = W.γ :=
    ⟨{ N := W.N, R := W.R, L := Lf, Rq := fun b => Qf (b - 1), m := W.m,
       Ap := fun b k => Af (b - 1) k, Ag := fun _ => 0, ρ := W.ρ, γ := W.γ },
     rfl, rfl, rfl, fun _ => rfl, rfl, fun _ _ => rfl, rfl, rfl, rfl⟩
  -- derived times agree
  have hτ : ∀ i j, i < W.N → P.c i j = W.c i j → P.τ i j = W.τ i j := fun i j hi h => by
    show (P.L i).fst (P.c i j) = _; rw [h, hPL]; exact (hLf i hi).2.2.2 j
  have hack : ∀ i j, i + 1 < W.N →
      P.ackT (i + 1) j (W.τ (i + 1) j) = W.ackT (i + 1) j (W.τ (i + 1) j) := by
    intro i j hi
    unfold PN.ackT PW.ackT
    simp only [hPAp, hPm]
    rw [fmin_congr _ _ _ (fun k hk => (hAf i k hi hk).2.2.2 j),
      fmax_congr _ _ _ (fun k hk => (hAf i k hi hk).2.2.2 j)]
  have hAin : ∀ i j, (∀ k, k < W.N → P.c k j = W.c k j) → P.Ain i (j + 1) = W.Ain i (j + 1) := by
    intro i j h
    by_cases hl : i + 1 < W.N
    · rw [PN.Ain_in P i j (by rw [hPN]; exact hl), W.Ain_in i j hl, hτ (i + 1) j hl (h _ hl),
        hack i j hl]
    · rw [PN.Ain_last P i j (by rw [hPN]; exact hl), W.Ain_last i j hl, hPγ]
  have hRin : ∀ i j, i + 1 < W.N → P.c i j = W.c i j → P.Rin (i + 1) j = W.Rin (i + 1) j := by
    intro i j hi h
    show (P.Rq (i + 1)).fst (P.τ i j) = _
    rw [hτ i j (by omega) h, hPRq]; exact (hQf i hi).2.2.2 j
  have hrow : ∀ j, (∀ i, P.Ain i j = W.Ain i j) → ∀ i, i < W.N → P.c i j = W.c i j := by
    intro j hA i
    induction i with
    | zero =>
      intro _; rw [PN.c_eq, W.c_eq, hA 0]
      show max (P.ρ j) _ = max (W.ρ j) _; rw [hPρ]
    | succ i ih => intro hi; rw [PN.c_eq, W.c_eq, hA (i + 1), hRin i j hi (ih (by omega))]
  have hc : ∀ j i, i < W.N → P.c i j = W.c i j := by
    intro j
    induction j with
    | zero => exact hrow 0 (fun i => by show P.R = W.R; exact hPR)
    | succ j ihj => exact hrow (j + 1) (fun i => hAin i j ihj)
  have hτ' : ∀ i j, i < W.N → P.τ i j = W.τ i j := fun i j hi => hτ i j hi (hc j i hi)
  -- bands
  have hPalo : ∀ i, i + 1 < W.N → P.alo (i + 1) = W.alo (i + 1) := fun i hi => by
    unfold PN.alo PW.alo; simp only [hPAp, hPm]
    exact fmin_congr _ _ _ (fun k hk => (hAf i k hi hk).1)
  have hPahi : ∀ i, i + 1 < W.N → P.ahi (i + 1) = W.ahi (i + 1) := fun i hi => by
    unfold PN.ahi PW.ahi; simp only [hPAp, hPm]
    exact fmax_congr _ _ _ (fun k hk => (hAf i k hi hk).2.1)
  have hPaslow : ∀ i, i + 1 < W.N → P.aslow (i + 1) = W.aslow (i + 1) := fun i hi => by
    unfold PN.aslow PW.aslow; simp only [hPAp, hPm]
    exact fmax_congr _ _ _ (fun k hk => (hAf i k hi hk).1)
  have hLlo : ∀ i, i < W.N → (P.L i).lo = W.lo i := fun i hi => by rw [hPL]; exact (hLf i hi).1
  have hLhi : ∀ i, i < W.N → (P.L i).hi = W.hi i := fun i hi => by rw [hPL]; exact (hLf i hi).2.1
  have hQlo : ∀ i, i + 1 < W.N → (P.Rq (i + 1)).lo = W.qlo (i + 1) := fun i hi => by
    rw [hPRq]; exact (hQf i hi).1
  have hQhi : ∀ i, i + 1 < W.N → (P.Rq (i + 1)).hi = W.qhi (i + 1) := fun i hi => by
    rw [hPRq]; exact (hQf i hi).2.1
  have hPER : ∀ i, i < W.N → P.ER Es i = W.ER Es i := fun i hi => by
    cases i with
    | zero => rfl
    | succ i =>
      show P.alo (i + 1) + (P.L i).lo + (P.Rq (i + 1)).lo = W.alo (i + 1) + W.lo i + W.qlo (i + 1)
      rw [hPalo i hi, hLlo i (by omega), hQlo i hi]
  have hPEA : ∀ i, i < W.N → P.EA Er i = W.EA Er i := fun i hi => by
    by_cases h : i + 1 < W.N
    · rw [PN.EA_in P Er i (by rw [hPN]; exact h), W.EA_in Er i h, hQlo i h, hLlo (i + 1) h,
        hPalo i h]
    · rw [PN.EA_last P Er i (by rw [hPN]; exact h), W.EA_last Er i h]
  have hPWon : ∀ i, i < W.N → P.Won Es Er i = W.Won Es Er i := fun i hi => by
    unfold PN.Won PW.Won; rw [hLlo i hi, hPER i hi, hPEA i hi]
  -- the pins before reset release
  obtain ⟨r', hr'0, hr's⟩ : ∃ r' : Nat → Trace, r' 0 = W.r 0 ∧ ∀ i t,
      r' (i + 1) t = if W.R ≤ t then W.r (i + 1) t else W.O i ((Qf i).σ t) :=
    ⟨fun i => match i with
      | 0 => W.r 0
      | i + 1 => fun t => if W.R ≤ t then W.r (i + 1) t else W.O i ((Qf i).σ t),
     rfl, fun _ _ => rfl⟩
  obtain ⟨a', ha's⟩ : ∃ a' : Nat → Trace, ∀ i t, a' i t =
      if i + 1 < W.N ∧ t < W.R then orAll (fun k => W.O (i + 1) ((Af i k).σ t)) (W.m (i + 1))
      else a i t :=
    ⟨fun i t => if i + 1 < W.N ∧ t < W.R then orAll (fun k => W.O (i + 1) ((Af i k).σ t)) (W.m (i + 1))
      else a i t, fun _ _ => rfl⟩
  have hr'R : ∀ i t, W.R ≤ t → r' i t = W.r i t := fun i t ht => by
    cases i with
    | zero => rw [hr'0]
    | succ i => rw [hr's, if_pos ht]
  have ha'R : ∀ i t, W.R ≤ t → a' i t = a i t := fun i t ht => by
    rw [ha's, if_neg (by omega)]
  have ha'N : a' (W.N - 1) = a (W.N - 1) := funext fun t => by rw [ha's, if_neg (by omega)]
  have hrst := rst_hi G E T
  refine ⟨P, hPN, hPR, hPρ, hPγ, hPm, fun i hi => ⟨hLlo i hi, hLhi i hi⟩,
    fun i hi => ⟨hQlo i hi, hQhi i hi⟩,
    fun i k hi hk => ⟨by rw [hPAp]; exact (hAf i k hi hk).1, by rw [hPAp]; exact (hAf i k hi hk).2.1⟩,
    fun i j hi => ⟨hc j i hi, hτ' i j hi⟩,
    fun i hi => ⟨hPER i hi, hPEA i hi, hPWon i hi⟩,
    fun i hi => ⟨hPalo i hi, hPahi i hi, hPaslow i hi⟩,
    r', a', hr'0, ha'N, fun i t ht => ⟨hr'R i t ht, ha'R i t ht⟩, ?_, ?_, ?_⟩
  · -- GatesN
    refine { H_RST := ?_, H_CTL := ?_, H_REQ_LINE := ?_, H_ACK_LINE := ?_ }
    · intro t; rw [G.H_RST, hPR]
    · intro i hi
      rw [hPN] at hi
      refine ⟨fun t ht => ?_, (G.H_ST i hi).H_FB, ?_⟩
      · rw [ex_congr hrst (hr'R i) (ha'R i)]
        rw [hPL] at ht ⊢
        exact (hLf i hi).2.2.1 t (by rw [← (hLf i hi).2.1]; exact ht)
      · rw [hLlo i hi]; exact (G.H_ST i hi).H_LOOP_POS
    · intro i hi t ht
      rw [hPN] at hi
      rw [hr's, hPRq]
      split
      · have := (T.H_RST_LINES i hi).1
        exact (hQf i hi).2.2.1 t (by omega)
      · rfl
    · intro i hi t _
      rw [hPN] at hi
      rw [ha's]
      simp only [hPAp, hPm]
      split
      · rfl
      · rename_i h
        have ht : W.R ≤ t := by omega
        have hl := T.H_RST_LINES i hi
        rw [G.H_ACK_LINE i hi t (by omega)]
        apply orAll_congr
        intro k hk
        have := phi_le G E T i k hk
        exact (hAf i k hi hk).2.2.1 t (by omega)
  · -- EnvN
    rw [show P.N - 1 = W.N - 1 by rw [hPN], ha'N, hr'0]
    have hn := T.H_N_POS
    exact { H_REQ_LOW0 := fun t h1 h2 => by rw [hPR, hPρ] at *; exact E.H_REQ_LOW0 t h1 h2
            H_REQ := fun j t h1 h2 => by rw [hPρ] at *; exact E.H_REQ j t h1 h2
            H_ACK_LOW0 := fun t h1 h2 => by rw [hPR, hPγ] at *; exact E.H_ACK_LOW0 t h1 h2
            H_ACK := fun j t h1 h2 => by rw [hPγ] at *; exact E.H_ACK j t h1 h2
            H_SND := fun j => by rw [hτ' 0 j (by omega), hPρ]; exact E.H_SND j
            H_RCV := fun j => by
              rw [hPN, hτ' (W.N - 1) j (by omega), hPγ]; exact E.H_RCV j
            H_RST_EARLY := by rw [hPR, hPρ]; exact E.H_RST_EARLY }
  · -- TimingN
    exact { H_N_POS := by rw [hPN]; exact T.H_N_POS
            H_R_POS := by rw [hPR]; exact T.H_R_POS
            H_RST_LONG := fun i hi => by
              rw [hPN] at hi; rw [hLhi i hi, hPR]; exact T.H_RST_LONG i hi
            H_RST_LINES := fun i hi => by
              rw [hPN] at hi
              have := T.H_RST_LINES i hi
              rw [hLhi i (by omega), hQhi i hi, hLhi (i + 1) hi, hPahi i hi, hPAg, hPR]
              exact ⟨this.1, this.2.1, Nat.zero_le _⟩
            H_LAT := fun i hi => by
              rw [hPN] at hi
              rw [hLhi i hi, hLlo i hi, hPER i hi, hPEA i hi]; exact T.H_LAT i hi
            H_ACK_FLUSH := fun i hi => by
              rw [hPN] at hi
              have := T.H_ACK_FLUSH_W i hi
              rw [hPahi i hi, hLlo (i + 1) hi, hPER (i + 1) hi, hPEA (i + 1) hi, hPalo i hi]
              unfold PW.Won at this; omega }

/-- **Corollary: PipeTimedN's data theorem on the all-Win pipe.** For the
lifted `P` (same stages, times, bands and node edges as the run), every data
contract `DataN P …` yields `PipeTimedN.pipe_forward`: the last stage
delivers every token. (`DataN`'s timing terms are `P`'s, which `lift` shows
equal to the run's: `τ`, `Won`, `ER`, `EA`, `aslow`, bands.) -/
theorem pipe_forward_w : ∃ P : PN, P.N = W.N ∧ P.ρ = W.ρ ∧ P.γ = W.γ ∧
    (∀ i j, i < W.N → P.τ i j = W.τ i j) ∧
    ∀ (d : Nat → Bundling.Sig) (x : Nat → Nat → Bundling.Sig) (val : Nat → Nat → Bool)
      (dS dE : Nat → Nat) (V : Nat → PipeTimed.Win) (Wd Erel Sdr Lag : Nat),
      PipeTimedN.DataN P W.O d x val dS dE V Wd Es Er Erel Sdr Lag → ∀ k b, b < Wd →
      (∀ t, P.Sx V dS k b (P.N - 1) ≤ t → t < P.γ (2 * k + 1) → x (P.N - 1) b t = val k b) ∧
      (PipeTimedN.Dl P V Sdr Lag (P.N - 1) b ≤ (Er : Int) →
        ∀ t, P.γ (2 * k) ≤ t → t < P.γ (2 * k + 1) → x (P.N - 1) b t = val k b) := by
  obtain ⟨P, hN, _, hρ, hγ, _, _, _, _, hct, _, _, r', a', _, _, _, G', E', T'⟩ := lift G E T
  exact ⟨P, hN, hρ, hγ, fun i j hi => (hct i j hi).2,
    fun d x val dS dE V Wd Erel Sdr Lag D k b hb => PipeTimedN.pipe_forward G' E' T' D k b hb⟩

end lift2


/-! ## 6. What a WIRE needs (the line hypothesis, justified)

In the digital model a routed wire (a buffer chain: site pins, pips, wire
segments) is a single-input pure delay line `y t = x (t - d t)` whose delay
`d t` lies in the band. That IS the window channel (`delay_line_iff_win`):
nothing in `Win` says more than "the output is the input some delay ago".
So `Win` alone lets a wire glitch on ONE input edge (`wire_glitch`, from
`WinFifo.win_glitch_not_fifo`): H_NO_REVERT is NOT provable for a wire from
`Win`. It is provable from `Win` + **monotone read** (`t - d t`
nondecreasing: a later output instant never shows an earlier input instant;
`mono_read_fifo` turns it into a FIFO read) on a clean input whose edges the
wire delivers before the input's next edge (`H_CATCH`) — `wire_noRevert`,
with NO spacing condition between the wire's band and the input's edges.
The physical content of monotone read for a wire: each stage of a buffer
chain has ONE input and a monotone transfer, so an edge cannot overtake the
previous one and a single input edge makes a single output edge; monotone
read composes along the chain (`PipeTimed.fifo_comp`). In the pipe,
`H_CATCH` is causality: the node's next edge waits for the acknowledge this
request line's edge triggers (`fifo_req_nr`, `fifo_copy_nr`: every FIFO line
of a PipeTimedN run satisfies H_REQ_WIN/H_REQ_NR and H_AP_WIN/H_AP_NR). So
for a wire, monotone read is the primitive and H_NO_REVERT is derived; for a
LUT (several inputs, a mux tree) it is not (Bw: skew glitches). -/

/-- **A window channel is a pure delay line with a time-varying delay**, and
conversely. -/
theorem delay_line_iff_win {lo hi : Nat} {x y : Trace} :
    Win lo hi x y ↔ ∃ d : Nat → Nat, ∀ t, hi ≤ t → lo ≤ d t ∧ d t ≤ hi ∧ y t = x (t - d t) := by
  constructor
  · intro hW
    refine ⟨fun t => if h : hi ≤ t then t - Classical.choose (hW t h) else lo, fun t ht => ?_⟩
    have s := Classical.choose_spec (hW t ht)
    simp only [ht, dite_true]
    refine ⟨by omega, by omega, ?_⟩
    rw [show t - (t - Classical.choose (hW t ht)) = Classical.choose (hW t ht) by omega]
    exact s.2.2
  · rintro ⟨d, hd⟩ t ht
    obtain ⟨h1, h2, h3⟩ := hd t ht
    exact ⟨t - d t, by omega, by omega, h3⟩

/-- **A wire can glitch under `Win` alone.** For every band at least two
ticks wide there is a delay function inside the band for which the wire's
output of ONE rising edge goes 1, 0, 1, and no FIFO read reproduces it. -/
theorem wire_glitch {lo hi : Nat} (h2 : lo + 2 ≤ hi) :
    ∃ d : Nat → Nat, (∀ t, hi ≤ t → lo ≤ d t ∧ d t ≤ hi ∧
        WinFifo.glitch hi lo t = WinFifo.step hi (t - d t)) ∧
      ∀ r : Ret, r.hi ≤ hi → ¬ ∀ t, r.hi ≤ t → WinFifo.glitch hi lo t = WinFifo.step hi (r.σ t) := by
  obtain ⟨hW, hn⟩ := WinFifo.win_glitch_not_fifo h2
  obtain ⟨d, hd⟩ := delay_line_iff_win.1 hW
  exact ⟨d, hd, hn⟩

/-- **Monotone read makes a delay line FIFO.** -/
theorem mono_read_fifo {lo hi : Nat} {x y : Trace} (d : Nat → Nat)
    (hd : ∀ t, lo ≤ d t ∧ d t ≤ hi) (hm : ∀ a b, a ≤ b → a - d a ≤ b - d b)
    (hy : ∀ t, y t = x (t - d t)) :
    ∃ r : Ret, r.lo = lo ∧ r.hi = hi ∧ ∀ t, y t = x (r.σ t) :=
  ⟨{ σ := fun t => t - d t, lo := lo, hi := hi, mono := hm,
     ge := fun t => by have := hd t; show t - hi ≤ t - d t; omega,
     le := fun t => by have := hd t; show t - d t ≤ t - lo; omega }, rfl, rfl, hy⟩

/-- Every instant after `c 0` lies in some segment of a strictly increasing `c`. -/
theorem seg_of {c : Nat → Nat} (hc : ∀ j, c j < c (j + 1)) (s : Nat) (hs : c 0 ≤ s) :
    ∃ k, c k ≤ s ∧ s < c (k + 1) := by
  have hge : ∀ k, k ≤ c k := by
    intro k; induction k with
    | zero => exact Nat.zero_le _
    | succ k ih => have := hc k; omega
  have P : ∀ n, s < c n → ∃ k, c k ≤ s ∧ s < c (k + 1) := by
    intro n
    induction n with
    | zero => intro h; omega
    | succ n ih =>
      intro h
      by_cases h' : s < c n
      · exact ih h'
      · exact ⟨n, by omega, h⟩
  exact P (s + 1) (by have := hge (s + 1); omega)

theorem cmono {c : Nat → Nat} (hc : ∀ j, c j < c (j + 1)) : ∀ i j, i ≤ j → c i ≤ c j := by
  intro i j h
  induction j with
  | zero => have : i = 0 := by omega
            rw [this]; exact Nat.le_refl _
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h' | h'
    · have := ih (by omega); have := hc j; omega
    · have : i = j + 1 := by omega
      rw [this]; exact Nat.le_refl _

/-- **H_NO_REVERT of a wire, from monotone read.** A FIFO read `r` (band
`[lo, hi]`) of an alternating clean input (edges `c`, values `val`) that
delivers each input edge before the input's next edge can arrive
(**H_CATCH**: `fst (c j) ≤ c (j+1) + lo`) satisfies the line hypothesis
`NoRevertFrom g` for every `g` with `c 0 + hi ≤ g + lo`. No spacing
condition between the band and the edges. -/
theorem wire_noRevert {lo hi g : Nat} {x y : Trace} {c : Nat → Nat} {val : Nat → Bool}
    (r : Ret) (hl : r.lo = lo) (hh : r.hi = hi) (hy : ∀ t, hi ≤ t → y t = x (r.σ t))
    (hc : ∀ j, c j < c (j + 1)) (halt : ∀ j, val (j + 1) = !val j)
    (hx : ∀ j s, c j ≤ s → s < c (j + 1) → x s = val j)
    (hcatch : ∀ j, r.fst (c j) ≤ c (j + 1) + lo) (hg : c 0 + hi ≤ g + lo) :
    NoRevertFrom g lo hi x y := by
  intro a b v t1 t2 hga hab h0 h1 h12 h2 hv
  have hlh : lo ≤ hi := by have := r.lo_le_hi; omega
  have cm := cmono hc
  obtain ⟨k, k1, k2⟩ := seg_of hc a (by omega)
  have hvk : val k = v := by rw [← hx k a k1 k2]; exact hab a (Nat.le_refl _) (by omega)
  have hb : b ≤ c (k + 1) := by
    apply Classical.byContradiction; intro hn
    have e1 := hab (c (k + 1)) (by omega) (by omega)
    rw [hx (k + 1) _ (Nat.le_refl _) (hc (k + 1)), halt, hvk] at e1
    cases v <;> simp at e1
  have g1 := r.ge t1; have l1 := r.le t1; have l2 := r.le t2
  rw [hh] at g1; rw [hl] at l1 l2
  have m12 := r.mono t1 t2 h12
  -- the read at `t1` is in segment `k - 1` or later
  have hlow : (k = 0 ∧ c 0 ≤ r.σ t1) ∨ (1 ≤ k ∧ c (k - 1) ≤ r.σ t1) := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · left; exact ⟨hk, by omega⟩
    · right
      refine ⟨hk, r.fst_after ?_⟩
      have := hcatch (k - 1); rw [show k - 1 + 1 = k by omega] at this; omega
  have hσ1 : c k ≤ r.σ t1 := by
    rcases hlow with ⟨hk, h⟩ | ⟨hk, h⟩
    · rw [hk]; exact h
    · apply Classical.byContradiction; intro hn
      have e := hx (k - 1) (r.σ t1) h (by rw [show k - 1 + 1 = k by omega]; omega)
      rw [hy t1 h0, e] at hv
      have := halt (k - 1); rw [show k - 1 + 1 = k by omega, hvk] at this
      rw [this] at hv; cases v <;> simp at hv
  rw [hy t2 (by omega), hx k _ (by omega) (by omega), hvk]


/-- `a, f 0, f 1, …` -/
def shL (a : Nat) (f : Nat → Nat) : Nat → Nat
  | 0 => a
  | j + 1 => f j

theorem vW_alt (j : Nat) : WinFifoCausal.vW (j + 1) = !WinFifoCausal.vW j := by
  cases j with
  | zero => rfl
  | succ j => show Vph (j + 1) = !Vph j; exact Vph_succ j

section fifo_special
variable {P : PN} {rst : Trace} {r a O q : Nat → Trace} {wl wh : Nat → Nat} {Es Er : Nat}
variable (G : GatesN P rst r a O q wl wh) (E : EnvN P (r 0) (a (P.N - 1)) Es Er)
  (T : TimingN P wh Es Er)
include G E T

theorem node_steps (i : Nat) (hi : i < P.N) :
    (∀ j, shL (P.L i).hi (P.τ i) j < shL (P.L i).hi (P.τ i) (j + 1)) ∧
    (∀ j s, shL (P.L i).hi (P.τ i) j ≤ s → s < shL (P.L i).hi (P.τ i) (j + 1) →
      O i s = WinFifoCausal.vW j) := by
  have C := G.H_CTL i hi
  have hwl : wl i ≤ wh i := by obtain ⟨s, h1, h2, _⟩ := C.H_FB (wh i) (Nat.le_refl _); omega
  have hp := C.H_LOOP_POS
  have nc := PipeTimedN.nodes_clean G E T i hi
  refine ⟨fun j => ?_, fun j s h1 h2 => ?_⟩
  · cases j with
    | zero =>
      show (P.L i).hi < P.τ i 0
      have := PipeTimedN.ge_R E 0 i; have := PipeTimedN.tau_lo E T i 0
      have := T.H_RST_LONG i hi; omega
    | succ j => exact PipeTimedN.live E T i j hi (by omega)
  · cases j with
    | zero => exact nc.1 s h1 h2
    | succ j => exact nc.2 j s h1 h2

/-- **FIFO request lines satisfy the line hypotheses** (H_REQ_WIN, H_REQ_NR)
in every PipeTimedN run: monotone read + causality (H_CATCH), no spacing. -/
theorem fifo_req_nr (i : Nat) (hi : i + 1 < P.N) :
    Win (P.Rq (i + 1)).lo (P.Rq (i + 1)).hi (O i) (r (i + 1)) ∧
    NoRevertFrom P.R (P.Rq (i + 1)).lo (P.Rq (i + 1)).hi (O i) (r (i + 1)) := by
  have hl := (T.H_RST_LINES i hi).1
  have ns := node_steps G E T i (by omega)
  refine ⟨PipeTimed.fifo_win _ (G.H_REQ_LINE i hi), ?_⟩
  refine wire_noRevert (P.Rq (i + 1)) rfl rfl (G.H_REQ_LINE i hi) ns.1 vW_alt ns.2 (fun j => ?_)
    (by show (P.L i).hi + _ ≤ _; omega)
  cases j with
  | zero =>
    show (P.Rq (i + 1)).fst (P.L i).hi ≤ P.τ i 0 + _
    have := (P.Rq (i + 1)).fst_le (P.L i).hi
    have := PipeTimedN.ge_R E 0 i; have := PipeTimedN.tau_lo E T i 0; omega
  | succ j =>
    show (P.Rq (i + 1)).fst (P.τ i j) ≤ P.τ i (j + 1) + _
    have h1 : P.Rin (i + 1) j = (P.Rq (i + 1)).fst (P.τ i j) := rfl
    have h2 := P.c_eq (i + 1) j
    have h3 := (P.L (i + 1)).fst_ge (P.c (i + 1) j)
    have h4 := P.ackT_ge' (i + 1) j (P.τ (i + 1) j)
    have h5 := P.c_eq i (j + 1); rw [P.Ain_in i j hi] at h5
    have h6 := PipeTimedN.tau_lo E T i (j + 1)
    unfold PN.τ at *; omega

/-- **FIFO acknowledge copies satisfy the copy hypotheses** (H_AP_WIN,
H_AP_NR) in every PipeTimedN run, with the copy trace `O (i+1) ∘ σ`. -/
theorem fifo_copy_nr (i : Nat) (hi : i + 1 < P.N) (k : Nat) (hk : k ≤ P.m (i + 1)) :
    Win (P.Ap (i + 1) k).lo (P.Ap (i + 1) k).hi (O (i + 1)) (fun t => O (i + 1) ((P.Ap (i + 1) k).σ t)) ∧
    NoRevertFrom P.R (P.Ap (i + 1) k).lo (P.Ap (i + 1) k).hi (O (i + 1))
      (fun t => O (i + 1) ((P.Ap (i + 1) k).σ t)) := by
  have hl := (T.H_RST_LINES i hi).2.1
  have ns := node_steps G E T (i + 1) hi
  have e1 := le_fmax_of (fun k => (P.Ap (i + 1) k).hi) _ (P.m (i + 1)) k hk (Nat.le_refl _)
  have e2 := fmin_le_of (fun k => (P.Ap (i + 1) k).lo) _ (P.m (i + 1)) k hk (Nat.le_refl _)
  have fl := T.H_ACK_FLUSH i hi
  refine ⟨PipeTimed.fifo_win _ (fun t _ => rfl), ?_⟩
  refine wire_noRevert (P.Ap (i + 1) k) rfl rfl (fun t _ => rfl) ns.1 vW_alt ns.2 (fun j => ?_)
    (by show (P.L (i + 1)).hi + _ ≤ _; unfold PN.ahi at hl; omega)
  cases j with
  | zero =>
    show (P.Ap (i + 1) k).fst (P.L (i + 1)).hi ≤ P.τ (i + 1) 0 + _
    have := (P.Ap (i + 1) k).fst_le (P.L (i + 1)).hi
    have := PipeTimedN.ge_R E 0 (i + 1); have := PipeTimedN.tau_lo E T (i + 1) 0
    unfold PN.ahi at hl; omega
  | succ j =>
    show (P.Ap (i + 1) k).fst (P.τ (i + 1) j) ≤ P.τ (i + 1) (j + 1) + _
    have := (P.Ap (i + 1) k).fst_le (P.τ (i + 1) j)
    have g := PipeTimedN.gap E T (i + 1) j hi
    unfold PN.Won at g; unfold PN.ahi PN.alo at fl; omega

end fifo_special


/-! ## 7. Non-vacuity for every `N ≥ 1`, every delay strictly inside its band

Every controller LUT, request line and acknowledge copy is a 2-tick
transport delay and is only ASSUMED to be a `Win 1 3` channel (band two
ticks wide, where `Win ⊄ FIFO`), so the actual delay sits strictly inside
the band; the feedback wires are 1 tick. Reset is released at 6. Stage `i`'s
request pin is the square wave `sqh (6 + 4i)` (8 high, 8 low), its node
`sqh (8 + 4i)`, its feedback `sqh (9 + 4i)`, its acknowledge pin
`sqh (14 + 4i)`. Closed-form event times: `c i j = 6 + 4i + 8j`,
`τ i j = 8 + 4i + 8j` (`cc_w`, `τ_w`): every edge is read off the traces at
`c + 2`, not at the band's end. -/

namespace Wn

/-- Square wave, half period 8: low before `o`, then 8 high, 8 low, … -/
def sqh (o t : Nat) : Bool := decide (o ≤ t ∧ (t - o) % 16 < 8)

theorem sqh_pre (o t : Nat) (h : t < o) : sqh o t = false := by
  unfold sqh; simp; omega

theorem sqh_phase (o j t : Nat) (h1 : o + 8 * j ≤ t) (h2 : t < o + 8 * (j + 1)) :
    sqh o t = Vph j := by
  unfold sqh Vph LinkTimed.Vph
  by_cases hj : j % 2 = 0
  · have : (t - o) % 16 < 8 := by omega
    simp [hj, this, show o ≤ t by omega]
  · have : ¬ ((t - o) % 16 < 8) := by omega
    simp [hj, this]

theorem sqh_del (o d t : Nat) (h : d ≤ t) : sqh (o + d) t = sqh o (t - d) := by
  unfold sqh
  have e : t - (o + d) = t - d - o := by omega
  rw [e]
  by_cases h' : o + d ≤ t
  · simp [h', show o ≤ t - d by omega]
  · simp [h', show ¬ (o ≤ t - d) by omega]

def rst6 (t : Nat) : Bool := decide (t < 6)

/-- The real `bd_c2n` excitation of square waves offset by 0 (request), +3
(own feedback) and +8 (acknowledge) is the request wave. -/
theorem key8 (o s : Nat) (ho : 6 ≤ o) :
    ex (sqh o) (sqh (o + 8)) (sqh (o + 3)) rst6 s = sqh o s := by
  unfold ex rst6
  rw [CElemTiming.c2n_eq]
  by_cases h0 : s < o
  · rw [sqh_pre o s h0, sqh_pre (o + 8) s (by omega), sqh_pre (o + 3) s (by omega)]
    cases decide (s < 6) <;> rfl
  · have hr : decide (s < 6) = false := by simp; omega
    rw [hr]
    by_cases hA : (s - o) % 16 < 8
    · have e1 : sqh o s = true := by unfold sqh; simp; omega
      have e2 : sqh (o + 8) s = false := by unfold sqh; simp; omega
      rw [e1, e2]; cases sqh (o + 3) s <;> rfl
    · have e1 : sqh o s = false := by unfold sqh; simp; omega
      have e2 : sqh (o + 8) s = true := by unfold sqh; simp; omega
      rw [e1, e2]; cases sqh (o + 3) s <;> rfl

/-- Edge list of `sqh o` as a clean-from-0 input. -/
def sc (o : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => o + 8 * j

theorem sq_clean (o : Nat) (ho : 1 ≤ o) : Clean (sqh o) (sc o) WinFifoCausal.vW :=
  ⟨rfl, WinFifo.smono_of_succ _ (fun j => by
      cases j with
      | zero => show 0 < o + 8 * 0; omega
      | succ j => show o + 8 * j < o + 8 * (j + 1); omega),
   fun j s h1 h2 => by
      cases j with
      | zero => exact sqh_pre o s (by simpa [sc] using h2)
      | succ j => exact sqh_phase o j s h1 (by simpa [sc] using h2)⟩

theorem sq_spread (o lo hi : Nat) (h : hi < lo + 8) : Spread lo hi (sc o) := by
  intro j hj
  cases j with
  | zero => omega
  | succ j => show o + 8 * j + hi < o + 8 * (j + 1) + lo; omega

/-- A fixed delay `d` inside the band `[lo, hi]` as a FIFO read. -/
def rd (d lo hi : Nat) (h1 : lo ≤ d) (h2 : d ≤ hi) : Ret where
  σ t := t - d
  lo := lo
  hi := hi
  mono a b h := by omega
  ge t := by omega
  le t := by omega

theorem del_win (o d lo hi : Nat) (h1 : lo ≤ d) (h2 : d ≤ hi) :
    Win lo hi (sqh o) (sqh (o + d)) :=
  fun t ht => ⟨t - d, by omega, by omega, sqh_del o d t (by omega)⟩

/-- **H_NO_REVERT holds for a delay STRICTLY inside the band** on the
square wave (Bex's witnesses only had the delay at `lo`). -/
theorem del_nr (o d lo hi : Nat) (ho : 1 ≤ o) (h1 : lo ≤ d) (h2 : d ≤ hi) (h3 : hi < lo + 8) :
    NoRevertI lo hi (sqh o) (sqh (o + d)) :=
  noRevertI_of_ret (sq_clean o ho) (sq_spread o lo hi h3) (rd d lo hi h1 h2) rfl rfl
    (fun t ht => sqh_del o d t (by omega))

/-- `nt` of a square wave whose `j`-th phase starts at `c + 2`. -/
theorem nt_sq (p c j : Nat) (h : p + 8 * j = c + 2) : nt (sqh p) 1 3 c (Vph j) = c + 2 := by
  unfold nt
  apply lfind_eq _ _ _ (by omega)
  · rw [sqh_phase p j (c + 2) (by omega) (by omega)]; simp
  · intro t ht
    by_cases h1 : c + 1 ≤ t
    · have e : t = c + 1 := by omega
      subst e
      have hv : sqh p (c + 1) = !Vph j := by
        cases j with
        | zero => rw [sqh_pre p _ (by omega), Vph_even 0]; rfl
        | succ j => rw [sqh_phase p j _ (by omega) (by omega), Vph_succ, Bool.not_not]
      rw [hv]; cases Vph j <;> simp
    · simp [h1]

/-- The witness run with `N` stages. -/
def Ww (N : Nat) : PW where
  N := N
  R := 6
  lo _ := 1
  hi _ := 3
  qlo _ := 1
  qhi _ := 3
  m _ := 0
  plo _ _ := 1
  phi _ _ := 3
  Ag _ := 0
  ρ j := 6 + 8 * j
  γ j := 10 + 4 * N + 8 * j
  O i := sqh (8 + 4 * i)
  r i := sqh (6 + 4 * i)
  Y b _ := sqh (10 + 4 * b)

def aW (i : Nat) : Trace := sqh (14 + 4 * i)
def qW (i : Nat) : Trace := sqh (9 + 4 * i)

theorem row_w (N j : Nat) (α : Nat → Nat) (hα : ∀ i, α i ≤ 6 + 4 * i + 8 * j) :
    ∀ i, (Ww N).row j α i = 6 + 4 * i + 8 * j := by
  intro i
  induction i with
  | zero => show max (6 + 8 * j) (α 0) = _; have := hα 0; omega
  | succ i ih =>
    show max (nt (sqh (6 + 4 * (i + 1))) 1 3 (nt (sqh (8 + 4 * i)) 1 3 ((Ww N).row j α i) (Vph j))
      (Vph j)) (α (i + 1)) = _
    rw [ih, nt_sq (8 + 4 * i) _ j (by omega), nt_sq (6 + 4 * (i + 1)) _ j (by omega)]
    have := hα (i + 1); omega

theorem cc_w (N : Nat) : ∀ j i, (Ww N).cc j i = 6 + 4 * i + 8 * j := by
  intro j
  induction j with
  | zero => exact row_w N 0 (fun _ => 6) (fun i => by omega)
  | succ j ih =>
    apply row_w
    intro i
    show (if i + 1 < N then (Ww N).ackT (i + 1) j (nt (sqh (8 + 4 * (i + 1))) 1 3 ((Ww N).cc j (i + 1))
      (Vph j)) else 10 + 4 * N + 8 * j) ≤ _
    split
    · rw [ih, nt_sq _ _ j (by omega)]
      show (if j % 2 = 0 then nt (sqh (10 + 4 * (i + 1))) 1 3 _ (Vph j)
        else nt (sqh (10 + 4 * (i + 1))) 1 3 _ (Vph j)) ≤ _
      rw [nt_sq (10 + 4 * (i + 1)) _ j (by omega)]
      split <;> omega
    · omega

theorem τ_w (N i j : Nat) : (Ww N).τ i j = 8 + 4 * i + 8 * j := by
  show nt (sqh (8 + 4 * i)) 1 3 ((Ww N).cc j i) (Vph j) = _
  rw [cc_w, nt_sq _ _ j (by omega)]; omega

/-- One controller of the witness: real `bd_c2n` INIT, LUT a 2-tick delay
assumed only `Win 1 3` + H_NO_REVERT, feedback 1 tick. -/
theorem stage_w (o : Nat) (ho : 6 ≤ o) :
    Stage (sqh o) (sqh (o + 8)) rst6 (sqh (o + 2)) (sqh (o + 3)) 1 3 1 1 := by
  have e : ex (sqh o) (sqh (o + 8)) (sqh (o + 3)) rst6 = sqh o := funext (fun s => key8 o s ho)
  exact { H_LUT_WIN := by rw [e]; exact del_win o 2 1 3 (by omega) (by omega)
          H_NO_REVERT := by rw [e]; exact del_nr o 2 1 3 (by omega) (by omega) (by omega) (by omega)
          H_FB := CElemTiming.transport_winDelay (Nat.le_refl 1) (Nat.le_refl 1)
            (fun t => by rw [show o + 3 = o + 2 + 1 by omega, sqh_del (o + 2) 1 (t + 1) (by omega)]
                         rfl)
          H_LOOP_POS := by decide }

theorem gates_w (N : Nat) : GatesNW (Ww N) rst6 aW qW (fun _ => 1) (fun _ => 1) where
  H_RST _ := rfl
  H_ST i _ := by
    have h := stage_w (6 + 4 * i) (by omega)
    rw [show 6 + 4 * i + 8 = 14 + 4 * i by omega, show 6 + 4 * i + 2 = 8 + 4 * i by omega,
      show 6 + 4 * i + 3 = 9 + 4 * i by omega] at h
    exact h
  H_REQ_WIN i _ := by
    have h := del_win (8 + 4 * i) 2 1 3 (by omega) (by omega)
    rw [show 8 + 4 * i + 2 = 6 + 4 * (i + 1) by omega] at h; exact h
  H_REQ_NR i _ := by
    have h := del_nr (8 + 4 * i) 2 1 3 (by omega) (by omega) (by omega) (by omega)
    rw [show 8 + 4 * i + 2 = 6 + 4 * (i + 1) by omega] at h; exact noRevertFrom_of_I h
  H_AP_WIN i _ k _ := by
    have h := del_win (8 + 4 * (i + 1)) 2 1 3 (by omega) (by omega)
    rw [show 8 + 4 * (i + 1) + 2 = 10 + 4 * (i + 1) by omega] at h; exact h
  H_AP_NR i _ k _ := by
    have h := del_nr (8 + 4 * (i + 1)) 2 1 3 (by omega) (by omega) (by omega) (by omega)
    rw [show 8 + 4 * (i + 1) + 2 = 10 + 4 * (i + 1) by omega] at h; exact noRevertFrom_of_I h
  H_ACK_LINE i _ t _ := by
    show sqh (14 + 4 * i) t = sqh (10 + 4 * (i + 1)) t
    rw [show 10 + 4 * (i + 1) = 14 + 4 * i by omega]

theorem env_w (N : Nat) (hN : 1 ≤ N) : EnvNW (Ww N) (aW ((Ww N).N - 1)) 6 6 where
  H_REQ_LOW0 t h1 h2 := by simp only [Ww] at h1 h2; omega
  H_REQ j t h1 h2 := sqh_phase 6 j t (by simp only [Ww] at h1; omega) (by simp only [Ww] at h2; omega)
  H_ACK_LOW0 t h1 h2 := by
    show sqh (14 + 4 * (N - 1)) t = false
    exact sqh_pre _ t (by simp only [Ww] at h2; omega)
  H_ACK j t h1 h2 := by
    show sqh (14 + 4 * (N - 1)) t = Vph j
    exact sqh_phase _ j t (by simp only [Ww] at h1; omega) (by simp only [Ww] at h2; omega)
  H_SND j := by rw [τ_w]; show 8 + 4 * 0 + 8 * j + 6 ≤ 6 + 8 * (j + 1); omega
  H_RCV j := by rw [τ_w]; show 8 + 4 * (N - 1) + 8 * j + 6 ≤ 10 + 4 * N + 8 * j; omega
  H_RST_EARLY := by show 6 ≤ 6 + 8 * 0; omega

theorem ER_w (N i : Nat) : 3 ≤ (Ww N).ER 6 i := by
  cases i with
  | zero => show 3 ≤ 6; omega
  | succ i => show 3 ≤ 1 + 1 + 1; omega

theorem EA_w (N i : Nat) : 3 ≤ (Ww N).EA 6 i := by
  unfold PW.EA; split
  · show 3 ≤ 1 + 1 + 1; omega
  · show 3 ≤ 6; omega

theorem timing_w (N : Nat) (hN : 1 ≤ N) : TimingNW (Ww N) (fun _ => 1) 6 6 where
  H_N_POS := hN
  H_R_POS := by show 1 ≤ 6; omega
  H_RST_LONG _ _ := by show 3 + 1 ≤ 6; omega
  H_RST_LINES _ _ := by show 3 + 3 ≤ 6 ∧ 3 + 3 ≤ 6 ∧ 0 ≤ 6; omega
  H_LAT i _ := by
    have := ER_w N i; have := EA_w N i
    show 3 + 1 ≤ 1 + min ((Ww N).ER 6 i) ((Ww N).EA 6 i); omega
  H_ACK_FLUSH_W i _ := by
    have := ER_w N (i + 1); have := EA_w N (i + 1)
    show 3 < 1 + max ((Ww N).ER 6 (i + 1)) ((Ww N).EA 6 (i + 1)) + 1; omega

/-- **Non-vacuity, every `N ≥ 1`, delays strictly inside the bands.** The
witness satisfies every field of `GatesNW`, `EnvNW`, `TimingNW`; every LUT,
request line and copy is a 2-tick delay inside its `[1, 3]` band (stated
here as trace equations), and the node edges alternate every 8 ticks. -/
theorem witness (N : Nat) (hN : 1 ≤ N) :
    GatesNW (Ww N) rst6 aW qW (fun _ => 1) (fun _ => 1) ∧
    EnvNW (Ww N) (aW ((Ww N).N - 1)) 6 6 ∧ TimingNW (Ww N) (fun _ => 1) 6 6 ∧
    (∀ i j, (Ww N).τ i j = 8 + 4 * i + 8 * j) ∧
    (∀ i t, 2 ≤ t → (Ww N).O i t = ex ((Ww N).r i) (aW i) (qW i) rst6 (t - 2)) ∧
    (∀ i t, 2 ≤ t → (Ww N).r (i + 1) t = (Ww N).O i (t - 2)) ∧
    (∀ i t, 2 ≤ t → (Ww N).Y (i + 1) 0 t = (Ww N).O (i + 1) (t - 2)) ∧
    (∀ i, (Ww N).lo i < 2 ∧ 2 < (Ww N).hi i ∧ (Ww N).qlo (i + 1) < 2 ∧ 2 < (Ww N).qhi (i + 1) ∧
      (Ww N).plo (i + 1) 0 < 2 ∧ 2 < (Ww N).phi (i + 1) 0) := by
  refine ⟨gates_w N, env_w N hN, timing_w N hN, τ_w N, fun i t ht => ?_, fun i t ht => ?_,
    fun i t ht => ?_, fun i => ⟨show 1 < 2 by omega, show 2 < 3 by omega, show 1 < 2 by omega, show 2 < 3 by omega,
      show 1 < 2 by omega, show 2 < 3 by omega⟩⟩
  · show sqh (8 + 4 * i) t = ex (sqh (6 + 4 * i)) (sqh (14 + 4 * i)) (sqh (9 + 4 * i)) rst6 (t - 2)
    have := key8 (6 + 4 * i) (t - 2) (by omega)
    rw [show 6 + 4 * i + 8 = 14 + 4 * i by omega, show 6 + 4 * i + 3 = 9 + 4 * i by omega] at this
    rw [this, show 8 + 4 * i = 6 + 4 * i + 2 by omega, sqh_del _ 2 t ht]
  · show sqh (6 + 4 * (i + 1)) t = sqh (8 + 4 * i) (t - 2)
    rw [show 6 + 4 * (i + 1) = 8 + 4 * i + 2 by omega, sqh_del _ 2 t ht]
  · show sqh (10 + 4 * (i + 1)) t = sqh (8 + 4 * (i + 1)) (t - 2)
    rw [show 10 + 4 * (i + 1) = 8 + 4 * (i + 1) + 2 by omega, sqh_del _ 2 t ht]

/-- The lift applies to the witness: a live PipeTimedN run whose every
channel was only assumed `Win`. -/
theorem witness_lift (N : Nat) (hN : 1 ≤ N) :
    ∃ P : PN, P.N = N ∧ (∀ i j, i < N → P.τ i j = 8 + 4 * i + 8 * j) ∧
      ∃ r' a' : Nat → Trace, GatesN P rst6 r' a' (Ww N).O qW (fun _ => 1) (fun _ => 1) ∧
        EnvN P (r' 0) (a' (P.N - 1)) 6 6 ∧ TimingN P (fun _ => 1) 6 6 := by
  obtain ⟨P, hN', _, _, _, _, _, _, _, hct, _, _, r', a', _, _, _, G', E', T'⟩ :=
    lift (gates_w N) (env_w N hN) (timing_w N hN)
  exact ⟨P, hN', fun i j hi => by rw [(hct i j hi).2, τ_w], r', a', G', E', T'⟩

end Wn


/-! ## 8. Counter-run: the line no-revert hypothesis cannot be dropped

Two stages, every LUT, request line and acknowledge copy a 2-tick delay in a
`[1, 3]` band, feedback 1 tick, half period 10 (the sender and receiver set
the pace, the internal loop has 2 ticks of slack, so stage 0's acknowledge
arrives 2 ticks before its next request). ONE glitch on the acknowledge copy
of boundary 1, inside the zone of stage 1's first node edge (`τ 1 0 = 12`,
zone `[13, 15)`): the copy shows 1 at 13 (it may: the window reads the node
at 12), 0 at 14 (reads 11), then 1. Stage 0's excitation cannot see it
(request and own feedback are both high there), so EVERY other hypothesis of
the all-Win pipe holds; H_AP_NR fails, the acknowledge pin is not clean
(the conclusion `pins_clean_w` fails at `t = 14`), and no FIFO read with
`hi ≤ 3` reproduces the copy. -/

namespace Wg

/-- Square wave, half period 10. -/
def sqT (o t : Nat) : Bool := decide (o ≤ t ∧ (t - o) % 20 < 10)

theorem sqT_pre (o t : Nat) (h : t < o) : sqT o t = false := by
  unfold sqT; simp; omega

theorem sqT_phase (o j t : Nat) (h1 : o + 10 * j ≤ t) (h2 : t < o + 10 * (j + 1)) :
    sqT o t = Vph j := by
  unfold sqT Vph LinkTimed.Vph
  by_cases hj : j % 2 = 0
  · have : (t - o) % 20 < 10 := by omega
    simp [hj, this, show o ≤ t by omega]
  · have : ¬ ((t - o) % 20 < 10) := by omega
    simp [hj, this]

theorem sqT_del (o d t : Nat) (h : d ≤ t) : sqT (o + d) t = sqT o (t - d) := by
  unfold sqT
  have e : t - (o + d) = t - d - o := by omega
  rw [e]
  by_cases h' : o + d ≤ t
  · simp [h', show o ≤ t - d by omega]
  · simp [h', show ¬ (o ≤ t - d) by omega]

open Wn (rst6 rd)

/-- `bd_c2n` of square waves: request at `o`, acknowledge at `o + k`
(`3 ≤ k ≤ 10`), own feedback at `o + 3`, is the request wave. -/
theorem keyT (o k s : Nat) (ho : 6 ≤ o) (hk1 : 3 ≤ k) (hk2 : k ≤ 10) :
    ex (sqT o) (sqT (o + k)) (sqT (o + 3)) rst6 s = sqT o s := by
  unfold ex rst6 sqT; rw [CElemTiming.c2n_eq]
  by_cases h0 : s < 6 <;> by_cases hA : (o ≤ s ∧ (s - o) % 20 < 10) <;>
    by_cases hB : (o + k ≤ s ∧ (s - (o + k)) % 20 < 10) <;>
    by_cases hC : (o + 3 ≤ s ∧ (s - (o + 3)) % 20 < 10) <;>
    simp [h0, hA, hB, hC] <;> omega

def sc (o : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => o + 10 * j

theorem sq_clean (o : Nat) (ho : 1 ≤ o) : Clean (sqT o) (sc o) WinFifoCausal.vW :=
  ⟨rfl, WinFifo.smono_of_succ _ (fun j => by
      cases j with
      | zero => show 0 < o + 10 * 0; omega
      | succ j => show o + 10 * j < o + 10 * (j + 1); omega),
   fun j s h1 h2 => by
      cases j with
      | zero => exact sqT_pre o s (by simpa [sc] using h2)
      | succ j => exact sqT_phase o j s h1 (by simpa [sc] using h2)⟩

theorem sq_spread (o lo hi : Nat) (h : hi < lo + 10) : Spread lo hi (sc o) := by
  intro j hj
  cases j with
  | zero => omega
  | succ j => show o + 10 * j + hi < o + 10 * (j + 1) + lo; omega

theorem del_win (o d lo hi : Nat) (h1 : lo ≤ d) (h2 : d ≤ hi) :
    Win lo hi (sqT o) (sqT (o + d)) :=
  fun t ht => ⟨t - d, by omega, by omega, sqT_del o d t (by omega)⟩

theorem del_nr (o d lo hi : Nat) (ho : 1 ≤ o) (h1 : lo ≤ d) (h2 : d ≤ hi) (h3 : hi < lo + 10) :
    NoRevertI lo hi (sqT o) (sqT (o + d)) :=
  noRevertI_of_ret (sq_clean o ho) (sq_spread o lo hi h3) (rd d lo hi h1 h2) rfl rfl
    (fun t ht => sqT_del o d t (by omega))

theorem nt_sq (p c j : Nat) (h : p + 10 * j = c + 2) : nt (sqT p) 1 3 c (Vph j) = c + 2 := by
  unfold nt
  apply lfind_eq _ _ _ (by omega)
  · rw [sqT_phase p j (c + 2) (by omega) (by omega)]; simp
  · intro t ht
    by_cases h1 : c + 1 ≤ t
    · have e : t = c + 1 := by omega
      subst e
      have hv : sqT p (c + 1) = !Vph j := by
        cases j with
        | zero => rw [sqT_pre p _ (by omega), Vph_even 0]; rfl
        | succ j => rw [sqT_phase p j _ (by omega) (by omega), Vph_succ, Bool.not_not]
      rw [hv]; cases Vph j <;> simp
    · simp [h1]

/-- The glitching acknowledge copy: the clean copy `sqT 14` except 1 at 13
and 0 at 14. -/
def Yg (t : Nat) : Bool := if t = 13 then true else if t = 14 then false else sqT 14 t

theorem Yg_eq (t : Nat) (h : 15 ≤ t) : Yg t = sqT 14 t := by
  unfold Yg; simp only [show t ≠ 13 by omega, show t ≠ 14 by omega, ite_false]

/-- `nt` only reads the trace from `c` on. -/
theorem nt_congr (O O' : Trace) (lo hi c : Nat) (v : Bool) (h : ∀ t, c ≤ t → O t = O' t) :
    nt O lo hi c v = nt O' lo hi c v := by
  unfold nt
  congr 1
  funext t
  by_cases ht : c + lo ≤ t
  · rw [h t (by omega)]
  · simp [ht]

def Wg : PW where
  N := 2
  R := 6
  lo _ := 1
  hi _ := 3
  qlo _ := 1
  qhi _ := 3
  m _ := 0
  plo _ _ := 1
  phi _ _ := 3
  Ag _ := 0
  ρ j := 6 + 10 * j
  γ j := 20 + 10 * j
  O i := sqT (8 + 4 * i)
  r i := sqT (6 + 4 * i)
  Y _ _ := Yg

def aG : Nat → Trace
  | 0 => Yg
  | _ => sqT 20

def qG (i : Nat) : Trace := sqT (9 + 4 * i)

theorem cc_g : ∀ j, Wg.cc j 0 = 6 + 10 * j ∧ Wg.cc j 1 = 10 + 10 * j := by
  intro j
  induction j with
  | zero =>
    refine ⟨rfl, ?_⟩
    show max (nt (sqT (6 + 4 * 1)) 1 3 (nt (sqT (8 + 4 * 0)) 1 3 (max (6 + 10 * 0) 6) (Vph 0))
      (Vph 0)) 6 = _
    rw [show max (6 + 10 * 0) 6 = 6 by rfl, nt_sq (8 + 4 * 0) 6 0 (by omega),
      nt_sq (6 + 4 * 1) _ 0 (by omega)]
    decide
  | succ j ih =>
    have h0 : Wg.cc (j + 1) 0 = 6 + 10 * (j + 1) := by
      show max (6 + 10 * (j + 1)) (Wg.ackIn j (fun i => Wg.tn i (Wg.cc j i) j) 0) = _
      have : Wg.ackIn j (fun i => Wg.tn i (Wg.cc j i) j) 0 ≤ 16 + 10 * j := by
        unfold PW.ackIn
        rw [if_pos (show 0 + 1 < Wg.N by decide)]
        show (if j % 2 = 0 then nt Yg 1 3 (nt (sqT (8 + 4 * 1)) 1 3 (Wg.cc j 1) (Vph j)) (Vph j)
          else nt Yg 1 3 (nt (sqT (8 + 4 * 1)) 1 3 (Wg.cc j 1) (Vph j)) (Vph j)) ≤ _
        rw [ih.2, nt_sq (8 + 4 * 1) _ j (by omega)]
        have := nt_le1 Yg 1 3 (10 + 10 * j + 2) (Vph j)
        split <;> omega
      omega
    refine ⟨h0, ?_⟩
    show max (Wg.rn 1 (Wg.tn 0 (Wg.cc (j + 1) 0) (j + 1)) (j + 1))
      (Wg.ackIn j (fun i => Wg.tn i (Wg.cc j i) j) 1) = _
    rw [h0]
    unfold PW.ackIn
    rw [if_neg (show ¬ (1 + 1 < Wg.N) by decide)]
    show max (nt (sqT (6 + 4 * 1)) 1 3 (nt (sqT (8 + 4 * 0)) 1 3 (6 + 10 * (j + 1)) (Vph (j + 1)))
      (Vph (j + 1))) (20 + 10 * j) = _
    rw [nt_sq (8 + 4 * 0) _ (j + 1) (by omega), nt_sq (6 + 4 * 1) _ (j + 1) (by omega)]
    omega

theorem τ0_g (j : Nat) : Wg.τ 0 j = 8 + 10 * j := by
  show nt (sqT (8 + 4 * 0)) 1 3 (Wg.cc j 0) (Vph j) = _
  rw [(cc_g j).1, nt_sq _ _ j (by omega)]; omega

theorem τ1_g (j : Nat) : Wg.τ 1 j = 12 + 10 * j := by
  show nt (sqT (8 + 4 * 1)) 1 3 (Wg.cc j 1) (Vph j) = _
  rw [(cc_g j).2, nt_sq _ _ j (by omega)]; omega

theorem stage_g (o k : Nat) (a : Trace) (ho : 6 ≤ o) (hk1 : 3 ≤ k) (hk2 : k ≤ 10)
    (ha : ∀ s, ex (sqT o) a (sqT (o + 3)) rst6 s = ex (sqT o) (sqT (o + k)) (sqT (o + 3)) rst6 s) :
    Stage (sqT o) a rst6 (sqT (o + 2)) (sqT (o + 3)) 1 3 1 1 := by
  have e : ex (sqT o) a (sqT (o + 3)) rst6 = sqT o :=
    funext (fun s => by rw [ha s, keyT o k s ho hk1 hk2])
  exact { H_LUT_WIN := by rw [e]; exact del_win o 2 1 3 (by omega) (by omega)
          H_NO_REVERT := by rw [e]; exact del_nr o 2 1 3 (by omega) (by omega) (by omega) (by omega)
          H_FB := CElemTiming.transport_winDelay (Nat.le_refl 1) (Nat.le_refl 1)
            (fun t => by rw [show o + 3 = o + 2 + 1 by omega, sqT_del (o + 2) 1 (t + 1) (by omega)]
                         rfl)
          H_LOOP_POS := by decide }

/-- Stage 0 cannot see the glitch: its request and own feedback are high. -/
theorem ex0_g (s : Nat) : ex (sqT 6) Yg (sqT 9) rst6 s = ex (sqT 6) (sqT 14) (sqT 9) rst6 s := by
  by_cases h13 : s = 13
  · subst h13; decide
  · by_cases h14 : s = 14
    · subst h14; decide
    · unfold ex Yg; simp only [h13, h14, ite_false]

theorem Yg_win : Win 1 3 (sqT 12) Yg := by
  intro t ht
  by_cases h13 : t = 13
  · subst h13; exact ⟨12, by omega, by omega, by decide⟩
  · by_cases h14 : t = 14
    · subst h14; exact ⟨11, by omega, by omega, by decide⟩
    · refine ⟨t - 2, by omega, by omega, ?_⟩
      unfold Yg; simp only [h13, h14, ite_false]
      exact sqT_del 12 2 t (by omega)

theorem ER_g (i : Nat) : 3 ≤ Wg.ER 6 i := by
  cases i with
  | zero => show 3 ≤ 6; omega
  | succ i => show 3 ≤ 1 + 1 + 1; omega

theorem EA_g (i : Nat) : 3 ≤ Wg.EA 6 i := by
  unfold PW.EA; split
  · show 3 ≤ 1 + 1 + 1; omega
  · show 3 ≤ 6; omega

/-- **Counter-run: H_AP_NR (the line's no-revert) cannot be dropped.** Every
field of `GatesNW` except `H_AP_NR`, every field of `EnvNW` and `TimingNW`
holds; `H_AP_NR` fails, the acknowledge pin conclusion of `pins_clean_w`
fails at `t = 14`, and no FIFO read with `hi ≤ 3` gives the copy. -/
theorem line_nr_needed :
    (∀ t, rst6 t = decide (t < Wg.R)) ∧
    (∀ i, i < Wg.N → Stage (Wg.r i) (aG i) rst6 (Wg.O i) (qG i) (Wg.lo i) (Wg.hi i) 1 1) ∧
    (∀ i, i + 1 < Wg.N → Win (Wg.qlo (i + 1)) (Wg.qhi (i + 1)) (Wg.O i) (Wg.r (i + 1))) ∧
    (∀ i, i + 1 < Wg.N → NoRevertFrom Wg.R (Wg.qlo (i + 1)) (Wg.qhi (i + 1)) (Wg.O i) (Wg.r (i + 1))) ∧
    (∀ i, i + 1 < Wg.N → ∀ k, k ≤ Wg.m (i + 1) →
      Win (Wg.plo (i + 1) k) (Wg.phi (i + 1) k) (Wg.O (i + 1)) (Wg.Y (i + 1) k)) ∧
    (∀ i, i + 1 < Wg.N → ∀ t, Wg.Ag (i + 1) ≤ t →
      aG i t = orAll (fun k => Wg.Y (i + 1) k t) (Wg.m (i + 1))) ∧
    EnvNW Wg (aG (Wg.N - 1)) 6 6 ∧ TimingNW Wg (fun _ => 1) 6 6 ∧
    ¬ NoRevertFrom Wg.R (Wg.plo 1 0) (Wg.phi 1 0) (Wg.O 1) (Wg.Y 1 0) ∧
    ¬ (∀ t, Wg.Ain 0 1 ≤ t → t < Wg.Ain 0 2 → aG 0 t = !Vph 1) ∧
    ∀ r : Ret, r.hi ≤ 3 → ¬ ∀ t, r.hi ≤ t → Wg.Y 1 0 t = Wg.O 1 (r.σ t) := by
  have hA1 : Wg.Ain 0 1 = 13 := by
    rw [Wg.Ain_in 0 0 (by decide), τ1_g]
    show (if 0 % 2 = 0 then nt Yg 1 3 (12 + 10 * 0) (Vph 0) else nt Yg 1 3 (12 + 10 * 0) (Vph 0)) = 13
    decide
  have hA2 : Wg.Ain 0 2 = 24 := by
    rw [Wg.Ain_in 0 1 (by decide), τ1_g]
    show (if 1 % 2 = 0 then nt Yg 1 3 (12 + 10 * 1) (Vph 1) else nt Yg 1 3 (12 + 10 * 1) (Vph 1)) = 24
    rw [if_neg (by decide), nt_congr Yg (sqT 14) 1 3 _ _ (fun t ht => Yg_eq t (by omega)),
      nt_sq 14 _ 1 (by omega)]
  refine ⟨fun _ => rfl, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi k _ => ?_,
    fun i hi t _ => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : i = 0 ∨ i = 1 := by simp only [Wg] at hi; omega
    rcases this with h | h <;> subst h
    · exact stage_g 6 8 Yg (by omega) (by omega) (by omega) ex0_g
    · exact stage_g 10 10 (sqT 20) (by omega) (by omega) (by omega) (fun _ => rfl)
  · have : i = 0 := by simp only [Wg] at hi; omega
    subst this; exact del_win 8 2 1 3 (by omega) (by omega)
  · have : i = 0 := by simp only [Wg] at hi; omega
    subst this; exact noRevertFrom_of_I (del_nr 8 2 1 3 (by omega) (by omega) (by omega) (by omega))
  · have : i = 0 := by simp only [Wg] at hi; omega
    subst this; exact Yg_win
  · have : i = 0 := by simp only [Wg] at hi; omega
    subst this; rfl
  · exact { H_REQ_LOW0 := fun t h1 h2 => by simp only [Wg] at h1 h2; omega
            H_REQ := fun j t h1 h2 => sqT_phase 6 j t (by simp only [Wg] at h1; omega)
              (by simp only [Wg] at h2; omega)
            H_ACK_LOW0 := fun t h1 h2 => sqT_pre 20 t (by simp only [Wg] at h2; omega)
            H_ACK := fun j t h1 h2 => sqT_phase 20 j t (by simp only [Wg] at h1; omega)
              (by simp only [Wg] at h2; omega)
            H_SND := fun j => by rw [τ0_g]; show 8 + 10 * j + 6 ≤ 6 + 10 * (j + 1); omega
            H_RCV := fun j => by
              rw [show Wg.N - 1 = 1 from rfl, τ1_g]; show 12 + 10 * j + 6 ≤ 20 + 10 * j; omega
            H_RST_EARLY := by show 6 ≤ 6 + 10 * 0; omega }
  · exact { H_N_POS := by decide
            H_R_POS := by decide
            H_RST_LONG := fun _ _ => by show 3 + 1 ≤ 6; omega
            H_RST_LINES := fun _ _ => by show 3 + 3 ≤ 6 ∧ 3 + 3 ≤ 6 ∧ 0 ≤ 6; omega
            H_LAT := fun i _ => by
              have := ER_g i; have := EA_g i
              show 3 + 1 ≤ 1 + min (Wg.ER 6 i) (Wg.EA 6 i); omega
            H_ACK_FLUSH_W := fun i _ => by
              have := ER_g (i + 1); have := EA_g (i + 1)
              show 3 < 1 + max (Wg.ER 6 (i + 1)) (Wg.EA 6 (i + 1)) + 1; omega }
  · intro h
    have := h 12 22 true 13 14 (by decide)
      (fun s h1 h2 => by show sqT (8 + 4 * 1) s = true; exact sqT_phase 12 0 s (by omega) (by omega))
      (by decide) (by decide) (by decide) (by decide) (by decide)
    exact absurd this (by decide)
  · intro h
    have := h 14 (by rw [hA1]; omega) (by rw [hA2]; omega)
    exact absurd this (by decide)
  · intro r hr H
    have a := H 13 (by omega); have b := H 14 (by omega)
    have m := r.mono 13 14 (by omega); have l := r.le 14
    have y13 : Wg.Y 1 0 13 = true := by decide
    have y14 : Wg.Y 1 0 14 = false := by decide
    rw [y13] at a; rw [y14] at b
    have g : 12 ≤ r.σ 13 := by
      apply Classical.byContradiction; intro hn
      rw [show Wg.O 1 (r.σ 13) = false from sqT_pre 12 _ (by omega)] at a; cases a
    rw [show Wg.O 1 (r.σ 14) = true from sqT_phase 12 0 _ (by omega) (by omega)] at b; cases b

end Wg

end Formal.Cells.WinFifoN
