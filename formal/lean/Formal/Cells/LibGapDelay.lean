/-!
# LibGapDelay: `bd_delay_gated`'s flush (H_GFLUSH), per pin, sufficient AND necessary

Probe Bdg (shard B, library gap). `bd_delay_gated` (`cells/rtl/bd_latch.v`) is
the matched delay of every generated unit of gcd_hw (29 instances, N = 12..94).
Before this file its JSON row `bd_delay_gated.gate` was proved **sufficient
only** (`GcdCells.no_early`, FIFO read maps; `ConstraintsFastFall`, window
model), with one failing run (`GcdCells.flush_needed`) but no general necessity.

## The cell, as bdc instantiates it (same indexing as `GcdCells`)

    s 0      = uor(gate)                 LUT1 INIT 2 (buffer), the anchor
    s 1      = g[0](s 0)                 LUT1 INIT 2
    s (i+1)  = g[i](s i, gate), 1 <= i   LUT2 INIT 8 = I0 AND I1
    z        = s N

## Model (named hypotheses)

* **H_PIN_READ** (per-pin box): every LUT input pin is read through its own
  read map `σ`, `σ t ∈ [t - hi, t - lo]` (`Win`; wire + site pin + that pin's
  arc to the output). The box `Box` gives `[lo, hi]` for the uor pin (`r0`),
  g[0]'s pin (`r1`), and per stage `i >= 1` the chain pin `p i` (`g[i].I0`)
  and the tap pin `q i` (`g[i].I1`). Read maps need NOT be monotone (no FIFO
  assumption): strictly more behaviours than `GcdCells` (FIFO `Ret`).
* **H_GATE_PULSE**: the gate is high before `F` (the previous token: the chain
  was full), low on `[F, T)`, high from `T` (`gate F T`). `Line` determines
  the trace (`line_unique`: every trace of the line is `run`), so the
  theorems are stated on `run`.

## Spec: what correct behaviour of a gated delay line is

* `fresh T`: the gate with the previous token erased (low before `T`, high
  from `T`). `run (fresh T)` is the line's response to the new token alone.
* **`Flushed`** (no stale pulse): from the fast-fall point `F + Vd N`
  (`= F + (q (N-1)).hi`, one tap read after the gate fell) on, `z` equals the
  response to the new token alone: nothing of the previous token reaches `z`.
* **`NoEarly`** (no early request): from `F + Vd N` on, `z` is high only at or
  after `T + Llo N`, the FULL matched length (sum of the chain's LOWER bounds:
  what rule A compares the data cone against) after the gate rose.
  `fresh_late`: the new-token response is never early, so Flushed ⇒ NoEarly.

**H_GFLUSH i** (`GF`, 1 <= i < N), the JSON row's inequality exactly:
stage 1: `F + r0.hi + r1.hi + (p 1).hi <= T + (q 1).lo`;
stage i >= 2: `F + (q (i-1)).hi + (p i).hi <= T + (q i).lo`.

## Results

* `flush_of_gflush` (sufficient, any read maps in the box): ∀ i, H_GFLUSH i ⇒
  Flushed. `no_early_of_gflush`: ⇒ NoEarly.
* `stale_pulse` (necessary, per stage): H_GFLUSH i false (by any amount,
  1 ps included) ⇒ at the box corner (stages <= i slow, tap i and everything
  after fast; constant delays, so even a FIFO / fixed-delay run) `z` is high
  at `t = T + (q i).lo + Pl i (N-1)` while the new-token response is low:
  a stale pulse of the previous token, passed by stage i whose tap the new
  rise already reopened. With H_SHORT it is also an early request
  (`t < T + Llo N`). Side conditions (the exact boundary of necessity):
  - **H_BAL_HI** (stages k < i): `Vd (k+1) <= Vd k + (p k).hi`: a tap's slow
    arrival is not later than the previous tap's plus one chain hop (so the
    stale value of `s i` really lives until `F + Vd i`);
  - **H_LO_ORDER** (stages k > i): `(q k).lo <= (q i).lo + Pl i k`: no later
    tap is so slow that it still reads the gate low when the pulse passes;
  - **H_START**: `F + Vd N <= t` (the pulse is after the fast-fall point);
  - (NoEarly only) **H_SHORT**: `(q i).lo < Llo (i+1)` (the tap path is
    shorter than the chain path to stage i+1).
* `box_exact_flushed`, `box_exact_no_early` (headline): under those side
  conditions at every stage, `Flushed` (resp. `NoEarly`) for EVERY read map
  tuple in the box **iff** H_GFLUSH i for every `1 <= i < N`.
* `rescue_*`: the side conditions are needed: N = 3 fixed delays, H_GFLUSH 1
  false, H_LO_ORDER false (tap 2 slower than tap 1 + chain hop), and still
  Flushed and NoEarly for every map in the box: the slow tap 2 covers stage 1's
  hole. So per-stage H_GFLUSH is NOT necessary in general (Blt's caveat).
* `real_*` (non-vacuity, SLOW corner, prjxray LUT arc (100, 124) ps; wires
  assumed, see the note): N = 12, gate low phase 900 ps meets every
  hypothesis (stage 1 binding, slack 0): Flushed and NoEarly for every map; z
  falls at 624 and rises at 6180 at the slow corner. 899 ps (H_GFLUSH 1 short
  by 1 ps): `stale_pulse` gives z high at 4499 ps < 5119 = T + Llo 12, an early
  request 620 ps before the matched length.

NOT covered: the data the request bundles (rule A on the compute cone);
glitch-freedom of the new token's rising edge itself (with non-monotone maps
the AND can bounce inside `[T + Llo, T + Lhi)`; `Flushed` says only that any
such bounce is the new token's, not the old one's; FIFO maps rule it out,
`GcdCells.rises`); the gate's own waveform (H_GATE_PULSE: the gate is the
join / arbiter node, its low phase is a return-to-zero); correlated corners:
the box form is the box corner (always sound); necessity uses corner values
of independent pins.

Core Lean only (no imports); no sorry, no declared axiom, no native code.
-/

namespace Formal.Cells.LibGapDelay

/-! ## 1. Model -/

/-- Per-pin delay box: `[lo, hi]` for each pin (H_PIN_READ). -/
structure Box where
  r0l : Int
  r0h : Int
  r1l : Int
  r1h : Int
  pl : Nat → Int
  ph : Nat → Int
  ql : Nat → Int
  qh : Nat → Int

/-- A read map inside the window `[lo, hi]`: at `t` the pin shows its driver at
`σ t ∈ [t - hi, t - lo]`. No monotonicity. -/
def Win (lo hi : Int) (σ : Int → Int) : Prop := ∀ t, t - hi ≤ σ t ∧ σ t ≤ t - lo

/-- Every pin's read map lies in its box window. -/
structure Fits (B : Box) (r0 r1 : Int → Int) (p q : Nat → Int → Int) : Prop where
  w0 : Win B.r0l B.r0h r0
  w1 : Win B.r1l B.r1h r1
  wp : ∀ i, Win (B.pl i) (B.ph i) (p i)
  wq : ∀ i, Win (B.ql i) (B.qh i) (q i)

/-- The box is well formed (`lo <= hi`). -/
def WF (B : Box) : Prop :=
  B.r0l ≤ B.r0h ∧ B.r1l ≤ B.r1h ∧ ∀ i, B.pl i ≤ B.ph i ∧ B.ql i ≤ B.qh i

/-- **The gated line, per pin** (the real INITs: LUT1 `2'h2` = buffer, LUT2
`4'h8` = AND). -/
structure Line (g : Int → Bool) (s : Nat → Int → Bool) (r0 r1 : Int → Int)
    (p q : Nat → Int → Int) : Prop where
  h0 : ∀ t, s 0 t = g (r0 t)
  h1 : ∀ t, s 1 t = s 0 (r1 t)
  hs : ∀ i, 1 ≤ i → ∀ t, s (i + 1) t = (s i (p i t) && g (q i t))

/-- The unique trace of the line (Line determines `s`). -/
def run (g : Int → Bool) (r0 r1 : Int → Int) (p q : Nat → Int → Int) : Nat → Int → Bool
  | 0 => fun t => g (r0 t)
  | 1 => fun t => g (r0 (r1 t))
  | k + 2 => fun t => run g r0 r1 p q (k + 1) (p (k + 1) t) && g (q (k + 1) t)

theorem run_line (g : Int → Bool) (r0 r1 : Int → Int) (p q : Nat → Int → Int) :
    Line g (run g r0 r1 p q) r0 r1 p q where
  h0 _ := rfl
  h1 _ := rfl
  hs i hi t := by
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    rfl

/-- Any trace of the line is `run`. -/
theorem line_unique {g : Int → Bool} {s : Nat → Int → Bool} {r0 r1 : Int → Int}
    {p q : Nat → Int → Int} (L : Line g s r0 r1 p q) : ∀ i t, s i t = run g r0 r1 p q i t := by
  intro i
  induction i with
  | zero => intro t; exact L.h0 t
  | succ i ih =>
    intro t
    cases i with
    | zero => rw [L.h1, ih]; rfl
    | succ k => rw [L.hs (k + 1) (by omega), ih]; rfl

/-- **H_GATE_PULSE**: high before `F` (previous token), low on `[F, T)`, high from `T`. -/
def gate (F T : Int) (u : Int) : Bool := !decide (F ≤ u ∧ u < T)

/-- The gate with the previous token erased: only the new token's rise at `T`. -/
def fresh (T : Int) (u : Int) : Bool := decide (T ≤ u)

theorem gate_lt {F T x : Int} (h : x < F) : gate F T x = true := by
  unfold gate; simp; omega
theorem gate_ge {F T x : Int} (h : T ≤ x) : gate F T x = true := by
  unfold gate; simp; omega
theorem gate_imp {F T x : Int} (h : gate F T x = true) (hx : F ≤ x) : T ≤ x := by
  unfold gate at h; simp at h; omega
theorem fresh_lt {T x : Int} (h : x < T) : fresh T x = false := by
  unfold fresh; simp; omega
theorem fresh_ge {T x : Int} (h : T ≤ x) : fresh T x = true := by
  unfold fresh; simp; omega
theorem fresh_imp {T x : Int} (h : fresh T x = true) : T ≤ x := by
  unfold fresh at h; simp at h; omega

/-- Full matched length to stage `i`: the sum of the chain's LOWER bounds. -/
def Llo (B : Box) : Nat → Int
  | 0 => B.r0l
  | 1 => B.r0l + B.r1l
  | k + 2 => Llo B (k + 1) + B.pl (k + 1)

/-- After `F + Vd i` stage `i` no longer shows the previous token for sure
(`GcdCells.V`, slow bounds): the head for stages 0, 1; tap `i-1` for `i >= 2`. -/
def Vd (B : Box) : Nat → Int
  | 0 => B.r0h
  | 1 => B.r0h + B.r1h
  | k + 2 => B.qh (k + 1)

/-- **H_GFLUSH i**: the stale value of stage `i` is gone from `g[i]`'s chain
pin before the new gate rise reaches its tap pin. -/
def GF (B : Box) (F T : Int) (i : Nat) : Prop := F + Vd B i + B.ph i ≤ T + B.ql i

instance (B : Box) (F T : Int) (i : Nat) : Decidable (GF B F T i) := by
  unfold GF; infer_instance

/-- **Spec 1 (no stale pulse).** From the fast-fall point on, `z` is the
response to the new token alone. -/
def Flushed (B : Box) (F : Int) (N : Nat) (z z' : Int → Bool) : Prop :=
  ∀ t, F + Vd B N ≤ t → z t = z' t

/-- **Spec 2 (no early request).** From the fast-fall point on, `z` is high
only at or after the full matched length after the gate rise. -/
def NoEarly (B : Box) (F T : Int) (N : Nat) (z : Int → Bool) : Prop :=
  ∀ t, F + Vd B N ≤ t → z t = true → T + Llo B N ≤ t

/-! ## 2. Sufficient (any read maps in the box) -/

section suff
variable {B : Box} {r0 r1 : Int → Int} {p q : Nat → Int → Int}

/-- The new token's response is never early (no hypothesis). -/
theorem fresh_late (hB : Fits B r0 r1 p q) (T : Int) :
    ∀ i u, run (fresh T) r0 r1 p q i u = true → T + Llo B i ≤ u := by
  intro i
  induction i with
  | zero =>
    intro u h
    have := fresh_imp h; have := (hB.w0 u).2
    show T + B.r0l ≤ u; omega
  | succ i ih =>
    intro u h
    cases i with
    | zero =>
      have := fresh_imp h; have := (hB.w0 (r1 u)).2; have := (hB.w1 u).2
      show T + (B.r0l + B.r1l) ≤ u; omega
    | succ k =>
      have h' : (run (fresh T) r0 r1 p q (k + 1) (p (k + 1) u) && fresh T (q (k + 1) u)) = true := h
      simp only [Bool.and_eq_true] at h'
      have := ih _ h'.1; have := (hB.wp (k + 1) u).2
      show T + (Llo B (k + 1) + B.pl (k + 1)) ≤ u; omega

/-- The new token's response is part of the real one (the real gate is high
wherever `fresh` is). -/
theorem fresh_le_real (F T : Int) :
    ∀ i u, run (fresh T) r0 r1 p q i u = true → run (gate F T) r0 r1 p q i u = true := by
  intro i
  induction i with
  | zero => intro u h; exact gate_ge (fresh_imp h)
  | succ i ih =>
    intro u h
    cases i with
    | zero => exact gate_ge (fresh_imp h)
    | succ k =>
      have h' : (run (fresh T) r0 r1 p q (k + 1) (p (k + 1) u) && fresh T (q (k + 1) u)) = true := h
      simp only [Bool.and_eq_true] at h'
      show (run (gate F T) r0 r1 p q (k + 1) (p (k + 1) u) && gate F T (q (k + 1) u)) = true
      rw [ih _ h'.1, gate_ge (fresh_imp h'.2)]; rfl

/-- **Per stage, H_GFLUSH flushes.** From `F + Vd i` on, a high at stage `i` is
the new token's. -/
theorem stale_free (hB : Fits B r0 r1 p q) (N : Nat) (F T : Int)
    (H_GFLUSH : ∀ i, 1 ≤ i → i < N → GF B F T i) :
    ∀ i, i ≤ N → ∀ u, F + Vd B i ≤ u → run (gate F T) r0 r1 p q i u = true →
      run (fresh T) r0 r1 p q i u = true := by
  intro i
  induction i with
  | zero =>
    intro _ u hu h
    have := (hB.w0 u).1
    have hu' : F + B.r0h ≤ u := hu
    exact fresh_ge (gate_imp h (by omega))
  | succ i ih =>
    intro hiN u hu h
    cases i with
    | zero =>
      have := (hB.w1 u).1
      have hu' : F + (B.r0h + B.r1h) ≤ u := hu
      exact ih (by omega) (r1 u) (by show F + B.r0h ≤ r1 u; omega) h
    | succ k =>
      have h' : (run (gate F T) r0 r1 p q (k + 1) (p (k + 1) u) && gate F T (q (k + 1) u)) = true := h
      simp only [Bool.and_eq_true] at h'
      have hu' : F + B.qh (k + 1) ≤ u := hu
      have wq := hB.wq (k + 1) u; have wp := hB.wp (k + 1) u
      have hT : T ≤ q (k + 1) u := gate_imp h'.2 (by omega)
      show (run (fresh T) r0 r1 p q (k + 1) (p (k + 1) u) && fresh T (q (k + 1) u)) = true
      rw [fresh_ge hT]
      rcases Int.lt_or_le (p (k + 1) u) (F + Vd B (k + 1)) with c | c
      · -- the chain pin still reads the stale stage: the tap read the gate low
        have := H_GFLUSH (k + 1) (by omega) (by omega)
        unfold GF at this; omega
      · rw [ih (by omega) _ c h'.1]; rfl

/-- **Sufficient: H_GFLUSH ⇒ no stale pulse.** -/
theorem flush_of_gflush (hB : Fits B r0 r1 p q) (N : Nat) (F T : Int)
    (H_GFLUSH : ∀ i, 1 ≤ i → i < N → GF B F T i) :
    Flushed B F N (run (gate F T) r0 r1 p q N) (run (fresh T) r0 r1 p q N) := by
  intro t ht
  cases h : run (gate F T) r0 r1 p q N t with
  | true => exact (stale_free hB N F T H_GFLUSH N (Nat.le_refl _) t ht h).symm
  | false =>
    cases h' : run (fresh T) r0 r1 p q N t with
    | false => rfl
    | true => rw [fresh_le_real F T N t h'] at h; exact Bool.noConfusion h

/-- **Sufficient: H_GFLUSH ⇒ no early request.** -/
theorem no_early_of_gflush (hB : Fits B r0 r1 p q) (N : Nat) (F T : Int)
    (H_GFLUSH : ∀ i, 1 ≤ i → i < N → GF B F T i) :
    NoEarly B F T N (run (gate F T) r0 r1 p q N) := by
  intro t ht h
  rw [flush_of_gflush hB N F T H_GFLUSH t ht] at h
  exact fresh_late hB T N t h

end suff

/-! ## 3. Necessary, per stage (box corner) -/

/-- A fixed transport delay. -/
def cm (d : Int) : Int → Int := fun t => t - d

/-- Corner for stage `i`: chain pins up to `i` slow, after `i` fast. -/
def cP (B : Box) (i k : Nat) : Int → Int := cm (if k ≤ i then B.ph k else B.pl k)
/-- Corner for stage `i`: taps before `i` slow, from `i` on fast. -/
def cQ (B : Box) (i k : Nat) : Int → Int := cm (if k < i then B.qh k else B.ql k)

theorem cP_le {B : Box} {i k : Nat} (h : k ≤ i) (u : Int) : cP B i k u = u - B.ph k := by
  simp [cP, cm, h]
theorem cP_gt {B : Box} {i k : Nat} (h : i < k) (u : Int) : cP B i k u = u - B.pl k := by
  have h' : ¬ k ≤ i := by omega
  simp [cP, cm, h']
theorem cQ_lt {B : Box} {i k : Nat} (h : k < i) (u : Int) : cQ B i k u = u - B.qh k := by
  simp [cQ, cm, h]
theorem cQ_ge {B : Box} {i k : Nat} (h : i ≤ k) (u : Int) : cQ B i k u = u - B.ql k := by
  have h' : ¬ k < i := by omega
  simp [cQ, cm, h']

theorem win_cm {lo hi d : Int} (h1 : lo ≤ d) (h2 : d ≤ hi) : Win lo hi (cm d) := by
  intro t; simp [cm]; omega

theorem fits_corner {B : Box} (H_WF : WF B) (i : Nat) :
    Fits B (cm B.r0h) (cm B.r1h) (cP B i) (cQ B i) where
  w0 := win_cm H_WF.1 (Int.le_refl _)
  w1 := win_cm H_WF.2.1 (Int.le_refl _)
  wp k := by
    have := (H_WF.2.2 k).1
    unfold cP; split
    · exact win_cm this (Int.le_refl _)
    · exact win_cm (Int.le_refl _) this
  wq k := by
    have := (H_WF.2.2 k).2
    unfold cQ; split
    · exact win_cm this (Int.le_refl _)
    · exact win_cm (Int.le_refl _) this

/-- Lower-bound sum of the chain pins `i+1 .. k`. -/
def Pl (B : Box) (i : Nat) : Nat → Int
  | 0 => 0
  | k + 1 => if k + 1 ≤ i then 0 else Pl B i k + B.pl (k + 1)

theorem Pl_self (B : Box) (i : Nat) : Pl B i i = 0 := by
  cases i with
  | zero => rfl
  | succ j => simp [Pl]

theorem Pl_succ (B : Box) {i k : Nat} (h : i ≤ k) : Pl B i (k + 1) = Pl B i k + B.pl (k + 1) := by
  have h' : ¬ k + 1 ≤ i := by omega
  simp [Pl, h']

theorem Llo_split (B : Box) {i : Nat} (_hi : 1 ≤ i) :
    ∀ d, Llo B (i + d + 1) = Llo B (i + 1) + Pl B i (i + d) := by
  intro d
  induction d with
  | zero => simp [Pl_self]
  | succ d ih =>
    have e : i + (d + 1) + 1 = (i + d) + 2 := by omega
    have e2 : i + (d + 1) = (i + d) + 1 := by omega
    rw [e, e2, Pl_succ B (by omega)]
    show Llo B (i + d + 1) + B.pl (i + d + 1) = _
    rw [ih]; omega

section nec
variable (B : Box) (F T : Int) (i : Nat)


/-- At the corner the previous token survives at stage `k <= i` until `F + Vd k`. -/
theorem corner_stale
    (H_BAL_HI : ∀ k, 1 ≤ k → k < i → Vd B (k + 1) ≤ Vd B k + B.ph k) :
    ∀ k, k ≤ i → ∀ u, u < F + Vd B k → run (gate F T) (cm B.r0h) (cm B.r1h) (cP B i) (cQ B i) k u = true := by
  intro k
  induction k with
  | zero =>
    intro _ u hu
    exact gate_lt (by show u - B.r0h < F; have : u < F + B.r0h := hu; omega)
  | succ k ih =>
    intro hk u hu
    cases k with
    | zero =>
      exact gate_lt (by show u - B.r1h - B.r0h < F; have : u < F + (B.r0h + B.r1h) := hu; omega)
    | succ j =>
      have hu' : u < F + B.qh (j + 1) := hu
      show (run (gate F T) (cm B.r0h) (cm B.r1h) (cP B i) (cQ B i) (j + 1) (cP B i (j + 1) u) && gate F T (cQ B i (j + 1) u)) = true
      rw [cP_le (by omega), cQ_lt (by omega), gate_lt (by omega)]
      have := H_BAL_HI (j + 1) (by omega) (by omega)
      have hv : u - B.ph (j + 1) < F + Vd B (j + 1) := by
        have : Vd B (j + 1 + 1) = B.qh (j + 1) := rfl
        omega
      rw [ih (by omega) _ hv]; rfl

/-- ... and the new token's response is low there (the gate fell before it rose). -/
theorem corner_stale' (hFT : F < T) :
    ∀ k, k ≤ i → ∀ u, u < F + Vd B k → run (fresh T) (cm B.r0h) (cm B.r1h) (cP B i) (cQ B i) k u = false := by
  intro k
  induction k with
  | zero =>
    intro _ u hu
    exact fresh_lt (by show u - B.r0h < T; have : u < F + B.r0h := hu; omega)
  | succ k _ =>
    intro hk u hu
    cases k with
    | zero =>
      exact fresh_lt (by show u - B.r1h - B.r0h < T; have : u < F + (B.r0h + B.r1h) := hu; omega)
    | succ j =>
      have hu' : u < F + B.qh (j + 1) := hu
      show (run (fresh T) (cm B.r0h) (cm B.r1h) (cP B i) (cQ B i) (j + 1) (cP B i (j + 1) u) && fresh T (cQ B i (j + 1) u)) = false
      rw [cQ_lt (by omega), fresh_lt (by omega)]; simp

/-- The stale pulse travels down the fast part of the chain. -/
theorem corner_down (hFT : F < T) (hi1 : 1 ≤ i) (N : Nat) (hbad : ¬ GF B F T i)
    (H_BAL_HI : ∀ k, 1 ≤ k → k < i → Vd B (k + 1) ≤ Vd B k + B.ph k)
    (H_LO_ORDER : ∀ k, i < k → k < N → B.ql k ≤ B.ql i + Pl B i k) :
    ∀ d, i + d < N →
      run (gate F T) (cm B.r0h) (cm B.r1h) (cP B i) (cQ B i) (i + d + 1) (T + B.ql i + Pl B i (i + d)) = true ∧
      run (fresh T) (cm B.r0h) (cm B.r1h) (cP B i) (cQ B i) (i + d + 1) (T + B.ql i + Pl B i (i + d)) = false := by
  unfold GF at hbad
  intro d
  induction d with
  | zero =>
    intro _
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    simp only [Nat.add_zero, Pl_self]
    have hv : T + B.ql (j + 1) + 0 - B.ph (j + 1) < F + Vd B (j + 1) := by omega
    refine ⟨?_, ?_⟩
    · show (run (gate F T) (cm B.r0h) (cm B.r1h) (cP B (j + 1)) (cQ B (j + 1)) (j + 1) (cP B (j + 1) (j + 1) _) &&
          gate F T (cQ B (j + 1) (j + 1) _)) = true
      rw [cP_le (Nat.le_refl _), cQ_ge (Nat.le_refl _),
        corner_stale B F T (j + 1) H_BAL_HI (j + 1) (Nat.le_refl _) _ hv,
        gate_ge (by omega)]; rfl
    · show (run (fresh T) (cm B.r0h) (cm B.r1h) (cP B (j + 1)) (cQ B (j + 1)) (j + 1) (cP B (j + 1) (j + 1) _) &&
          fresh T (cQ B (j + 1) (j + 1) _)) = false
      rw [cP_le (Nat.le_refl _), corner_stale' B F T (j + 1) hFT (j + 1) (Nat.le_refl _) _ hv]
      rfl
  | succ d ih =>
    intro hd
    obtain ⟨h1, h2⟩ := ih (by omega)
    have e : i + (d + 1) + 1 = (i + d + 1) + 1 := by omega
    have e2 : i + (d + 1) = (i + d) + 1 := by omega
    rw [e, e2, Pl_succ B (by omega)]
    have hlo := H_LO_ORDER (i + d + 1) (by omega) (by omega)
    rw [Pl_succ B (by omega)] at hlo
    have hk : 1 ≤ i + d + 1 := by omega
    rw [(run_line _ _ _ _ _).hs _ hk, (run_line _ _ _ _ _).hs _ hk]
    rw [cP_gt (by omega), cQ_ge (by omega)]
    have ev : T + B.ql i + (Pl B i (i + d) + B.pl (i + d + 1)) - B.pl (i + d + 1) =
        T + B.ql i + Pl B i (i + d) := by omega
    rw [ev, h1, h2, gate_ge (by omega)]
    exact ⟨rfl, by simp⟩

/-- **Necessary, per stage: a stale pulse.** H_GFLUSH i false (by any amount,
1 ps included): at the corner (in the box) `z` is high at
`t = T + (q i).lo + Pl i (N-1)`, after the fast-fall point, while the new
token's response is low there. -/
theorem stale_pulse (H_WF : WF B) (hFT : F < T) (N : Nat) (hi1 : 1 ≤ i) (hiN : i < N)
    (hbad : ¬ GF B F T i)
    (H_BAL_HI : ∀ k, 1 ≤ k → k < i → Vd B (k + 1) ≤ Vd B k + B.ph k)
    (H_LO_ORDER : ∀ k, i < k → k < N → B.ql k ≤ B.ql i + Pl B i k)
    (H_START : F + Vd B N ≤ T + B.ql i + Pl B i (N - 1)) :
    Fits B (cm B.r0h) (cm B.r1h) (cP B i) (cQ B i) ∧
    F + Vd B N ≤ T + B.ql i + Pl B i (N - 1) ∧
    run (gate F T) (cm B.r0h) (cm B.r1h) (cP B i) (cQ B i) N (T + B.ql i + Pl B i (N - 1)) = true ∧
    run (fresh T) (cm B.r0h) (cm B.r1h) (cP B i) (cQ B i) N (T + B.ql i + Pl B i (N - 1)) = false := by
  have h := corner_down B F T i hFT hi1 N hbad H_BAL_HI H_LO_ORDER (N - 1 - i) (by omega)
  have e1 : i + (N - 1 - i) + 1 = N := by omega
  have e2 : i + (N - 1 - i) = N - 1 := by omega
  rw [e1, e2] at h
  exact ⟨fits_corner H_WF i, H_START, h.1, h.2⟩

/-- With **H_SHORT** the stale pulse is an early request. -/
theorem stale_pulse_early (hi1 : 1 ≤ i) (N : Nat) (hiN : i < N)
    (H_SHORT : B.ql i < Llo B (i + 1)) :
    T + B.ql i + Pl B i (N - 1) < T + Llo B N := by
  have := Llo_split B hi1 (N - 1 - i)
  have e1 : i + (N - 1 - i) + 1 = N := by omega
  have e2 : i + (N - 1 - i) = N - 1 := by omega
  rw [e1, e2] at this; omega

end nec

/-! ## 4. Exact over the box -/

/-- **Box-exact (no stale pulse).** Under the side conditions at every
stage, the line is Flushed for EVERY read-map tuple in the box iff
H_GFLUSH holds at every stage. -/
theorem box_exact_flushed (B : Box) (F T : Int) (N : Nat) (H_WF : WF B) (hFT : F < T)
    (H_BAL_HI : ∀ k, 1 ≤ k → k + 1 < N → Vd B (k + 1) ≤ Vd B k + B.ph k)
    (H_LO_ORDER : ∀ i k, 1 ≤ i → i < k → k < N → B.ql k ≤ B.ql i + Pl B i k)
    (H_START : ∀ i, 1 ≤ i → i < N → F + Vd B N ≤ T + B.ql i + Pl B i (N - 1)) :
    (∀ r0 r1 p q, Fits B r0 r1 p q →
        Flushed B F N (run (gate F T) r0 r1 p q N) (run (fresh T) r0 r1 p q N)) ↔
      (∀ i, 1 ≤ i → i < N → GF B F T i) := by
  constructor
  · intro hall i hi1 hiN
    by_cases hg : GF B F T i
    · exact hg
    · exfalso
      obtain ⟨hf, hs, h1, h2⟩ := stale_pulse B F T i H_WF hFT N hi1 hiN hg
        (fun k a b => H_BAL_HI k a (by omega)) (fun k a b => H_LO_ORDER i k hi1 a b)
        (H_START i hi1 hiN)
      have := hall _ _ _ _ hf _ hs
      rw [h1, h2] at this; exact Bool.noConfusion this
  · intro hg r0 r1 p q hf
    exact flush_of_gflush hf N F T hg

/-- **Box-exact (no early request)**, with H_SHORT added. -/
theorem box_exact_no_early (B : Box) (F T : Int) (N : Nat) (H_WF : WF B) (hFT : F < T)
    (H_BAL_HI : ∀ k, 1 ≤ k → k + 1 < N → Vd B (k + 1) ≤ Vd B k + B.ph k)
    (H_LO_ORDER : ∀ i k, 1 ≤ i → i < k → k < N → B.ql k ≤ B.ql i + Pl B i k)
    (H_START : ∀ i, 1 ≤ i → i < N → F + Vd B N ≤ T + B.ql i + Pl B i (N - 1))
    (H_SHORT : ∀ i, 1 ≤ i → i < N → B.ql i < Llo B (i + 1)) :
    (∀ r0 r1 p q, Fits B r0 r1 p q → NoEarly B F T N (run (gate F T) r0 r1 p q N)) ↔
      (∀ i, 1 ≤ i → i < N → GF B F T i) := by
  constructor
  · intro hall i hi1 hiN
    by_cases hg : GF B F T i
    · exact hg
    · exfalso
      obtain ⟨hf, hs, h1, _⟩ := stale_pulse B F T i H_WF hFT N hi1 hiN hg
        (fun k a b => H_BAL_HI k a (by omega)) (fun k a b => H_LO_ORDER i k hi1 a b)
        (H_START i hi1 hiN)
      have := hall _ _ _ _ hf _ hs h1
      have := stale_pulse_early B T i hi1 N hiN (H_SHORT i hi1 hiN)
      omega
  · intro hg r0 r1 p q hf
    exact no_early_of_gflush hf N F T hg

/-- Flushed ⇒ NoEarly (any read maps in the box). -/
theorem noEarly_of_flushed {B : Box} {r0 r1 : Int → Int} {p q : Nat → Int → Int}
    (hB : Fits B r0 r1 p q) (F T : Int) (N : Nat)
    (h : Flushed B F N (run (gate F T) r0 r1 p q N) (run (fresh T) r0 r1 p q N)) :
    NoEarly B F T N (run (gate F T) r0 r1 p q N) := by
  intro t ht hz
  rw [h t ht] at hz
  exact fresh_late hB T N t hz

theorem gate_in {F T x : Int} (h1 : F ≤ x) (h2 : x < T) : gate F T x = false := by
  unfold gate; simp; omega

/-! ## 5. The side conditions are needed: a slow tap rescues stage 1

N = 3, fixed delays (`lo = hi`), gate low on `[0, 10)`. Stage 1 fails
H_GFLUSH (`0 + 20 + 5 = 25 > 20 = 10 + 10`), and H_LO_ORDER fails (tap 2,
28, is slower than tap 1 + chain hop 2, 20). Unrolled,
`z t = g (t - 35) && g (t - 20) && g (t - 28)`: the hole `[30, 35)` of
stage 1's flush is covered by tap 2's read of the low gate. Flushed and
NoEarly hold for every map in the box. -/

def Bres : Box where
  r0l := 10
  r0h := 10
  r1l := 10
  r1h := 10
  pl k := if k = 1 then 5 else 10
  ph k := if k = 1 then 5 else 10
  ql k := if k = 2 then 28 else 10
  qh k := if k = 2 then 28 else 10

theorem rescue_hyps : WF Bres ∧ ¬ GF Bres 0 10 1 ∧ GF Bres 0 10 2 ∧
    ¬ (Bres.ql 2 ≤ Bres.ql 1 + Pl Bres 1 2) := by
  refine ⟨⟨by decide, by decide, fun k => ?_⟩, by decide, by decide, by decide⟩
  simp only [Bres]; constructor <;> split <;> decide

theorem win_eq {d : Int} {σ : Int → Int} (h : Win d d σ) (t : Int) : σ t = t - d := by
  have := h t; omega

theorem rescue_flushed (r0 r1 : Int → Int) (p q : Nat → Int → Int) (hf : Fits Bres r0 r1 p q) :
    Flushed Bres 0 3 (run (gate 0 10) r0 r1 p q 3) (run (fresh 10) r0 r1 p q 3) := by
  have e0 := win_eq hf.w0; have e1 := win_eq hf.w1
  have ep1 := win_eq (hf.wp 1); have ep2 := win_eq (hf.wp 2)
  have eq1 := win_eq (hf.wq 1); have eq2 := win_eq (hf.wq 2)
  simp only [Bres] at e0 e1 ep1 ep2 eq1 eq2
  simp only [ite_true, ite_false, show (2 : Nat) ≠ 1 by decide, show (1 : Nat) ≠ 2 by decide] at ep1 ep2 eq1 eq2
  intro t ht
  have ht' : 28 ≤ t := by
    have : Vd Bres 3 = 28 := rfl
    omega
  show ((gate 0 10 (r0 (r1 (p 1 (p 2 t)))) && gate 0 10 (q 1 (p 2 t))) && gate 0 10 (q 2 t)) =
    ((fresh 10 (r0 (r1 (p 1 (p 2 t)))) && fresh 10 (q 1 (p 2 t))) && fresh 10 (q 2 t))
  rw [eq2, ep2, eq1, ep1, e1, e0]
  rcases Int.lt_or_le t 38 with c | c
  · rw [gate_in (x := t - 28) (by omega) (by omega), fresh_lt (x := t - 10 - 5 - 10 - 10) (by omega)]
    simp
  · rcases Int.lt_or_le t 45 with c' | c'
    · rw [gate_in (x := t - 10 - 5 - 10 - 10) (by omega) (by omega),
        fresh_lt (x := t - 10 - 5 - 10 - 10) (by omega)]
      simp
    · rw [gate_ge (x := t - 10 - 5 - 10 - 10) (by omega), gate_ge (x := t - 10 - 10) (by omega),
        gate_ge (x := t - 28) (by omega), fresh_ge (x := t - 10 - 5 - 10 - 10) (by omega),
        fresh_ge (x := t - 10 - 10) (by omega), fresh_ge (x := t - 28) (by omega)]

theorem rescue_no_early (r0 r1 : Int → Int) (p q : Nat → Int → Int) (hf : Fits Bres r0 r1 p q) :
    NoEarly Bres 0 10 3 (run (gate 0 10) r0 r1 p q 3) :=
  noEarly_of_flushed hf 0 10 3 (rescue_flushed r0 r1 p q hf)

/-! ## 6. Non-vacuity on realistic numbers (SLOW corner, one corner)

ps, prjxray SLOW corner only (SLOW_MIN..SLOW_MAX), N = 12 (bdc's smallest
gated line). LUT arc (100, 124) (prjxray-db slicel IOPATH, every pin, C-10c).
Wires (assumed, not routed): chain hop in-slice 210..264 (C-10c hand check:
264 slow_max for a 3-pip in-slice hop), gate net (high fanout: uor and every
tap) 400..500. So per pin, wire + arc: `r0 = q i = [500, 624]`,
`r1 = p i = [310, 388]`. H_GFLUSH 1: `T - F >= 624 + 388 + 388 - 500 = 900`;
stage i >= 2: `T - F >= 624 + 388 - 500 = 512`. -/

def Bx : Box where
  r0l := 500
  r0h := 624
  r1l := 310
  r1h := 388
  pl _ := 310
  ph _ := 388
  ql _ := 500
  qh _ := 624

theorem Bx_wf : WF Bx :=
  ⟨by decide, by decide, fun _ => ⟨show (310 : Int) ≤ 388 by decide, show (500 : Int) ≤ 624 by decide⟩⟩

theorem Bx_bal_hi : ∀ k, 1 ≤ k → k + 1 < 12 → Vd Bx (k + 1) ≤ Vd Bx k + Bx.ph k := by
  have h : ∀ k, k < 12 → (1 ≤ k → k + 1 < 12 → Vd Bx (k + 1) ≤ Vd Bx k + Bx.ph k) := by decide
  intro k a b; exact h k (by omega) a b

theorem Bx_lo_order : ∀ i k, 1 ≤ i → i < k → k < 12 → Bx.ql k ≤ Bx.ql i + Pl Bx i k := by
  have h : ∀ i, i < 12 → ∀ k, k < 12 → (1 ≤ i → i < k → Bx.ql k ≤ Bx.ql i + Pl Bx i k) := by decide
  intro i k a b c; exact h i (by omega) k c a b

theorem Bx_start (T : Int) (hT : 124 ≤ T) :
    ∀ i, 1 ≤ i → i < 12 → 0 + Vd Bx 12 ≤ T + Bx.ql i + Pl Bx i (12 - 1) := by
  have h : ∀ i, i < 12 → (1 ≤ i → (0 : Int) ≤ Pl Bx i 11) := by decide
  intro i a b
  have := h i b a
  have : Vd Bx 12 = 624 := rfl
  have : Bx.ql i = 500 := rfl
  show 0 + Vd Bx 12 ≤ T + Bx.ql i + Pl Bx i 11
  omega

theorem Bx_short : ∀ i, 1 ≤ i → i < 12 → Bx.ql i < Llo Bx (i + 1) := by
  have h : ∀ i, i < 12 → (1 ≤ i → Bx.ql i < Llo Bx (i + 1)) := by decide
  intro i a b; exact h i b a

/-- H_GFLUSH at every stage with a 900 ps low phase (stage 1: slack 0). -/
theorem real_gf : ∀ i, 1 ≤ i → i < 12 → GF Bx 0 900 i := by
  have h : ∀ i, i < 12 → (1 ≤ i → GF Bx 0 900 i) := by decide
  intro i a b; exact h i b a

/-- **Non-vacuity (sufficient side).** Every hypothesis of `box_exact_flushed`
and `box_exact_no_early` holds, and so does their right side: for EVERY
read-map tuple in the box, the line is Flushed and not early. -/
theorem real_ok :
    (∀ r0 r1 p q, Fits Bx r0 r1 p q →
      Flushed Bx 0 12 (run (gate 0 900) r0 r1 p q 12) (run (fresh 900) r0 r1 p q 12)) ∧
    (∀ r0 r1 p q, Fits Bx r0 r1 p q → NoEarly Bx 0 900 12 (run (gate 0 900) r0 r1 p q 12)) :=
  ⟨(box_exact_flushed Bx 0 900 12 Bx_wf (by decide) Bx_bal_hi Bx_lo_order
      (Bx_start 900 (by decide))).mpr real_gf,
   (box_exact_no_early Bx 0 900 12 Bx_wf (by decide) Bx_bal_hi Bx_lo_order
      (Bx_start 900 (by decide)) Bx_short).mpr real_gf⟩

/-- ... and the line does its job at the slow corner (all pins at SLOW_MAX):
the previous token is still out at 623, `z` falls at the fast-fall point 624
(`= F + Vd 12`), stays low, and rises at 6180 (`= 900 + 624 + 12 * 388`). -/
theorem real_rises :
    run (gate 0 900) (cm 624) (cm 388) (fun _ => cm 388) (fun _ => cm 624) 12 623 = true ∧
    run (gate 0 900) (cm 624) (cm 388) (fun _ => cm 388) (fun _ => cm 624) 12 624 = false ∧
    run (gate 0 900) (cm 624) (cm 388) (fun _ => cm 388) (fun _ => cm 624) 12 6179 = false ∧
    run (gate 0 900) (cm 624) (cm 388) (fun _ => cm 388) (fun _ => cm 624) 12 6180 = true := by
  decide

/-- **Necessity on realistic numbers, violated by 1 ps.** A 899 ps low phase:
H_GFLUSH 1 fails by 1 ps; at the stage-1 corner `z` is high at 4499 ps
while the new token's response is low there, and 4499 < 5119 = 899 + Llo 12:
an early request 620 ps before the matched length (a stale pulse of the
previous token). -/
theorem real_bad :
    ¬ GF Bx 0 899 1 ∧ GF Bx 0 900 1 ∧
    Fits Bx (cm Bx.r0h) (cm Bx.r1h) (cP Bx 1) (cQ Bx 1) ∧
    run (gate 0 899) (cm Bx.r0h) (cm Bx.r1h) (cP Bx 1) (cQ Bx 1) 12 4499 = true ∧
    run (fresh 899) (cm Bx.r0h) (cm Bx.r1h) (cP Bx 1) (cQ Bx 1) 12 4499 = false ∧
    0 + Vd Bx 12 ≤ 4499 ∧ 4499 < 899 + Llo Bx 12 ∧ 899 + Llo Bx 12 = 5119 := by
  have hbad : ¬ GF Bx 0 899 1 := by decide
  obtain ⟨hf, _, h1, h2⟩ := stale_pulse Bx 0 899 1 Bx_wf (by decide) 12 (by decide) (by decide)
    hbad (fun k a b => by omega) (fun k a b => Bx_lo_order 1 k (by decide) a b)
    (Bx_start 899 (by decide) 1 (by decide) (by decide))
  have e : (899 : Int) + Bx.ql 1 + Pl Bx 1 (12 - 1) = 4499 := by decide
  rw [e] at h1 h2
  exact ⟨hbad, by decide, hf, h1, h2, by decide, by decide, by decide⟩

end Formal.Cells.LibGapDelay
