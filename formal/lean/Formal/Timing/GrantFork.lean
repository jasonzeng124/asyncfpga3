import Formal.Cells.ArbBinary

/-!
# C-10i: the grant-fork race of the shipped (held) `bd_arbiter` (H_GRANT_FORK)

C-12c (TChecker, dense time) found that mutual exclusion of the HELD arbiter's
grant wires depends on q's route to the grant LUT `ugrant` against q's own
feedback copy into `ustate`. This file states that race in gate-fidelity form
(real INITs: `stA` = `ustate` O6 INIT `FFF0_FFB2_ACAC_ACAC` with A0 on I4,
`gr1`/`gr2` = `ugrant` O5/O6 INIT `0C0C_0C0C_A0A0_A0A0`, all from shard B's
`Formal.Cells.ArbBinary`, read-only), proves the exact condition, and gives a
box checker (`okT`, `okI`) whose verdicts on the routed instances are decided by
the kernel in `GrantForkInst.lean`.

## Model (client 2 direction; client 1 is the mirror)

Per-pin transport (pure) delays, one per (pin, output), as in B's
`ArbOverlapRace.Dl`: route + site-pin input buffer + the LUT arc of that pin.
No rise/fall split (prjxray-db has none).
* `ustate`:  `q t = stA (r1 (t-s1)) (r2 (t-s2)) (q (t-L)) (a0 (t-sa))`   (H_ST)
* `ugrant`:  `g2 t = gr2 (r1 (t-x1)) (r2 (t-a2)) (q (t-b6))`             (H_G6)
             `g1 t = gr1 (r1 (t-a1)) (r2 (t-x2)) (q (t-b5))`             (H_G5)
* Scenario `Scn2`: A0 low (H_A0_LOW: the server is idle; the hold pin does not
  act), r1 rises at `t1` while r2 is low, q rises once at `T = t1 + s1` and stays
  (the q waveform is a step: no q runt, the tier-3 case excluded), r2 rises at
  `t2`. `consistent2_iff`: the step is a solution of H_ST iff
  `T + L ≤ t2 + s2` (r2 reaches ustate's core after q's own feedback copy).
* `runt2_iff`: g2 is ever high iff `t2 + a2 < T + b6`.
* **`fork_runt2_iff`**: a consistent scenario with a g2 runt exists iff
  `0 < W2`, `W2 = (b6 - L) - (a2 - s2)`. The runt is at most `W2` wide
  (`runt2_width`).
* Mirror (`Scn1`, q falls, r1 rises late, g1 = r1.q runt on O5):
  `fork_runt1_iff`, `W1 = (b5 - L) - (a1 - s1)`.

## Instance data and the checker

`Q` = the eight routed quantities of one client (suffix routes after the branch
point of the q net and of the r net, and four arcs). H_SHARED_PREFIX: the
branch point's prefix `cq` (`cr`) is ONE delay in both sums
(`lumped_W`), so it cancels. `Box` = one integer interval per quantity.
* `okT B`: transport H_GRANT_FORK, `Whi ≤ 0`. `okT_iff`: true iff every point
  of the box has `W ≤ 0`; with `transport_sound` no consistent scenario at any
  delays in the box has a runt; with `transport_exact` (box non-empty) a false
  verdict has a concrete runt scenario at delays in the box.
* `okI B`: the inertial reading (C-12c). H_INERTIAL_COMMIT: r_k reaches
  ustate's core no earlier than q's output edge and late enough that ustate
  swallows its own reversal; the grant LUT's core then sees the stale q for at
  most `maxW = dqg - (drg - drs) - max 0 (dqs - dst + 1)`; the runt is swallowed
  iff that is below the grant output's inertial delay, taken as the smaller of
  the two pin arcs (H_INERTIAL_ARC). `okI_iff`. With C-12c's zero-skew,
  `wq_s < 56` rows this is exactly its `wq_g < 56`.
-/

namespace Formal.Timing.GrantFork
open Formal.Cells Formal.Cells.ArbBinary

abbrev Sig := Int → Bool

/-- A rising step at `t0`. -/
def step (t0 : Int) : Sig := fun t => decide (t0 ≤ t)

/-! ## Client 2: q rises for r1, r2 rises late, g2 runt on O6 -/

/-- H_ST for the client-2 scenario: A0 low, r1 = step t1, r2 = step t2,
q = step T. -/
def Cons2 (s1 s2 L t1 t2 T : Int) : Prop :=
  ∀ t, step T t = stA (step t1 (t - s1)) (step t2 (t - s2)) (step T (t - L)) false

/-- The step `q = step (t1 + s1)` is a solution of the state LUT's relation iff
r2 reaches ustate after q's own feedback copy. -/
theorem consistent2_iff (s1 s2 L t1 t2 : Int) (hL : 0 < L) :
    Cons2 s1 s2 L t1 t2 (t1 + s1) ↔ t1 + s1 + L ≤ t2 + s2 := by
  constructor
  · intro h
    refine Int.not_lt.mp fun hlt => ?_
    have ht := h (max (t1 + s1) (t2 + s2))
    simp only [step, stA_eq, stF_eq] at ht
    by_cases hm : t1 + s1 ≤ t2 + s2
    · rw [Int.max_eq_right hm] at ht
      by_cases h2 : t1 + s1 ≤ t2 + s2 - L <;> simp [hm, h2, show t1 ≤ t2 + s2 - s1 by omega] at ht
      omega
    · rw [Int.max_eq_left (by omega)] at ht
      by_cases h2 : t2 ≤ t1 + s1 - s2 <;> by_cases h3 : t1 + s1 ≤ t1 + s1 - L <;>
        simp [h2, h3] at ht <;> omega
  · intro h t
    simp only [step, stA_eq, stF_eq]
    by_cases h1 : t1 ≤ t - s1 <;> by_cases h2 : t2 ≤ t - s2 <;>
      by_cases h3 : t1 + s1 ≤ t - L <;> by_cases h4 : t1 + s1 ≤ t <;>
      simp [h1, h2, h3, h4] <;> omega

/-- H_G6 evaluated on the scenario: the g2 waveform. -/
def g2w (x1 a2 b6 t1 t2 T : Int) : Sig := fun t =>
  gr2 (step t1 (t - x1)) (step t2 (t - a2)) (step T (t - b6))

/-- g2 is ever high iff r2 reaches ugrant before the new q does. -/
theorem runt2_iff (x1 a2 b6 t1 t2 T : Int) :
    (∃ t, g2w x1 a2 b6 t1 t2 T t = true) ↔ t2 + a2 < T + b6 := by
  constructor
  · rintro ⟨t, ht⟩
    simp only [g2w, gr2_eq, step, Bool.and_eq_true, decide_eq_true_eq,
      Bool.not_eq_true', decide_eq_false_iff_not] at ht
    omega
  · intro h
    refine ⟨t2 + a2, ?_⟩
    simp only [g2w, gr2_eq, step, Bool.and_eq_true, decide_eq_true_eq,
      Bool.not_eq_true', decide_eq_false_iff_not]
    omega

/-- The runt is at most `W2` wide: every high instant of g2 lies in
`[t2 + a2, T + b6)`, and consistency puts `t2 + a2 ≥ T + L - s2 + a2`. -/
theorem runt2_width (s1 s2 L x1 a2 b6 t1 t2 : Int) (hL : 0 < L)
    (hc : Cons2 s1 s2 L t1 t2 (t1 + s1)) (t : Int)
    (ht : g2w x1 a2 b6 t1 t2 (t1 + s1) t = true) :
    t2 + a2 ≤ t ∧ t < t1 + s1 + b6 ∧ (t1 + s1 + b6) - (t2 + a2) ≤ (b6 - L) - (a2 - s2) := by
  have := (consistent2_iff s1 s2 L t1 t2 hL).1 hc
  simp only [g2w, gr2_eq, step, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_true', decide_eq_false_iff_not] at ht
  omega

/-- **The client-2 grant-fork race, exactly.** There are request times with a
consistent (no-q-runt) state trace and a g2 runt iff `W2 > 0`. -/
theorem fork_runt2_iff (s1 s2 L x1 a2 b6 : Int) (hL : 0 < L) :
    (∃ t1 t2, Cons2 s1 s2 L t1 t2 (t1 + s1) ∧ ∃ t, g2w x1 a2 b6 t1 t2 (t1 + s1) t = true) ↔
      0 < (b6 - L) - (a2 - s2) := by
  constructor
  · rintro ⟨t1, t2, hc, hr⟩
    have h1 := (consistent2_iff s1 s2 L t1 t2 hL).1 hc
    have h2 := (runt2_iff x1 a2 b6 t1 t2 (t1 + s1)).1 hr
    omega
  · intro hW
    refine ⟨0, s1 + L - s2, (consistent2_iff s1 s2 L 0 _ hL).2 (by omega),
      (runt2_iff x1 a2 b6 0 _ _).2 (by omega)⟩

/-! ## Client 1 (mirror): q falls for r2, r1 rises late, g1 runt on O5 -/

/-- A falling step at `t0`. -/
def fstep (t0 : Int) : Sig := fun t => decide (t < t0)

def Cons1 (s1 s2 L t1 t2 T : Int) : Prop :=
  ∀ t, fstep T t = stA (step t1 (t - s1)) (step t2 (t - s2)) (fstep T (t - L)) false

theorem consistent1_iff (s1 s2 L t1 t2 : Int) (hL : 0 < L) :
    Cons1 s1 s2 L t1 t2 (t2 + s2) ↔ t2 + s2 + L ≤ t1 + s1 := by
  constructor
  · intro h
    refine Int.not_lt.mp fun hlt => ?_
    have ht := h (max (t2 + s2) (t1 + s1))
    simp only [fstep, step, stA_eq, stF_eq] at ht
    by_cases hm : t2 + s2 ≤ t1 + s1
    · rw [Int.max_eq_right hm] at ht
      by_cases h1 : t1 ≤ t1 + s1 - s1 <;> by_cases h2 : t2 ≤ t1 + s1 - s2 <;>
        by_cases h3 : t1 + s1 - L < t2 + s2 <;> by_cases h4 : t1 + s1 < t2 + s2 <;>
        simp [h2, h3, h4] at ht <;> omega
    · rw [Int.max_eq_left (by omega)] at ht
      by_cases h1 : t1 ≤ t2 + s2 - s1 <;> by_cases h3 : t2 + s2 - L < t2 + s2 <;>
        simp [h1, h3] at ht <;> omega
  · intro h t
    simp only [fstep, step, stA_eq, stF_eq]
    by_cases h1 : t1 ≤ t - s1 <;> by_cases h2 : t2 ≤ t - s2 <;>
      by_cases h3 : t - L < t2 + s2 <;> by_cases h4 : t < t2 + s2 <;>
      simp [h1, h2, h3, h4] <;> omega

def g1w (a1 x2 b5 t1 t2 T : Int) : Sig := fun t =>
  gr1 (step t1 (t - a1)) (step t2 (t - x2)) (fstep T (t - b5))

theorem runt1_iff (a1 x2 b5 t1 t2 T : Int) :
    (∃ t, g1w a1 x2 b5 t1 t2 T t = true) ↔ t1 + a1 < T + b5 := by
  constructor
  · rintro ⟨t, ht⟩
    simp only [g1w, gr1_eq, step, fstep, Bool.and_eq_true, decide_eq_true_eq] at ht
    omega
  · intro h
    refine ⟨t1 + a1, ?_⟩
    simp only [g1w, gr1_eq, step, fstep, Bool.and_eq_true, decide_eq_true_eq]
    omega

theorem fork_runt1_iff (s1 s2 L a1 x2 b5 : Int) (hL : 0 < L) :
    (∃ t1 t2, Cons1 s1 s2 L t1 t2 (t2 + s2) ∧ ∃ t, g1w a1 x2 b5 t1 t2 (t2 + s2) t = true) ↔
      0 < (b5 - L) - (a1 - s1) := by
  constructor
  · rintro ⟨t1, t2, hc, hr⟩
    have h1 := (consistent1_iff s1 s2 L t1 t2 hL).1 hc
    have h2 := (runt1_iff a1 x2 b5 t1 t2 (t2 + s2)).1 hr
    omega
  · intro hW
    refine ⟨s2 + L - s1, 0, (consistent1_iff s1 s2 L _ 0 hL).2 (by omega),
      (runt1_iff a1 x2 b5 _ 0 _).2 (by omega)⟩

/-! ## Routed quantities, H_SHARED_PREFIX, and the box checker -/

/-- The eight routed quantities of one client k (ps). -/
structure Q where
  /-- q net, branch point → ugrant's q pin (route + site pin). -/
  dqg : Int
  /-- q net, branch point → ustate's own q pin. -/
  dqs : Int
  /-- r_k net, branch point → ugrant's r_k pin. -/
  drg : Int
  /-- r_k net, branch point → ustate's r_k pin. -/
  drs : Int
  /-- ugrant arc, q pin → the client's output (O6 for k = 2, O5 for k = 1). -/
  agq : Int
  /-- ugrant arc, r_k pin → that output. -/
  agr : Int
  /-- ustate arc, q pin → O6. -/
  asq : Int
  /-- ustate arc, r_k pin → O6. -/
  asr : Int

/-- The transport window of `Q`. -/
def Wq (x : Q) : Int := (x.dqg + x.agq) - (x.dqs + x.asq) - ((x.drg + x.agr) - (x.drs + x.asr))

/-- **H_SHARED_PREFIX.** The lumped per-pin delays are prefix + suffix + arc with
ONE prefix `cq` for both q sinks and ONE prefix `cr` for both r_k sinks; the
window does not depend on the prefixes. -/
theorem lumped_W (x : Q) (cq cr : Int) :
    ((cq + x.dqg + x.agq) - (cq + x.dqs + x.asq)) - ((cr + x.drg + x.agr) - (cr + x.drs + x.asr)) = Wq x := by
  unfold Wq; omega

structure Iv where
  lo : Int
  hi : Int
deriving DecidableEq, Repr

structure Box where
  dqg : Iv
  dqs : Iv
  drg : Iv
  drs : Iv
  agq : Iv
  agr : Iv
  asq : Iv
  asr : Iv
deriving DecidableEq, Repr

def Iv.mem (i : Iv) (v : Int) : Prop := i.lo ≤ v ∧ v ≤ i.hi

def Box.mem (B : Box) (x : Q) : Prop :=
  B.dqg.mem x.dqg ∧ B.dqs.mem x.dqs ∧ B.drg.mem x.drg ∧ B.drs.mem x.drs ∧
  B.agq.mem x.agq ∧ B.agr.mem x.agr ∧ B.asq.mem x.asq ∧ B.asr.mem x.asr

def Box.wf (B : Box) : Bool :=
  decide (B.dqg.lo ≤ B.dqg.hi ∧ B.dqs.lo ≤ B.dqs.hi ∧ B.drg.lo ≤ B.drg.hi ∧ B.drs.lo ≤ B.drs.hi ∧
    B.agq.lo ≤ B.agq.hi ∧ B.agr.lo ≤ B.agr.hi ∧ B.asq.lo ≤ B.asq.hi ∧ B.asr.lo ≤ B.asr.hi)

/-- The worst point of the box for the transport window. -/
def worstT (B : Box) : Q :=
  ⟨B.dqg.hi, B.dqs.lo, B.drg.lo, B.drs.hi, B.agq.hi, B.agr.lo, B.asq.lo, B.asr.hi⟩

def Whi (B : Box) : Int := Wq (worstT B)

/-- Transport H_GRANT_FORK on a box. -/
def okT (B : Box) : Bool := decide (Whi B ≤ 0)

theorem W_le_Whi (B : Box) (x : Q) (h : B.mem x) : Wq x ≤ Whi B := by
  obtain ⟨⟨_, a⟩, ⟨b, _⟩, ⟨c, _⟩, ⟨_, d⟩, ⟨_, e⟩, ⟨f, _⟩, ⟨g, _⟩, ⟨_, k⟩⟩ := h
  simp only [Whi, Wq, worstT]; omega

theorem worstT_mem (B : Box) (h : B.wf = true) : B.mem (worstT B) := by
  simp only [Box.wf, decide_eq_true_eq] at h
  simp only [Box.mem, Iv.mem, worstT]; omega

/-- **The transport checker is exact on non-empty boxes.** -/
theorem okT_iff (B : Box) (h : B.wf = true) : okT B = true ↔ ∀ x, B.mem x → Wq x ≤ 0 := by
  unfold okT
  constructor
  · intro hk x hx
    have := W_le_Whi B x hx
    simp only [decide_eq_true_eq] at hk; omega
  · intro hall
    have := hall _ (worstT_mem B h)
    exact decide_eq_true this

/-- **Soundness, client 2.** A passing box: at every delay assignment in it
(any prefixes, any loop delay `L ≥ 1`), no consistent scenario has a g2 runt. -/
theorem transport_sound2 (B : Box) (hok : okT B = true) (h : B.wf = true)
    (x : Q) (hx : B.mem x) (cq cr s1 x1 : Int)
    (hL : 0 < cq + x.dqs + x.asq) (t1 t2 : Int)
    (hc : Cons2 s1 (cr + x.drs + x.asr) (cq + x.dqs + x.asq) t1 t2 (t1 + s1)) (t : Int) :
    g2w x1 (cr + x.drg + x.agr) (cq + x.dqg + x.agq) t1 t2 (t1 + s1) t = false := by
  have hW := (okT_iff B h).1 hok x hx
  cases hg : g2w x1 (cr + x.drg + x.agr) (cq + x.dqg + x.agq) t1 t2 (t1 + s1) t
  · rfl
  · have := (fork_runt2_iff s1 _ _ x1 _ _ hL).1 ⟨t1, t2, hc, t, hg⟩
    rw [lumped_W] at this; omega

/-- **Soundness, client 1** (O5, q falls). -/
theorem transport_sound1 (B : Box) (hok : okT B = true) (h : B.wf = true)
    (x : Q) (hx : B.mem x) (cq cr s2 x2 : Int)
    (hL : 0 < cq + x.dqs + x.asq) (t1 t2 : Int)
    (hc : Cons1 (cr + x.drs + x.asr) s2 (cq + x.dqs + x.asq) t1 t2 (t2 + s2)) (t : Int) :
    g1w (cr + x.drg + x.agr) x2 (cq + x.dqg + x.agq) t1 t2 (t2 + s2) t = false := by
  have hW := (okT_iff B h).1 hok x hx
  cases hg : g1w (cr + x.drg + x.agr) x2 (cq + x.dqg + x.agq) t1 t2 (t2 + s2) t
  · rfl
  · have := (fork_runt1_iff _ s2 _ _ x2 _ hL).1 ⟨t1, t2, hc, t, hg⟩
    rw [lumped_W] at this; omega

/-- **Exactness, client 2.** A failing (non-empty) box has delays in it and a
consistent scenario with a g2 runt (for any prefixes with `L ≥ 1`). -/
theorem transport_exact2 (B : Box) (hok : okT B = false) (h : B.wf = true) (cq cr s1 x1 : Int)
    (hL : 0 < cq + B.dqs.lo + B.asq.lo) :
    ∃ x, B.mem x ∧ ∃ t1 t2, Cons2 s1 (cr + x.drs + x.asr) (cq + x.dqs + x.asq) t1 t2 (t1 + s1) ∧
      ∃ t, g2w x1 (cr + x.drg + x.agr) (cq + x.dqg + x.agq) t1 t2 (t1 + s1) t = true := by
  refine ⟨worstT B, worstT_mem B h, ?_⟩
  have hW : 0 < Whi B := by simp only [okT, decide_eq_false_iff_not] at hok; omega
  apply (fork_runt2_iff s1 _ _ x1 _ _ hL).2
  dsimp only [Whi, Wq, worstT] at hW ⊢; omega

/-- **Exactness, client 1.** -/
theorem transport_exact1 (B : Box) (hok : okT B = false) (h : B.wf = true) (cq cr s2 x2 : Int)
    (hL : 0 < cq + B.dqs.lo + B.asq.lo) :
    ∃ x, B.mem x ∧ ∃ t1 t2, Cons1 (cr + x.drs + x.asr) s2 (cq + x.dqs + x.asq) t1 t2 (t2 + s2) ∧
      ∃ t, g1w (cr + x.drg + x.agr) x2 (cq + x.dqg + x.agq) t1 t2 (t2 + s2) t = true := by
  refine ⟨worstT B, worstT_mem B h, ?_⟩
  have hW : 0 < Whi B := by simp only [okT, decide_eq_false_iff_not] at hok; omega
  apply (fork_runt1_iff _ s2 _ _ x2 _ hL).2
  dsimp only [Whi, Wq, worstT] at hW ⊢; omega

/-! ## The inertial reading (C-12c)

Each LUT = Boolean function of its core inputs (pin arrival = source edge +
route + site pin; per-pin arc differences neglected, H_INERTIAL_ARC) followed by
an inertial output delay: an excitation shorter than it is swallowed.
q's output edge is at `T`. r_k reaches ustate's core at `u` and ugrant's core at
`u + (drg - drs)` (H_SHARED_PREFIX); the new q reaches ustate's core at
`T + dqs` and ugrant's core at `T + dqg`.
* H_INERTIAL_COMMIT (`Adm`): the q edge stands and q does not reverse: r_k came
  no earlier than `T` (else the set excitation was withdrawn before it matured)
  and ustate's reversal excitation `[u, T + dqs)` is shorter than ustate's
  inertial delay `dst` (else q flips back: a q runt, tier 3, not this race).
* The grant core then sees `r_k ∧ stale q` on `[u + (drg - drs), T + dqg)`;
  the runt reaches the grant wire iff that is at least ugrant's inertial
  delay, taken as `min agq agr` (`thr`). ustate's delay is taken as
  `max asq asr` (`dstOf`), the choice that admits the most `u`. -/

/-- Width of the grant-core excitation. -/
def inWidth (x : Q) (T u : Int) : Int := (T + x.dqg) - (u + (x.drg - x.drs))

/-- H_INERTIAL_COMMIT. -/
def Adm (x : Q) (dst T u : Int) : Prop := T ≤ u ∧ T + x.dqs - u < dst

def dstOf (x : Q) : Int := max x.asq x.asr

/-- H_INERTIAL_ARC: ugrant's inertial delay. -/
def thr (x : Q) : Int := min x.agq x.agr

/-- The widest admissible excitation. -/
def maxW (x : Q) (dst : Int) : Int := x.dqg - (x.drg - x.drs) - max 0 (x.dqs - dst + 1)

theorem inWidth_le (x : Q) (dst T u : Int) (h : Adm x dst T u) : inWidth x T u ≤ maxW x dst := by
  unfold Adm at h; unfold inWidth maxW; omega

theorem inWidth_attained (x : Q) (dst T : Int) :
    Adm x dst T (max T (T + x.dqs - dst + 1)) ∧
      inWidth x T (max T (T + x.dqs - dst + 1)) = maxW x dst := by
  unfold Adm inWidth maxW; omega

def okI (B : Box) : Bool :=
  decide (B.dqg.hi - (B.drg.lo - B.drs.hi) - max 0 (B.dqs.lo - max B.asq.hi B.asr.hi + 1)
    < min B.agq.lo B.agr.lo)

/-- **The inertial checker is exact on non-empty boxes**: it passes iff at every
point of the box every admissible grant-core excitation is shorter than the
grant LUT's inertial delay. -/
theorem okI_iff (B : Box) (h : B.wf = true) :
    okI B = true ↔ ∀ x, B.mem x → ∀ T u, Adm x (dstOf x) T u → inWidth x T u < thr x := by
  unfold okI thr dstOf
  constructor
  · intro hk x hx T u hu
    obtain ⟨⟨_, a⟩, ⟨b, _⟩, ⟨c, _⟩, ⟨_, d⟩, ⟨e, _⟩, ⟨f, _⟩, ⟨_, g⟩, ⟨_, k⟩⟩ := hx
    simp only [decide_eq_true_eq] at hk
    have := inWidth_le x _ T u hu
    unfold maxW at this
    omega
  · intro hall
    let y : Q := ⟨B.dqg.hi, B.dqs.lo, B.drg.lo, B.drs.hi, B.agq.lo, B.agr.lo, B.asq.hi, B.asr.hi⟩
    have hy : B.mem y := by
      simp only [Box.wf, decide_eq_true_eq] at h
      simp only [Box.mem, Iv.mem, y]; omega
    obtain ⟨hadm, heq⟩ := inWidth_attained y (max y.asq y.asr) 0
    have := hall y hy 0 _ hadm
    rw [heq] at this
    simp only [maxW, y] at this
    exact decide_eq_true this

end Formal.Timing.GrantFork
