import Formal.Core.Substrate.Chan
import Formal.Core.Substrate.CornerNat
import Formal.Core.Discretize
import Formal.Core.Delay.Corner
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Substrate, part 3: the ℝ bridge, stated once

Real time is the physics; `ℕ` ps is where proofs and checkers live. This
file restates the discretisation theorems of `Formal.Core.Discretize`
against the substrate's relation (`Win` / `WinR` / `DNet`) and links the ℕ
corner model (`CornerNat`) to the ℝ one (`Formal.Core.Corner`).

## Discretisation, against `Win`

* `chan_sample_win`: a continuous FIFO transport channel `[lo, hi]`
  (`DelayPure.Chan`) whose input has no two transitions within one quantum
  (`Discretize.Sep q`, **H_SEP**) is, on the grid `k·q`, a `Win L H`
  channel for any `L·q ≤ lo`, `hi ≤ H·q`. No rest hypothesis.
  `chan_sample_winR`: with **H_REST** (`AtRest`) it is `WinR`.
* `circuit_sample_win`, `transfer_win`, `transfer_win_invariant`: the same
  for a whole continuous circuit (`Discretize.CCircuit`) and the substrate
  net `CCircuit.toDNet L H`: **any theorem proved for all `DNet.Beh`
  behaviours holds for the samples of every continuous behaviour whose
  excitations are separated** (`Sep q` on each gate's excitation, e.g. from
  joint separation of its fan-in: `Discretize.sep_map`).
* `invariant_real_time`: a state invariant of a jointly separated, at-rest
  tuple of nets that holds at every grid point holds at every real time
  (`Discretize.invariant_everywhere` with the Archimedean witness discharged).
  Without joint separation this is false (`Discretize.mutex_between`).

## Corner model, ℕ ↔ ℝ

* `nom_real`, `scat_real`, `realizesAt_real`: an ℕ realisation at corner
  `w1/(w0+w1)` is an ℝ `Corner.Scat` realisation at that corner.
* `endpoint_real`, **`endpoints_sound_real`**: the decidable ℕ endpoint
  check (`EndpointOK`) implies the bundling inequality for EVERY REAL corner
  `c ∈ [0,1]` and every REAL delays within scatter `κ` (through
  `Corner.bundle_ratio_affine`). So a checker that decides `EndpointOK` in ℕ
  is sound for real silicon under H_AFFINE + H_SHARED_CORNER + H_SCATTER,
  with no rationality or rounding assumption on the die's corner.
* `corner_chan_sample_ind`: a real corner-model channel (band
  `(1±κ)·D(c)` at any real `c`) samples to `Win (indLo) (indHi)` on the 1-ps
  grid; `corner_chan_sample_band`: at a corner of the ℕ model, to
  `Win (bandLo c) (bandHi c)`.
-/

namespace Formal.Core.Substrate

open Formal.Core.Discretize (Sep AtRest sample sampleAll CCircuit pick pick_bounds pick_val)

/-! ## 1. One channel -/

/-- **Discretisation into `Win`.** No rest hypothesis: `Win` only constrains
steps `≥ H`, whose read times are `≥ 0`. -/
theorem chan_sample_win {q lo hi : ℝ} {L H : ℕ} (hq : 0 ≤ q)
    (hL : (L : ℝ) * q ≤ lo) (hH : hi ≤ (H : ℝ) * q)
    {x y : ℝ → Bool} (hc : DelayPure.Chan lo hi x y) (hsep : Sep q x) :
    Win L H (sample q x) (sample q y) := by
  obtain ⟨r, e⟩ := hc
  have hLH : L ≤ H := by
    have a := r.ge 0; have b := r.le 0
    have : (L : ℝ) * q ≤ (H : ℝ) * q := by linarith
    exact_mod_cast le_of_mul_le_mul_right this hq
  intro t ht
  have hge := r.ge ((t : ℝ) * q)
  have hpos : 0 ≤ r.σ ((t : ℝ) * q) := by
    have h3 : (H : ℝ) ≤ t := by exact_mod_cast ht
    have := mul_le_mul_of_nonneg_right h3 hq.le
    linarith
  have hneg : r.σ ((t : ℝ) * q) < 0 → x (r.σ ((t : ℝ) * q)) = x 0 :=
    fun h => absurd h (not_lt.mpr hpos)
  obtain ⟨hex, b1, b2⟩ := pick_bounds (x := x) (k := t) hq hL hH (by linarith) (r.le _) hneg
  refine ⟨pick q x (r.σ ((t : ℝ) * q)), by omega, by omega, ?_⟩
  show y ((t : ℝ) * q) = x ((pick q x (r.σ ((t : ℝ) * q)) : ℝ) * q)
  rw [e, pick_val hsep hex hneg]

/-- **Discretisation into `WinR`** (with H_REST), from `Discretize.chan_sample`. -/
theorem chan_sample_winR {q lo hi : ℝ} {L H : ℕ} (hq : 0 < q)
    (hL : (L : ℝ) * q ≤ lo) (hH : hi ≤ (H : ℝ) * q)
    {x y : ℝ → Bool} (hc : DelayPure.Chan lo hi x y) (hsep : Sep q x) (hrest : AtRest x) :
    WinR L H (sample q x) (sample q y) :=
  transport_winR (Discretize.chan_sample hq hL hH hc hsep hrest)

/-! ## 2. Circuits -/

/-- A continuous circuit with grid bounds `L, H`, as a substrate net. -/
def _root_.Formal.Core.Discretize.CCircuit.toDNet {N : Type} (C : CCircuit N) (L H : N → ℕ) :
    DNet N := ⟨C.drv, C.f, L, H⟩

/-- A discrete circuit of `Discretize` as a substrate net. -/
def _root_.Formal.Core.Discretize.DCircuit.toDNet {N : Type} (D : Discretize.DCircuit N) :
    DNet N := ⟨D.drv, D.f, D.L, D.H⟩

/-- `Discretize`'s discrete circuit semantics is the substrate's transport
semantics. -/
theorem dcircuit_beh_iff {N : Type} (D : Discretize.DCircuit N) (v : N → Sig) :
    D.Beh v ↔ D.toDNet.BehT v := Iff.rfl

/-- **H_GRID** for a circuit: positive quantum, grid bounds enclose the real
bounds. -/
structure GridBounds {N : Type} (q : ℝ) (C : CCircuit N) (L H : N → ℕ) : Prop where
  q_pos : 0 < q
  lo_grid : ∀ n, C.drv n → (L n : ℝ) * q ≤ C.lo n
  hi_grid : ∀ n, C.drv n → C.hi n ≤ (H n : ℝ) * q

/-- **Discretisation soundness, circuit, into `DNet.Beh`.** Only separation
of each excitation is needed (no rest). -/
theorem circuit_sample_win {N : Type} {q : ℝ} {C : CCircuit N} {L H : N → ℕ}
    {v : N → ℝ → Bool} (hb : C.Beh v) (hg : GridBounds q C L H)
    (hsep : ∀ n, C.drv n → Sep q (C.exc v n)) :
    (C.toDNet L H).Beh (sampleAll q v) := by
  intro n hn
  exact chan_sample_win hg.q_pos (hg.lo_grid n hn) (hg.hi_grid n hn) (hb n hn) (hsep n hn)

/-- With H_REST as well (the full `Discretize.Discretizes`), into `BehR`. -/
theorem circuit_sample_winR {N : Type} {q : ℝ} {C : CCircuit N} {L H : N → ℕ}
    {v : N → ℝ → Bool} (hb : C.Beh v) (hd : Discretize.Discretizes q C L H v) :
    (C.toDNet L H).BehR (sampleAll q v) :=
  DNet.BehT.toBehR _ (Discretize.circuit_sample hb hd)

/-- **Transfer.** A property proved for all substrate (`Win`) behaviours of
the gridded net holds of the samples of every separated continuous
behaviour. -/
theorem transfer_win {N : Type} {q : ℝ} {C : CCircuit N} {L H : N → ℕ}
    (P : (N → Sig) → Prop) (hP : ∀ vd, (C.toDNet L H).Beh vd → P vd)
    {v : N → ℝ → Bool} (hb : C.Beh v) (hg : GridBounds q C L H)
    (hsep : ∀ n, C.drv n → Sep q (C.exc v n)) : P (sampleAll q v) :=
  hP _ (circuit_sample_win hb hg hsep)

/-- Transfer of a state invariant, at every grid point. -/
theorem transfer_win_invariant {N : Type} {q : ℝ} {C : CCircuit N} {L H : N → ℕ}
    (Inv : (N → Bool) → Prop) (hP : ∀ vd, (C.toDNet L H).Beh vd → ∀ k, Inv (fun n => vd n k))
    {v : N → ℝ → Bool} (hb : C.Beh v) (hg : GridBounds q C L H)
    (hsep : ∀ n, C.drv n → Sep q (C.exc v n)) :
    ∀ k : ℕ, Inv (fun n => v n ((k : ℝ) * q)) :=
  hP _ (circuit_sample_win hb hg hsep)

/-- **Between grid points.** A grid invariant of a JOINTLY separated, at-rest
tuple of nets holds at every real time. -/
theorem invariant_real_time {N : Type} {q : ℝ} (hq : 0 < q) {v : N → ℝ → Bool}
    (hsep : Sep q (fun t n => v n t)) (hrest : AtRest (fun t n => v n t))
    (Inv : (N → Bool) → Prop) (hinv : ∀ k : ℕ, Inv (fun n => v n ((k : ℝ) * q))) (t : ℝ) :
    Inv (fun n => v n t) := by
  obtain ⟨T, hT⟩ := exists_nat_ge (t / q)
  refine Discretize.invariant_everywhere hq hsep hrest Inv hinv t ⟨T, ?_⟩
  have := mul_le_mul_of_nonneg_right hT hq.le
  rwa [div_mul_cancel₀ t hq.ne'] at this

/-! ## 3. Corner model: ℕ ↔ ℝ -/

/-- `κ` as a real number. -/
noncomputable def Kappa.toReal (k : Kappa) : ℝ := (k.num : ℝ) / k.den

/-- The corner as a real number `w1 / (w0 + w1)`. -/
noncomputable def Corner.toReal (c : Corner) : ℝ := (c.w1 : ℝ) / c.W

/-- An ℕ arc as an ℝ `Corner.Arc`. -/
def CArc.toArc (a : CArc) : Formal.Core.Corner.Arc :=
  ⟨a.F, a.S, Nat.cast_nonneg _, by exact_mod_cast a.F_le_S⟩

theorem Kappa.toReal_nonneg (k : Kappa) : 0 ≤ k.toReal :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem Kappa.toReal_le_one (k : Kappa) : k.toReal ≤ 1 := by
  unfold Kappa.toReal
  rw [div_le_one (by exact_mod_cast k.den_pos)]; exact_mod_cast k.num_le

theorem Corner.toReal_mem (c : Corner) : 0 ≤ c.toReal ∧ c.toReal ≤ 1 := by
  have hW : (0 : ℝ) < c.W := by exact_mod_cast c.W_pos
  refine ⟨div_nonneg (Nat.cast_nonneg _) hW.le, ?_⟩
  unfold Corner.toReal
  rw [div_le_one hW]; unfold Corner.W; push_cast; linarith [(Nat.cast_nonneg c.w0 : (0:ℝ) ≤ c.w0)]

theorem kappa_lo_real (k : Kappa) : (k.lo : ℝ) = k.den * (1 - k.toReal) := by
  have hd : (k.den : ℝ) ≠ 0 := by exact_mod_cast k.den_pos.ne'
  unfold Kappa.lo Kappa.toReal
  rw [Nat.cast_sub k.num_le]; field_simp

theorem kappa_hi_real (k : Kappa) : (k.hi : ℝ) = k.den * (1 + k.toReal) := by
  have hd : (k.den : ℝ) ≠ 0 := by exact_mod_cast k.den_pos.ne'
  unfold Kappa.hi Kappa.toReal
  push_cast; field_simp

/-- The ℕ nominal value is `W` times the ℝ nominal delay at the same corner. -/
theorem nom_real (c : Corner) (a : CArc) :
    (nom c a : ℝ) = c.W * (a.toArc.at' c.toReal) := by
  have hW : (c.W : ℝ) ≠ 0 := by exact_mod_cast c.W_pos.ne'
  unfold nom Formal.Core.Corner.Arc.at' Formal.Core.Corner.lerp Corner.toReal CArc.toArc
  simp only
  unfold Corner.W at hW ⊢
  push_cast at hW ⊢
  field_simp
  ring

/-- **ℕ realisation ⇒ ℝ realisation** at the same corner. -/
theorem scat_real {k : Kappa} {c : Corner} {a : CArc} {d : ℕ} (h : Scat k c a d) :
    Formal.Core.Corner.Scat k.toReal (a.toArc.at' c.toReal) (d : ℝ) := by
  have hd : (0 : ℝ) < k.den := by exact_mod_cast k.den_pos
  have hW : (0 : ℝ) < c.W := by exact_mod_cast c.W_pos
  have hQ : (0 : ℝ) < k.den * c.W := mul_pos hd hW
  obtain ⟨h1, h2⟩ := h
  have r1 : (k.lo : ℝ) * nom c a ≤ k.den * c.W * d := by exact_mod_cast h1
  have r2 : (k.den : ℝ) * c.W * d ≤ k.hi * nom c a := by exact_mod_cast h2
  rw [kappa_lo_real, nom_real] at r1
  rw [kappa_hi_real, nom_real] at r2
  constructor
  · refine le_of_mul_le_mul_left ?_ hQ
    linarith
  · refine le_of_mul_le_mul_left ?_ hQ
    linarith

theorem realizesAt_real {A : Type} (M : CornerModel A) {c : Corner} {d : A → ℕ}
    (h : M.RealizesAt c d) (e : A) :
    Formal.Core.Corner.Scat M.κ.toReal ((M.arc e).toArc.at' c.toReal) (d e : ℝ) :=
  scat_real (h e)

/-- The ℕ endpoint check, read in ℝ: `(1+κ)·D + m ≤ (1-κ)·R` at both
endpoints. -/
theorem endpoint_real {k : Kappa} {D R : CArc} {m : ℕ} (h : EndpointOK k D R m) :
    (1 + k.toReal) * (D.F : ℝ) + m ≤ (1 - k.toReal) * R.F ∧
    (1 + k.toReal) * (D.S : ℝ) + m ≤ (1 - k.toReal) * R.S := by
  have hd : (0 : ℝ) < k.den := by exact_mod_cast k.den_pos
  obtain ⟨h0, h1⟩ := h
  have r0 : (k.hi : ℝ) * D.F + k.den * m ≤ k.lo * R.F := by exact_mod_cast h0
  have r1 : (k.hi : ℝ) * D.S + k.den * m ≤ k.lo * R.S := by exact_mod_cast h1
  rw [kappa_lo_real, kappa_hi_real] at r0 r1
  constructor
  · refine le_of_mul_le_mul_left ?_ hd; linarith
  · refine le_of_mul_le_mul_left ?_ hd; linarith

/-- **The decidable ℕ endpoint check is sound for real silicon.** For every
REAL corner `c ∈ [0,1]` and all REAL delays within scatter `κ` of their
nominal values at `c`: data + `m` ≤ request. -/
theorem endpoints_sound_real {k : Kappa} {D R : CArc} {m : ℕ} (h : EndpointOK k D R m)
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) {δD δR : ℝ}
    (hD : Formal.Core.Corner.Scat k.toReal (D.toArc.at' c) δD)
    (hR : Formal.Core.Corner.Scat k.toReal (R.toArc.at' c) δR) : δD + m ≤ δR := by
  obtain ⟨e0, e1⟩ := endpoint_real h
  have := Formal.Core.Corner.bundle_ratio_affine (κ := k.toReal) (m := (m : ℝ))
    (Fd := D.F) (Sd := D.S) (Fr := R.F) (Sr := R.S) hc0 hc1 e0 e1
  have a := hD.2; have b := hR.1
  unfold Formal.Core.Corner.Arc.at' CArc.toArc at a b
  simp only at a b
  linarith

/-- Path endpoints agree with `Corner.pathF` / `Corner.pathS`. -/
theorem pathArc_F (l : List CArc) :
    ((pathArc l).F : ℝ) = Formal.Core.Corner.pathF (l.map CArc.toArc) := by
  induction l with
  | nil => simp [pathArc, CArc.zero, Formal.Core.Corner.pathF]
  | cons a l ih =>
    simp only [pathArc, CArc.add, List.map_cons, Formal.Core.Corner.pathF]
    push_cast; rw [ih]; rfl

theorem pathArc_S (l : List CArc) :
    ((pathArc l).S : ℝ) = Formal.Core.Corner.pathS (l.map CArc.toArc) := by
  induction l with
  | nil => simp [pathArc, CArc.zero, Formal.Core.Corner.pathS]
  | cons a l ih =>
    simp only [pathArc, CArc.add, List.map_cons, Formal.Core.Corner.pathS]
    push_cast; rw [ih]; rfl

/-! ## 4. Corner channels to `Win` on the 1-ps grid -/

/-- The independent band encloses the real scatter band at every corner. -/
theorem ind_encloses (k : Kappa) (a : CArc) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (indLo k a : ℝ) ≤ (1 - k.toReal) * a.toArc.at' c ∧
    (1 + k.toReal) * a.toArc.at' c ≤ (indHi k a : ℝ) := by
  have hd : (0 : ℝ) < k.den := by exact_mod_cast k.den_pos
  have hl := Formal.Core.Corner.lerp_ge_left a.toArc.F_le_S hc0 (c := c)
  have hr := Formal.Core.Corner.lerp_le_right a.toArc.F_le_S hc1 (c := c)
  have k0 := k.toReal_nonneg; have k1 := k.toReal_le_one
  have f1 : indLo k a * k.den ≤ k.lo * a.F := Nat.div_mul_le_self _ _
  have f2 : k.hi * a.S ≤ indHi k a * k.den := le_cdiv_mul k.den_pos
  have r1 : (indLo k a : ℝ) * k.den ≤ k.lo * a.F := by exact_mod_cast f1
  have r2 : (k.hi : ℝ) * a.S ≤ indHi k a * k.den := by exact_mod_cast f2
  rw [kappa_lo_real] at r1; rw [kappa_hi_real] at r2
  unfold Formal.Core.Corner.Arc.at' CArc.toArc at *
  simp only at hl hr ⊢
  constructor
  · have : (indLo k a : ℝ) ≤ (1 - k.toReal) * a.F := by
      refine le_of_mul_le_mul_left ?_ hd; linarith
    have := mul_le_mul_of_nonneg_left hl (by linarith : (0:ℝ) ≤ 1 - k.toReal)
    linarith
  · have : (1 + k.toReal) * a.S ≤ (indHi k a : ℝ) := by
      refine le_of_mul_le_mul_left ?_ hd; linarith
    have := mul_le_mul_of_nonneg_left hr (by linarith : (0:ℝ) ≤ 1 + k.toReal)
    linarith

/-- At a corner of the ℕ model, the outward-rounded band encloses the real
scatter band. -/
theorem band_encloses (k : Kappa) (c : Corner) (a : CArc) :
    (bandLo k c a : ℝ) ≤ (1 - k.toReal) * a.toArc.at' c.toReal ∧
    (1 + k.toReal) * a.toArc.at' c.toReal ≤ (bandHi k c a : ℝ) := by
  have hd : (0 : ℝ) < k.den := by exact_mod_cast k.den_pos
  have hW : (0 : ℝ) < c.W := by exact_mod_cast c.W_pos
  have hQ : (0 : ℝ) < k.den * c.W := mul_pos hd hW
  have f1 : bandLo k c a * (k.den * c.W) ≤ k.lo * nom c a := Nat.div_mul_le_self _ _
  have f2 : k.hi * nom c a ≤ bandHi k c a * (k.den * c.W) := le_cdiv_mul (q_pos k c)
  have r1 : (bandLo k c a : ℝ) * (k.den * c.W) ≤ k.lo * nom c a := by exact_mod_cast f1
  have r2 : (k.hi : ℝ) * nom c a ≤ bandHi k c a * (k.den * c.W) := by exact_mod_cast f2
  rw [kappa_lo_real, nom_real] at r1
  rw [kappa_hi_real, nom_real] at r2
  constructor
  · refine le_of_mul_le_mul_left ?_ hQ; linarith
  · refine le_of_mul_le_mul_left ?_ hQ; linarith

/-- **A real corner-model arc, sampled at 1 ps, is a `Win` channel with the
independent ℕ band**, at any real corner (input separated by 1 ps). -/
theorem corner_chan_sample_ind (k : Kappa) (a : CArc) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    {x y : ℝ → Bool}
    (hch : DelayPure.Chan ((1 - k.toReal) * a.toArc.at' c) ((1 + k.toReal) * a.toArc.at' c) x y)
    (hsep : Sep 1 x) : Win (indLo k a) (indHi k a) (sample 1 x) (sample 1 y) := by
  obtain ⟨h1, h2⟩ := ind_encloses k a hc0 hc1
  exact chan_sample_win one_pos (by simpa using h1) (by simpa using h2) hch hsep

/-- At a corner of the ℕ model: the corner band `[bandLo c, bandHi c]`. -/
theorem corner_chan_sample_band (k : Kappa) (c : Corner) (a : CArc) {x y : ℝ → Bool}
    (hch : DelayPure.Chan ((1 - k.toReal) * a.toArc.at' c.toReal)
      ((1 + k.toReal) * a.toArc.at' c.toReal) x y)
    (hsep : Sep 1 x) : Win (bandLo k c a) (bandHi k c a) (sample 1 x) (sample 1 y) := by
  obtain ⟨h1, h2⟩ := band_encloses k c a
  exact chan_sample_win one_pos (by simpa using h1) (by simpa using h2) hch hsep

end Formal.Core.Substrate
