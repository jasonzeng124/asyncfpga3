import Formal.Core.Delay.Corner
import Formal.Core.Substrate.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Cast.Order

/-!
# Corner cells: a finite grid of corner intervals covers the continuum

Probe A / KapRes2. The KapRes sweep (`formal/tools-A/kappa/kapres2/`) does not run the
timing checker at every corner `c ∈ [0,1]`; it runs it on finitely many corner CELLS
`[ca, cb]`, each with one band file whose band for arc `e` is (`tools-A/kappa/kapres2/cornerband2.py`)

    [ ⌊(1-κ)·min(lerp(f0,s0,ca), lerp(f0,s0,cb))⌋ ,  ⌈(1+κ)·max(lerp(f1,s1,ca), lerp(f1,s1,cb))⌉ ]

where `[f0, f1]` is the arc's FAST band and `[s0, s1]` its SLOW band in the band files (ps).
This file proves that this cell band contains every delay the corner model
(`Formal.Core.Corner`: H-affine, SharedCorner, `Scat κ`) allows for that arc at any corner
`c ∈ [ca, cb]`, whatever the arc's true endpoints are inside the two bands.

## The model (hypotheses are explicit arguments)

* the arc's fast endpoint `F ∈ [f0, f1]` and slow endpoint `S ∈ [s0, s1]` (reals);
  no `F ≤ S` is needed;
* nominal delay `Corner.lerp F S c`, one corner `c` for all arcs (SharedCorner);
* `Corner.Scat κ (lerp F S c) d`, `0 ≤ κ ≤ 1`.

If a band file has `f0 > f1` (the committed FAST files do, `formal/notes/A-kapres2.md`) the
hypothesis `f0 ≤ F ≤ f1` is unsatisfiable and the theorems say nothing about that arc: the
band-file validator (`tools-A/kappa/kapres2/check_bands.py`, `Formal.Core.XAudit.BandCheck.readBands`) is what makes
them non-vacuous.

## What is proved

* `lerp_min_le`, `lerp_le_max`: for `ca ≤ c ≤ cb`, `lerp F S c` lies between its values at
  `ca` and `cb` (no sign condition on `S - F`).
* `cell_band`: the statement proposed in `A-kapres.md` §2.
* `cell_band_mem`: real form of the cover with endpoint intervals.
* `cell_band_int`: the same for the integer band `cellLo`/`cellHi` (exact ℚ arithmetic,
  floor / ceiling: the transcription of `cornerband2.py`).
* `cell_band_nat`, `realizes_cell`: the same for the ℕ model `Substrate.CornerNat`
  (decidable `Scat` at an ℕ corner `w1/(w0+w1)`): every arc of an assignment realised at one
  shared corner in the cell lies in its cell band.
* `corner_mem_iff`: the ℕ corner is in a rational cell iff two ℕ/ℚ inequalities hold.
* `cellLo_anti`, `cellHi_mono`: widening κ or the cell widens every band (the containment
  used by the sweep's `implied_clean`).
* `cover_mem`: a list of cells that is contiguous from 0 to 1 contains every `c ∈ [0,1]`.

## What is NOT covered

Whether the model is true of silicon; whether the band files hold prjxray's numbers
correctly; anything about the timing checker itself.
-/

namespace Formal.Core.CornerCell

open Formal.Core.Corner

/-! ## 1. Affine interpolation on a cell -/

theorem lerp_sub (F S c c' : ℝ) : lerp F S c - lerp F S c' = (c - c') * (S - F) := by
  unfold lerp; ring

theorem lerp_min_le {F S ca cb c : ℝ} (h1 : ca ≤ c) (h2 : c ≤ cb) :
    min (lerp F S ca) (lerp F S cb) ≤ lerp F S c := by
  rcases le_total F S with h | h
  · have e := lerp_sub F S c ca
    have : 0 ≤ (c - ca) * (S - F) := mul_nonneg (by linarith) (by linarith)
    exact (min_le_left _ _).trans (by linarith)
  · have e := lerp_sub F S c cb
    have : 0 ≤ (cb - c) * (F - S) := mul_nonneg (by linarith) (by linarith)
    exact (min_le_right _ _).trans (by linarith)

theorem lerp_le_max {F S ca cb c : ℝ} (h1 : ca ≤ c) (h2 : c ≤ cb) :
    lerp F S c ≤ max (lerp F S ca) (lerp F S cb) := by
  rcases le_total F S with h | h
  · have e := lerp_sub F S cb c
    have : 0 ≤ (cb - c) * (S - F) := mul_nonneg (by linarith) (by linarith)
    exact le_trans (by linarith) (le_max_right _ _)
  · have e := lerp_sub F S ca c
    have : 0 ≤ (c - ca) * (F - S) := mul_nonneg (by linarith) (by linarith)
    exact le_trans (by linarith) (le_max_left _ _)

/-- `lerp` is monotone in both endpoints on `[0,1]`. -/
theorem lerp_mono {F S F' S' c : ℝ} (hF : F ≤ F') (hS : S ≤ S') (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    lerp F S c ≤ lerp F' S' c := by
  unfold lerp
  have h1 : 0 ≤ (1 - c) * (F' - F) := mul_nonneg (by linarith) (by linarith)
  have h2 : 0 ≤ c * (S' - S) := mul_nonneg hc0 (by linarith)
  linarith

/-- **The cell lemma** (the statement proposed in `A-kapres.md` §2; the proposal's
`0 ≤ ca` and `cb ≤ 1` are not needed). -/
theorem cell_band {F S ca cb c κ : ℝ} (hcab : ca ≤ c) (hcb : c ≤ cb)
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) :
    (1 - κ) * min (lerp F S ca) (lerp F S cb) ≤ (1 - κ) * lerp F S c ∧
    (1 + κ) * lerp F S c ≤ (1 + κ) * max (lerp F S ca) (lerp F S cb) :=
  ⟨mul_le_mul_of_nonneg_left (lerp_min_le hcab hcb) (by linarith),
   mul_le_mul_of_nonneg_left (lerp_le_max hcab hcb) (by linarith)⟩

/-- **Cell cover, real form.** Any endpoints `F ∈ [Fl, Fh]`, `S ∈ [Sl, Sh]`, any corner
`c ∈ [ca, cb] ⊆ [0,1]`, any delay `d` with `Scat κ (lerp F S c) d`: `d` lies in the cell band. -/
theorem cell_band_mem {Fl Fh Sl Sh F S ca cb c κ d : ℝ}
    (hFl : Fl ≤ F) (hFh : F ≤ Fh) (hSl : Sl ≤ S) (hSh : S ≤ Sh)
    (hca : 0 ≤ ca) (hcab : ca ≤ c) (hcb : c ≤ cb) (hcb1 : cb ≤ 1)
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hd : Scat κ (lerp F S c) d) :
    (1 - κ) * min (lerp Fl Sl ca) (lerp Fl Sl cb) ≤ d ∧
    d ≤ (1 + κ) * max (lerp Fh Sh ca) (lerp Fh Sh cb) := by
  have hc0 : 0 ≤ c := le_trans hca hcab
  have hc1 : c ≤ 1 := le_trans hcb hcb1
  obtain ⟨h1, h2⟩ := hd
  constructor
  · have a := lerp_min_le (F := Fl) (S := Sl) hcab hcb
    have b := lerp_mono hFl hSl hc0 hc1
    have := mul_le_mul_of_nonneg_left (le_trans a b) (by linarith : (0 : ℝ) ≤ 1 - κ)
    linarith
  · have a := lerp_le_max (F := Fh) (S := Sh) hcab hcb
    have b := lerp_mono hFh hSh hc0 hc1
    have := mul_le_mul_of_nonneg_left (le_trans b a) (by linarith : (0 : ℝ) ≤ 1 + κ)
    linarith

/-! ## 2. The integer band (transcription of `kapres2/cornerband2.py`) -/

/-- `lerp` over ℚ (the sweep's exact arithmetic). -/
def lerpQ (f s c : ℚ) : ℚ := (1 - c) * f + c * s

/-- Lower end of the cell band of an arc with FAST band `[f0, f1]` and SLOW band `[s0, s1]`. -/
def cellLo (f0 _f1 s0 _s1 : ℕ) (ca cb κ : ℚ) : ℤ :=
  ⌊(1 - κ) * min (lerpQ f0 s0 ca) (lerpQ f0 s0 cb)⌋

/-- Upper end of the cell band. -/
def cellHi (_f0 f1 _s0 s1 : ℕ) (ca cb κ : ℚ) : ℤ :=
  ⌈(1 + κ) * max (lerpQ f1 s1 ca) (lerpQ f1 s1 cb)⌉

theorem cast_lerpQ (f s c : ℚ) : ((lerpQ f s c : ℚ) : ℝ) = lerp f s c := by
  unfold lerpQ lerp; push_cast; ring

/-- **Cell cover, integer band.** The arc's real endpoints lie in its two (validated, so
non-empty) band-file intervals; the corner `c` is in the rational cell `[ca, cb] ⊆ [0,1]`;
`0 ≤ κ ≤ 1`; the real delay `d` satisfies the corner model's scatter at `c`. Then
`cellLo ≤ d ≤ cellHi`. -/
theorem cell_band_int {f0 f1 s0 s1 : ℕ} {ca cb κ : ℚ} {F S c d : ℝ}
    (hFl : (f0 : ℝ) ≤ F) (hFh : F ≤ f1) (hSl : (s0 : ℝ) ≤ S) (hSh : S ≤ s1)
    (hca : 0 ≤ ca) (hcab : (ca : ℝ) ≤ c) (hcb : c ≤ cb) (hcb1 : cb ≤ 1)
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hd : Scat κ (lerp F S c) d) :
    (cellLo f0 f1 s0 s1 ca cb κ : ℝ) ≤ d ∧ d ≤ (cellHi f0 f1 s0 s1 ca cb κ : ℝ) := by
  have hca' : (0 : ℝ) ≤ ca := by exact_mod_cast hca
  have hcb1' : (cb : ℝ) ≤ 1 := by exact_mod_cast hcb1
  have hκ0' : (0 : ℝ) ≤ κ := by exact_mod_cast hκ0
  have hκ1' : (κ : ℝ) ≤ 1 := by exact_mod_cast hκ1
  obtain ⟨h1, h2⟩ := cell_band_mem hFl hFh hSl hSh hca' hcab hcb hcb1' hκ0' hκ1' hd
  constructor
  · unfold cellLo
    have e : (((1 - κ) * min (lerpQ f0 s0 ca) (lerpQ f0 s0 cb) : ℚ) : ℝ)
        = (1 - (κ : ℝ)) * min (lerp f0 s0 ca) (lerp f0 s0 cb) := by
      push_cast [Rat.cast_min, cast_lerpQ]; rfl
    have hf : ((⌊(1 - κ) * min (lerpQ f0 s0 ca) (lerpQ f0 s0 cb)⌋ : ℤ) : ℚ)
        ≤ (1 - κ) * min (lerpQ f0 s0 ca) (lerpQ f0 s0 cb) := Int.floor_le _
    have hr : ((⌊(1 - κ) * min (lerpQ f0 s0 ca) (lerpQ f0 s0 cb)⌋ : ℤ) : ℝ)
        ≤ (((1 - κ) * min (lerpQ f0 s0 ca) (lerpQ f0 s0 cb) : ℚ) : ℝ) := by
      exact_mod_cast hf
    have : ((f0 : ℚ) : ℝ) = (f0 : ℝ) := by push_cast; rfl
    rw [e] at hr
    simpa using le_trans hr (by simpa using h1)
  · unfold cellHi
    have e : (((1 + κ) * max (lerpQ f1 s1 ca) (lerpQ f1 s1 cb) : ℚ) : ℝ)
        = (1 + (κ : ℝ)) * max (lerp f1 s1 ca) (lerp f1 s1 cb) := by
      push_cast [Rat.cast_max, cast_lerpQ]; rfl
    have hf : (1 + κ) * max (lerpQ f1 s1 ca) (lerpQ f1 s1 cb)
        ≤ ((⌈(1 + κ) * max (lerpQ f1 s1 ca) (lerpQ f1 s1 cb)⌉ : ℤ) : ℚ) := Int.le_ceil _
    have hr : (((1 + κ) * max (lerpQ f1 s1 ca) (lerpQ f1 s1 cb) : ℚ) : ℝ)
        ≤ ((⌈(1 + κ) * max (lerpQ f1 s1 ca) (lerpQ f1 s1 cb)⌉ : ℤ) : ℝ) := by
      exact_mod_cast hf
    rw [e] at hr
    exact le_trans (by simpa using h2) (by simpa using hr)

/-! ## 3. The ℕ model (`Substrate.CornerNat`) -/

open Formal.Core.Substrate in
/-- The ℕ corner `w1/(w0+w1)` lies in the rational cell `[ca, cb]` iff
`ca·W ≤ w1` and `w1 ≤ cb·W` (decidable over ℚ). -/
theorem corner_mem_iff (c : Substrate.Corner) (ca cb : ℚ) :
    ((ca : ℝ) ≤ c.toReal ∧ c.toReal ≤ cb) ↔ (ca * c.W ≤ c.w1 ∧ (c.w1 : ℚ) ≤ cb * c.W) := by
  have hW : (0 : ℝ) < c.W := by exact_mod_cast c.W_pos
  unfold Substrate.Corner.toReal
  rw [le_div_iff₀ hW, div_le_iff₀ hW]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

open Formal.Core.Substrate in
/-- **Cell cover, ℕ model.** An ℕ delay `d` that satisfies the decidable corner-model
scatter `Substrate.Scat k c a d` at an ℕ corner `c` inside the cell lies in the integer cell
band with `κ = num/den`, provided the arc's endpoints lie in its band-file intervals. -/
theorem cell_band_nat {f0 f1 s0 s1 : ℕ} {ca cb : ℚ} {k : Kappa} {c : Substrate.Corner}
    {a : CArc} {d : ℕ}
    (hF : f0 ≤ a.F ∧ a.F ≤ f1) (hS : s0 ≤ a.S ∧ a.S ≤ s1)
    (hca : 0 ≤ ca) (hc : (ca : ℝ) ≤ c.toReal ∧ c.toReal ≤ cb) (hcb1 : cb ≤ 1)
    (h : Substrate.Scat k c a d) :
    cellLo f0 f1 s0 s1 ca cb ((k.num : ℚ) / k.den) ≤ d ∧
    (d : ℤ) ≤ cellHi f0 f1 s0 s1 ca cb ((k.num : ℚ) / k.den) := by
  have hr := scat_real h
  have hden : (0 : ℚ) < k.den := by exact_mod_cast k.den_pos
  have hκ0 : (0 : ℚ) ≤ (k.num : ℚ) / k.den := div_nonneg (Nat.cast_nonneg _) hden.le
  have hκ1 : (k.num : ℚ) / k.den ≤ 1 := by
    rw [div_le_one hden]; exact_mod_cast k.num_le
  have hκ : (((k.num : ℚ) / k.den : ℚ) : ℝ) = k.toReal := by
    unfold Kappa.toReal; push_cast; rfl
  have hr' : Formal.Core.Corner.Scat (((k.num : ℚ) / k.den : ℚ) : ℝ)
      (lerp (a.F : ℝ) (a.S : ℝ) c.toReal) (d : ℝ) := by
    rw [hκ]; exact hr
  obtain ⟨l, u⟩ := cell_band_int (f0 := f0) (f1 := f1) (s0 := s0) (s1 := s1)
    (by exact_mod_cast hF.1) (by exact_mod_cast hF.2)
    (by exact_mod_cast hS.1) (by exact_mod_cast hS.2) hca hc.1 hc.2 hcb1 hκ0 hκ1 hr'
  exact ⟨by exact_mod_cast l, by exact_mod_cast u⟩

open Formal.Core.Substrate in
/-- **Every arc at once** (SharedCorner): an assignment realised at ONE ℕ corner inside the
cell has every arc's delay in that arc's cell band. `fb e`, `sb e` are the FAST and SLOW
band-file pairs of arc `e`, assumed to contain the arc's endpoints. -/
theorem realizes_cell {A : Type} (M : CornerModel A) (fb sb : A → ℕ × ℕ)
    (hF : ∀ e, (fb e).1 ≤ (M.arc e).F ∧ (M.arc e).F ≤ (fb e).2)
    (hS : ∀ e, (sb e).1 ≤ (M.arc e).S ∧ (M.arc e).S ≤ (sb e).2)
    {ca cb : ℚ} (hca : 0 ≤ ca) (hcb1 : cb ≤ 1) {c : Substrate.Corner}
    (hc : (ca : ℝ) ≤ c.toReal ∧ c.toReal ≤ cb) {d : A → ℕ} (h : M.RealizesAt c d) (e : A) :
    cellLo (fb e).1 (fb e).2 (sb e).1 (sb e).2 ca cb ((M.κ.num : ℚ) / M.κ.den) ≤ d e ∧
    (d e : ℤ) ≤ cellHi (fb e).1 (fb e).2 (sb e).1 (sb e).2 ca cb ((M.κ.num : ℚ) / M.κ.den) :=
  cell_band_nat (hF e) (hS e) hca hc hcb1 (h e)

/-! ## 4. Widening (the sweep's `implied_clean`) and covers -/

theorem lerpQ_sub (F S c c' : ℚ) : lerpQ F S c - lerpQ F S c' = (c - c') * (S - F) := by
  unfold lerpQ; ring

theorem lerpQ_min_le {F S ca cb c : ℚ} (h1 : ca ≤ c) (h2 : c ≤ cb) :
    min (lerpQ F S ca) (lerpQ F S cb) ≤ lerpQ F S c := by
  rcases le_total F S with h | h
  · have e := lerpQ_sub F S c ca
    have : 0 ≤ (c - ca) * (S - F) := mul_nonneg (by linarith) (by linarith)
    exact (min_le_left _ _).trans (by linarith)
  · have e := lerpQ_sub F S c cb
    have : 0 ≤ (cb - c) * (F - S) := mul_nonneg (by linarith) (by linarith)
    exact (min_le_right _ _).trans (by linarith)

theorem lerpQ_le_max {F S ca cb c : ℚ} (h1 : ca ≤ c) (h2 : c ≤ cb) :
    lerpQ F S c ≤ max (lerpQ F S ca) (lerpQ F S cb) := by
  rcases le_total F S with h | h
  · have e := lerpQ_sub F S cb c
    have : 0 ≤ (cb - c) * (S - F) := mul_nonneg (by linarith) (by linarith)
    exact le_trans (by linarith) (le_max_right _ _)
  · have e := lerpQ_sub F S ca c
    have : 0 ≤ (c - ca) * (F - S) := mul_nonneg (by linarith) (by linarith)
    exact le_trans (by linarith) (le_max_left _ _)

theorem lerpQ_nonneg {F S c : ℚ} (hF : 0 ≤ F) (hS : 0 ≤ S) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    0 ≤ lerpQ F S c := by
  unfold lerpQ
  have := mul_nonneg (by linarith : (0 : ℚ) ≤ 1 - c) hF
  have := mul_nonneg hc0 hS
  linarith

/-- Widening κ or the cell can only lower the lower end. -/
theorem cellLo_anti {f0 f1 s0 s1 : ℕ} {ca cb ca' cb' κ κ' : ℚ}
    (h0 : 0 ≤ ca') (h1 : ca' ≤ ca) (h2 : ca ≤ cb) (h3 : cb ≤ cb') (h4 : cb' ≤ 1)
    (hk : κ ≤ κ') (hk1 : κ' ≤ 1) :
    cellLo f0 f1 s0 s1 ca' cb' κ' ≤ cellLo f0 f1 s0 s1 ca cb κ := by
  unfold cellLo
  apply Int.floor_mono
  have hF : (0 : ℚ) ≤ f0 := Nat.cast_nonneg _
  have hS : (0 : ℚ) ≤ s0 := Nat.cast_nonneg _
  have ma := lerpQ_min_le (F := f0) (S := s0) h1 (le_trans h2 h3)
  have mb := lerpQ_min_le (F := f0) (S := s0) (le_trans h1 h2) h3
  have hm : min (lerpQ f0 s0 ca') (lerpQ f0 s0 cb') ≤ min (lerpQ f0 s0 ca) (lerpQ f0 s0 cb) :=
    le_min ma mb
  have hnn : 0 ≤ min (lerpQ f0 s0 ca') (lerpQ f0 s0 cb') :=
    le_min (lerpQ_nonneg hF hS h0 (by linarith)) (lerpQ_nonneg hF hS (by linarith) h4)
  have a := mul_le_mul_of_nonneg_right (by linarith : 1 - κ' ≤ 1 - κ) hnn
  have c := mul_le_mul_of_nonneg_left hm (by linarith : (0 : ℚ) ≤ 1 - κ)
  linarith

/-- Widening κ or the cell can only raise the upper end. -/
theorem cellHi_mono {f0 f1 s0 s1 : ℕ} {ca cb ca' cb' κ κ' : ℚ}
    (h0 : 0 ≤ ca') (h1 : ca' ≤ ca) (h2 : ca ≤ cb) (h3 : cb ≤ cb') (h4 : cb' ≤ 1)
    (hk0 : 0 ≤ κ) (hk : κ ≤ κ') :
    cellHi f0 f1 s0 s1 ca cb κ ≤ cellHi f0 f1 s0 s1 ca' cb' κ' := by
  unfold cellHi
  apply Int.ceil_mono
  have hF : (0 : ℚ) ≤ f1 := Nat.cast_nonneg _
  have hS : (0 : ℚ) ≤ s1 := Nat.cast_nonneg _
  have ma := lerpQ_le_max (F := f1) (S := s1) h1 (le_trans h2 h3)
  have mb := lerpQ_le_max (F := f1) (S := s1) (le_trans h1 h2) h3
  have hm : max (lerpQ f1 s1 ca) (lerpQ f1 s1 cb) ≤ max (lerpQ f1 s1 ca') (lerpQ f1 s1 cb') :=
    max_le ma mb
  have hnn : 0 ≤ max (lerpQ f1 s1 ca) (lerpQ f1 s1 cb) :=
    le_trans (lerpQ_nonneg hF hS (by linarith) (by linarith)) (le_max_left _ _)
  have a := mul_le_mul_of_nonneg_right (by linarith : 1 + κ ≤ 1 + κ') hnn
  have b := mul_le_mul_of_nonneg_left hm (by linarith : (0 : ℚ) ≤ 1 + κ')
  linarith

/-- A list of cells `[(a₀,b₀), …]` is a cover of `[0,1]` when it starts at 0, ends at 1 and
each cell starts where the previous one ends (`kapres2/table2.py` checks exactly this). -/
def Chain : ℚ → List (ℚ × ℚ) → Prop
  | x, [] => x = 1
  | x, p :: l => p.1 = x ∧ p.1 ≤ p.2 ∧ Chain p.2 l

theorem chain_mem : ∀ (x : ℚ) (l : List (ℚ × ℚ)), Chain x l → ∀ c : ℝ, (x : ℝ) < c → c ≤ 1 →
    ∃ p ∈ l, (p.1 : ℝ) ≤ c ∧ c ≤ p.2
  | x, [], h, c, h1, h2 => by
      simp only [Chain] at h; subst h; push_cast at h1; exact absurd h2 (not_le.mpr h1)
  | x, p :: l, ⟨hx, _, hl⟩, c, h1, h2 => by
      by_cases hc : c ≤ p.2
      · exact ⟨p, List.mem_cons_self .., by rw [hx]; exact h1.le, hc⟩
      · obtain ⟨q, hq, hq1, hq2⟩ := chain_mem p.2 l hl c (not_le.mp hc) h2
        exact ⟨q, List.mem_cons_of_mem _ hq, hq1, hq2⟩

/-- **Cover.** Every corner `c ∈ [0,1]` lies in some cell of a chain from 0 to 1. -/
theorem cover_mem {l : List (ℚ × ℚ)} (h : Chain 0 l) {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) :
    ∃ p ∈ l, (p.1 : ℝ) ≤ c ∧ c ≤ p.2 := by
  rcases lt_or_eq_of_le h0 with hc | hc
  · exact chain_mem 0 l h c (by simpa using hc) h1
  · subst hc
    match l, h with
    | [], h => simp [Chain] at h
    | p :: _, ⟨hp, hle, _⟩ =>
      refine ⟨p, List.mem_cons_self .., by rw [hp]; simp, ?_⟩
      have : (0 : ℚ) ≤ p.2 := hp ▸ hle
      exact_mod_cast this

end Formal.Core.CornerCell
