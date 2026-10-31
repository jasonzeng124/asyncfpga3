import Formal.Core.Delay.Corner
import Formal.Core.Substrate.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor

/-!
# Corner cells: one band covers a whole interval of corners

Probe KapRes2 (shard A). The KapRes sweep (`formal/tools-A/xaudit/kapres/cornerband.py`,
`formal/notes/A-kapres.md` §2) runs the per-pin checker once per corner CELL
`[ca, cb] ⊆ [0, 1]` instead of once per corner. This file proves that this is sound
against the corner model of `Formal.Core.Corner` (H-affine `lerp`, one shared corner,
`Scat κ`), with the endpoints of each arc known only up to prjxray's per-corner
`[MIN, MAX]`, and with exactly the rational arithmetic and outward integer rounding
that `cornerband.py` performs.

## Statements

* `lerp_min_le`, `lerp_le_max`: for `ca ≤ c ≤ cb`, `lerp F S c` lies between
  `lerp F S ca` and `lerp F S cb` (an affine function of `c`). No sign condition on
  `F`, `S`, `c`.
* `cell_band` (the statement proposed in A-kapres §2, verbatim up to hypotheses that are
  not needed).
* `cell_band_mem`: every delay allowed by `Scat κ` at any corner `c ∈ [ca, cb]` for any
  admissible endpoints `F ∈ [Fl, Fh]`, `S ∈ [Sl, Sh]` lies in
  `[(1-κ)·min(lerp Fl Sl ca, lerp Fl Sl cb), (1+κ)·max(lerp Fh Sh ca, lerp Fh Sh cb)]`.
* `cellLo`, `cellHi`: `cornerband.py`'s per-arc band, transcribed: integer band
  `[f0, f1]` (fast, possibly inverted, read as its hull `[min, max]`), `[s0, s1]` (slow,
  likewise), rational `ca, cb, κ`, `⌊·⌋` / `⌈·⌉` of exact rationals.
  §5 checks the transcription on four arcs against the Python output (`decide +kernel`).
* **`cell_band_int`**: the real delay `d` at any real corner `c ∈ [ca, cb]`, for any real
  endpoints inside the hulls, with `Scat κ` lies in `[cellLo, cellHi]`.
* `cell_band_nat`: the same for the ℕ model `Substrate.CornerNat` (an ℕ delay `d`
  satisfying `Substrate.Scat k c a d` at an ℕ corner whose real value is in `[ca, cb]`).
* **`cellLo_anti`, `cellHi_mono`** (widening): for nonnegative endpoints, a larger κ and a
  larger cell give a band that contains the smaller one. This is the containment lemma
  the sweep uses to skip cells (`implied_clean`).

## Hypotheses / what is NOT covered

* The model hypotheses of `Formal.Core.Corner` (H-affine, SharedCorner, symmetric relative
  scatter `0 ≤ κ ≤ 1`). Nothing here says the model is true of silicon.
* The endpoints of each arc are assumed to lie in the hull of the committed one-corner band
  file numbers. That the band files contain prjxray's numbers correctly is a property of the
  data pipeline (`routed2x.py`), not proved here.
* Gate bands in the band files are aggregates (min lo / max hi over IOPATH rows); the
  statement is per arc; the aggregate step is the same lemma applied row by row and is not
  formalised.
* The global `lut` / `route` summary fields that `cornerband.py` also writes are not covered.
* This file says nothing about the checker (`xevents*`); only that its input bands contain
  every delay the model allows on the cell.
-/

namespace Formal.Core.Corner

/-! ## 1. Real statements -/

theorem lerp_min_le {F S ca c cb : ℝ} (h1 : ca ≤ c) (h2 : c ≤ cb) :
    min (lerp F S ca) (lerp F S cb) ≤ lerp F S c := by
  unfold lerp
  rcases le_total F S with h | h
  · exact min_le_of_left_le (by nlinarith)
  · exact min_le_of_right_le (by nlinarith)

theorem lerp_le_max {F S ca c cb : ℝ} (h1 : ca ≤ c) (h2 : c ≤ cb) :
    lerp F S c ≤ max (lerp F S ca) (lerp F S cb) := by
  unfold lerp
  rcases le_total F S with h | h
  · exact le_max_of_le_right (by nlinarith)
  · exact le_max_of_le_left (by nlinarith)

/-- `lerp` is monotone in both endpoints on `c ∈ [0, 1]`. -/
theorem lerp_mono {F F' S S' c : ℝ} (hF : F ≤ F') (hS : S ≤ S') (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    lerp F S c ≤ lerp F' S' c := by
  unfold lerp
  have := mul_le_mul_of_nonneg_left hF (by linarith : (0:ℝ) ≤ 1 - c)
  have := mul_le_mul_of_nonneg_left hS hc0
  linarith

/-- **The cell lemma** as proposed in A-kapres §2 (the proposal's `0 ≤ ca`, `cb ≤ 1` are
not needed for this form). -/
theorem cell_band {F S ca cb c κ : ℝ} (hcab : ca ≤ c) (hcb : c ≤ cb) (hκ0 : 0 ≤ κ)
    (hκ1 : κ ≤ 1) :
    (1 - κ) * min (lerp F S ca) (lerp F S cb) ≤ (1 - κ) * lerp F S c ∧
    (1 + κ) * lerp F S c ≤ (1 + κ) * max (lerp F S ca) (lerp F S cb) :=
  ⟨mul_le_mul_of_nonneg_left (lerp_min_le hcab hcb) (by linarith),
   mul_le_mul_of_nonneg_left (lerp_le_max hcab hcb) (by linarith)⟩

/-- **Every delay the model allows on the cell lies in the cell band**, for any endpoints
`F ∈ [Fl, Fh]`, `S ∈ [Sl, Sh]` (prjxray gives each corner only as `[MIN, MAX]`). -/
theorem cell_band_mem {Fl Fh Sl Sh F S ca cb c κ d : ℝ}
    (hF : Fl ≤ F ∧ F ≤ Fh) (hS : Sl ≤ S ∧ S ≤ Sh)
    (hca : 0 ≤ ca) (hcab : ca ≤ c) (hcb : c ≤ cb) (hcb1 : cb ≤ 1)
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hd : Scat κ (lerp F S c) d) :
    (1 - κ) * min (lerp Fl Sl ca) (lerp Fl Sl cb) ≤ d ∧
    d ≤ (1 + κ) * max (lerp Fh Sh ca) (lerp Fh Sh cb) := by
  obtain ⟨h1, h2⟩ := hd
  have hc0 : 0 ≤ c := le_trans hca hcab
  have hc1 : c ≤ 1 := le_trans hcb hcb1
  have ml := lerp_mono hF.1 hS.1 hc0 hc1
  have mh := lerp_mono hF.2 hS.2 hc0 hc1
  obtain ⟨b1, -⟩ := cell_band (F := Fl) (S := Sl) hcab hcb hκ0 hκ1
  obtain ⟨-, b2⟩ := cell_band (F := Fh) (S := Sh) hcab hcb hκ0 hκ1
  have e1 := mul_le_mul_of_nonneg_left ml (by linarith : (0:ℝ) ≤ 1 - κ)
  have e2 := mul_le_mul_of_nonneg_left mh (by linarith : (0:ℝ) ≤ 1 + κ)
  exact ⟨by linarith, by linarith⟩

/-! ## 2. `cornerband.py`'s integer band, transcribed

`cornerband.py` reads the fast band `[f0, f1]` and the slow band `[s0, s1]` (whole ps),
takes `flo, fhi = min(f0,f1), max(f0,f1)` and `slo, shi` likewise, and writes
`lo = floor((1-κ)·min(lerp(flo,slo,ca), lerp(flo,slo,cb)))`,
`hi = ceil((1+κ)·max(lerp(fhi,shi,ca), lerp(fhi,shi,cb)))` in exact rationals
(`fractions.Fraction`). -/

/-- `lerp` over ℚ (the Python `lerp` on `Fraction`s). -/
def qlerp (F S c : ℚ) : ℚ := (1 - c) * F + c * S

/-- `cornerband.py`'s lo end. -/
def cellLo (f0 f1 s0 s1 : ℤ) (ca cb κ : ℚ) : ℤ :=
  ⌊(1 - κ) * min (qlerp (min f0 f1 : ℤ) (min s0 s1 : ℤ) ca)
                 (qlerp (min f0 f1 : ℤ) (min s0 s1 : ℤ) cb)⌋

/-- `cornerband.py`'s hi end. -/
def cellHi (f0 f1 s0 s1 : ℤ) (ca cb κ : ℚ) : ℤ :=
  ⌈(1 + κ) * max (qlerp (max f0 f1 : ℤ) (max s0 s1 : ℤ) ca)
                 (qlerp (max f0 f1 : ℤ) (max s0 s1 : ℤ) cb)⌉

theorem qlerp_cast (F S c : ℚ) : ((qlerp F S c : ℚ) : ℝ) = lerp F S c := by
  unfold qlerp lerp; push_cast; ring

/-- **Cell band, integer form (soundness of `cornerband.py`).** For every real corner
`c ∈ [ca, cb] ⊆ [0, 1]`, every real fast endpoint in the hull of `[f0, f1]`, every real slow
endpoint in the hull of `[s0, s1]`, and every real delay `d` within scatter `κ ∈ [0, 1]` of
the nominal `lerp F S c`: `cellLo ≤ d ≤ cellHi`. -/
theorem cell_band_int {f0 f1 s0 s1 : ℤ} {ca cb κ : ℚ} {F S c d : ℝ}
    (hF : ((min f0 f1 : ℤ) : ℝ) ≤ F ∧ F ≤ ((max f0 f1 : ℤ) : ℝ))
    (hS : ((min s0 s1 : ℤ) : ℝ) ≤ S ∧ S ≤ ((max s0 s1 : ℤ) : ℝ))
    (hca : 0 ≤ ca) (hcab : (ca : ℝ) ≤ c) (hcb : c ≤ (cb : ℝ)) (hcb1 : cb ≤ 1)
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hd : Scat (κ : ℝ) (lerp F S c) d) :
    ((cellLo f0 f1 s0 s1 ca cb κ : ℤ) : ℝ) ≤ d ∧ d ≤ ((cellHi f0 f1 s0 s1 ca cb κ : ℤ) : ℝ) := by
  have hca' : (0:ℝ) ≤ ca := by exact_mod_cast hca
  have hcb1' : (cb:ℝ) ≤ 1 := by exact_mod_cast hcb1
  have hκ0' : (0:ℝ) ≤ κ := by exact_mod_cast hκ0
  have hκ1' : (κ:ℝ) ≤ 1 := by exact_mod_cast hκ1
  obtain ⟨b1, b2⟩ := cell_band_mem hF hS hca' hcab hcb hcb1' hκ0' hκ1' hd
  constructor
  · unfold cellLo
    set x : ℚ := (1 - κ) * min (qlerp (min f0 f1 : ℤ) (min s0 s1 : ℤ) ca)
                 (qlerp (min f0 f1 : ℤ) (min s0 s1 : ℤ) cb) with hx
    have hfl : ((⌊x⌋ : ℤ) : ℚ) ≤ x := Int.floor_le x
    have hfl' : ((⌊x⌋ : ℤ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast hfl
    have hxr : (x : ℝ) = (1 - (κ:ℝ)) * min (lerp ((min f0 f1 : ℤ) : ℝ) ((min s0 s1 : ℤ) : ℝ) ca)
        (lerp ((min f0 f1 : ℤ) : ℝ) ((min s0 s1 : ℤ) : ℝ) cb) := by
      rw [hx]; push_cast [Rat.cast_min, qlerp_cast]; rfl
    linarith
  · unfold cellHi
    set x : ℚ := (1 + κ) * max (qlerp (max f0 f1 : ℤ) (max s0 s1 : ℤ) ca)
                 (qlerp (max f0 f1 : ℤ) (max s0 s1 : ℤ) cb) with hx
    have hcl : x ≤ ((⌈x⌉ : ℤ) : ℚ) := Int.le_ceil x
    have hcl' : (x : ℝ) ≤ ((⌈x⌉ : ℤ) : ℝ) := by exact_mod_cast hcl
    have hxr : (x : ℝ) = (1 + (κ:ℝ)) * max (lerp ((max f0 f1 : ℤ) : ℝ) ((max s0 s1 : ℤ) : ℝ) ca)
        (lerp ((max f0 f1 : ℤ) : ℝ) ((max s0 s1 : ℤ) : ℝ) cb) := by
      rw [hx]; push_cast [Rat.cast_max, qlerp_cast]; rfl
    linarith

/-! ## 3. Widening (containment in κ and in the cell) -/

theorem qlerp_min_le {F S ca c cb : ℚ} (h1 : ca ≤ c) (h2 : c ≤ cb) :
    min (qlerp F S ca) (qlerp F S cb) ≤ qlerp F S c := by
  unfold qlerp
  rcases le_total F S with h | h
  · exact min_le_of_left_le (by nlinarith)
  · exact min_le_of_right_le (by nlinarith)

theorem qlerp_le_max {F S ca c cb : ℚ} (h1 : ca ≤ c) (h2 : c ≤ cb) :
    qlerp F S c ≤ max (qlerp F S ca) (qlerp F S cb) := by
  unfold qlerp
  rcases le_total F S with h | h
  · exact le_max_of_le_right (by nlinarith)
  · exact le_max_of_le_left (by nlinarith)

theorem qlerp_nonneg {F S c : ℚ} (hF : 0 ≤ F) (hS : 0 ≤ S) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    0 ≤ qlerp F S c := by
  unfold qlerp
  have := mul_nonneg (by linarith : (0:ℚ) ≤ 1 - c) hF
  have := mul_nonneg hc0 hS
  linarith

/-- Min over a larger cell is no larger. -/
theorem qmin_widen {F S ca cb ca' cb' : ℚ} (hca : ca' ≤ ca) (hab : ca ≤ cb) (hcb : cb ≤ cb') :
    min (qlerp F S ca') (qlerp F S cb') ≤ min (qlerp F S ca) (qlerp F S cb) :=
  le_min (qlerp_min_le hca (le_trans hab hcb)) (qlerp_min_le (le_trans hca hab) hcb)

theorem qmax_widen {F S ca cb ca' cb' : ℚ} (hca : ca' ≤ ca) (hab : ca ≤ cb) (hcb : cb ≤ cb') :
    max (qlerp F S ca) (qlerp F S cb) ≤ max (qlerp F S ca') (qlerp F S cb') :=
  max_le (qlerp_le_max hca (le_trans hab hcb)) (qlerp_le_max (le_trans hca hab) hcb)

/-- **Widening, lo end.** Nonnegative endpoints, `κ ≤ κ' ≤ 1`, `[ca, cb] ⊆ [ca', cb'] ⊆ [0, 1]`:
the lo end at `(κ', ca', cb')` is at most the lo end at `(κ, ca, cb)`. -/
theorem cellLo_anti {f0 f1 s0 s1 : ℤ} {ca cb ca' cb' κ κ' : ℚ}
    (hf : 0 ≤ min f0 f1) (hs : 0 ≤ min s0 s1)
    (hca0 : 0 ≤ ca') (hca : ca' ≤ ca) (hab : ca ≤ cb) (hcb : cb ≤ cb') (hcb1 : cb' ≤ 1)
    (hκ : κ ≤ κ') (hκ1 : κ' ≤ 1) :
    cellLo f0 f1 s0 s1 ca' cb' κ' ≤ cellLo f0 f1 s0 s1 ca cb κ := by
  unfold cellLo
  apply Int.floor_mono
  have hf' : (0:ℚ) ≤ ((min f0 f1 : ℤ) : ℚ) := by exact_mod_cast hf
  have hs' : (0:ℚ) ≤ ((min s0 s1 : ℤ) : ℚ) := by exact_mod_cast hs
  have hw := qmin_widen (F := ((min f0 f1 : ℤ) : ℚ)) (S := ((min s0 s1 : ℤ) : ℚ)) hca hab hcb
  have h0 : 0 ≤ min (qlerp ((min f0 f1 : ℤ) : ℚ) ((min s0 s1 : ℤ) : ℚ) ca')
      (qlerp ((min f0 f1 : ℤ) : ℚ) ((min s0 s1 : ℤ) : ℚ) cb') :=
    le_min (qlerp_nonneg hf' hs' hca0 (by linarith)) (qlerp_nonneg hf' hs' (by linarith) hcb1)
  have := mul_le_mul_of_nonneg_left hw (by linarith : (0:ℚ) ≤ 1 - κ')
  nlinarith

/-- **Widening, hi end.** Under the same hypotheses the hi end grows. -/
theorem cellHi_mono {f0 f1 s0 s1 : ℤ} {ca cb ca' cb' κ κ' : ℚ}
    (hf : 0 ≤ min f0 f1) (hs : 0 ≤ min s0 s1)
    (hca0 : 0 ≤ ca') (hca : ca' ≤ ca) (hab : ca ≤ cb) (hcb : cb ≤ cb') (hcb1 : cb' ≤ 1)
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ κ') :
    cellHi f0 f1 s0 s1 ca cb κ ≤ cellHi f0 f1 s0 s1 ca' cb' κ' := by
  unfold cellHi
  apply Int.ceil_mono
  have hf' : (0:ℚ) ≤ ((max f0 f1 : ℤ) : ℚ) := by
    have : min f0 f1 ≤ max f0 f1 := min_le_max
    exact_mod_cast le_trans hf this
  have hs' : (0:ℚ) ≤ ((max s0 s1 : ℤ) : ℚ) := by
    have : min s0 s1 ≤ max s0 s1 := min_le_max
    exact_mod_cast le_trans hs this
  have hw := qmax_widen (F := ((max f0 f1 : ℤ) : ℚ)) (S := ((max s0 s1 : ℤ) : ℚ)) hca hab hcb
  have h0 : 0 ≤ max (qlerp ((max f0 f1 : ℤ) : ℚ) ((max s0 s1 : ℤ) : ℚ) ca)
      (qlerp ((max f0 f1 : ℤ) : ℚ) ((max s0 s1 : ℤ) : ℚ) cb) :=
    le_max_of_le_left (qlerp_nonneg hf' hs' (by linarith) (by linarith))
  have := mul_le_mul_of_nonneg_left hw (by linarith : (0:ℚ) ≤ 1 + κ')
  nlinarith

/-! ## 4. The ℕ model (`Substrate.CornerNat`) -/

open Formal.Core.Substrate in
/-- **Cell band for the ℕ corner model.** An ℕ delay `d` that satisfies the decidable
`Substrate.Scat k c a d` at an ℕ corner `c` whose value `w1/(w0+w1)` lies in `[ca, cb]`, for an
arc whose endpoints lie in the band-file hulls, lies in `[cellLo, cellHi]` with κ = num/den. -/
theorem cell_band_nat {f0 f1 s0 s1 : ℤ} {ca cb : ℚ} {k : Kappa} {c : Substrate.Corner} {a : CArc}
    {d : ℕ}
    (hF : min f0 f1 ≤ (a.F : ℤ) ∧ (a.F : ℤ) ≤ max f0 f1)
    (hS : min s0 s1 ≤ (a.S : ℤ) ∧ (a.S : ℤ) ≤ max s0 s1)
    (hca : 0 ≤ ca) (hcab : (ca : ℝ) ≤ c.toReal) (hcb : c.toReal ≤ (cb : ℝ)) (hcb1 : cb ≤ 1)
    (hd : Substrate.Scat k c a d) :
    cellLo f0 f1 s0 s1 ca cb ((k.num : ℚ) / k.den) ≤ (d : ℤ) ∧
    (d : ℤ) ≤ cellHi f0 f1 s0 s1 ca cb ((k.num : ℚ) / k.den) := by
  have hκ : (((k.num : ℚ) / k.den : ℚ) : ℝ) = k.toReal := by
    unfold Kappa.toReal; push_cast; rfl
  have hκ0 : (0:ℚ) ≤ (k.num : ℚ) / k.den := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hκ1 : (k.num : ℚ) / k.den ≤ 1 := by
    rw [div_le_one (by exact_mod_cast k.den_pos)]; exact_mod_cast k.num_le
  have hr := scat_real hd
  rw [← hκ] at hr
  have hF' : ((min f0 f1 : ℤ) : ℝ) ≤ (a.F : ℝ) ∧ (a.F : ℝ) ≤ ((max f0 f1 : ℤ) : ℝ) :=
    ⟨by exact_mod_cast hF.1, by exact_mod_cast hF.2⟩
  have hS' : ((min s0 s1 : ℤ) : ℝ) ≤ (a.S : ℝ) ∧ (a.S : ℝ) ≤ ((max s0 s1 : ℤ) : ℝ) :=
    ⟨by exact_mod_cast hS.1, by exact_mod_cast hS.2⟩
  obtain ⟨h1, h2⟩ := cell_band_int hF' hS' hca hcab hcb hcb1 hκ0 hκ1 hr
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

/-! ## 5. Spot checks against `cornerband.py`

Values printed by `cornerband.py`'s formula (`formal/tools-A/xaudit/kapres2/spot.py`). -/

example : cellLo 95 103 211 230 (1/8 : ℚ) (1/4 : ℚ) (1/10 : ℚ) = 98 := by decide +kernel
example : cellHi 95 103 211 230 (1/8 : ℚ) (1/4 : ℚ) (1/10 : ℚ) = 149 := by decide +kernel
example : cellLo 412 377 905 951 (0/1 : ℚ) (1/16 : ℚ) (453/5000 : ℚ) = 342 := by decide +kernel
example : cellHi 412 377 905 951 (0/1 : ℚ) (1/16 : ℚ) (453/5000 : ℚ) = 487 := by decide +kernel
example : cellLo 1 1 2 3 (3/32 : ℚ) (1/8 : ℚ) (1/20 : ℚ) = 1 := by decide +kernel
example : cellHi 1 1 2 3 (3/32 : ℚ) (1/8 : ℚ) (1/20 : ℚ) = 2 := by decide +kernel
example : cellLo 240 260 233 250 (7/8 : ℚ) (1/1 : ℚ) (1/10 : ℚ) = 209 := by decide +kernel
example : cellHi 240 260 233 250 (7/8 : ℚ) (1/1 : ℚ) (1/10 : ℚ) = 277 := by decide +kernel

end Formal.Core.Corner
