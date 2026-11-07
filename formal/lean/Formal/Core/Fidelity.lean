import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Fidelity: from prjxray timing numbers to delay hypotheses

The bridge between prjxray-db's timing data for the xc7z010-1 and the delay
hypotheses that circuit proofs take as arguments. See
`formal/notes/A-fidelity.md` for which primitive each piece models, how
faithful that is, and how each hypothesis could be tested.

* `DelayBound`: a delay known only to lie in `[lo, hi]`, with `0 ≤ lo ≤ hi`.
  For one prjxray element: `lo` = FAST corner min, `hi` = SLOW corner max.
  `series` adds two bounds (interval sum). It is associative and
  commutative, has `zero` as its unit, and is monotone for containment
  (`DelayBound.Le`). `path` folds a list of hops, and `mem_path` is the
  bridge theorem: if each hop's real delay lies in its bound, the path's
  real delay lies in the path bound.
* `elmore`: Elmore delay of an RC ladder, the reduced form of prjxray's
  `timing.py` RC tree seen from one sink. Each section is a series R
  followed by a C to ground. A side branch's total capacitance is lumped
  onto its branch node, which is exact for Elmore. `elmorePi` is the
  pi-model variant prjxray uses for wires: a wire's own R sees only half of
  its own C. Both are monotone in every R and every C (`elmore_mono`,
  `elmore_mono_R`, `elmore_mono_C`, `elmorePi_mono`), and
  `elmorePi ≤ elmore`.
* `rcBound` turns per-element R/C ranges into a `DelayBound`, and
  `mem_rcBound` gives soundness. The model-error factor `κ` and the
  claim that real R and C lie in their ranges are explicit hypotheses.

Everything here is unit-agnostic. prjxray-db stores R in Ω and C in fF, so
`R·C·1e-6` is in ns. Callers pick consistent units.
-/

noncomputable section

namespace Formal.Core.Fidelity

/-! ## Delay bounds -/

/-- A delay known only to lie in `[lo, hi]`. -/
structure DelayBound where
  lo : ℝ
  hi : ℝ
  lo_nonneg : 0 ≤ lo
  lo_le_hi : lo ≤ hi

namespace DelayBound

theorem ext' {a b : DelayBound} (h1 : a.lo = b.lo) (h2 : a.hi = b.hi) : a = b := by
  cases a with
  | mk alo ahi ah0 ah1 =>
    cases b with
    | mk blo bhi bh0 bh1 =>
      simp only at h1 h2
      subst h1
      subst h2
      rfl

/-- The real delay `t` is allowed by the bound `b`. -/
def Mem (t : ℝ) (b : DelayBound) : Prop := b.lo ≤ t ∧ t ≤ b.hi

/-- `a.Le b`: the interval of `a` is inside the interval of `b`, so `b` is
the more conservative bound. -/
def Le (a b : DelayBound) : Prop := b.lo ≤ a.lo ∧ a.hi ≤ b.hi

/-- The exact zero delay. -/
def zero : DelayBound := ⟨0, 0, le_refl _, le_refl _⟩

/-- An exact delay `d ≥ 0`. -/
def exact (d : ℝ) (h : 0 ≤ d) : DelayBound := ⟨d, d, h, le_refl _⟩

/-- Series composition: interval sum. -/
def series (a b : DelayBound) : DelayBound :=
  ⟨a.lo + b.lo, a.hi + b.hi,
    by linarith [a.lo_nonneg, b.lo_nonneg],
    by linarith [a.lo_le_hi, b.lo_le_hi]⟩

theorem series_lo (a b : DelayBound) : (series a b).lo = a.lo + b.lo := rfl
theorem series_hi (a b : DelayBound) : (series a b).hi = a.hi + b.hi := rfl

theorem series_assoc (a b c : DelayBound) :
    series (series a b) c = series a (series b c) := by
  apply ext'
  · simp only [series_lo, add_assoc]
  · simp only [series_hi, add_assoc]

theorem series_comm (a b : DelayBound) : series a b = series b a := by
  apply ext'
  · simp only [series_lo, add_comm]
  · simp only [series_hi, add_comm]

theorem zero_series (a : DelayBound) : series zero a = a := by
  apply ext'
  · simp only [series_lo, zero, zero_add]
  · simp only [series_hi, zero, zero_add]

theorem series_zero (a : DelayBound) : series a zero = a := by
  rw [series_comm]; exact zero_series a

theorem mem_series {s t : ℝ} {a b : DelayBound} (hs : Mem s a) (ht : Mem t b) :
    Mem (s + t) (series a b) := by
  obtain ⟨hs1, hs2⟩ := hs
  obtain ⟨ht1, ht2⟩ := ht
  exact ⟨by simp only [series_lo]; linarith, by simp only [series_hi]; linarith⟩

theorem Le.refl (a : DelayBound) : Le a a := ⟨le_refl _, le_refl _⟩

theorem Le.trans {a b c : DelayBound} (h1 : Le a b) (h2 : Le b c) : Le a c :=
  ⟨le_trans h2.1 h1.1, le_trans h1.2 h2.2⟩

theorem Mem.of_le {t : ℝ} {a b : DelayBound} (ht : Mem t a) (h : Le a b) : Mem t b :=
  ⟨le_trans h.1 ht.1, le_trans ht.2 h.2⟩

/-- Series composition is monotone for containment in both arguments. -/
theorem series_mono {a a' b b' : DelayBound} (ha : Le a a') (hb : Le b b') :
    Le (series a b) (series a' b') := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  exact ⟨by simp only [series_lo]; linarith, by simp only [series_hi]; linarith⟩

/-! ### Paths: a list of hops in series -/

/-- The bound of a path of hops in series. -/
def path : List DelayBound → DelayBound
  | [] => zero
  | b :: bs => series b (path bs)

/-- Sum of a list of real delays (own definition, to keep imports small). -/
def tsum : List ℝ → ℝ
  | [] => 0
  | t :: ts => t + tsum ts

/-- Pointwise relation between two lists of the same length. -/
def Pw {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | a :: as, b :: bs => R a b ∧ Pw R as bs
  | _, _ => False

/-- **Bridge theorem.** If the real delay of each hop lies in that hop's
bound, the real path delay lies in the path bound. -/
theorem mem_path : ∀ (ts : List ℝ) (bs : List DelayBound),
    Pw Mem ts bs → Mem (tsum ts) (path bs)
  | [], [], _ => ⟨le_refl _, le_refl _⟩
  | t :: ts, b :: bs, h => by
    obtain ⟨h1, h2⟩ := h
    exact mem_series h1 (mem_path ts bs h2)
  | [], _ :: _, h => absurd h (by simp [Pw])
  | _ :: _, [], h => absurd h (by simp [Pw])

theorem path_append : ∀ (l₁ l₂ : List DelayBound),
    path (l₁ ++ l₂) = series (path l₁) (path l₂)
  | [], l₂ => by simp only [List.nil_append, path]; rw [zero_series]
  | b :: l₁, l₂ => by
    simp only [List.cons_append, path]
    rw [path_append l₁ l₂, series_assoc]

theorem path_mono : ∀ (bs bs' : List DelayBound),
    Pw Le bs bs' → Le (path bs) (path bs')
  | [], [], _ => Le.refl _
  | b :: bs, b' :: bs', h => by
    obtain ⟨h1, h2⟩ := h
    exact series_mono h1 (path_mono bs bs' h2)
  | [], _ :: _, h => absurd h (by simp [Pw])
  | _ :: _, [], h => absurd h (by simp [Pw])

/-! ### From prjxray corner data -/

/-- One prjxray delay 4-tuple `[fast_min, fast_max, slow_min, slow_max]`,
with the ordering the database is expected to satisfy taken as hypotheses
(`fmin ≤ fmax`, `smin ≤ smax`, `fmin ≤ smax`). -/
structure Corners where
  fmin : ℝ
  fmax : ℝ
  smin : ℝ
  smax : ℝ
  fmin_nonneg : 0 ≤ fmin
  fmin_le_fmax : fmin ≤ fmax
  smin_le_smax : smin ≤ smax
  fmin_le_smax : fmin ≤ smax

/-- The whole PVT band `[fast_min, slow_max]`: the bound for a die whose
corner is unknown. -/
def ofCorners (c : Corners) : DelayBound :=
  ⟨c.fmin, c.smax, c.fmin_nonneg, c.fmin_le_smax⟩

/-- Only the SLOW corner `[slow_min, slow_max]`, under the extra hypothesis
`0 ≤ slow_min`. -/
def slowOnly (c : Corners) (h : 0 ≤ c.smin) : DelayBound :=
  ⟨c.smin, c.smax, h, c.smin_le_smax⟩

/-- A one-corner bound is inside the full band whenever `fast_min ≤ slow_min`. -/
theorem slowOnly_le_ofCorners (c : Corners) (h : 0 ≤ c.smin) (hfs : c.fmin ≤ c.smin) :
    Le (slowOnly c h) (ofCorners c) :=
  ⟨hfs, le_refl _⟩

/-- Widen a bound by a relative model error `ε ∈ [0,1]` (for example prjxray's
±1.5% against Vivado): `[lo(1-ε), hi(1+ε)]`. -/
def widen (b : DelayBound) (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) : DelayBound :=
  ⟨b.lo * (1 - ε), b.hi * (1 + ε),
    by
      have : 0 ≤ 1 - ε := by linarith
      exact mul_nonneg b.lo_nonneg this,
    by
      have hlo := mul_nonneg b.lo_nonneg h0
      have hhi := mul_nonneg (le_trans b.lo_nonneg b.lo_le_hi) h0
      have := b.lo_le_hi
      nlinarith⟩

theorem le_widen (b : DelayBound) (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    Le b (widen b ε h0 h1) := by
  have hlo := mul_nonneg b.lo_nonneg h0
  have hhi := mul_nonneg (le_trans b.lo_nonneg b.lo_le_hi) h0
  refine ⟨?_, ?_⟩
  · show b.lo * (1 - ε) ≤ b.lo
    nlinarith
  · show b.hi ≤ b.hi * (1 + ε)
    nlinarith

end DelayBound

/-! ## Elmore delay of an RC ladder -/

/-- One ladder section: a series resistance `r`, then a capacitance `c` to
ground at its downstream node. A prjxray `Outpin` or `Buffer` driver is
`⟨R_drive, 0⟩`, a wire is `⟨R_wire, C_wire⟩`, and an `Inpin` (or an
enabled buffer's `in_cap`) is `⟨0, C_in⟩`. -/
structure RC where
  r : ℝ
  c : ℝ

/-- Total capacitance of a ladder. -/
def totalC : List RC → ℝ
  | [] => 0
  | s :: l => s.c + totalC l

/-- Elmore delay from the ladder's input to its far end:
`Σ_i r_i · (Σ_{j ≥ i} c_j)`. -/
def elmore : List RC → ℝ
  | [] => 0
  | s :: l => s.r * (s.c + totalC l) + elmore l

/-- prjxray's pi-model (`timing.py`, `Wire.propigate_downstream_capacitance`):
a wire's own `r` sees only half of its own `c`. Upstream elements still see
all of it. -/
def elmorePi : List RC → ℝ
  | [] => 0
  | s :: l => s.r * (s.c / 2 + totalC l) + elmorePi l

/-- Every `r` and `c` is nonnegative. -/
def Nonneg : List RC → Prop
  | [] => True
  | s :: l => 0 ≤ s.r ∧ 0 ≤ s.c ∧ Nonneg l

/-- Pointwise `≤` on two ladders of the same shape. -/
def LeRC : List RC → List RC → Prop
  | [], [] => True
  | s :: l, t :: m => s.r ≤ t.r ∧ s.c ≤ t.c ∧ LeRC l m
  | _, _ => False

theorem totalC_nonneg : ∀ l : List RC, Nonneg l → 0 ≤ totalC l
  | [], _ => le_refl _
  | s :: l, h => by
    obtain ⟨_, hc, hl⟩ := h
    have := totalC_nonneg l hl
    simp only [totalC]; linarith

theorem totalC_mono : ∀ l m : List RC, LeRC l m → totalC l ≤ totalC m
  | [], [], _ => le_refl _
  | s :: l, t :: m, h => by
    obtain ⟨_, hc, hl⟩ := h
    have := totalC_mono l m hl
    simp only [totalC]; linarith
  | [], _ :: _, h => absurd h (by simp [LeRC])
  | _ :: _, [], h => absurd h (by simp [LeRC])

theorem elmore_nonneg : ∀ l : List RC, Nonneg l → 0 ≤ elmore l
  | [], _ => le_refl _
  | s :: l, h => by
    obtain ⟨hr, hc, hl⟩ := h
    have h1 := totalC_nonneg l hl
    have h2 := elmore_nonneg l hl
    have h3 : 0 ≤ s.r * (s.c + totalC l) := mul_nonneg hr (by linarith)
    simp only [elmore]; linarith

theorem Nonneg.of_le : ∀ l m : List RC, Nonneg l → LeRC l m → Nonneg m
  | [], [], _, _ => trivial
  | s :: l, t :: m, h, hle => by
    obtain ⟨hr, hc, hl⟩ := h
    obtain ⟨hr', hc', hlm⟩ := hle
    exact ⟨le_trans hr hr', le_trans hc hc', Nonneg.of_le l m hl hlm⟩
  | [], _ :: _, _, h => absurd h (by simp [LeRC])
  | _ :: _, [], _, h => absurd h (by simp [LeRC])

/-- **Elmore delay is monotone in every R and every C at once**: raising any
resistances and capacitances (from a nonnegative start) never lowers it. -/
theorem elmore_mono : ∀ l m : List RC, Nonneg l → LeRC l m → elmore l ≤ elmore m
  | [], [], _, _ => le_refl _
  | s :: l, t :: m, h, hle => by
    obtain ⟨hr, hc, hl⟩ := h
    obtain ⟨hr', hc', hlm⟩ := hle
    have hT := totalC_mono l m hlm
    have hT0 := totalC_nonneg l hl
    have hE := elmore_mono l m hl hlm
    have hmul : s.r * (s.c + totalC l) ≤ t.r * (t.c + totalC m) :=
      mul_le_mul hr' (by linarith) (by linarith) (le_trans hr hr')
    simp only [elmore]; linarith
  | [], _ :: _, _, h => absurd h (by simp [LeRC])
  | _ :: _, [], _, h => absurd h (by simp [LeRC])

theorem elmorePi_mono : ∀ l m : List RC, Nonneg l → LeRC l m → elmorePi l ≤ elmorePi m
  | [], [], _, _ => le_refl _
  | s :: l, t :: m, h, hle => by
    obtain ⟨hr, hc, hl⟩ := h
    obtain ⟨hr', hc', hlm⟩ := hle
    have hT := totalC_mono l m hlm
    have hT0 := totalC_nonneg l hl
    have hE := elmorePi_mono l m hl hlm
    have hmul : s.r * (s.c / 2 + totalC l) ≤ t.r * (t.c / 2 + totalC m) :=
      mul_le_mul hr' (by linarith) (by linarith) (le_trans hr hr')
    simp only [elmorePi]; linarith
  | [], _ :: _, _, h => absurd h (by simp [LeRC])
  | _ :: _, [], _, h => absurd h (by simp [LeRC])

/-- The pi-model never exceeds the lumped (L-section) model. -/
theorem elmorePi_le_elmore : ∀ l : List RC, Nonneg l → elmorePi l ≤ elmore l
  | [], _ => le_refl _
  | s :: l, h => by
    obtain ⟨hr, hc, hl⟩ := h
    have hE := elmorePi_le_elmore l hl
    have : s.r * (s.c / 2 + totalC l) ≤ s.r * (s.c + totalC l) :=
      mul_le_mul_of_nonneg_left (by linarith) hr
    simp only [elmorePi, elmore]; linarith

theorem LeRC.refl : ∀ l : List RC, LeRC l l
  | [] => trivial
  | _ :: l => ⟨le_refl _, le_refl _, LeRC.refl l⟩

theorem LeRC.append : ∀ (a b c d : List RC), LeRC a b → LeRC c d → LeRC (a ++ c) (b ++ d)
  | [], [], _, _, _, h => by simpa using h
  | _ :: a, _ :: b, c, d, hab, hcd => by
    obtain ⟨h1, h2, h3⟩ := hab
    exact ⟨h1, h2, LeRC.append a b c d h3 hcd⟩
  | [], _ :: _, _, _, h, _ => absurd h (by simp [LeRC])
  | _ :: _, [], _, _, h, _ => absurd h (by simp [LeRC])

/-- Monotone in one resistance: raising the `r` of one section (everything
else fixed) never lowers the Elmore delay. -/
theorem elmore_mono_R (pre post : List RC) (r r' c : ℝ)
    (hn : Nonneg (pre ++ ⟨r, c⟩ :: post)) (hrr : r ≤ r') :
    elmore (pre ++ ⟨r, c⟩ :: post) ≤ elmore (pre ++ ⟨r', c⟩ :: post) :=
  elmore_mono _ _ hn
    (LeRC.append _ _ _ _ (LeRC.refl pre) ⟨hrr, le_refl _, LeRC.refl post⟩)

/-- Monotone in one capacitance. -/
theorem elmore_mono_C (pre post : List RC) (r c c' : ℝ)
    (hn : Nonneg (pre ++ ⟨r, c⟩ :: post)) (hcc : c ≤ c') :
    elmore (pre ++ ⟨r, c⟩ :: post) ≤ elmore (pre ++ ⟨r, c'⟩ :: post) :=
  elmore_mono _ _ hn
    (LeRC.append _ _ _ _ (LeRC.refl pre) ⟨le_refl _, hcc, LeRC.refl post⟩)

/-! ## From R/C ranges to a delay bound -/

/-- The RC part of one buffered hop as a `DelayBound`. `lo` and `hi` are
the per-element lower and upper R/C ladders. `κ ∈ [0,1]` is the lower
model factor: the 50% delay of an RC tree is at most its Elmore delay
(Gupta–Tutuianu–Pileggi 1997), but only `κ·Elmore` is claimed as a lower
bound. `κ = 0` is always sound, and `κ = 1` is Vivado/prjxray's own
convention. -/
def rcBound (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (lo hi : List RC)
    (hn : Nonneg lo) (hle : LeRC lo hi) : DelayBound :=
  ⟨κ * elmore lo, elmore hi,
    mul_nonneg hκ0 (elmore_nonneg lo hn),
    by
      have h1 := elmore_mono lo hi hn hle
      have h0 := elmore_nonneg lo hn
      have : κ * elmore lo ≤ 1 * elmore lo := mul_le_mul_of_nonneg_right hκ1 h0
      linarith⟩

/-- **Soundness of `rcBound`.** Explicit hypotheses: the real ladder `x`
lies between `lo` and `hi` element by element (`hlo`, `hhi`), and the real
RC delay `t` lies in `[κ·elmore x, elmore x]` (`hmodel`, the RC-model
hypothesis). Then `t` is in the bound. -/
theorem mem_rcBound (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (lo hi x : List RC)
    (hn : Nonneg lo) (hle : LeRC lo hi) (hlo : LeRC lo x) (hhi : LeRC x hi)
    (t : ℝ) (hmodel : κ * elmore x ≤ t ∧ t ≤ elmore x) :
    DelayBound.Mem t (rcBound κ hκ0 hκ1 lo hi hn hle) := by
  have hnx := Nonneg.of_le lo x hn hlo
  have h1 := elmore_mono lo x hn hlo
  have h2 := elmore_mono x hi hnx hhi
  have h3 : κ * elmore lo ≤ κ * elmore x := mul_le_mul_of_nonneg_left h1 hκ0
  exact ⟨by show κ * elmore lo ≤ t; linarith, by show t ≤ elmore hi; linarith⟩

/-- One buffered hop as prjxray models it: the intrinsic band of the pip
(or site pin) in series with the RC band of the ladder it drives. -/
def hop (intr : DelayBound) (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (lo hi : List RC)
    (hn : Nonneg lo) (hle : LeRC lo hi) : DelayBound :=
  DelayBound.series intr (rcBound κ hκ0 hκ1 lo hi hn hle)

theorem mem_hop (intr : DelayBound) (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (lo hi x : List RC) (hn : Nonneg lo) (hle : LeRC lo hi)
    (hlo : LeRC lo x) (hhi : LeRC x hi)
    (d t : ℝ) (hd : DelayBound.Mem d intr) (hmodel : κ * elmore x ≤ t ∧ t ≤ elmore x) :
    DelayBound.Mem (d + t) (hop intr κ hκ0 hκ1 lo hi hn hle) :=
  DelayBound.mem_series hd (mem_rcBound κ hκ0 hκ1 lo hi x hn hle hlo hhi t hmodel)

/-! ## Trace level: bounded transport channels compose in series -/

/-- A binary signal: a trace over real time. -/
abbrev Sig := ℝ → Bool

/-- **Bounded transport with order-preserving warp** (the hypothesis shape
for a buffered routing hop, see the notes). `y` is `x` delayed by a
per-instant delay `δ t` in the bound `b`. The warp `t ↦ t + δ t` is
strictly increasing and onto, so every input edge reaches the output, in
order, and the output has no edges of its own. -/
def BoundedTransport (b : DelayBound) (x y : Sig) : Prop :=
  ∃ δ : ℝ → ℝ, (∀ t, DelayBound.Mem (δ t) b) ∧
    (∀ t, y (t + δ t) = x t) ∧
    (∀ s t, s < t → s + δ s < t + δ t) ∧
    (∀ u, ∃ t, u = t + δ t)

/-- Two bounded-transport channels in series form a bounded-transport
channel with the series bound. This is the trace-level counterpart of
`DelayBound.series`. -/
theorem boundedTransport_series (a b : DelayBound) (x y z : Sig)
    (h₁ : BoundedTransport a x y) (h₂ : BoundedTransport b y z) :
    BoundedTransport (DelayBound.series a b) x z := by
  obtain ⟨δ₁, hb₁, hy₁, hm₁, ho₁⟩ := h₁
  obtain ⟨δ₂, hb₂, hy₂, hm₂, ho₂⟩ := h₂
  refine ⟨fun t => δ₁ t + δ₂ (t + δ₁ t), ?_, ?_, ?_, ?_⟩
  · intro t
    exact DelayBound.mem_series (hb₁ t) (hb₂ (t + δ₁ t))
  · intro t
    have e := hy₂ (t + δ₁ t)
    rw [hy₁ t] at e
    show z (t + (δ₁ t + δ₂ (t + δ₁ t))) = x t
    rw [← add_assoc]; exact e
  · intro s t hst
    have h1 := hm₁ s t hst
    have h2 := hm₂ _ _ h1
    show s + (δ₁ s + δ₂ (s + δ₁ s)) < t + (δ₁ t + δ₂ (t + δ₁ t))
    linarith
  · intro u
    obtain ⟨s, hs⟩ := ho₂ u
    obtain ⟨t, ht⟩ := ho₁ s
    refine ⟨t, ?_⟩
    show u = t + (δ₁ t + δ₂ (t + δ₁ t))
    rw [hs, ht, add_assoc]

/-- A bounded-transport channel also satisfies any wider bound. -/
theorem boundedTransport_widen (a b : DelayBound) (x y : Sig)
    (h : BoundedTransport a x y) (hab : DelayBound.Le a b) : BoundedTransport b x y := by
  obtain ⟨δ, hb, hy, hm, ho⟩ := h
  exact ⟨δ, fun t => (hb t).of_le hab, hy, hm, ho⟩

/-! ## Sanity examples (prjxray-db zynq7 numbers, ns) -/

/-- An INT_L `IMUX_L` pip: `[0.038, 0.047, 0.114, 0.138]` ns. -/
def imuxPip : DelayBound.Corners :=
  ⟨0.038, 0.047, 0.114, 0.138, by norm_num, by norm_num, by norm_num, by norm_num⟩

example : (DelayBound.ofCorners imuxPip).lo = 0.038 := rfl
example : (DelayBound.ofCorners imuxPip).hi = 0.138 := rfl

/-- One 1.48 kΩ driver into a 13 fF wire and two 7.57 fF enabled-pip loads.
With R in kΩ and C in pF, R·C is in ns. -/
example : elmore [⟨1.4765, 0⟩, ⟨0, 0.013 + 0.00757 + 0.00757⟩] = 1.4765 * 0.02814 := by
  simp only [elmore, totalC]; norm_num

end Formal.Core.Fidelity

end
