/-!
# Corner cells over ℚ, Mathlib-free (KapRes2)

Mathlib-free companion of `Formal/Core/Delay/CornerCell.lean` (which states the same facts over
ℝ for `Formal.Core.Corner.lerp` and the ℕ model, and needs Mathlib). Everything here uses only
core Lean's `Rat` (with `Rat.floor` / `Rat.ceil`) and `grind`'s linear arithmetic.

The sweep (`formal/tools-A/kappa/kapres2/cornerband2.py`) gives arc `e` on the corner cell
`[ca, cb]` the band

    [ ⌊(1-κ)·min(lerp(f0,s0,ca), lerp(f0,s0,cb))⌋ , ⌈(1+κ)·max(lerp(f1,s1,ca), lerp(f1,s1,cb))⌉ ]

(`cellLo`, `cellHi`), `[f0,f1]` its FAST band, `[s0,s1]` its SLOW band, `lerp f s c = (1-c)f + cs`.

Proved (all rationals):
* `lerp_min_le`, `lerp_le_max`: for `ca ≤ c ≤ cb`, `lerp F S c` lies between its values at the
  two ends (no sign condition on `S - F`);
* `cell_band`: A-kapres §2's statement (its `0 ≤ ca`, `cb ≤ 1` are not needed);
* `cell_band_mem`: endpoints `F ∈ [Fl,Fh]`, `S ∈ [Sl,Sh]`, corner `c ∈ [ca,cb] ⊆ [0,1]`,
  `0 ≤ κ ≤ 1`, a delay `d` with `(1-κ)·lerp F S c ≤ d ≤ (1+κ)·lerp F S c`: `d` is in the cell band;
* `cell_band_int`: the same with the integer band `cellLo ≤ d ≤ cellHi`;
* `cellLo_anti`, `cellHi_mono`: widening κ or the cell widens the band (the sweep's
  `implied_clean`), for nonnegative band-file numbers;
* `cover_mem`: a chain of cells from 0 to 1 contains every `c ∈ [0,1]`.

NOT covered: the real-valued model (that is `CornerCell.lean`), whether the model holds of
silicon, the band files' numbers, the timing checker.
-/

namespace KapRes2.CornerCellQ

/-- `lerp` over ℚ. -/
def lerp (F S c : Rat) : Rat := (1 - c) * F + c * S

theorem lerp_sub (F S c c' : Rat) : lerp F S c - lerp F S c' = (c - c') * (S - F) := by
  unfold lerp; grind

theorem mul_nn {a b : Rat} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := Rat.mul_nonneg ha hb

theorem lerp_min_le {F S ca cb c : Rat} (h1 : ca ≤ c) (h2 : c ≤ cb) :
    min (lerp F S ca) (lerp F S cb) ≤ lerp F S c := by
  rcases (Rat.le_total : F ≤ S ∨ S ≤ F) with h | h
  · have e := lerp_sub F S c ca
    have : 0 ≤ (c - ca) * (S - F) := mul_nn (by grind) (by grind)
    have : min (lerp F S ca) (lerp F S cb) ≤ lerp F S ca := by grind
    grind
  · have e := lerp_sub F S c cb
    have : 0 ≤ (cb - c) * (F - S) := mul_nn (by grind) (by grind)
    have e2 : (c - cb) * (S - F) = (cb - c) * (F - S) := by grind
    have : min (lerp F S ca) (lerp F S cb) ≤ lerp F S cb := by grind
    grind

theorem lerp_le_max {F S ca cb c : Rat} (h1 : ca ≤ c) (h2 : c ≤ cb) :
    lerp F S c ≤ max (lerp F S ca) (lerp F S cb) := by
  rcases (Rat.le_total : F ≤ S ∨ S ≤ F) with h | h
  · have e := lerp_sub F S cb c
    have : 0 ≤ (cb - c) * (S - F) := mul_nn (by grind) (by grind)
    have : lerp F S cb ≤ max (lerp F S ca) (lerp F S cb) := by grind
    grind
  · have e := lerp_sub F S ca c
    have : 0 ≤ (c - ca) * (F - S) := mul_nn (by grind) (by grind)
    have e2 : (ca - c) * (S - F) = (c - ca) * (F - S) := by grind
    have : lerp F S ca ≤ max (lerp F S ca) (lerp F S cb) := by grind
    grind

/-- `lerp` is monotone in both endpoints on `[0,1]`. -/
theorem lerp_mono {F S F' S' c : Rat} (hF : F ≤ F') (hS : S ≤ S') (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    lerp F S c ≤ lerp F' S' c := by
  unfold lerp
  have h1 : 0 ≤ (1 - c) * (F' - F) := mul_nn (by grind) (by grind)
  have h2 : 0 ≤ c * (S' - S) := mul_nn hc0 (by grind)
  grind

theorem lerp_nonneg {F S c : Rat} (hF : 0 ≤ F) (hS : 0 ≤ S) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    0 ≤ lerp F S c := by
  unfold lerp
  have := mul_nn (by grind : (0 : Rat) ≤ 1 - c) hF
  have := mul_nn hc0 hS
  grind

/-- **The cell lemma** (A-kapres §2's statement, over ℚ). -/
theorem cell_band {F S ca cb c κ : Rat} (hcab : ca ≤ c) (hcb : c ≤ cb)
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) :
    (1 - κ) * min (lerp F S ca) (lerp F S cb) ≤ (1 - κ) * lerp F S c ∧
    (1 + κ) * lerp F S c ≤ (1 + κ) * max (lerp F S ca) (lerp F S cb) :=
  ⟨Rat.mul_le_mul_of_nonneg_left (lerp_min_le hcab hcb) (by grind),
   Rat.mul_le_mul_of_nonneg_left (lerp_le_max hcab hcb) (by grind)⟩

/-- The corner model's local scatter for one delay (as `Corner.Scat`, over ℚ). -/
def Scat (κ D d : Rat) : Prop := (1 - κ) * D ≤ d ∧ d ≤ (1 + κ) * D

/-- **Cell cover.** Any endpoints in the band-file intervals, any corner in the cell
`[ca,cb] ⊆ [0,1]`, any delay within scatter κ of the nominal delay at that corner, lies in the
cell band. -/
theorem cell_band_mem {Fl Fh Sl Sh F S ca cb c κ d : Rat}
    (hFl : Fl ≤ F) (hFh : F ≤ Fh) (hSl : Sl ≤ S) (hSh : S ≤ Sh)
    (hca : 0 ≤ ca) (hcab : ca ≤ c) (hcb : c ≤ cb) (hcb1 : cb ≤ 1)
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hd : Scat κ (lerp F S c) d) :
    (1 - κ) * min (lerp Fl Sl ca) (lerp Fl Sl cb) ≤ d ∧
    d ≤ (1 + κ) * max (lerp Fh Sh ca) (lerp Fh Sh cb) := by
  have hc0 : 0 ≤ c := Rat.le_trans hca hcab
  have hc1 : c ≤ 1 := Rat.le_trans hcb hcb1
  obtain ⟨h1, h2⟩ := hd
  constructor
  · have a := lerp_min_le (F := Fl) (S := Sl) hcab hcb
    have b := lerp_mono hFl hSl hc0 hc1
    have := Rat.mul_le_mul_of_nonneg_left (Rat.le_trans a b) (by grind : (0 : Rat) ≤ 1 - κ)
    grind
  · have a := lerp_le_max (F := Fh) (S := Sh) hcab hcb
    have b := lerp_mono hFh hSh hc0 hc1
    have := Rat.mul_le_mul_of_nonneg_left (Rat.le_trans b a) (by grind : (0 : Rat) ≤ 1 + κ)
    grind

/-! ## The integer band (transcription of `cornerband2.py`) -/

def cellLo (f0 _f1 s0 _s1 : Nat) (ca cb κ : Rat) : Int :=
  ((1 - κ) * min (lerp f0 s0 ca) (lerp f0 s0 cb)).floor

def cellHi (_f0 f1 _s0 s1 : Nat) (ca cb κ : Rat) : Int :=
  ((1 + κ) * max (lerp f1 s1 ca) (lerp f1 s1 cb)).ceil

/-- **Cell cover, integer band.** -/
theorem cell_band_int {f0 f1 s0 s1 : Nat} {ca cb κ F S c d : Rat}
    (hFl : (f0 : Rat) ≤ F) (hFh : F ≤ f1) (hSl : (s0 : Rat) ≤ S) (hSh : S ≤ s1)
    (hca : 0 ≤ ca) (hcab : ca ≤ c) (hcb : c ≤ cb) (hcb1 : cb ≤ 1)
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hd : Scat κ (lerp F S c) d) :
    ((cellLo f0 f1 s0 s1 ca cb κ : Int) : Rat) ≤ d ∧ d ≤ ((cellHi f0 f1 s0 s1 ca cb κ : Int) : Rat) := by
  obtain ⟨h1, h2⟩ := cell_band_mem hFl hFh hSl hSh hca hcab hcb hcb1 hκ0 hκ1 hd
  exact ⟨Rat.le_trans (Rat.floor_le _) h1, Rat.le_trans h2 Rat.le_ceil⟩

theorem natCast_nonneg (n : Nat) : (0 : Rat) ≤ (n : Rat) := by
  have := Rat.natCast_nonneg (a := n); exact this

/-- Widening κ or the cell can only lower the lower end. -/
theorem cellLo_anti {f0 f1 s0 s1 : Nat} {ca cb ca' cb' κ κ' : Rat}
    (h0 : 0 ≤ ca') (h1 : ca' ≤ ca) (h2 : ca ≤ cb) (h3 : cb ≤ cb') (h4 : cb' ≤ 1)
    (hk : κ ≤ κ') (hk1 : κ' ≤ 1) :
    cellLo f0 f1 s0 s1 ca' cb' κ' ≤ cellLo f0 f1 s0 s1 ca cb κ := by
  unfold cellLo
  apply Rat.floor_monotone
  have hF := natCast_nonneg f0
  have hS := natCast_nonneg s0
  have ma := lerp_min_le (F := f0) (S := s0) h1 (Rat.le_trans h2 h3)
  have mb := lerp_min_le (F := f0) (S := s0) (Rat.le_trans h1 h2) h3
  have hm : min (lerp f0 s0 ca') (lerp f0 s0 cb') ≤ min (lerp f0 s0 ca) (lerp f0 s0 cb) :=
    by grind
  have hnn : 0 ≤ min (lerp f0 s0 ca') (lerp f0 s0 cb') :=
    have := lerp_nonneg (c := ca') hF hS h0 (by grind)
    have := lerp_nonneg (c := cb') hF hS (by grind) h4
    by grind
  have a := Rat.mul_le_mul_of_nonneg_right (by grind : 1 - κ' ≤ 1 - κ) hnn
  have c := Rat.mul_le_mul_of_nonneg_left hm (by grind : (0 : Rat) ≤ 1 - κ)
  exact Rat.le_trans a c

/-- Widening κ or the cell can only raise the upper end. -/
theorem cellHi_mono {f0 f1 s0 s1 : Nat} {ca cb ca' cb' κ κ' : Rat}
    (h0 : 0 ≤ ca') (h1 : ca' ≤ ca) (h2 : ca ≤ cb) (h3 : cb ≤ cb') (h4 : cb' ≤ 1)
    (hk0 : 0 ≤ κ) (hk : κ ≤ κ') :
    cellHi f0 f1 s0 s1 ca cb κ ≤ cellHi f0 f1 s0 s1 ca' cb' κ' := by
  unfold cellHi
  apply Rat.ceil_le_iff.mpr
  refine Rat.le_trans ?_ Rat.le_ceil
  have hF := natCast_nonneg f1
  have hS := natCast_nonneg s1
  have ma := lerp_le_max (F := f1) (S := s1) h1 (Rat.le_trans h2 h3)
  have mb := lerp_le_max (F := f1) (S := s1) (Rat.le_trans h1 h2) h3
  have hm : max (lerp f1 s1 ca) (lerp f1 s1 cb) ≤ max (lerp f1 s1 ca') (lerp f1 s1 cb') :=
    by grind
  have hnn : 0 ≤ max (lerp f1 s1 ca) (lerp f1 s1 cb) :=
    have := lerp_nonneg (c := ca) hF hS (by grind) (by grind)
    by grind
  have a := Rat.mul_le_mul_of_nonneg_right (by grind : 1 + κ ≤ 1 + κ') hnn
  have b := Rat.mul_le_mul_of_nonneg_left hm (by grind : (0 : Rat) ≤ 1 + κ')
  exact Rat.le_trans a b

/-! ## Covers -/

/-- A list of cells is a chain from `x` to 1 (`kapres2/table2.py` checks exactly this). -/
def Chain : Rat → List (Rat × Rat) → Prop
  | x, [] => x = 1
  | x, p :: l => p.1 = x ∧ p.1 ≤ p.2 ∧ Chain p.2 l

theorem chain_mem : ∀ (x : Rat) (l : List (Rat × Rat)), Chain x l → ∀ c : Rat, x < c → c ≤ 1 →
    ∃ p ∈ l, p.1 ≤ c ∧ c ≤ p.2
  | x, [], h, c, h1, h2 => by
      simp only [Chain] at h; subst h; exact absurd h2 (Rat.not_le.mpr h1)
  | x, p :: l, ⟨hx, _, hl⟩, c, h1, h2 => by
      by_cases hc : c ≤ p.2
      · exact ⟨p, List.mem_cons_self, by rw [hx]; exact Rat.le_of_lt h1, hc⟩
      · obtain ⟨q, hq, hq1, hq2⟩ := chain_mem p.2 l hl c (Rat.not_le.mp hc) h2
        exact ⟨q, List.mem_cons_of_mem _ hq, hq1, hq2⟩

/-- **Cover.** Every corner `c ∈ [0,1]` lies in some cell of a chain from 0 to 1. -/
theorem cover_mem {l : List (Rat × Rat)} (h : Chain 0 l) {c : Rat} (h0 : 0 ≤ c) (h1 : c ≤ 1) :
    ∃ p ∈ l, p.1 ≤ c ∧ c ≤ p.2 := by
  by_cases hc : 0 < c
  · exact chain_mem 0 l h c hc h1
  · have hc0 : c = 0 := by grind
    subst hc0
    match l, h with
    | [], h => simp only [Chain] at h; exact absurd h (by decide)
    | p :: _, ⟨hp, hle, _⟩ =>
      exact ⟨p, List.mem_cons_self, by rw [hp]; exact Rat.le_refl, by rw [← hp]; exact hle⟩

end KapRes2.CornerCellQ
