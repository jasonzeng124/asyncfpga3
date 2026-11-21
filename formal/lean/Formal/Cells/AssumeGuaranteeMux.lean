import Formal.Cells.AssumeGuaranteeEnds

/-!
# Probe Bmux2 (shard B): segment lemmas for `bd_mux`'s joins and acknowledges, and `bd_src`

Bseg (`AssumeGuaranteeEnds*`) gave segment lemmas for links, `n`-pin C-elements and steer
branches, and left every cell of the 21 muxes, the 3 sources and the 18 sinks of gcd_hw as
assumed segment contracts. This file gives the segment lemmas of those cells (the ORs are
in `AssumeGuaranteeMuxOr`), in the per-segment form `net_closed_gen` consumes. Every
hypothesis is about the segment's own phase, except the departure bounds, which are
edge-time inequalities quantified over phases as in Bseg (no infinite alternation is
assumed beyond a total token enumeration `κ`, as in Bseg's steer).

## Assumed / proved / NOT covered

**Proved:**
* `celX_segK`: a C-element LUT (any pins, `CelLaw`, B's `CelG`), one segment, from the
  EXCITATION CONDITION of that phase only: at every instant of phase `j` either all pins
  show `Vph j`, or some pin does and the node edge plus `E` has passed (feedback settled).
  Bseg's `celG_segK` is the case where the pins are four-phase in the cell's numbering.
* `muxj_segK` (`uj0`/`uj1` = `C(x_req, ctl_req ∧ (s == b))`): segment `k` from the input
  request's segment `k`, the control request's segments `≤ sN κ k`, H_SEL_STABLE and the
  control token enumeration `κ`. `uj0_cel`/`uj1_cel`: the REAL LUTs (INIT `0xAE08`,
  `0xEA80`) are the `G2` model.
* `muxa_segK` (`uxa`/`uya` = `C(j, z_ack)`): `z_ack` carries EVERY output token; the cell
  holds low through the other input's tokens under exactly two edge-time conditions:
  `H_SNDZ` (the next `z_ack` edge of any token comes `E` after the cell's edge) and
  `H_ZFALL` (`z_ack` has fallen for every earlier token before the join rises:
  `ζ (2 κ m - 1) ≤ ρ (2m)`). `muxa_conds_tight`: violating either puts a `1` on the
  excitation inside the low phase. `uxa_cel`/`uya_cel`: the REAL LUTs.
* `src_segK` (the REAL `bd_src` LUT1 `¬ack`, no reset, H_PWR_SRC): node segment `k` from
  the acknowledge's segments `< k`; `src_wait` its H_WAIT. `snk_wire`: `bd_snk` has no
  cell (its acknowledge is its request net).
* Witnesses (nonzero delays, the REAL LUTs): `Wit.muxj_witness` (the control carries both
  inputs' tokens, `uj0` gets the even ones), `Wit.muxa_witness` (a foreign `z_ack` pulse
  while `j0` is low, `uxa` holds low), `Wit.src_witness` (power-up rise before any ack).

**Assumed (named):** B's gate models (`CelG`; `Win` + H_NO_REVERT), H_PWR (H_PWR_SRC for
the source), H_RST_LONG, H_LAT, H_LUT_POS; per cell the departure bounds (`H_SND`,
`H_SNDJ`, `H_SNDZ`, `H_ZFALL`, `H_SPACE`) as edge-time inequalities; H_SEL_STABLE and `κ`.

**NOT covered:** the mux request OR `uor` and the steer acknowledge OR `uack` (see
`AssumeGuaranteeMuxOr`: their low segments are not strictly causal); the departure bounds
are not derived from delay constants; runs are infinite (edges are total functions). Core
Lean only.
-/

namespace Formal.Cells.AssumeGuaranteeMux
open Formal.Cells
open Formal.Cells.AssumeGuaranteeLinks (SegK phases_of_segK segK_of_phases)
open Formal.Cells.AssumeGuaranteeEnds (sN sN_even sN_odd gc_sN gated_segK lutnf_segK GC2 lawC2
  c2_gen)
open Formal.Cells.WinFifo (Win win_le)
open Formal.Cells.WinFifoCausal (NoRevertI nt nt_lo nt_before node_win)
open Formal.Cells.PipeTimed (Vph)
open Formal.Cells.LutFbBridge (Phases)
open Formal.Cells.LutFbBridge2 (CelLaw CelG gc)
open Formal.Net.Ops.Gen (genF cel2)
open Formal.Gen Formal.Gen.Cells

/-! ## 1. A C-element, one segment, from a per-phase excitation condition -/

section celx
variable {ι : Type} {G : (ι → Bool) → Bool → Bool → Bool} {p : Nat → ι → Bool}
  {rst O qp : Nat → Bool} {lo hi wl wh R E : Nat} {c : Nat → Nat}

/-- **C-element, one segment, from the excitation condition of that phase only.** -/
theorem celX_segK (L : CelLaw G) (C : CelG G p rst O qp lo hi wl wh)
    (H_RST : ∀ t, rst t = decide (t < R)) (H_RST_LONG : hi + wh ≤ R)
    (H_LAT : hi + wh ≤ lo + E) (H_PWR : ∀ t, t < hi → O t = false) (k : Nat)
    (H_EX0 : k = 0 → ∀ s, R ≤ s → s < c 0 → ∃ i, p s i = false)
    (H_EXJ : ∀ j, k = j + 1 → R ≤ c j ∧ nt O lo hi (c j) (Vph j) + E ≤ c (j + 1) ∧
      ∀ s, c j ≤ s → s < c (j + 1) →
        (∀ i, p s i = Vph j) ∨ ((∃ i, p s i = Vph j) ∧ nt O lo hi (c j) (Vph j) + E ≤ s)) :
    SegK O (fun j => nt O lo hi (c j) (Vph j)) k := by
  have hlh := win_le C.H_LUT_WIN
  have hlo := C.H_LUT_POS
  have hwl : wl ≤ wh := by obtain ⟨s, h1, h2, _⟩ := C.H_FB wh (Nat.le_refl _); omega
  have ntl : ∀ j, c j + lo ≤ nt O lo hi (c j) (Vph j) := fun j => nt_lo O _ _ hlh
  match k with
  | 0 =>
    have pre : ∀ s, s < c 0 → G (p s) (qp s) (rst s) = false := by
      intro s
      induction s using Nat.strongRecOn with
      | _ s ih =>
        intro h
        by_cases hs : s < R
        · rw [H_RST s]; simp only [hs, decide_true]; exact L.rst _ _
        · have hr : rst s = false := by rw [H_RST]; simp; omega
          obtain ⟨u, hu1, hu2, e⟩ := C.H_FB s (by omega)
          obtain ⟨s', q1, q2, q3⟩ := C.H_LUT_WIN u (by omega)
          have hq : qp s = false := by rw [e, q3]; exact ih s' (by omega) (by omega)
          rw [hr, hq]
          exact L.hold _ _ (H_EX0 rfl s (by omega) h)
    intro t _ ht
    show O t = false
    by_cases hh : t < hi
    · exact H_PWR t hh
    · by_cases h1 : t < c 0 + lo
      · obtain ⟨s, s1, s2, s3⟩ := C.H_LUT_WIN t (by omega)
        rw [s3]; exact pre s (by omega)
      · have := nt_before O lo hi (c 0) (Vph 0) t (by omega) ht
        rw [this, PipeTimed.Vph_even 0]; rfl
  | j + 1 =>
    obtain ⟨hR, hgap, hX⟩ := H_EXJ j rfl
    have hl := ntl j
    have exj : ∀ s, c j ≤ s → s < c (j + 1) → G (p s) (qp s) (rst s) = Vph j := by
      intro s
      induction s using Nat.strongRecOn with
      | _ s ih =>
        intro h1 h2
        have hr : rst s = false := by rw [H_RST]; simp; omega
        rw [hr]
        rcases hX s h1 h2 with hall | ⟨⟨i2, hi2⟩, hlate⟩
        · exact L.all _ _ _ hall
        · obtain ⟨u, hu1, hu2, e⟩ := C.H_FB s (by omega)
          obtain ⟨s', q1, q2, q3⟩ := C.H_LUT_WIN u (by omega)
          have hq : qp s = Vph j := by
            rw [e, q3]; exact ih s' (by omega) (by omega) (by omega)
          rw [hq]
          exact L.hold _ _ ⟨i2, hi2⟩
    have hsp : c j + hi < c (j + 1) + lo := by omega
    have nw := node_win (v := Vph j) C.H_LUT_WIN C.H_NO_REVERT (fun s a b => exj s a b)
      (by omega) hsp
    intro t h1 h2
    show O t = Vph j
    by_cases ht : t < c (j + 1) + lo
    · exact nw.2.2.1 t h1 ht
    · have := nt_before O lo hi (c (j + 1)) (Vph (j + 1)) t (by omega) h2
      rw [this, PipeTimed.Vph_succ, Bool.not_not]

end celx

/-! ## 2. `bd_mux` joins `uj0`/`uj1`: a C-element of the input request and the gated control -/

open Formal.Cells.LutFbBridge2 (G2 law2 pv2 gate uj0_exc uj1_exc)

theorem max_last {a b s : Nat} (h : s < max a b) : ∃ i : Fin 2, s < (if i.val = 0 then a else b) := by
  by_cases h1 : s < a
  · exact ⟨0, by simpa using h1⟩
  · exact ⟨1, by simp; omega⟩

/-- **A mux join, one segment** (`uj0` for `b = false`, `uj1` for `b = true`, as `G2` of the
input request `x` and the gated control `cr ∧ (s == b)`). The control token enumeration `κ`
(the control tokens selecting this input) and H_SEL_STABLE turn the control's segments
`≤ sN κ k` into the gated pin's segment `k` (`gated_segK`); the input request is read at its
own segment `k` (each input token is consumed by exactly one control token). The departure
bounds `H_SND` are per phase-pin edge-time inequalities, as in `CelSpec`. -/
theorem muxj_segK {b : Bool} {x cr s rst O qp : Nat → Bool} {lo hi wl wh R E : Nat}
    {ρ γ κ : Nat → Nat} {σ : Nat → Bool}
    (C : CelG G2 (pv2 x (gate b cr s)) rst O qp lo hi wl wh)
    (H_RST : ∀ t, rst t = decide (t < R)) (H_RST_LONG : hi + wh ≤ R)
    (H_LAT : hi + wh ≤ lo + E) (H_PWR : ∀ t, t < hi → O t = false)
    (hγ : ∀ k, γ k < γ (k + 1))
    (H_SEL_STABLE : ∀ n t, γ (2 * n) ≤ t → t < γ (2 * n + 1) → s t = σ n)
    (hκ : ∀ m, κ m < κ (m + 1)) (hκb : ∀ m, σ (κ m) = b)
    (hκall : ∀ n, σ n = b → ∃ m, κ m = n)
    (H_RST_EARLY : R ≤ max (ρ 0) (gc κ γ 0))
    (H_SND : ∀ j, nt O lo hi (max (ρ j) (gc κ γ j)) (Vph j) + E ≤ ρ (j + 1) ∧
      nt O lo hi (max (ρ j) (gc κ γ j)) (Vph j) + E ≤ gc κ γ (j + 1)) (k : Nat)
    (hx : SegK x ρ k) (hc : ∀ k', k' ≤ sN κ k → SegK cr γ k') :
    SegK O (fun j => nt O lo hi (max (ρ j) (gc κ γ j)) (Vph j)) k := by
  have hg := gated_segK hγ H_SEL_STABLE hκ hκb hκall k hc
  let ρ2 : Fin 2 → Nat → Nat := fun i => if i.val = 0 then ρ else gc κ γ
  have harr : ∀ i j, ρ2 i j ≤ max (ρ j) (gc κ γ j) := by
    intro i j; by_cases h : i.val = 0
    · simp only [ρ2, h, ite_true]; exact Nat.le_max_left _ _
    · simp only [ρ2, h, ite_false]; exact Nat.le_max_right _ _
  have hlast : ∀ j s, s < max (ρ j) (gc κ γ j) → ∃ i, s < ρ2 i j := by
    intro j s h; obtain ⟨i, hi⟩ := max_last h
    exact ⟨i, by by_cases hh : i.val = 0 <;> simp only [ρ2, hh, ite_true, ite_false] at hi ⊢ <;>
      exact hi⟩
  refine AssumeGuaranteeEnds.celG_segK law2 C (0 : Fin 2) H_RST H_RST_LONG H_LAT H_PWR harr
    hlast H_RST_EARLY (fun i j => ?_) k (fun hk i t h1 h2 => ?_) (fun j hk i t h1 h2 => ?_)
  · by_cases h : i.val = 0
    · simp only [ρ2, h, ite_true]; exact (H_SND j).1
    · simp only [ρ2, h, ite_false]; exact (H_SND j).2
  · subst hk
    by_cases h : i.val = 0
    · simp only [ρ2, h, ite_true] at h2; simp only [pv2, h, ite_true]
      exact hx t (Nat.zero_le _) h2
    · simp only [ρ2, h, ite_false] at h2; simp only [pv2, h, ite_false]
      exact hg t (Nat.zero_le _) h2
  · subst hk
    by_cases h : i.val = 0
    · simp only [ρ2, h, ite_true] at h1 h2; simp only [pv2, h, ite_true]
      exact hx t h1 h2
    · simp only [ρ2, h, ite_false] at h1 h2; simp only [pv2, h, ite_false]
      exact hg t h1 h2

/-- **The REAL `uj0`** (`bd_mux` LUT6 INIT `0xAE08`, pins `x_req, ctl_req, s, j0, rst`): its
generated excitation is `G2` of `(x_req, ctl_req ∧ ¬s)` (`uj0_exc`), so B's `CelG` model of
the real LUT is the `G2` model, and `muxj_segK` applies with `b = false`. -/
theorem uj0_cel {x cr s rst O qp : Nat → Bool} {lo hi wl wh : Nat}
    (H_LUT_WIN : Win lo hi (fun t => genF bd_mux_W2 "uj0" .O ["x_req", "ctl_req", "s", "j0", "rst"]
      [x t, cr t, s t, qp t, rst t]) O)
    (H_NO_REVERT : NoRevertI lo hi (fun t => genF bd_mux_W2 "uj0" .O
      ["x_req", "ctl_req", "s", "j0", "rst"] [x t, cr t, s t, qp t, rst t]) O)
    (H_FB : CElemTiming.WinDelay wl wh O qp) (H_LUT_POS : 1 ≤ lo) :
    CelG G2 (pv2 x (gate false cr s)) rst O qp lo hi wl wh := by
  rw [uj0_exc] at H_LUT_WIN H_NO_REVERT
  exact ⟨H_LUT_WIN, H_NO_REVERT, H_FB, H_LUT_POS⟩

/-- **The REAL `uj1`** (INIT `0xEA80`, pins `y_req, ctl_req, s, j1, rst`), `b = true`. -/
theorem uj1_cel {y cr s rst O qp : Nat → Bool} {lo hi wl wh : Nat}
    (H_LUT_WIN : Win lo hi (fun t => genF bd_mux_W2 "uj1" .O ["y_req", "ctl_req", "s", "j1", "rst"]
      [y t, cr t, s t, qp t, rst t]) O)
    (H_NO_REVERT : NoRevertI lo hi (fun t => genF bd_mux_W2 "uj1" .O
      ["y_req", "ctl_req", "s", "j1", "rst"] [y t, cr t, s t, qp t, rst t]) O)
    (H_FB : CElemTiming.WinDelay wl wh O qp) (H_LUT_POS : 1 ≤ lo) :
    CelG G2 (pv2 y (gate true cr s)) rst O qp lo hi wl wh := by
  rw [uj1_exc] at H_LUT_WIN H_NO_REVERT
  exact ⟨H_LUT_WIN, H_NO_REVERT, H_FB, H_LUT_POS⟩

/-! ## 3. `bd_mux` acknowledges `uxa`/`uya`: holding through the other input's tokens -/

open Formal.Cells.LutFbBridge2 (gc_even gc_odd mono_of_succ)

/-- `uxa` (`bd_c2` inside `bd_mux`, INIT `0x00E8…`) with its real reset pin. -/
theorem uxa_gen : ∀ a z q r : Bool,
    genF bd_mux_W2 "uxa.u" .O ["j0", "z_ack", "x_ack", "rst"] [a, z, q, r] = (!r && cel2 a z q) := by
  decide +kernel

theorem uya_gen : ∀ a z q r : Bool,
    genF bd_mux_W2 "uya.u" .O ["j1", "z_ack", "y_ack", "rst"] [a, z, q, r] = (!r && cel2 a z q) := by
  decide +kernel

theorem uxa_exc (a z qp rst : Nat → Bool) :
    (fun t => genF bd_mux_W2 "uxa.u" .O ["j0", "z_ack", "x_ack", "rst"] [a t, z t, qp t, rst t]) =
    (fun t => G2 (pv2 a z t) (qp t) (rst t)) := by
  funext t; rw [uxa_gen]; rfl

theorem uya_exc (a z qp rst : Nat → Bool) :
    (fun t => genF bd_mux_W2 "uya.u" .O ["j1", "z_ack", "y_ack", "rst"] [a t, z t, qp t, rst t]) =
    (fun t => G2 (pv2 a z t) (qp t) (rst t)) := by
  funext t; rw [uya_gen]; rfl

theorem vph_true_even {n : Nat} (h : Vph n = true) : n % 2 = 0 := by
  rcases Nat.mod_two_eq_zero_or_one n with e | e
  · exact e
  · rw [show n = 2 * (n / 2) + 1 by omega, PipeTimed.Vph_odd] at h; cases h

/-- A step signal read up to segment `B` is high at `s < ζ B` only inside one of its high
phases `[ζ (2n), ζ (2n+1))` with `2n + 1 ≤ B`. -/
theorem z_high {z : Nat → Bool} {ζ : Nat → Nat} {B s : Nat} (hζ : ∀ n, ζ n < ζ (n + 1))
    (hz : ∀ k', k' ≤ B → SegK z ζ k') (hs : s < ζ B) (h : z s = true) :
    ∃ n, ζ (2 * n) ≤ s ∧ s < ζ (2 * n + 1) ∧ 2 * n + 1 ≤ B := by
  have zm := mono_of_succ hζ
  rcases LutFbBridge.seg_of_mono ζ hζ s with h0 | ⟨n', n1, n2⟩
  · have := hz 0 (Nat.zero_le _) s (Nat.zero_le _) h0; rw [h] at this; cases this
  · have hn : n' < B := by
      apply Classical.byContradiction; intro hc; have := zm B n' (by omega); omega
    have hv : z s = Vph n' := hz (n' + 1) (by omega) s n1 n2
    rw [h] at hv
    have he := vph_true_even hv.symm
    refine ⟨n' / 2, ?_, ?_, by omega⟩
    · rw [show 2 * (n' / 2) = n' by omega]; exact n1
    · rw [show 2 * (n' / 2) + 1 = n' + 1 by omega]; exact n2

/-- **A mux acknowledge C-element, one segment** (`uxa = C(j0, z_ack)`, `uya = C(j1, z_ack)`,
as `G2`). The join pin `a` (edges `ρ`) is four-phase in the cell's own numbering; the
output acknowledge `z` (edges `ζ`) carries EVERY token of the mux output, and `κ` (strictly
increasing) picks the tokens of this input. Between this input's tokens `κ m` and `κ (m+1)`
the other input's tokens pulse `z` high; the cell holds low through them under exactly:

* `H_SNDZ`: the next `z` edge of ANY token comes `E` after the cell's edge (so the feedback
  has settled before a foreign pulse begins; the same bound as `CelSpec`'s `H_SND` read on
  `z`'s own edges);
* `H_ZFALL`: before the join rises for this input's token `m`, `z` has fallen for every
  earlier token (`ζ (2 κ m - 1) ≤ ρ (2m)`).

No select enumeration of the other input and no `σ` is needed. Reads: `a` at segment `k`,
`z` at segments `≤ sN κ k` (strictly causal: all end by the cell's phase start). -/
theorem muxa_segK {a z rst O qp : Nat → Bool} {lo hi wl wh R E : Nat} {ρ ζ κ : Nat → Nat}
    (C : CelG G2 (pv2 a z) rst O qp lo hi wl wh)
    (H_RST : ∀ t, rst t = decide (t < R)) (H_RST_LONG : hi + wh ≤ R)
    (H_LAT : hi + wh ≤ lo + E) (H_PWR : ∀ t, t < hi → O t = false)
    (hζ : ∀ n, ζ n < ζ (n + 1)) (hκ : ∀ m, κ m < κ (m + 1))
    (H_RST_EARLY : R ≤ max (ρ 0) (gc κ ζ 0))
    (H_SNDJ : ∀ j, nt O lo hi (max (ρ j) (gc κ ζ j)) (Vph j) + E ≤ ρ (j + 1))
    (H_SNDZ : ∀ j, nt O lo hi (max (ρ j) (gc κ ζ j)) (Vph j) + E ≤ ζ (sN κ j + 1))
    (H_ZFALL : ∀ m, 0 < κ m → ζ (2 * κ m - 1) ≤ ρ (2 * m))
    (k : Nat) (ha : SegK a ρ k) (hz : ∀ k', k' ≤ sN κ k → SegK z ζ k') :
    SegK O (fun j => nt O lo hi (max (ρ j) (gc κ ζ j)) (Vph j)) k := by
  have hlh := win_le C.H_LUT_WIN
  have zm := mono_of_succ hζ
  have km := mono_of_succ hκ
  have gap : ∀ j, max (ρ j) (gc κ ζ j) + lo + E ≤ max (ρ (j + 1)) (gc κ ζ (j + 1)) := by
    intro j
    have := nt_lo O (max (ρ j) (gc κ ζ j)) (Vph j) hlh (hi := hi)
    have := H_SNDJ j; have := Nat.le_max_left (ρ (j + 1)) (gc κ ζ (j + 1)); omega
  have cge : ∀ j, R ≤ max (ρ j) (gc κ ζ j) := by
    intro j
    induction j with
    | zero => exact H_RST_EARLY
    | succ j ih => have := gap j; omega
  have p0 : ∀ s, pv2 a z s 0 = a s := fun _ => rfl
  have p1 : ∀ s, pv2 a z s 1 = z s := fun _ => rfl
  have pall : ∀ s v, a s = v → z s = v → ∀ i, pv2 a z s i = v := by
    intro s v h1 h2 i
    by_cases hi : i.val = 0
    · simp only [pv2, hi, ite_true]; exact h1
    · simp only [pv2, hi, ite_false]; exact h2
  have gap2 : ∀ j, nt O lo hi (max (ρ j) (gc κ ζ j)) (Vph j) + E ≤
      max (ρ (j + 1)) (gc κ ζ (j + 1)) := fun j => by
    have := H_SNDJ j; have := Nat.le_max_left (ρ (j + 1)) (gc κ ζ (j + 1)); omega
  refine celX_segK law2 C H_RST H_RST_LONG H_LAT H_PWR k (fun hk s h1 h2 => ?_)
    (fun j hk => ⟨cge j, gap2 j, fun s h1 h2 => ?_⟩)
  · -- segment 0
    subst hk
    have e0 : gc κ ζ 0 = ζ (2 * κ 0) := by unfold gc; simp
    have s0 : sN κ 0 = 2 * κ 0 := by unfold sN; simp
    rw [e0] at h2
    by_cases ha0 : s < ρ 0
    · exact ⟨0, by rw [p0]; exact ha s (Nat.zero_le _) ha0⟩
    · refine ⟨1, ?_⟩
      rw [p1]
      cases hzs : z s
      · rfl
      · obtain ⟨n, n1, n2, n3⟩ := z_high (B := 2 * κ 0) hζ (fun k' h => hz k' (by rw [s0]; exact h))
          (by omega) hzs
        have hzf := H_ZFALL 0 (by omega)
        rw [Nat.mul_zero] at hzf
        have := zm (2 * n + 1) (2 * κ 0 - 1) (by omega)
        omega
  · subst hk
    have hsz := H_SNDZ j
    have hsj := H_SNDJ j
    generalize nt O lo hi (max (ρ j) (gc κ ζ j)) (Vph j) = N at hsz hsj ⊢
    obtain ⟨m, rfl | rfl⟩ : ∃ m, j = 2 * m ∨ j = 2 * m + 1 := ⟨j / 2, by omega⟩
    · -- high phase of this input's token `m`
      rw [gc_even] at h1; rw [gc_odd] at h2
      have ha' : ∀ t, ρ (2 * m) ≤ t → t < ρ (2 * m + 1) → a t = true := fun t u v => by
        have := ha t u v; rw [this]; exact PipeTimed.Vph_even m
      have hzs : ∀ t, ζ (2 * κ m) ≤ t → t < ζ (2 * κ m + 1) → z t = true := fun t u v => by
        have := hz (2 * κ m + 1) (by rw [sN_odd]; exact Nat.le_refl _) t u v
        rw [this]; exact PipeTimed.Vph_even _
      rw [sN_even] at hsz
      have hm1 := Nat.le_max_left (ρ (2 * m)) (ζ (2 * κ m))
      have hm2 := Nat.le_max_right (ρ (2 * m)) (ζ (2 * κ m))
      rw [PipeTimed.Vph_even]
      by_cases ha1 : s < ρ (2 * m + 1)
      · have hav : a s = true := ha' s (by omega) ha1
        by_cases hz1 : s < ζ (2 * κ m + 1)
        · exact Or.inl (pall s _ hav (hzs s (by omega) hz1))
        · exact Or.inr ⟨⟨0, by rw [p0]; exact hav⟩, by omega⟩
      · have hz1 : s < ζ (2 * κ m + 1) := by
          rcases Nat.lt_or_ge s (ζ (2 * κ m + 1)) with h | h
          · exact h
          · have : max (ρ (2 * m + 1)) (ζ (2 * κ m + 1)) ≤ s := Nat.max_le.2 ⟨by omega, h⟩
            omega
        exact Or.inr ⟨⟨1, by rw [p1]; exact hzs s (by omega) hz1⟩, by omega⟩
    · -- low phase between this input's tokens `m` and `m + 1`
      rw [gc_odd] at h1
      have e2 : gc κ ζ (2 * m + 1 + 1) = ζ (2 * κ (m + 1)) := by
        rw [show 2 * m + 1 + 1 = 2 * (m + 1) by omega, gc_even]
      have s2 : sN κ (2 * m + 1 + 1) = 2 * κ (m + 1) := by
        rw [show 2 * m + 1 + 1 = 2 * (m + 1) by omega, sN_even]
      rw [e2] at h2
      have ha' : ∀ t, ρ (2 * m + 1) ≤ t → t < ρ (2 * m + 2) → a t = false := fun t u v => by
        have := ha t u v; rw [this]; exact PipeTimed.Vph_odd m
      rw [sN_odd] at hsz
      have hk1 := hκ m
      have hm1 := Nat.le_max_left (ρ (2 * m + 1)) (ζ (2 * κ m + 1))
      have hm2 := Nat.le_max_right (ρ (2 * m + 1)) (ζ (2 * κ m + 1))
      have hsz' : N + E ≤ ζ (2 * κ m + 2) := hsz
      have hsj' : N + E ≤ ρ (2 * m + 2) := hsj
      rw [PipeTimed.Vph_odd]
      by_cases ha2 : s < ρ (2 * m + 2)
      · have hav : a s = false := ha' s (by omega) ha2
        by_cases hz2 : s < ζ (2 * κ m + 2)
        · have hzs : z s = false := by
            have := hz (2 * κ m + 2) (by rw [s2]; omega) s (by show ζ (2 * κ m + 1) ≤ s; omega) hz2
            rw [this]; exact PipeTimed.Vph_odd _
          exact Or.inl (pall s _ hav hzs)
        · exact Or.inr ⟨⟨0, by rw [p0]; exact hav⟩, by omega⟩
      · have hz2 : s < ζ (2 * κ (m + 1)) := by
          rcases Nat.lt_or_ge s (ζ (2 * κ (m + 1))) with h | h
          · exact h
          · have : max (ρ (2 * m + 1 + 1)) (ζ (2 * κ (m + 1))) ≤ s :=
              Nat.max_le.2 ⟨by show ρ (2 * m + 2) ≤ s; omega, h⟩
            omega
        have hzv : z s = false := by
          cases hzs : z s
          · rfl
          · obtain ⟨n, n1, n2, n3⟩ := z_high (B := 2 * κ (m + 1)) hζ
              (fun k' h => hz k' (by rw [s2]; exact h)) hz2 hzs
            have hzf := H_ZFALL (m + 1) (by omega)
            rw [show 2 * (m + 1) = 2 * m + 2 by omega] at hzf
            have := zm (2 * n + 1) (2 * κ (m + 1) - 1) (by omega)
            omega
        exact Or.inr ⟨⟨1, by rw [p1]; exact hzv⟩, by omega⟩

/-- **The REAL `uxa`/`uya` LUTs are the `G2` model** (`uxa_exc`, `uya_exc`). -/
theorem uxa_cel {a z rst O qp : Nat → Bool} {lo hi wl wh : Nat}
    (H_LUT_WIN : Win lo hi (fun t => genF bd_mux_W2 "uxa.u" .O ["j0", "z_ack", "x_ack", "rst"]
      [a t, z t, qp t, rst t]) O)
    (H_NO_REVERT : NoRevertI lo hi (fun t => genF bd_mux_W2 "uxa.u" .O
      ["j0", "z_ack", "x_ack", "rst"] [a t, z t, qp t, rst t]) O)
    (H_FB : CElemTiming.WinDelay wl wh O qp) (H_LUT_POS : 1 ≤ lo) :
    CelG G2 (pv2 a z) rst O qp lo hi wl wh := by
  rw [uxa_exc] at H_LUT_WIN H_NO_REVERT
  exact ⟨H_LUT_WIN, H_NO_REVERT, H_FB, H_LUT_POS⟩

theorem uya_cel {a z rst O qp : Nat → Bool} {lo hi wl wh : Nat}
    (H_LUT_WIN : Win lo hi (fun t => genF bd_mux_W2 "uya.u" .O ["j1", "z_ack", "y_ack", "rst"]
      [a t, z t, qp t, rst t]) O)
    (H_NO_REVERT : NoRevertI lo hi (fun t => genF bd_mux_W2 "uya.u" .O
      ["j1", "z_ack", "y_ack", "rst"] [a t, z t, qp t, rst t]) O)
    (H_FB : CElemTiming.WinDelay wl wh O qp) (H_LUT_POS : 1 ≤ lo) :
    CelG G2 (pv2 a z) rst O qp lo hi wl wh := by
  rw [uya_exc] at H_LUT_WIN H_NO_REVERT
  exact ⟨H_LUT_WIN, H_NO_REVERT, H_FB, H_LUT_POS⟩

/-- **The two conditions are the exact excitation conditions** (run mode, `rst = 0`):
`H_ZFALL` excludes a foreign pulse still high when the join rises (`C(1,1) = 1`: the
acknowledge would fire for the other input's token), and `H_SNDZ` excludes a foreign
pulse before the feedback has settled low (`C(0,1; q = 1) = 1`). In both cases the
excitation is `1` inside the cell's low phase. -/
theorem muxa_conds_tight :
    (∀ q, G2 (fun _ => true) q false = true) ∧ G2 (fun i => i.val != 0) true false = true :=
  ⟨fun q => by cases q <;> rfl, rfl⟩

/-! ## 4. The source `bd_src` (LUT1 `¬ack`, no reset pin) -/

open Formal.Net.Ops.Gen (src_gate)
open Formal.Cells.WinFifoCausal (cW vW)

/-- **The source's node edges**: the first rise is the power-up rise (first instant showing
1, searched up to `hi`); edge `j + 1` follows the acknowledge pin's edge `j`. -/
def srcE (O : Nat → Bool) (lo hi : Nat) (α : Nat → Nat) : Nat → Nat
  | 0 => nt O 0 hi 0 true
  | j + 1 => nt O lo hi (α j) (Vph (j + 1))

/-- **The source, one segment** (the REAL `bd_src` `u`, LUT1 `¬ack`: `Win` + H_NO_REVERT on
its generated excitation; no reset, so B's H_PWR is replaced by H_PWR_SRC: during the
power-up window `t < hi` the output may only rise). Segment `k + 1` of the node follows from
the acknowledge pin's segment `k` (offset one: segment `k` reads ack segments `< k`), and the
excitation spacing `H_SPACE` (an edge-time inequality on the acknowledge's edges). -/
theorem src_segK {a O : Nat → Bool} {lo hi : Nat} {α : Nat → Nat}
    (H_LUT_WIN : Win lo hi (fun t => genF bd_src_W2 "u" .O ["ack"] [a t]) O)
    (H_NO_REVERT : NoRevertI lo hi (fun t => genF bd_src_W2 "u" .O ["ack"] [a t]) O)
    (H_LUT_POS : 1 ≤ lo)
    (H_PWR_SRC : ∀ t, t + 1 < hi → O (t + 1) ≠ O t → O (t + 1) = true)
    (H_SPACE : hi ≤ α 0 ∧ ∀ j, α j + hi < α (j + 1) + lo) (k : Nat)
    (ha : ∀ k', k' + 1 ≤ k → SegK a α k') :
    SegK O (srcE O lo hi α) k := by
  have ex : (fun t => genF bd_src_W2 "u" .O ["ack"] [a t]) = fun t => !a t :=
    funext fun t => src_gate (a t)
  rw [ex] at H_LUT_WIN H_NO_REVERT
  have hlh := win_le H_LUT_WIN
  have am : ∀ j, hi ≤ α j := by
    intro j
    induction j with
    | zero => exact H_SPACE.1
    | succ j ih => have := H_SPACE.2 j; omega
  match k with
  | 0 =>
    intro t _ ht
    have := nt_before O 0 hi 0 true t (by omega) ht
    exact this
  | 1 =>
    have h0 := ha 0 (Nat.le_refl _)
    -- the excitation is 1 on `[0, α 0)`
    have x1 : ∀ s, 0 ≤ s → s < α 0 → (!a s) = true := by
      intro s _ hs; rw [h0 s (Nat.zero_le _) hs]; rfl
    have hhi : O hi = true := by
      obtain ⟨s, s1, s2, s3⟩ := H_LUT_WIN hi (Nat.le_refl _)
      rw [s3]; exact x1 s (Nat.zero_le _) (by have := H_SPACE.1; omega)
    have hle : nt O 0 hi 0 true ≤ hi := by
      apply Classical.byContradiction; intro hn
      have := PipeTimed.lfind_min (fun t => decide (0 + 0 ≤ t) && (O t == true)) (0 + hi + 1) hi
        (by unfold nt at hn; omega)
      simp [hhi] at this
    have hsp := PipeTimed.lfind_spec (fun t => decide (0 + 0 ≤ t) && (O t == true)) (0 + hi + 1)
      (by unfold nt at hle; omega)
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hsp
    -- before `hi` the output only rises
    have rise : ∀ d, nt O 0 hi 0 true + d < hi → O (nt O 0 hi 0 true + d) = true := by
      intro d
      induction d with
      | zero => intro _; exact hsp.2
      | succ d ih =>
        intro h
        by_cases hc : O (nt O 0 hi 0 true + d + 1) = O (nt O 0 hi 0 true + d)
        · rw [show nt O 0 hi 0 true + (d + 1) = nt O 0 hi 0 true + d + 1 by omega, hc]
          exact ih (by omega)
        · rw [show nt O 0 hi 0 true + (d + 1) = nt O 0 hi 0 true + d + 1 by omega]
          exact H_PWR_SRC _ (by omega) hc
    intro t h1 h2
    show O t = Vph 0
    rw [PipeTimed.Vph_even 0]
    have h1' : nt O 0 hi 0 true ≤ t := h1
    by_cases ht : t < hi
    · have := rise (t - nt O 0 hi 0 true) (by omega)
      rwa [show nt O 0 hi 0 true + (t - nt O 0 hi 0 true) = t by omega] at this
    · by_cases ht2 : t < α 0 + lo
      · exact H_NO_REVERT 0 (α 0) true hi t x1 (Nat.le_refl _) (by omega) (by omega) ht2 hhi
      · have h2' : t < nt O lo hi (α 0) (Vph 1) := h2
        have := nt_before O lo hi (α 0) (Vph 1) t (by omega) h2'
        rw [this, show (1 : Nat) = 0 + 1 from rfl, PipeTimed.Vph_succ, Bool.not_not,
          PipeTimed.Vph_even 0]
  | j + 2 =>
    have hj := ha (j + 1) (Nat.le_refl _)
    have xj : ∀ s, α j ≤ s → s < α (j + 1) → (!a s) = Vph (j + 1) := by
      intro s u v; rw [hj s u v, PipeTimed.Vph_succ]; rfl
    have nw := node_win (v := Vph (j + 1)) H_LUT_WIN H_NO_REVERT xj (am j) (H_SPACE.2 j)
    intro t h1 h2
    show O t = Vph (j + 1)
    have h1' : nt O lo hi (α j) (Vph (j + 1)) ≤ t := h1
    by_cases ht : t < α (j + 1) + lo
    · exact nw.2.2.1 t h1' ht
    · have h2' : t < nt O lo hi (α (j + 1)) (Vph (j + 1 + 1)) := h2
      have := nt_before O lo hi (α (j + 1)) (Vph (j + 1 + 1)) t (by omega) h2'
      rw [this, PipeTimed.Vph_succ, Bool.not_not]

/-- **H_WAIT of the source, unconditional**: edge `k` comes `lo` after every acknowledge
edge it reads (`k' < k`), given the acknowledge's edges are non-decreasing. -/
theorem src_wait {O : Nat → Bool} {lo hi : Nat} {α : Nat → Nat} (hlh : lo ≤ hi)
    (hα : ∀ i j, i ≤ j → α i ≤ α j) (k k' : Nat) (hk : k' < k) :
    α k' + lo ≤ srcE O lo hi α k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have := nt_lo O (α j) (Vph (j + 1)) hlh (hi := hi)
  have := hα k' j (by omega)
  show α k' + lo ≤ nt O lo hi (α j) (Vph (j + 1)); omega

/-- **The sink `bd_snk` has no cell**: its acknowledge output IS its request input net
(`assign ack = req`). In a gate-level network it contributes no node: the producer's
acknowledge pin is the routed path producer → sink → producer, a `Wire` like any other. -/
theorem snk_wire : bd_snk_W2.cells = [] ∧ bd_snk_W2.outputs = [("ack", .net 2)] ∧
    bd_snk_W2.inputs.head? = some ("req", 2) := ⟨rfl, rfl, rfl⟩

/-! ## 5. Non-vacuity, nonzero delays -/

namespace Wit
open Formal.Cells.PipeTimed.Wit (rstW)
open Formal.Cells.WinFifoCausal (nt_eq noRevertI_shift)

/-- Square waves of period 16 / 8 (high 4 ticks) from offset `o`, and their edges. -/
def pw16 (o t : Nat) : Bool := decide (o ≤ t ∧ (t - o) % 16 < 4)
def e16 (o j : Nat) : Nat := o + 16 * (j / 2) + 4 * (j % 2)
def pw8 (o t : Nat) : Bool := decide (o ≤ t ∧ (t - o) % 8 < 4)
def e8 (o j : Nat) : Nat := o + 8 * (j / 2) + 4 * (j % 2)

theorem pw16_segK (o k : Nat) : SegK (pw16 o) (e16 o) k := by
  match k with
  | 0 =>
    intro t _ ht
    show decide _ = false
    simp only [decide_eq_false_iff_not]; unfold e16 at ht; omega
  | j + 1 =>
    intro t h1 h2
    have h1' : e16 o j ≤ t := h1
    show decide _ = decide (j % 2 = 0)
    rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]; unfold e16 at h1' h2; omega

theorem pw8_segK (o k : Nat) : SegK (pw8 o) (e8 o) k := by
  match k with
  | 0 =>
    intro t _ ht
    show decide _ = false
    simp only [decide_eq_false_iff_not]; unfold e8 at ht; omega
  | j + 1 =>
    intro t h1 h2
    have h1' : e8 o j ≤ t := h1
    show decide _ = decide (j % 2 = 0)
    rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]; unfold e8 at h1' h2; omega

theorem e16_inc (o j : Nat) : e16 o j < e16 o (j + 1) := by unfold e16; omega
theorem e8_inc (o j : Nat) : e8 o j < e8 o (j + 1) := by unfold e8; omega

theorem pw16_per (o u : Nat) (h : o + 16 ≤ u) : pw16 o u = pw16 o (u - 16) := by
  unfold pw16; rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]; omega
theorem pw8_per (o u : Nat) (h : o + 16 ≤ u) : pw8 o u = pw8 o (u - 16) := by
  unfold pw8; rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]; omega

/-! ### The mux acknowledge `uxa` holding through a foreign token -/

/-- `j0` (the x join): high on `[16m+4, 16m+8)`; `z_ack`: EVERY output token, high on
`[8n+6, 8n+10)` (the even tokens are x's, `κ m = 2m`; the odd ones are y's); `uxa`: high on
`[16m+7, 16m+11)`. -/
def aM : Nat → Bool := pw16 4
def zM : Nat → Bool := pw8 6
def OM : Nat → Bool := pw16 7
def qpM (t : Nat) : Bool := OM (t - 1)
def κM (m : Nat) : Nat := 2 * m

theorem uxa_step_small : ∀ t, t < 40 → 1 ≤ t →
    OM t = (!rstW (t - 1) && cel2 (aM (t - 1)) (zM (t - 1)) (OM (t - 1 - 1))) := by
  decide

theorem uxa_step : ∀ t, 1 ≤ t →
    OM t = (!rstW (t - 1) && cel2 (aM (t - 1)) (zM (t - 1)) (OM (t - 1 - 1))) := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    intro ht
    by_cases hs : t < 40
    · exact uxa_step_small t hs ht
    · have h := ih (t - 16) (by omega) (by omega)
      have r1 : rstW (t - 1) = rstW (t - 16 - 1) := by unfold rstW; simp; omega
      unfold OM aM zM at h ⊢
      rw [pw16_per 7 t (by omega), pw16_per 4 (t - 1) (by omega), pw8_per 6 (t - 1) (by omega),
        pw16_per 7 (t - 1 - 1) (by omega), r1, h,
        show t - 1 - 16 = t - 16 - 1 by omega, show t - 1 - 1 - 16 = t - 16 - 1 - 1 by omega]

/-- **Non-vacuity of `muxa_segK` with a FOREIGN token** (the REAL `uxa` LUT via `uxa_cel`;
LUT band `[1, 1]`, feedback 1, reset 4): every hypothesis holds, every segment of the node
follows, and during the y-token pulse of `z_ack` (`t = 14`) the join is low and `uxa` stays
low (`OM 15 = false`) although `z_ack` is high. -/
theorem muxa_witness :
    CelG G2 (pv2 aM zM) rstW OM qpM 1 1 1 1 ∧
    (∀ k, SegK OM (fun j => nt OM 1 1 (max (e16 4 j) (gc κM (e8 6) j)) (Vph j)) k) ∧
    zM 14 = true ∧ aM 14 = false ∧ OM 15 = false := by
  have hW : Win 1 1 (fun t => genF bd_mux_W2 "uxa.u" .O ["j0", "z_ack", "x_ack", "rst"]
      [aM t, zM t, qpM t, rstW t]) OM := fun t ht =>
    ⟨t - 1, by omega, by omega, by
      show OM t = genF bd_mux_W2 "uxa.u" .O ["j0", "z_ack", "x_ack", "rst"]
        [aM (t - 1), zM (t - 1), qpM (t - 1), rstW (t - 1)]
      rw [uxa_gen, uxa_step t ht]; rfl⟩
  have hN : NoRevertI 1 1 (fun t => genF bd_mux_W2 "uxa.u" .O ["j0", "z_ack", "x_ack", "rst"]
      [aM t, zM t, qpM t, rstW t]) OM :=
    noRevertI_shift (fun t ht => by
      show OM t = genF bd_mux_W2 "uxa.u" .O ["j0", "z_ack", "x_ack", "rst"]
        [aM (t - 1), zM (t - 1), qpM (t - 1), rstW (t - 1)]
      rw [uxa_gen, uxa_step t ht]; rfl)
  have hF : CElemTiming.WinDelay 1 1 OM qpM := fun t ht => ⟨t - 1, by omega, by omega, rfl⟩
  have C := uxa_cel hW hN hF (Nat.le_refl 1)
  have gcM : ∀ j, gc κM (e8 6) j = 6 + 16 * (j / 2) + 4 * (j % 2) := fun j => by
    unfold gc κM e8; omega
  have ntM : ∀ j, nt OM 1 1 (max (e16 4 j) (gc κM (e8 6) j)) (Vph j) =
      7 + 16 * (j / 2) + 4 * (j % 2) := by
    intro j
    have hm : max (e16 4 j) (gc κM (e8 6) j) = 6 + 16 * (j / 2) + 4 * (j % 2) := by
      rw [gcM]; unfold e16; omega
    rw [hm, nt_eq OM (Nat.le_refl 1)]
    · omega
    · show decide _ = decide (j % 2 = 0)
      rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]; omega
  refine ⟨C, fun k => muxa_segK (E := 1) C (fun _ => rfl) (by decide) (by decide)
    (fun t h => by unfold OM pw16; simp; omega) (e8_inc 6) (fun m => by unfold κM; omega)
    (by rw [gcM]; unfold e16; omega)
    (fun j => by rw [ntM]; unfold e16; omega)
    (fun j => by rw [ntM]; unfold sN κM e8; omega)
    (fun m h => by unfold κM e8 e16; unfold κM at h; omega)
    k (pw16_segK 4 k) (fun k' _ => pw8_segK 6 k'), by decide, by decide, by decide⟩

/-! ### The mux join `uj0` on a token subset of its control -/

/-- `x_req`: high on `[16m+9, 16m+13)`; `ctl_req`: every control token, high on
`[8n+10, 8n+14)`; select `s`: token `n` selects `y` iff `n` is odd (so `uj0` gets the even
control tokens, `κ m = 2m`); `j0`: high on `[16m+11, 16m+15)`. -/
def xJ : Nat → Bool := pw16 9
def cJ : Nat → Bool := pw8 10
def sJ (t : Nat) : Bool := decide (10 ≤ t ∧ (t - 10) / 8 % 2 = 1)
def σJ (n : Nat) : Bool := n % 2 == 1
def OJ : Nat → Bool := pw16 11
def qpJ (t : Nat) : Bool := OJ (t - 1)
def κJ (m : Nat) : Nat := 2 * m

theorem sJ_per (u : Nat) (h : 26 ≤ u) : sJ u = sJ (u - 16) := by
  unfold sJ; rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]; omega

theorem uj0_step_small : ∀ t, t < 48 → 1 ≤ t →
    OJ t = (!rstW (t - 1) && cel2 (xJ (t - 1)) (cJ (t - 1) && !sJ (t - 1)) (OJ (t - 1 - 1))) := by
  decide

theorem uj0_step : ∀ t, 1 ≤ t →
    OJ t = (!rstW (t - 1) && cel2 (xJ (t - 1)) (cJ (t - 1) && !sJ (t - 1)) (OJ (t - 1 - 1))) := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    intro ht
    by_cases hs : t < 48
    · exact uj0_step_small t hs ht
    · have h := ih (t - 16) (by omega) (by omega)
      have r1 : rstW (t - 1) = rstW (t - 16 - 1) := by unfold rstW; simp; omega
      unfold OJ xJ cJ at h ⊢
      rw [pw16_per 11 t (by omega), pw16_per 9 (t - 1) (by omega), pw8_per 10 (t - 1) (by omega),
        sJ_per (t - 1) (by omega), pw16_per 11 (t - 1 - 1) (by omega), r1, h,
        show t - 1 - 16 = t - 16 - 1 by omega, show t - 1 - 1 - 16 = t - 16 - 1 - 1 by omega]

/-- **Non-vacuity of `muxj_segK`** (the REAL `uj0` LUT via `uj0_cel`, band `[1, 1]`, feedback
1, reset 4): the control carries tokens for both inputs, `uj0` receives only the even ones
(`κ m = 2m`, H_SEL_STABLE on the real select trace); every hypothesis holds and every node
segment follows; during the y-token (`t = 18`) the control request is high and `j0` stays
low. -/
theorem muxj_witness :
    CelG G2 (pv2 xJ (gate false cJ sJ)) rstW OJ qpJ 1 1 1 1 ∧
    (∀ k, SegK OJ (fun j => nt OJ 1 1 (max (e16 9 j) (gc κJ (e8 10) j)) (Vph j)) k) ∧
    cJ 18 = true ∧ OJ 19 = false := by
  have hW : Win 1 1 (fun t => genF bd_mux_W2 "uj0" .O ["x_req", "ctl_req", "s", "j0", "rst"]
      [xJ t, cJ t, sJ t, qpJ t, rstW t]) OJ := fun t ht =>
    ⟨t - 1, by omega, by omega, by
      show OJ t = genF bd_mux_W2 "uj0" .O ["x_req", "ctl_req", "s", "j0", "rst"]
        [xJ (t - 1), cJ (t - 1), sJ (t - 1), qpJ (t - 1), rstW (t - 1)]
      rw [LutFbBridge2.uj0_gen, uj0_step t ht]; rfl⟩
  have hN : NoRevertI 1 1 (fun t => genF bd_mux_W2 "uj0" .O
      ["x_req", "ctl_req", "s", "j0", "rst"] [xJ t, cJ t, sJ t, qpJ t, rstW t]) OJ :=
    noRevertI_shift (fun t ht => by
      show OJ t = genF bd_mux_W2 "uj0" .O ["x_req", "ctl_req", "s", "j0", "rst"]
        [xJ (t - 1), cJ (t - 1), sJ (t - 1), qpJ (t - 1), rstW (t - 1)]
      rw [LutFbBridge2.uj0_gen, uj0_step t ht]; rfl)
  have hF : CElemTiming.WinDelay 1 1 OJ qpJ := fun t ht => ⟨t - 1, by omega, by omega, rfl⟩
  have C := uj0_cel hW hN hF (Nat.le_refl 1)
  have gcJ : ∀ j, gc κJ (e8 10) j = 10 + 16 * (j / 2) + 4 * (j % 2) := fun j => by
    unfold gc κJ e8; omega
  have ntJ : ∀ j, nt OJ 1 1 (max (e16 9 j) (gc κJ (e8 10) j)) (Vph j) =
      11 + 16 * (j / 2) + 4 * (j % 2) := by
    intro j
    have hm : max (e16 9 j) (gc κJ (e8 10) j) = 10 + 16 * (j / 2) + 4 * (j % 2) := by
      rw [gcJ]; unfold e16; omega
    rw [hm, nt_eq OJ (Nat.le_refl 1)]
    · omega
    · show pw16 11 _ = decide (j % 2 = 0)
      unfold pw16; rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]; omega
  have hS : ∀ n t, e8 10 (2 * n) ≤ t → t < e8 10 (2 * n + 1) → sJ t = σJ n := by
    intro n t h1 h2
    unfold e8 at h1 h2
    have : (t - 10) / 8 = n := by omega
    unfold sJ σJ; rw [this]
    rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h] <;> omega
  refine ⟨C, fun k => muxj_segK (E := 1) C (fun _ => rfl) (by decide) (by decide)
    (fun t h => by unfold OJ pw16; simp; omega) (e8_inc 10) hS
    (fun m => by unfold κJ; omega) (fun m => by unfold σJ κJ; simp)
    (fun n h => ⟨n / 2, by unfold σJ at h; simp at h; unfold κJ; omega⟩)
    (by rw [gcJ]; unfold e16; omega)
    (fun j => ⟨by rw [ntJ]; unfold e16; omega, by rw [ntJ, gcJ]; omega⟩)
    k (pw16_segK 9 k) (fun k' _ => pw8_segK 10 k'), by decide, by decide⟩

/-! ### The source -/

def aS : Nat → Bool := pw8 3
def OS (t : Nat) : Bool := if t = 0 then false else !aS (t - 1)

/-- **Non-vacuity of `src_segK`** (the REAL `bd_src` LUT1, band `[1, 1]`; its acknowledge a
four-phase wave from `t = 3`): every hypothesis holds, every node segment follows, and the
source's first request edge is its power-up rise at `t = 1`, before any acknowledge. -/
theorem src_witness :
    Win 1 1 (fun t => genF bd_src_W2 "u" .O ["ack"] [aS t]) OS ∧
    NoRevertI 1 1 (fun t => genF bd_src_W2 "u" .O ["ack"] [aS t]) OS ∧
    (∀ k, SegK OS (srcE OS 1 1 (e8 3)) k) ∧ srcE OS 1 1 (e8 3) 0 = 1 := by
  have hx : ∀ t, 1 ≤ t → OS t = genF bd_src_W2 "u" .O ["ack"] [aS (t - 1)] := by
    intro t ht; rw [src_gate]; unfold OS; simp [show t ≠ 0 by omega]
  have hW : Win 1 1 (fun t => genF bd_src_W2 "u" .O ["ack"] [aS t]) OS :=
    fun t ht => ⟨t - 1, by omega, by omega, hx t ht⟩
  have hN : NoRevertI 1 1 (fun t => genF bd_src_W2 "u" .O ["ack"] [aS t]) OS :=
    noRevertI_shift hx
  exact ⟨hW, hN, fun k => src_segK hW hN (Nat.le_refl 1) (fun t h => by omega)
    ⟨by decide, fun j => by unfold e8; omega⟩ k (fun k' _ => pw8_segK 3 k'), by decide⟩

end Wit

end Formal.Cells.AssumeGuaranteeMux
