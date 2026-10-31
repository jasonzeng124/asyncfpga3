import Formal.Cells.FiniteNetMixed
import Formal.Cells.AssumeGuaranteeMuxN
import Formal.Cells.AssumeGuaranteeMuxNTree

/-!
# Probe Bmn (shard B): muxn cells, the mux acknowledge and the C-trees, TRUNCATED form

Bfin2's time-indexed rule (`FiniteNet.ag_trunc`, `fnet_closed`, `fmixed_closed`) covers runs
that stop as well as infinite ones and needs no H_WAIT and no wire spacing. This file gives
the cells of `AssumeGuaranteeMuxN` / `AssumeGuaranteeMuxNTree` in that form (`FCellOK`):

## Assumed / proved / NOT covered

**Proved:**
* `tdgated`, `tdec`: the decoded gate `ctl_req ∧ (code(s0, s1) == k)` and the REAL decode
  LUT3, truncated (via Bfin2's `tgated` on the Bool trace `code == k`, and `tnode`).
  `FDecSpec`, `fdec_spec_cell`.
* `tz_high` and **`tmuxa`**: the mux acknowledge `C(j, z_ack)` (`bdc_muxn`'s `ua_k`, and
  `bd_mux`'s `uxa`/`uya`, which Bfin2 left open) truncated: `z_ack` carries every output
  token; the cell holds low through foreign tokens under the truncated `H_SNDZ` and
  `H_ZFALL` (now with EXISTENCE: before the join rises for this input's token `m`, `z_ack`'s
  fall for token `κ m - 1` has HAPPENED and come no later). `FMuxASpec`,
  `fmuxa_spec_cell`.
* `FBufSpec`, `fbuf_spec_cell`: the `uor` / stage-0 LUT1 buffers.
* `tand`, `FAndSpec`, `fand_spec_cell`: a FASTFALL stage `s[i] ∧ |j` of `bd_delay_gated`
  (REAL LUT2 `4'h8`), truncated: the excitation's edges are the later rise and the EARLIER
  fall, under ONE edge-time hypothesis per token (H_OVL: each pin rises before the other's
  fall of that token, and before the other's next rise). The segment rule could not carry
  these stages (`AssumeGuaranteeMuxN.Wit.gstage_not_causal`); the time-indexed rule can.
* `FCelNoSnd`, `FTree5`, `FTree6`, `ftree5_cel`, `ftree6_cel`: the fork trees' nodes are
  Bfin2's `FCelSpec`, inner departure bounds composed from the leaves' bound relative to
  the ROOT (truncated: for leaf edges that exist).
* `FMuxJSpec`, `fmuxj_spec_cell`: `bd_mux`'s joins as a truncated cell spec (a wrapper of
  Bfin2's `tmuxj`), so every `bd_mux` cell has one.
* Witnesses (in `AssumeGuaranteeMuxNFinWit`): `Wit.tmuxa_fin_witness` (a FINITE run of a mux acknowledge: input 0's token,
  a foreign token, then quiet; every hypothesis of `tmuxa` and the node clean at every
  `T`); `Wit.tand_fin_witness` (one token through a FASTFALL stage, then quiet);
  `Wit.ftree5_witness`, `Wit.ftree6_witness` (the segment-form tree networks with every
  edge set `True`, i.e. infinite runs, meet `FTree5`/`FTree6`); `Wit.tdec_witness` (the
  3-way decode run of `AssumeGuaranteeMuxN.Wit`, `L = True`).

**NOT covered:** the request OR `|j` (3 inputs; Bfin2's `tor_ex` is the 2-branch OR);
departure bounds are edge-time inequalities; the tree and decode witnesses are infinite runs
(`L = True`), only the mux-acknowledge and AND-stage witnesses are finite. Core Lean only.
-/

namespace Formal.Cells.AssumeGuaranteeMuxNFin
open Formal.Cells
open Formal.Cells.FiniteNet
open Formal.Cells.FiniteRuns (fe)
open Formal.Cells.AssumeGuaranteeEnds (GPin gE sN sN_even sN_odd gc_sN GC2 GC4 cmax cmax_arr
  cmax_last)
open Formal.Cells.AssumeGuaranteeEndsNet (GD)
open Formal.Cells.AssumeGuaranteeMuxNTree (rp5 ip4 rp6 ip2 snd_wire)
open Formal.Cells.WinFifo (Win win_le)
open Formal.Cells.WinFifoCausal (NoRevertI nt nt_lo nt_before)
open Formal.Cells.PipeTimed (Vph)
open Formal.Cells.LutFbBridge2 (CelLaw CelG gc gc_even gc_odd G2 law2 pv2 mono_of_succ)
open Formal.Cells.LutFbBridge2Env (Wire ε ε_lo)
open Formal.Cells.LibGapMuxN (code bit0 bit1 code_bits dec dec_eq)

/-! ## 1. The decoded gate and the decode, truncated -/

theorem tdgated {r s0 s1 : Nat → Bool} {γ σ κ : Nat → Nat} {Lγ : Nat → Prop} {k T : Nat}
    (hd : ∀ j, Lγ (j + 1) → Lγ j) (hγ : ∀ j, Lγ (j + 1) → γ j < γ (j + 1))
    (H_SEL_STABLE : ∀ n t, Lγ (2 * n) → γ (2 * n) ≤ t → (Lγ (2 * n + 1) → t < γ (2 * n + 1)) →
      s0 t = bit0 (σ n) ∧ s1 t = bit1 (σ n))
    (H_S_RANGE : ∀ n, σ n < 4)
    (hκ : ∀ m, κ m < κ (m + 1)) (hκk : ∀ m, σ (κ m) = k)
    (hκall : ∀ n, σ n = k → ∃ m, κ m = n) (hr : GPhT r γ Lγ T) :
    GPhT (fun t => r t && (code (s0 t) (s1 t) == k)) (gc κ γ) (fun j => Lγ (sN κ j)) T := by
  have g := tgated (s := fun t => code (s0 t) (s1 t) == k) (σ := fun n => σ n == k) (b := true)
    hd hγ (fun n t a b c => by
      obtain ⟨e0, e1⟩ := H_SEL_STABLE n t a b c
      show (code (s0 t) (s1 t) == k) = (σ n == k)
      rw [e0, e1, code_bits _ (H_S_RANGE n)]) hκ (fun m => by simp [hκk m])
    (fun n h => hκall n (by simpa using h)) hr
  have e : (fun t => r t && ((code (s0 t) (s1 t) == k) == true)) =
      (fun t => r t && (code (s0 t) (s1 t) == k)) := by
    funext t; cases (code (s0 t) (s1 t) == k) <;> rfl
  rw [e] at g; exact g

/-- **Decode `k`, truncated** (the REAL inferred LUT3). -/
theorem tdec (k : Nat) (hk : k < 3) {cr s0 s1 O : Nat → Bool} {lo hi T : Nat}
    {γ σ κ : Nat → Nat} {Lγ : Nat → Prop}
    (H_LUT_WIN : Win lo hi (fun t => dec k (s0 t) (s1 t) (cr t)) O)
    (H_NO_REVERT : NoRevertI lo hi (fun t => dec k (s0 t) (s1 t) (cr t)) O)
    (H_PWR : ∀ t, t < hi → O t = false)
    (hd : ∀ j, Lγ (j + 1) → Lγ j) (hγ : ∀ j, Lγ (j + 1) → γ j < γ (j + 1))
    (H_SEL_STABLE : ∀ n t, Lγ (2 * n) → γ (2 * n) ≤ t → (Lγ (2 * n + 1) → t < γ (2 * n + 1)) →
      s0 t = bit0 (σ n) ∧ s1 t = bit1 (σ n))
    (H_S_RANGE : ∀ n, σ n < 4)
    (hκ : ∀ m, κ m < κ (m + 1)) (hκk : ∀ m, σ (κ m) = k)
    (hκall : ∀ n, σ n = k → ∃ m, κ m = n)
    (H_FLOOR : ∀ j, Lγ (sN κ j) → hi ≤ gc κ γ j + lo)
    (hr : GPhT cr γ Lγ T) :
    GPhT O (fe O lo hi (gc κ γ)) (fun j => Lγ (sN κ j)) (T + lo) := by
  rw [AssumeGuaranteeMuxN.dec_exc k hk] at H_LUT_WIN H_NO_REVERT
  exact tnode H_LUT_WIN H_NO_REVERT
    (tdgated hd hγ H_SEL_STABLE H_S_RANGE hκ hκk hκall hr) H_FLOOR H_PWR

/-! ## 2. The mux acknowledge `C(j, z_ack)`, truncated -/

/-- A truncated step signal high at `s` is inside one of its high phases. -/
theorem tz_high {z : Nat → Bool} {ζ : Nat → Nat} {Lz : Nat → Prop} {T s : Nat}
    (hd : ∀ j, Lz (j + 1) → Lz j) (hζ : ∀ j, Lz (j + 1) → ζ j < ζ (j + 1))
    (hz : GPhT z ζ Lz T) (hs : s < T) (h : z s = true) :
    ∃ n, Lz (2 * n) ∧ ζ (2 * n) ≤ s ∧ (Lz (2 * n + 1) → s < ζ (2 * n + 1)) := by
  rcases seg_find hd hζ s with h0 | ⟨j, hj, h1, h2⟩
  · rw [hz.pre s hs h0] at h; cases h
  · have hv := hz.ph j s hs hj h1 h2
    rw [h] at hv
    have he := AssumeGuaranteeMux.vph_true_even hv.symm
    refine ⟨j / 2, ?_, ?_, ?_⟩
    · rw [show 2 * (j / 2) = j by omega]; exact hj
    · rw [show 2 * (j / 2) = j by omega]; exact h1
    · rw [show 2 * (j / 2) + 1 = j + 1 by omega]; exact h2

/-- **The mux acknowledge, truncated** (`bdc_muxn`'s `ua_k`, `bd_mux`'s `uxa`/`uya`: B's `CelG`
of `G2` on the join `a` and the output acknowledge `z`, which carries EVERY output token;
`κ` this input's tokens). Node edge `j` exists iff join edge `j` and `z` edge `sN κ j` do.
The cell holds low through foreign `z` pulses under `H_SNDZ` (the next `z` edge comes `E`
after the cell's) and `H_ZFALL` (before the join rises for token `m`, `z`'s fall for token
`κ m - 1` has HAPPENED, no later than the join's rise). -/
theorem tmuxa {a z rst O qp : Nat → Bool} {lo hi wl wh R E T : Nat} {ρ ζ κ : Nat → Nat}
    {La Lz Ln : Nat → Prop}
    (C : CelG G2 (pv2 a z) rst O qp lo hi wl wh)
    (H_RST : ∀ t, rst t = decide (t < R)) (H_RST_LONG : hi + wh ≤ R)
    (H_LAT : hi + wh ≤ lo + E) (H_PWR : ∀ t, t < hi → O t = false)
    (hdz : ∀ j, Lz (j + 1) → Lz j) (hζ : ∀ j, Lz (j + 1) → ζ j < ζ (j + 1))
    (H_CNT : ∀ j, Ln j ↔ La j ∧ Lz (sN κ j))
    (hcR : ∀ j, Ln j → R ≤ max (ρ j) (gc κ ζ j))
    (H_SNDJ : ∀ j, Ln j → La (j + 1) →
      nt O lo hi (max (ρ j) (gc κ ζ j)) (Vph j) + E ≤ ρ (j + 1))
    (H_SNDZ : ∀ j, Ln j → Lz (sN κ j + 1) →
      nt O lo hi (max (ρ j) (gc κ ζ j)) (Vph j) + E ≤ ζ (sN κ j + 1))
    (H_ZFALL : ∀ m, 0 < κ m → La (2 * m) → Lz (2 * κ m - 1) ∧ ζ (2 * κ m - 1) ≤ ρ (2 * m))
    (ha : GPhT a ρ La T) (hz : GPhT z ζ Lz T) :
    GPhT O (fe O lo hi (fun j => max (ρ j) (gc κ ζ j))) Ln (T + lo) := by
  have zm := mono_ex hdz hζ
  have zd := down_ex hdz
  -- `z` is low once this input's join has risen for token `m`, until `z` rises for `κ m`
  have zlow : ∀ m s, s < T → La (2 * m) → ρ (2 * m) ≤ s →
      (Lz (2 * κ m) → s < ζ (2 * κ m)) → z s = false := by
    intro m s hs hL h1 h2
    cases hzs : z s
    · rfl
    · obtain ⟨n, n1, n2, n3⟩ := tz_high hdz hζ hz hs hzs
      have hn : n < κ m := by
        apply Classical.byContradiction; intro hc
        have hL2 : Lz (2 * κ m) := zd _ _ (by omega) n1
        have := zm (2 * κ m) (2 * n) (by omega) n1
        have := h2 hL2; omega
      obtain ⟨f1, f2⟩ := H_ZFALL m (by omega) hL
      have hl : Lz (2 * n + 1) := zd _ _ (by omega) f1
      have := zm (2 * n + 1) (2 * κ m - 1) (by omega) f1
      have := n3 hl; omega
  refine tcelX law2 C H_RST H_RST_LONG H_LAT H_PWR hcR (fun s hs hR h => ?_)
    (fun j s hs hj h1 h2 => ?_)
  · -- before the first node edge
    by_cases ha0 : La 0 ∧ ρ 0 ≤ s
    · refine ⟨1, ?_⟩
      show z s = false
      refine zlow 0 s hs ha0.1 ha0.2 (fun hz0 => ?_)
      have e0 : gc κ ζ 0 = ζ (2 * κ 0) := gc_even κ ζ 0
      have s0 : sN κ 0 = 2 * κ 0 := sN_even κ 0
      rcases h with h | h
      · exact absurd ((H_CNT 0).2 ⟨ha0.1, by rw [s0]; exact hz0⟩) h
      · rw [e0] at h; have := ha0.2; omega
    · refine ⟨0, ?_⟩
      show a s = false
      refine ha.pre s hs ?_
      by_cases h0 : La 0
      · exact Or.inr (by apply Classical.byContradiction; intro hc; exact ha0 ⟨h0, by omega⟩)
      · exact Or.inl h0
  · obtain ⟨hLa, hLz⟩ := (H_CNT j).1 hj
    have hsz := H_SNDZ j hj
    have hsj := H_SNDJ j hj
    generalize nt O lo hi (max (ρ j) (gc κ ζ j)) (Vph j) = N at hsz hsj ⊢
    obtain ⟨m, rfl | rfl⟩ : ∃ m, j = 2 * m ∨ j = 2 * m + 1 := ⟨j / 2, by omega⟩
    · -- high phase of this input's token `m`
      rw [gc_even] at h1
      rw [sN_even] at hLz hsz
      have e2 : gc κ ζ (2 * m + 1) = ζ (2 * κ m + 1) := gc_odd κ ζ m
      have hs2 : sN κ (2 * m + 1) = 2 * κ m + 1 := sN_odd κ m
      rw [e2] at h2
      have hm1 := Nat.le_max_left (ρ (2 * m)) (ζ (2 * κ m))
      have hm2 := Nat.le_max_right (ρ (2 * m)) (ζ (2 * κ m))
      rw [PipeTimed.Vph_even]
      by_cases hA : La (2 * m + 1) → s < ρ (2 * m + 1)
      · have hav : a s = true := by
          have := ha.ph (2 * m) s hs hLa (by omega) hA; rw [this, PipeTimed.Vph_even]
        by_cases hZ : Lz (2 * κ m + 1) → s < ζ (2 * κ m + 1)
        · have hzv : z s = true := by
            have := hz.ph (2 * κ m) s hs hLz (by omega) hZ; rw [this, PipeTimed.Vph_even]
          refine Or.inl (fun i => ?_)
          by_cases hi : i.val = 0
          · simp only [pv2, hi, ite_true]; exact hav
          · simp only [pv2, hi, ite_false]; exact hzv
        · have hZ' : Lz (2 * κ m + 1) ∧ ζ (2 * κ m + 1) ≤ s := by
            apply Classical.byContradiction; intro hc
            exact hZ (fun hl => by apply Classical.byContradiction; intro hc'; exact hc ⟨hl, by omega⟩)
          exact Or.inr ⟨⟨0, hav⟩, by have := hsz hZ'.1; omega⟩
      · have hA' : La (2 * m + 1) ∧ ρ (2 * m + 1) ≤ s := by
          apply Classical.byContradiction; intro hc
          exact hA (fun hl => by apply Classical.byContradiction; intro hc'; exact hc ⟨hl, by omega⟩)
        by_cases hZ : Lz (2 * κ m + 1) → s < ζ (2 * κ m + 1)
        · have hzv : z s = true := by
            have := hz.ph (2 * κ m) s hs hLz (by omega) hZ; rw [this, PipeTimed.Vph_even]
          exact Or.inr ⟨⟨1, hzv⟩, by have := hsj hA'.1; omega⟩
        · have hZ' : Lz (2 * κ m + 1) ∧ ζ (2 * κ m + 1) ≤ s := by
            apply Classical.byContradiction; intro hc
            exact hZ (fun hl => by apply Classical.byContradiction; intro hc'; exact hc ⟨hl, by omega⟩)
          have hn1 : Ln (2 * m + 1) := (H_CNT _).2 ⟨hA'.1, by rw [hs2]; exact hZ'.1⟩
          have := h2 hn1
          have := Nat.max_le.2 ⟨hA'.2, hZ'.2⟩
          omega
    · -- low phase after this input's token `m`
      rw [gc_odd] at h1
      rw [sN_odd] at hLz hsz
      have e2 : gc κ ζ (2 * m + 1 + 1) = ζ (2 * κ (m + 1)) := by
        rw [show 2 * m + 1 + 1 = 2 * (m + 1) by omega, gc_even]
      have hs2 : sN κ (2 * m + 1 + 1) = 2 * κ (m + 1) := by
        rw [show 2 * m + 1 + 1 = 2 * (m + 1) by omega, sN_even]
      rw [e2] at h2
      have hm1 := Nat.le_max_left (ρ (2 * m + 1)) (ζ (2 * κ m + 1))
      have hm2 := Nat.le_max_right (ρ (2 * m + 1)) (ζ (2 * κ m + 1))
      rw [PipeTimed.Vph_odd]
      by_cases hA : La (2 * m + 1 + 1) → s < ρ (2 * m + 1 + 1)
      · have hav : a s = false := by
          have := ha.ph (2 * m + 1) s hs hLa (by omega) hA; rw [this, PipeTimed.Vph_odd]
        cases hzs : z s
        · refine Or.inl (fun i => ?_)
          by_cases hi : i.val = 0
          · simp only [pv2, hi, ite_true]; exact hav
          · simp only [pv2, hi, ite_false]; exact hzs
        · obtain ⟨n, n1, n2, n3⟩ := tz_high hdz hζ hz hs hzs
          have hn : κ m + 1 ≤ n := by
            apply Classical.byContradiction; intro hc
            have hl : Lz (2 * n + 1) := zd _ _ (by omega) hLz
            have := zm (2 * n + 1) (2 * κ m + 1) (by omega) hLz
            have := n3 hl; omega
          have hl2 : Lz (2 * κ m + 1 + 1) := zd _ _ (by omega) n1
          have := zm (2 * κ m + 1 + 1) (2 * n) (by omega) n1
          exact Or.inr ⟨⟨0, hav⟩, by have := hsz hl2; omega⟩
      · have hA' : La (2 * m + 1 + 1) ∧ ρ (2 * m + 1 + 1) ≤ s := by
          apply Classical.byContradiction; intro hc
          exact hA (fun hl => by apply Classical.byContradiction; intro hc'; exact hc ⟨hl, by omega⟩)
        have hL2 : La (2 * (m + 1)) := by rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega]; exact hA'.1
        have hzv : z s = false := zlow (m + 1) s hs hL2
          (by rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega]; exact hA'.2)
          (fun hz2 => by
            have hn2 : Ln (2 * m + 1 + 1) := (H_CNT _).2 ⟨hA'.1, by rw [hs2]; exact hz2⟩
            have := h2 hn2
            have := hA'.2
            rcases Nat.lt_or_ge s (ζ (2 * κ (m + 1))) with h' | h'
            · exact h'
            · have := Nat.max_le.2 ⟨hA'.2, h'⟩; omega)
        exact Or.inr ⟨⟨1, hzv⟩, by have := hsj hA'.1; omega⟩

/-! ## 3. Cell specs, truncated form -/

variable {ι : Type}

/-- **A decode LUT3 of `bdc_muxn`**, truncated (`DecSpec` with an edge set). -/
structure FDecSpec (D : GD ι) (L : ι → Nat → Prop) (c : ι) (cp : GPin ι) (k : Nat)
    (s0 s1 : Nat → Bool) (σ κ : Nat → Nat) : Prop where
  H_K : k < 3
  H_PINS : D.pins c = [cp]
  H_LUT_WIN : Win (D.lo c) (D.hi c) (fun t => dec k (s0 t) (s1 t) (cp.P t)) (D.O c)
  H_NO_REVERT : NoRevertI (D.lo c) (D.hi c) (fun t => dec k (s0 t) (s1 t) (cp.P t)) (D.O c)
  H_PWR : ∀ t, t < D.hi c → D.O c t = false
  H_TIMES : ∀ j, D.τ c j = nt (D.O c) (D.lo c) (D.hi c) (gc κ (gE D.τ cp) j) (Vph j)
  H_CNT : ∀ j, L c j ↔ L cp.drv (sN κ j)
  H_DOWN : ∀ j, L cp.drv (j + 1) → L cp.drv j
  H_INC : ∀ j, L cp.drv (j + 1) → gE D.τ cp j < gE D.τ cp (j + 1)
  H_SEL_STABLE : ∀ n t, L cp.drv (2 * n) → gE D.τ cp (2 * n) ≤ t →
    (L cp.drv (2 * n + 1) → t < gE D.τ cp (2 * n + 1)) → s0 t = bit0 (σ n) ∧ s1 t = bit1 (σ n)
  H_S_RANGE : ∀ n, σ n < 4
  H_KAPPA : ∀ m, κ m < κ (m + 1)
  H_KAPPA_K : ∀ m, σ (κ m) = k
  H_KAPPA_ALL : ∀ n, σ n = k → ∃ m, κ m = n
  H_FLOOR : ∀ j, L c j → D.hi c ≤ gc κ (gE D.τ cp) j + D.lo c

/-- **A mux acknowledge** (`ua_k` of `bdc_muxn`; also `bd_mux`'s `uxa`/`uya`), truncated. -/
structure FMuxASpec (D : GD ι) (L : ι → Nat → Prop) (c : ι) (ap zp : GPin ι) (κ : Nat → Nat)
    (E : Nat) : Prop where
  H_PINS : D.pins c = [ap, zp]
  H_CEL : CelG G2 (pv2 ap.P zp.P) D.rst (D.O c) (D.qp c) (D.lo c) (D.hi c) (D.fl c) (D.fh c)
  H_PWR : ∀ t, t < D.hi c → D.O c t = false
  H_TIMES : ∀ j, L c j → D.τ c j =
    nt (D.O c) (D.lo c) (D.hi c) (max (gE D.τ ap j) (gc κ (gE D.τ zp) j)) (Vph j)
  H_CNT : ∀ j, L c j ↔ L ap.drv j ∧ L zp.drv (sN κ j)
  H_DOWNZ : ∀ j, L zp.drv (j + 1) → L zp.drv j
  H_INCZ : ∀ j, L zp.drv (j + 1) → gE D.τ zp j < gE D.τ zp (j + 1)
  H_RST_EARLY : ∀ j, L c j → D.R ≤ max (gE D.τ ap j) (gc κ (gE D.τ zp) j)
  H_SNDJ : ∀ j, L c j → L ap.drv (j + 1) → D.τ c j + E ≤ gE D.τ ap (j + 1)
  H_SNDZ : ∀ j, L c j → L zp.drv (sN κ j + 1) → D.τ c j + E ≤ gE D.τ zp (sN κ j + 1)
  H_ZFALL : ∀ m, 0 < κ m → L ap.drv (2 * m) →
    L zp.drv (2 * κ m - 1) ∧ gE D.τ zp (2 * κ m - 1) ≤ gE D.τ ap (2 * m)
  H_RST_LONG : D.hi c + D.fh c ≤ D.R
  H_LAT : D.hi c + D.fh c ≤ D.lo c + E

/-- **A buffer** (`uor`, stage 0 of `bd_delay_gated`: LUT1 `2'h2`), truncated. -/
structure FBufSpec (D : GD ι) (L : ι → Nat → Prop) (c : ι) (p : GPin ι) : Prop where
  H_PINS : D.pins c = [p]
  H_LUT_WIN : Win (D.lo c) (D.hi c) p.P (D.O c)
  H_NO_REVERT : NoRevertI (D.lo c) (D.hi c) p.P (D.O c)
  H_PWR : ∀ t, t < D.hi c → D.O c t = false
  H_TIMES : ∀ j, L c j → D.τ c j = nt (D.O c) (D.lo c) (D.hi c) (gE D.τ p j) (Vph j)
  H_CNT : ∀ j, L c j ↔ L p.drv j
  H_FLOOR : ∀ j, L c j → D.hi c ≤ gE D.τ p j + D.lo c

section cls
variable {D : GD ι} {L : ι → Nat → Prop}

theorem fdec_spec_cell {c : ι} {cp : GPin ι} {k : Nat} {s0 s1 : Nat → Bool} {σ κ : Nat → Nat}
    (S : FDecSpec D L c cp k s0 s1 σ κ) : FCellOK D L c := by
  intro T hA
  have hτ : D.τ c = fe (D.O c) (D.lo c) (D.hi c) (gc κ (gE D.τ cp)) := funext S.H_TIMES
  have hL : L c = fun j => L cp.drv (sN κ j) := funext fun j => propext (S.H_CNT j)
  rw [hτ, hL]
  exact tdec k S.H_K S.H_LUT_WIN S.H_NO_REVERT S.H_PWR S.H_DOWN S.H_INC S.H_SEL_STABLE
    S.H_S_RANGE S.H_KAPPA S.H_KAPPA_K S.H_KAPPA_ALL (fun j hj => S.H_FLOOR j (by rw [hL]; exact hj))
    (hA cp (by rw [S.H_PINS]; simp))

theorem fmuxa_spec_cell (NW : FNetW D L) {c : ι} {ap zp : GPin ι} {κ : Nat → Nat} {E : Nat}
    (S : FMuxASpec D L c ap zp κ E) : FCellOK D L c := by
  intro T hA
  refine FiniteNet.gphT_congr (c' := fe (D.O c) (D.lo c) (D.hi c)
      (fun j => max (gE D.τ ap j) (gc κ (gE D.τ zp) j))) (fun j hj => S.H_TIMES j hj) ?_
  exact tmuxa S.H_CEL NW.H_RST S.H_RST_LONG S.H_LAT S.H_PWR S.H_DOWNZ S.H_INCZ S.H_CNT
    S.H_RST_EARLY (fun j h1 h2 => by rw [← S.H_TIMES j h1]; exact S.H_SNDJ j h1 h2)
    (fun j h1 h2 => by rw [← S.H_TIMES j h1]; exact S.H_SNDZ j h1 h2) S.H_ZFALL
    (hA ap (by rw [S.H_PINS]; simp)) (hA zp (by rw [S.H_PINS]; simp))

theorem fbuf_spec_cell {c : ι} {p : GPin ι} (S : FBufSpec D L c p) : FCellOK D L c := by
  intro T hA
  have hL : L c = L p.drv := funext fun j => propext (S.H_CNT j)
  refine FiniteNet.gphT_congr (c' := fe (D.O c) (D.lo c) (D.hi c) (gE D.τ p))
    (fun j hj => S.H_TIMES j hj) ?_
  rw [hL]
  exact tnode S.H_LUT_WIN S.H_NO_REVERT (hA p (by rw [S.H_PINS]; simp))
    (fun j hj => S.H_FLOOR j (by rw [hL]; exact hj)) S.H_PWR

end cls

/-! ## 4. The fork trees, truncated -/

/-- **`FCelSpec` without `H_SND` and `H_LAT`.** -/
structure FCelNoSnd {n : Nat} (G : (Fin n → Bool) → Bool → Bool → Bool) (D : GD ι)
    (L : ι → Nat → Prop) (c : ι) (pv : Fin n → GPin ι) : Prop where
  H_PINS : D.pins c = (List.finRange n).map pv
  H_LAW : CelLaw G
  H_CEL : CelG G (fun t i => (pv i).P t) D.rst (D.O c) (D.qp c) (D.lo c) (D.hi c) (D.fl c)
    (D.fh c)
  H_PWR : ∀ t, t < D.hi c → D.O c t = false
  H_TIMES : ∀ j, D.τ c j =
    nt (D.O c) (D.lo c) (D.hi c) (cmax (fun i => gE D.τ (pv i)) j) (Vph j)
  H_CNT : ∀ j, L c j ↔ ∀ i, L (pv i).drv j
  H_RST_EARLY : ∀ j, L c j → D.R ≤ cmax (fun i => gE D.τ (pv i)) j
  H_RST_LONG : D.hi c + D.fh c ≤ D.R

theorem FCelNoSnd.spec {n : Nat} {G : (Fin n → Bool) → Bool → Bool → Bool} {D : GD ι}
    {L : ι → Nat → Prop} {c : ι} {pv : Fin n → GPin ι} (N : FCelNoSnd G D L c pv) {E : Nat}
    (H_SND : ∀ i j, L c j → L (pv i).drv (j + 1) → D.τ c j + E ≤ gE D.τ (pv i) (j + 1))
    (H_LAT : D.hi c + D.fh c ≤ D.lo c + E) : FCelSpec G D L c pv E :=
  ⟨N.H_PINS, N.H_LAW, N.H_CEL, N.H_PWR, fun j _ => N.H_TIMES j, N.H_CNT, N.H_RST_EARLY, H_SND,
    N.H_RST_LONG, H_LAT⟩

theorem fsnd_up {n : Nat} {G : (Fin n → Bool) → Bool → Bool → Bool} {D : GD ι}
    {L : ι → Nat → Prop} {c : ι} {pv : Fin n → GPin ι} (N : FCelNoSnd G D L c pv) (i : Fin n)
    (j : Nat) : gE D.τ (pv i) j + D.lo c ≤ D.τ c j := by
  rw [N.H_TIMES j]
  have := nt_lo (D.O c) (cmax (fun i => gE D.τ (pv i)) j) (Vph j) (win_le N.H_CEL.H_LUT_WIN)
    (hi := D.hi c)
  have := cmax_arr (fun i => gE D.τ (pv i)) i j
  omega

/-- **A `forkH5` tree, truncated**: `H_ACK` only for leaf edges that exist. -/
structure FTree5 (D : GD ι) (L : ι → Nat → Prop) (r n : ι) (pin : GPin ι) (lv : Fin 5 → GPin ι)
    (E : Nat) : Prop where
  root : FCelNoSnd GC2 D L r (rp5 pin lv)
  inner : FCelNoSnd GC4 D L n (ip4 (m := 1) lv)
  H_DRV : pin.drv = n
  H_WIRE : Wire pin.wl pin.wh (D.O pin.drv) pin.P
  H_ACK : ∀ i j, L (lv i).drv (j + 1) → D.τ r j + E ≤ gE D.τ (lv i) (j + 1)
  H_LAT_R : D.hi r + D.fh r ≤ D.lo r + E
  H_LAT_N : D.hi n + D.fh n ≤ D.lo n + (E + pin.wl + D.lo r)

theorem ftree5_cel {D : GD ι} {L : ι → Nat → Prop} {r n : ι} {pin : GPin ι}
    {lv : Fin 5 → GPin ι} {E : Nat} (T : FTree5 D L r n pin lv E) :
    FCelSpec GC2 D L r (rp5 pin lv) E ∧
    FCelSpec GC4 D L n (ip4 (m := 1) lv) (E + pin.wl + D.lo r) := by
  refine ⟨T.root.spec (fun i j _ hl => ?_) T.H_LAT_R, T.inner.spec (fun i j _ hl => ?_) T.H_LAT_N⟩
  · by_cases h : i.val = 0
    · have e : rp5 pin lv i = pin := by simp only [rp5, h, ite_true]
      rw [e] at hl ⊢
      rw [T.H_DRV] at hl
      have h1 := snd_wire T.H_WIRE (j + 1)
      rw [T.H_DRV] at h1
      have h2 := fsnd_up T.inner 0 (j + 1)
      have h3 := T.H_ACK 0 j ((T.inner.H_CNT (j + 1)).1 hl 0)
      have e2 : ip4 (m := 1) lv 0 = lv 0 := rfl
      rw [e2] at h2
      omega
    · have e : rp5 pin lv i = lv 4 := by simp only [rp5, h, ite_false]
      rw [e] at hl ⊢; exact T.H_ACK 4 j hl
  · have h1 := snd_wire T.H_WIRE j
    rw [T.H_DRV] at h1
    have h2 := fsnd_up T.root 0 j
    have e : rp5 pin lv 0 = pin := rfl
    rw [e] at h2
    have h3 := T.H_ACK ⟨i.val, by omega⟩ j hl
    show D.τ n j + (E + pin.wl + D.lo r) ≤ gE D.τ (lv ⟨i.val, by omega⟩) (j + 1)
    omega

/-- **A `forkH6` tree, truncated.** -/
structure FTree6 (D : GD ι) (L : ι → Nat → Prop) (r na nb : ι) (pa pb : GPin ι)
    (lv : Fin 6 → GPin ι) (E : Nat) : Prop where
  root : FCelNoSnd GC2 D L r (rp6 pa pb)
  innerA : FCelNoSnd GC4 D L na (ip4 (m := 2) lv)
  innerB : FCelNoSnd GC2 D L nb (ip2 lv)
  H_DRVA : pa.drv = na
  H_DRVB : pb.drv = nb
  H_WIREA : Wire pa.wl pa.wh (D.O pa.drv) pa.P
  H_WIREB : Wire pb.wl pb.wh (D.O pb.drv) pb.P
  H_ACK : ∀ i j, L (lv i).drv (j + 1) → D.τ r j + E ≤ gE D.τ (lv i) (j + 1)
  H_LAT_R : D.hi r + D.fh r ≤ D.lo r + E
  H_LAT_A : D.hi na + D.fh na ≤ D.lo na + (E + pa.wl + D.lo r)
  H_LAT_B : D.hi nb + D.fh nb ≤ D.lo nb + (E + pb.wl + D.lo r)

theorem ftree6_cel {D : GD ι} {L : ι → Nat → Prop} {r na nb : ι} {pa pb : GPin ι}
    {lv : Fin 6 → GPin ι} {E : Nat} (T : FTree6 D L r na nb pa pb lv E) :
    FCelSpec GC2 D L r (rp6 pa pb) E ∧
    FCelSpec GC4 D L na (ip4 (m := 2) lv) (E + pa.wl + D.lo r) ∧
    FCelSpec GC2 D L nb (ip2 lv) (E + pb.wl + D.lo r) := by
  refine ⟨T.root.spec (fun i j _ hl => ?_) T.H_LAT_R, T.innerA.spec (fun i j _ hl => ?_) T.H_LAT_A,
    T.innerB.spec (fun i j _ hl => ?_) T.H_LAT_B⟩
  · by_cases h : i.val = 0
    · have e : rp6 pa pb i = pa := by simp only [rp6, h, ite_true]
      rw [e] at hl ⊢
      rw [T.H_DRVA] at hl
      have h1 := snd_wire T.H_WIREA (j + 1)
      rw [T.H_DRVA] at h1
      have h2 := fsnd_up T.innerA 0 (j + 1)
      have h3 := T.H_ACK 0 j ((T.innerA.H_CNT (j + 1)).1 hl 0)
      have e2 : ip4 (m := 2) lv 0 = lv 0 := rfl
      rw [e2] at h2
      omega
    · have e : rp6 pa pb i = pb := by simp only [rp6, h, ite_false]
      rw [e] at hl ⊢
      rw [T.H_DRVB] at hl
      have h1 := snd_wire T.H_WIREB (j + 1)
      rw [T.H_DRVB] at h1
      have h2 := fsnd_up T.innerB 0 (j + 1)
      have h3 := T.H_ACK 4 j ((T.innerB.H_CNT (j + 1)).1 hl 0)
      have e2 : ip2 lv 0 = lv 4 := rfl
      rw [e2] at h2
      omega
  · have h1 := snd_wire T.H_WIREA j
    rw [T.H_DRVA] at h1
    have h2 := fsnd_up T.root 0 j
    have e : rp6 pa pb 0 = pa := rfl
    rw [e] at h2
    have h3 := T.H_ACK ⟨i.val, by omega⟩ j hl
    show D.τ na j + (E + pa.wl + D.lo r) ≤ gE D.τ (lv ⟨i.val, by omega⟩) (j + 1)
    omega
  · have h1 := snd_wire T.H_WIREB j
    rw [T.H_DRVB] at h1
    have h2 := fsnd_up T.root 1 j
    have e : rp6 pa pb 1 = pb := rfl
    rw [e] at h2
    have h3 := T.H_ACK ⟨i.val + 4, by omega⟩ j hl
    show D.τ nb j + (E + pb.wl + D.lo r) ≤ gE D.τ (lv ⟨i.val + 4, by omega⟩) (j + 1)
    omega

/-! ## 5. A FASTFALL stage `s[i] ∧ |j`, truncated -/

/-- The AND's excitation edges: the later rise, the EARLIER fall. -/
def xe (ρ γ : Nat → Nat) (j : Nat) : Nat := if j % 2 = 0 then max (ρ j) (γ j) else min (ρ j) (γ j)

/-- **The AND excitation, truncated.** Both pins carry the same tokens (`H_SAME`: the same
edge set); **H_OVL**: each pin's edge `j` comes before the other's edge `j + 1` (each rises
before the other falls, and falls before the other rises again). Then `a ∧ g` is clean on
`[0, T)` with edges `xe`. No ordering between the two falls is needed: the stage may fall
from its gate BEFORE its data pin falls (FASTFALL). -/
theorem tand_ex {a g : Nat → Bool} {ρ γ : Nat → Nat} {La Lg : Nat → Prop} {T : Nat}
    (H_SAME : ∀ j, Lg j ↔ La j)
    (H_OVL : ∀ j, La (j + 1) → ρ j < γ (j + 1) ∧ γ j < ρ (j + 1))
    (ha : GPhT a ρ La T) (hg : GPhT g γ Lg T) :
    GPhT (fun t => a t && g t) (xe ρ γ) La T := by
  refine ⟨fun s hs h => ?_, fun j s hs hj h1 h2 => ?_⟩
  · show (a s && g s) = false
    by_cases h0 : La 0
    · have e : xe ρ γ 0 = max (ρ 0) (γ 0) := rfl
      rcases h with h | h
      · exact absurd h0 h
      · rw [e] at h
        by_cases h' : s < ρ 0
        · rw [ha.pre s hs (Or.inr h')]; rfl
        · rw [hg.pre s hs (Or.inr (by omega))]; simp
    · rw [ha.pre s hs (Or.inl h0)]; rfl
  · show (a s && g s) = Vph j
    have hgj : Lg j := (H_SAME j).2 hj
    obtain ⟨m, rfl | rfl⟩ : ∃ m, j = 2 * m ∨ j = 2 * m + 1 := ⟨j / 2, by omega⟩
    · have e0 : xe ρ γ (2 * m) = max (ρ (2 * m)) (γ (2 * m)) := by
        unfold xe; simp
      have e1 : xe ρ γ (2 * m + 1) = min (ρ (2 * m + 1)) (γ (2 * m + 1)) := by
        unfold xe; simp
      rw [e0] at h1; rw [e1] at h2
      have hav := ha.ph (2 * m) s hs hj (by omega) (fun h => by have := h2 h; omega)
      have hgv := hg.ph (2 * m) s hs hgj (by omega)
        (fun h => by have := h2 ((H_SAME _).1 h); omega)
      rw [hav, hgv, PipeTimed.Vph_even]; rfl
    · have e0 : xe ρ γ (2 * m + 1) = min (ρ (2 * m + 1)) (γ (2 * m + 1)) := by
        unfold xe; simp
      have e1 : xe ρ γ (2 * m + 1 + 1) = max (ρ (2 * m + 1 + 1)) (γ (2 * m + 1 + 1)) := by
        unfold xe; simp; omega
      rw [e0] at h1; rw [e1] at h2
      rw [PipeTimed.Vph_odd]
      -- one pin has fallen; it is low until its next rise, and the other covers the rest
      have lowA : ρ (2 * m + 1) ≤ s → (La (2 * m + 1 + 1) → s < ρ (2 * m + 1 + 1)) → a s = false :=
        fun u v => by rw [ha.ph (2 * m + 1) s hs hj u v, PipeTimed.Vph_odd]
      have lowG : γ (2 * m + 1) ≤ s → (Lg (2 * m + 1 + 1) → s < γ (2 * m + 1 + 1)) → g s = false :=
        fun u v => by rw [hg.ph (2 * m + 1) s hs hgj u v, PipeTimed.Vph_odd]
      by_cases hA : La (2 * m + 1 + 1) → s < ρ (2 * m + 1 + 1)
      · by_cases hρ : ρ (2 * m + 1) ≤ s
        · rw [lowA hρ hA]; rfl
        · have hγ : γ (2 * m + 1) ≤ s := by omega
          by_cases hG : Lg (2 * m + 1 + 1) → s < γ (2 * m + 1 + 1)
          · rw [lowG hγ hG]; simp
          · have hL : La (2 * m + 1 + 1) := Classical.byContradiction fun hn =>
              hG (fun h => absurd ((H_SAME _).1 h) hn)
            have := (H_OVL _ hL).1
            have : ¬ s < γ (2 * m + 1 + 1) := fun h => hG (fun _ => h)
            -- `g` rose again, so `a` (risen before) must have fallen: `ρ (2m+1) < γ (2m+2) ≤ s`
            omega
      · have hL : La (2 * m + 1 + 1) := Classical.byContradiction fun hn => hA (fun h => absurd h hn)
        have hs2 : ρ (2 * m + 1 + 1) ≤ s := Classical.byContradiction fun hn => hA (fun _ => by omega)
        have hsg : s < γ (2 * m + 1 + 1) := by have := h2 hL; omega
        have := (H_OVL _ hL).2
        rw [lowG (by omega) (fun _ => hsg)]; simp

/-- **A FASTFALL stage, truncated** (the REAL LUT2 `4'h8` on `[s[i], gate]`). -/
theorem tand {a g O : Nat → Bool} {lo hi T : Nat} {ρ γ : Nat → Nat} {La Lg : Nat → Prop}
    (H_LUT_WIN : Win lo hi (fun t => Formal.Cells.lutB 0x8 [a t, g t]) O)
    (H_NO_REVERT : NoRevertI lo hi (fun t => Formal.Cells.lutB 0x8 [a t, g t]) O)
    (H_PWR : ∀ t, t < hi → O t = false)
    (H_SAME : ∀ j, Lg j ↔ La j)
    (H_OVL : ∀ j, La (j + 1) → ρ j < γ (j + 1) ∧ γ j < ρ (j + 1))
    (H_FLOOR : ∀ j, La j → hi ≤ xe ρ γ j + lo)
    (ha : GPhT a ρ La T) (hg : GPhT g γ Lg T) :
    GPhT O (fe O lo hi (xe ρ γ)) La (T + lo) := by
  have ex : (fun t => Formal.Cells.lutB 0x8 [a t, g t]) = fun t => a t && g t :=
    funext fun t => AssumeGuaranteeMuxN.Wit.stg_eq (a t) (g t)
  rw [ex] at H_LUT_WIN H_NO_REVERT
  exact tnode H_LUT_WIN H_NO_REVERT (tand_ex H_SAME H_OVL ha hg) H_FLOOR H_PWR

/-- **A FASTFALL stage cell** (`bd_delay_gated` stages 1..N-1): data pin `ap` (`s[i]`), gate
pin `gp` (`|j`). -/
structure FAndSpec (D : GD ι) (L : ι → Nat → Prop) (c : ι) (ap gp : GPin ι) : Prop where
  H_PINS : D.pins c = [ap, gp]
  H_LUT_WIN : Win (D.lo c) (D.hi c) (fun t => Formal.Cells.lutB 0x8 [ap.P t, gp.P t]) (D.O c)
  H_NO_REVERT : NoRevertI (D.lo c) (D.hi c) (fun t => Formal.Cells.lutB 0x8 [ap.P t, gp.P t])
    (D.O c)
  H_PWR : ∀ t, t < D.hi c → D.O c t = false
  H_TIMES : ∀ j, D.τ c j = nt (D.O c) (D.lo c) (D.hi c) (xe (gE D.τ ap) (gE D.τ gp) j) (Vph j)
  H_CNT : ∀ j, L c j ↔ L ap.drv j
  H_SAME : ∀ j, L gp.drv j ↔ L ap.drv j
  H_OVL : ∀ j, L ap.drv (j + 1) →
    gE D.τ ap j < gE D.τ gp (j + 1) ∧ gE D.τ gp j < gE D.τ ap (j + 1)
  H_FLOOR : ∀ j, L c j → D.hi c ≤ xe (gE D.τ ap) (gE D.τ gp) j + D.lo c

theorem fand_spec_cell {D : GD ι} {L : ι → Nat → Prop} {c : ι} {ap gp : GPin ι}
    (S : FAndSpec D L c ap gp) : FCellOK D L c := by
  intro T hA
  have hτ : D.τ c = fe (D.O c) (D.lo c) (D.hi c) (xe (gE D.τ ap) (gE D.τ gp)) :=
    funext S.H_TIMES
  have hL : L c = L ap.drv := funext fun j => propext (S.H_CNT j)
  rw [hτ, hL]
  exact tand S.H_LUT_WIN S.H_NO_REVERT S.H_PWR S.H_SAME S.H_OVL
    (fun j hj => S.H_FLOOR j (by rw [hL]; exact hj))
    (hA ap (by rw [S.H_PINS]; simp)) (hA gp (by rw [S.H_PINS]; simp))

/-! ## 6. `bd_mux`'s join as a truncated cell spec (a wrapper of Bfin2's `tmuxj`) -/

open Formal.Cells.LutFbBridge2 (gate)

/-- **A `bd_mux` join** (`uj0`/`uj1`), truncated (`MuxJSpec` with an edge set). -/
structure FMuxJSpec (D : GD ι) (L : ι → Nat → Prop) (c : ι) (xp cp : GPin ι) (b : Bool)
    (s σ : Nat → Bool) (κ : Nat → Nat) (E : Nat) : Prop where
  H_PINS : D.pins c = [xp, cp]
  H_CEL : CelG G2 (pv2 xp.P (gate b cp.P s)) D.rst (D.O c) (D.qp c) (D.lo c) (D.hi c)
    (D.fl c) (D.fh c)
  H_PWR : ∀ t, t < D.hi c → D.O c t = false
  H_TIMES : ∀ j, L c j → D.τ c j =
    nt (D.O c) (D.lo c) (D.hi c) (max (gE D.τ xp j) (gc κ (gE D.τ cp) j)) (Vph j)
  H_CNT : ∀ j, L c j ↔ L xp.drv j ∧ L cp.drv (sN κ j)
  H_DOWNC : ∀ j, L cp.drv (j + 1) → L cp.drv j
  H_INCC : ∀ j, L cp.drv (j + 1) → gE D.τ cp j < gE D.τ cp (j + 1)
  H_SEL_STABLE : ∀ n t, L cp.drv (2 * n) → gE D.τ cp (2 * n) ≤ t →
    (L cp.drv (2 * n + 1) → t < gE D.τ cp (2 * n + 1)) → s t = σ n
  H_KAPPA : ∀ m, κ m < κ (m + 1)
  H_KAPPA_B : ∀ m, σ (κ m) = b
  H_KAPPA_ALL : ∀ n, σ n = b → ∃ m, κ m = n
  H_RST_EARLY : ∀ j, L c j → D.R ≤ max (gE D.τ xp j) (gc κ (gE D.τ cp) j)
  H_SND : ∀ j, L c j → (L xp.drv (j + 1) → D.τ c j + E ≤ gE D.τ xp (j + 1)) ∧
    (L cp.drv (sN κ (j + 1)) → D.τ c j + E ≤ gc κ (gE D.τ cp) (j + 1))
  H_RST_LONG : D.hi c + D.fh c ≤ D.R
  H_LAT : D.hi c + D.fh c ≤ D.lo c + E

theorem fmuxj_spec_cell {D : GD ι} {L : ι → Nat → Prop} (NW : FNetW D L) {c : ι}
    {xp cp : GPin ι} {b : Bool} {s σ : Nat → Bool} {κ : Nat → Nat} {E : Nat}
    (S : FMuxJSpec D L c xp cp b s σ κ E) : FCellOK D L c := by
  intro T hA
  refine FiniteNet.gphT_congr (c' := fe (D.O c) (D.lo c) (D.hi c)
      (fun j => max (gE D.τ xp j) (gc κ (gE D.τ cp) j))) (fun j hj => S.H_TIMES j hj) ?_
  exact tmuxj S.H_CEL NW.H_RST S.H_RST_LONG S.H_LAT S.H_PWR S.H_DOWNC S.H_INCC S.H_SEL_STABLE
    S.H_KAPPA S.H_KAPPA_B S.H_KAPPA_ALL (fun _ => rfl) S.H_CNT S.H_RST_EARLY
    (fun j hj => by rw [← S.H_TIMES j hj]; exact S.H_SND j hj)
    (hA xp (by rw [S.H_PINS]; simp)) (hA cp (by rw [S.H_PINS]; simp))

end Formal.Cells.AssumeGuaranteeMuxNFin
