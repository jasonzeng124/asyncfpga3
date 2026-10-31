import Formal.Cells.AssumeGuaranteeMuxNFin
import Formal.Cells.FiniteNetWit

/-!
# Probe Bmn (shard B): non-vacuity of the truncated muxn / mux-acknowledge / C-tree lemmas

* `tmuxa_fin_witness`: a FINITE run of a mux acknowledge on the REAL `bd_c2` LUT (band
  `[1, 1]`, feedback 1, reset 4): input 0's token, a foreign token, input 0's second token,
  then quiet forever. Every hypothesis of `tmuxa` holds (`H_ZFALL` non-vacuously, for the
  second token), the node is clean at every `T`, it holds low through the foreign `z_ack`
  pulse, and it is constant low after `t = 27`.
* `tdec_witness`: `tdec` on `AssumeGuaranteeMuxN.Wit`'s 3-way decode run, edge sets `True`.
* `ftree5_witness`, `ftree6_witness`: `AssumeGuaranteeMuxNTree.Wit`'s tree networks with
  every edge set `True` meet `FTree5` / `FTree6` (infinite runs only).
-/

namespace Formal.Cells.AssumeGuaranteeMuxNFin.Wit
open Formal.Cells
open Formal.Cells.FiniteNet
open Formal.Cells.FiniteRuns (fe)
open Formal.Cells.FiniteRunsWit (sortedB cL cnt_tail)
open Formal.Cells.FiniteNetWit (cL_gph)
open Formal.Net.CapNet.Wit (cntLt bv)
open Formal.Cells.AssumeGuaranteeEnds (GPin gE sN GC2 GC4 cmax)
open Formal.Cells.AssumeGuaranteeEndsNet (GD)
open Formal.Cells.AssumeGuaranteeMuxNTree (rp5 ip4 rp6 ip2 CelNoSnd)
open Formal.Cells.WinFifo (Win)
open Formal.Cells.WinFifoCausal (NoRevertI nt noRevertI_shift)
open Formal.Cells.PipeTimed (Vph)
open Formal.Cells.PipeTimed.Wit (rstW)
open Formal.Cells.LutFbBridge2 (CelG gc G2 pv2)
open Formal.Net.Ops.Gen (cel2)

/-! ## 1. A finite run of the mux acknowledge -/

def AL : List Nat := [4, 8, 20, 24]
def ZL : List Nat := [6, 10, 14, 18, 22, 26]
def OL : List Nat := [7, 11, 23, 27]
def aF : Nat → Bool := cL AL
def zF : Nat → Bool := cL ZL
def OF : Nat → Bool := cL OL
def ρF (j : Nat) : Nat := AL.getD j 1
def ζF (j : Nat) : Nat := ZL.getD j 1
def κF (m : Nat) : Nat := 2 * m
def LaF (j : Nat) : Prop := j < AL.length
def LzF (j : Nat) : Prop := j < ZL.length
def LnF (j : Nat) : Prop := j < 4

theorem cL_tail (L : List Nat) (N t : Nat) (h : L.all (fun e => decide (e < N)) = true)
    (ht : N ≤ t) : cL L t = cL L N := by
  unfold cL bv; rw [cnt_tail L N (t + 1) h (by omega), cnt_tail L N (N + 1) h (by omega)]

theorem stepF_small : ∀ t, t < 40 → 1 ≤ t →
    OF t = (!rstW (t - 1) && cel2 (aF (t - 1)) (zF (t - 1)) (OF (t - 1 - 1))) := by decide

theorem stepF : ∀ t, 1 ≤ t →
    OF t = (!rstW (t - 1) && cel2 (aF (t - 1)) (zF (t - 1)) (OF (t - 1 - 1))) := by
  intro t ht
  by_cases h : t < 40
  · exact stepF_small t h ht
  · have r : rstW (t - 1) = false := by unfold rstW; simp; omega
    unfold OF aF zF
    rw [cL_tail OL 30 t (by decide) (by omega), cL_tail AL 30 (t - 1) (by decide) (by omega),
      cL_tail ZL 30 (t - 1) (by decide) (by omega), cL_tail OL 30 (t - 1 - 1) (by decide) (by omega),
      r]
    decide

theorem gcF : ∀ j, j < 4 → gc κF ζF j = [6, 10, 22, 26].getD j 1 := by decide

/-- **Non-vacuity of `tmuxa` on a FINITE run** (REAL `bd_c2` via `ua_cel`'s model, band
`[1, 1]`, feedback 1, reset 4, `E = 1`): `j` (input 0's join) pulses for tokens 0 and 2 of
`z_ack`, which also carries a foreign token 1 (`t ∈ [14, 18)`); every hypothesis of `tmuxa`
holds, the node is clean at every `T` with 4 edges, stays low through the foreign pulse
(`OF 16 = false`), and is low forever after `27`. -/
theorem tmuxa_fin_witness :
    CelG G2 (pv2 aF zF) rstW OF (fun t => OF (t - 1)) 1 1 1 1 ∧
    (∀ m, 0 < κF m → LaF (2 * m) → LzF (2 * κF m - 1) ∧ ζF (2 * κF m - 1) ≤ ρF (2 * m)) ∧
    (∃ m, 0 < κF m ∧ LaF (2 * m)) ∧
    (∀ T, GPhT OF (fe OF 1 1 (fun j => max (ρF j) (gc κF ζF j))) LnF T) ∧
    (zF 15 = true ∧ aF 15 = false ∧ OF 16 = false) ∧ (∀ t, 27 ≤ t → OF t = false) := by
  have hW : Win 1 1 (fun t => G2 (pv2 aF zF t) ((fun t => OF (t - 1)) t) (rstW t)) OF :=
    fun t ht => ⟨t - 1, by omega, by omega, by rw [stepF t ht]; rfl⟩
  have hN : NoRevertI 1 1 (fun t => G2 (pv2 aF zF t) ((fun t => OF (t - 1)) t) (rstW t)) OF :=
    noRevertI_shift (fun t ht => by rw [stepF t ht]; rfl)
  have C : CelG G2 (pv2 aF zF) rstW OF (fun t => OF (t - 1)) 1 1 1 1 :=
    ⟨hW, hN, fun t ht => ⟨t - 1, by omega, by omega, rfl⟩, Nat.le_refl 1⟩
  have hzf : ∀ m, 0 < κF m → LaF (2 * m) → LzF (2 * κF m - 1) ∧ ζF (2 * κF m - 1) ≤ ρF (2 * m) := by
    have key : ∀ m, m < 2 → 0 < κF m → LzF (2 * κF m - 1) ∧ ζF (2 * κF m - 1) ≤ ρF (2 * m) := by
      unfold LzF; decide
    intro m h1 h2; unfold LaF AL at h2; exact key m (by simp at h2; omega) h1
  have hsz : ∀ j, j < 6 → j + 1 < 6 → ζF j < ζF (j + 1) := by decide
  have hsnj : ∀ j, j < 3 → nt OF 1 1 (max (ρF j) (gc κF ζF j)) (Vph j) + 1 ≤ ρF (j + 1) := by
    decide
  have hsnz : ∀ j, j < 4 → sN κF j + 1 < 6 →
      nt OF 1 1 (max (ρF j) (gc κF ζF j)) (Vph j) + 1 ≤ ζF (sN κF j + 1) := by decide
  have hcr : ∀ j, j < 4 → 4 ≤ max (ρF j) (gc κF ζF j) := by decide
  have hT : ∀ T, GPhT OF (fe OF 1 1 (fun j => max (ρF j) (gc κF ζF j))) LnF (T + 1) := fun T =>
    tmuxa (E := 1) C (fun _ => rfl) (by decide) (by decide)
      (fun t h => by have : t = 0 := by omega
                     subst this; decide)
      (fun j h => by unfold LzF at h ⊢; omega)
      (fun j h => hsz j (by unfold LzF ZL at h; simp at h; omega) (by unfold LzF ZL at h; simpa using h))
      (fun j => by unfold LnF LaF LzF AL ZL sN κF; simp; omega)
      (fun j h => hcr j h)
      (fun j h1 h2 => hsnj j (by unfold LaF AL at h2; simp at h2; omega))
      (fun j h1 h2 => hsnz j h1 (by unfold LzF ZL at h2; simpa using h2))
      hzf (cL_gph (by decide) T) (cL_gph (by decide) T)
  refine ⟨C, hzf, ⟨1, by decide, by unfold LaF AL; decide⟩, fun T => ?_, by decide, fun t ht => ?_⟩
  · exact gphT_mono (hT T) (by omega)
  · unfold OF
    by_cases h : t = 27
    · subst h; decide
    · rw [cL_tail OL 28 t (by decide) (by omega)]; decide

/-! ## 2. The decode, edge sets `True` -/

open Formal.Cells.AssumeGuaranteeMux.Wit (pw8 e8 pw8_segK e8_inc)
open Formal.Cells.LibGapMuxN (bit0 bit1 dec)

/-- **Non-vacuity of `tdec`** on `AssumeGuaranteeMuxN.Wit`'s 3-way decode run (REAL decode
LUT3 `8'h10`, band `[1, 1]`; every edge set `True`). -/
theorem tdec_witness : ∀ T, GPhT AssumeGuaranteeMuxN.Wit.Od
    (fe AssumeGuaranteeMuxN.Wit.Od 1 1 (gc AssumeGuaranteeMuxN.Wit.κ (e8 10))) (fun _ => True)
    (T + 1) := by
  intro T
  have hxd : ∀ t, 1 ≤ t → AssumeGuaranteeMuxN.Wit.Od t = dec 0 (AssumeGuaranteeMuxN.Wit.s0 (t - 1))
      (AssumeGuaranteeMuxN.Wit.s1 (t - 1)) (AssumeGuaranteeMuxN.Wit.cr (t - 1)) := by
    intro t ht; unfold AssumeGuaranteeMuxN.Wit.Od; simp [show t ≠ 0 by omega]
  have hS : ∀ n t, e8 10 (2 * n) ≤ t → t < e8 10 (2 * n + 1) →
      AssumeGuaranteeMuxN.Wit.s0 t = bit0 (AssumeGuaranteeMuxN.Wit.σ n) ∧
      AssumeGuaranteeMuxN.Wit.s1 t = bit1 (AssumeGuaranteeMuxN.Wit.σ n) := by
    intro n t h1 h2
    unfold e8 at h1 h2
    have : AssumeGuaranteeMuxN.Wit.sidx t = AssumeGuaranteeMuxN.Wit.σ n := by
      unfold AssumeGuaranteeMuxN.Wit.sidx AssumeGuaranteeMuxN.Wit.σ
      rw [show (t - 10) / 8 = n by omega]
    unfold AssumeGuaranteeMuxN.Wit.s0 AssumeGuaranteeMuxN.Wit.s1; rw [this]; exact ⟨rfl, rfl⟩
  have hr : GPhT AssumeGuaranteeMuxN.Wit.cr (e8 10) (fun _ => True) T :=
    gph_inf_iff.2 (AssumeGuaranteeLinks.phases_of_segK (pw8_segK 10)) T
  exact tdec 0 (by decide) (lo := 1) (hi := 1) (κ := AssumeGuaranteeMuxN.Wit.κ) (σ := AssumeGuaranteeMuxN.Wit.σ)
    (fun t ht => ⟨t - 1, by omega, by omega, hxd t ht⟩) (noRevertI_shift hxd)
    (fun t h => by unfold AssumeGuaranteeMuxN.Wit.Od; simp [show t = 0 by omega])
    (fun _ _ => trivial) (fun j _ => e8_inc 10 j) (fun n t _ h1 h2 => hS n t h1 (h2 trivial))
    (fun n => by unfold AssumeGuaranteeMuxN.Wit.σ; omega)
    (fun m => by unfold AssumeGuaranteeMuxN.Wit.κ; omega)
    (fun m => by unfold AssumeGuaranteeMuxN.Wit.σ AssumeGuaranteeMuxN.Wit.κ; omega)
    (fun n h => ⟨n / 3, by unfold AssumeGuaranteeMuxN.Wit.σ at h; unfold AssumeGuaranteeMuxN.Wit.κ; omega⟩)
    (fun j _ => by omega) hr

/-! ## 3. The trees, edge sets `True` -/

open Formal.Cells.AssumeGuaranteeMuxNTree.Wit (w5 pin5 lv5 inner5 root5 tree5_witness cm_inner5
  cm_root5 w6 pa6 pb6 lv6 innerA6 innerB6 root6 tree6_witness cm_a6 cm_b6 cm_r6 f16)

variable {ι : Type}

/-- A segment-form node is a truncated one with every edge set `True`, given its reset bound
at every edge. -/
theorem toF {n : Nat} {G : (Fin n → Bool) → Bool → Bool → Bool} {D : GD ι} {c : ι}
    {pv : Fin n → GPin ι} (N : CelNoSnd G D c pv)
    (hR : ∀ j, D.R ≤ cmax (fun i => gE D.τ (pv i)) j) :
    FCelNoSnd G D (fun _ _ => True) c pv :=
  ⟨N.H_PINS, N.H_LAW, N.H_CEL, N.H_PWR, N.H_TIMES, fun _ => ⟨fun _ _ => trivial, fun _ => trivial⟩,
    fun j _ => hR j, N.H_RST_LONG⟩

/-- **Non-vacuity of `ftree5_cel`** (infinite run: the segment witness network, edge sets
`True`). -/
theorem ftree5_witness : FTree5 w5 (fun _ _ => True) 6 5 pin5 lv5 2 :=
  { root := toF root5 (fun j => by rw [cm_root5]; show 4 ≤ _; unfold f16; omega)
    inner := toF inner5 (fun j => by rw [cm_inner5]; show 4 ≤ _; unfold f16; omega)
    H_DRV := tree5_witness.1.H_DRV
    H_WIRE := tree5_witness.1.H_WIRE
    H_ACK := fun i j _ => tree5_witness.1.H_ACK i j
    H_LAT_R := tree5_witness.1.H_LAT_R
    H_LAT_N := tree5_witness.1.H_LAT_N }

/-- **Non-vacuity of `ftree6_cel`** (infinite run, edge sets `True`). -/
theorem ftree6_witness : FTree6 w6 (fun _ _ => True) 8 6 7 pa6 pb6 lv6 2 :=
  { root := toF root6 (fun j => by rw [cm_r6]; show 4 ≤ _; unfold f16; omega)
    innerA := toF innerA6 (fun j => by rw [cm_a6]; show 4 ≤ _; unfold f16; omega)
    innerB := toF innerB6 (fun j => by rw [cm_b6]; show 4 ≤ _; unfold f16; omega)
    H_DRVA := tree6_witness.H_DRVA
    H_DRVB := tree6_witness.H_DRVB
    H_WIREA := tree6_witness.H_WIREA
    H_WIREB := tree6_witness.H_WIREB
    H_ACK := fun i j _ => tree6_witness.H_ACK i j
    H_LAT_R := tree6_witness.H_LAT_R
    H_LAT_A := tree6_witness.H_LAT_A
    H_LAT_B := tree6_witness.H_LAT_B }

/-! ## 4. One token through a FASTFALL stage, then quiet -/

def GL : List Nat := [4, 12]
def DL : List Nat := [6, 16]
def SL : List Nat := [7, 13]

theorem stepG : ∀ t, 1 ≤ t → cL SL t = Formal.Core.LutList.lutB 0x8 [cL DL (t - 1), cL GL (t - 1)] := by
  have small : ∀ t, t < 30 → 1 ≤ t →
      cL SL t = Formal.Core.LutList.lutB 0x8 [cL DL (t - 1), cL GL (t - 1)] := by decide
  intro t ht
  by_cases h : t < 30
  · exact small t h ht
  · rw [cL_tail SL 20 t (by decide) (by omega), cL_tail DL 20 (t - 1) (by decide) (by omega),
      cL_tail GL 20 (t - 1) (by decide) (by omega)]
    decide

/-- **Non-vacuity of `tand` on a FINITE run** (REAL LUT2 `4'h8`, band `[1, 1]`): the gate
`|j` high on `[4, 12)`, the data pin `s[i]` high on `[6, 16)`, one token, then quiet. Every
hypothesis holds; the stage is clean at every `T`; it FALLS at `13`, before its data pin
falls (`16`): the case the segment rule cannot carry (`gstage_not_causal`). -/
theorem tand_fin_witness :
    (∀ T, GPhT (cL SL) (fe (cL SL) 1 1 (xe (fun j => DL.getD j 1) (fun j => GL.getD j 1)))
      (fun j => j < DL.length) T) ∧
    fe (cL SL) 1 1 (xe (fun j => DL.getD j 1) (fun j => GL.getD j 1)) 1 = 13 ∧
    DL.getD 1 1 = 16 ∧ cL SL 13 = false ∧ cL DL 13 = true := by
  have hW : Win 1 1 (fun t => Formal.Core.LutList.lutB 0x8 [cL DL t, cL GL t]) (cL SL) :=
    fun t ht => ⟨t - 1, by omega, by omega, stepG t ht⟩
  have hN : NoRevertI 1 1 (fun t => Formal.Core.LutList.lutB 0x8 [cL DL t, cL GL t]) (cL SL) :=
    noRevertI_shift stepG
  refine ⟨fun T => gphT_mono (tand (T := T) hW hN (fun t h => by
      have : t = 0 := by omega
      subst this; decide) (fun j => by simp [DL, GL])
      (fun j h => by
        have : j = 0 := by simp [DL] at h; omega
        subst this; decide)
      (fun j _ => by omega) (cL_gph (by decide) T) (cL_gph (by decide) T)) (by omega),
    by decide, by decide, by decide, by decide⟩

end Formal.Cells.AssumeGuaranteeMuxNFin.Wit
