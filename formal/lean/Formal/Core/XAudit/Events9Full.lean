import Formal.Core.XAudit.Events9Setup
import Formal.Core.XAudit.Events9ParBeh

/-!
# Formal.Core.XAudit.Events9Full — `design_verdict9_full`: the corrected arbiter core, the
junction select rows and the setup rows under ONE realisation

Probe E9Setup (shard A). Notes: `formal/notes/A-e9setup.md`.

`Events9Par.design_verdict9par` (corrected virtual arbiter core HARB7', parallel-pair log
`LnP`, HRst) and `Events9SelJ.design_verdict9_selJ` (select literals, junction-anchored causal
hold rows, old `runLog`, `HARB7`) were separate statements about separate realisations. This
file states them for one realisation and one log:

* `verdict9par_upto`: `Events9Prefix.verdict9_upto` for the log `LnP` (prefix form, `RstSync`).
* `design_behPG`: `Events9Par.design_behP` (common-reset realisation of the `rs` nodes) also
  exposing every REAL node's select value and copy warps (`sv = svOf`, `G = tau full (· + 1)`),
  under the checked side condition `hrsv` (only virtual nodes are in a reset class; xevents9par
  puts `rc` only on virtual non-merge nodes).
* `Osel`: per literal, `Events9Setup.Ofirst` (the request wire's rise) where the setup row is
  certified (`cs = true`), a free `Ou` where it is not.
* **`design_verdict9_full`**: the checks of `design_verdict9par` (log `LnP` accepted, items) plus,
  per real select literal, `entOK`, `treeOK`, `reqOK` (`ReqLineT` lines of the SAME accepted
  log), per copy `holdBandS` + `jrowOK` (junction log over the same `J`), and the setup row
  `suOK` where `cs = true`. Trace hypotheses: SatPin, constants, reset, HARB7', HRst, SelOK at
  the virtual pins (part of the arbiter hypothesis), SelPart, C's H_BUNDLE (`Held`) of each mapped
  channel, H_SEL_FN (the select sequence is the bus read at `Osel`), the residual obligations
  of uncertified items and, for `cs = false` literals only, H_SEL_O / setup at `Ou`.
  Conclusion: SelOK of the realisation and the count/wire link of every real LUT wire at every
  time.

NOT covered: H_BUNDLE (C's hypothesis; its channel NAME map is untrusted `mkmap.py`), HARB7'
and HRst themselves, H_SEL_FN, the parsers. The setup rows credit the bus nothing before its
request wire rises (H_BUNDLE says nothing earlier), so a failing setup row is a statement about
that contract, not necessarily about the circuit (notes §3).
-/

namespace Formal.Core.XAudit.Events9Full

open Formal.Core
open Formal.Core.XAudit
open Formal.Core.TraceDiscrete (Sig Warp Mono)
open Formal.Core.XAudit.Events (ph)
open Formal.Core.XAudit.Events2Pin (SatPin)
open Formal.Core.XAudit.Events5
open Formal.Core.XAudit.Events6
open Formal.Core.XAudit.Events7
open Formal.Core.XAudit.Events8
open Formal.Core.XAudit.Events9
open Formal.Core.XAudit.Events8Bridge
open Formal.Core.XAudit.Events9Sel
open Formal.Core.XAudit.Events9SelC
open Formal.Core.XAudit.Events9SelHold
open Formal.Core.XAudit.Events9SelSplit
open Formal.Core.XAudit.Events9Prefix
open Formal.Core.XAudit.Events9PrefixSel
open Formal.Core.XAudit.Events9SelL
open Formal.Core.XAudit.Events9SelJ
open Formal.Core.XAudit.Events9Arb
open Formal.Core.XAudit.Events9Par
open Formal.Core.XAudit.Events9Setup

/-! ## 1. The prefix verdict for the log `LnP` -/

section
variable {N : Nat} {net : Net4 N} {b : Bands4 net} {sel : Nat → Nat → Bool} (x : Beh7 net b sel)

/-- **`verdict9par_upto`**: `Events9Prefix.verdict9_upto` with the log `LnP` (accepted by
`runLogP`, sound under `RstSync`). -/
theorem verdict9par_upto (hOK : net.OK7) {parts : List (List Nat)} (hp : SelPart sel parts) {rs : Nat → Nat}
    (hrs : RstSync x rs) {log : List LnP} {J : Array Jd} (hJ : runLogP net b rs parts log = some J)
    (back line : (j : Fin N) → Fin (net.ar j) → Nat) (xS xw : Fin N → Nat) (xa : Fin N → List Arm)
    (hl : List HLn9) (gd : (j : Fin N) → Fin (net.ar j) → GD)
    (cp : (j : Fin N) → Fin (net.ar j) → Bool) (cxm : Fin N → Bool) (cl : (j : Fin N) → Fin (net.ar j) → Bool)
    (cg : (j : Fin N) → Fin (net.ar j) → Bool)
    (hcp : ∀ j p, cp j p = true → backOK7 net b J j p (back j p) = true)
    (hcx : ∀ m, cxm m = true → exclOK7 net b parts J m (xS m) (xa m) (xw m) = true)
    (hcl : ∀ j p, cl j p = true → lineOK7 net b J j p (line j p) = true)
    (hcg : ∀ j p, cg j p = true → guardOK8 net b parts J (hl.map (san J)) j p (gd j p) = true)
    (hgc : ∀ j p s, net.pk j p = PK.guard → x.gc j p s = gcnt net sel j p (x.cm j p s))
    (t0 : Nat)
    (rB : ∀ j p s, s < t0 → net.mg j = false → net.pk j p ≠ PK.guard → cp j p = false →
      x.P j p s ≤ x.M (x.Q j s) j + 1)
    (rX : ∀ m s, s < t0 → net.mg m = true → cxm m = false → fodd (net.ar m) (fun p => x.P m p s) ≤ 1)
    (rL : ∀ j p s, s < t0 → net.pk j p = PK.multi → cl j p = false → ContigF (net.nc j p) (x.cm j p s))
    (rG : ∀ j p, net.pk j p = PK.guard → cg j p = false → GuardPinB x t0 j p)
    (hsel : ∀ s, s < t0 → SelAt x s) : Link x t0 := by
  have hA := runLogP_sound x hOK hp hrs hJ
  have hH := hdsub_san x hOK hp hA hl
  refine safe8_upto x hOK t0 hsel ?_ ?_ ?_ cg hgc ?_ rG
  · intro j p s hs hk
    cases hc : cl j p
    · exact rL j p s hs hk hc
    · exact lineOK7_sound x hA j p _ (hcl j p hc) s
  · intro j p s hs hm hk
    cases hc : cp j p
    · exact rB j p s hs hm hk hc
    · exact backOK7_sound x hOK hA j p hk _ (hcp j p hc) s
  · intro m s hs hm
    cases hc : cxm m
    · exact rX m s hs hm hc
    · exact exclOK7_sound x hOK hp hA m hm _ _ _ (hcx m hc) s
  · intro j p hk hc
    have h := guardOK8_sound x hOK hA hH j p (gd j p) (fun s => hgc j p s hk) (hcg j p hc)
    exact ⟨h.1, guardCntB_of x h.2 t0⟩

end

/-! ## 2. One realisation: common resets, real select values and copy warps exposed -/

section
variable {N : Nat} {d : Design} {net : Net4 N} {b : Bands4 net} {rn : Fin N → RNode} {rank : Fin N → Nat}
  {rw fuel : Nat} {x : Fin d.n → Sig} (hsat : SatPin d plG x)
  (h0 : ∀ t, x (d.wire 0) t = false) (h1 : ∀ t, x (d.wire 1) t = true)
  {T : Nat} (hT : 1 ≤ T) (hrst : ∀ t, x (d.wire rw) t = decide (t < T))
  {cv : Fin N → Sig} (hr : Recog6 d net b rn rank rw fuel) (hOK : net.OK7) (harb : HARB7 net b rn x cv)
  {rs : Nat → Nat} (hR : HRst net b rn x cv rs)

include hsat h0 h1 hT hrst hr hOK harb hR

/-- **`design_behPG`**: `Events9Par.design_behP`, also exposing every real node's select value
and copy warps, when only virtual nodes are in a reset class (`hrsv`, checked). -/
theorem design_behPG (hrsv : ∀ j : Fin N, rs j.val ≠ 0 → (rn j).virt = true) (sel : Nat → Nat → Bool) :
    ∃ bh : Beh7 net b sel, (∀ j t, bh.c j t = ccOf rn x cv j t) ∧
      (∀ j p s, bh.gc j p s = gcnt net sel j p (bh.cm j p s)) ∧
      (∀ j, (rn j).virt = false → ∀ t, bh.c j t = x (d.wire (gt d (rn j).lut).out) t) ∧
      (∀ j, (rn j).virt = false → ∀ p s, bh.sv j p s = svOf (rn := rn) hsat j p s) ∧
      (∀ j, (rn j).virt = false → ∀ p i s, bh.G j p i s = tau hsat (full net rn j p i.val) (s + 1)) ∧
      RstSync bh rs := by
  have mg0 : ∀ j, net.mg j = true → ccOf rn x cv j 0 = false := fun j hm => by
    rw [init0_7 hsat h0 h1 hT hrst hr hOK harb j]; exact ((hOK j ⟨0, net.ar_pos j⟩).2.2.2.1 hm).1
  have hrs0 : ∀ j : Fin N, (rn j).virt = false → ¬ (rs j.val ≠ 0) := fun j hv hne => by
    have := hrsv j hne; rw [hv] at this; exact absurd this (by decide)
  refine ⟨beh8 sel (ndAllP hsat h0 h1 hT hrst hr hOK harb hR) mg0, fun j t => rfl,
    beh8_gc sel (ndAllP hsat h0 h1 hT hrst hr hOK harb hR) mg0, fun j hv t => ?_, fun j hv p s => ?_,
    fun j hv p i s => ?_, ?_⟩
  · show ccOf rn x cv j t = _
    unfold ccOf; rw [hv, (hr.2 j hv).2.1]; rfl
  · show (ndAllP hsat h0 h1 hT hrst hr hOK harb hR j).sv p s = _
    unfold ndAllP
    rw [dif_neg (hrs0 j hv)]
    unfold ndAll7
    simp only [hv, Bool.false_eq_true, ↓reduceDIte]
    rfl
  · show (ndAllP hsat h0 h1 hT hrst hr hOK harb hR j).G p i s = _
    unfold ndAllP
    rw [dif_neg (hrs0 j hv)]
    unfold ndAll7
    simp only [hv, Bool.false_eq_true, ↓reduceDIte]
    rfl
  · intro z y hz hy s
    show (ndAllP hsat h0 h1 hT hrst hr hOK harb hR z).r s = (ndAllP hsat h0 h1 hT hrst hr hOK harb hR y).r s
    unfold ndAllP
    have hz' : rs z.val ≠ 0 := by rw [hz]; exact hy
    rw [dif_pos hz', dif_pos hy, (Classical.choice (hR.choose_spec z hz')).property,
      (Classical.choice (hR.choose_spec y hy)).property, hz]

end

/-! ## 3. The combined verdict -/

/-- The bus-open time of a literal: the request wire's rise (`Ofirst`) where the setup row is
certified (`cs = true`), the free `Ou` otherwise. -/
noncomputable def Osel {N : Nat} {d : Design} {net : Net4 N} {b : Bands4 net} {sel : Nat → Nat → Bool}
    {x : Fin d.n → Sig} (bh : Beh7 net b sel) (hsat : SatPin d plG x)
    (tq : (j : Fin N) → Fin (net.ar j) → Nat → AT) (cs : (j : Fin N) → Fin (net.ar j) → Nat → Bool)
    (Ou : (j : Fin N) → Fin (net.ar j) → Nat → Nat → Nat) (j : Fin N) (p : Fin (net.ar j)) (i k : Nat) : Nat :=
  if cs j p i then Ofirst bh hsat (AT.leaves (tq j p i)) k else Ou j p i k

section
variable {N : Nat} {d : Design} {net : Net4 N} {b : Bands4 net} {rn : Fin N → RNode} {rank : Fin N → Nat}
  {rw fuel : Nat} {x : Fin d.n → Sig} {cv : Fin N → Sig}

/-- **`design_verdict9_full`** (what `xevents9par` + `xfull` CLEAN on one certificate means).
Checked (decidable, evaluated on the parsed netlist and certificate): `Recog6`, `Net4.OK7`, the
log `LnP` accepted by `runLogP` with reset classes `rs`, `hrsv`, the item checks of
`design_verdict9par`; per real select literal `entOK`, `treeOK`, `reqOK` (lines of the same
`J`); per copy `holdBandS` + `jrowOK`; the setup row `suOK` for each literal with `cs = true`.
Assumed: SatPin, constant wires, reset, HARB7' (corrected virtual arbiter core), HRst; then for
every select sequence there is ONE `Beh7` realising `x` such that under SelPart, SelOK at the
virtual pins, C's H_BUNDLE of each mapped channel, H_SEL_FN (`sel` is the bus read at `Osel`),
for the `cs = false` literals only H_SEL_O / the setup inequality at `Ou`, and the residual
obligations of uncertified items: SelOK holds and every real LUT wire is its reset value flipped
`M t j` times at every time. -/
theorem design_verdict9_full (hr : Recog6 d net b rn rank rw fuel) (hOK : net.OK7)
    {parts : List (List Nat)} {rs : Nat → Nat} {log : List LnP} {J : Array Jd}
    (hJ : runLogP net b rs parts log = some J)
    (hrsv : ∀ j : Fin N, rs j.val ≠ 0 → (rn j).virt = true)
    (back line : (j : Fin N) → Fin (net.ar j) → Nat) (xS xw : Fin N → Nat) (xa : Fin N → List Arm)
    (hl : List HLn9) (gd : (j : Fin N) → Fin (net.ar j) → GD)
    (cp : (j : Fin N) → Fin (net.ar j) → Bool) (cxm : Fin N → Bool) (cl : (j : Fin N) → Fin (net.ar j) → Bool)
    (cg : (j : Fin N) → Fin (net.ar j) → Bool)
    (hcp : ∀ j p, cp j p = true → backOK7 net b J j p (back j p) = true)
    (hcx : ∀ m, cxm m = true → exclOK7 net b parts J m (xS m) (xa m) (xw m) = true)
    (hcl : ∀ j p, cl j p = true → lineOK7 net b J j p (line j p) = true)
    (hcg : ∀ j p, cg j p = true → guardOK8 net b parts J (hl.map (san J)) j p (gd j p) = true)
    (m : (j : Fin N) → Fin (net.ar j) → Nat → SelEnt) (cut : (j : Fin N) → Fin (net.ar j) → Nat → Nat)
    (Dl : (j : Fin N) → Fin (net.ar j) → Nat → Nat → Nat)
    (ta tq : (j : Fin N) → Fin (net.ar j) → Nat → AT) (na : (j : Fin N) → Fin (net.ar j) → Nat → Fin N)
    (κa : (j : Fin N) → Fin (net.ar j) → Nat → Path)
    (wq : (j : Fin N) → Fin (net.ar j) → Nat → List Nat)
    (jl : (j : Fin N) → Fin (net.ar j) → Nat → List JLn) (jw : (j : Fin N) → Fin (net.ar j) → Nat → Nat → Nat)
    (scut : (j : Fin N) → Fin (net.ar j) → Nat → Nat → Nat) (su : (j : Fin N) → Fin (net.ar j) → Nat → SU)
    (cs : (j : Fin N) → Fin (net.ar j) → Nat → Bool)
    (hm : ∀ j p (sb : Nat × Bool), (rn j).virt = false → net.pk j p = PK.filt → sb ∈ selLits net rn j p →
      entOK d net rn j p sb.1 (m j p sb.1) = true ∧
      treeOK (d := d) (net := net) (rn := rn) (m j p sb.1) (ta j p sb.1) (tq j p sb.1) (na j p sb.1) (κa j p sb.1) = true ∧
      reqOK d J (na j p sb.1).val (κa j p sb.1) (AT.leaves (tq j p sb.1)) (wq j p sb.1) = true)
    (hrow : ∀ j p (sb : Nat × Bool) (i : Fin (net.nc j p)), (rn j).virt = false → net.pk j p = PK.filt →
      sb ∈ selLits net rn j p →
      holdBandS d net rn j p (m j p sb.1) i.val (cut j p i.val) (Dl j p i.val sb.1) = true ∧
      jrowOK d net b rn parts J (net.src j p).val (botP d net rn j p i.val (cut j p i.val)) (jl j p i.val)
        (jw j p i.val sb.1) (na j p sb.1).val (plo d (κa j p sb.1)) (Dl j p i.val sb.1) = true)
    (hsu : ∀ j p (sb : Nat × Bool), (rn j).virt = false → net.pk j p = PK.filt → sb ∈ selLits net rn j p →
      cs j p sb.1 = true →
      suOK d net rn j p (m j p sb.1) (AT.leaves (tq j p sb.1)) (scut j p sb.1) (su j p sb.1) = true)
    (hsat : SatPin d plG x) (h0 : ∀ t, x (d.wire 0) t = false) (h1 : ∀ t, x (d.wire 1) t = true)
    {T : Nat} (hT : 1 ≤ T) (hrst : ∀ t, x (d.wire rw) t = decide (t < T)) (harb : HARB7' net b rn x cv)
    (hR : HRst net b rn x cv rs) (sel : Nat → Nat → Bool) :
    ∃ bh : Beh7 net b sel, (∀ j t, bh.c j t = ccOf rn x cv j t) ∧
      (∀ j p s, bh.gc j p s = gcnt net sel j p (bh.cm j p s)) ∧
      (SelPart sel parts →
        (∀ j p s (i : Fin (net.nc j p)), (rn j).virt = true → net.pk j p = PK.filt →
          bh.M (bh.G j p i s) (net.src j p) % 2 = 1 →
          bh.sv j p s = sel (net.grp j p) (bh.M (bh.G j p i s) (net.src j p) / 2)) →
        ∀ (Ou : (j : Fin N) → Fin (net.ar j) → Nat → Nat → Nat),
        -- C's H_BUNDLE of each mapped channel
        (∀ j p (sb : Nat × Bool), (rn j).virt = false → net.pk j p = PK.filt → sb ∈ selLits net rn j p →
          Formal.Net.Ops.Held ((m j p sb.1).ch x)) →
        -- residual H_SEL_O, only for literals without a setup row
        (∀ j p (sb : Nat × Bool) k u, (rn j).virt = false → net.pk j p = PK.filt → sb ∈ selLits net rn j p →
          cs j p sb.1 = false →
          bh.M u (net.src j p) = 2 * k + 1 → ∀ l ∈ AT.leaves (tq j p sb.1),
          2 * k + 1 ≤ Mn bh (tau hsat l.2 (Ou j p sb.1 k)) l.1) →
        -- residual setup, only for literals without a setup row
        (∀ j p (sb : Nat × Bool) (i : Fin (net.nc j p)) k r, (rn j).virt = false → net.pk j p = PK.filt →
          sb ∈ selLits net rn j p → cs j p sb.1 = false →
          bh.M (tau hsat (botP d net rn j p i.val (scut j p sb.1 i.val)) r) (net.src j p) = 2 * k + 1 →
          Ou j p sb.1 k + (gt d (m j p sb.1).rg).hi + selHi d net rn j p ≤
            r + (plo d (topP d net rn j p i.val (scut j p sb.1 i.val)) - 1)) →
        -- H_SEL_FN: the select sequence is the bus read at the open time
        (∀ j p k, (rn j).virt = false → net.pk j p = PK.filt →
          sel (net.grp j p) k = selFn (selLits net rn j p)
            (fun i => x (d.wire (m j p i).dw) (Osel bh hsat tq cs Ou j p i k))) →
        (∀ j p s, net.mg j = false → net.pk j p ≠ PK.guard → cp j p = false → bh.P j p s ≤ bh.M (bh.Q j s) j + 1) →
        (∀ m s, net.mg m = true → cxm m = false → fodd (net.ar m) (fun p => bh.P m p s) ≤ 1) →
        (∀ j p s, net.pk j p = PK.multi → cl j p = false → ContigF (net.nc j p) (bh.cm j p s)) →
        (∀ j p, net.pk j p = PK.guard → cg j p = false → GuardPin bh j p) →
        bh.SelOK ∧ ∀ t j, (rn j).virt = false →
          x (d.wire (gt d (rn j).lut).out) t = ph (net.v j) (bh.M t j)) := by
  obtain ⟨bh, hc, hgc, hreal, hsv, hG, hsync⟩ := design_behPG hsat h0 h1 hT hrst hr hOK harb.1 hR hrsv sel
  refine ⟨bh, hc, hgc, fun hp hvirt Ou hheld hOr hSr hsel rB rX rL rG => ?_⟩
  have hA := runLogP_sound bh hOK hp hsync hJ
  let O := Osel bh hsat tq cs Ou
  -- H_SEL_O at O, for every literal
  have hO : ∀ j p (sb : Nat × Bool) k u, (rn j).virt = false → net.pk j p = PK.filt → sb ∈ selLits net rn j p →
      bh.M u (net.src j p) = 2 * k + 1 → ∀ l ∈ AT.leaves (tq j p sb.1),
      2 * k + 1 ≤ Mn bh (tau hsat l.2 (O j p sb.1 k)) l.1 := by
    intro j p sb k u hv hk hs hu l hl
    show 2 * k + 1 ≤ Mn bh (tau hsat l.2 (Osel bh hsat tq cs Ou j p sb.1 k)) l.1
    unfold Osel
    cases hcs : cs j p sb.1
    · simp only [Bool.false_eq_true, ite_false]
      exact hOr j p sb k u hv hk hs hcs hu l hl
    · simp only [ite_true]
      obtain ⟨_, hTr, _⟩ := hm j p sb hv hk hs
      obtain ⟨_, _, _, _, _, hlq⟩ := treeOK_spec hTr
      exact (su_sound hsat hr bh hG j hv p (m j p sb.1) _ (fun l hl => (hlq l hl).2) (scut j p sb.1)
        (su j p sb.1) (hsu j p sb hv hk hs hcs)).1 k u hu l hl
  -- the setup inequality at O, junction-anchored at the setup cut
  have hsetJ : ∀ j p (sb : Nat × Bool) (i : Fin (net.nc j p)) k r, (rn j).virt = false → net.pk j p = PK.filt →
      sb ∈ selLits net rn j p →
      bh.M (tau hsat (botP d net rn j p i.val (scut j p sb.1 i.val)) r) (net.src j p) = 2 * k + 1 →
      O j p sb.1 k + (gt d (m j p sb.1).rg).hi + selHi d net rn j p ≤
        r + (plo d (topP d net rn j p i.val (scut j p sb.1 i.val)) - 1) := by
    intro j p sb i k r hv hk hs hmr
    show Osel bh hsat tq cs Ou j p sb.1 k + _ + _ ≤ _
    unfold Osel
    cases hcs : cs j p sb.1
    · simp only [Bool.false_eq_true, ite_false]
      exact hSr j p sb i k r hv hk hs hcs hmr
    · simp only [ite_true]
      obtain ⟨_, hTr, _⟩ := hm j p sb hv hk hs
      obtain ⟨_, _, _, _, _, hlq⟩ := treeOK_spec hTr
      exact (su_sound hsat hr bh hG j hv p (m j p sb.1) _ (fun l hl => (hlq l hl).2) (scut j p sb.1)
        (su j p sb.1) (hsu j p sb hv hk hs hcs)).2 i k r hmr
  -- H_REQ_CNT from the ReqLineT lines
  have hRq : ∀ j p (sb : Nat × Bool) v, (rn j).virt = false → net.pk j p = PK.filt → sb ∈ selLits net rn j p →
      ∀ l ∈ AT.leaves (tq j p sb.1),
      Mn bh (tau hsat l.2 v) l.1 ≤ bh.M (tau hsat (κa j p sb.1) v) (na j p sb.1) + 1 := by
    intro j p sb v hv hk hs l hl
    obtain ⟨_, hTr, hq⟩ := hm j p sb hv hk hs
    obtain ⟨_, _, _, hκp, _, hlq⟩ := treeOK_spec hTr
    obtain ⟨w, hw⟩ := reqOK_mem d _ _ hq l hl
    exact reqCnt_of_lineT bh hA hw (tau_warp hsat _ (hlq l hl).2) (tau_warp hsat _ hκp) (Nat.le_refl _) v
  -- H_ACK_CNT from the junction rows
  have hAk : ∀ j p (sb : Nat × Bool) (i : Fin (net.nc j p)) k r σ, (rn j).virt = false →
      net.pk j p = PK.filt → sb ∈ selLits net rn j p →
      bh.M (tau hsat (botP d net rn j p i.val (cut j p i.val)) r) (net.src j p) = 2 * k + 1 →
      σ < r + Dl j p i.val sb.1 → bh.M (tau hsat (κa j p sb.1) σ) (na j p sb.1) ≤ 2 * k + 1 := by
    intro j p sb i k r σ hv hk hs hu hσ
    obtain ⟨_, hTr, _⟩ := hm j p sb hv hk hs
    obtain ⟨_, _, _, hκp, _, _⟩ := treeOK_spec hTr
    have hbot := botP_ok hr j hv p i (cut j p i.val)
    have hjr := (hrow j p sb i hv hk hs).2
    unfold jrowOK at hjr
    split at hjr
    · rename_i JJ hrun
      split at hjr
      · rename_i hjw
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hjr
        obtain ⟨⟨⟨⟨hu', hc''⟩, ha'⟩, ht'⟩, hD⟩ := hjr
        have wB := tau_warp hsat _ hbot
        have hall := runJ_sound bh (S := (net.src j p).val) wB.mono
          (fac_of_ok hsat hr bh hG _ hbot)
          (fun hid v => by
            have e := of_decide_eq_true hid
            rw [e]; exact Nat.le_refl _)
          wB.early_le hOK hp hA hrun
        obtain ⟨_, hH⟩ := hall (jw j p i.val sb.1) hjw
        rw [hu', hc''] at hH
        have h1 := hH (tau hsat (κa j p sb.1) σ)
        rw [ha', ht', Mn_fin, Mn_fin] at h1
        have wκ := tau_warp hsat _ hκp
        have h2 := wκ.le_late σ
        have h3 := bh.M_mono _ (net.src j p) _ (wB.mono (tau hsat (κa j p sb.1) σ - JJ[jw j p i.val sb.1].d) r (by omega))
        omega
      · simp at hjr
    · simp at hjr
  -- the prefix verdict
  have hpre : ∀ t0, (∀ s, s < t0 → SelAt bh s) → Link bh t0 := fun t0 hs =>
    verdict9par_upto bh hOK hp hsync hJ back line xS xw xa hl gd cp cxm cl cg hcp hcx hcl hcg
      (fun j p s _ => hgc j p s) t0 (fun j p s _ => rB j p s) (fun m s _ => rX m s)
      (fun j p s _ => rL j p s) (fun j p hk hc => guardPinB_of bh (rG j p hk hc) t0) hs
  let S0 : (j : Fin N) → Fin (net.ar j) → Nat → Nat → Nat :=
    fun j p i k => O j p i k + (gt d (m j p i).rg).hi
  let vb : (j : Fin N) → Fin (net.ar j) → Nat → Nat → Bool :=
    fun j p i k => x (d.wire (m j p i).dw) (O j p i k)
  have hstep : ∀ s, (∀ u, u < s → ∀ j : Fin N, bh.c j u = ph (net.v j) (bh.M u j)) → SelAt bh s := by
    intro s hlink
    refine selAt_setJ hsat hr bh hsv hG hvirt cut scut S0 vb
      (fun j p sb i k r hvf hk hsb h => hsetJ j p sb i k r hvf hk hsb h) hsel s ?_
    intro j p sb i k t r hts hvf hk hsb hu ht htu
    obtain ⟨hEnt, hTr, _⟩ := hm j p sb hvf hk hsb
    obtain ⟨hg, hb, hin, hout, hw⟩ := entOK_spec d net rn hEnt
    obtain ⟨hta, hlta, hnaL, hκp, htq, hlq⟩ := treeOK_spec hTr
    obtain ⟨_, hnav, hnav0⟩ := leafOK_spec net rn hnaL
    have hband := of_decide_eq_true (hrow j p sb i hvf hk hsb).1
    have hrg1 : 1 ≤ (gt d (m j p sb.1).rg).lo := (hr.1 _ (gt_mem d hg)).2.2.2.1
    have hrg2 : (gt d (m j p sb.1).rg).lo ≤ (gt d (m j p sb.1).rg).hi := (hr.1 _ (gt_mem d hg)).2.2.2.2.1
    have hS0 : S0 j p sb.1 k = O j p sb.1 k + (gt d (m j p sb.1).rg).hi := rfl
    have wκ := tau_warp hsat _ hκp
    have hwire : ∀ (n : Fin N), (rn n).virt = false → net.v n = false → ∀ τ, τ < s →
        x (d.wire (nodeW d rn n.val)) τ = ph false (bh.M τ n) := by
      intro n hv hv0 τ hτ
      rw [nodeW_fin, ← hreal n hv τ, hlink τ hτ, hv0]
    have htx : ∀ σ, O j p sb.1 k ≤ σ → σ ≤ t - (gt d (m j p sb.1).rg).lo →
        Formal.Net.Ops.inTx ((m j p sb.1).ch x) σ = true := by
      intro σ hσ1 hσ2
      have hσs : σ < s := by omega
      have hκσ : tau hsat (κa j p sb.1) σ ≤ σ := by have := wκ.le_late σ; omega
      have hAle := hAk j p sb i k r σ hvf hk hsb hu (by omega)
      unfold Formal.Net.Ops.inTx
      by_cases hA : bh.M (tau hsat (κa j p sb.1) σ) (na j p sb.1) % 2 = 1
      · have hak : x (d.wire (m j p sb.1).ak) σ = true := by
          refine at_true hsat (ta j p sb.1) _ hta σ (fun l hl => ?_)
          rw [hlta, List.mem_singleton] at hl
          subst hl
          show x (d.wire (nodeW d rn (na j p sb.1).val)) (tau hsat (κa j p sb.1) σ) = true
          rw [hwire _ hnav hnav0 _ (by omega)]
          simp [ph, hA]
        show (x (d.wire (m j p sb.1).rq) σ || x (d.wire (m j p sb.1).ak) σ) = true
        rw [hak, Bool.or_true]
      · have hrq : x (d.wire (m j p sb.1).rq) σ = true := by
          refine at_true hsat (tq j p sb.1) _ htq σ (fun l hl => ?_)
          obtain ⟨hlL, hlp⟩ := hlq l hl
          obtain ⟨hn, hlv, hlv0⟩ := leafOK_spec net rn hlL
          have wl := tau_warp hsat _ hlp
          have hlσ : tau hsat l.2 σ ≤ σ := by have := wl.le_late σ; omega
          have hlo := hO j p sb k _ hvf hk hsb hu l hl
          have hmo := Mn_mono bh l.1 (wl.mono _ _ hσ1)
          have hup := hRq j p sb σ hvf hk hsb l hl
          simp only [Mn, dif_pos hn] at hlo hmo hup
          show x (d.wire (nodeW d rn (⟨l.1, hn⟩ : Fin N).val)) _ = true
          rw [hwire ⟨l.1, hn⟩ hlv hlv0 _ (by omega)]
          have : bh.M (tau hsat l.2 σ) ⟨l.1, hn⟩ = 2 * k + 1 := by omega
          simp [ph, this, Nat.add_mod]
        show (x (d.wire (m j p sb.1).rq) σ || x (d.wire (m j p sb.1).ak) σ) = true
        rw [hrq, Bool.true_or]
    rw [← hout]
    have hmem : d.wire (m j p sb.1).dw ∈ (m j p sb.1).ws.map d.wire := List.mem_map.mpr ⟨_, hw, rfl⟩
    have hinF : ∀ σ, O j p sb.1 k ≤ σ → σ ≤ t - (gt d (m j p sb.1).rg).lo →
        x (d.wire ((gt d (m j p sb.1).rg).ins.getD 0 0)) σ = vb j p sb.1 k := by
      intro σ h1' h2'
      rw [hin]
      exact held_wire (rq := d.wire (m j p sb.1).rq) (ak := d.wire (m j p sb.1).ak) (hheld j p sb hvf hk hsb)
        (fun σ' a1 a2 => htx σ' a1 (by omega)) hmem h1' h2'
    exact route_hold hsat h0 h1 hg hb hinF ht (by omega)
  obtain ⟨hselok, hall⟩ := causal_close bh hpre hstep
  refine ⟨hselok, fun t j hv => ?_⟩
  rw [← hreal j hv t]; exact hall t j

end

end Formal.Core.XAudit.Events9Full
