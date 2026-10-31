import Formal.Core.XAudit.Events9Full
import Formal.Core.XAudit.Events9ArbNetEdge
import Formal.Core.XAudit.Events9ArbB1

/-!
# Formal.Core.XAudit.Events9FullArb — one statement: full select/setup verdict + arbiter link

Shard A, lead, 2026-10-31. Joins `Events9Full.design_verdict9_full` (corrected arbiter core,
junction select rows, setup rows, one realisation) with `Events9ArbNet` (the corrected core's
hypotheses HARB7' / HRst discharged at the real bd_arbiter LUTs) and `Events9ArbNetEdge`
(the per-arbiter trace conditions ArbCond from decidable rows plus edge windows).

**Problem statement.** For a routed netlist `d` parsed by xaudit, a certificate accepted by the
checker, and every behaviour `x` of `d` in the per-pin delay bands (SatPin):

* CHECKED (decidable, evaluated by the executables on the real files): everything
  `design_verdict9_full` checks, plus per arbiter `ArbOK` (bd_arbiter's four LUT functions read off
  the INITs, read paths, request nets, corrected-core shape and bands), `OwnOK`, `RsOK`,
  `FixShape`, and `ArbRowsOK` (B1 rows and the start bounds).
* ASSUMED (hypotheses of the theorem): SatPin (the delay model), constant wires and the design
  reset; per arbiter `ArbEdge`: `QClean` (q makes clean transitions: no metastable runt, the
  digital no-metastability hypothesis), a quiet start up to `T0`, a settle bound `H k`
  (unbounded for a near tie, so this is an uncontested-schedule hypothesis), and per reader the
  edge windows (no re-request while the arbiter switches away, settledness after request rises
  and literal flips, A0 high around request falls); then, as in `design_verdict9_full`, SelPart,
  SelOK at the virtual pins, C's H_BUNDLE per mapped select channel, H_SEL_FN, H_SEL_O / setup for
  the literals without a setup row, and the residual obligations of uncertified items.
* PROVED: there are virtual signals `cv` and ONE `Beh7` realisation such that SelOK holds and
  every real LUT wire equals its reset value flipped `M t j` times at every time.

NOT covered: the edge windows themselves (no theorem derives them from the printed rows or from
the certificate's walks), the near-tie/metastable schedules (excluded by QClean and H), the
parsers and generators, and whether the hypotheses are jointly satisfiable on a real gcd_hw run
(no witness here). HARB7 (the old core) is not used.
-/

namespace Formal.Core.XAudit.Events9FullArb

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
open Formal.Core.XAudit.Events9ArbNet
open Formal.Core.XAudit.Events9Full

section
variable {N K : Nat} {d : Design} {net : Net4 N} {b : Bands4 net} {rn : Fin N → RNode} {rank : Fin N → Nat}
  {rw fuel : Nat} {x : Fin d.n → Sig}

/-- **`design_verdict9_full_arb`**: `design_verdict9_full` with HARB7' and HRst replaced by the
checked arbiter link (`ArbOK`, `OwnOK`, `RsOK`, `FixShape`, `ArbRowsOK`) and the per-arbiter
edge-window hypotheses `ArbEdge`. Same conclusion, for SOME virtual signals `cv`. -/
theorem design_verdict9_full_arb (hr : Recog6 d net b rn rank rw fuel) (hOK : net.OK7)
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
    {T : Nat} (hT : 1 ≤ T) (hrst : ∀ t, x (d.wire rw) t = decide (t < T))
    (as : Fin K → ArbD N) (own : Fin N → Option (Fin K))
    (hA : ∀ k, ArbOK d net b rn fuel rw (as k)) (hown : OwnOK rn as own) (hrs : RsOK as rs)
    (hfs : Events9Arb.FixShape net b rn)
    (T0 : Nat) (H : Fin K → Nat) (hrows : ∀ k, ArbRowsOK d (as k) T T0)
    (he : ∀ k, ArbEdge hsat rn (as k) T0 (H k)) (sel : Nat → Nat → Bool) :
    ∃ cv : Fin N → Sig, ∃ bh : Beh7 net b sel, (∀ j t, bh.c j t = ccOf rn x cv j t) ∧
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
  have hc : ∀ k, ArbCond hsat rn (as k) T0 (H k) := fun k =>
    arbCond_of_edge hsat h0 h1 (hA k) hrst (hrows k) (he k)
  obtain ⟨cv, harb, hR⟩ := harb_of_arbs hsat h0 h1 as own rs hA hown hrs hfs T0 H hc
  exact ⟨cv, design_verdict9_full hr hOK hJ hrsv back line xS xw xa hl gd cp cxm cl cg hcp hcx hcl hcg
    m cut Dl ta tq na κa wq jl jw scut su cs hm hrow hsu hsat h0 h1 hT hrst harb hR sel⟩


/-- **`design_verdict9arbnet_edge`** (what `xevents9par` CLEAN plus `xarbnet` "ArbOK and ArbRowsOK
K/K" with OwnOK, RsOK, FixShape on ONE certificate mean): `Events9ArbNet.design_verdict9arbnet` with
the per-arbiter trace conditions `ArbCond` replaced by the checked rows `ArbRowsOK` and the edge-window
hypotheses `ArbEdge` (QClean, quiet start, settle bound, per-reader windows). Plain statement: every
SatPin behaviour of the parsed netlist with constant wires, the design reset released at `T`, and
`ArbEdge` at every arbiter, has a Beh7 realisation (for some virtual core signals `cv`) in which, under
SelPart and SelOK and the residual obligations of uncertified items, every real LUT wire is its reset
value flipped `M t j` times at every time. HARB7, HARB7' and HRst are not hypotheses. -/
theorem design_verdict9arbnet_edge (hr : Recog6 d net b rn rank rw fuel) (hOK : net.OK7)
    {parts : List (List Nat)} {rs : Nat → Nat} {log : List LnP} {J : Array Jd}
    (hJ : runLogP net b rs parts log = some J)
    (back line : (j : Fin N) → Fin (net.ar j) → Nat) (xS xw : Fin N → Nat) (xa : Fin N → List Arm)
    (hl : List HLn9) (gd : (j : Fin N) → Fin (net.ar j) → GD)
    (cp : (j : Fin N) → Fin (net.ar j) → Bool) (cxm : Fin N → Bool) (cl : (j : Fin N) → Fin (net.ar j) → Bool)
    (cg : (j : Fin N) → Fin (net.ar j) → Bool)
    (hcp : ∀ j p, cp j p = true → backOK7 net b J j p (back j p) = true)
    (hcx : ∀ m, cxm m = true → exclOK7 net b parts J m (xS m) (xa m) (xw m) = true)
    (hcl : ∀ j p, cl j p = true → lineOK7 net b J j p (line j p) = true)
    (hcg : ∀ j p, cg j p = true → guardOK8 net b parts J (hl.map (san J)) j p (gd j p) = true)
    (as : Fin K → ArbD N) (own : Fin N → Option (Fin K))
    (hA : ∀ k, ArbOK d net b rn fuel rw (as k)) (hown : OwnOK rn as own) (hrs : RsOK as rs)
    (hfs : Events9Arb.FixShape net b rn)
    (hsat : SatPin d plG x) (h0 : ∀ t, x (d.wire 0) t = false) (h1 : ∀ t, x (d.wire 1) t = true)
    {T : Nat} (hT : 1 ≤ T) (hrst : ∀ t, x (d.wire rw) t = decide (t < T))
    (T0 : Nat) (H : Fin K → Nat) (hrows : ∀ k, ArbRowsOK d (as k) T T0)
    (he : ∀ k, ArbEdge hsat rn (as k) T0 (H k)) (sel : Nat → Nat → Bool) :
    ∃ cv : Fin N → Sig, ∃ bh : Beh7 net b sel, (∀ j t, bh.c j t = ccOf rn x cv j t) ∧
      (∀ j p s, bh.gc j p s = gcnt net sel j p (bh.cm j p s)) ∧
      (SelPart sel parts → bh.SelOK →
        (∀ j p s, net.mg j = false → net.pk j p ≠ PK.guard → cp j p = false → bh.P j p s ≤ bh.M (bh.Q j s) j + 1) →
        (∀ m s, net.mg m = true → cxm m = false → fodd (net.ar m) (fun p => bh.P m p s) ≤ 1) →
        (∀ j p s, net.pk j p = PK.multi → cl j p = false → ContigF (net.nc j p) (bh.cm j p s)) →
        (∀ j p, net.pk j p = PK.guard → cg j p = false → GuardPin bh j p) →
        ∀ t j, (rn j).virt = false →
          x (d.wire (gt d (rn j).lut).out) t = ph (net.v j) (bh.M t j)) :=
  design_verdict9arbnet hr hOK hJ back line xS xw xa hl gd cp cxm cl cg hcp hcx hcl hcg as own hA hown hrs hfs
    hsat h0 h1 hT hrst T0 H (fun k => arbCond_of_edge hsat h0 h1 (hA k) hrst (hrows k) (he k)) sel


/-- **`design_verdict9arbnet_ord`**: `design_verdict9arbnet_edge` with the four B1 band rows of
`ArbRowsOK` replaced by the behaviour hypothesis `ArbOrd` (each reader's read order; given under
fixed path delays in a corner model by `ord_of_transport` + `corner_ord`). Checked: the par verdict's
checks, ArbOK, OwnOK, RsOK, FixShape, `ArbRowsOKS` (start bounds). Assumed: SatPin, constants,
reset, `ArbEdge`, `ArbOrd`, then SelPart, SelOK and the residual obligations. -/
theorem design_verdict9arbnet_ord (hr : Recog6 d net b rn rank rw fuel) (hOK : net.OK7)
    {parts : List (List Nat)} {rs : Nat → Nat} {log : List LnP} {J : Array Jd}
    (hJ : runLogP net b rs parts log = some J)
    (back line : (j : Fin N) → Fin (net.ar j) → Nat) (xS xw : Fin N → Nat) (xa : Fin N → List Arm)
    (hl : List HLn9) (gd : (j : Fin N) → Fin (net.ar j) → GD)
    (cp : (j : Fin N) → Fin (net.ar j) → Bool) (cxm : Fin N → Bool) (cl : (j : Fin N) → Fin (net.ar j) → Bool)
    (cg : (j : Fin N) → Fin (net.ar j) → Bool)
    (hcp : ∀ j p, cp j p = true → backOK7 net b J j p (back j p) = true)
    (hcx : ∀ m, cxm m = true → exclOK7 net b parts J m (xS m) (xa m) (xw m) = true)
    (hcl : ∀ j p, cl j p = true → lineOK7 net b J j p (line j p) = true)
    (hcg : ∀ j p, cg j p = true → guardOK8 net b parts J (hl.map (san J)) j p (gd j p) = true)
    (as : Fin K → ArbD N) (own : Fin N → Option (Fin K))
    (hA : ∀ k, ArbOK d net b rn fuel rw (as k)) (hown : OwnOK rn as own) (hrs : RsOK as rs)
    (hfs : Events9Arb.FixShape net b rn)
    (hsat : SatPin d plG x) (h0 : ∀ t, x (d.wire 0) t = false) (h1 : ∀ t, x (d.wire 1) t = true)
    {T : Nat} (hT : 1 ≤ T) (hrst : ∀ t, x (d.wire rw) t = decide (t < T))
    (T0 : Nat) (H : Fin K → Nat) (hrows : ∀ k, ArbRowsOKS d (as k) T T0)
    (he : ∀ k, ArbEdge hsat rn (as k) T0 (H k)) (ho : ∀ k, ArbOrd hsat (as k) T0) (sel : Nat → Nat → Bool) :
    ∃ cv : Fin N → Sig, ∃ bh : Beh7 net b sel, (∀ j t, bh.c j t = ccOf rn x cv j t) ∧
      (∀ j p s, bh.gc j p s = gcnt net sel j p (bh.cm j p s)) ∧
      (SelPart sel parts → bh.SelOK →
        (∀ j p s, net.mg j = false → net.pk j p ≠ PK.guard → cp j p = false → bh.P j p s ≤ bh.M (bh.Q j s) j + 1) →
        (∀ m s, net.mg m = true → cxm m = false → fodd (net.ar m) (fun p => bh.P m p s) ≤ 1) →
        (∀ j p s, net.pk j p = PK.multi → cl j p = false → ContigF (net.nc j p) (bh.cm j p s)) →
        (∀ j p, net.pk j p = PK.guard → cg j p = false → GuardPin bh j p) →
        ∀ t j, (rn j).virt = false →
          x (d.wire (gt d (rn j).lut).out) t = ph (net.v j) (bh.M t j)) :=
  design_verdict9arbnet hr hOK hJ back line xS xw xa hl gd cp cxm cl cg hcp hcx hcl hcg as own hA hown hrs hfs
    hsat h0 h1 hT hrst T0 H (fun k => arbCond_of_ord hsat h0 h1 (hA k) hrst (hrows k) (he k) (ho k)) sel

end

end Formal.Core.XAudit.Events9FullArb
