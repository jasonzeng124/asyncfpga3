import Formal.Core.XAudit.Events9Beh

/-!
# Formal.Core.XAudit.Events9ArbBeh — `HARB7'` and `design_verdict9arb`

Probe E8ArbFix (shard A). See `formal/notes/A-e8arbfix.md`.

`Events7.HARB7` is generic in the certificate: it says that every VIRTUAL node of the parsed
certificate (`Net4`, `Bands4`) has an `ND7` behaviour in the certificate's bands. Which virtual
core it asserts is therefore decided by the certificate. `HARB7'` is `HARB7` together with the
SHAPE of the corrected core that events4/model.py (`build_arb_fix`) emits, as a structural
predicate on the certificate (`FixShape`):

* every virtual node has stage band `(1,1)`;
* every virtual non-merge node (ctl, grants, shadow grants) has own-value band `(1,1)`;
* every virtual merge (R0) has every tap `(1,1)`, and its arms are virtual nodes WITHOUT a wire
  (the shadow grants), so no real grant wire is an arm of R0 (the old core's R0 read the grants).

`design_verdict9arb` is `Events9.design_verdict9` (HDsub discharged) with `HARB7'` as the
arbiter hypothesis: the same conclusion, from the stronger premise. What it does NOT give: the
corrected core's certificates (on gcd_hw the Events7 log rules certify none of the 54 items that
needed the old R0-reads-grant link; notes §4), and `HARB7'` itself (it is a hypothesis; its
cell-level sufficiency is `Events9Arb.core_of_en`, modulo the enable construction).
-/

namespace Formal.Core.XAudit.Events9Arb

open Formal.Core
open Formal.Core.XAudit
open Formal.Core.TraceDiscrete (Sig Warp)
open Formal.Core.XAudit.Events (ph)
open Formal.Core.XAudit.Events2Pin (SatPin)
open Formal.Core.XAudit.Events5
open Formal.Core.XAudit.Events6
open Formal.Core.XAudit.Events7
open Formal.Core.XAudit.Events8
open Formal.Core.XAudit.Events9

/-- **The corrected core's shape** on a certificate (decidable data; see the module doc). -/
def FixShape {N : Nat} (net : Net4 N) (b : Bands4 net) (rn : Fin N → RNode) : Prop :=
  ∀ j, (rn j).virt = true → b.loF j = 1 ∧ b.hiF j = 1 ∧
    (net.mg j = false → b.loQ j = 1 ∧ b.hiQ j = 1) ∧
    (net.mg j = true → ∀ p (i : Fin (net.nc j p)), b.loC j p i = 1 ∧ b.hiC j p i = 1 ∧
      (rn (net.src j p)).virt = true ∧ (rn (net.src j p)).hasW = false)

/-- **`HARB7'`**: H_ARB for the corrected virtual core: `HARB7` over a certificate of the
corrected shape. -/
def HARB7' {N : Nat} {d : Design} (net : Net4 N) (b : Bands4 net) (rn : Fin N → RNode)
    (x : Fin d.n → Sig) (cv : Fin N → Sig) : Prop :=
  HARB7 net b rn x cv ∧ FixShape net b rn

section
variable {N : Nat} {d : Design} {net : Net4 N} {b : Bands4 net} {rn : Fin N → RNode} {rank : Fin N → Nat}
  {rw fuel : Nat} {x : Fin d.n → Sig} {cv : Fin N → Sig}

/-- **`design_verdict9arb`**: `design_verdict9` (no HDsub) under `HARB7'` (the corrected virtual
arbiter core). Same conclusion as `design_verdict9`. -/
theorem design_verdict9arb (hr : Recog6 d net b rn rank rw fuel) (hOK : net.OK7)
    {parts : List (List Nat)} {log : List Ln} {J : Array Jd} (hJ : runLog net b parts log = some J)
    (back line : (j : Fin N) → Fin (net.ar j) → Nat) (xS xw : Fin N → Nat) (xa : Fin N → List Arm)
    (hl : List HLn9) (gd : (j : Fin N) → Fin (net.ar j) → GD)
    (cp : (j : Fin N) → Fin (net.ar j) → Bool) (cxm : Fin N → Bool) (cl : (j : Fin N) → Fin (net.ar j) → Bool)
    (cg : (j : Fin N) → Fin (net.ar j) → Bool)
    (hcp : ∀ j p, cp j p = true → backOK7 net b J j p (back j p) = true)
    (hcx : ∀ m, cxm m = true → exclOK7 net b parts J m (xS m) (xa m) (xw m) = true)
    (hcl : ∀ j p, cl j p = true → lineOK7 net b J j p (line j p) = true)
    (hcg : ∀ j p, cg j p = true → guardOK8 net b parts J (hl.map (san J)) j p (gd j p) = true)
    (hsat : SatPinW d plG x) (h0 : ∀ t, x (d.wire 0) t = false) (h1 : ∀ t, x (d.wire 1) t = true)
    {T : Nat} (hT : 1 ≤ T) (hrst : ∀ t, x (d.wire rw) t = decide (t < T)) (harb : HARB7' net b rn x cv)
    (sel : Nat → Nat → Bool) :
    ∃ bh : Beh7 net b sel, (∀ j t, bh.c j t = ccOf rn x cv j t) ∧
      (∀ j p s, bh.gc j p s = gcnt net sel j p (bh.cm j p s)) ∧
      (SelPart sel parts → bh.SelOK →
        (∀ j p s, net.mg j = false → net.pk j p ≠ PK.guard → cp j p = false → bh.P j p s ≤ bh.M (bh.Q j s) j + 1) →
        (∀ m s, net.mg m = true → cxm m = false → fodd (net.ar m) (fun p => bh.P m p s) ≤ 1) →
        (∀ j p s, net.pk j p = PK.multi → cl j p = false → ContigF (net.nc j p) (bh.cm j p s)) →
        (∀ j p, net.pk j p = PK.guard → cg j p = false → GuardPin bh j p) →
        ∀ t j, (rn j).virt = false →
          x (d.wire (gt d (rn j).lut).out) t = ph (net.v j) (bh.M t j)) :=
  design_verdict9 hr hOK hJ back line xS xw xa hl gd cp cxm cl cg hcp hcx hcl hcg hsat h0 h1 hT hrst
    harb.1 sel

end

end Formal.Core.XAudit.Events9Arb
