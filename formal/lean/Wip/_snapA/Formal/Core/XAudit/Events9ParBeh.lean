import Formal.Core.XAudit.Events9ArbBeh
import Formal.Core.XAudit.Events9Par

/-!
# Formal.Core.XAudit.Events9ParBeh — `design_verdict9par`: the netlist-level verdict with
parallel-pair lines (probe E9Par, shard A)

See `formal/notes/A-e9par.md`.

* **`HRst`** (NAMED HYPOTHESIS, part of the arbiter hypothesis): the nodes of each reset class
  (in `xevents9par`: the four readers of one arbiter of the corrected core — two grants, two
  shadows) have node behaviours (`ND7`) with ONE common reset signal. In the cell-level
  sufficiency proof every reader of an arbiter is built with the reset `fun u => decide (u < T0)`
  for the same `T0` (`Events9ParRst.core_of_en_rst`).
* `ndAllP`, **`design_behP`**: as `Events8.design_beh8`, with the virtual nodes of `rs` realised
  by the common-reset node behaviours; the realisation satisfies `RstSync`.
* **`design_verdict9par`** (what `xevents9par` checks): `Events9Arb.design_verdict9arb` with the
  log `LnP` (`runLogP`) and the extra hypothesis `HRst`. Same conclusion.
-/

namespace Formal.Core.XAudit.Events9Par

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
open Formal.Core.XAudit.Events9Arb

/-- **`HRst`** (named hypothesis): the nodes of each reset class `k ≠ 0` (`rs j = k`) have node
behaviours with one common reset signal `ρ k`. -/
def HRst {N : Nat} {d : Design} (net : Net4 N) (b : Bands4 net) (rn : Fin N → RNode) (x : Fin d.n → Sig)
    (cv : Fin N → Sig) (rs : Nat → Nat) : Prop :=
  ∃ ρ : Nat → Sig, ∀ j : Fin N, rs j.val ≠ 0 → Nonempty {nd : ND7 net b (ccOf rn x cv) j // nd.r = ρ (rs j.val)}

section
variable {N : Nat} {d : Design} {net : Net4 N} {b : Bands4 net} {rn : Fin N → RNode} {rank : Fin N → Nat}
  {rw fuel : Nat} {x : Fin d.n → Sig} (hsat : SatPin d plG x)
  (h0 : ∀ t, x (d.wire 0) t = false) (h1 : ∀ t, x (d.wire 1) t = true)
  {T : Nat} (hT : 1 ≤ T) (hrst : ∀ t, x (d.wire rw) t = decide (t < T))
  {cv : Fin N → Sig} (hr : Recog6 d net b rn rank rw fuel) (hOK : net.OK7) (harb : HARB7 net b rn x cv)
  {rs : Nat → Nat} (hR : HRst net b rn x cv rs)

include hsat h0 h1 hT hrst hr hOK harb hR

/-- The node behaviours: the `rs` nodes from `HRst` (common reset), every other node as
`Events7.ndAll7`. -/
noncomputable def ndAllP (j : Fin N) : ND7 net b (ccOf rn x cv) j :=
  if h : rs j.val ≠ 0 then (Classical.choice (hR.choose_spec j h)).val
  else ndAll7 hsat h0 h1 hT hrst hr hOK harb j

/-- **`design_behP`**: `Events8.design_beh8` with the `rs` nodes realised by `HRst`'s node
behaviours, so the realisation satisfies `RstSync`. -/
theorem design_behP (sel : Nat → Nat → Bool) :
    ∃ bh : Beh7 net b sel, (∀ j t, bh.c j t = ccOf rn x cv j t) ∧
      (∀ j p s, bh.gc j p s = gcnt net sel j p (bh.cm j p s)) ∧
      (∀ j, (rn j).virt = false → ∀ t, bh.c j t = x (d.wire (gt d (rn j).lut).out) t) ∧
      RstSync bh rs := by
  have mg0 : ∀ j, net.mg j = true → ccOf rn x cv j 0 = false := fun j hm => by
    rw [init0_7 hsat h0 h1 hT hrst hr hOK harb j]; exact ((hOK j ⟨0, net.ar_pos j⟩).2.2.2.1 hm).1
  refine ⟨beh8 sel (ndAllP hsat h0 h1 hT hrst hr hOK harb hR) mg0, fun j t => rfl,
    beh8_gc sel (ndAllP hsat h0 h1 hT hrst hr hOK harb hR) mg0, fun j hv t => ?_, ?_⟩
  · show ccOf rn x cv j t = _
    unfold ccOf; rw [hv, (hr.2 j hv).2.1]; rfl
  · intro z y hz hy s
    show (ndAllP hsat h0 h1 hT hrst hr hOK harb hR z).r s = (ndAllP hsat h0 h1 hT hrst hr hOK harb hR y).r s
    unfold ndAllP
    have hz' : rs z.val ≠ 0 := by rw [hz]; exact hy
    rw [dif_pos hz', dif_pos hy, (Classical.choice (hR.choose_spec z hz')).property,
      (Classical.choice (hR.choose_spec y hy)).property, hz]

end

section
variable {N : Nat} {d : Design} {net : Net4 N} {b : Bands4 net} {rn : Fin N → RNode} {rank : Fin N → Nat}
  {rw fuel : Nat} {x : Fin d.n → Sig} {cv : Fin N → Sig}

/-- **`design_verdict9par`** (what a run of `xevents9par` means). The executable checks
`Recog6`, `Net4.OK7`, that the derivation log `LnP` is accepted (`runLogP … rs … = some J`,
`rs` = its reset classes) and, per item, `backOK7` / `exclOK7` / `lineOK7` /
`guardOK8` (against the sanitized hypothesis lines). Then for every per-pin behaviour `x` of the
parsed netlist (constant wires, reset high until `T`, the corrected arbiter hypothesis `HARB7'`,
and `HRst`: the nodes of each reset class have node behaviours with one common reset) and every select sequence
there is a `Beh7` realising `x`, whose guarded count is `gcnt`, such that under SelPart, SelOK and
the residual obligations of the items NOT certified, every real LUT wire is its reset value flipped
`M t j` times at every time. -/
theorem design_verdict9par (hr : Recog6 d net b rn rank rw fuel) (hOK : net.OK7)
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
    (hsat : SatPin d plG x) (h0 : ∀ t, x (d.wire 0) t = false) (h1 : ∀ t, x (d.wire 1) t = true)
    {T : Nat} (hT : 1 ≤ T) (hrst : ∀ t, x (d.wire rw) t = decide (t < T)) (harb : HARB7' net b rn x cv)
    (hR : HRst net b rn x cv rs) (sel : Nat → Nat → Bool) :
    ∃ bh : Beh7 net b sel, (∀ j t, bh.c j t = ccOf rn x cv j t) ∧
      (∀ j p s, bh.gc j p s = gcnt net sel j p (bh.cm j p s)) ∧
      (SelPart sel parts → bh.SelOK →
        (∀ j p s, net.mg j = false → net.pk j p ≠ PK.guard → cp j p = false → bh.P j p s ≤ bh.M (bh.Q j s) j + 1) →
        (∀ m s, net.mg m = true → cxm m = false → fodd (net.ar m) (fun p => bh.P m p s) ≤ 1) →
        (∀ j p s, net.pk j p = PK.multi → cl j p = false → ContigF (net.nc j p) (bh.cm j p s)) →
        (∀ j p, net.pk j p = PK.guard → cg j p = false → GuardPin bh j p) →
        ∀ t j, (rn j).virt = false →
          x (d.wire (gt d (rn j).lut).out) t = ph (net.v j) (bh.M t j)) := by
  obtain ⟨bh, hc, hgc, hreal, hsync⟩ := design_behP hsat h0 h1 hT hrst hr hOK harb.1 hR sel
  refine ⟨bh, hc, hgc, fun hp hsel rB rX rL rG t j hv => ?_⟩
  rw [← hreal j hv t]
  exact verdict9par bh hOK hp hsync hJ back line xS xw xa hl gd cp cxm cl cg hcp hcx hcl hcg
    (fun j p s _ => hgc j p s) rB rX rL rG hsel t j

end

end Formal.Core.XAudit.Events9Par
