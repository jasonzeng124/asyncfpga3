import Formal.Core.XAudit.Events8Cert

/-!
# Formal.Core.XAudit.Events8Beh — `design_verdict8`: the netlist-level verdict without GuardOK

Probe WE4g. See `formal/notes/A-events8.md`.

* **`design_beh8`**: every per-pin behaviour of a recognised netlist (`Recog6`,
  `Net4.OK7`, constant wires, reset, H_ARB) is the `Beh7` `beh8` of its node family,
  for every select sequence: its guarded count is `gcnt` of its own copy counts.
* **`design_verdict8`** (what `xevents8` checks): with an accepted log and the
  certified items, INCLUDING the guarded pins (`guardOK8`), every per-pin behaviour
  has a realising `Beh7` such that, if `sel` satisfies SelPart and the realisation
  SelOK, `HDsub` and the obligations of the items the checker did NOT certify, every
  real LUT wire is its reset value flipped `M t j` times at every time. GuardOK is no
  longer a hypothesis: a certified guarded pin needs `HDsub` (two count inequalities),
  an uncertified one carries GuardOK for that pin only (`GuardPin`).
* `design_guardOK8`: on a row where every guarded pin is certified, the Events7
  hypothesis `GuardOK` itself holds for that realisation (given SelOK, SelPart and
  the other residual obligations).
-/

namespace Formal.Core.XAudit.Events8

open Formal.Core
open Formal.Core.XAudit
open Formal.Core.TraceDiscrete (Sig Warp)
open Formal.Core.XAudit.Events (ph)
open Formal.Core.XAudit.Events2Pin (SatPin)
open Formal.Core.XAudit.Events5
open Formal.Core.XAudit.Events6
open Formal.Core.XAudit.Events7

section
variable {N : Nat} {d : Design} {net : Net4 N} {b : Bands4 net} {rn : Fin N → RNode} {rank : Fin N → Nat}
  {rw fuel : Nat} {x : Fin d.n → Sig} (hsat : SatPin d plG x)
  (h0 : ∀ t, x (d.wire 0) t = false) (h1 : ∀ t, x (d.wire 1) t = true)
  {T : Nat} (hT : 1 ≤ T) (hrst : ∀ t, x (d.wire rw) t = decide (t < T))
  {cv : Fin N → Sig} (hr : Recog6 d net b rn rank rw fuel) (hOK : net.OK7) (harb : HARB7 net b rn x cv)

include hsat h0 h1 hT hrst hr hOK harb

/-- **`design_beh8`.** Every per-pin behaviour of a recognised netlist with `Net4.OK7`
(constant wires, reset high until `T`, H_ARB) is a `Beh7` of the recognised `Net4`
whose guarded count is `gcnt` of its own copy counts, for every select sequence. -/
theorem design_beh8 (sel : Nat → Nat → Bool) :
    ∃ bh : Beh7 net b sel, (∀ j t, bh.c j t = ccOf rn x cv j t) ∧
      (∀ j p s, bh.gc j p s = gcnt net sel j p (bh.cm j p s)) ∧
      (∀ j, (rn j).virt = false → ∀ t, bh.c j t = x (d.wire (gt d (rn j).lut).out) t) := by
  have mg0 : ∀ j, net.mg j = true → ccOf rn x cv j 0 = false := fun j hm => by
    rw [init0_7 hsat h0 h1 hT hrst hr hOK harb j]; exact ((hOK j ⟨0, net.ar_pos j⟩).2.2.2.1 hm).1
  refine ⟨beh8 sel (ndAll7 hsat h0 h1 hT hrst hr hOK harb) mg0, fun j t => rfl,
    beh8_gc sel (ndAll7 hsat h0 h1 hT hrst hr hOK harb) mg0, fun j hv t => ?_⟩
  show ccOf rn x cv j t = _
  unfold ccOf; rw [hv, (hr.2 j hv).2.1]; rfl

end

section
variable {N : Nat} {d : Design} {net : Net4 N} {b : Bands4 net} {rn : Fin N → RNode} {rank : Fin N → Nat}
  {rw fuel : Nat} {x : Fin d.n → Sig} {cv : Fin N → Sig}

/-- **`design_verdict8`** (what a run of `xevents8` means). The executable checks
`Recog6`, `Net4.OK7`, that the derivation log is accepted (`runLog … = some J`) and,
per item, `backOK7` / `exclOK7` / `lineOK7` / **`guardOK8`** against `J`; `cp`, `cxm`,
`cl`, `cg` record which items it certified. Then for every per-pin behaviour `x` of
the parsed netlist (constant wires, reset high until `T`, H_ARB) and every select
sequence `sel` there is a `Beh7` realising `x`, whose guarded count is `gcnt`, such
that — if `sel` satisfies SelPart for the certificate's partitions and the
realisation satisfies SelOK, `HDsub` (the certificate's labelled walks from guarded
sources, two count inequalities per guarded pin) and the residual obligations of the
items the checker did NOT certify — every real LUT wire is its reset value flipped
`M t j` times at every time. With no residual item (CLEAN) the last hypotheses are
vacuous: the verdict then rests on SatPin, the constants and reset, H_ARB, SelOK,
SelPart and HDsub (GuardOK is not a hypothesis). -/
theorem design_verdict8 (hr : Recog6 d net b rn rank rw fuel) (hOK : net.OK7)
    {parts : List (List Nat)} {log : List Ln} {J : Array Jd} (hJ : runLog net b parts log = some J)
    (back line : (j : Fin N) → Fin (net.ar j) → Nat) (xS xw : Fin N → Nat) (xa : Fin N → List Arm)
    (hl : List HLn) (gd : (j : Fin N) → Fin (net.ar j) → GD)
    (cp : (j : Fin N) → Fin (net.ar j) → Bool) (cxm : Fin N → Bool) (cl : (j : Fin N) → Fin (net.ar j) → Bool)
    (cg : (j : Fin N) → Fin (net.ar j) → Bool)
    (hcp : ∀ j p, cp j p = true → backOK7 net b J j p (back j p) = true)
    (hcx : ∀ m, cxm m = true → exclOK7 net b parts J m (xS m) (xa m) (xw m) = true)
    (hcl : ∀ j p, cl j p = true → lineOK7 net b J j p (line j p) = true)
    (hcg : ∀ j p, cg j p = true → guardOK8 net b parts J hl j p (gd j p) = true)
    (hsat : SatPin d plG x) (h0 : ∀ t, x (d.wire 0) t = false) (h1 : ∀ t, x (d.wire 1) t = true)
    {T : Nat} (hT : 1 ≤ T) (hrst : ∀ t, x (d.wire rw) t = decide (t < T)) (harb : HARB7 net b rn x cv)
    (sel : Nat → Nat → Bool) :
    ∃ bh : Beh7 net b sel, (∀ j t, bh.c j t = ccOf rn x cv j t) ∧
      (∀ j p s, bh.gc j p s = gcnt net sel j p (bh.cm j p s)) ∧
      (SelPart sel parts → bh.SelOK → HDsub bh parts J hl →
        (∀ j p s, net.mg j = false → net.pk j p ≠ PK.guard → cp j p = false → bh.P j p s ≤ bh.M (bh.Q j s) j + 1) →
        (∀ m s, net.mg m = true → cxm m = false → fodd (net.ar m) (fun p => bh.P m p s) ≤ 1) →
        (∀ j p s, net.pk j p = PK.multi → cl j p = false → ContigF (net.nc j p) (bh.cm j p s)) →
        (∀ j p, net.pk j p = PK.guard → cg j p = false → GuardPin bh j p) →
        ∀ t j, (rn j).virt = false →
          x (d.wire (gt d (rn j).lut).out) t = ph (net.v j) (bh.M t j)) := by
  obtain ⟨bh, hc, hgc, hreal⟩ := design_beh8 hsat h0 h1 hT hrst hr hOK harb sel
  refine ⟨bh, hc, hgc, fun hp hsel hH rB rX rL rG t j hv => ?_⟩
  rw [← hreal j hv t]
  exact verdict8 bh hOK hp hJ back line xS xw xa hl gd cp cxm cl cg hcp hcx hcl hcg
    (fun j p s _ => hgc j p s) rB rX rL rG hsel hH t j

/-- **GuardOK discharged (the Events7 hypothesis itself).** On a row where the checker
certified every guarded pin, the realisation of `design_verdict8` satisfies
`Beh7.GuardOK` (under SelPart, SelOK and the other items' obligations, all vacuous on a
CLEAN row). So `design_verdict7`'s GuardOK hypothesis holds for this choice of `gc`. -/
theorem design_guardOK8 (hr : Recog6 d net b rn rank rw fuel) (hOK : net.OK7)
    {parts : List (List Nat)} {log : List Ln} {J : Array Jd} (hJ : runLog net b parts log = some J)
    (back line : (j : Fin N) → Fin (net.ar j) → Nat) (xS xw : Fin N → Nat) (xa : Fin N → List Arm)
    (hl : List HLn) (gd : (j : Fin N) → Fin (net.ar j) → GD)
    (cp : (j : Fin N) → Fin (net.ar j) → Bool) (cxm : Fin N → Bool) (cl : (j : Fin N) → Fin (net.ar j) → Bool)
    (hcp : ∀ j p, cp j p = true → backOK7 net b J j p (back j p) = true)
    (hcx : ∀ m, cxm m = true → exclOK7 net b parts J m (xS m) (xa m) (xw m) = true)
    (hcl : ∀ j p, cl j p = true → lineOK7 net b J j p (line j p) = true)
    (hcg : ∀ j p, net.pk j p = PK.guard → guardOK8 net b parts J hl j p (gd j p) = true)
    (hsat : SatPin d plG x) (h0 : ∀ t, x (d.wire 0) t = false) (h1 : ∀ t, x (d.wire 1) t = true)
    {T : Nat} (hT : 1 ≤ T) (hrst : ∀ t, x (d.wire rw) t = decide (t < T)) (harb : HARB7 net b rn x cv)
    (sel : Nat → Nat → Bool) :
    ∃ bh : Beh7 net b sel, (∀ j t, bh.c j t = ccOf rn x cv j t) ∧
      (∀ j p s, bh.gc j p s = gcnt net sel j p (bh.cm j p s)) ∧
      (SelPart sel parts → bh.SelOK → HDsub bh parts J hl →
        (∀ j p s, net.mg j = false → net.pk j p ≠ PK.guard → cp j p = false → bh.P j p s ≤ bh.M (bh.Q j s) j + 1) →
        (∀ m s, net.mg m = true → cxm m = false → fodd (net.ar m) (fun p => bh.P m p s) ≤ 1) →
        (∀ j p s, net.pk j p = PK.multi → cl j p = false → ContigF (net.nc j p) (bh.cm j p s)) →
        bh.GuardOK) := by
  obtain ⟨bh, hc, hgc, _⟩ := design_beh8 hsat h0 h1 hT hrst hr hOK harb sel
  refine ⟨bh, hc, hgc, fun hp hsel hH rB rX rL => ?_⟩
  have hA := runLog_sound bh hOK hp hJ
  refine guardOK_of_cnt bh hOK hsel ?_ ?_ ?_ (fun j p s _ => hgc j p s)
    (fun j p hk => guardOK8_sound bh hOK hA hH j p (gd j p) (hgc j p) (hcg j p hk))
  · intro j p s hk
    cases hc : cl j p
    · exact rL j p s hk hc
    · exact lineOK7_sound bh hA j p _ (hcl j p hc) s
  · intro j p s hm hk
    cases hc : cp j p
    · exact rB j p s hm hk hc
    · exact backOK7_sound bh hOK hA j p hk _ (hcp j p hc) s
  · intro m s hm
    cases hc : cxm m
    · exact rX m s hm hc
    · exact exclOK7_sound bh hOK hp hA m hm _ _ _ (hcx m hc) s

end

end Formal.Core.XAudit.Events8
