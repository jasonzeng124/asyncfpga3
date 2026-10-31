import Formal.Core.XAudit.Events9Cert

/-!
# Formal.Core.XAudit.Events9Beh — `design_verdict9`: the netlist-level verdict without HDsub

Probe HDsub. See `formal/notes/A-events9.md`.

**`design_verdict9`** (what `xevents9` checks) is `Events8.design_verdict8` with the
guard certificates checked against the hypothesis lines `hl.map (HLn9.toH J)` (each
`dsub` line carries a log line `wS`, a walk from the label source to the walk's
start with at most one token, checked by `wsOK`), and WITHOUT the hypothesis
`HDsub`: it is proved (`hdsub9`, the first-reach rule `dsub9`).

On a CLEAN row the verdict rests on: per-pin SatPin, the constant wires and reset,
H_ARB, SelOK and SelPart.

`design_guardOK9`: on a row where every guarded pin is certified, the Events7
hypothesis `GuardOK` holds for the realisation (given SelOK, SelPart and the other
items' obligations, vacuous on a CLEAN row) — now without HDsub.
-/

namespace Formal.Core.XAudit.Events9

open Formal.Core
open Formal.Core.XAudit
open Formal.Core.TraceDiscrete (Sig Warp)
open Formal.Core.XAudit.Events (ph)
open Formal.Core.XAudit.Events2Pin (SatPin)
open Formal.Core.XAudit.Events5
open Formal.Core.XAudit.Events6
open Formal.Core.XAudit.Events7
open Formal.Core.XAudit.Events8

section
variable {N : Nat} {d : Design} {net : Net4 N} {b : Bands4 net} {rn : Fin N → RNode} {rank : Fin N → Nat}
  {rw fuel : Nat} {x : Fin d.n → Sig} {cv : Fin N → Sig}

/-- **`design_verdict9`** (what a run of `xevents9` means). The executable checks
`Recog6`, `Net4.OK7`, that the derivation log is accepted (`runLog … = some J`) and,
per item, `backOK7` / `exclOK7` / `lineOK7` / `guardOK8` against `J` and the
hypothesis lines `hl.map (HLn9.toH J)`; `cp`, `cxm`, `cl`, `cg` record which items it
certified. Then for every per-pin behaviour `x` of the parsed netlist (constant
wires, reset high until `T`, H_ARB) and every select sequence `sel` there is a
`Beh7` realising `x`, whose guarded count is `gcnt`, such that — if `sel` satisfies
SelPart for the certificate's partitions and the realisation satisfies SelOK and the
residual obligations of the items the checker did NOT certify — every real LUT wire
is its reset value flipped `M t j` times at every time. There is no HDsub (and no
GuardOK) hypothesis. -/
theorem design_verdict9 (hr : Recog6 d net b rn rank rw fuel) (hOK : net.OK7)
    {parts : List (List Nat)} {log : List Ln} {J : Array Jd} (hJ : runLog net b parts log = some J)
    (back line : (j : Fin N) → Fin (net.ar j) → Nat) (xS xw : Fin N → Nat) (xa : Fin N → List Arm)
    (hl : List HLn9) (gd : (j : Fin N) → Fin (net.ar j) → GD)
    (cp : (j : Fin N) → Fin (net.ar j) → Bool) (cxm : Fin N → Bool) (cl : (j : Fin N) → Fin (net.ar j) → Bool)
    (cg : (j : Fin N) → Fin (net.ar j) → Bool)
    (hcp : ∀ j p, cp j p = true → backOK7 net b J j p (back j p) = true)
    (hcx : ∀ m, cxm m = true → exclOK7 net b parts J m (xS m) (xa m) (xw m) = true)
    (hcl : ∀ j p, cl j p = true → lineOK7 net b J j p (line j p) = true)
    (hcg : ∀ j p, cg j p = true → guardOK8 net b parts J (hl.map (HLn9.toH J)) j p (gd j p) = true)
    (hsat : SatPin d plG x) (h0 : ∀ t, x (d.wire 0) t = false) (h1 : ∀ t, x (d.wire 1) t = true)
    {T : Nat} (hT : 1 ≤ T) (hrst : ∀ t, x (d.wire rw) t = decide (t < T)) (harb : HARB7 net b rn x cv)
    (sel : Nat → Nat → Bool) :
    ∃ bh : Beh7 net b sel, (∀ j t, bh.c j t = ccOf rn x cv j t) ∧
      (∀ j p s, bh.gc j p s = gcnt net sel j p (bh.cm j p s)) ∧
      (SelPart sel parts → bh.SelOK →
        (∀ j p s, net.mg j = false → net.pk j p ≠ PK.guard → cp j p = false → bh.P j p s ≤ bh.M (bh.Q j s) j + 1) →
        (∀ m s, net.mg m = true → cxm m = false → fodd (net.ar m) (fun p => bh.P m p s) ≤ 1) →
        (∀ j p s, net.pk j p = PK.multi → cl j p = false → ContigF (net.nc j p) (bh.cm j p s)) →
        (∀ j p, net.pk j p = PK.guard → cg j p = false → GuardPin bh j p) →
        ∀ t j, (rn j).virt = false →
          x (d.wire (gt d (rn j).lut).out) t = ph (net.v j) (bh.M t j)) := by
  obtain ⟨bh, hc, hgc, hreal⟩ := design_beh8 hsat h0 h1 hT hrst hr hOK harb sel
  refine ⟨bh, hc, hgc, fun hp hsel rB rX rL rG t j hv => ?_⟩
  rw [← hreal j hv t]
  exact verdict9 bh hOK hp hJ back line xS xw xa hl gd cp cxm cl cg hcp hcx hcl hcg
    (fun j p s _ => hgc j p s) rB rX rL rG hsel t j

/-- **GuardOK discharged without HDsub.** On a row where the checker certified every
guarded pin, the realisation satisfies `Beh7.GuardOK` (under SelPart, SelOK and the
other items' obligations, all vacuous on a CLEAN row). -/
theorem design_guardOK9 (hr : Recog6 d net b rn rank rw fuel) (hOK : net.OK7)
    {parts : List (List Nat)} {log : List Ln} {J : Array Jd} (hJ : runLog net b parts log = some J)
    (back line : (j : Fin N) → Fin (net.ar j) → Nat) (xS xw : Fin N → Nat) (xa : Fin N → List Arm)
    (hl : List HLn9) (gd : (j : Fin N) → Fin (net.ar j) → GD)
    (cp : (j : Fin N) → Fin (net.ar j) → Bool) (cxm : Fin N → Bool) (cl : (j : Fin N) → Fin (net.ar j) → Bool)
    (hcp : ∀ j p, cp j p = true → backOK7 net b J j p (back j p) = true)
    (hcx : ∀ m, cxm m = true → exclOK7 net b parts J m (xS m) (xa m) (xw m) = true)
    (hcl : ∀ j p, cl j p = true → lineOK7 net b J j p (line j p) = true)
    (hcg : ∀ j p, net.pk j p = PK.guard → guardOK8 net b parts J (hl.map (HLn9.toH J)) j p (gd j p) = true)
    (hsat : SatPin d plG x) (h0 : ∀ t, x (d.wire 0) t = false) (h1 : ∀ t, x (d.wire 1) t = true)
    {T : Nat} (hT : 1 ≤ T) (hrst : ∀ t, x (d.wire rw) t = decide (t < T)) (harb : HARB7 net b rn x cv)
    (sel : Nat → Nat → Bool) :
    ∃ bh : Beh7 net b sel, (∀ j t, bh.c j t = ccOf rn x cv j t) ∧
      (∀ j p s, bh.gc j p s = gcnt net sel j p (bh.cm j p s)) ∧
      (SelPart sel parts → bh.SelOK →
        (∀ j p s, net.mg j = false → net.pk j p ≠ PK.guard → cp j p = false → bh.P j p s ≤ bh.M (bh.Q j s) j + 1) →
        (∀ m s, net.mg m = true → cxm m = false → fodd (net.ar m) (fun p => bh.P m p s) ≤ 1) →
        (∀ j p s, net.pk j p = PK.multi → cl j p = false → ContigF (net.nc j p) (bh.cm j p s)) →
        bh.GuardOK) := by
  obtain ⟨bh, hc, hgc, h⟩ := design_guardOK8 hr hOK hJ back line xS xw xa (hl.map (HLn9.toH J)) gd cp cxm cl
    hcp hcx hcl hcg hsat h0 h1 hT hrst harb sel
  refine ⟨bh, hc, hgc, fun hp hsel rB rX rL => h hp hsel ?_ rB rX rL⟩
  exact hdsub9 bh hOK hp (runLog_sound bh hOK hp hJ) hl

end

end Formal.Core.XAudit.Events9
