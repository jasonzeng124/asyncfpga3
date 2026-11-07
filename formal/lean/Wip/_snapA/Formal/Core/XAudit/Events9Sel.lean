import Formal.Core.XAudit.Events8BridgeSel
import Formal.Core.XAudit.Events9Beh

/-!
# Formal.Core.XAudit.Events9Sel — design_verdict9 with SelOK replaced at the real pins

Probe E8SelC (shard A). Notes: `formal/notes/A-e8selc.md` §1.

Port of `Events8Bridge.design_verdict8_sel` (probe E8Hyp) to the Events9 verdict
(`Events9.design_verdict9`, probe HDsub), so that BOTH replacements hold at once:
HDsub is proved (first-reach rule `dsub9`), and `bh.SelOK` is replaced at every REAL
filtered pin by B's H_S_STABLE (open-ended hold form) and H_SETUP_PIN on the select WIRES
of the parsed netlist (bands `selLo` / `selHi`).

* `selOK_real`: the SelOK derivation of design_verdict8_sel as a lemma (the realisation of
  `design_beh8_sv`, the virtual pins' SelOK, and the four select-wire premises give
  `bh.SelOK`). Reused by `Events9SelC`.
* **`design_verdict9_sel`**: `design_verdict9` with `bh.SelOK` replaced as above and no
  HDsub premise.

NOT covered (as in Events8BridgeSel): why the select wires are stable (they are free inputs
of the skeleton; see `Events9SelC` for C's H_BUNDLE), the virtual pins' SelOK (H_ARB).
-/

namespace Formal.Core.XAudit.Events9Sel

open Formal.Core
open Formal.Core.XAudit
open Formal.Core.TraceDiscrete (Sig Warp)
open Formal.Core.XAudit.Events2Pin (SatPin)
open Formal.Core.XAudit.Events5
open Formal.Core.XAudit.Events6
open Formal.Core.XAudit.Events7
open Formal.Core.XAudit.Events8
open Formal.Core.XAudit.Events9
open Formal.Core.XAudit.Events8Bridge

section
variable {N : Nat} {d : Design} {net : Net4 N} {b : Bands4 net} {rn : Fin N → RNode} {rank : Fin N → Nat}
  {rw fuel : Nat} {x : Fin d.n → Sig} {sel : Nat → Nat → Bool}

/-- **SelOK from the select-wire premises** (the core of `design_verdict8_sel`, as a lemma).
For a realisation `bh` whose real filtered pins see `svOf` (as `design_beh8_sv` gives):
SelOK at the virtual pins, plus, at the real ones, the transaction-start bound `R`, B's
per-pin setup, the open-ended stability of each select-bit wire, and `sel = selFn vb`,
give `bh.SelOK`. -/
theorem selOK_real (hsat : SatPin d plG x) (hr : Recog6 d net b rn rank rw fuel)
    (bh : Beh7 net b sel)
    (hsv : ∀ j, (rn j).virt = false → ∀ p s, bh.sv j p s = svOf (rn := rn) hsat j p s)
    (hvirt : ∀ j p s (i : Fin (net.nc j p)), (rn j).virt = true → net.pk j p = PK.filt →
      bh.M (bh.G j p i s) (net.src j p) % 2 = 1 →
      bh.sv j p s = sel (net.grp j p) (bh.M (bh.G j p i s) (net.src j p) / 2))
    (R : (j : Fin N) → Fin (net.ar j) → Nat → Nat)
    (S0 : (j : Fin N) → Fin (net.ar j) → Nat → Nat → Nat)
    (vb : (j : Fin N) → Fin (net.ar j) → Nat → Nat → Bool)
    (hwin : ∀ j p u k, (rn j).virt = false → net.pk j p = PK.filt →
      bh.M u (net.src j p) = 2 * k + 1 → R j p k ≤ u)
    (hsetup : ∀ j p (sb : Nat × Bool) (i : Fin (net.nc j p)) k, (rn j).virt = false → net.pk j p = PK.filt →
      sb ∈ selLits net rn j p → S0 j p sb.1 k + selHi d net rn j p ≤ R j p k + b.loC j p i)
    (hstab : ∀ j p (sb : Nat × Bool) (i : Fin (net.nc j p)) k t u, (rn j).virt = false →
      net.pk j p = PK.filt → sb ∈ selLits net rn j p → bh.M u (net.src j p) = 2 * k + 1 →
      S0 j p sb.1 k ≤ t → t + selLo d net rn j p ≤ u + b.hiC j p i →
      x (d.wire ((gt d (selGate net rn j p)).ins.getD sb.1 0)) t = vb j p sb.1 k)
    (hsel : ∀ j p k, (rn j).virt = false → net.pk j p = PK.filt →
      sel (net.grp j p) k = selFn (selLits net rn j p) (fun i => vb j p i k)) :
    bh.SelOK := by
  intro j p s i hk hodd
  by_cases hvj : (rn j).virt = true
  · exact hvirt j p s i hvj hk hodd
  · have hvf : (rn j).virt = false := by simpa using hvj
    have hk2 : bh.M (bh.G j p i s) (net.src j p) =
        2 * (bh.M (bh.G j p i s) (net.src j p) / 2) + 1 := by omega
    rw [hsv j hvf p s, svOf_shape hsat j p s, hsel j p _ hvf hk]
    apply selFn_congr
    intro sb hsb
    exact sel_read_hold (bh.wG j p i) (sel_warp hsat hr.1 j (hr.2 j hvf) p sb hsb)
      (fun u => bh.M u (net.src j p)) (bh.M_zero _)
      (x (d.wire ((gt d (selGate net rn j p)).ins.getD sb.1 0))) (vb j p sb.1) (R j p)
      (fun k => S0 j p sb.1 k) (fun u k h => hwin j p u k hvf hk h)
      (fun k => hsetup j p sb i k hvf hk hsb)
      (fun k t u h1 h2 h3 => hstab j p sb i k t u hvf hk hsb h1 h2 h3) s _ hk2

end

section
variable {N : Nat} {d : Design} {net : Net4 N} {b : Bands4 net} {rn : Fin N → RNode} {rank : Fin N → Nat}
  {rw fuel : Nat} {x : Fin d.n → Sig} {cv : Fin N → Sig}

/-- **`design_verdict9` with SelOK discharged at the real pins by B's steer conditions.**
Same checks and hypotheses as `design_verdict9` (HDsub proved, not assumed), except that
`bh.SelOK` is replaced by: SelOK at the VIRTUAL filtered pins only (part of H_ARB), and at
every REAL filtered pin `(j, p)` and select literal `sb`: transaction `k` of the pin's
source starts no earlier than `R j p k`; B's per-pin setup `S0 + selHi ≤ R + loC` against
every copy; the select bit's wire is `vb j p sb.1 k` from `S0 j p sb.1 k` on, as long as the
source was in transaction `k` at most `hiC - selLo` before (open-ended hold); and `sel` is
`selFn` of those bit values. All premises are about the trace `x`, the realisation's counts
and band numbers of the recognised netlist. -/
theorem design_verdict9_sel (hr : Recog6 d net b rn rank rw fuel) (hOK : net.OK7)
    {parts : List (List Nat)} {log : List Ln} {J : Array Jd} (hJ : runLog net b parts log = some J)
    (back line : (j : Fin N) → Fin (net.ar j) → Nat) (xS xw : Fin N → Nat) (xa : Fin N → List Arm)
    (hl : List HLn9) (gd : (j : Fin N) → Fin (net.ar j) → GD)
    (cp : (j : Fin N) → Fin (net.ar j) → Bool) (cxm : Fin N → Bool) (cl : (j : Fin N) → Fin (net.ar j) → Bool)
    (cg : (j : Fin N) → Fin (net.ar j) → Bool)
    (hcp : ∀ j p, cp j p = true → backOK7 net b J j p (back j p) = true)
    (hcx : ∀ m, cxm m = true → exclOK7 net b parts J m (xS m) (xa m) (xw m) = true)
    (hcl : ∀ j p, cl j p = true → lineOK7 net b J j p (line j p) = true)
    (hcg : ∀ j p, cg j p = true → guardOK8 net b parts J (hl.map (san J)) j p (gd j p) = true)
    (hsat : SatPin d plG x) (h0 : ∀ t, x (d.wire 0) t = false) (h1 : ∀ t, x (d.wire 1) t = true)
    {T : Nat} (hT : 1 ≤ T) (hrst : ∀ t, x (d.wire rw) t = decide (t < T)) (harb : HARB7 net b rn x cv)
    (sel : Nat → Nat → Bool) :
    ∃ bh : Beh7 net b sel, (∀ j t, bh.c j t = ccOf rn x cv j t) ∧
      (∀ j p s, bh.gc j p s = gcnt net sel j p (bh.cm j p s)) ∧
      (SelPart sel parts →
        (∀ j p s (i : Fin (net.nc j p)), (rn j).virt = true → net.pk j p = PK.filt →
          bh.M (bh.G j p i s) (net.src j p) % 2 = 1 →
          bh.sv j p s = sel (net.grp j p) (bh.M (bh.G j p i s) (net.src j p) / 2)) →
        ∀ (R : (j : Fin N) → Fin (net.ar j) → Nat → Nat)
          (S0 : (j : Fin N) → Fin (net.ar j) → Nat → Nat → Nat)
          (vb : (j : Fin N) → Fin (net.ar j) → Nat → Nat → Bool),
        (∀ j p u k, (rn j).virt = false → net.pk j p = PK.filt →
          bh.M u (net.src j p) = 2 * k + 1 → R j p k ≤ u) →
        (∀ j p (sb : Nat × Bool) (i : Fin (net.nc j p)) k, (rn j).virt = false → net.pk j p = PK.filt →
          sb ∈ selLits net rn j p → S0 j p sb.1 k + selHi d net rn j p ≤ R j p k + b.loC j p i) →
        (∀ j p (sb : Nat × Bool) (i : Fin (net.nc j p)) k t u, (rn j).virt = false →
          net.pk j p = PK.filt → sb ∈ selLits net rn j p → bh.M u (net.src j p) = 2 * k + 1 →
          S0 j p sb.1 k ≤ t → t + selLo d net rn j p ≤ u + b.hiC j p i →
          x (d.wire ((gt d (selGate net rn j p)).ins.getD sb.1 0)) t = vb j p sb.1 k) →
        (∀ j p k, (rn j).virt = false → net.pk j p = PK.filt →
          sel (net.grp j p) k = selFn (selLits net rn j p) (fun i => vb j p i k)) →
        (∀ j p s, net.mg j = false → net.pk j p ≠ PK.guard → cp j p = false → bh.P j p s ≤ bh.M (bh.Q j s) j + 1) →
        (∀ m s, net.mg m = true → cxm m = false → fodd (net.ar m) (fun p => bh.P m p s) ≤ 1) →
        (∀ j p s, net.pk j p = PK.multi → cl j p = false → ContigF (net.nc j p) (bh.cm j p s)) →
        (∀ j p, net.pk j p = PK.guard → cg j p = false → GuardPin bh j p) →
        ∀ t j, (rn j).virt = false →
          x (d.wire (gt d (rn j).lut).out) t = Formal.Core.XAudit.Events.ph (net.v j) (bh.M t j)) := by
  obtain ⟨bh, hc, hgc, hreal, hsv⟩ := design_beh8_sv hsat h0 h1 hT hrst hr hOK harb sel
  refine ⟨bh, hc, hgc, fun hp hvirt R S0 vb hwin hsetup hstab hsel rB rX rL rG t j hv => ?_⟩
  have hselok : bh.SelOK :=
    selOK_real hsat hr bh hsv hvirt R S0 vb hwin hsetup hstab hsel
  rw [← hreal j hv t]
  exact verdict9 bh hOK hp hJ back line xS xw xa hl gd cp cxm cl cg hcp hcx hcl hcg
    (fun j p s _ => hgc j p s) rB rX rL rG hselok t j

end

end Formal.Core.XAudit.Events9Sel
