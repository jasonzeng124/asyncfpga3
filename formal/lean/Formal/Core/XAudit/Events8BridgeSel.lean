import Formal.Core.XAudit.Events8Bridge

/-!
# Formal.Core.XAudit.Events8BridgeSel — design_verdict8 with SelOK discharged at the real pins

Probe E8Hyp (shard A). Notes: `formal/notes/A-e8hyp.md` §3.3.

`Events8Bridge.selOK_of_hold` derives `Beh7.SelOK` from B's steer conditions for a
realisation whose select reads have a known shape. This file shows that design_verdict8's
own realisation has that shape and assembles the result:

* `chkT_pathOK`: a successful tree check of one path is a path of existing gate inputs.
* `selLits`, `selGate`, `selLo`, `selHi`, `selFn`: per real filtered pin, its select
  literals, the gate that reads them (steer gate or stage LUT), the band of each bit read
  (explicit sums of gate bands and the `top` path band), and the pattern function.
* `svOf_shape`, `sel_warp`: the realised select (`Events6.svOf`) is `selFn` of the bit wires,
  each read through a warp in `[selLo, selHi]`.
* `design_beh8_sv`: `design_beh8`, also exposing that the realisation's `sv` is `svOf`.
* **`design_verdict8_sel`**: `design_verdict8` with `bh.SelOK` replaced by SelOK at the
  VIRTUAL filtered pins (part of H_ARB) and, at the real ones, B's H_S_STABLE (open-ended
  hold form) and H_SETUP_PIN on the select WIRES of the parsed netlist, with explicit band
  numbers.

NOT covered: the stability of the select wires themselves (they are free inputs of the
skeleton: a data-path fact, C's H_BUNDLE / H_LATCH_HOLD), and the virtual pins' SelOK.
-/

namespace Formal.Core.XAudit.Events8Bridge

open Formal.Core
open Formal.Core.XAudit
open Formal.Core.TraceDiscrete (Sig Warp Mono)
open Formal.Core.XAudit.Events2Pin (SatPin)
open Formal.Core.XAudit.Events5
open Formal.Core.XAudit.Events6
open Formal.Core.XAudit.Events7
open Formal.Core.XAudit.Events8

/-- A tree check of ONE path succeeds only on a path of existing gate inputs. -/
theorem chkT_pathOK {d : Design} {sw : Nat} : ∀ (fuel : Nat) (op : Bool) (w : Nat) (π : Path)
    (par : Bool), chkT d sw fuel op w [π] = some par → pathOK d π = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro op w π par h
    cases π with
    | nil => simp [pathOK]
    | cons e r => unfold chkT at h; simp at h
  | succ n ih =>
    intro op w π par h
    cases π with
    | nil => simp [pathOK]
    | cons e r =>
      obtain ⟨gi, i⟩ := e
      unfold chkT at h
      simp only [show ¬ ([(gi, i) :: r] = [[]]) from by simp, ↓reduceIte] at h
      split at h
      · rename_i hc
        obtain ⟨hg, _, hh⟩ := hc
        have hi : i ∈ liveIdx (gt d gi) := by
          simp [headOK] at hh; exact hh
        have hik := mem_liveIdx hi
        have hr : pathOK d r = true := by
          split at h
          · split at h
            · simp only [List.map_cons, List.map_nil, List.tail_cons] at h; exact ih _ _ r _ h
            · split at h
              · simp only [List.map_cons, List.map_nil, List.tail_cons] at h
                generalize hq : chkT d sw n op _ [r] = o at h
                cases o with
                | none => simp at h
                | some p' => exact ih _ _ r _ hq
              · simp at h
          · split at h
            · rename_i hc2
              have hall := List.all_eq_true.mp hc2.2.2 i hi
              have hsub : subOf [(gi, i) :: r] i = [r] := by simp [subOf]
              rw [hsub] at hall
              exact ih _ _ r _ (by simpa using hall)
            · simp at h
        simp only [pathOK, List.all_cons, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨hg, hik⟩, hr⟩
      · simp at h

/-! ## The select a real filtered pin sees, in design_verdict8's realisation -/

section
variable {N : Nat} (d : Design) (net : Net4 N) (rn : Fin N → RNode)

/-- The select literals of a filtered pin: the steer gate's (`ssel`) or the folded ones. -/
def selLits (j : Fin N) (p : Fin (net.ar j)) : List (Nat × Bool) :=
  if (rpin net rn j p).st then (rpin net rn j p).ssel else (rpin net rn j p).fold

/-- The gate whose inputs are the select bits: the steer gate, or the stage LUT. -/
def selGate (j : Fin N) (p : Fin (net.ar j)) : Nat :=
  if (rpin net rn j p).st then (rpin net rn j p).sg else (rn j).lut

/-- Band ends of a select-bit read, relative to the stage's sample time `s`. -/
def selLo (j : Fin N) (p : Fin (net.ar j)) : Nat :=
  if (rpin net rn j p).st then
    (gt d (rpin net rn j p).sg).lo + (plo d (rpin net rn j p).top + ((gt d (rn j).lut).lo - 1))
  else (gt d (rn j).lut).lo - 1

def selHi (j : Fin N) (p : Fin (net.ar j)) : Nat :=
  if (rpin net rn j p).st then
    (gt d (rpin net rn j p).sg).hi + (phi d (rpin net rn j p).top + ((gt d (rn j).lut).hi - 1))
  else (gt d (rn j).lut).hi - 1

/-- The select value from the bit values (indexed by the gate input they enter). -/
def selFn (l : List (Nat × Bool)) (v : Nat → Bool) : Bool :=
  if l.length = 1 then v (l.headD (0, false)).1 else foldM v l

theorem selFn_congr (l : List (Nat × Bool)) {v w : Nat → Bool} (h : ∀ sb ∈ l, v sb.1 = w sb.1) :
    selFn l v = selFn l w := by
  unfold selFn
  split
  · rename_i hl
    match l, hl with
    | [a], _ => exact h a (List.mem_singleton_self a)
  · unfold foldM
    rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    constructor
    · intro H sb hsb; rw [← h sb hsb]; exact H sb hsb
    · intro H sb hsb; rw [h sb hsb]; exact H sb hsb

end

section
variable {N : Nat} {d : Design} {net : Net4 N} {b : Bands4 net} {rn : Fin N → RNode} {rank : Fin N → Nat}
  {rw fuel : Nat} {x : Fin d.n → Sig} (hsat : SatPinW d plG x)

/-- The sample-time map before the select gate's own pin warp. -/
noncomputable def selBase (j : Fin N) (p : Fin (net.ar j)) : Nat → Nat := fun s =>
  if (rpin net rn j p).st then tau hsat (rpin net rn j p).top (wf hsat (rn j).lut (rpin net rn j p).ip (s + 1))
  else s + 1

theorem svOf_shape (j : Fin N) (p : Fin (net.ar j)) (s : Nat) :
    svOf (rn := rn) hsat j p s =
      selFn (selLits net rn j p) (fun i => vals hsat (selGate net rn j p) i (selBase (rn := rn) hsat j p s)) := by
  unfold svOf selFn selLits selGate selBase
  by_cases hst : (rpin net rn j p).st = true
  · simp only [hst, ↓reduceIte]
  · simp only [hst, Bool.false_eq_true, ↓reduceIte]

/-- Each select-bit read of a recognised real filtered pin is a warp in `[selLo, selHi]`. -/
theorem sel_warp (hwf : d.WF) (j : Fin N) (hn : NodeR d net b rn rank rw fuel j) (p : Fin (net.ar j))
    (sb : Nat × Bool) (hsb : sb ∈ selLits net rn j p) :
    Warp (selLo d net rn j p) (selHi d net rn j p)
      (fun s => wf hsat (selGate net rn j p) sb.1 (selBase (rn := rn) hsat j p s)) := by
  have hlut := hn.1
  have hlo1 := (hwf _ (gt_mem d hlut)).2.2.2.1
  obtain ⟨hip, _, _, _, _, _, hst, hnst⟩ := hn.2.2.2.2.2.2 p
  unfold selLo selHi selGate selBase
  by_cases h : (rpin net rn j p).st = true
  · obtain ⟨_, _, hsg, _, hssel, _, htop, _, _⟩ := hst h
    have hmem : sb ∈ (rpin net rn j p).ssel := by unfold selLits at hsb; simpa [h] using hsb
    simp only [h, ↓reduceIte]
    have w0 := shift1 (wf_warp hsat hlut hip) hlo1
    have w1 := Events5.warp_comp (tau_warp hsat _ (chkT_pathOK _ _ _ _ _ htop)) w0
    exact Events5.warp_comp (wf_warp hsat hsg (hssel sb hmem)) w1
  · have h' : (rpin net rn j p).st = false := by simpa using h
    obtain ⟨_, hfold, _, _⟩ := hnst h'
    have hmem : sb ∈ (rpin net rn j p).fold := by unfold selLits at hsb; simpa [h] using hsb
    simp only [h', Bool.false_eq_true, ↓reduceIte]
    exact shift1 (wf_warp hsat hlut (hfold sb hmem)) hlo1

end

/-! ## design_verdict8 with SelOK replaced by B's steer conditions at the real pins -/

section
variable {N : Nat} {d : Design} {net : Net4 N} {b : Bands4 net} {rn : Fin N → RNode} {rank : Fin N → Nat}
  {rw fuel : Nat} {x : Fin d.n → Sig} (hsat : SatPinW d plG x)
  (h0 : ∀ t, x (d.wire 0) t = false) (h1 : ∀ t, x (d.wire 1) t = true)
  {T : Nat} (hT : 1 ≤ T) (hrst : ∀ t, x (d.wire rw) t = decide (t < T))
  {cv : Fin N → Sig} (hr : Recog6 d net b rn rank rw fuel) (hOK : net.OK7) (harb : HARB7 net b rn x cv)

include hsat h0 h1 hT hrst hr hOK harb

/-- `design_beh8`, also exposing what a real filtered pin's select is: `svOf`. -/
theorem design_beh8_sv (sel : Nat → Nat → Bool) :
    ∃ bh : Beh7 net b sel, (∀ j t, bh.c j t = ccOf rn x cv j t) ∧
      (∀ j p s, bh.gc j p s = gcnt net sel j p (bh.cm j p s)) ∧
      (∀ j, (rn j).virt = false → ∀ t, bh.c j t = x (d.wire (gt d (rn j).lut).out) t) ∧
      (∀ j, (rn j).virt = false → ∀ p s, bh.sv j p s = svOf (rn := rn) hsat j p s) := by
  have mg0 : ∀ j, net.mg j = true → ccOf rn x cv j 0 = false := fun j hm => by
    rw [init0_7 hsat h0 h1 hT hrst hr hOK harb j]; exact ((hOK j ⟨0, net.ar_pos j⟩).2.2.2.1 hm).1
  refine ⟨beh8 sel (ndAll7 hsat h0 h1 hT hrst hr hOK harb) mg0, fun j t => rfl,
    beh8_gc sel (ndAll7 hsat h0 h1 hT hrst hr hOK harb) mg0, fun j hv t => ?_, fun j hv p s => ?_⟩
  · show ccOf rn x cv j t = _
    unfold ccOf; rw [hv, (hr.2 j hv).2.1]; rfl
  · show (ndAll7 hsat h0 h1 hT hrst hr hOK harb j).sv p s = _
    unfold ndAll7
    simp only [hv, Bool.false_eq_true, ↓reduceDIte]
    rfl

end

section
variable {N : Nat} {d : Design} {net : Net4 N} {b : Bands4 net} {rn : Fin N → RNode} {rank : Fin N → Nat}
  {rw fuel : Nat} {x : Fin d.n → Sig} {cv : Fin N → Sig}

/-- **`design_verdict8` with SelOK discharged at the real pins by B's steer conditions.**
Same checks and hypotheses as `design_verdict8`, except that `bh.SelOK` is replaced by:
* SelOK at the VIRTUAL filtered pins only (each arbiter grant's `ctl·[σ = b]` pin; part of
  H_ARB);
* at every REAL filtered pin `(j, p)` and select literal `sb` (gate input `sb.1` of
  `selGate`): transaction `k` of the pin's source starts no earlier than `R j p k`; the select
  bit's wire is `vb j p sb.1 k` from `S0 j p sb.1 k` on, as long as the source was in
  transaction `k` at most `hiC - selLo` before (B's H_S_STABLE with the open-ended hold of
  `selOK_of_hold`); B's per-pin setup `S0 + selHi ≤ R + loC` against every copy; and `sel`
  is the pattern function `selFn` of those bit values.
`selLo` / `selHi` are explicit band sums of the recognised netlist (steer gate + top path
+ stage LUT, or the stage LUT alone), so every premise is about the trace `x` and numbers. -/
theorem design_verdict8_sel (hr : Recog6 d net b rn rank rw fuel) (hOK : net.OK7)
    {parts : List (List Nat)} {log : List Ln} {J : Array Jd} (hJ : runLog net b parts log = some J)
    (back line : (j : Fin N) → Fin (net.ar j) → Nat) (xS xw : Fin N → Nat) (xa : Fin N → List Arm)
    (hl : List HLn) (gd : (j : Fin N) → Fin (net.ar j) → GD)
    (cp : (j : Fin N) → Fin (net.ar j) → Bool) (cxm : Fin N → Bool) (cl : (j : Fin N) → Fin (net.ar j) → Bool)
    (cg : (j : Fin N) → Fin (net.ar j) → Bool)
    (hcp : ∀ j p, cp j p = true → backOK7 net b J j p (back j p) = true)
    (hcx : ∀ m, cxm m = true → exclOK7 net b parts J m (xS m) (xa m) (xw m) = true)
    (hcl : ∀ j p, cl j p = true → lineOK7 net b J j p (line j p) = true)
    (hcg : ∀ j p, cg j p = true → guardOK8 net b parts J hl j p (gd j p) = true)
    (hsat : SatPinW d plG x) (h0 : ∀ t, x (d.wire 0) t = false) (h1 : ∀ t, x (d.wire 1) t = true)
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
        HDsub bh parts J hl →
        (∀ j p s, net.mg j = false → net.pk j p ≠ PK.guard → cp j p = false → bh.P j p s ≤ bh.M (bh.Q j s) j + 1) →
        (∀ m s, net.mg m = true → cxm m = false → fodd (net.ar m) (fun p => bh.P m p s) ≤ 1) →
        (∀ j p s, net.pk j p = PK.multi → cl j p = false → ContigF (net.nc j p) (bh.cm j p s)) →
        (∀ j p, net.pk j p = PK.guard → cg j p = false → GuardPin bh j p) →
        ∀ t j, (rn j).virt = false →
          x (d.wire (gt d (rn j).lut).out) t = Formal.Core.XAudit.Events.ph (net.v j) (bh.M t j)) := by
  obtain ⟨bh, hc, hgc, hreal, hsv⟩ := design_beh8_sv hsat h0 h1 hT hrst hr hOK harb sel
  refine ⟨bh, hc, hgc, fun hp hvirt R S0 vb hwin hsetup hstab hsel hH rB rX rL rG t j hv => ?_⟩
  have hselok : bh.SelOK := by
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
  rw [← hreal j hv t]
  exact verdict8 bh hOK hp hJ back line xS xw xa hl gd cp cxm cl cg hcp hcx hcl hcg
    (fun j p s _ => hgc j p s) rB rX rL rG hselok hH t j

end

end Formal.Core.XAudit.Events8Bridge
