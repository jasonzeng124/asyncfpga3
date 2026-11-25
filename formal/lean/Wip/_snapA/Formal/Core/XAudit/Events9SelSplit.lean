import Formal.Core.XAudit.Events9SelHold

/-!
# Formal.Core.XAudit.Events9SelSplit — the hold row without common-path pessimism

Probe E8SelC (shard A). Notes: `formal/notes/A-e8selc.md` §3.3.

`design_verdict9_selH` anchors the hold condition at the SOURCE node: the select must stay
until `hiC - selLo` after the last time the source shows transaction `k`, and the
acknowledge lag is measured from the source too. When the copy path and the acknowledge path
share a stretch (a mux join reads the select link's controller through that link's own
request delay line, which is also on the way to the select channel's acknowledge), the band
form counts the shared stretch twice, at its high end on the copy side and at its low end on
the lag side.

This file anchors at a JUNCTION wire `w` on the copy path instead. A copy's read is
`G s = tau full (s + 1)` (exposed from `design_beh8`'s realisation: `design_beh8_svG`), and
`full = top ++ bot` with `top = full.take (n + 1)` (`n` from the certificate, the stage LUT
always in `top`), so `G s = tau bot (tau top (s + 1))` (`tau_append`). Then

* `sel_read_split`: SelOK at one read from stability against `r + (phi top - 1)` for every
  `r` with `M (tau bot r) = 2k+1` (`r` is a time at `w`);
* `selOK_real_split`: `Beh7.SelOK` from those premises at every real filtered pin, copy and
  select literal;
* **`design_verdict9_selS`**: `design_verdict9` with SelOK at the real pins replaced by the
  checked map (`entOK`), C's H_BUNDLE of the mapped channel, H_SEL_SETUP (anchored at the
  source, as before), and the split hold row: a checked certificate path from the channel's
  acknowledge wire down to the junction wire `w` (`chainOK`), the band check
  `phi top - 1 + 1 ≤ plo π + selLo + lo(rg)` (`holdBandS`), and **H_ACK_LAG_w**: the channel
  stays mid-transaction from `O k` until `plo π` after every time `r` at which the junction
  shows transaction `k` (`M (tau bot r) src = 2k+1`).

With `n + 1 = full.length` (`bot = []`, `w` = the source's output) this is the source-anchored
row of `Events9SelHold`. `xselhold` takes, per copy, the junction that maximises the margin
among those whose `bot` is a chain of 1-input buffers (so `w` carries the source's value,
delayed: `w` at `r` IS the source at `tau bot r`).
NOT proved: H_ACK_LAG_w (as H_ACK_LAG: a causality statement, here from the junction).
-/

namespace Formal.Core.XAudit.Events9SelSplit

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
open Formal.Core.XAudit.Events9Sel
open Formal.Core.XAudit.Events9SelC
open Formal.Core.XAudit.Events9SelHold

/-! ## One select read against a factored copy warp -/

/-- **One select read, junction-anchored hold.** The copy warp factors as
`gR s = gB (gT s)` with `gT` a warp in `[Tlo, Thi]`; the select is `v k` at every
`t ≥ S0 k` with `t + Slo ≤ r + Thi` for some `r` at which `M (gB r) = 2k+1`. -/
theorem sel_read_split {Rlo Rhi Slo Shi Tlo Thi : Nat} {gR gS gT : Nat → Nat} (gB : Nat → Nat)
    (wR : Warp Rlo Rhi gR) (wS : Warp Slo Shi gS) (wT : Warp Tlo Thi gT) (hfac : ∀ s, gR s = gB (gT s))
    (M : Nat → Nat) (hM0 : M 0 = 0)
    (xs : Sig) (v : Nat → Bool) (R S0 : Nat → Nat)
    (hwin : ∀ u k, M u = 2 * k + 1 → R k ≤ u)
    (hsetup : ∀ k, S0 k + Shi ≤ R k + Rlo)
    (hstab : ∀ k t r, M (gB r) = 2 * k + 1 → S0 k ≤ t → t + Slo ≤ r + Thi → xs t = v k) :
    ∀ s k, M (gR s) = 2 * k + 1 → xs (gS s) = v k := by
  intro s k hm
  have hlh := warp_lo_le_hi wS
  have hlo : Rlo ≤ s := by
    rcases Nat.lt_or_ge s Rlo with hc | hc
    · have : gR s = 0 := by have := wR.le_late s; omega
      rw [this, hM0] at hm; omega
    · exact hc
  have a1 := wR.le_late s
  have b1 := wS.le_late s; have b2 := wS.early_le s
  have c2 := wT.early_le s
  have hR := hwin _ k hm; have hS := hsetup k
  rw [hfac s] at hm
  exact hstab k _ (gT s) hm (by omega) (by omega)

/-! ## The realisation's copy warps -/

section
variable {N : Nat} {d : Design} {net : Net4 N} {b : Bands4 net} {rn : Fin N → RNode} {rank : Fin N → Nat}
  {rw fuel : Nat} {x : Fin d.n → Sig} (hsat : SatPin d plG x)
  (h0 : ∀ t, x (d.wire 0) t = false) (h1 : ∀ t, x (d.wire 1) t = true)
  {T : Nat} (hT : 1 ≤ T) (hrst : ∀ t, x (d.wire rw) t = decide (t < T))
  {cv : Fin N → Sig} (hr : Recog6 d net b rn rank rw fuel) (hOK : net.OK7) (harb : HARB7 net b rn x cv)

include hsat h0 h1 hT hrst hr hOK harb

/-- `design_beh8_sv`, also exposing every real copy warp: `G s = tau full (s + 1)`. -/
theorem design_beh8_svG (sel : Nat → Nat → Bool) :
    ∃ bh : Beh7 net b sel, (∀ j t, bh.c j t = ccOf rn x cv j t) ∧
      (∀ j p s, bh.gc j p s = gcnt net sel j p (bh.cm j p s)) ∧
      (∀ j, (rn j).virt = false → ∀ t, bh.c j t = x (d.wire (gt d (rn j).lut).out) t) ∧
      (∀ j, (rn j).virt = false → ∀ p s, bh.sv j p s = svOf (rn := rn) hsat j p s) ∧
      (∀ j, (rn j).virt = false → ∀ p i s, bh.G j p i s = tau hsat (full net rn j p i.val) (s + 1)) := by
  have mg0 : ∀ j, net.mg j = true → ccOf rn x cv j 0 = false := fun j hm => by
    rw [init0_7 hsat h0 h1 hT hrst hr hOK harb j]; exact ((hOK j ⟨0, net.ar_pos j⟩).2.2.2.1 hm).1
  refine ⟨beh8 sel (ndAll7 hsat h0 h1 hT hrst hr hOK harb) mg0, fun j t => rfl,
    beh8_gc sel (ndAll7 hsat h0 h1 hT hrst hr hOK harb) mg0, fun j hv t => ?_, fun j hv p s => ?_,
    fun j hv p i s => ?_⟩
  · show ccOf rn x cv j t = _
    unfold ccOf; rw [hv, (hr.2 j hv).2.1]; rfl
  · show (ndAll7 hsat h0 h1 hT hrst hr hOK harb j).sv p s = _
    unfold ndAll7
    simp only [hv, Bool.false_eq_true, ↓reduceDIte]
    rfl
  · show (ndAll7 hsat h0 h1 hT hrst hr hOK harb j).G p i s = _
    unfold ndAll7
    simp only [hv, Bool.false_eq_true, ↓reduceDIte]
    rfl

end

/-! ## SelOK with junction-anchored holds -/

section
variable {N : Nat} {d : Design} {net : Net4 N} {b : Bands4 net} {rn : Fin N → RNode} {rank : Fin N → Nat}
  {rw fuel : Nat} {x : Fin d.n → Sig} {sel : Nat → Nat → Bool}

/-- The top part of copy `i` of pin `p` (stage LUT plus the first `n` hops). -/
def topP (d : Design) (net : Net4 N) (rn : Fin N → RNode) (j : Fin N) (p : Fin (net.ar j)) (i n : Nat) : Path :=
  (full net rn j p i).take (n + 1)

/-- The rest of the copy, from the junction wire down to the source's output. -/
def botP (d : Design) (net : Net4 N) (rn : Fin N → RNode) (j : Fin N) (p : Fin (net.ar j)) (i n : Nat) : Path :=
  (full net rn j p i).drop (n + 1)

theorem selOK_real_split (hsat : SatPin d plG x) (hr : Recog6 d net b rn rank rw fuel)
    (bh : Beh7 net b sel)
    (hsv : ∀ j, (rn j).virt = false → ∀ p s, bh.sv j p s = svOf (rn := rn) hsat j p s)
    (hG : ∀ j, (rn j).virt = false → ∀ p i s, bh.G j p i s = tau hsat (full net rn j p i.val) (s + 1))
    (hvirt : ∀ j p s (i : Fin (net.nc j p)), (rn j).virt = true → net.pk j p = PK.filt →
      bh.M (bh.G j p i s) (net.src j p) % 2 = 1 →
      bh.sv j p s = sel (net.grp j p) (bh.M (bh.G j p i s) (net.src j p) / 2))
    (cut : (j : Fin N) → Fin (net.ar j) → Nat → Nat)
    (R : (j : Fin N) → Fin (net.ar j) → Nat → Nat)
    (S0 : (j : Fin N) → Fin (net.ar j) → Nat → Nat → Nat)
    (vb : (j : Fin N) → Fin (net.ar j) → Nat → Nat → Bool)
    (hwin : ∀ j p u k, (rn j).virt = false → net.pk j p = PK.filt →
      bh.M u (net.src j p) = 2 * k + 1 → R j p k ≤ u)
    (hsetup : ∀ j p (sb : Nat × Bool) (i : Fin (net.nc j p)) k, (rn j).virt = false → net.pk j p = PK.filt →
      sb ∈ selLits net rn j p → S0 j p sb.1 k + selHi d net rn j p ≤ R j p k + b.loC j p i)
    (hstab : ∀ j p (sb : Nat × Bool) (i : Fin (net.nc j p)) k t r, (rn j).virt = false →
      net.pk j p = PK.filt → sb ∈ selLits net rn j p →
      bh.M (tau hsat (botP d net rn j p i.val (cut j p i.val)) r) (net.src j p) = 2 * k + 1 →
      S0 j p sb.1 k ≤ t → t + selLo d net rn j p ≤ r + (phi d (topP d net rn j p i.val (cut j p i.val)) - 1) →
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
    have hn := hr.2 j hvf
    have hok := (full_ok hr.1 j hn p i).1
    have htop : pathOK d (topP d net rn j p i.val (cut j p i.val)) = true := by
      unfold topP; unfold pathOK at hok ⊢
      exact List.all_eq_true.mpr fun e he => List.all_eq_true.mp hok e (List.mem_of_mem_take he)
    have hlo1 : 1 ≤ plo d (topP d net rn j p i.val (cut j p i.val)) := by
      unfold topP full
      simp only [List.take_succ_cons, plo]
      have := (hr.1 _ (gt_mem d hn.1)).2.2.2.1
      omega
    have wT := shift1 (tau_warp hsat _ htop) hlo1
    have hfac : ∀ s', bh.G j p i s' =
        tau hsat (botP d net rn j p i.val (cut j p i.val))
          ((fun s => tau hsat (topP d net rn j p i.val (cut j p i.val)) (s + 1)) s') := by
      intro s'
      rw [hG j hvf p i s']
      unfold topP botP
      rw [← tau_append, List.take_append_drop]
    rw [hsv j hvf p s, svOf_shape hsat j p s, hsel j p _ hvf hk]
    apply selFn_congr
    intro sb hsb
    exact sel_read_split _ (bh.wG j p i) (sel_warp hsat hr.1 j hn p sb hsb) wT hfac
      (fun u => bh.M u (net.src j p)) (bh.M_zero _)
      (x (d.wire ((gt d (selGate net rn j p)).ins.getD sb.1 0))) (vb j p sb.1) (R j p)
      (fun k => S0 j p sb.1 k) (fun u k h => hwin j p u k hvf hk h)
      (fun k => hsetup j p sb i k hvf hk hsb)
      (fun k t r h1 h2 h3 => hstab j p sb i k t r hvf hk hsb h1 h2 h3) s _ hk2

end

/-! ## The split hold row and the verdict -/

section
variable {N : Nat} (d : Design) (net : Net4 N) (rn : Fin N → RNode)

/-- The junction wire of copy `i` cut after `n + 1` elements: the input wire of the last
element of `topP` (the output of the first element of `botP`, or the source's output). -/
def junW (j : Fin N) (p : Fin (net.ar j)) (i n : Nat) : Nat :=
  match (topP d net rn j p i n).getLast? with
  | some (g, k) => (gt d g).ins.getD k 0
  | none => 0

/-- **The split hold band check** of one select literal and copy (decidable). -/
def holdBandS (j : Fin N) (p : Fin (net.ar j)) (e : SelEnt) (i n D : Nat) : Bool :=
  decide (phi d (topP d net rn j p i n) - 1 + 1 ≤ D + selLo d net rn j p + (gt d e.rg).lo)

end

section
variable {N : Nat} {d : Design} {net : Net4 N} {b : Bands4 net} {rn : Fin N → RNode} {rank : Fin N → Nat}
  {rw fuel : Nat} {x : Fin d.n → Sig} {cv : Fin N → Sig}

/-- **`design_verdict9` with junction-anchored hold rows.** As `design_verdict9_selH`, but the
hold row of every real filtered pin `(j, p)`, copy `i` and select literal `sb` is cut at the
junction after `cut j p i + 1` elements of the copy path: a checked path `π j p i sb.1` from
the mapped channel's acknowledge wire down to the junction wire (`chainOK`), the checked band
`phi top - 1 + 1 ≤ plo π + selLo + lo(rg)` (`holdBandS`), and **H_ACK_LAG_w**: the channel stays
mid-transaction from `O k` until `plo π` after every `r` with `M (tau bot r) src = 2k+1`. -/
theorem design_verdict9_selS (hr : Recog6 d net b rn rank rw fuel) (hOK : net.OK7)
    {parts : List (List Nat)} {log : List Ln} {J : Array Jd} (hJ : runLog net b parts log = some J)
    (back line : (j : Fin N) → Fin (net.ar j) → Nat) (xS xw : Fin N → Nat) (xa : Fin N → List Arm)
    (hl : List HLn9) (gd : (j : Fin N) → Fin (net.ar j) → GD)
    (cp : (j : Fin N) → Fin (net.ar j) → Bool) (cxm : Fin N → Bool) (cl : (j : Fin N) → Fin (net.ar j) → Bool)
    (cg : (j : Fin N) → Fin (net.ar j) → Bool)
    (hcp : ∀ j p, cp j p = true → backOK7 net b J j p (back j p) = true)
    (hcx : ∀ m, cxm m = true → exclOK7 net b parts J m (xS m) (xa m) (xw m) = true)
    (hcl : ∀ j p, cl j p = true → lineOK7 net b J j p (line j p) = true)
    (hcg : ∀ j p, cg j p = true → guardOK8 net b parts J (hl.map (san J)) j p (gd j p) = true)
    (m : (j : Fin N) → Fin (net.ar j) → Nat → SelEnt) (cut : (j : Fin N) → Fin (net.ar j) → Nat → Nat)
    (π : (j : Fin N) → Fin (net.ar j) → Nat → Nat → Path)
    (hm : ∀ j p (sb : Nat × Bool), (rn j).virt = false → net.pk j p = PK.filt → sb ∈ selLits net rn j p →
      entOK d net rn j p sb.1 (m j p sb.1) = true)
    (hrow : ∀ j p (sb : Nat × Bool) (i : Fin (net.nc j p)), (rn j).virt = false → net.pk j p = PK.filt →
      sb ∈ selLits net rn j p →
      chainOK d (m j p sb.1).ak (junW d net rn j p i.val (cut j p i.val)) (π j p i.val sb.1) = true ∧
      holdBandS d net rn j p (m j p sb.1) i.val (cut j p i.val) (plo d (π j p i.val sb.1)) = true)
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
          (O : (j : Fin N) → Fin (net.ar j) → Nat → Nat → Nat),
        (∀ j p (sb : Nat × Bool), (rn j).virt = false → net.pk j p = PK.filt → sb ∈ selLits net rn j p →
          Formal.Net.Ops.Held ((m j p sb.1).ch x)) →
        (∀ j p (sb : Nat × Bool) (i : Fin (net.nc j p)) k r s, (rn j).virt = false →
          net.pk j p = PK.filt → sb ∈ selLits net rn j p →
          bh.M (tau hsat (botP d net rn j p i.val (cut j p i.val)) r) (net.src j p) = 2 * k + 1 →
          O j p sb.1 k ≤ s → s < r + plo d (π j p i.val sb.1) →
          Formal.Net.Ops.inTx ((m j p sb.1).ch x) s = true) →
        (∀ j p (sb : Nat × Bool) (i : Fin (net.nc j p)) k, (rn j).virt = false → net.pk j p = PK.filt →
          sb ∈ selLits net rn j p →
          O j p sb.1 k + (gt d (m j p sb.1).rg).hi + selHi d net rn j p ≤ R j p k + b.loC j p i) →
        (∀ j p u k, (rn j).virt = false → net.pk j p = PK.filt →
          bh.M u (net.src j p) = 2 * k + 1 → R j p k ≤ u) →
        (∀ j p k, (rn j).virt = false → net.pk j p = PK.filt →
          sel (net.grp j p) k = selFn (selLits net rn j p)
            (fun i => x (d.wire (m j p i).dw) (O j p i k))) →
        (∀ j p s, net.mg j = false → net.pk j p ≠ PK.guard → cp j p = false → bh.P j p s ≤ bh.M (bh.Q j s) j + 1) →
        (∀ m s, net.mg m = true → cxm m = false → fodd (net.ar m) (fun p => bh.P m p s) ≤ 1) →
        (∀ j p s, net.pk j p = PK.multi → cl j p = false → ContigF (net.nc j p) (bh.cm j p s)) →
        (∀ j p, net.pk j p = PK.guard → cg j p = false → GuardPin bh j p) →
        ∀ t j, (rn j).virt = false →
          x (d.wire (gt d (rn j).lut).out) t = Formal.Core.XAudit.Events.ph (net.v j) (bh.M t j)) := by
  obtain ⟨bh, hc, hgc, hreal, hsv, hG⟩ := design_beh8_svG hsat h0 h1 hT hrst hr hOK harb sel
  refine ⟨bh, hc, hgc, fun hp hvirt R O hheld hlag hsetup hwin hsel rB rX rL rG t j hv => ?_⟩
  let S0 : (j : Fin N) → Fin (net.ar j) → Nat → Nat → Nat :=
    fun j p i k => O j p i k + (gt d (m j p i).rg).hi
  let vb : (j : Fin N) → Fin (net.ar j) → Nat → Nat → Bool :=
    fun j p i k => x (d.wire (m j p i).dw) (O j p i k)
  have hstab : ∀ j p (sb : Nat × Bool) (i : Fin (net.nc j p)) k t r, (rn j).virt = false →
      net.pk j p = PK.filt → sb ∈ selLits net rn j p →
      bh.M (tau hsat (botP d net rn j p i.val (cut j p i.val)) r) (net.src j p) = 2 * k + 1 →
      S0 j p sb.1 k ≤ t → t + selLo d net rn j p ≤ r + (phi d (topP d net rn j p i.val (cut j p i.val)) - 1) →
      x (d.wire ((gt d (selGate net rn j p)).ins.getD sb.1 0)) t = vb j p sb.1 k := by
    intro j p sb i k t r hvf hk hsb hu ht htu
    obtain ⟨hg, hb, hin, hout, hw⟩ := entOK_spec d net rn (hm j p sb hvf hk hsb)
    have hband := of_decide_eq_true (hrow j p sb i hvf hk hsb).2
    exact stab_of_held hsat h0 h1 hg hb hin hout hw (hheld j p sb hvf hk hsb)
      (fun r => bh.M (tau hsat (botP d net rn j p i.val (cut j p i.val)) r) (net.src j p)) (O j p sb.1)
      (selLo d net rn j p) (phi d (topP d net rn j p i.val (cut j p i.val)) - 1)
      (tx_of_lag hband (fun k r s h1 h2 h3 => hlag j p sb i k r s hvf hk hsb h1 h2 h3)) k t r hu ht htu
  have hselok : bh.SelOK :=
    selOK_real_split hsat hr bh hsv hG hvirt cut R S0 vb hwin
      (fun j p sb i k hvf hk hsb => hsetup j p sb i k hvf hk hsb) hstab hsel
  rw [← hreal j hv t]
  exact verdict9 bh hOK hp hJ back line xS xw xa hl gd cp cxm cl cg hcp hcx hcl hcg
    (fun j p s _ => hgc j p s) rB rX rL rG hselok t j

end

end Formal.Core.XAudit.Events9SelSplit
