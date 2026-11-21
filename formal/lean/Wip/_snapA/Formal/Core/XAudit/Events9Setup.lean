import Formal.Core.XAudit.Events9SelJ

/-!
# Formal.Core.XAudit.Events9Setup — H_SEL_O and H_SEL_SETUP as checked rows

Probe E9Setup (shard A). Notes: `formal/notes/A-e9setup.md`.

`Events9SelL.design_verdict9_selTP` (and through it `selT` / `selJ`) takes, per real select
literal, a time `O k` from which C's H_BUNDLE holds the select bus, with two trace hypotheses:
* **H_SEL_O**: by `O k` every request leaf's read has seen transaction `k`;
* **H_SEL_SETUP**: `O k + hi(rg) + selHi ≤ R k + loC` (source-anchored: `R k` a lower bound of
  the time the pin's source shows transaction `k`).

This file replaces both by a decidable row over the band file, with `O k` DEFINED as the first
time at which every request leaf's read shows transaction `k` (`Ofirst`: the request wire's
rise for transaction `k`, the earliest time H_BUNDLE can hold the bus), and the setup anchored
at a JUNCTION of the copy path instead of the source (no common-path pessimism):

* `sel_read_setJ` / `selAt_setJ`: `Events9PrefixSel.sel_read_split_at` / `selAt_split` with
  the setup premise stated against a second factorisation of the copy warp at a setup cut
  `scut`: `∀ r, M (tau bot' r) src = 2k+1 → S0 k + selHi ≤ r + (plo top' − 1)`.
* `firstUp`, `ReqUp`, `Ofirst` (+ `Ofirst_up`, `Ofirst_le`).
* **`suOK`** (decidable), two forms:
  - *wire form* (mux joins): the request tree is ONE leaf `(src, π)` and every copy path of the
    pin is `top ++ π` (it passes the request wire): a copy showing `k` at the request wire means
    the request has risen, so `O k ≤ r`; row `hi(rg) + selHi + 1 ≤ plo top`.
  - *stage form* (steer joins): the pin's source `J` is a real non-merge stage whose pin `jq`
    (offset 0; an AND line or a single-copy plain pin) reads every request leaf through
    `topJ ++ π_l`; `J` showing `k` at `u` means every leaf was read high at
    `tau topJ (F u + 1) ≤ u − plo topJ`; row (cut at the source)
    `hi(rg) + selHi + 1 ≤ plo topJ + plo full`.
* **`su_sound`**: `suOK` gives H_SEL_O at `Ofirst` and the junction setup inequality.

NOT covered: H_BUNDLE itself (C's, a hypothesis); that `Ofirst` is the moment the bus is
stable is exactly H_BUNDLE + the request tree identity (`treeOK`), nothing more: a select bus
that becomes valid BEFORE its request wire rises is credited nothing (the row is pessimistic
there, see notes §3). The rows use the certificate's bands (trusted parser).
-/

namespace Formal.Core.XAudit.Events9Setup

open Formal.Core
open Formal.Core.XAudit
open Formal.Core.TraceDiscrete (Sig Warp Mono)
open Formal.Core.XAudit.Events (ph)
open Formal.Core.XAudit.Events2Pin (SatPin)
open Formal.Core.XAudit.Events2 (fmin fmin_le)
open Formal.Core.XAudit.Events4 (andCnt)
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

/-! ## 1. One select read with a junction-anchored setup -/

/-- `sel_read_split_at` with the setup premise stated at a second factorisation
`gR = gC ∘ gU` of the copy warp (the setup cut): if every junction time `r` at which the copy's
lower part `gC` shows transaction `k` has `S0 k + Shi ≤ r + Ulo`, the select read at the sample
sees the stable value. -/
theorem sel_read_setJ {Slo Shi Tlo Thi Ulo Uhi Clo Chi : Nat} {gR gS gT gU : Nat → Nat} (gB gC : Nat → Nat)
    (wS : Warp Slo Shi gS) (wT : Warp Tlo Thi gT) (wU : Warp Ulo Uhi gU) (wC : Warp Clo Chi gC)
    (hfac : ∀ s, gR s = gB (gT s)) (hfacU : ∀ s, gR s = gC (gU s))
    (M : Nat → Nat) (hM0 : M 0 = 0)
    (xs : Sig) (v : Nat → Bool) (S0 : Nat → Nat) (s : Nat)
    (hset : ∀ k r, M (gC r) = 2 * k + 1 → S0 k + Shi ≤ r + Ulo)
    (hstab : ∀ k t r, t ≤ s → M (gB r) = 2 * k + 1 → S0 k ≤ t → t + Slo ≤ r + Thi → xs t = v k) :
    ∀ k, M (gR s) = 2 * k + 1 → xs (gS s) = v k := by
  intro k hm
  have hlh := warp_lo_le_hi wS
  have hmU : M (gC (gU s)) = 2 * k + 1 := by rw [← hfacU s]; exact hm
  have hsU : Ulo ≤ s := by
    rcases Nat.lt_or_ge s Ulo with hc | hc
    · have h1 : gU s = 0 := by have := wU.le_late s; omega
      have h2 : gC 0 = 0 := by have := wC.le_late 0; omega
      rw [h1, h2, hM0] at hmU; omega
    · exact hc
  have hU := hset k (gU s) hmU
  have u1 := wU.le_late s
  have b1 := wS.le_late s; have b2 := wS.early_le s
  have c2 := wT.early_le s
  rw [hfac s] at hm
  exact hstab k _ (gT s) (by omega) hm (by omega) (by omega)

section
variable {N : Nat} {d : Design} {net : Net4 N} {b : Bands4 net} {rn : Fin N → RNode} {rank : Fin N → Nat}
  {rw fuel : Nat} {x : Fin d.n → Sig} {sel : Nat → Nat → Bool}

theorem topP_lo1 (hr : Recog6 d net b rn rank rw fuel) (j : Fin N) (hvf : (rn j).virt = false)
    (p : Fin (net.ar j)) (i n : Nat) : 1 ≤ plo d (topP d net rn j p i n) := by
  have hn := hr.2 j hvf
  unfold topP full
  simp only [List.take_succ_cons, plo]
  have := (hr.1 _ (gt_mem d hn.1)).2.2.2.1
  omega

theorem topP_ok (hr : Recog6 d net b rn rank rw fuel) (j : Fin N) (hvf : (rn j).virt = false)
    (p : Fin (net.ar j)) (i : Fin (net.nc j p)) (n : Nat) : pathOK d (topP d net rn j p i.val n) = true := by
  have hok := (full_ok hr.1 j (hr.2 j hvf) p i).1
  unfold topP; unfold pathOK at hok ⊢
  exact List.all_eq_true.mpr fun e he => List.all_eq_true.mp hok e (List.mem_of_mem_take he)

theorem botP_ok (hr : Recog6 d net b rn rank rw fuel) (j : Fin N) (hvf : (rn j).virt = false)
    (p : Fin (net.ar j)) (i : Fin (net.nc j p)) (n : Nat) : pathOK d (botP d net rn j p i.val n) = true := by
  have hok := (full_ok hr.1 j (hr.2 j hvf) p i).1
  unfold botP; unfold pathOK at hok ⊢
  exact List.all_eq_true.mpr fun e he => List.all_eq_true.mp hok e (List.mem_of_mem_drop he)

/-- **`selAt_setJ`**: `Events9PrefixSel.selAt_split` with the setup premise anchored at a
setup cut `scut` of each copy (per literal), instead of the source-anchored pair `hwin` /
`hsetup`. -/
theorem selAt_setJ (hsat : SatPin d plG x) (hr : Recog6 d net b rn rank rw fuel)
    (bh : Beh7 net b sel)
    (hsv : ∀ j, (rn j).virt = false → ∀ p s, bh.sv j p s = svOf (rn := rn) hsat j p s)
    (hG : ∀ j, (rn j).virt = false → ∀ p i s, bh.G j p i s = tau hsat (full net rn j p i.val) (s + 1))
    (hvirt : ∀ j p s (i : Fin (net.nc j p)), (rn j).virt = true → net.pk j p = PK.filt →
      bh.M (bh.G j p i s) (net.src j p) % 2 = 1 →
      bh.sv j p s = sel (net.grp j p) (bh.M (bh.G j p i s) (net.src j p) / 2))
    (cut : (j : Fin N) → Fin (net.ar j) → Nat → Nat)
    (scut : (j : Fin N) → Fin (net.ar j) → Nat → Nat → Nat)
    (S0 : (j : Fin N) → Fin (net.ar j) → Nat → Nat → Nat)
    (vb : (j : Fin N) → Fin (net.ar j) → Nat → Nat → Bool)
    (hsetJ : ∀ j p (sb : Nat × Bool) (i : Fin (net.nc j p)) k r, (rn j).virt = false → net.pk j p = PK.filt →
      sb ∈ selLits net rn j p →
      bh.M (tau hsat (botP d net rn j p i.val (scut j p sb.1 i.val)) r) (net.src j p) = 2 * k + 1 →
      S0 j p sb.1 k + selHi d net rn j p ≤ r + (plo d (topP d net rn j p i.val (scut j p sb.1 i.val)) - 1))
    (hsel : ∀ j p k, (rn j).virt = false → net.pk j p = PK.filt →
      sel (net.grp j p) k = selFn (selLits net rn j p) (fun i => vb j p i k))
    (s : Nat)
    (hstab : ∀ j p (sb : Nat × Bool) (i : Fin (net.nc j p)) k t r, t ≤ s → (rn j).virt = false →
      net.pk j p = PK.filt → sb ∈ selLits net rn j p →
      bh.M (tau hsat (botP d net rn j p i.val (cut j p i.val)) r) (net.src j p) = 2 * k + 1 →
      S0 j p sb.1 k ≤ t → t + selLo d net rn j p ≤ r + (phi d (topP d net rn j p i.val (cut j p i.val)) - 1) →
      x (d.wire ((gt d (selGate net rn j p)).ins.getD sb.1 0)) t = vb j p sb.1 k) :
    SelAt bh s := by
  intro j p i hk hodd
  by_cases hvj : (rn j).virt = true
  · exact hvirt j p s i hvj hk hodd
  · have hvf : (rn j).virt = false := by simpa using hvj
    have hk2 : bh.M (bh.G j p i s) (net.src j p) =
        2 * (bh.M (bh.G j p i s) (net.src j p) / 2) + 1 := by omega
    have hn := hr.2 j hvf
    have wT := shift1 (tau_warp hsat _ (topP_ok hr j hvf p i (cut j p i.val))) (topP_lo1 hr j hvf p i.val _)
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
    have wU := shift1 (tau_warp hsat _ (topP_ok hr j hvf p i (scut j p sb.1 i.val)))
      (topP_lo1 hr j hvf p i.val _)
    have wC := tau_warp hsat _ (botP_ok hr j hvf p i (scut j p sb.1 i.val))
    have hfacU : ∀ s', bh.G j p i s' =
        tau hsat (botP d net rn j p i.val (scut j p sb.1 i.val))
          ((fun s => tau hsat (topP d net rn j p i.val (scut j p sb.1 i.val)) (s + 1)) s') := by
      intro s'
      rw [hG j hvf p i s']
      unfold topP botP
      rw [← tau_append, List.take_append_drop]
    exact sel_read_setJ _ _ (sel_warp hsat hr.1 j hn p sb hsb) wT wU wC hfac hfacU
      (fun u => bh.M u (net.src j p)) (bh.M_zero _)
      (x (d.wire ((gt d (selGate net rn j p)).ins.getD sb.1 0))) (vb j p sb.1)
      (fun k => S0 j p sb.1 k) s
      (fun k r h => hsetJ j p sb i k r hvf hk hsb h)
      (fun k t r ht h1 h2 h3 => hstab j p sb i k t r ht hvf hk hsb h1 h2 h3) _ hk2

end

/-! ## 2. The first time the request has risen -/

section F
variable (P : Nat → Prop) [DecidablePred P]

/-- Scan `a, a+1, …, a+n` for the first time `P` holds (`a + n` if none before). -/
def firstUp : Nat → Nat → Nat
  | a, 0 => a
  | a, n + 1 => if P a then a else firstUp (a + 1) n

theorem firstUp_P : ∀ n a, P (a + n) → P (firstUp P a n)
  | 0, a, h => by simpa [firstUp] using h
  | n + 1, a, h => by
      unfold firstUp
      split
      · assumption
      · exact firstUp_P n (a + 1) (by rw [show a + 1 + n = a + (n + 1) by omega]; exact h)

theorem firstUp_le : ∀ n a t, a ≤ t → P t → firstUp P a n ≤ t
  | 0, a, t, h, _ => by simpa [firstUp] using h
  | n + 1, a, t, h, hp => by
      unfold firstUp
      split
      · exact h
      · rename_i hn
        have : a ≠ t := fun e => hn (e ▸ hp)
        exact firstUp_le n (a + 1) t (by omega) hp

end F

section
variable {N : Nat} {d : Design} {net : Net4 N} {b : Bands4 net} {sel : Nat → Nat → Bool}
  {x : Fin d.n → Sig}

/-- Every request leaf's read shows (at least) transaction `k` at time `t`. -/
def ReqUp (bh : Beh7 net b sel) (hsat : SatPin d plG x) (ls : List (Nat × Path)) (k t : Nat) : Prop :=
  ∀ l ∈ ls, 2 * k + 1 ≤ Mn bh (tau hsat l.2 t) l.1

open Classical in
/-- **`Ofirst`**: the first time every request leaf's read shows transaction `k` (0 if never):
the request wire's rise for transaction `k` in count terms. -/
noncomputable def Ofirst (bh : Beh7 net b sel) (hsat : SatPin d plG x) (ls : List (Nat × Path)) (k : Nat) : Nat :=
  if h : ∃ t, ReqUp bh hsat ls k t then firstUp (ReqUp bh hsat ls k) 0 (Classical.choose h) else 0

theorem Ofirst_up (bh : Beh7 net b sel) (hsat : SatPin d plG x) (ls : List (Nat × Path)) (k : Nat)
    (h : ∃ t, ReqUp bh hsat ls k t) : ReqUp bh hsat ls k (Ofirst bh hsat ls k) := by
  classical
  unfold Ofirst
  rw [dif_pos h]
  exact firstUp_P _ _ 0 (by rw [Nat.zero_add]; exact Classical.choose_spec h)

theorem Ofirst_le (bh : Beh7 net b sel) (hsat : SatPin d plG x) (ls : List (Nat × Path)) (k t : Nat)
    (h : ReqUp bh hsat ls k t) : Ofirst bh hsat ls k ≤ t := by
  classical
  unfold Ofirst
  rw [dif_pos ⟨t, h⟩]
  exact firstUp_le _ _ 0 t (Nat.zero_le _) h

end

/-! ## 3. The setup row -/

/-- Setup data of one literal: the form (`fw = true`: wire form; `false`: stage form) and, for
the stage form, the pin `jq` of the source that reads the request, the length `tl` of the
shared top `topJ`, and per request leaf the copy of `jq` that reads it. -/
structure SU where
  fw : Bool := true
  jq : Nat := 0
  tl : Nat := 0
  lc : List Nat := []
  deriving Repr, Inhabited

section
variable {N : Nat} (d : Design) (net : Net4 N) (rn : Fin N → RNode)

/-- Each request leaf `l` (positionally with its copy index `c`) is read by copy `c` of pin `q`
of `J` through `topJ ++ l.2`, and `l`'s node is that pin's source. -/
def leafCopiesOK (J : Fin N) (q : Fin (net.ar J)) (topJ : Path) : List (Nat × Path) → List Nat → Bool
  | [], _ => true
  | l :: ls, c :: cs => decide (c < net.nc J q) && decide (full net rn J q c = topJ ++ l.2) &&
      decide (l.1 = (net.src J q).val) && leafCopiesOK J q topJ ls cs
  | _ :: _, [] => false

theorem leafCopiesOK_mem {J : Fin N} {q : Fin (net.ar J)} {topJ : Path} :
    ∀ (ls : List (Nat × Path)) (cs : List Nat), leafCopiesOK net rn J q topJ ls cs = true →
      ∀ l ∈ ls, ∃ c : Fin (net.nc J q), full net rn J q c.val = topJ ++ l.2 ∧ l.1 = (net.src J q).val
  | [], _, _, l, hl => absurd hl (by simp)
  | _ :: _, [], h, _, _ => by simp [leafCopiesOK] at h
  | l0 :: ls, c :: cs, h, l, hl => by
      simp only [leafCopiesOK, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨hc, hf⟩, hs⟩, hr⟩ := h
      rcases List.mem_cons.mp hl with e | e
      · subst e; exact ⟨⟨c, hc⟩, hf, hs⟩
      · exact leafCopiesOK_mem ls cs hr l e

/-- The source pin of the stage form: `J` real, non-merge, pin `q` with offset 0, an AND line or
a single-copy plain pin (a pin whose count at least `2k+1` forces EVERY copy to `2k+1`). -/
def stagePinOK (J : Fin N) (q : Fin (net.ar J)) : Bool :=
  decide ((rn J).virt = false) && decide (net.mg J = false) && decide (net.off J q = 0) &&
  ((decide (net.pk J q = PK.multi) && net.op J q) || (decide (net.pk J q = PK.plain) && decide (net.nc J q = 1)))

/-- **The setup row of one real select literal** (decidable). `X = hi(rg) + selHi` is the
latest the select gate can still be reading the bus value of before `O k`, relative to a
sample. Wire form: the request tree is the one leaf `(src, bot)` of every copy's setup cut, and
`X + 1 ≤ plo top`. Stage form: see `stagePinOK`, `leafCopiesOK`; every copy is cut at the
source (`bot = []`) and `X + 1 ≤ plo topJ + plo top`. -/
def suOK (j : Fin N) (p : Fin (net.ar j)) (e : SelEnt) (ls : List (Nat × Path)) (scut : Nat → Nat) (u : SU) : Bool :=
  if u.fw then
    (List.finRange (net.nc j p)).all fun i =>
      decide (ls = [((net.src j p).val, botP d net rn j p i.val (scut i.val))]) &&
      decide ((gt d e.rg).hi + selHi d net rn j p + 1 ≤ plo d (topP d net rn j p i.val (scut i.val)))
  else
    decide (ls ≠ []) &&
    (if hq : u.jq < net.ar (net.src j p) then
      stagePinOK net rn (net.src j p) ⟨u.jq, hq⟩ &&
      leafCopiesOK net rn (net.src j p) ⟨u.jq, hq⟩ ((full net rn (net.src j p) ⟨u.jq, hq⟩ (u.lc.headD 0)).take u.tl) ls u.lc &&
      (List.finRange (net.nc j p)).all fun i =>
        decide (botP d net rn j p i.val (scut i.val) = []) &&
        decide ((gt d e.rg).hi + selHi d net rn j p + 1 ≤
          plo d ((full net rn (net.src j p) ⟨u.jq, hq⟩ (u.lc.headD 0)).take u.tl) +
          plo d (topP d net rn j p i.val (scut i.val)))
    else false)

/-- The setup margin of one copy (ps; printed by the executable). -/
def suMargin (j : Fin N) (p : Fin (net.ar j)) (e : SelEnt) (scut : Nat → Nat) (u : SU) (i : Nat) : Int :=
  let X : Int := (gt d e.rg).hi + selHi d net rn j p + 1
  if u.fw then (plo d (topP d net rn j p i (scut i)) : Int) - X
  else if hq : u.jq < net.ar (net.src j p) then
    (plo d ((full net rn (net.src j p) ⟨u.jq, hq⟩ (u.lc.headD 0)).take u.tl) : Int) +
      plo d (topP d net rn j p i (scut i)) - X
  else -1000000000

end

section
variable {N : Nat} {d : Design} {net : Net4 N} {b : Bands4 net} {rn : Fin N → RNode} {rank : Fin N → Nat}
  {rw fuel : Nat} {x : Fin d.n → Sig} {sel : Nat → Nat → Bool}

/-- A non-merge stage whose AND-line (or single-copy plain) pin `q` (offset 0) has count at least
`2k+1` at `u` has read EVERY copy of `q` at least `2k+1` at its sample `F u`. -/
theorem stage_copies (bh : Beh7 net b sel) (J : Fin N) (q : Fin (net.ar J))
    (hst : stagePinOK net rn J q = true) {k u : Nat} (hu : 2 * k + 1 ≤ bh.M u J) :
    1 ≤ u ∧ ∀ c : Fin (net.nc J q), 2 * k + 1 ≤ bh.cm J q (bh.F J u) c := by
  simp only [stagePinOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hst
  obtain ⟨⟨⟨_, hmg⟩, hoff⟩, hpk⟩ := hst
  have hu1 : 1 ≤ u := by
    rcases Nat.eq_zero_or_pos u with h | h
    · subst h; rw [bh.M_zero] at hu; omega
    · exact h
  refine ⟨hu1, ?_⟩
  rw [bh.M_eq u J hu1] at hu
  unfold Beh7.E at hu
  simp only [hmg, Bool.false_eq_true, ite_false] at hu
  split at hu
  · omega
  · have hP := Nat.le_trans hu (fmin_le _ (fun p => bh.P J p (bh.F J u)) q)
    unfold Beh7.P Beh7.pc at hP
    rw [hoff, Nat.add_zero] at hP
    intro c
    rcases hpk with ⟨hk, hop⟩ | ⟨hk, hnc⟩
    · simp only [hk, hop, ite_true] at hP
      have h1 := fmin_le _ (bh.cm J q (bh.F J u)) c
      unfold andCnt at hP
      have : 2 * k + 1 ≤ fmin _ (bh.cm J q (bh.F J u)) := by omega
      omega
    · simp only [hk] at hP
      have h1 := fmax_le _ (bh.cm J q (bh.F J u)) (net.nc_pos J q) (bh.cm J q (bh.F J u) c) (by
        intro i
        have : i = c := Fin.ext (by have := i.isLt; have := c.isLt; omega)
        subst this; exact Nat.le_refl _)
      omega

/-- **`su_sound`**: a passing setup row gives, for `O = Ofirst`, H_SEL_O (if the source ever
shows transaction `k`, every request leaf is read high at `O k`) and the junction-anchored
setup inequality of every copy. -/
theorem su_sound (hsat : SatPin d plG x) (hr : Recog6 d net b rn rank rw fuel) (bh : Beh7 net b sel)
    (hG : ∀ j, (rn j).virt = false → ∀ p i s, bh.G j p i s = tau hsat (full net rn j p i.val) (s + 1))
    (j : Fin N) (hvf : (rn j).virt = false) (p : Fin (net.ar j)) (e : SelEnt) (ls : List (Nat × Path))
    (hls : ∀ l ∈ ls, pathOK d l.2 = true) (scut : Nat → Nat) (u : SU)
    (h : suOK d net rn j p e ls scut u = true) :
    (∀ k u0, bh.M u0 (net.src j p) = 2 * k + 1 → ReqUp bh hsat ls k (Ofirst bh hsat ls k)) ∧
    (∀ (i : Fin (net.nc j p)) k r,
      bh.M (tau hsat (botP d net rn j p i.val (scut i.val)) r) (net.src j p) = 2 * k + 1 →
      Ofirst bh hsat ls k + (gt d e.rg).hi + selHi d net rn j p ≤ r + (plo d (topP d net rn j p i.val (scut i.val)) - 1)) := by
  unfold suOK at h
  split at h
  · -- wire form
    rename_i hfw
    have hall := List.all_eq_true.mp h
    have hc : ∀ i : Fin (net.nc j p), ls = [((net.src j p).val, botP d net rn j p i.val (scut i.val))] ∧
        (gt d e.rg).hi + selHi d net rn j p + 1 ≤ plo d (topP d net rn j p i.val (scut i.val)) := by
      intro i
      have := hall i (List.mem_finRange i)
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      exact this
    refine ⟨fun k u0 hu0 => ?_, fun i k r hm => ?_⟩
    · apply Ofirst_up
      let i0 : Fin (net.nc j p) := ⟨0, net.nc_pos j p⟩
      obtain ⟨hl0, _⟩ := hc i0
      refine ⟨u0 + phi d (botP d net rn j p i0.val (scut i0.val)), fun l hl => ?_⟩
      rw [hl0, List.mem_singleton] at hl
      subst hl
      have wB := tau_warp hsat _ (botP_ok hr j hvf p i0 (scut i0.val))
      have h1 := wB.early_le (u0 + phi d (botP d net rn j p i0.val (scut i0.val)))
      rw [Mn_fin]
      have := bh.M_mono (tau hsat (botP d net rn j p i0.val (scut i0.val))
        (u0 + phi d (botP d net rn j p i0.val (scut i0.val)))) (net.src j p) u0 (by omega)
      dsimp only
      omega
    · obtain ⟨hl, hX⟩ := hc i
      have hup : ReqUp bh hsat ls k r := by
        intro l hl'
        rw [hl, List.mem_singleton] at hl'
        subst hl'
        rw [Mn_fin, hm]; exact Nat.le_refl _
      have := Ofirst_le bh hsat ls k r hup
      omega
  · -- stage form
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hne, h2⟩ := h
    split at h2
    · rename_i hq
      simp only [Bool.and_eq_true] at h2
      obtain ⟨⟨hst, hlc⟩, hall⟩ := h2
      obtain ⟨topJ, htop⟩ : ∃ t, t = (full net rn (net.src j p) ⟨u.jq, hq⟩ (u.lc.headD 0)).take u.tl := ⟨_, rfl⟩
      rw [← htop] at hlc hall
      have hJv : (rn (net.src j p)).virt = false := by
        simp only [stagePinOK, Bool.and_eq_true, decide_eq_true_eq] at hst; exact hst.1.1.1
      -- the key fact: J showing k at u means every leaf was read high at tau topJ (F u + 1)
      have key : ∀ k u', 2 * k + 1 ≤ bh.M u' (net.src j p) →
          ReqUp bh hsat ls k (tau hsat topJ (bh.F (net.src j p) u' + 1)) ∧ tau hsat topJ (bh.F (net.src j p) u' + 1) + plo d topJ ≤ u' := by
        intro k u' hu'
        obtain ⟨hu1, hcp⟩ := stage_copies bh (net.src j p) ⟨u.jq, hq⟩ hst hu'
        have hup : ReqUp bh hsat ls k (tau hsat topJ (bh.F (net.src j p) u' + 1)) := by
          intro l hl
          obtain ⟨c, hfull, hsrc⟩ := leafCopiesOK_mem net rn ls u.lc hlc l hl
          have := hcp c
          unfold Beh7.cm at this
          rw [hG (net.src j p) hJv ⟨u.jq, hq⟩ c, hfull, tau_append] at this
          rw [hsrc, Mn_fin]
          exact this
        refine ⟨hup, ?_⟩
        -- pathOK of topJ: a prefix of a full copy path
        obtain ⟨l0, hl0⟩ : ∃ l0, l0 ∈ ls := by
          cases ls with
          | nil => exact absurd rfl hne
          | cons a _ => exact ⟨a, List.mem_cons_self⟩
        obtain ⟨c0, hf0, _⟩ := leafCopiesOK_mem net rn ls u.lc hlc l0 hl0
        have hok := (full_ok hr.1 (net.src j p) (hr.2 (net.src j p) hJv) ⟨u.jq, hq⟩ c0).1
        rw [hf0] at hok
        have htopok : pathOK d topJ = true := by
          unfold pathOK at hok ⊢
          exact List.all_eq_true.mpr fun e' he => List.all_eq_true.mp hok e' (List.mem_append_left _ he)
        have wJ := tau_warp hsat _ htopok
        have a1 := wJ.le_late (bh.F (net.src j p) u' + 1)
        have a2 := bh.F_lt (net.src j p) u' hu1
        -- the read time is positive (a leaf is high there)
        have hpos : 1 ≤ tau hsat topJ (bh.F (net.src j p) u' + 1) := by
          rcases Nat.eq_zero_or_pos (tau hsat topJ (bh.F (net.src j p) u' + 1)) with hz | hz
          · exfalso
            have h1 := hup l0 hl0
            have wl := tau_warp hsat _ (hls l0 hl0)
            have h2 : tau hsat l0.2 (tau hsat topJ (bh.F (net.src j p) u' + 1)) = 0 := by
              have := wl.le_late (tau hsat topJ (bh.F (net.src j p) u' + 1)); omega
            rw [h2] at h1
            have hM0 : Mn bh 0 l0.1 = 0 := by
              unfold Mn; split
              · exact bh.M_zero _
              · rfl
            omega
          · exact hz
        omega
      refine ⟨fun k u0 hu0 => Ofirst_up bh hsat ls k ⟨_, (key k u0 (Nat.le_of_eq hu0.symm)).1⟩, fun i k r hm => ?_⟩
      have hc := List.all_eq_true.mp hall i (List.mem_finRange i)
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨hb, hX⟩ := hc
      rw [hb] at hm
      simp only [tau] at hm
      obtain ⟨hup, hle⟩ := key k r (Nat.le_of_eq hm.symm)
      have := Ofirst_le bh hsat ls k _ hup
      omega
    · simp at h2

end

end Formal.Core.XAudit.Events9Setup
