import Formal.Core.XAudit.Events9Prefix
import Formal.Core.XAudit.Events9SelSplit

/-!
# Formal.Core.XAudit.Events9PrefixSel — H_ACK_LAG without circularity

Probe E8Causal (shard A). Notes: `formal/notes/A-e8causal.md` §2.

E8SelC's `design_verdict9_selS` (junction-anchored select rows) assumes **H_ACK_LAG_w**: the
mapped select channel stays mid-transaction (`req ∨ ack`) from `O k` until `D` after every
time `r` at which the junction shows transaction `k`. That is a statement about WIRES; the
counts that would prove it are tied to the wires only by the verdict, which itself needs
SelOK, which needs H_ACK_LAG_w (circular in the all-times form). This file breaks the
circle with the prefix verdict (`Events9Prefix.verdict9_upto`) and `causal_close`:

* `bufs`, `bufPath`, **`bufPath_val`**: a checked chain of 1-input buffers from wire `top`
  down to wire `bot` carries `bot`'s value: `x top t = x bot (tau κ t)` (the request wire of a
  select channel is the end of a delay line driven by a real node).
* `inTx_of_cnt`: a channel whose ack and req wires read reset-0 counts `A`, `R` with
  `2k+1 ≤ R ≤ A + 1` and `A ≤ 2k+1` is mid-transaction.
* `sel_read_split_at`, `selAt_split`: E8SelC's `sel_read_split` / `selOK_real_split` at ONE
  sample `s`, needing select stability only at times `t ≤ s`.
* **`design_verdict9_selP`**: the verdict with SelOK at the real filtered pins replaced by
  C's H_BUNDLE, H_SEL_SETUP, H_SEL_O (the request of token `k` has arrived by `O k`), checked
  identities (`ackOK`: the ack wire IS a real node's LUT output, the req wire is a buffer
  chain from a real node's LUT output, both reset 0), a checked hold row `holdBandS` with lag
  `Dl`, and three COUNT facts of the realisation instead of H_ACK_LAG_w:
  H_ACK_CNT (the ack's count stays `≤ 2k+1` until `Dl` after the junction shows `k`),
  H_REQ_CNT (the req's count is at most one ahead of the ack's), and H_SEL_O. Conclusion:
  SelOK and the link of every real LUT wire at ALL times.
* `reqCnt_of_line`, `ackCnt_of_line`: the two count facts from lines of the accepted log
  (decidable `ReqLine` / `AckLine`; sound for every behaviour, `runLog_sound`). `AckLine` is
  anchored at the SOURCE: it gives H_ACK_CNT for `Dl` with `Dl + phi bot ≤ dW + 1`.
* **`design_verdict9_selL`**: the verdict with only C's H_BUNDLE, H_SEL_SETUP and H_SEL_O as
  select-side trace hypotheses; H_ACK_LAG(_w) is gone (every row it needed is a checked log
  line). Its hold rows are `holdBandS` at the source-anchored lag `Dl` that the log line
  supports, NOT at E8SelC's junction lag `plo π` (see notes: `plo π` is not derivable from a
  band walk, and for tokens of the SIBLING branch not from causality through `π` at all).

NOT covered: H_BUNDLE, H_SEL_SETUP, H_SEL_O (trace hypotheses), H_ARB (all times), the
virtual pins' SelOK; the log lines `ReqLine` / `AckLine` are not produced by any certificate
generator yet, so no gcd_hw row has been evaluated with this verdict.
-/

namespace Formal.Core.XAudit.Events9PrefixSel

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
open Formal.Core.XAudit.Events8Bridge
open Formal.Core.XAudit.Events9Sel
open Formal.Core.XAudit.Events9SelC
open Formal.Core.XAudit.Events9SelHold
open Formal.Core.XAudit.Events9SelSplit
open Formal.Core.XAudit.Events9Prefix

/-! ## 1. Buffer chains -/

/-- Every element of the path is input 0 of an existing 1-input BUFFER gate. -/
def bufs (d : Design) (κ : Path) : Bool :=
  κ.all fun e => decide (e.1 < d.gates.length) && decide ((gt d e.1).k = 1) &&
    decide (InitSpec (gt d e.1) (fun v => v 0)) && (e.2 == 0)

/-- **A checked buffer chain** from wire `top` down to wire `bot` (`[]`: `top = bot`). -/
def bufPath (d : Design) (top bot : Nat) (κ : Path) : Bool :=
  match κ with
  | [] => top == bot
  | _ :: _ => chainOK d top bot κ && bufs d κ

theorem bufPath_pathOK {d : Design} {top bot : Nat} {κ : Path} (h : bufPath d top bot κ = true) :
    pathOK d κ = true := by
  cases κ with
  | nil => rfl
  | cons e r =>
    simp only [bufPath, chainOK, Bool.and_eq_true] at h
    exact h.1.2

section
variable {d : Design} {x : Fin d.n → Sig} (hsat : SatPin d plG x)
  (h0 : ∀ t, x (d.wire 0) t = false) (h1 : ∀ t, x (d.wire 1) t = true)
include hsat h0 h1

theorem links_val (bot : Nat) : ∀ (r : Path) (g i : Nat), links d bot ((g, i) :: r) = true →
    bufs d ((g, i) :: r) = true → ∀ t, x (d.wire (gt d g).out) t = x (d.wire bot) (tau hsat ((g, i) :: r) t)
  | [], g, i, hl, hb, t => by
    simp only [links, beq_iff_eq] at hl
    simp only [bufs, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq] at hb
    obtain ⟨⟨⟨hg, hk⟩, hs⟩, hi⟩ := hb
    subst hi
    rw [buf_read hsat h0 h1 hg ⟨hk, hs⟩ t, hl]; rfl
  | (g2, i2) :: r, g, i, hl, hb, t => by
    simp only [links, Bool.and_eq_true, beq_iff_eq] at hl
    simp only [bufs, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hb
    obtain ⟨⟨⟨⟨hg, hk⟩, hs⟩, hi⟩, hrest⟩ := hb
    subst hi
    rw [buf_read hsat h0 h1 hg ⟨hk, hs⟩ t, hl.1]
    have ih := links_val bot r g2 i2 hl.2 (by simpa [bufs] using hrest) (wf hsat g 0 t)
    rw [ih]; rfl

/-- **A buffer chain carries its source's value**, delayed by its own warp. -/
theorem bufPath_val {top bot : Nat} {κ : Path} (h : bufPath d top bot κ = true) (t : Nat) :
    x (d.wire top) t = x (d.wire bot) (tau hsat κ t) := by
  cases κ with
  | nil => simp only [bufPath, beq_iff_eq] at h; subst h; rfl
  | cons e r =>
    obtain ⟨g, i⟩ := e
    simp only [bufPath, chainOK, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hout, hl⟩, _⟩, hb⟩ := h
    rw [← hout]
    exact links_val hsat h0 h1 bot r g i hl hb t

end

/-! ## 2. A channel in transaction, from counts -/

/-- `req ∨ ack` from the counts of two reset-0 wires: the request has reached transaction `k`,
the acknowledge has not closed it, and the request is at most one ahead. -/
theorem inTx_of_cnt {c : Formal.Net.Handshake.Chan} {s A R k : Nat}
    (ha : c.ack s = ph false A) (hq : c.req s = ph false R)
    (hR : 2 * k + 1 ≤ R) (hA : A ≤ 2 * k + 1) (hRA : R ≤ A + 1) : Formal.Net.Ops.inTx c s = true := by
  unfold Formal.Net.Ops.inTx
  by_cases hk : A = 2 * k + 1
  · have : A % 2 = 1 := by omega
    rw [ha]; simp [ph, this]
  · have hR' : R % 2 = 1 := by omega
    rw [hq]; simp [ph, hR']

/-! ## 3. One select read, needing stability only up to the sample -/

/-- `Events9SelSplit.sel_read_split` at one sample `s`: stability is needed only at times
`t ≤ s` (the select is read at `gS s ≤ s`). -/
theorem sel_read_split_at {Rlo Rhi Slo Shi Tlo Thi : Nat} {gR gS gT : Nat → Nat} (gB : Nat → Nat)
    (wR : Warp Rlo Rhi gR) (wS : Warp Slo Shi gS) (wT : Warp Tlo Thi gT) (hfac : ∀ s, gR s = gB (gT s))
    (M : Nat → Nat) (hM0 : M 0 = 0)
    (xs : Sig) (v : Nat → Bool) (R S0 : Nat → Nat) (s : Nat)
    (hwin : ∀ u k, M u = 2 * k + 1 → R k ≤ u)
    (hsetup : ∀ k, S0 k + Shi ≤ R k + Rlo)
    (hstab : ∀ k t r, t ≤ s → M (gB r) = 2 * k + 1 → S0 k ≤ t → t + Slo ≤ r + Thi → xs t = v k) :
    ∀ k, M (gR s) = 2 * k + 1 → xs (gS s) = v k := by
  intro k hm
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
  exact hstab k _ (gT s) (by omega) hm (by omega) (by omega)

section
variable {N : Nat} {d : Design} {net : Net4 N} {b : Bands4 net} {rn : Fin N → RNode} {rank : Fin N → Nat}
  {rw fuel : Nat} {x : Fin d.n → Sig} {sel : Nat → Nat → Bool}

/-- `Events9SelSplit.selOK_real_split` at ONE sample `s` (`SelAt bh s`), needing the select
wires' stability only at times `t ≤ s`. -/
theorem selAt_split (hsat : SatPin d plG x) (hr : Recog6 d net b rn rank rw fuel)
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
    exact sel_read_split_at _ (bh.wG j p i) (sel_warp hsat hr.1 j hn p sb hsb) wT hfac
      (fun u => bh.M u (net.src j p)) (bh.M_zero _)
      (x (d.wire ((gt d (selGate net rn j p)).ins.getD sb.1 0))) (vb j p sb.1) (R j p)
      (fun k => S0 j p sb.1 k) s (fun u k h => hwin j p u k hvf hk h)
      (fun k => hsetup j p sb i k hvf hk hsb)
      (fun k t r ht h1 h2 h3 => hstab j p sb i k t r ht hvf hk hsb h1 h2 h3) _ hk2

end

/-! ## 4. The identity checks -/

section
variable {N : Nat} (d : Design) (net : Net4 N) (rn : Fin N → RNode)

/-- **The identity check of a select channel's handshake wires** (decidable): the ack wire is
the LUT output of the real node `na`, the request wire is a checked buffer chain `κ` from the
LUT output of the real node `nq`; both nodes reset to 0. -/
def ackOK (e : SelEnt) (na nq : Fin N) (κ : Path) : Bool :=
  decide ((rn na).virt = false) && decide ((gt d (rn na).lut).out = e.ak) && decide (net.v na = false) &&
  decide ((rn nq).virt = false) && decide (net.v nq = false) && bufPath d e.rq (gt d (rn nq).lut).out κ

theorem ackOK_spec {e : SelEnt} {na nq : Fin N} {κ : Path} (h : ackOK d net rn e na nq κ = true) :
    (rn na).virt = false ∧ (gt d (rn na).lut).out = e.ak ∧ net.v na = false ∧
      (rn nq).virt = false ∧ net.v nq = false ∧ bufPath d e.rq (gt d (rn nq).lut).out κ = true := by
  simp only [ackOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

end

/-! ## 5. The verdict with H_ACK_LAG_w replaced by count facts -/

section
variable {N : Nat} {d : Design} {net : Net4 N} {b : Bands4 net} {rn : Fin N → RNode} {rank : Fin N → Nat}
  {rw fuel : Nat} {x : Fin d.n → Sig} {cv : Fin N → Sig}

/-- **`design_verdict9_selP`: the split select verdict without H_ACK_LAG_w.** Same checks
and trace hypotheses as `design_verdict9_selS` (Recog6, OK7, the accepted log and certified
items, `entOK` of the map, SatPin, constants, reset, H_ARB), except:
* the hold row of each real filtered pin `(j, p)`, copy `i` and select literal `sb` is
  `holdBandS` at a lag `Dl j p i sb.1` (checked), and no certificate path is needed;
* per literal, `ackOK` (checked): the mapped channel's ack wire is the LUT output of the real
  reset-0 node `na`, its request wire a buffer chain `κ` from the LUT output of the real
  reset-0 node `nq`;
* H_ACK_LAG_w (a WIRE statement) is replaced by three statements about the realisation's
  COUNTS: **H_SEL_O** (`2k+1 ≤ M (tau κ (O k)) nq`: by `O k` the request has reached
  transaction `k`), **H_REQ_CNT** (`M (tau κ v) nq ≤ M v na + 1`), **H_ACK_CNT**
  (`M σ na ≤ 2k+1` whenever the junction shows transaction `k` at some `r` with `σ < r + Dl`).
Proved: SelOK of the realisation AND the link of every real LUT wire at every time. The
circularity of E8SelC §3.3 is removed by `causal_close`: SelOK at a sample `s` uses the
channel's wires only at times `< s`, where the prefix verdict already gives the link. -/
theorem design_verdict9_selP (hr : Recog6 d net b rn rank rw fuel) (hOK : net.OK7)
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
    (Dl : (j : Fin N) → Fin (net.ar j) → Nat → Nat → Nat)
    (na nq : (j : Fin N) → Fin (net.ar j) → Nat → Fin N) (κ : (j : Fin N) → Fin (net.ar j) → Nat → Path)
    (hm : ∀ j p (sb : Nat × Bool), (rn j).virt = false → net.pk j p = PK.filt → sb ∈ selLits net rn j p →
      entOK d net rn j p sb.1 (m j p sb.1) = true ∧
      ackOK d net rn (m j p sb.1) (na j p sb.1) (nq j p sb.1) (κ j p sb.1) = true)
    (hrow : ∀ j p (sb : Nat × Bool) (i : Fin (net.nc j p)), (rn j).virt = false → net.pk j p = PK.filt →
      sb ∈ selLits net rn j p →
      holdBandS d net rn j p (m j p sb.1) i.val (cut j p i.val) (Dl j p i.val sb.1) = true)
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
        (∀ j p (sb : Nat × Bool) k, (rn j).virt = false → net.pk j p = PK.filt → sb ∈ selLits net rn j p →
          2 * k + 1 ≤ bh.M (tau hsat (κ j p sb.1) (O j p sb.1 k)) (nq j p sb.1)) →
        (∀ j p (sb : Nat × Bool) v, (rn j).virt = false → net.pk j p = PK.filt → sb ∈ selLits net rn j p →
          bh.M (tau hsat (κ j p sb.1) v) (nq j p sb.1) ≤ bh.M v (na j p sb.1) + 1) →
        (∀ j p (sb : Nat × Bool) (i : Fin (net.nc j p)) k r σ, (rn j).virt = false →
          net.pk j p = PK.filt → sb ∈ selLits net rn j p →
          bh.M (tau hsat (botP d net rn j p i.val (cut j p i.val)) r) (net.src j p) = 2 * k + 1 →
          σ < r + Dl j p i.val sb.1 → bh.M σ (na j p sb.1) ≤ 2 * k + 1) →
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
        bh.SelOK ∧ ∀ t j, (rn j).virt = false →
          x (d.wire (gt d (rn j).lut).out) t = ph (net.v j) (bh.M t j)) := by
  obtain ⟨bh, hc, hgc, hreal, hsv, hG⟩ := design_beh8_svG hsat h0 h1 hT hrst hr hOK harb sel
  refine ⟨bh, hc, hgc, fun hp hvirt R O hheld hO hRq hAk hsetup hwin hsel rB rX rL rG => ?_⟩
  -- the prefix verdict on this realisation
  have hpre : ∀ t0, (∀ s, s < t0 → SelAt bh s) → Link bh t0 := fun t0 hs =>
    verdict9_upto bh hOK hp hJ back line xS xw xa hl gd cp cxm cl cg hcp hcx hcl hcg
      (fun j p s _ => hgc j p s) t0 (fun j p s _ => rB j p s) (fun m s _ => rX m s)
      (fun j p s _ => rL j p s) (fun j p hk hc => guardPinB_of bh (rG j p hk hc) t0) hs
  let S0 : (j : Fin N) → Fin (net.ar j) → Nat → Nat → Nat :=
    fun j p i k => O j p i k + (gt d (m j p i).rg).hi
  let vb : (j : Fin N) → Fin (net.ar j) → Nat → Nat → Bool :=
    fun j p i k => x (d.wire (m j p i).dw) (O j p i k)
  -- the causal step: SelOK at sample s from the link at all times < s
  have hstep : ∀ s, (∀ u, u < s → ∀ j : Fin N, bh.c j u = ph (net.v j) (bh.M u j)) → SelAt bh s := by
    intro s hlink
    refine selAt_split hsat hr bh hsv hG hvirt cut R S0 vb hwin
      (fun j p sb i k hvf hk hsb => hsetup j p sb i k hvf hk hsb) hsel s ?_
    intro j p sb i k t r hts hvf hk hsb hu ht htu
    obtain ⟨hEnt, hAck⟩ := hm j p sb hvf hk hsb
    obtain ⟨hg, hb, hin, hout, hw⟩ := entOK_spec d net rn hEnt
    obtain ⟨hnav, hnaout, hnav0, hnqv, hnqv0, hκ⟩ := ackOK_spec d net rn hAck
    have hband := of_decide_eq_true (hrow j p sb i hvf hk hsb)
    have hrg1 : 1 ≤ (gt d (m j p sb.1).rg).lo := (hr.1 _ (gt_mem d hg)).2.2.2.1
    have hrg2 : (gt d (m j p sb.1).rg).lo ≤ (gt d (m j p sb.1).rg).hi := (hr.1 _ (gt_mem d hg)).2.2.2.2.1
    have hS0 : S0 j p sb.1 k = O j p sb.1 k + (gt d (m j p sb.1).rg).hi := rfl
    have wκ := tau_warp hsat _ (bufPath_pathOK hκ)
    -- the channel is mid-transaction at every time σ in [O k, t - lo(rg)]
    have htx : ∀ σ, O j p sb.1 k ≤ σ → σ ≤ t - (gt d (m j p sb.1).rg).lo →
        Formal.Net.Ops.inTx ((m j p sb.1).ch x) σ = true := by
      intro σ hσ1 hσ2
      have hσs : σ < s := by omega
      have hκσ : tau hsat (κ j p sb.1) σ ≤ σ := by have := wκ.le_late σ; omega
      have hack : ((m j p sb.1).ch x).ack σ = ph false (bh.M σ (na j p sb.1)) := by
        show x (d.wire (m j p sb.1).ak) σ = _
        rw [← hnaout, ← hreal _ hnav σ, hlink σ hσs, hnav0]
      have hreq : ((m j p sb.1).ch x).req σ = ph false (bh.M (tau hsat (κ j p sb.1) σ) (nq j p sb.1)) := by
        show x (d.wire (m j p sb.1).rq) σ = _
        rw [bufPath_val hsat h0 h1 hκ σ, ← hreal _ hnqv, hlink _ (by omega), hnqv0]
      refine inTx_of_cnt (k := k) hack hreq ?_ ?_ (hRq j p sb σ hvf hk hsb)
      · exact Nat.le_trans (hO j p sb k hvf hk hsb)
          (bh.M_mono _ _ _ (wκ.mono _ _ hσ1))
      · exact hAk j p sb i k r σ hvf hk hsb hu (by omega)
    -- H_BUNDLE holds the bus over that interval; the route arc carries it to the pin
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

/-! ## 6. The count facts from lines of the accepted log -/

section
variable {N : Nat} {net : Net4 N} {b : Bands4 net} {sel : Nat → Nat → Bool} (x : Beh7 net b sel)

/-- **The protocol line** (decidable): log line `w` is an unlabelled walk from `nq` to `na`
with at most one token. -/
def ReqLine (J : Array Jd) (nq na w : Nat) : Prop :=
  ∃ h : w < J.size, J[w].u = false ∧ J[w].c = none ∧ J[w].a = nq ∧ J[w].bb = na ∧ J[w].t ≤ 1

instance (J : Array Jd) (nq na w : Nat) : Decidable (ReqLine J nq na w) := by unfold ReqLine; exact inferInstance

/-- **The lag line** (decidable): log line `w` is an unlabelled walk from `na` to the source
`src` with NO token, whose delay covers the lag `D` plus the junction's lower part's upper
band end `phb`: `D + phb ≤ dW + 1`. -/
def AckLine (J : Array Jd) (na src w D phb : Nat) : Prop :=
  ∃ h : w < J.size, J[w].u = false ∧ J[w].c = none ∧ J[w].a = na ∧ J[w].bb = src ∧ J[w].t = 0 ∧
    D + phb ≤ J[w].d + 1

instance (J : Array Jd) (na src w D phb : Nat) : Decidable (AckLine J na src w D phb) := by
  unfold AckLine; exact inferInstance

theorem reqCnt_of_line {J : Array Jd} (hA : AllH x J) {nq na : Fin N} {w : Nat} (h : ReqLine J nq.val na.val w)
    (g : Nat → Nat) (hg : ∀ v, g v ≤ v) : ∀ v, x.M (g v) nq ≤ x.M v na + 1 := by
  obtain ⟨hw, hu, hc, ha, hb, ht⟩ := h
  obtain ⟨_, _, hs⟩ := holds_w x (hA w hw) hu hc
  intro v
  have := hs (g v)
  rw [ha, hb, Mn_fin, Mn_fin] at this
  have := x.M_mono v na (g v - J[w].d) (by have := hg v; omega)
  omega

theorem ackCnt_of_line {J : Array Jd} (hA : AllH x J) {na src : Fin N} {w D lo hi : Nat} {g : Nat → Nat}
    (wg : Warp lo hi g) (h : AckLine J na.val src.val w D hi) :
    ∀ k r σ, x.M (g r) src = 2 * k + 1 → σ < r + D → x.M σ na ≤ 2 * k + 1 := by
  obtain ⟨hw, hu, hc, ha, hb, ht, hD⟩ := h
  obtain ⟨_, _, hs⟩ := holds_w x (hA w hw) hu hc
  intro k r σ hk hσ
  have h1 := hs σ
  rw [ha, hb, Mn_fin, Mn_fin, ht] at h1
  have h2 := wg.early_le r
  have h3 := x.M_mono (g r) src (σ - J[w].d) (by omega)
  omega

end

/-! ## 7. The verdict with every select-side count fact checked -/

section
variable {N : Nat} {d : Design} {net : Net4 N} {b : Bands4 net} {rn : Fin N → RNode} {rank : Fin N → Nat}
  {rw fuel : Nat} {x : Fin d.n → Sig} {cv : Fin N → Sig}

/-- **`design_verdict9_selL`: the select verdict with H_ACK_LAG discharged.** As
`design_verdict9_selP`, with H_REQ_CNT and H_ACK_CNT replaced by CHECKED lines of the accepted
log: per literal a `ReqLine` (walk `nq → na`, ≤ 1 token) and per copy and literal an `AckLine`
(walk `na → src`, no token, `Dl + phi bot ≤ dW + 1`). The select-side trace hypotheses left
are C's H_BUNDLE, H_SEL_SETUP and H_SEL_O; with SatPin, the constants, reset, H_ARB (with the
virtual pins' SelOK) and SelPart, they give SelOK and the link of every real LUT wire at every
time (on a row whose other items are certified). -/
theorem design_verdict9_selL (hr : Recog6 d net b rn rank rw fuel) (hOK : net.OK7)
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
    (Dl : (j : Fin N) → Fin (net.ar j) → Nat → Nat → Nat)
    (na nq : (j : Fin N) → Fin (net.ar j) → Nat → Fin N) (κ : (j : Fin N) → Fin (net.ar j) → Nat → Path)
    (wq : (j : Fin N) → Fin (net.ar j) → Nat → Nat) (wa : (j : Fin N) → Fin (net.ar j) → Nat → Nat → Nat)
    (hm : ∀ j p (sb : Nat × Bool), (rn j).virt = false → net.pk j p = PK.filt → sb ∈ selLits net rn j p →
      entOK d net rn j p sb.1 (m j p sb.1) = true ∧
      ackOK d net rn (m j p sb.1) (na j p sb.1) (nq j p sb.1) (κ j p sb.1) = true ∧
      decide (ReqLine J (nq j p sb.1).val (na j p sb.1).val (wq j p sb.1)) = true)
    (hrow : ∀ j p (sb : Nat × Bool) (i : Fin (net.nc j p)), (rn j).virt = false → net.pk j p = PK.filt →
      sb ∈ selLits net rn j p →
      holdBandS d net rn j p (m j p sb.1) i.val (cut j p i.val) (Dl j p i.val sb.1) = true ∧
      decide (AckLine J (na j p sb.1).val (net.src j p).val (wa j p i.val sb.1) (Dl j p i.val sb.1)
        (phi d (botP d net rn j p i.val (cut j p i.val)))) = true)
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
        (∀ j p (sb : Nat × Bool) k, (rn j).virt = false → net.pk j p = PK.filt → sb ∈ selLits net rn j p →
          2 * k + 1 ≤ bh.M (tau hsat (κ j p sb.1) (O j p sb.1 k)) (nq j p sb.1)) →
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
        bh.SelOK ∧ ∀ t j, (rn j).virt = false →
          x (d.wire (gt d (rn j).lut).out) t = ph (net.v j) (bh.M t j)) := by
  obtain ⟨bh, hc, hgc, H⟩ := design_verdict9_selP hr hOK hJ back line xS xw xa hl gd cp cxm cl cg
    hcp hcx hcl hcg m cut Dl na nq κ (fun j p sb hv hk hs => ⟨(hm j p sb hv hk hs).1, (hm j p sb hv hk hs).2.1⟩)
    (fun j p sb i hv hk hs => (hrow j p sb i hv hk hs).1) hsat h0 h1 hT hrst harb sel
  refine ⟨bh, hc, hgc, fun hp hvirt R O hheld hO hsetup hwin hsel rB rX rL rG => ?_⟩
  have hA := runLog_sound bh hOK hp hJ
  refine H hp hvirt R O hheld hO ?_ ?_ hsetup hwin hsel rB rX rL rG
  · intro j p sb v hv hk hs
    obtain ⟨_, hAck, hq⟩ := hm j p sb hv hk hs
    have hκ := (ackOK_spec d net rn hAck).2.2.2.2.2
    have wκ := tau_warp hsat _ (bufPath_pathOK hκ)
    exact reqCnt_of_line bh hA (of_decide_eq_true hq) _ (fun v => by have := wκ.le_late v; omega) v
  · intro j p sb i k r σ hv hk hs hu hσ
    have hn := hr.2 j hv
    have hok := (full_ok hr.1 j hn p i).1
    have hbot : pathOK d (botP d net rn j p i.val (cut j p i.val)) = true := by
      unfold botP; unfold pathOK at hok ⊢
      exact List.all_eq_true.mpr fun e he => List.all_eq_true.mp hok e (List.mem_of_mem_drop he)
    exact ackCnt_of_line bh hA (tau_warp hsat _ hbot) (of_decide_eq_true (hrow j p sb i hv hk hs).2)
      k r σ hu hσ

end

/-! ## 8. Negative control: the junction lag through the pin's OWN arm is not enough -/

/-- **NEGATIVE CONTROL (sibling branch).** An acknowledge that is a merge of two branches of
one source `n` (the counts `filt` of each branch, read through two arms: the OWN arm of the
pin, lag 30, which passes the pin's junction; the SIBLING arm, lag 5, which does not).
Transaction 0 is routed to the sibling branch (`sel = false`). The junction (here the
source itself) shows transaction 0 at `r = 19`, yet the acknowledge's count reaches 2
(transaction 0 closed) at `σ = 26 < r + 30`: H_ACK_CNT fails at the own-arm lag 30. It holds
at the sibling lag (`σ < r + 6`, checked on the whole window). So the lag of a junction row
must be the minimum over ALL arms by which the acknowledge can close, not the length of a
path through the junction. -/
theorem sibling_lag_neg :
    let n : Nat → Nat := fun t => if t < 10 then 0 else if t < 20 then 1 else 2
    let sv : Nat → Bool := fun _ => false
    let A : Nat → Nat := fun σ =>
      Formal.Core.XAudit.Events3.filt sv false (n (σ - 5)) + Formal.Core.XAudit.Events3.filt sv true (n (σ - 30))
    n 19 = 2 * 0 + 1 ∧ 26 < 19 + 30 ∧ ¬ (A 26 ≤ 2 * 0 + 1) ∧ (∀ σ, σ < 19 + 6 → A σ ≤ 2 * 0 + 1) := by
  decide

end Formal.Core.XAudit.Events9PrefixSel
