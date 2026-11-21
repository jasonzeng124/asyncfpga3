import Formal.Core.XAudit.Events9PrefixSel

/-!
# Formal.Core.XAudit.Events9SelL — the select verdict with gate-tree handshake identities

Probe E9SelRun (shard A). Notes: `formal/notes/A-e9selrun.md` §2.

E8Causal's `Events9PrefixSel.design_verdict9_selL` identifies a select channel's handshake wires
by `ackOK`: the acknowledge wire IS a real node's LUT output, the request wire is a chain of
1-input BUFFERS from a real node's LUT output. On the routed gcd_hw that fails for most
literals (notes §1): the request wire of a comparator-fed channel is the end of an asymmetric
(fast-fall) delay line of 2-input AND LUTs, `chain.g[m] = AND(r, chain.g[m-1])`, all fed by
the same request `r`; some acknowledge wires are an OR of the controller and its delayed copy.

This file replaces `ackOK` by **positive gate trees** (`AT`): a tree of gates whose root is the
wire, whose leaves are real reset-0 nodes' LUT outputs, and at every gate the INIT is 1 on every
address in which the listed inputs are 1 (`initAll`; an AND lists all its inputs, an OR or a
buffer one). `at_true`: if every leaf reads 1 at its path-warped time, the root reads 1.

* the acknowledge tree has exactly ONE leaf `(na, κa)` (`κa` its path);
* the request tree may have many leaves (the AND delay line: one leaf per element, all the
  same node).

**`design_verdict9_selTP`**: `Events9PrefixSel.design_verdict9_selP` with the tree identities,
and the count facts restated for them:
* H_SEL_O (per request leaf): by `O k` every leaf's read has seen transaction `k`;
* H_REQ_CNT (per request leaf): the leaf's count at its read is at most one ahead of the ack
  leaf's count at ITS read;
* H_ACK_CNT: the ack leaf's count at its read stays `≤ 2k+1` until `Dl` after the junction
  shows transaction `k`.

**`design_verdict9_selT`**: H_REQ_CNT and H_ACK_CNT discharged by CHECKED lines of the accepted
log: per request leaf a `ReqLineT` (walk leaf → `na`, ≤ 1 token, delay `≥ phi κa − plo π`), per
copy an `AckLineT` (walk `na → src`, no token, `Dl + phi bot ≤ dW + plo κa + 1`). With `κa = []`
and a buffer-chain request this is E8Causal's `selL` (and a little stronger: `plo κa` is
credited). The remaining select-side trace hypotheses are C's H_BUNDLE, H_SEL_SETUP and H_SEL_O.

NOT covered: H_BUNDLE, H_SEL_SETUP, H_SEL_O (trace hypotheses); the trusted map (channel name;
which wire is the channel's ack/req); H_ARB at all times; the residual obligations of
uncertified items. The junction-anchored lag is `Events9SelJ`.
-/

namespace Formal.Core.XAudit.Events9SelL

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
open Formal.Core.XAudit.Events9PrefixSel

/-! ## 1. Positive gate trees -/

mutual
/-- A positive gate tree: a leaf is a node (its LUT output wire); a gate lists the inputs whose
1 forces its output to 1, each with the subtree that drives it. -/
inductive AT where
  | leaf (n : Nat)
  | gate (gi : Nat) (ch : ATL)
/-- The children of a gate: `(input index, subtree)`. -/
inductive ATL where
  | nil
  | cons (i : Nat) (s : AT) (r : ATL)
end

instance : Inhabited AT := ⟨AT.leaf 0⟩

/-- The input indices listed by a gate. -/
def ATL.idx : ATL → List Nat
  | .nil => []
  | .cons i _ r => i :: ATL.idx r

mutual
/-- The leaves of a tree with their paths from the root wire. -/
def AT.leaves : AT → List (Nat × Path)
  | .leaf n => [(n, [])]
  | .gate gi ch => ATL.leaves gi ch
def ATL.leaves (gi : Nat) : ATL → List (Nat × Path)
  | .nil => []
  | .cons i s r => (AT.leaves s).map (fun l => (l.1, (gi, i) :: l.2)) ++ ATL.leaves gi r
end

/-- Every address with the bits `is` set reads INIT 1 (decidable; `2^k ≤ 64` addresses). -/
def initAll (g : GSpec) (is : List Nat) : Bool :=
  (List.range (2 ^ g.k)).all fun a => !(is.all fun i => a.testBit i) || g.init.testBit a

theorem initAll_spec {g : GSpec} {is : List Nat} (h : initAll g is = true) {a : Nat} (ha : a < 2 ^ g.k)
    (hb : ∀ i ∈ is, a.testBit i = true) : g.init.testBit a = true := by
  unfold initAll at h
  have h1 := List.all_eq_true.mp h a (List.mem_range.mpr ha)
  have hall : (is.all fun i => a.testBit i) = true := List.all_eq_true.mpr hb
  simpa [hall] using h1

section
variable {N : Nat} (d : Design) (net : Net4 N) (rn : Fin N → RNode)

/-- The LUT output wire of node `n` (`d.n`, no wire, outside the network). -/
def nodeW (n : Nat) : Nat := if h : n < N then (gt d (rn ⟨n, h⟩).lut).out else d.n

/-- A leaf node: real, reset 0. -/
def leafOK (n : Nat) : Bool :=
  if h : n < N then decide ((rn ⟨n, h⟩).virt = false) && decide (net.v ⟨n, h⟩ = false) else false

mutual
/-- **The tree check** (decidable): every gate exists, drives the wire its parent reads, and its
INIT is 1 whenever the listed inputs are 1; every leaf node's LUT output is the wire read. -/
def atOK (w : Nat) : AT → Bool
  | .leaf n => decide (nodeW d rn n = w)
  | .gate gi ch => decide (gi < d.gates.length) && decide ((gt d gi).out = w) &&
      initAll (gt d gi) (ATL.idx ch) && atlOK gi ch
def atlOK (gi : Nat) : ATL → Bool
  | .nil => true
  | .cons i s r => decide (i < (gt d gi).k) && atOK ((gt d gi).ins.getD i 0) s && atlOK gi r
end

theorem nodeW_fin (n : Fin N) : nodeW d rn n.val = (gt d (rn n).lut).out := by
  simp [nodeW, n.isLt]

theorem leafOK_spec {n : Nat} (h : leafOK net rn n = true) :
    ∃ hn : n < N, (rn ⟨n, hn⟩).virt = false ∧ net.v ⟨n, hn⟩ = false := by
  unfold leafOK at h
  split at h
  · rename_i hn
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨hn, h.1, h.2⟩
  · simp at h

end

section
variable {N : Nat} {d : Design} {rn : Fin N → RNode} {x : Fin d.n → Sig} (hsat : SatPin d plG x)

mutual
/-- **A positive tree reads 1** when every leaf reads 1 at its path-warped time. -/
theorem at_true : ∀ (s : AT) (w : Nat), atOK d rn w s = true → ∀ t,
    (∀ l ∈ AT.leaves s, x (d.wire (nodeW d rn l.1)) (tau hsat l.2 t) = true) → x (d.wire w) t = true
  | .leaf n, w, h, t, hl => by
      simp only [atOK, decide_eq_true_eq] at h
      have := hl (n, []) (by simp [AT.leaves])
      rw [← h]; simpa [tau] using this
  | .gate gi ch, w, h, t, hl => by
      simp only [atOK, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨hg, hw⟩, hI⟩, hc⟩ := h
      rw [← hw, wf_eval hsat hg t]
      apply initAll_spec hI (addr_lt _)
      intro i hi
      obtain ⟨hk, hv⟩ := atl_true ch gi hc t (fun l hl' => hl l (by simpa [AT.leaves] using hl')) i hi
      rw [Events2.testBit_addr, dif_pos hk]
      exact hv
theorem atl_true : ∀ (ch : ATL) (gi : Nat), atlOK d rn gi ch = true → ∀ t,
    (∀ l ∈ ATL.leaves gi ch, x (d.wire (nodeW d rn l.1)) (tau hsat l.2 t) = true) →
    ∀ i ∈ ATL.idx ch, i < (gt d gi).k ∧ x (d.wire ((gt d gi).ins.getD i 0)) (wf hsat gi i t) = true
  | .nil, _, _, _, _, i, hi => absurd hi (by simp [ATL.idx])
  | .cons i0 s r, gi, h, t, hl, i, hi => by
      simp only [atlOK, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hk, hs⟩, hr⟩ := h
      simp only [ATL.idx, List.mem_cons] at hi
      rcases hi with e | e
      · subst e
        refine ⟨hk, at_true s _ hs (wf hsat gi i t) (fun l hl' => ?_)⟩
        have := hl (l.1, (gi, i) :: l.2) (by
          simp only [ATL.leaves, List.mem_append, List.mem_map]
          exact Or.inl ⟨l, hl', rfl⟩)
        simpa [tau] using this
      · exact atl_true r gi hr t (fun l hl' => hl l (by
          simp only [ATL.leaves, List.mem_append]; exact Or.inr hl')) i e
end

end

/-! ## 2. The count facts from log lines -/

/-- **The protocol line of one request leaf** (decidable): log line `w` is an unlabelled walk
from the leaf `nq` to the ack leaf `na` with at most one token and delay at least `dm`. -/
def ReqLineT (J : Array Jd) (nq na w dm : Nat) : Prop :=
  ∃ h : w < J.size, J[w].u = false ∧ J[w].c = none ∧ J[w].a = nq ∧ J[w].bb = na ∧ J[w].t ≤ 1 ∧ dm ≤ J[w].d

instance (J : Array Jd) (nq na w dm : Nat) : Decidable (ReqLineT J nq na w dm) := by
  unfold ReqLineT; exact inferInstance

/-- **The (source-anchored) lag line** (decidable): log line `w` is an unlabelled walk from the
ack leaf `na` to the source `src` with no token, and `Dl + phb ≤ dW + plk + 1` (`phb` the upper
band end of the junction's lower part, `plk` the lower band end of the ack leaf's path). -/
def AckLineT (J : Array Jd) (na src w Dl phb plk : Nat) : Prop :=
  ∃ h : w < J.size, J[w].u = false ∧ J[w].c = none ∧ J[w].a = na ∧ J[w].bb = src ∧ J[w].t = 0 ∧
    Dl + phb ≤ J[w].d + plk + 1

instance (J : Array Jd) (na src w Dl phb plk : Nat) : Decidable (AckLineT J na src w Dl phb plk) := by
  unfold AckLineT; exact inferInstance

section
variable (d : Design)

/-- The request leaves and their lines (positionally): every leaf `(nq, π)` has a `ReqLineT`
with `dm = phi κa - plo π`. -/
def reqOK (J : Array Jd) (na : Nat) (κa : Path) : List (Nat × Path) → List Nat → Bool
  | [], _ => true
  | l :: ls, w :: ws => decide (ReqLineT J l.1 na w (phi d κa - plo d l.2)) && reqOK J na κa ls ws
  | _ :: _, [] => false

theorem reqOK_mem {J : Array Jd} {na : Nat} {κa : Path} :
    ∀ (ls : List (Nat × Path)) (ws : List Nat), reqOK d J na κa ls ws = true →
      ∀ l ∈ ls, ∃ w, ReqLineT J l.1 na w (phi d κa - plo d l.2)
  | [], _, _, l, hl => absurd hl (by simp)
  | _ :: _, [], h, _, _ => by simp [reqOK] at h
  | l0 :: ls, w :: ws, h, l, hl => by
      simp only [reqOK, Bool.and_eq_true, decide_eq_true_eq] at h
      rcases List.mem_cons.mp hl with e | e
      · subst e; exact ⟨w, h.1⟩
      · exact reqOK_mem ls ws h.2 l e

end

section
variable {N : Nat} {net : Net4 N} {b : Bands4 net} {sel : Nat → Nat → Bool} (x : Beh7 net b sel)

theorem reqCnt_of_lineT {J : Array Jd} (hA : AllH x J) {nq : Nat} {na : Fin N} {w dm : Nat}
    (h : ReqLineT J nq na.val w dm) {loπ hiπ loκ hiκ : Nat} {gπ gκ : Nat → Nat}
    (wπ : Warp loπ hiπ gπ) (wκ : Warp loκ hiκ gκ) (hdm : hiκ - loπ ≤ dm) :
    ∀ v, Mn x (gπ v) nq ≤ x.M (gκ v) na + 1 := by
  obtain ⟨hw, hu, hc, ha, hb, ht, hd⟩ := h
  obtain ⟨_, _, hs⟩ := holds_w x (hA w hw) hu hc
  intro v
  have h1 := hs (gπ v)
  rw [ha, hb, Mn_fin] at h1
  have a1 := wπ.le_late v
  have a2 := wκ.early_le v
  have h2 := x.M_mono (gκ v) na (gπ v - J[w].d) (by omega)
  omega

theorem ackCnt_of_lineT {J : Array Jd} (hA : AllH x J) {na src : Fin N} {w Dl lo hi loκ hiκ : Nat}
    {g gκ : Nat → Nat} (wg : Warp lo hi g) (wκ : Warp loκ hiκ gκ) (h : AckLineT J na.val src.val w Dl hi loκ) :
    ∀ k r σ, x.M (g r) src = 2 * k + 1 → σ < r + Dl → x.M (gκ σ) na ≤ 2 * k + 1 := by
  obtain ⟨hw, hu, hc, ha, hb, ht, hD⟩ := h
  obtain ⟨_, _, hs⟩ := holds_w x (hA w hw) hu hc
  intro k r σ hk hσ
  have h1 := hs (gκ σ)
  rw [ha, hb, Mn_fin, Mn_fin, ht] at h1
  have h2 := wg.early_le r
  have h3 := wκ.le_late σ
  have h4 := x.M_mono (g r) src (gκ σ - J[w].d) (by omega)
  omega

end

/-! ## 3. The verdict with tree identities and count facts -/

section
variable {N : Nat} {d : Design} {net : Net4 N} {b : Bands4 net} {rn : Fin N → RNode} {rank : Fin N → Nat}
  {rw fuel : Nat} {x : Fin d.n → Sig} {cv : Fin N → Sig}

/-- **The identity check of a select channel with gate trees** (decidable): the acknowledge
wire is a positive tree with the single leaf `(na, κa)`, the request wire a positive tree whose
leaves are real reset-0 nodes; all paths exist. -/
def treeOK (e : SelEnt) (ta tq : AT) (na : Fin N) (κa : Path) : Bool :=
  atOK d rn e.ak ta && decide (AT.leaves ta = [(na.val, κa)]) && leafOK net rn na.val && pathOK d κa &&
  atOK d rn e.rq tq && (AT.leaves tq).all (fun l => leafOK net rn l.1 && pathOK d l.2)

theorem treeOK_spec {e : SelEnt} {ta tq : AT} {na : Fin N} {κa : Path} (h : treeOK (d := d) (net := net) (rn := rn) e ta tq na κa = true) :
    atOK d rn e.ak ta = true ∧ AT.leaves ta = [(na.val, κa)] ∧ leafOK net rn na.val = true ∧ pathOK d κa = true ∧
    atOK d rn e.rq tq = true ∧ ∀ l ∈ AT.leaves tq, leafOK net rn l.1 = true ∧ pathOK d l.2 = true := by
  simp only [treeOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- **`design_verdict9_selTP`.** As `Events9PrefixSel.design_verdict9_selP`, with `ackOK`
replaced by `treeOK` (gate-tree identities of the ack and request wires) and the count facts
stated for the tree leaves: H_SEL_O and H_REQ_CNT per request leaf, H_ACK_CNT for the ack leaf
at its read `tau κa σ`. Proved: SelOK of the realisation and the link of every real LUT wire at
every time; the realisation's real copy warps are exposed (`G = tau full (· + 1)`, as
`design_beh8_svG`) for `Events9SelJ`. -/
theorem design_verdict9_selTP (hr : Recog6 d net b rn rank rw fuel) (hOK : net.OK7)
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
    (ta tq : (j : Fin N) → Fin (net.ar j) → Nat → AT) (na : (j : Fin N) → Fin (net.ar j) → Nat → Fin N)
    (κa : (j : Fin N) → Fin (net.ar j) → Nat → Path)
    (hm : ∀ j p (sb : Nat × Bool), (rn j).virt = false → net.pk j p = PK.filt → sb ∈ selLits net rn j p →
      entOK d net rn j p sb.1 (m j p sb.1) = true ∧
      treeOK (d := d) (net := net) (rn := rn) (m j p sb.1) (ta j p sb.1) (tq j p sb.1) (na j p sb.1) (κa j p sb.1) = true)
    (hrow : ∀ j p (sb : Nat × Bool) (i : Fin (net.nc j p)), (rn j).virt = false → net.pk j p = PK.filt →
      sb ∈ selLits net rn j p →
      holdBandS d net rn j p (m j p sb.1) i.val (cut j p i.val) (Dl j p i.val sb.1) = true)
    (hsat : SatPin d plG x) (h0 : ∀ t, x (d.wire 0) t = false) (h1 : ∀ t, x (d.wire 1) t = true)
    {T : Nat} (hT : 1 ≤ T) (hrst : ∀ t, x (d.wire rw) t = decide (t < T)) (harb : HARB7 net b rn x cv)
    (sel : Nat → Nat → Bool) :
    ∃ bh : Beh7 net b sel, (∀ j t, bh.c j t = ccOf rn x cv j t) ∧
      (∀ j p s, bh.gc j p s = gcnt net sel j p (bh.cm j p s)) ∧
      (∀ j, (rn j).virt = false → ∀ p i s, bh.G j p i s = tau hsat (full net rn j p i.val) (s + 1)) ∧
      (SelPart sel parts →
        (∀ j p s (i : Fin (net.nc j p)), (rn j).virt = true → net.pk j p = PK.filt →
          bh.M (bh.G j p i s) (net.src j p) % 2 = 1 →
          bh.sv j p s = sel (net.grp j p) (bh.M (bh.G j p i s) (net.src j p) / 2)) →
        ∀ (R : (j : Fin N) → Fin (net.ar j) → Nat → Nat)
          (O : (j : Fin N) → Fin (net.ar j) → Nat → Nat → Nat),
        (∀ j p (sb : Nat × Bool), (rn j).virt = false → net.pk j p = PK.filt → sb ∈ selLits net rn j p →
          Formal.Net.Ops.Held ((m j p sb.1).ch x)) →
        (∀ j p (sb : Nat × Bool) k u, (rn j).virt = false → net.pk j p = PK.filt → sb ∈ selLits net rn j p →
          bh.M u (net.src j p) = 2 * k + 1 → ∀ l ∈ AT.leaves (tq j p sb.1),
          2 * k + 1 ≤ Mn bh (tau hsat l.2 (O j p sb.1 k)) l.1) →
        (∀ j p (sb : Nat × Bool) v, (rn j).virt = false → net.pk j p = PK.filt → sb ∈ selLits net rn j p →
          ∀ l ∈ AT.leaves (tq j p sb.1),
          Mn bh (tau hsat l.2 v) l.1 ≤ bh.M (tau hsat (κa j p sb.1) v) (na j p sb.1) + 1) →
        (∀ j p (sb : Nat × Bool) (i : Fin (net.nc j p)) k r σ, (rn j).virt = false →
          net.pk j p = PK.filt → sb ∈ selLits net rn j p →
          bh.M (tau hsat (botP d net rn j p i.val (cut j p i.val)) r) (net.src j p) = 2 * k + 1 →
          σ < r + Dl j p i.val sb.1 → bh.M (tau hsat (κa j p sb.1) σ) (na j p sb.1) ≤ 2 * k + 1) →
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
  refine ⟨bh, hc, hgc, hG, fun hp hvirt R O hheld hO hRq hAk hsetup hwin hsel rB rX rL rG => ?_⟩
  have hpre : ∀ t0, (∀ s, s < t0 → SelAt bh s) → Link bh t0 := fun t0 hs =>
    verdict9_upto bh hOK hp hJ back line xS xw xa hl gd cp cxm cl cg hcp hcx hcl hcg
      (fun j p s _ => hgc j p s) t0 (fun j p s _ => rB j p s) (fun m s _ => rX m s)
      (fun j p s _ => rL j p s) (fun j p hk hc => guardPinB_of bh (rG j p hk hc) t0) hs
  let S0 : (j : Fin N) → Fin (net.ar j) → Nat → Nat → Nat :=
    fun j p i k => O j p i k + (gt d (m j p i).rg).hi
  let vb : (j : Fin N) → Fin (net.ar j) → Nat → Nat → Bool :=
    fun j p i k => x (d.wire (m j p i).dw) (O j p i k)
  have hstep : ∀ s, (∀ u, u < s → ∀ j : Fin N, bh.c j u = ph (net.v j) (bh.M u j)) → SelAt bh s := by
    intro s hlink
    refine selAt_split hsat hr bh hsv hG hvirt cut R S0 vb hwin
      (fun j p sb i k hvf hk hsb => hsetup j p sb i k hvf hk hsb) hsel s ?_
    intro j p sb i k t r hts hvf hk hsb hu ht htu
    obtain ⟨hEnt, hTr⟩ := hm j p sb hvf hk hsb
    obtain ⟨hg, hb, hin, hout, hw⟩ := entOK_spec d net rn hEnt
    obtain ⟨hta, hlta, hnaL, hκp, htq, hlq⟩ := treeOK_spec hTr
    obtain ⟨_, hnav, hnav0⟩ := leafOK_spec net rn hnaL
    have hband := of_decide_eq_true (hrow j p sb i hvf hk hsb)
    have hrg1 : 1 ≤ (gt d (m j p sb.1).rg).lo := (hr.1 _ (gt_mem d hg)).2.2.2.1
    have hrg2 : (gt d (m j p sb.1).rg).lo ≤ (gt d (m j p sb.1).rg).hi := (hr.1 _ (gt_mem d hg)).2.2.2.2.1
    have hS0 : S0 j p sb.1 k = O j p sb.1 k + (gt d (m j p sb.1).rg).hi := rfl
    have wκ := tau_warp hsat _ hκp
    -- a real reset-0 node's wire at a time before `s` reads its count's parity
    have hwire : ∀ (n : Fin N), (rn n).virt = false → net.v n = false → ∀ τ, τ < s →
        x (d.wire (nodeW d rn n.val)) τ = ph false (bh.M τ n) := by
      intro n hv hv0 τ hτ
      rw [nodeW_fin, ← hreal n hv τ, hlink τ hτ, hv0]
    -- the channel is mid-transaction at every time σ in [O k, t - lo(rg)]
    have htx : ∀ σ, O j p sb.1 k ≤ σ → σ ≤ t - (gt d (m j p sb.1).rg).lo →
        Formal.Net.Ops.inTx ((m j p sb.1).ch x) σ = true := by
      intro σ hσ1 hσ2
      have hσs : σ < s := by omega
      have hκσ : tau hsat (κa j p sb.1) σ ≤ σ := by have := wκ.le_late σ; omega
      have hAle := hAk j p sb i k r σ hvf hk hsb hu (by omega)
      unfold Formal.Net.Ops.inTx
      by_cases hA : bh.M (tau hsat (κa j p sb.1) σ) (na j p sb.1) % 2 = 1
      · -- the ack leaf is odd: the acknowledge reads 1
        have hak : x (d.wire (m j p sb.1).ak) σ = true := by
          refine at_true hsat (ta j p sb.1) _ hta σ (fun l hl => ?_)
          rw [hlta, List.mem_singleton] at hl
          subst hl
          show x (d.wire (nodeW d rn (na j p sb.1).val)) (tau hsat (κa j p sb.1) σ) = true
          rw [hwire _ hnav hnav0 _ (by omega)]
          simp [ph, hA]
        show (x (d.wire (m j p sb.1).rq) σ || x (d.wire (m j p sb.1).ak) σ) = true
        rw [hak, Bool.or_true]
      · -- the ack leaf is at most 2k: every request leaf is exactly 2k+1, so the request reads 1
        have hrq : x (d.wire (m j p sb.1).rq) σ = true := by
          refine at_true hsat (tq j p sb.1) _ htq σ (fun l hl => ?_)
          obtain ⟨hlL, hlp⟩ := hlq l hl
          obtain ⟨hn, hlv, hlv0⟩ := leafOK_spec net rn hlL
          have wl := tau_warp hsat _ hlp
          have hlσ : tau hsat l.2 σ ≤ σ := by have := wl.le_late σ; omega
          have hlo := hO j p sb k _ hvf hk hsb hu l hl
          have hmo := Mn_mono bh l.1 (wl.mono _ _ hσ1)
          have hup := hRq j p sb σ hvf hk hsb l hl
          simp only [Mn, dif_pos hn] at hlo hmo hup
          show x (d.wire (nodeW d rn (⟨l.1, hn⟩ : Fin N).val)) _ = true
          rw [hwire ⟨l.1, hn⟩ hlv hlv0 _ (by omega)]
          have : bh.M (tau hsat l.2 σ) ⟨l.1, hn⟩ = 2 * k + 1 := by omega
          simp [ph, this, Nat.add_mod]
        show (x (d.wire (m j p sb.1).rq) σ || x (d.wire (m j p sb.1).ak) σ) = true
        rw [hrq, Bool.true_or]
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

/-- **`design_verdict9_selT`: the tree-identity select verdict with every count fact but
H_SEL_O checked.** As `design_verdict9_selTP`, with H_REQ_CNT and H_ACK_CNT replaced by checked
lines of the accepted log: per request leaf `(nq, π)` a `ReqLineT` (walk `nq → na`, ≤ 1 token,
delay `≥ phi κa − plo π`, through `reqOK` with the line list `wq`), and per copy an `AckLineT`
(walk `na → src`, no token, `Dl + phi bot ≤ dW + plo κa + 1`). Select-side trace hypotheses left:
C's H_BUNDLE, H_SEL_SETUP, H_SEL_O (per request leaf). -/
theorem design_verdict9_selT (hr : Recog6 d net b rn rank rw fuel) (hOK : net.OK7)
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
    (ta tq : (j : Fin N) → Fin (net.ar j) → Nat → AT) (na : (j : Fin N) → Fin (net.ar j) → Nat → Fin N)
    (κa : (j : Fin N) → Fin (net.ar j) → Nat → Path)
    (wq : (j : Fin N) → Fin (net.ar j) → Nat → List Nat) (wa : (j : Fin N) → Fin (net.ar j) → Nat → Nat → Nat)
    (hm : ∀ j p (sb : Nat × Bool), (rn j).virt = false → net.pk j p = PK.filt → sb ∈ selLits net rn j p →
      entOK d net rn j p sb.1 (m j p sb.1) = true ∧
      treeOK (d := d) (net := net) (rn := rn) (m j p sb.1) (ta j p sb.1) (tq j p sb.1) (na j p sb.1) (κa j p sb.1) = true ∧
      reqOK d J (na j p sb.1).val (κa j p sb.1) (AT.leaves (tq j p sb.1)) (wq j p sb.1) = true)
    (hrow : ∀ j p (sb : Nat × Bool) (i : Fin (net.nc j p)), (rn j).virt = false → net.pk j p = PK.filt →
      sb ∈ selLits net rn j p →
      holdBandS d net rn j p (m j p sb.1) i.val (cut j p i.val) (Dl j p i.val sb.1) = true ∧
      decide (AckLineT J (na j p sb.1).val (net.src j p).val (wa j p i.val sb.1) (Dl j p i.val sb.1)
        (phi d (botP d net rn j p i.val (cut j p i.val))) (plo d (κa j p sb.1))) = true)
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
        (∀ j p (sb : Nat × Bool) k u, (rn j).virt = false → net.pk j p = PK.filt → sb ∈ selLits net rn j p →
          bh.M u (net.src j p) = 2 * k + 1 → ∀ l ∈ AT.leaves (tq j p sb.1),
          2 * k + 1 ≤ Mn bh (tau hsat l.2 (O j p sb.1 k)) l.1) →
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
  obtain ⟨bh, hc, hgc, _, H⟩ := design_verdict9_selTP hr hOK hJ back line xS xw xa hl gd cp cxm cl cg
    hcp hcx hcl hcg m cut Dl ta tq na κa (fun j p sb hv hk hs => ⟨(hm j p sb hv hk hs).1, (hm j p sb hv hk hs).2.1⟩)
    (fun j p sb i hv hk hs => (hrow j p sb i hv hk hs).1) hsat h0 h1 hT hrst harb sel
  refine ⟨bh, hc, hgc, fun hp hvirt R O hheld hO hsetup hwin hsel rB rX rL rG => ?_⟩
  have hA := runLog_sound bh hOK hp hJ
  refine H hp hvirt R O hheld hO ?_ ?_ hsetup hwin hsel rB rX rL rG
  · intro j p sb v hv hk hs l hl
    obtain ⟨_, hTr, hq⟩ := hm j p sb hv hk hs
    obtain ⟨_, _, _, hκp, _, hlq⟩ := treeOK_spec hTr
    obtain ⟨w, hw⟩ := reqOK_mem d _ _ hq l hl
    exact reqCnt_of_lineT bh hA hw (tau_warp hsat _ (hlq l hl).2) (tau_warp hsat _ hκp) (Nat.le_refl _) v
  · intro j p sb i k r σ hv hk hs hu hσ
    obtain ⟨_, hTr, _⟩ := hm j p sb hv hk hs
    obtain ⟨_, _, _, hκp, _, _⟩ := treeOK_spec hTr
    have hn := hr.2 j hv
    have hok := (full_ok hr.1 j hn p i).1
    have hbot : pathOK d (botP d net rn j p i.val (cut j p i.val)) = true := by
      unfold botP; unfold pathOK at hok ⊢
      exact List.all_eq_true.mpr fun e he => List.all_eq_true.mp hok e (List.mem_of_mem_drop he)
    exact ackCnt_of_lineT bh hA (tau_warp hsat _ hbot) (tau_warp hsat _ hκp)
      (of_decide_eq_true (hrow j p sb i hv hk hs).2) k r σ hu hσ

end

end Formal.Core.XAudit.Events9SelL
