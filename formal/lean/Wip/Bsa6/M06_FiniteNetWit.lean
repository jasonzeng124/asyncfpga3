-- MUTANT M06_FiniteNetWit of Formal/Cells/FiniteNetWit.lean: witness claims out0 carries 4 instead of gcd(12,18) = 6 (must FAIL)
import Formal.Cells.FiniteNet
import Formal.Cells.FiniteRunsWitData

/-!
# Probe Bfin2 (shard B): C's terminating gcd run meets the DERIVED-environment theorem

Note: `formal/notes/B-finite-net.md`. Companion of `FiniteNet`.

## Assumed / proved / NOT covered

**Assumed:** nothing beyond the imported files. The kernel checks are Bfin's (`lk_all`,
`FiniteRunsWitData`, the checker `linkB` on all 175 links of `chW`); nothing is re-decided.

**Proved:**
* `linkB_chain`: Bfin's checker `linkB x y = true` implies `FInChain x.ch y.ch`: the link
  sits in a three-cell chain (the producer's request node as source, the link, the
  consumer's acknowledge node as sink, every node read off the run one tick before its
  pin) that meets every field of `FChain`/`FChainT` with finite edge counts (the request's,
  `min nr (na + 1)`, the acknowledge's), unit LUT and wire delays, `R = 2`, end waits
  `lo = 1`, so Bnet's derived slacks are `Es = Ea = 3` (the slacks Bfin's checker verified).
* `chW_fin_chains`: every link of `chW` (a = 12, b = 18, quiet after 476 ticks) is
  `FInChain`.
* `gcd_hw_fin_chains_witness`: `chW` meets ALL hypotheses of
  `FiniteNet.gcd_hw_safe_fin_chains` together, and out0 latches a token carrying 6;
  `gcd_hw_fin_chains_consistent` applies the theorem to it.

**NOT covered:** the chains are the shortest ones (one link between two END cells), not
gcd_hw's maximal link chains (`AssumeGuaranteeCap.chain_lengths`: up to 3 links), and the
END contracts hold on the run because their conclusions do (as in Bnet's witnesses); the
run is C's unit-delay simulation (every B window met at width 0), `R = 2` is chosen.
Core Lean only.
-/

namespace Formal.Cells.FiniteNetWit
open Formal.Cells
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapSafe
open Formal.Net.CapNet.Wit (CD cntLt bv nv chW cdA bv_zero)
open Formal.Cells.WinFifoCausal (Stage Timing1 cph τs nt nt_eq noRevertI_shift)
open Formal.Cells.PipeTimed (Vph ex)
open Formal.Cells.LutFbBridge2Env (Wire ε ash isLink)
open Formal.Cells.FiniteRunsWit (sortedB bv_phase bv_low all_t bv_tail nv_tail lutQ datQ sndQ
  rcvQ linkB cL rst2 c2nB_eq wire_shift NB lk_all)
open Formal.Cells.AssumeGuaranteeLinks (ChainData)
open Formal.Cells.FiniteNet

/-! ## 1. Event-list facts -/

theorem getD_or : ∀ (L : List Nat) (j d : Nat), L.getD j d ∈ L ∨ L.getD j d = d
  | [], _, _ => Or.inr (by simp)
  | a :: L, 0, _ => Or.inl (by simp)
  | a :: L, j + 1, d => by
    simp only [List.getD_cons_succ]
    rcases getD_or L j d with h | h
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · exact Or.inr h

theorem getD_irrel : ∀ (L : List Nat) (j d d' : Nat), j < L.length → L.getD j d = L.getD j d'
  | [], _, _, _, h => absurd h (by simp)
  | a :: L, 0, _, _, _ => by simp
  | a :: L, j + 1, d, d', h => by
    simp only [List.getD_cons_succ]; exact getD_irrel L j d d' (by simp at h; omega)

theorem sorted_ge1 : ∀ (L : List Nat), sortedB L = true → 1 ≤ L.getD 0 1 → ∀ j, 1 ≤ L.getD j 1
  | [], _, _, j => by simp
  | a :: L, hs, h0, j => by
    simp only [sortedB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hs
    simp only [List.getD_cons_zero] at h0
    cases j with
    | zero => simpa using h0
    | succ j =>
      simp only [List.getD_cons_succ]
      rcases getD_or L j 1 with h | h
      · have := hs.1 _ h; omega
      · omega

theorem sorted_succ : ∀ (L : List Nat), sortedB L = true → ∀ (j d : Nat), j + 1 < L.length →
    L.getD j d < L.getD (j + 1) d
  | [], _, _, _, h => absurd h (by simp)
  | [_], _, _, _, h => absurd h (by simp)
  | a :: b :: L, hs, j, d, h => by
    have hs' := hs
    rw [sortedB, Bool.and_eq_true] at hs'
    cases j with
    | zero =>
      have := List.all_eq_true.1 hs'.1 b (by simp)
      simpa using this
    | succ j =>
      simp only [List.getD_cons_succ]
      exact sorted_succ (b :: L) hs'.2 j d (by simp at h ⊢; omega)

/-- An event-list node `cL L` (the pin `bv L` one tick earlier) is a step signal with edges
`L[j]` and `L.length` edges. -/
theorem cL_gph {L : List Nat} (hs : sortedB L = true) :
    GPh (cL L) (fun j => L.getD j 1) (fun j => j < L.length) := by
  intro _
  refine ⟨fun s _ h => bv_low L hs (s + 1) 1 ?_, fun j s _ hj h1 h2 => bv_phase L hs j (s + 1) 1
    hj (by omega) (fun h => by have := h2 h; omega)⟩
  rcases h with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

theorem eps_bv {L : List Nat} (hs : sortedB L = true) (j : Nat) (hj : j < L.length) :
    ε (bv L) 1 1 (fun j => L.getD j 1) j = L.getD j 1 + 1 := by
  show nt (bv L) 1 1 (L.getD j 1) (Vph j) = _
  exact nt_eq _ (Nat.le_refl 1) (bv_phase L hs j _ 1 hj (by omega)
    (fun h => by have := sorted_succ L hs j 1 h; omega))

/-! ## 2. The checker, unpacked -/

theorem linkB_facts {x y : CD} (h : linkB x y = true) :
    x.ak = y.rq ∧ sortedB x.rq = true ∧ sortedB y.ak = true ∧ bv y.rq 1 = false ∧
    1 ≤ x.rq.getD 0 1 ∧
    Stage (bv x.rq) (bv y.ak) rst2 (cL y.rq) (bv y.rq) 1 1 1 1 ∧
    (∀ j, j < x.rq.length → sndQ x y j = true) ∧ (∀ j, j < y.ak.length → rcvQ x y j = true) ∧
    (∀ t, cL y.rq t = true → nv y.d0 y.dt t = nv x.d0 x.dt t) ∧
    (∀ t, cL y.rq (t + 1) = false → nv y.d0 y.dt (t + 1) = nv y.d0 y.dt t) := by
  simp only [linkB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hak, bx⟩, by1⟩, by2⟩, bdx⟩, bdy⟩, sx⟩, sy⟩, c0⟩, r0⟩, hlut⟩, hdat⟩, hsnd⟩,
    hrcv⟩ := h
  have hNB : NB = 480 := rfl
  have lutA : ∀ t, lutQ x y t = true := all_t NB hlut (fun t ht => by
    unfold lutQ
    rw [bv_tail by1 (t + 2) (by omega), bv_tail bx t ht, bv_tail by2 t ht, bv_tail by1 t ht,
      bv_tail by1 (NB + 2) (by omega), bv_tail bx NB (Nat.le_refl _),
      bv_tail by2 NB (Nat.le_refl _), bv_tail by1 NB (Nat.le_refl _)]
    simp [show ¬ t < 2 by omega, show ¬ NB < 2 by omega])
  have datA : ∀ t, datQ x y t = true := all_t NB hdat (fun t ht => by
    unfold datQ
    rw [bv_tail by1 (t + 1) (by omega), bv_tail by1 (t + 2) (by omega),
      bv_tail by1 (NB + 1) (by omega), bv_tail by1 (NB + 2) (by omega),
      nv_tail y.d0 bdy t ht, nv_tail y.d0 bdy (t + 1) (by omega), nv_tail x.d0 bdx t ht,
      nv_tail y.d0 bdy (NB + 1) (by omega)])
  have hex : ∀ t, cL y.rq (t + 1) = ex (bv x.rq) (bv y.ak) (bv y.rq) rst2 t := fun t => by
    have := lutA t
    unfold lutQ at this
    unfold ex; rw [c2nB_eq]
    simpa [cL, rst2] using this
  refine ⟨hak, sx, sy, c0, r0, ⟨CElemTiming.transport_winDelay (Nat.le_refl 1) (Nat.le_refl 1) hex,
      noRevertI_shift (fun t ht => by
        have := hex (t - 1); rw [Nat.sub_add_cancel ht] at this; exact this),
      CElemTiming.transport_winDelay (Nat.le_refl 1) (Nat.le_refl 1) (fun _ => rfl), by decide⟩,
    fun j hj => List.all_eq_true.1 hsnd j (List.mem_range.2 hj),
    fun j hj => List.all_eq_true.1 hrcv j (List.mem_range.2 hj), fun t hc => ?_, fun t hc => ?_⟩
  · have := datA t
    simp only [datQ, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at this
    rcases this.1 with h | h
    · exact absurd hc (by simp [cL, h])
    · exact h
  · have := datA t
    simp only [datQ, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at this
    rcases this.2 with h | h
    · exact absurd hc (by simp [cL, h])
    · exact h

/-! ## 3. The three-cell chain around one link -/

def τ0 (x : CD) (j : Nat) : Nat := x.rq.getD j 1
def τ2 (y : CD) (j : Nat) : Nat := y.ak.getD j 1
def ρc (x : CD) : Nat → Nat := ε (bv x.rq) 1 1 (τ0 x)
def αc (y : CD) : Nat → Nat := ash 2 (ε (bv y.ak) 1 1 (τ2 y))
def τ1 (x y : CD) : Nat → Nat := τs (cL y.rq) 1 1 (ρc x) (αc y)

/-- Source (cell 0): the producer's request node; link (cell 1); sink (cell 2): the
consumer's acknowledge node. Every node is its pin one tick earlier. -/
def chD (x y : CD) : ChainData where
  N := 1
  R := 2
  O | 0 => cL x.rq | 1 => cL y.rq | _ => cL y.ak
  req | 1 => bv x.rq | _ => bv y.rq
  ack | 0 => bv x.ak | _ => bv y.ak
  qp _ := bv y.rq
  rst := rst2
  lo _ := 1
  hi _ := 1
  fl _ := 1
  fh _ := 1
  wl _ := 1
  wh _ := 1
  vl _ := 1
  vh _ := 1
  τ | 0 => τ0 x | 1 => τ1 x y | _ => τ2 y

def cnt3 (x y : CD) : Nat → Nat
  | 0 => x.rq.length
  | 1 => min x.rq.length (y.ak.length + 1)
  | _ => y.ak.length

def L3 (x y : CD) (i j : Nat) : Prop := j < cnt3 x y i

section chain
variable {x y : CD} (h : linkB x y = true)
include h

/-- On the phases that exist, the chain's phase starts are the checker's. -/
theorem cph_eq (j : Nat) (hr : j < x.rq.length) (ha : j ≤ y.ak.length) :
    cph (ρc x) (αc y) j = cph (FiniteRunsWit.ρL x.rq) (FiniteRunsWit.αL y.ak) j := by
  obtain ⟨_, sx, sy, _⟩ := linkB_facts h
  have e1 : ρc x j = FiniteRunsWit.ρL x.rq j := eps_bv sx j hr
  have e2 : αc y j = FiniteRunsWit.αL y.ak j := by
    cases j with
    | zero => rfl
    | succ k =>
      show ε (bv y.ak) 1 1 (τ2 y) k = y.ak.getD k 0 + 1
      rw [show τ2 y = fun j => y.ak.getD j 1 from rfl, eps_bv sy k (by omega),
        getD_irrel y.ak k 1 0 (by omega)]
  unfold cph; rw [e1, e2]

/-- The link's node edge and the pin edge one wire later, from the checker's `Vph` test. -/
theorem link_edges (j : Nat) (hr : j < x.rq.length) (ha : j ≤ y.ak.length)
    (hv : cL y.rq (cph (FiniteRunsWit.ρL x.rq) (FiniteRunsWit.αL y.ak) j + 1) = Vph j) :
    τ1 x y j = cph (FiniteRunsWit.ρL x.rq) (FiniteRunsWit.αL y.ak) j + 1 ∧
    ε (bv y.rq) 1 1 (τ1 x y) j = cph (FiniteRunsWit.ρL x.rq) (FiniteRunsWit.αL y.ak) j + 2 := by
  have e := cph_eq h j hr ha
  have t1 : τ1 x y j = cph (FiniteRunsWit.ρL x.rq) (FiniteRunsWit.αL y.ak) j + 1 := by
    unfold τ1 τs; rw [e]; exact nt_eq _ (Nat.le_refl 1) hv
  refine ⟨t1, ?_⟩
  unfold ε; rw [t1]; exact nt_eq _ (Nat.le_refl 1) hv

theorem chD_chain : FChain (chD x y) (L3 x y) := by
  obtain ⟨hak, sx, sy, c0, r0, St, hsnd, hrcv, _, _⟩ := linkB_facts h
  refine { H_RST := fun _ => rfl
           H_STAGE := fun m hm => ?_
           H_PWR := fun m hm t ht => ?_
           H_LUT_POS := fun _ _ => Nat.le_refl 1
           H_WF := fun i hi => ?_
           H_WB := fun i hi => ?_
           H_TIMES := fun m hm j => ?_
           H_CNT := fun m hm j => ?_
           SRC_T := fun j => ?_
           SRC_WAIT := fun j h1 h2 => ?_
           SRC_SEG := fun T _ => ?_
           SNK_T := fun j _ => ?_
           SNK_WAIT := fun j h1 h2 => ?_
           SNK_SEG := fun T _ => ?_ }
  · have : m = 0 := by change m < 1 at hm; omega
    subst this; exact St
  · have : m = 0 := by change m < 1 at hm; omega
    subst this
    have : t = 0 := by change t < 1 at ht; omega
    subst this; exact c0
  · rcases (show i = 0 ∨ i = 1 by change i ≤ 1 at hi; omega) with rfl | rfl
    · exact wire_shift x.rq
    · exact wire_shift y.rq
  · rcases (show i = 0 ∨ i = 1 by change i ≤ 1 at hi; omega) with rfl | rfl
    · show Wire 1 1 (cL y.rq) (bv x.ak); rw [hak]; exact wire_shift y.rq
    · exact wire_shift y.ak
  · have : m = 0 := by change m < 1 at hm; omega
    subst this; rfl
  · have : m = 0 := by change m < 1 at hm; omega
    subst this
    show j < min x.rq.length (y.ak.length + 1) ↔
      LnL (fun j => j < x.rq.length) (fun j => j < y.ak.length) j
    exact (lnL_fin x.rq.length y.ak.length j).symm
  · show 2 ≤ x.rq.getD j 1 + 1
    have := sorted_ge1 x.rq sx r0 j; omega
  · -- the source waits for the link's acknowledge
    have hr : j + 1 < x.rq.length := h1
    have hl : j < min x.rq.length (y.ak.length + 1) := h2
    have q := hsnd j (by omega)
    simp only [sndQ, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, Bool.and_eq_true, beq_iff_eq] at q
    rcases q with (q | q) | ⟨q1, q2⟩
    · exact absurd hr q
    · exact absurd (show j ≤ y.ak.length by omega) q
    · obtain ⟨_, e2⟩ := link_edges h j (by omega) (by omega) q1
      show ε (bv x.ak) 1 1 (τ1 x y) j + 1 ≤ x.rq.getD (j + 1) 1
      have e3 : FiniteRunsWit.ρL x.rq (j + 1) = x.rq.getD (j + 1) 1 + 1 := rfl
      rw [hak, e2]; omega
  · exact gphT_mono (cL_gph sx (T + 1)) (Nat.le_refl _)
  · show 1 ≤ y.ak.getD j 1 + 1; omega
  · -- the sink waits for the link's request
    have ha : j < y.ak.length := h1
    have hl : j < min x.rq.length (y.ak.length + 1) := h2
    have q := hrcv j ha
    simp only [rcvQ, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, Bool.and_eq_true, beq_iff_eq] at q
    rcases q with (q | q) | ⟨q1, q2⟩
    · exact absurd ha q
    · exact absurd (show j < x.rq.length by omega) q
    · obtain ⟨_, e2⟩ := link_edges h j (by omega) (by omega) q1
      show ε (bv y.rq) 1 1 (τ1 x y) j + 1 ≤ y.ak.getD j 1
      rw [e2, getD_irrel y.ak j 1 0 ha]
      rw [FiniteRunsWit.αL_succ] at q2; omega
  · exact gphT_mono (cL_gph sy (T + 1)) (Nat.le_refl _)

omit h in
theorem chD_chainT : FChainT (chD x y) where
  H_RST_LONG _ _ := by show 1 + 1 ≤ 2; decide
  H_LAT _ _ := by show 1 + 1 ≤ 1 + min (1 + 1 + 1) (1 + 1 + 1); decide
  H_WIRE_R _ _ := by show 1 ≤ 2 ∧ 1 ≤ 2; decide

/-- **Bfin's checker gives the link a DERIVED-environment chain** (`FInChain`). -/
theorem linkB_chain : FInChainC x.ch y.ch := by
  exact ⟨chD x y, L3 x y, cnt3 x y, 0, by show 0 < 1; decide, chD_chain h, chD_chainT,
    fun i j => Iff.rfl, rfl, rfl, rfl, rfl,
    by show 1 + 1 ≤ 2 * 1 + min (1 + 1 + 1) (1 + 1 + 1); decide,
    by show 1 + 1 ≤ 2 * 1 + min (1 + 1 + 1) (1 + 1 + 1); decide,
    (linkB_facts h).2.2.2.2.2.2.2.2.1, (linkB_facts h).2.2.2.2.2.2.2.2.2⟩

end chain

end Formal.Cells.FiniteNetWit

namespace Formal.Cells.FiniteNetWit
open Formal.Cells
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapSafe
open Formal.Net.CapNet.Wit (CD chW cdA)
open Formal.Cells.LutFbBridge2Env (isLink)
open Formal.Cells.FiniteRunsWit (lkChk lk_all)
open Formal.Cells.FiniteNet

/-! ## 4. C's witness run -/

/-- **Every one of the 175 links of C's terminating run `chW` sits in a derived-environment
chain** (Bfin's kernel checks `lk_all`, reused). -/
theorem chW_fin_chains :
    ∀ (o : Fin NO) (i o' : Fin NC), opAt o = .link i o' → FInChain chW i o' := by
  intro o i o' e
  have := List.all_eq_true.mp lk_all _ (getD_mem (o := o))
  rw [e] at this
  exact linkB_chain this

open Formal.Net.CapNet.Wit (w_cells w_held w_start_once yW yW_good yW_walk w_out0 out0Close
  gcd_12_18)

/-- **Joint non-vacuity of `FiniteNet.gcd_hw_safe_fin_chains`** on C's terminating run
(a = 12, b = 18): every hypothesis holds together, and out0 latches a token carrying 6. -/
theorem gcd_hw_fin_chains_witness :
    ∃ ch : Fin NC → Chan,
      (∀ (o : Fin NO) (i o' : Fin NC), opAt o = .link i o' → FInChain ch i o') ∧
      (∀ o : Fin NO, isLink (opAt o) = false → Cell ch (srcV 12 18) (opAt o)) ∧
      (∀ c, Held (ch c)) ∧
      (∃ y, Good 12 18 y ∧ ∀ o : Fin NO, Forced ch (omOf 12 18 y) (opAt o)) ∧
      (∃ k e, TokAt (ch out0) k e ∧ (ch out0).dat e = 4) :=
  ⟨chW, chW_fin_chains, fun o _ => w_cells o, w_held,
    ⟨yW, yW_good, gcd_hw_forced 12 18 chW yW yW_good w_cells w_held w_start_once yW_walk⟩,
    ⟨0, out0Close, w_out0⟩⟩

/-- The derived-environment theorem applied to the witness gives the value it latches. -/
theorem gcd_hw_fin_chains_consistent :
    (∀ k e, TokAt (chW out0) k e → (chW out0).dat e = 6) ∧ TokAt (chW out0) 0 out0Close := by
  have h := gcd_hw_safe_fin_chains 12 18 chW chW_fin_chains (fun o _ => w_cells o)
    w_held ⟨yW, yW_good, gcd_hw_forced 12 18 chW yW yW_good w_cells w_held w_start_once yW_walk⟩
  rw [gcd_12_18] at h
  exact ⟨h.1, w_out0.1⟩

end Formal.Cells.FiniteNetWit
