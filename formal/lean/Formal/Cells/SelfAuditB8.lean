import Formal.Cells.AssumeGuaranteeCap
import Formal.Cells.ResetCapstoneMap
import Formal.Net.CapstoneWitnessData

/-!
# SelfAuditB8 (probe Bsa5, shard B): checks found while auditing shard B's work since self-audit 4

Note: `formal/notes/B-self-audit5.md`. Core Lean only (no Mathlib).

## Assumed / proved / NOT covered

**Assumed:** nothing beyond the imported files.

**Proved:**
1. `physLink_req_alternates`: Bfb2's `PhysLink i o` (the hypothesis that replaces `H_CELLS` for
   every link in `LutFbBridge2Env.gcd_hw_safe_phys_links`, and that `AssumeGuaranteeCap.InChain`
   produces for `gcd_hw_safe_chains`) forces the input request `i.req` to be high at some
   `t ≥ T` and low at some `t ≥ T`, for EVERY `T`: the link handshakes infinitely often.
   `eventually_const_not_physLink`: a request that is constant from some time on admits no
   `PhysLink`.
2. `chW_not_physLink`, `chW_not_inChain`: C's witness run `Wit.chW` (finite event lists) meets
   `PhysLink` / `InChain` on NO channel pair; `chW_fails_H_LINKS` / `chW_fails_H_LINKS_chain`:
   it violates the `H_LINKS` hypothesis of both end-to-end theorems. So the only joint witness
   of C's capstone hypotheses in the repository is outside both theorems; neither theorem has a
   joint non-vacuity witness, and every run in which some gcd_hw link stops handshaking (for
   instance a run that computes one gcd and goes quiet) is outside them.
3. `μS_wire`, `μS_ne`: a second channel map `μS` (the requests of channels 13 and 14 swapped)
   meets the strengthened predicate `ResetCapstoneMap.WireOK` and differs from the generated
   table `μT`. So `WireOK` (with `MapOK`) does not determine the table: that row `c` is the
   driver of C's wire `c` rests on the generator only, as `ResetCapstoneMap`'s header says.

**NOT covered:** whether a gcd_hw run with every link handshaking infinitely often exists (C's
network from a single start offer); the other findings of the note are reading, not Lean.
-/

namespace Formal.Cells.SelfAuditB8
open Formal.Cells
open Formal.Cells.WinFifoCausal (Stage Env1 Timing1 cph τs nt_lo)
open Formal.Cells.PipeTimed (Vph)

/-! ## 1. `PhysLink` forces infinitely many handshakes -/

section phys
open Formal.Cells.LutFbBridge2Env (PhysLink)

/-- The phase starts of a `PhysLink` environment grow by at least one tick per phase. -/
theorem rho_step {req ack rst c qp : Nat → Bool} {lo hi wl wh R Es Ea : Nat} {ρ α : Nat → Nat}
    (S : Stage req ack rst c qp lo hi wl wh) (E : Env1 req ack rst c lo hi R ρ α Es Ea)
    (T : Timing1 lo hi wh R Es Ea) (hpos : 1 ≤ lo) (j : Nat) : ρ j + 1 ≤ ρ (j + 1) := by
  have h1 := E.H_SND j
  have h2 := nt_lo c (cph ρ α j) (Vph j) (WinFifoCausal.s_lh S E T)
  have h3 : ρ j ≤ cph ρ α j := Nat.le_max_left _ _
  unfold τs at h1
  omega

theorem rho_ge {ρ : Nat → Nat} (h : ∀ j, ρ j + 1 ≤ ρ (j + 1)) : ∀ j, j ≤ ρ j := by
  intro j
  induction j with
  | zero => exact Nat.zero_le _
  | succ j ih => have := h j; omega

/-- **`PhysLink` forces infinitely many handshakes on the input request.** -/
theorem physLink_req_alternates {i o : Formal.Net.Handshake.Chan} (h : PhysLink i o) :
    ∀ T, (∃ t, T ≤ t ∧ i.req t = true) ∧ (∃ t, T ≤ t ∧ i.req t = false) := by
  obtain ⟨rst, c, qp, lo, hi, wl, wh, R, Es, Ea, wla, wha, wlr, whr, ρ, α, S, E, Tm, hpos, -⟩ := h
  have st := rho_step S E Tm hpos
  have ge := rho_ge st
  intro T
  refine ⟨⟨ρ (2 * T), ?_, ?_⟩, ⟨ρ (2 * T + 1), ?_, ?_⟩⟩
  · have := ge (2 * T); omega
  · rw [E.H_REQ (2 * T) (ρ (2 * T)) (Nat.le_refl _) (by have := st (2 * T); omega)]
    exact PipeTimed.Vph_even T
  · have := ge (2 * T + 1); omega
  · rw [E.H_REQ (2 * T + 1) (ρ (2 * T + 1)) (Nat.le_refl _) (by have := st (2 * T + 1); omega)]
    exact PipeTimed.Vph_odd T

/-- A request constant from some time on admits no `PhysLink`. -/
theorem eventually_const_not_physLink {i o : Formal.Net.Handshake.Chan}
    (hc : ∃ T, ∀ t, T ≤ t → i.req t = i.req T) : ¬ PhysLink i o := by
  intro h
  obtain ⟨T, hT⟩ := hc
  obtain ⟨⟨t1, h1, e1⟩, ⟨t2, h2, e2⟩⟩ := physLink_req_alternates h T
  rw [hT t1 h1] at e1; rw [hT t2 h2] at e2
  rw [e1] at e2; exact absurd e2 (by decide)

end phys

/-! ## 2. C's witness run is outside both end-to-end link theorems -/

section witness
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapNet.Wit (cntLt bv chW cdA)
open Formal.Cells.LutFbBridge2Env (PhysLink isLink isLink_eq)

/-- A bound above every element of a list. -/
def ub : List Nat → Nat
  | [] => 0
  | e :: L => max (e + 1) (ub L)

theorem lt_ub : ∀ (L : List Nat) (e : Nat), e ∈ L → e < ub L
  | [], _, h => absurd h (List.not_mem_nil)
  | x :: L, e, h => by
    rcases List.mem_cons.1 h with rfl | h'
    · unfold ub; omega
    · have := lt_ub L e h'; unfold ub; omega

theorem cntLt_full : ∀ (L : List Nat) (t : Nat), (∀ e ∈ L, e < t) → cntLt L t = L.length
  | [], _, _ => rfl
  | x :: L, t, h => by
    have hx : x < t := h x (List.mem_cons_self ..)
    have ih := cntLt_full L t (fun e he => h e (List.mem_cons_of_mem _ he))
    simp only [cntLt, ih, if_pos hx, List.length_cons]

/-- An event-list signal is constant from `ub L` on. -/
theorem bv_const (L : List Nat) : ∀ t, ub L ≤ t → bv L t = bv L (ub L) := by
  intro t ht
  have a := cntLt_full L t (fun e he => by have := lt_ub L e he; omega)
  have b := cntLt_full L (ub L) (fun e he => lt_ub L e he)
  unfold bv; rw [a, b]

/-- **C's witness run meets `PhysLink` on no channel pair.** -/
theorem chW_not_physLink (i o : Fin NC) : ¬ PhysLink (chW i) (chW o) :=
  eventually_const_not_physLink ⟨ub (cdA i).rq, bv_const (cdA i).rq⟩

/-- ... nor `InChain`. -/
theorem chW_not_inChain (i o : Fin NC) : ¬ AssumeGuaranteeCap.InChain chW i o :=
  fun h => chW_not_physLink i o (AssumeGuaranteeCap.physLink_of_inChain h)

/-- gcd_hw has a link operator. -/
theorem some_link : ∃ (o : Fin NO) (i o' : Fin NC), opAt o = .link i o' := by
  have h : ((List.finRange NO).filter (fun o => isLink (opAt o))).length = 175 :=
    LutFbBridge2Env.link_count
  obtain ⟨o, ho⟩ : ∃ o, o ∈ (List.finRange NO).filter (fun o => isLink (opAt o)) := by
    cases hl : (List.finRange NO).filter (fun o => isLink (opAt o)) with
    | nil => rw [hl] at h; exact absurd h (by decide)
    | cons x _ => exact ⟨x, List.mem_cons_self ..⟩
  obtain ⟨i, o', e⟩ := isLink_eq (List.mem_filter.1 ho).2
  exact ⟨o, i, o', e⟩

/-- **C's witness violates `H_LINKS` of `LutFbBridge2Env.gcd_hw_safe_phys_links`.** -/
theorem chW_fails_H_LINKS :
    ¬ ∀ (o : Fin NO) (i o' : Fin NC), opAt o = .link i o' → PhysLink (chW i) (chW o') := by
  intro h
  obtain ⟨o, i, o', e⟩ := some_link
  exact chW_not_physLink i o' (h o i o' e)

/-- **... and `H_LINKS` of `AssumeGuaranteeCap.gcd_hw_safe_chains`.** -/
theorem chW_fails_H_LINKS_chain :
    ¬ ∀ (o : Fin NO) (i o' : Fin NC), opAt o = .link i o' → AssumeGuaranteeCap.InChain chW i o' := by
  intro h
  obtain ⟨o, i, o', e⟩ := some_link
  exact chW_not_inChain i o' (h o i o' e)

end witness

/-! ## 3. `WireOK` does not determine the channel table -/

section map
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Cells.TernarySound Formal.Cells.ResetContract Formal.Cells.ResetGcd
open Formal.Cells.ResetCapstone Formal.Cells.ResetCapstoneMap

/-- The generated table with the requests of channels 13 and 14 (nodes 3062 and 3069)
exchanged. -/
def μS : ChanMap :=
  ⟨fun c => if c.val = 13 then 3069 else if c.val = 14 then 3062 else reqL.getD c.val 0,
   fun c => ackL.getD c.val 0⟩

theorem μS_ne : μS.μR ⟨13, by decide⟩ ≠ μT.μR ⟨13, by decide⟩ := by decide

theorem μS_ok_b : (List.finRange NC).all (fun c =>
    gCtl (μS.μR c) && (μS.μR c != 0) && gCtl (μS.μA c) && (μS.μA c != 0) &&
    (onesL.contains (μS.μR c) == hot c) && (onesL.contains (μS.μA c) == decide (c.val = 3))) =
    true := by decide +kernel

theorem μS_ok : MapOK μS := by
  intro c
  have := List.all_eq_true.1 μS_ok_b c (List.mem_finRange c)
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at this
  obtain ⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩ := this
  refine ⟨a1, a2, a3, a4, ?_, ?_⟩
  · rw [← List.contains_iff_mem, a5]
  · rw [← List.contains_iff_mem, a6]; simp

theorem copyOK_S : copyOK μS = true := by decide +kernel
theorem cas_eq_S : ops.flatMap (copyAs μS) = casL := by decide +kernel
theorem drivenL_S_nodupB : nodupB (drivenOf μS crsL [0, 1, 2] casL) = true := by decide +kernel
theorem srcL_S : srcL μS = [3275, 3275, 3275] := by unfold srcL; rw [srcs_eq]; decide +kernel
theorem src_not_driven_S : (drivenOf μS crsL [0, 1, 2] casL).contains 3275 = false := by
  decide +kernel

/-- **A different table meets `WireOK`.** -/
theorem μS_wire : WireOK μS := by
  have e : drivenL μS = drivenOf μS crsL [0, 1, 2] casL := by
    unfold drivenL; rw [crs_eq, srcs_eq, cas_eq_S]
  refine ⟨μS_ok, copyOK_S, e ▸ nodupB_sound _ drivenL_S_nodupB, ?_, ?_⟩
  · intro x hx y hy
    rw [srcL_S] at hx hy
    simp at hx hy
    rw [hx, hy]
  · intro x hx hm
    rw [srcL_S] at hx
    simp at hx
    subst hx
    rw [e] at hm
    have := src_not_driven_S
    rw [List.contains_iff_mem.2 hm] at this
    exact absurd this (by decide)

/-- `WireOK` (and `MapOK`) hold for two different tables. -/
theorem wireOK_not_unique : ∃ μ₁ μ₂ : ChanMap, WireOK μ₁ ∧ WireOK μ₂ ∧ μ₁.μR ≠ μ₂.μR :=
  ⟨μS, μT, μS_wire, μT_wire, fun h => μS_ne (congrFun h _)⟩

end map

end Formal.Cells.SelfAuditB8
