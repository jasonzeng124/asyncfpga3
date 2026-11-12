import Formal.Net.AO.UnrollClaim
import Formal.Net.AO.UnrollUX

/-!
# Claim proofs for every word, with upper-bound joins and external claims (shard C, 2026-11-10)

**Problem, plainly.** `UnrollUX.timedA_follows_unrollUX` (safety for the certificate of every word of kinds, with
claims joined by separations OR upper bounds, `TimedOccUp.ChainUOK`, and with external claims `ext` assumed) still
takes `hGC` and `hInit` as hypotheses about the LONG claim list `uclT (wk (wP ks)) 0`, which has unboundedly many
claims. `UnrollClaim` reduced these to checks on sub-words for `ChainOK` chains and no external claims; this file does
the same for `ChainUOK` and `ext`.

**How `ext` is expressed.** `ext` is a predicate on (long) claims, as in `timedA_follows_unrollUX`. A window check
can skip a claim only if skipping transfers to the long claim, which is the window claim shifted by the window's
offsets (`shC o`). So we ask `ExtShift ext`: `ext c → ext (shC o c)` for every shift `o`, and the window check
`GcWinU` skips a kind claim exactly when `ext` holds of it in the sub-word's coordinates. A per-kind Bool flag was not
used: a long claim does not record which window/kind it came from, so a flag on kind claims does not determine `ext`
on long claims without a further compatibility hypothesis about the long list (infinitely many claims). A predicate
of the claim's node and value (`fun c => P c.z c.val`, `extShift_node`), or any predicate ignoring the event indices,
is shift-closed, and that covers "the datapath condition claims" (claims on given nodes).

**Proved.**
* `chainUOK_window`: a sub-word `ChainUOK` chain (sub-word tables `Sep'`, `Up'`, restricted to the sub-word's events),
  shifted by `o`, is a `ChainUOK` chain for the long tables, given the window correspondences (`sep_win`, `up_win`,
  `wsep_dom`, `wup_dom` of `UnrollTime` supply them).
* `GcWinU`: the window check (as `UnrollClaim.GcWin`, with `ChainUOK` over `WSep s`, `WUp s`, skipping claims with
  `ext`).
* `gc_unrollU_gen`, `gc_unrollU`, `gc_unrollU_kind`: the hypothesis `hGC` of `timedA_follows_unrollUX` for every word
  from `GcWinU` on the sub-words `(ks.drop (i - 1)).take r` (`r ≥ 2`), with the start state either the long one
  flipped by the event-count parities before the sub-word, or (under `StChain`) the sub-word's first kind's own.
* `timedA_follows_unrollUXC`: `timedA_follows_unrollUX` with `hGC` replaced by the `GcWinU` checks and `hInit` by
  `UnrollClaim.init_unroll`'s per-kind check.

**Not shown.** That any instance (the target's kinds) passes the checks; `hExt` (the external claims' truth) and
`hEnvC` are NOT reduced; liveness with `ChainUOK`/`ext` (no `timedA_liveUX` unroll exists here). The checks are only
sufficient, with the same restrictions as `UnrollClaim` (a claim of window `i` must be proved, and its chain built,
inside the sub-word from window `i - 1`; `.ex 0` only in sub-words starting the word). Chain members are never
skipped as external: each must have a `GateProofW`, since `hGC` demands a `GateProof` of every chain member.
-/

namespace Formal.Net.AO
open Formal.Net.OccNet (st)
open Formal.Net.OccNet.Timed Formal.Net.OccNet.TimedX Formal.Net.OccNet.TimedR Formal.Net.OccNet.TimedU

variable {α : Type} [DecidableEq α]
set_option linter.unusedSectionVars false

/-! ## Chains with upper-bound joins, shifted -/

section transfer
variable {C' : Cert α} {Sep Sep' : α → Nat → α → Nat → Option Nat} {Up Up' : α × Nat → α × Nat → Option Nat}
  {o : α → Nat}

/-- **A shifted `ChainUOK` chain is a chain** for the long separation and upper-bound tables, when the window's
chain is one for the window's (restricted) tables. -/
theorem chainUOK_window
    (hSep : ∀ b m a k, m < C'.len b → k < C'.len a → Sep b (m + o b) a (k + o a) = Sep' b m a k)
    (hSepDom : ∀ b m a k d, Sep' b m a k = some d → m < C'.len b ∧ k < C'.len a)
    (hUp : ∀ e0 e : α × Nat, e0.2 < C'.len e0.1 → e.2 < C'.len e.1 → Up (shE o e0) (shE o e) = Up' e0 e)
    (hUpDom : ∀ e0 e d, Up' e0 e = some d → e0.2 < C'.len e0.1 ∧ e.2 < C'.len e.1) :
    ∀ (cs : List (Claim α)) (c : Claim α), ChainUOK Sep' Up' c cs → ChainUOK Sep Up (shC o c) (cs.map (shC o))
  | [], _, h => h.elim
  | [c1], c, h => by
    obtain ⟨hz, hv, hA, ha, hB, hb⟩ := h
    simp only [List.map_cons, List.map_nil, ChainUOK, shC]
    exact ⟨hz, hv, by rw [hA], ha, by rw [hB], hb⟩
  | c1 :: c2 :: cs, c, h => by
    obtain ⟨hz, hv, hA, ha, hj, hrest⟩ := h
    have ih := chainUOK_window hSep hSepDom hUp hUpDom (c2 :: cs) ⟨c.z, c.val, c2.A, c2.a, c.B, c.b⟩ hrest
    simp only [List.map_cons] at ih ⊢
    refine ⟨hz, hv, by simp only [shC]; rw [hA], ha, ?_, ih⟩
    cases hB1 : c1.B with
    | none => simp [shC, hB1]
    | some e1 =>
      cases hA2 : c2.A with
      | none => simp [shC, hB1, hA2]
      | some e2 =>
        rw [hB1, hA2] at hj
        simp only [shC, hB1, hA2, Option.map]
        rcases hj with ⟨d, hd, hle⟩ | ⟨u, hu, h1, hle⟩
        · left
          obtain ⟨h1, h2⟩ := hSepDom _ _ _ _ _ hd
          exact ⟨d, by simp only [shE]; rw [hSep e2.1 e2.2 e1.1 e1.2 h1 h2]; exact hd, hle⟩
        · right
          obtain ⟨h0, h2⟩ := hUpDom _ _ _ hu
          exact ⟨u, by rw [hUp e1 e2 h0 h2]; exact hu, h1, hle⟩

end transfer

/-! ## External claims under shifts -/

/-- `ext` is closed under shifting a claim's events: an external window claim stays external in the long list. -/
def ExtShift (ext : Claim α → Prop) : Prop := ∀ (o : α → Nat) (c : Claim α), ext c → ext (shC o c)

/-- A predicate of a claim's node and value is shift-closed. -/
theorem extShift_node (P : α → Bool → Prop) : ExtShift (fun c : Claim α => P c.z c.val) :=
  fun _ _ h => h

/-! ## The claim hypothesis `hGC` of `timedA_follows_unrollUX` for every word -/

/-- **The window check for claim proofs with upper-bound joins and external claims** of the sub-word `s` (target
window `t`), with `s0` the state at the start of `s`: every claim of window `t`'s kind on a gate, shifted to `s`'s
coordinates, that is not external (`ext`, read in `s`'s coordinates), has a proof `GateProofW` in `s`'s claim list
with `s`'s restricted separation table, or is the union (`ChainUOK` with `s`'s restricted tables `WSep s`, `WUp s`)
of a chain of claims of that list that have such proofs. A property of `s`, `t`, `s0` and `ext` only. -/
def GcWinU (N : TNet α) (dat : α → Bool) (ext : Claim α → Prop) (s0 : α → Bool) (s : List (WKindT α)) (t : Nat) :
    Prop :=
  ∀ (h : t < s.length), ∀ c0 ∈ s[t].cl, ¬ ext (shC (off (wt s) t) c0) → N.gate c0.z = true →
    GateProofW N dat (WSep s) s0 (uclT (wk s) (fun _ => 0)) t (shC (off (wt s) t) c0) ∨
    ∃ cs : List (Claim α), (∀ c' ∈ cs, c' ∈ uclT (wk s) (fun _ => 0) ∧
      GateProofW N dat (WSep s) s0 (uclT (wk s) (fun _ => 0)) t c') ∧
      ChainUOK (WSep s) (WUp s) (shC (off (wt s) t) c0) cs

/-- **`hGC` (upper-bound joins, external claims) of the long certificate, for every word, from the window checks**,
general form: as `UnrollClaim.gc_unroll_gen`, with `GcWinU` and a shift-closed `ext`. -/
theorem gc_unrollU_gen (N : TNet α) (dat : α → Bool) (ext : Claim α → Prop) (hX : ExtShift ext) (r : Nat)
    (hr : 2 ≤ r) (ks : List (WKindT α)) (s0 : α → Bool) (sw : Nat → α → Bool)
    (hsw : ∀ i, i < ks.length → ∀ w ∈ (ks.drop (i - 1)).take r, ∀ c0 ∈ w.cl, ∀ u ∈ N.pins c0.z,
      sw i u = st s0 (off (wt ks) (i - 1)) u)
    (hW : ∀ i, i < ks.length → GcWinU N dat ext (sw i) ((ks.drop (i - 1)).take r) (i - (i - 1))) :
    ∀ c ∈ uclT (wk ks) (fun _ => 0), ¬ ext c → N.gate c.z = true →
      GateProof N dat (LSep ks) s0 (uclT (wk ks) (fun _ => 0)) c ∨
      ∃ cs : List (Claim α), (∀ c' ∈ cs, c' ∈ uclT (wk ks) (fun _ => 0) ∧
        GateProof N dat (LSep ks) s0 (uclT (wk ks) (fun _ => 0)) c') ∧ ChainUOK (LSep ks) (LUp ks) c cs := by
  intro c hc hx hg
  obtain ⟨i, hi, c0, hc0, rfl⟩ := mem_uclT (wk ks) _ c hc
  have hi' : i < ks.length := by simpa [wk] using hi
  have hwi : (wk ks)[i] = ks[i].toWKind := by simp [wk]
  have ht : i - (i - 1) < ((ks.drop (i - 1)).take r).length := by simp; omega
  have hst : ((ks.drop (i - 1)).take r)[i - (i - 1)] = ks[i] := by
    simp only [List.getElem_take, List.getElem_drop]
    congr 1; omega
  have hcE : shC (fun p => (fun _ => 0) p + off (wcs (wk ks)) i p) c0 =
      shC (off (wt ks) (i - 1)) (shC (off (wt ((ks.drop (i - 1)).take r)) (i - (i - 1))) c0) := by
    rw [shC_shC]; congr 1; funext p
    have e1 := off_wt_split ks (i - 1) (i - (i - 1)) p
    rw [show i - 1 + (i - (i - 1)) = i by omega] at e1
    have e2 := off_wt_take (ks.drop (i - 1)) r (i - (i - 1)) p (by omega)
    show 0 + off (wt ks) i p = _
    omega
  have hws : wk ((ks.drop (i - 1)).take r) = ((wk ks).drop (i - 1)).take r := by rw [wk_take, wk_drop]
  have hL : ∀ n (h : n < (uclT (wk ((ks.drop (i - 1)).take r)) (fun _ => 0)).length),
      (uclT (wk ks) (fun _ => 0))[ncl ((wk ks).take (i - 1)) + n]? =
        some (shC (off (wt ks) (i - 1)) (uclT (wk ((ks.drop (i - 1)).take r)) (fun _ => 0))[n]) := by
    intro n h
    have := uclT_win (wk ks) (i - 1) r n (by rw [← hws]; exact h)
    rw [← hws] at this
    rw [this, List.getElem?_eq_getElem h]
    rfl
  have ht0 : i - (i - 1) = 0 → ∀ u, off (wt ks) (i - 1) u = 0 := by
    intro h u
    have : i = 0 := by omega
    subst this
    exact off_zero _ _
  have hc0' : c0 ∈ ks[i].cl := by rw [hwi] at hc0; exact hc0
  rw [hcE] at hx ⊢
  have hxw : ¬ ext (shC (off (wt ((ks.drop (i - 1)).take r)) (i - (i - 1))) c0) :=
    fun h => hx (hX _ _ h)
  have hW' := hW i hi' ht c0 (by rw [hst]; exact hc0') hxw hg
  rcases hW' with hp | ⟨cs, hcs, hch⟩
  · left
    exact gateProof_window (sep_win 0 ks (i - 1) r) (wsep_dom 0 ks (i - 1) r) s0 _ _ _ _ _ hL _
      (fun u hu => hsw i hi' _ (by rw [← hst]; exact List.getElem_mem ht) c0 hc0' u hu) ht0 hp
  · right
    refine ⟨cs.map (shC (off (wt ks) (i - 1))), fun c' hc' => ?_,
      chainUOK_window (sep_win 0 ks (i - 1) r) (wsep_dom 0 ks (i - 1) r) (up_win 0 ks (i - 1) r)
        (wup_dom 0 ks (i - 1) r) cs _ hch⟩
    obtain ⟨c'', hc'', rfl⟩ := List.mem_map.mp hc'
    obtain ⟨hm, hgp⟩ := hcs c'' hc''
    obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hm
    obtain ⟨j, hj, c1, hc1, heq⟩ := mem_uclT _ _ _ hm
    have hj' : j < ((ks.drop (i - 1)).take r).length := by simpa [wk] using hj
    have hwj : (wk ((ks.drop (i - 1)).take r))[j] = ((ks.drop (i - 1)).take r)[j].toWKind := by simp [wk]
    rw [hwj] at hc1
    exact ⟨List.mem_iff_getElem?.mpr ⟨_, hL n hn⟩,
      gateProof_window (sep_win 0 ks (i - 1) r) (wsep_dom 0 ks (i - 1) r) s0 _ _ _ _ _ hL _
        (fun u hu => hsw i hi' _ (List.getElem_mem hj') c1 hc1 u (by rw [heq] at hu; exact hu)) ht0 hgp⟩

/-- **`hGC` (upper-bound joins, external claims) for every word from the window checks**: the sub-word from window
`i - 1` is checked with the long start state flipped by the event-count parities before it. -/
theorem gc_unrollU (N : TNet α) (dat : α → Bool) (ext : Claim α → Prop) (hX : ExtShift ext) (r : Nat) (hr : 2 ≤ r)
    (ks : List (WKindT α)) (s0 : α → Bool)
    (hW : ∀ i, i < ks.length →
      GcWinU N dat ext (st s0 (off (wt ks) (i - 1))) ((ks.drop (i - 1)).take r) (i - (i - 1))) :
    ∀ c ∈ uclT (wk ks) (fun _ => 0), ¬ ext c → N.gate c.z = true →
      GateProof N dat (LSep ks) s0 (uclT (wk ks) (fun _ => 0)) c ∨
      ∃ cs : List (Claim α), (∀ c' ∈ cs, c' ∈ uclT (wk ks) (fun _ => 0) ∧
        GateProof N dat (LSep ks) s0 (uclT (wk ks) (fun _ => 0)) c') ∧ ChainUOK (LSep ks) (LUp ks) c cs :=
  gc_unrollU_gen N dat ext hX r hr ks s0 (fun i => st s0 (off (wt ks) (i - 1))) (fun _ _ _ _ _ _ _ _ => rfl) hW

/-- **`hGC` (upper-bound joins, external claims) for every word from checks on the sub-words alone**: as
`UnrollClaim.gc_unroll_kind`, each sub-word checked with its first kind's own start state, under `StChain`. -/
theorem gc_unrollU_kind (N : TNet α) (dat : α → Bool) (ext : Claim α → Prop) (hX : ExtShift ext) (r : Nat)
    (hr : 2 ≤ r) (ks : List (WKindT α)) (s0 : α → Bool)
    (Dv : List α) (hDv : ∀ w ∈ ks, ∀ c0 ∈ w.cl, ∀ u ∈ N.pins c0.z, u ∈ Dv) (hSC : StChain Dv (wk ks))
    (hhd : ∀ w, (wk ks).head? = some w → ∀ u ∈ Dv, w.s0 u = s0 u)
    (hW : ∀ i (hi : i < ks.length),
      GcWinU N dat ext (ks[i - 1]'(by omega)).s0 ((ks.drop (i - 1)).take r) (i - (i - 1))) :
    ∀ c ∈ uclT (wk ks) (fun _ => 0), ¬ ext c → N.gate c.z = true →
      GateProof N dat (LSep ks) s0 (uclT (wk ks) (fun _ => 0)) c ∨
      ∃ cs : List (Claim α), (∀ c' ∈ cs, c' ∈ uclT (wk ks) (fun _ => 0) ∧
        GateProof N dat (LSep ks) s0 (uclT (wk ks) (fun _ => 0)) c') ∧ ChainUOK (LSep ks) (LUp ks) c cs := by
  refine gc_unrollU_gen N dat ext hX r hr ks s0
    (fun i u => match ks[i - 1]? with | some w => w.s0 u | none => s0 u) ?_ ?_
  · intro i hi w hw c0 hc0 u hu
    have hi1 : i - 1 < ks.length := by omega
    simp only [List.getElem?_eq_getElem hi1]
    have hwk : (wk ks)[i - 1]? = some ks[i - 1].toWKind := by simp [wk, hi1]
    exact (st_off Dv (wk ks) s0 hSC hhd (i - 1) _ hwk u (hDv w (mem_sub hw) c0 hc0 u hu)).symm
  · intro i hi
    have hi1 : i - 1 < ks.length := by omega
    simp only [List.getElem?_eq_getElem hi1]
    exact hW i hi

/-! ## The timed theorem with the claim hypotheses reduced -/

section main
variable {N : TNet α} {dat : α → Bool} {envEn : α → (α → Bool) → Bool} {x : α → Nat → Bool}
  {r : α → α → Nat → Nat} {t0 H : Nat} {D : α → List α}

/-- **Safety for the certificate of every word, upper-bound joins and external claims, claim proofs and initial
claims from window checks**: `UnrollUX.timedA_follows_unrollUX` with `hGC` replaced by the window checks `GcWinU`
on the sub-words `((wP ks).drop (i - 1)).take r'` (start state: the long start state flipped by the event-count
parities before the sub-word; `ext` shift-closed) and `hInit` by the per-kind check of `UnrollClaim.init_unroll`. -/
theorem timedA_follows_unrollUXC (ext : Claim α → Prop) [DecidablePred ext] (hX : ExtShift ext)
    (BIG r' : Nat) (hr : 2 ≤ r') (ks : List (WKindF α)) (Dc : α → List α)
    (hKP : ∀ w ∈ ks, KindTm BIG w.toWKindT) (hKF : ∀ w ∈ ks, KindTm BIG w.full)
    (hcD : ∀ w ∈ wP ks, ∀ u k, ∀ alt ∈ w.causes u k, ∀ q ∈ alt, q.1 ∈ Dc u) (hBC : BackChain (wP ks))
    (hS : ∀ i, i < (wP ks).length → SepWin N BIG (((wP ks).drop (i - 1)).take r') (i - (i - 1)))
    (hU : ∀ i, i < (wP ks).length → UpWin N dat BIG (((wP ks).drop (i - 1)).take r') (i - (i - 1)))
    (hT : ∀ i, i < (wP ks).length → TOWin N BIG D (((wP ks).drop (i - 1)).take r') (i - (i - 1)))
    (hG : ∀ i, i < (wP ks).length → GdWin N (((wP ks).drop (i - 1)).take r') (i - (i - 1)))
    (hL : ∀ i (hi : i < (wF ks).length), KindLStep (if i = 0 then none else (wF ks)[i - 1]?) (wF ks)[i])
    (hRTk : ∀ w ∈ ks, KindRT w)
    (hSEk : ∀ w ∈ ks, ∀ b m a k d, w.sep b m a k = some d → dat a = false)
    (hDLk : ∀ w ∈ ks, ∀ u, dat u = true → w.len u = 0)
    (hb : TBehX N dat envEn x r t0 H) (hDE : ∀ v u, u ∈ D v → dat u = false)
    (hloc : ∀ v, N.gate v = true → dat v = false → v ∈ D v ∧
      LCheckXA N dat envEn (fun w => x w t0) (LC BIG (wP ks)) (uL (wk (wP ks)) (fun _ => 0)) D
        (uclT (wk (wP ks)) (fun _ => 0)) (fun v z => ugd v z (wk (wP ks)) (fun _ => 0) 0) v)
    (hEnvE : ∀ v s, N.gate v = false → dat v = false → t0 < s → x v s ≠ x v (s - 1) →
      Ideal (CFu BIG ks) (fun u => cntE dat x t0 u (s - 1)) → Enabled (CPu BIG ks) (fun w => cnt x t0 w (s - 1)) v)
    (hgdF : ∀ v z, N.gate v = false → ugd v z (wk (wP ks)) (fun _ => 0) 0 = [])
    (hGW : ∀ i, i < (wP ks).length → GcWinU N dat ext (st (fun w => x w t0) (off (wt (wP ks)) (i - 1)))
      (((wP ks).drop (i - 1)).take r') (i - (i - 1)))
    (hExt : ∀ c ∈ uclT (wk (wP ks)) (fun _ => 0), ext c → ∀ s,
      (∀ τ, τ ≤ s → Ideal (CFu BIG ks) (fun u => cntE dat x t0 u τ)) → Holds x t0 H c s)
    (hEnvC : ∀ c ∈ uclT (wk (wP ks)) (fun _ => 0), N.gate c.z = false → ∀ s,
      (∀ τ, τ ≤ s → Ideal (CFu BIG ks) (fun u => cntE dat x t0 u τ)) → Holds x t0 H c s)
    (hIk : ∀ i (hi : i < (wP ks).length), ∀ c0 ∈ (wP ks)[i].cl,
      (c0.A ≠ none ∧ 0 ≤ c0.a) ∨ (i = 0 ∧ ∀ s, s ≤ t0 → Holds x t0 H c0 s)) :
    ∀ t, (∀ τ, τ ≤ t → Ideal (CFu BIG ks) (fun u => cntE dat x t0 u τ)) ∧
      (∀ v s, dat v = false → t0 < s → s ≤ t → x v s ≠ x v (s - 1) → ChangeOKA N (CPu BIG ks) x t0 r v s) ∧
      (∀ c ∈ uclT (wk (wP ks)) (fun _ => 0), ∀ s, s ≤ t → Holds x t0 H c s) ∧ SepSound x t0 (LSep (wP ks)) t :=
  timedA_follows_unrollUX ext BIG r' hr ks Dc hKP hKF hcD hBC hS hU hT hG hL hRTk hSEk hDLk hb hDE hloc hEnvE hgdF
    (gc_unrollU N dat ext hX r' hr (wP ks) (fun w => x w t0) hGW) hExt hEnvC (init_unroll (wP ks) hIk)

end main

end Formal.Net.AO
