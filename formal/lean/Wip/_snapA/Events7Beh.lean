import Formal.Core.XAudit.Events6Beh
import Formal.Core.XAudit.Events7Cert

/-!
# Formal.Core.XAudit.Events7Beh — `design_beh7` and the netlist-level verdict `design_verdict7`

Probe A-events7 (rebuilt in E7r). See `formal/notes/A-events7.md`.

As `Events6Design` / `Events6Beh`, for `Beh7`:

* `ND7`: the per-node part of a `Beh7` (a guarded pin reads the AND / OR of all its
  copies); `ofND7` assembles a `Beh7` from node behaviours.
* `HARB7`: H_ARB (the arbiter cores as virtual mux cores; a HYPOTHESIS, not checked)
  with `ND7` node behaviours.
* `ndReal7`: the `ND7` of a recognised real node (`Events6.Recog6`, unchanged: a
  guarded pin's copies are `chkT`-checked like any tree pin, with its operator).
* `init0_7`, **`design_beh7`**: every per-pin behaviour (`SatPin d plG x`, no
  H_ATOMIC_LUT) of a recognised netlist with `Net4.OK7`, under H_ARB, is a `Beh7`,
  for every select sequence and every monotone guarded count `gc`.
* **`design_verdict7`** (what `xevents7` checks): with an accepted log and the
  certified items, every per-pin behaviour has a realising `Beh7` such that, if it
  satisfies SelPart, SelOK, GuardOK and the residual obligations, every real LUT
  wire equals `ph (v j) (M t j)` at every time.
-/

namespace Formal.Core.XAudit.Events7

open Formal.Core
open Formal.Core.XAudit
open Formal.Core.TraceDiscrete (Sig Warp)
open Formal.Core.XAudit.Events (ph)
open Formal.Core.XAudit.Events2 (cel)
open Formal.Core.XAudit.Events2Pin (SatPin)
open Formal.Core.XAudit.Events5
open Formal.Core.XAudit.Events6

/-- The per-node part of a `Beh7` (as `Events6.ND`; a guarded pin reads the AND /
OR of all its copies). -/
structure ND7 {N : Nat} (net : Net4 N) (b : Bands4 net) (cc : Fin N → Sig) (j : Fin N) where
  pin : Fin (net.ar j) → Sig
  q : Sig
  r : Sig
  sv : Fin (net.ar j) → Sig
  F : Nat → Nat
  G : (p : Fin (net.ar j)) → Fin (net.nc j p) → Nat → Nat
  Q : Nat → Nat
  wF : Warp (b.loF j) (b.hiF j) F
  wG : ∀ p i, Warp (b.loC j p i) (b.hiC j p i) (G p i)
  wQ : Warp (b.loQ j) (b.hiQ j) Q
  loF1 : 1 ≤ b.loF j
  loC1 : ∀ p i, 1 ≤ b.loC j p i
  loQ1 : 1 ≤ b.loQ j
  hc : ∀ t, cc j t =
    if net.mg j then fany (net.ar j) (fun p => pin p (F t))
    else if r (F t) then net.v j else cel (fun p => pin p (F t) ^^ net.neg j p) (q (F t))
  hpin : ∀ p t, pin p t = (net.inv j p ^^
    match net.pk j p with
    | PK.multi => if net.op j p then fall (net.nc j p) (fun i => cc (net.src j p) (G p i t))
                  else fany (net.nc j p) (fun i => cc (net.src j p) (G p i t))
    | PK.guard => if net.op j p then fall (net.nc j p) (fun i => cc (net.src j p) (G p i t))
                  else fany (net.nc j p) (fun i => cc (net.src j p) (G p i t))
    | PK.filt => fany (net.nc j p) (fun i => cc (net.src j p) (G p i t) && (sv p t == net.br j p))
    | PK.plain => fany (net.nc j p) (fun i => cc (net.src j p) (G p i t)))
  hq : ∀ t, q t = cc j (Q t)
  r0 : r 0 = true
  ranti : ∀ a c, a ≤ c → r c = true → r a = true
  hskew : ∀ p (i i' : Fin (net.nc j p)), i'.val = i.val + 1 → ∀ s,
    G p i s ≤ G p i' s + b.dw j p i.val ∧ G p i' s ≤ G p i s + b.dw j p i.val

/-- A `Beh7` from node behaviours. -/
noncomputable def ofND7 {N : Nat} {net : Net4 N} {b : Bands4 net} (sel : Nat → Nat → Bool) (cc : Fin N → Sig)
    (nd : ∀ j, ND7 net b cc j) (gc : (j : Fin N) → Fin (net.ar j) → Nat → Nat)
    (gcmono : ∀ j p a s, a ≤ s → gc j p a ≤ gc j p s)
    (mg0 : ∀ j, net.mg j = true → cc j 0 = false) : Beh7 net b sel where
  c := cc
  pin := fun j => (nd j).pin
  q := fun j => (nd j).q
  r := fun j => (nd j).r
  sv := fun j => (nd j).sv
  gc := gc
  F := fun j => (nd j).F
  G := fun j => (nd j).G
  Q := fun j => (nd j).Q
  wF := fun j => (nd j).wF
  wG := fun j => (nd j).wG
  wQ := fun j => (nd j).wQ
  loF1 := fun j => (nd j).loF1
  loC1 := fun j => (nd j).loC1
  loQ1 := fun j => (nd j).loQ1
  hc := fun j => (nd j).hc
  hpin := fun j => (nd j).hpin
  hq := fun j => (nd j).hq
  r0 := fun j => (nd j).r0
  ranti := fun j => (nd j).ranti
  hskew := fun j => (nd j).hskew
  mg0 := mg0
  gcmono := gcmono

/-- **H_ARB** for `Beh7` (hypothesis, as `Events6.HARB`): the virtual nodes behave
as the virtual mux core in their bands; the grant and `R0` wires carry the
virtual signals; `R0` is low at time 0. -/
def HARB7 {N : Nat} {d : Design} (net : Net4 N) (b : Bands4 net) (rn : Fin N → RNode) (x : Fin d.n → Sig)
    (cv : Fin N → Sig) : Prop :=
  (∀ j, (rn j).virt = true → Nonempty (ND7 net b (ccOf rn x cv) j)) ∧
  (∀ j, (rn j).virt = true → (rn j).hasW = true → ∀ t, x (d.wire (rn j).ow) t = cv j t) ∧
  (∀ j, (rn j).virt = true → net.mg j = true → cv j 0 = false)

/-! ## The node behaviour of a real node -/

section
variable {N : Nat} {d : Design} {net : Net4 N} {b : Bands4 net} {rn : Fin N → RNode} {rank : Fin N → Nat}
  {rw fuel : Nat} {x : Fin d.n → Sig} (hsat : SatPin d plG x)
  (h0 : ∀ t, x (d.wire 0) t = false) (h1 : ∀ t, x (d.wire 1) t = true)
  {T : Nat} (hT : 1 ≤ T) (hrst : ∀ t, x (d.wire rw) t = decide (t < T))
  {cv : Fin N → Sig}
  (hwf : d.WF) (hOK : net.OK7)
  (hW : ∀ s, (rn s).virt = true → (rn s).hasW = true → ∀ t, x (d.wire (rn s).ow) t = cv s t)
  (j : Fin N) (hv : (rn j).virt = false) (hn : NodeR d net b rn rank rw fuel j)

include h0 h1 hrst hwf hOK hW hv hn in
/-- **The node behaviour of a recognised real node** (as `Events6.ndReal`; a guarded pin with
many copies reads their AND / OR, as a delay line). -/
noncomputable def ndReal7 : ND7 net b (ccOf rn x cv) j where
  pin := fun p s => vals hsat (rn j).lut (rpin net rn j p).ip (s + 1) &&
    foldM (fun i => vals hsat (rn j).lut i (s + 1)) (rpin net rn j p).fold
  q := fun s => if net.mg j then ccOf rn x cv j (s - 1) else vals hsat (rn j).lut (rn j).qi (s + 1)
  r := fun s => if net.mg j then true else vals hsat (rn j).lut (rn j).ri (s + 1)
  sv := fun p s => svOf (rn := rn) hsat j p s
  F := fun t => t - 1
  G := fun p i s => tau hsat (full net rn j p i.val) (s + 1)
  Q := fun s => if net.mg j then s - 1 else tau hsat (((rn j).lut, (rn j).qi) :: (rn j).qp) (s + 1)
  wF := by
    rw [hn.2.2.1, hn.2.2.2.1]
    exact ⟨fun a c h => by omega, fun t => by omega, fun t => by omega⟩
  wG := by
    intro p i
    obtain ⟨hok, h2⟩ := full_ok hwf j hn p i
    rw [((hn.2.2.2.2.2.2 p).2.2.2.2.1 i).1, ((hn.2.2.2.2.2.2 p).2.2.2.2.1 i).2]
    exact shift1 (tau_warp hsat _ hok) (by omega)
  wQ := by
    by_cases hm : net.mg j = true
    · obtain ⟨_, hlo, hhi, _⟩ := hn.2.2.2.2.2.1 hm
      simp only [hm, ite_true]; rw [hlo, hhi]
      exact ⟨fun a c h => by omega, fun t => by omega, fun t => by omega⟩
    · have hm' : net.mg j = false := by simpa using hm
      obtain ⟨_, hqi, _, _, hqok, hqne, _, _, hlo, hhi⟩ := hn.2.2.2.2.1 hm'
      simp only [hm', Bool.false_eq_true, ite_false]; rw [hlo, hhi]
      have hok : pathOK d (((rn j).lut, (rn j).qi) :: (rn j).qp) = true := by
        simp only [pathOK, List.all_cons, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨hn.1, hqi⟩, hqok⟩
      have := plo_pos hwf _ hqok hqne
      have hl := (hwf _ (gt_mem d hn.1)).2.2.2.1
      exact shift1 (tau_warp hsat _ hok) (by simp only [plo]; omega)
  loF1 := by rw [hn.2.2.1]; exact Nat.le_refl 1
  loC1 := by
    intro p i
    have := (full_ok hwf j hn p i).2
    rw [((hn.2.2.2.2.2.2 p).2.2.2.2.1 i).1]; omega
  loQ1 := by
    by_cases hm : net.mg j = true
    · rw [(hn.2.2.2.2.2.1 hm).2.1]; exact Nat.le_refl 1
    · have hm' : net.mg j = false := by simpa using hm
      obtain ⟨_, _, _, _, hqok, hqne, _, _, hlo, _⟩ := hn.2.2.2.2.1 hm'
      rw [hlo]
      have := plo_pos hwf _ hqok hqne
      have hl := (hwf _ (gt_mem d hn.1)).2.2.2.1
      simp only [plo]; omega
  hc := by
    intro t
    have hout : ccOf rn x cv j t = x (d.wire (gt d (rn j).lut).out) t := by
      unfold ccOf; rw [hv, hn.2.1]; rfl
    rw [hout]
    by_cases hm : net.mg j = true
    · obtain ⟨hs, _, _, _⟩ := hn.2.2.2.2.2.1 hm
      rw [gate_spec hsat h0 h1 hn.1 hs t]
      simp only [hm, ite_true, mergeSpec]
      congr 1; funext p
      obtain ⟨hip, _, _, _, _, _, hst, hnst⟩ := hn.2.2.2.2.2.2 p
      have hf : (rpin net rn j p).fold = [] := by
        cases hs' : (rpin net rn j p).st
        · by_cases hne : (rpin net rn j p).fold = []
          · exact hne
          · have := ((hnst hs').2.2.1 hne).2.2.2; rw [hm] at this; exact absurd this (by decide)
        · exact (hst hs').2.1
      rw [if_pos hip, hf]
      simp only [foldM, List.all_nil, Bool.and_true]
      exact vals_pred hsat hwf j hn _ hip t
    · have hm' : net.mg j = false := by simpa using hm
      obtain ⟨hs, hqi, hri, _⟩ := hn.2.2.2.2.1 hm'
      rw [gate_spec hsat h0 h1 hn.1 hs t]
      simp only [hm', Bool.false_eq_true, ite_false, stageSpec]
      rw [if_pos hri, if_pos hqi, ← vals_pred hsat hwf j hn _ hri t, ← vals_pred hsat hwf j hn _ hqi t]
      have hfun : (fun p : Fin (net.ar j) => ((if (rpin net rn j p).ip < (gt d (rn j).lut).k then
            x (d.wire ((gt d (rn j).lut).ins.getD (rpin net rn j p).ip 0)) (wf hsat (rn j).lut (rpin net rn j p).ip t)
            else false) ^^ net.neg j p) &&
          foldM (fun i => if i < (gt d (rn j).lut).k then
            x (d.wire ((gt d (rn j).lut).ins.getD i 0)) (wf hsat (rn j).lut i t) else false) (rpin net rn j p).fold)
        = (fun p => (vals hsat (rn j).lut (rpin net rn j p).ip (t - 1 + 1) &&
            foldM (fun i => vals hsat (rn j).lut i (t - 1 + 1)) (rpin net rn j p).fold) ^^ net.neg j p) := by
        funext p
        obtain ⟨hip, _, _, _, _, _, hst, hnst⟩ := hn.2.2.2.2.2.2 p
        rw [if_pos hip, ← vals_pred hsat hwf j hn _ hip t]
        have hlt : ∀ sb ∈ (rpin net rn j p).fold, sb.1 < (gt d (rn j).lut).k := by
          cases hs' : (rpin net rn j p).st
          · exact (hnst hs').2.1
          · rw [(hst hs').2.1]; intro sb hsb; simp at hsb
        have hfm : foldM (fun i => if i < (gt d (rn j).lut).k then
              x (d.wire ((gt d (rn j).lut).ins.getD i 0)) (wf hsat (rn j).lut i t) else false) (rpin net rn j p).fold =
            foldM (fun i => vals hsat (rn j).lut i (t - 1 + 1)) (rpin net rn j p).fold := by
          unfold foldM
          apply Bool.eq_iff_iff.mpr; rw [List.all_eq_true, List.all_eq_true]
          constructor
          · intro H sb hsb; have := H sb hsb; simp only [if_pos (hlt sb hsb)] at this ⊢
            rw [← vals_pred hsat hwf j hn _ (hlt sb hsb) t]; exact this
          · intro H sb hsb; have := H sb hsb; simp only [if_pos (hlt sb hsb)] at this ⊢
            rw [← vals_pred hsat hwf j hn _ (hlt sb hsb) t] at this; exact this
        rw [hfm]
        unfold vals
        by_cases hf : (rpin net rn j p).fold = []
        · rw [hf]; simp [foldM]
        · have hneg : net.neg j p = false := by
            cases hs' : (rpin net rn j p).st
            · exact ((hnst hs').2.2.1 hf).2.1
            · exact absurd (hst hs').2.1 hf
          rw [hneg]; simp
      rw [hfun]; rfl
  hpin := by
    intro p t
    obtain ⟨hip, hsw, hlen, hpaths, _, _, hst, hnst⟩ := hn.2.2.2.2.2.2 p
    obtain ⟨hnc1, _, hinv, _, _⟩ := hOK j p
    have hsrc := src_wire hW (net.src j p) hsw
    -- the LUT pin wire at the pin's own time
    have hpw : vals hsat (rn j).lut (rpin net rn j p).ip (t + 1) =
        x (d.wire (pinW d net rn j p)) (wf hsat (rn j).lut (rpin net rn j p).ip (t + 1)) := rfl
    generalize hu : wf hsat (rn j).lut (rpin net rn j p).ip (t + 1) = u at hpw
    have hG : ∀ i : Fin (net.nc j p), tau hsat (full net rn j p i.val) (t + 1) =
        tau hsat ((rpin net rn j p).copies.getD i.val []) u := by
      intro i; rw [← hu]; rfl
    simp only [hG]
    cases hs : (rpin net rn j p).st
    · -- tree kind
      obtain ⟨hchk, _, hfo, hfe⟩ := hnst hs
      have hc : (rpin net rn j p).copies = (rpin net rn j p).paths := by simp [RPin.copies, hs]
      have ev := chkT_sound hsat h0 h1 _ fuel _ _ _ _ hchk u
      simp only [hsrc] at ev
      rw [hpw, ev, hc]
      by_cases hf : (rpin net rn j p).fold = []
      · have hk := hfe hf
        rw [hf]; simp only [foldM, List.all_nil, Bool.and_true]
        cases hpk : net.pk j p with
        | filt => exact absurd hpk hk
        | multi =>
          simp only
          rw [hc] at hlen
          rw [fall_list (fun π => ccOf rn x cv (net.src j p) (tau hsat π u)) [] _ _ hlen,
            fany_list (fun π => ccOf rn x cv (net.src j p) (tau hsat π u)) [] _ _ hlen]
          unfold specL; cases net.op j p <;> rfl
        | plain =>
          simp only
          have h1' := hnc1 (by rw [hpk]; decide)
          rw [hc] at hlen
          rw [fany_list (fun π => ccOf rn x cv (net.src j p) (tau hsat π u)) [] _ _ hlen]
          unfold specL; split
          · rw [all_eq_any_one _ _ (by rw [hlen, h1'])]
          · rfl
        | guard =>
          simp only
          rw [hc] at hlen
          rw [fall_list (fun π => ccOf rn x cv (net.src j p) (tau hsat π u)) [] _ _ hlen,
            fany_list (fun π => ccOf rn x cv (net.src j p) (tau hsat π u)) [] _ _ hlen]
          unfold specL; cases net.op j p <;> rfl
      · obtain ⟨hpk, _, hbr, _⟩ := hfo hf
        have hi := hinv hpk
        have h1' := hnc1 (by rw [hpk]; decide)
        rw [hpk, hi]
        simp only [Bool.false_xor]
        rw [hc] at hlen
        have hfl := fany_list (fun π => ccOf rn x cv (net.src j p) (tau hsat π u) && (svOf (rn := rn) hsat j p t == net.br j p))
          [] _ _ hlen
        try simp only at hfl ⊢
        rw [hfl]
        have hl1 : (rpin net rn j p).paths.length = 1 := by rw [hlen, h1']
        have hsv : (svOf (rn := rn) hsat j p t == net.br j p) = foldM (fun i => vals hsat (rn j).lut i (t + 1)) (rpin net rn j p).fold := by
          unfold svOf; rw [hs, hbr]; simp only [Bool.false_eq_true, ite_false]
          exact sv_br _ _
        match hpp : (rpin net rn j p).paths, hl1 with
        | [π], _ => simp [specL, hsv]
    · -- steer kind
      obtain ⟨hpk, hfold, hsg, hsci, hssel, hspec, hct, hcb, hbr⟩ := hst hs
      have hi := hinv hpk
      have h1' := hnc1 (by rw [hpk]; decide)
      have hc : (rpin net rn j p).copies = [(rpin net rn j p).top ++ ((rpin net rn j p).sg, (rpin net rn j p).sci) :: (rpin net rn j p).bot] := by
        simp [RPin.copies, hs]
      rw [hpk, hi, hpw, hfold]
      simp only [foldM, List.all_nil, Bool.and_true, Bool.false_xor]
      have ev1 := chkT_sound hsat h0 h1 _ fuel _ _ _ _ hct u
      simp only [Bool.false_xor, specL, ite_true, List.all_cons, List.all_nil, Bool.and_true] at ev1
      rw [ev1]
      generalize hu' : tau hsat (rpin net rn j p).top u = u'
      rw [gate_spec hsat h0 h1 hsg hspec u']
      simp only [steerSpec]
      rw [if_pos hsci]
      have ev2 := chkT_sound hsat h0 h1 _ fuel _ _ _ _ hcb (wf hsat (rpin net rn j p).sg (rpin net rn j p).sci u')
      simp only [Bool.false_xor, specL, ite_true, List.all_cons, List.all_nil, Bool.and_true] at ev2
      rw [ev2, hsrc]
      have hfl := fany_list (fun π => ccOf rn x cv (net.src j p) (tau hsat π u) && (svOf (rn := rn) hsat j p t == net.br j p))
        [] _ _ hlen
      try simp only at hfl ⊢
      rw [hfl, hc]
      simp only [List.any_cons, List.any_nil, Bool.or_false]
      rw [tau_append]
      simp only [tau]
      rw [hu']
      congr 1
      unfold svOf; rw [hs, hbr]; simp only [ite_true]
      rw [hu, hu']
      have hsb := sv_br (fun i => vals hsat (rpin net rn j p).sg i u') (rpin net rn j p).ssel
      try simp only at hsb
      rw [hsb]
      unfold foldM vals
      apply Bool.eq_iff_iff.mpr; rw [List.all_eq_true, List.all_eq_true]
      constructor
      · intro H sb hsb; have := H sb hsb; simp only [if_pos (hssel sb hsb)] at this ⊢; exact this
      · intro H sb hsb; have := H sb hsb; simp only [if_pos (hssel sb hsb)] at this ⊢; exact this
  hq := by
    intro t
    by_cases hm : net.mg j = true
    · simp only [hm, ite_true]
    · have hm' : net.mg j = false := by simpa using hm
      obtain ⟨_, _, _, hcq, _, _, _, _, _, _⟩ := hn.2.2.2.2.1 hm'
      simp only [hm', Bool.false_eq_true, ite_false]
      have ev := chkT_sound hsat h0 h1 _ fuel _ _ _ _ hcq (wf hsat (rn j).lut (rn j).qi (t + 1))
      simp only [Bool.false_xor, specL, ite_true, List.all_cons, List.all_nil, Bool.and_true] at ev
      unfold vals; rw [ev]
      unfold ccOf; rw [hv, hn.2.1]; rfl
  r0 := by
    by_cases hm : net.mg j = true
    · simp only [hm, ite_true]
    · have hm' : net.mg j = false := by simpa using hm
      obtain ⟨_, _, hri, _, _, _, hcr, hrok, _, _⟩ := hn.2.2.2.2.1 hm'
      simp only [hm', Bool.false_eq_true, ite_false]
      have ev := chkT_sound hsat h0 h1 _ fuel _ _ _ _ hcr (wf hsat (rn j).lut (rn j).ri (0 + 1))
      simp only [Bool.false_xor, specL, ite_true, List.all_cons, List.all_nil, Bool.and_true] at ev
      unfold vals; rw [ev, hrst]
      have w := lut_warp hsat hwf j hn _ hri
      have e0 : wf hsat (rn j).lut (rn j).ri (0 + 1) = 0 := by have := w.1.le_late (0 + 1); omega
      rw [e0, tau_zero hsat _ hrok]; simp only [decide_eq_true_eq]; omega
  ranti := by
    intro a c hac hrc
    by_cases hm : net.mg j = true
    · simp only [hm, ite_true]
    · have hm' : net.mg j = false := by simpa using hm
      obtain ⟨_, _, hri, _, _, _, hcr, hrok, _, _⟩ := hn.2.2.2.2.1 hm'
      simp only [hm', Bool.false_eq_true, ite_false] at hrc ⊢
      have eva := chkT_sound hsat h0 h1 _ fuel _ _ _ _ hcr (wf hsat (rn j).lut (rn j).ri (a + 1))
      have evc := chkT_sound hsat h0 h1 _ fuel _ _ _ _ hcr (wf hsat (rn j).lut (rn j).ri (c + 1))
      simp only [Bool.false_xor, specL, ite_true, List.all_cons, List.all_nil, Bool.and_true] at eva evc
      unfold vals at hrc ⊢; rw [eva, hrst]; rw [evc, hrst] at hrc
      have w := lut_warp hsat hwf j hn _ hri
      have m1 := w.1.mono (a + 1) (c + 1) (by omega)
      have m2 := (tau_warp hsat _ hrok).mono _ _ m1
      simp only [decide_eq_true_eq] at hrc ⊢; omega
  hskew := by
    intro p i i' hii s
    obtain ⟨_, _, _, _, _, hdw, _, _⟩ := hn.2.2.2.2.2.2 p
    have hlt : i.val + 1 < net.nc j p := by rw [← hii]; exact i'.isLt
    rw [hdw i hlt]
    have := pairW_sound hsat hwf _ _ (full_ok hwf j hn p i).1 (full_ok hwf j hn p i').1 (s + 1)
    rw [hii] at this ⊢
    exact this

end

/-! ## Time 0 -/

section
variable {N : Nat} {net : Net4 N} {b : Bands4 net} {cc : Fin N → Sig}

theorem nd7_stage0 {j : Fin N} (nd : ND7 net b cc j) (hm : net.mg j = false) : cc j 0 = net.v j := by
  rw [nd.hc 0]
  have : nd.F 0 = 0 := warp_zero nd.wF
  simp only [hm, Bool.false_eq_true, ite_false, this, nd.r0, ite_true]

theorem nd7_merge0 (hOK : net.OK7) {j : Fin N} (nd : ND7 net b cc j) (hm : net.mg j = true)
    (hs : ∀ p, cc (net.src j p) 0 = net.v (net.src j p)) : cc j 0 = false := by
  rw [nd.hc 0]
  have hF : nd.F 0 = 0 := warp_zero nd.wF
  simp only [hm, ite_true, hF]
  apply fany_all_false
  intro p
  obtain ⟨hnc, hvs, hinv, hmg, _⟩ := hOK j p
  obtain ⟨hvj, hng, hkg, hoff⟩ := hmg hm
  have hG : ∀ i, nd.G p i 0 = 0 := fun i => warp_zero (nd.wG p i)
  rw [nd.hpin p 0]
  simp only [hG, hs]
  unfold Net4.off Formal.Core.XAudit.Events.offB at hoff
  rw [hvj, hng] at hoff
  cases hpk : net.pk j p with
  | guard => exact absurd hpk hkg
  | multi =>
    have hv0 := hvs (Or.inl hpk)
    simp only [hv0]
    rw [fall_false _ (net.nc_pos j p), fany_false']
    split <;> (simp at hoff; cases h : net.inv j p <;> simp_all)
  | filt =>
    have hv0 := hvs (Or.inr hpk)
    simp only [hv0, Bool.false_and, hinv hpk, fany_false', Bool.false_xor]
  | plain =>
    have h1 := hnc (by rw [hpk]; decide)
    simp only
    have : fany (net.nc j p) (fun _ => net.v (net.src j p)) = net.v (net.src j p) := by
      rw [Beh4.fany_one h1]
    rw [this]
    cases h : net.inv j p <;> cases h' : net.v (net.src j p) <;> simp_all

end

/-! ## `design_beh7` -/

section
variable {N : Nat} {d : Design} {net : Net4 N} {b : Bands4 net} {rn : Fin N → RNode} {rank : Fin N → Nat}
  {rw fuel : Nat} {x : Fin d.n → Sig} (hsat : SatPin d plG x)
  (h0 : ∀ t, x (d.wire 0) t = false) (h1 : ∀ t, x (d.wire 1) t = true)
  {T : Nat} (hT : 1 ≤ T) (hrst : ∀ t, x (d.wire rw) t = decide (t < T))
  {cv : Fin N → Sig} (hr : Recog6 d net b rn rank rw fuel) (hOK : net.OK7) (harb : HARB7 net b rn x cv)

include hsat h0 h1 hT hrst hr hOK harb

/-- The node behaviours: real nodes from the netlist, virtual ones from H_ARB. -/
noncomputable def ndAll7 (j : Fin N) : ND7 net b (ccOf rn x cv) j :=
  if h : (rn j).virt = true then Classical.choice (harb.1 j h)
  else ndReal7 hsat h0 h1 hT hrst hr.1 hOK harb.2.1 j (by simpa using h) (hr.2 j (by simpa using h))

theorem init0_7 : ∀ j, ccOf rn x cv j 0 = net.v j := by
  have key : ∀ n, ∀ j, rank j ≤ n → ccOf rn x cv j 0 = net.v j := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro j hj
      by_cases hm : net.mg j = true
      · have hv0 := ((hOK j ⟨0, net.ar_pos j⟩).2.2.2.1 hm).1
        rw [hv0]
        by_cases hvt : (rn j).virt = true
        · unfold ccOf; rw [if_pos hvt]; exact harb.2.2 j hvt hm
        · have hvf : (rn j).virt = false := by simpa using hvt
          have hn := hr.2 j hvf
          apply nd7_merge0 hOK (ndAll7 hsat h0 h1 hT hrst hr hOK harb j) hm
          intro p
          by_cases hs : (rn (net.src j p)).virt = false ∧ net.mg (net.src j p) = true
          · have := (hn.2.2.2.2.2.1 hm).2.2.2 p hs.1 hs.2
            exact ih (rank (net.src j p)) (by omega) _ (Nat.le_refl _)
          · by_cases hms : net.mg (net.src j p) = true
            · have hvs : (rn (net.src j p)).virt = true := by
                cases h : (rn (net.src j p)).virt
                · exact absurd ⟨h, hms⟩ hs
                · rfl
              have hv1 := ((hOK (net.src j p) ⟨0, net.ar_pos _⟩).2.2.2.1 hms).1
              rw [hv1]; unfold ccOf; rw [if_pos hvs]; exact harb.2.2 _ hvs hms
            · exact nd7_stage0 (ndAll7 hsat h0 h1 hT hrst hr hOK harb _) (by simpa using hms)
      · exact nd7_stage0 (ndAll7 hsat h0 h1 hT hrst hr hOK harb j) (by simpa using hm)
  exact fun j => key (rank j) j (Nat.le_refl _)

/-- **`design_beh7`.** Every per-pin behaviour of a recognised netlist with
`Net4.OK7` (constant wires, reset high until `T`, H_ARB) is a `Beh7` of the
recognised `Net4` in its bands, for every select sequence `sel` and every
monotone guarded count `gc`: its node `j` is the wire of `j`'s LUT when `j` is real. -/
theorem design_beh7 (sel : Nat → Nat → Bool) (gc : (j : Fin N) → Fin (net.ar j) → Nat → Nat)
    (gcmono : ∀ j p a s, a ≤ s → gc j p a ≤ gc j p s) :
    ∃ bh : Beh7 net b sel, (∀ j t, bh.c j t = ccOf rn x cv j t) ∧ bh.gc = gc ∧
      (∀ j, (rn j).virt = false → ∀ t, bh.c j t = x (d.wire (gt d (rn j).lut).out) t) := by
  refine ⟨ofND7 sel (ccOf rn x cv) (ndAll7 hsat h0 h1 hT hrst hr hOK harb) gc gcmono
    (fun j hm => by rw [init0_7 hsat h0 h1 hT hrst hr hOK harb j]; exact ((hOK j ⟨0, net.ar_pos j⟩).2.2.2.1 hm).1),
    fun j t => rfl, rfl, fun j hv t => ?_⟩
  show ccOf rn x cv j t = _
  unfold ccOf; rw [hv, (hr.2 j hv).2.1]; rfl

end

/-! ## The netlist-level verdict -/

section
variable {N : Nat} {d : Design} {net : Net4 N} {b : Bands4 net} {rn : Fin N → RNode} {rank : Fin N → Nat}
  {rw fuel : Nat} {x : Fin d.n → Sig} {cv : Fin N → Sig}

/-- **`design_verdict7`** (what a run of `xevents7` means). The executable checks
`Recog6`, `Net4.OK7`, that the derivation log is accepted (`runLog … = some J`)
and, per item, `backOK7` / `exclOK7` / `lineOK7` against `J`; `cp`, `cxm`, `cl`
record which items it certified. Then for every per-pin behaviour `x` of the
parsed netlist (constant wires, reset high until `T`, H_ARB), every select
sequence `sel` and every monotone guarded count `gc`, there is a `Beh7` realising
`x` such that — if `sel` satisfies SelPart for the certificate's partitions and
the realisation satisfies SelOK, GuardOK and the residual obligations of the
items the checker did NOT certify — every real LUT wire is its reset value
flipped `M t j` times at every time. With no residual item (CLEAN) the last
hypotheses are vacuous. -/
theorem design_verdict7 (hr : Recog6 d net b rn rank rw fuel) (hOK : net.OK7)
    {parts : List (List Nat)} {log : List Ln} {J : Array Jd} (hJ : runLog net b parts log = some J)
    (back line : (j : Fin N) → Fin (net.ar j) → Nat) (xS xw : Fin N → Nat) (xa : Fin N → List Arm)
    (cp : (j : Fin N) → Fin (net.ar j) → Bool) (cxm : Fin N → Bool) (cl : (j : Fin N) → Fin (net.ar j) → Bool)
    (hcp : ∀ j p, cp j p = true → backOK7 net b J j p (back j p) = true)
    (hcx : ∀ m, cxm m = true → exclOK7 net b parts J m (xS m) (xa m) (xw m) = true)
    (hcl : ∀ j p, cl j p = true → lineOK7 net b J j p (line j p) = true)
    (hsat : SatPin d plG x) (h0 : ∀ t, x (d.wire 0) t = false) (h1 : ∀ t, x (d.wire 1) t = true)
    {T : Nat} (hT : 1 ≤ T) (hrst : ∀ t, x (d.wire rw) t = decide (t < T)) (harb : HARB7 net b rn x cv)
    (sel : Nat → Nat → Bool) (gc : (j : Fin N) → Fin (net.ar j) → Nat → Nat)
    (gcmono : ∀ j p a s, a ≤ s → gc j p a ≤ gc j p s) :
    ∃ bh : Beh7 net b sel, (∀ j t, bh.c j t = ccOf rn x cv j t) ∧ bh.gc = gc ∧
      (SelPart sel parts → bh.SelOK → bh.GuardOK →
        (∀ j p s, net.mg j = false → net.pk j p ≠ PK.guard → cp j p = false → bh.P j p s ≤ bh.M (bh.Q j s) j + 1) →
        (∀ m s, net.mg m = true → cxm m = false → fodd (net.ar m) (fun p => bh.P m p s) ≤ 1) →
        (∀ j p s, net.pk j p = PK.multi → cl j p = false → ContigF (net.nc j p) (bh.cm j p s)) →
        ∀ t j, (rn j).virt = false →
          x (d.wire (gt d (rn j).lut).out) t = ph (net.v j) (bh.M t j)) := by
  obtain ⟨bh, hc, hgc, hreal⟩ := design_beh7 hsat h0 h1 hT hrst hr hOK harb sel gc gcmono
  refine ⟨bh, hc, hgc, fun hp hsel hguard rB rX rL t j hv => ?_⟩
  rw [← hreal j hv t]
  exact verdict7 bh hOK hp hJ back line xS xw xa cp cxm cl hcp hcx hcl rB rX rL hsel hguard t j

end

end Formal.Core.XAudit.Events7
