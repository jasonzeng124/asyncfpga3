import Formal.Core.XAudit.Events6Design

/-!
# Formal.Core.XAudit.Events6Beh — `design_beh4` (W-E4n) and the netlist-level verdict

Probe A-events6. See `formal/notes/A-events6.md` and `Events6Design`.

* `ndReal`: the node behaviour (`ND`) of a recognised REAL node, built from the
  per-pin warps of the parsed gates (`SatPin d plG x`).
* `init0`: every node reads its reset value at time 0 (stages: reset high; merges:
  by induction on the merge rank the recogniser checks; virtual nodes: H_ARB).
* **`design_beh4`**: every per-pin behaviour of a recognised design, under H_ARB,
  is a `Beh4` whose nodes are the LUT wires (real) and the H_ARB signals (virtual).
* **`design_verdict`**: with the checked certificates (`verdictR`'s hypotheses),
  every per-pin behaviour of the parsed netlist has, at every time, every real
  node's wire equal to its reset value flipped `M t j` times, for the `M` of a
  `Beh4` realising it — provided that realisation satisfies the bundling
  hypothesis SelOK, GuardOK and the residual obligations.
-/

namespace Formal.Core.XAudit.Events6

open Formal.Core
open Formal.Core.XAudit
open Formal.Core.TraceDiscrete (Sig Warp)
open Formal.Core.XAudit.Events (ph)
open Formal.Core.XAudit.Events2 (cel)
open Formal.Core.XAudit.Events2Pin (SatPin)
open Formal.Core.XAudit.Events5

theorem shift1 {lo hi : Nat} {f : Nat → Nat} (w : Warp lo hi f) (h : 1 ≤ lo) :
    Warp (lo - 1) (hi - 1) (fun s => f (s + 1)) := by
  have e1 := w.early_le 1; have l1 := w.le_late 1
  refine ⟨fun a c hac => w.mono _ _ (by omega), fun s => ?_, fun s => ?_⟩
  · have := w.le_late (s + 1); omega
  · have := w.early_le (s + 1); omega

theorem fall_list {α : Type} (f : α → Bool) (dflt : α) : ∀ (l : List α) (n : Nat) (h : l.length = n),
    fall n (fun i : Fin n => f (l.getD i.val dflt)) = l.all f
  | [], n, h => by subst h; rfl
  | a :: l, n, h => by
      subst h
      simp only [fall, List.all_cons, List.length_cons]
      congr 1
      exact fall_list f dflt l l.length rfl

theorem fany_list {α : Type} (f : α → Bool) (dflt : α) : ∀ (l : List α) (n : Nat) (h : l.length = n),
    fany n (fun i : Fin n => f (l.getD i.val dflt)) = l.any f
  | [], n, h => by subst h; rfl
  | a :: l, n, h => by
      subst h
      simp only [fany, List.any_cons, List.length_cons]
      congr 1
      exact fany_list f dflt l l.length rfl

theorem all_eq_any_one {α : Type} (f : α → Bool) (l : List α) (h : l.length = 1) : l.all f = l.any f := by
  match l, h with
  | [a], _ => simp

theorem sv_br (v : Nat → Bool) (l : List (Nat × Bool)) :
    ((if l.length = 1 then v (l.headD (0, false)).1 else foldM v l) == brOf l) = foldM v l := by
  match l with
  | [] => simp [foldM, brOf]
  | [(i, b0)] => simp [foldM, brOf]
  | a :: c :: rest => simp [foldM, brOf]

theorem plo_pos {d : Design} (hwf : d.WF) (p : Path) (hp : pathOK d p = true) (hne : p ≠ []) : 1 ≤ plo d p := by
  match p, hp, hne with
  | (gi, i) :: r, hp, _ =>
    simp only [pathOK, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hp
    have := (hwf _ (gt_mem d hp.1.1)).2.2.2.1
    simp only [plo]; omega

section
variable {N : Nat} {d : Design} {net : Net4 N} {b : Bands4 net} {rn : Fin N → RNode} {rank : Fin N → Nat}
  {rw fuel : Nat} {x : Fin d.n → Sig} (hsat : SatPinW d plG x) {cv : Fin N → Sig}

/-- Input `i` of gate `L`, read at the gate's time `u`. -/
noncomputable def vals (L i u : Nat) : Bool := x (d.wire ((gt d L).ins.getD i 0)) (wf hsat L i u)

/-- The select a filtered pin sees. -/
noncomputable def svOf (j : Fin N) (p : Fin (net.ar j)) (s : Nat) : Bool :=
  if (rpin net rn j p).st then
    if (rpin net rn j p).ssel.length = 1 then
      vals hsat (rpin net rn j p).sg ((rpin net rn j p).ssel.headD (0, false)).1
        (tau hsat (rpin net rn j p).top (wf hsat (rn j).lut (rpin net rn j p).ip (s + 1)))
    else foldM (fun i => vals hsat (rpin net rn j p).sg i
        (tau hsat (rpin net rn j p).top (wf hsat (rn j).lut (rpin net rn j p).ip (s + 1)))) (rpin net rn j p).ssel
  else
    if (rpin net rn j p).fold.length = 1 then vals hsat (rn j).lut ((rpin net rn j p).fold.headD (0, false)).1 (s + 1)
    else foldM (fun i => vals hsat (rn j).lut i (s + 1)) (rpin net rn j p).fold

end

/-! ## The node behaviour of a real node -/

section
variable {N : Nat} {d : Design} {net : Net4 N} {b : Bands4 net} {rn : Fin N → RNode} {rank : Fin N → Nat}
  {rw fuel : Nat} {x : Fin d.n → Sig} (hsat : SatPinW d plG x)
  (h0 : ∀ t, x (d.wire 0) t = false) (h1 : ∀ t, x (d.wire 1) t = true)
  {T : Nat} (hT : 1 ≤ T) (hrst : ∀ t, x (d.wire rw) t = decide (t < T))
  {cv : Fin N → Sig}
  (hwf : d.WF) (hOK : net.OK)
  (hW : ∀ s, (rn s).virt = true → (rn s).hasW = true → ∀ t, x (d.wire (rn s).ow) t = cv s t)
  (j : Fin N) (hv : (rn j).virt = false) (hn : NodeR d net b rn rank rw fuel j)

include hwf hn in
theorem lut_warp (i : Nat) (hi : i < (gt d (rn j).lut).k) :
    Warp (gt d (rn j).lut).lo (gt d (rn j).lut).hi (wf hsat (rn j).lut i) ∧ 1 ≤ (gt d (rn j).lut).lo :=
  ⟨wf_warp hsat hn.1 hi, (hwf _ (gt_mem d hn.1)).2.2.2.1⟩

include hwf hn in
theorem vals_pred (i : Nat) (hi : i < (gt d (rn j).lut).k) (t : Nat) :
    vals hsat (rn j).lut i t = vals hsat (rn j).lut i (t - 1 + 1) := by
  have w := lut_warp hsat hwf j hn i hi
  unfold vals; rw [← warp_pred w.1 w.2 t]

include hW in
theorem src_wire (s : Fin N) (hs : (rn s).virt = true → (rn s).hasW = true) (t : Nat) :
    x (d.wire (rn s).ow) t = ccOf rn x cv s t := by
  unfold ccOf
  cases h : (rn s).virt
  · rfl
  · simp only [ite_true]; exact hW s h (hs h) t

include hwf hn in
theorem full_ok (p : Fin (net.ar j)) (i : Fin (net.nc j p)) :
    pathOK d (full net rn j p i.val) = true ∧ 2 ≤ plo d (full net rn j p i.val) := by
  obtain ⟨hip, _, hlen, hpaths, _⟩ := hn.2.2.2.2.2.2 p
  have hmem : (rpin net rn j p).copies.getD i.val [] ∈ (rpin net rn j p).copies := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
  obtain ⟨hok, hne⟩ := hpaths _ hmem
  have hl := (hwf _ (gt_mem d hn.1)).2.2.2.1
  have := plo_pos hwf _ hok hne
  refine ⟨?_, ?_⟩
  · simp only [full, pathOK, List.all_cons, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hn.1, hip⟩, hok⟩
  · simp only [full, plo]; omega

include h0 h1 hrst hwf hOK hW hv hn in
/-- **The node behaviour of a recognised real node.** -/
noncomputable def ndReal : ND net b (ccOf rn x cv) j where
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
          have h1' := hnc1 (by rw [hpk]; decide)
          rw [hc] at hlen
          rw [fany_list (fun π => ccOf rn x cv (net.src j p) (tau hsat π u)) [] _ _ hlen]
          unfold specL; split
          · rw [all_eq_any_one _ _ (by rw [hlen, h1'])]
          · rfl
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

theorem fall_false : ∀ (n : Nat), 0 < n → fall n (fun _ => false) = false
  | 0, h => absurd h (Nat.lt_irrefl 0)
  | n + 1, _ => rfl

theorem fany_false' : ∀ (n : Nat), fany n (fun _ => false) = false
  | 0 => rfl
  | n + 1 => by simp only [fany, Bool.false_or]; exact fany_false' n

theorem fany_all_false : ∀ (n : Nat) (f : Fin n → Bool), (∀ i, f i = false) → fany n f = false
  | 0, _, _ => rfl
  | n + 1, f, h => by
      simp only [fany, h 0, Bool.false_or]; exact fany_all_false n _ (fun i => h i.succ)

section
variable {N : Nat} {net : Net4 N} {b : Bands4 net} {cc : Fin N → Sig}

/-- A stage node reads its reset value at time 0. -/
theorem nd_stage0 {j : Fin N} (nd : ND net b cc j) (hm : net.mg j = false) : cc j 0 = net.v j := by
  rw [nd.hc 0]
  have : nd.F 0 = 0 := warp_zero nd.wF
  simp only [hm, Bool.false_eq_true, ite_false, this, nd.r0, ite_true]

/-- A merge node is low at time 0 when every source reads its reset value. -/
theorem nd_merge0 (hOK : net.OK) {j : Fin N} (nd : ND net b cc j) (hm : net.mg j = true)
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

/-! ## `design_beh4` -/

section
variable {N : Nat} {d : Design} {net : Net4 N} {b : Bands4 net} {rn : Fin N → RNode} {rank : Fin N → Nat}
  {rw fuel : Nat} {x : Fin d.n → Sig} (hsat : SatPinW d plG x)
  (h0 : ∀ t, x (d.wire 0) t = false) (h1 : ∀ t, x (d.wire 1) t = true)
  {T : Nat} (hT : 1 ≤ T) (hrst : ∀ t, x (d.wire rw) t = decide (t < T))
  {cv : Fin N → Sig} (hr : Recog6 d net b rn rank rw fuel) (hOK : net.OK) (harb : HARB net b rn x cv)

include hsat h0 h1 hT hrst hr hOK harb

/-- The node behaviours: real nodes from the netlist, virtual ones from H_ARB. -/
noncomputable def ndAll (j : Fin N) : ND net b (ccOf rn x cv) j :=
  if h : (rn j).virt = true then Classical.choice (harb.1 j h)
  else ndReal hsat h0 h1 hT hrst hr.1 hOK harb.2.1 j (by simpa using h) (hr.2 j (by simpa using h))

theorem init0 : ∀ j, ccOf rn x cv j 0 = net.v j := by
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
          apply nd_merge0 hOK (ndAll hsat h0 h1 hT hrst hr hOK harb j) hm
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
            · exact nd_stage0 (ndAll hsat h0 h1 hT hrst hr hOK harb _) (by simpa using hms)
      · exact nd_stage0 (ndAll hsat h0 h1 hT hrst hr hOK harb j) (by simpa using hm)
  exact fun j => key (rank j) j (Nat.le_refl _)

/-- **W-E4n: `design_beh4`.** Every per-pin behaviour of a recognised netlist
(constant wires, reset high until `T`, H_ARB) is a `Beh4` of the recognised
`Net4` in its bands, for every select sequence `sel` and every monotone guarded
count `gc`: its node `j` is the wire of `j`'s LUT when `j` is real. -/
theorem design_beh4 (sel : Nat → Nat → Bool) (gc : (j : Fin N) → Fin (net.ar j) → Nat → Nat)
    (gcmono : ∀ j p a s, a ≤ s → gc j p a ≤ gc j p s) :
    ∃ bh : Beh4 net b sel, (∀ j t, bh.c j t = ccOf rn x cv j t) ∧ bh.gc = gc ∧
      (∀ j, (rn j).virt = false → ∀ t, bh.c j t = x (d.wire (gt d (rn j).lut).out) t) := by
  refine ⟨ofND sel (ccOf rn x cv) (ndAll hsat h0 h1 hT hrst hr hOK harb) gc gcmono
    (fun j hm => by rw [init0 hsat h0 h1 hT hrst hr hOK harb j]; exact ((hOK j ⟨0, net.ar_pos j⟩).2.2.2.1 hm).1),
    fun j t => rfl, rfl, fun j hv t => ?_⟩
  show ccOf rn x cv j t = _
  unfold ccOf; rw [hv, (hr.2 j hv).2.1]; rfl

end

/-! ## Certificates as data, and the netlist-level verdict -/

section
variable {N : Nat} {net : Net4 N}

/-- A stage pin's Back certificate as data (STRICT margin: `hiQ < loP + d`). -/
def backOK (b : Bands4 net) (j : Fin N) (p : Fin (net.ar j)) (D : DW) : Bool :=
  D.valid net && D.st == (net.src j p).val && D.en == j.val &&
    D.cx == (if net.pk j p = PK.filt then some (net.grp j p, net.br j p) else none) &&
    decide (D.tk net + net.off j p ≤ 1) && decide (b.hiQ j < b.loP j p + D.d b)

theorem backOK_sound (b : Bands4 net) (j : Fin N) (p : Fin (net.ar j)) (D : DW) (h : backOK b j p D = true) :
    BackW1 b j p := by
  simp only [backOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hv, hs⟩, he⟩, hc⟩, ht⟩, hq⟩ := h
  have w := DW.sound b D hv (net.src j p) j hs.symm he.symm
  rw [hc] at w
  exact ⟨_, _, w, ht, by omega⟩

/-- A line pin's certificate as data (STRICT: every hop window `< d`). -/
def lineOK (b : Bands4 net) (j : Fin N) (p : Fin (net.ar j)) (D : DW) : Bool :=
  D.valid net && D.st == (net.src j p).val && D.en == (net.src j p).val && D.cx == none &&
    decide (D.tk net ≤ 1) && (List.range (net.nc j p - 1)).all (fun i => decide (b.dw j p i < D.d b))

theorem lineOK_sound (b : Bands4 net) (j : Fin N) (p : Fin (net.ar j)) (D : DW) (h : lineOK b j p D = true) :
    LineW b j p := by
  simp only [lineOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨hv, hs⟩, he⟩, hc⟩, ht⟩, hw⟩ := h
  have w := DW.sound b D hv (net.src j p) (net.src j p) hs.symm he.symm
  rw [hc] at w
  exact ⟨_, _, w, ht, fun i hi => Nat.le_of_lt (hw i (by omega))⟩

/-- A binary merge's exclusivity certificate as data. -/
def exclOK (b : Bands4 net) (x : Fin N) (g a0 a1 : Nat) (D : DW) (u0 u1 : UA) : Bool :=
  decide (net.ar x ≤ 1) ||
  (decide (net.ar x = 2) && decide (a0 < 2) && decide (a1 < 2) && a0 != a1 && D.valid net && D.en == x.val &&
    D.cx == none && decide (D.tk net ≤ 1) && decide (D.st < N) &&
    u0.ok net x.val a0 D.st g false && u1.ok net x.val a1 D.st g true)

theorem exclOK_sound (b : Bands4 net) (x : Fin N) (g a0 a1 : Nat) (D : DW) (u0 u1 : UA)
    (h : exclOK b x g a0 a1 D u0 u1 = true) : ExclW b x := by
  simp only [exclOK, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne, ne_eq] at h
  rcases h with h | h
  · exact Or.inl h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨har, h0⟩, h1⟩, hne⟩, hv⟩, he⟩, hc⟩, ht⟩, hS⟩, hu0⟩, hu1⟩ := h
  have w := DW.sound b D hv ⟨D.st, hS⟩ x rfl he.symm
  rw [hc] at w
  have h0' : a0 < net.ar x := by omega
  have h1' : a1 < net.ar x := by omega
  exact Or.inr ⟨har, ⟨D.st, hS⟩, g, ⟨a0, h0'⟩, ⟨a1, h1'⟩, _, _, _, _,
    fun e => hne (congrArg Fin.val e), w, ht,
    UA.sound b u0 x ⟨a0, h0'⟩ ⟨D.st, hS⟩ g false hu0, UA.sound b u1 x ⟨a1, h1'⟩ ⟨D.st, hS⟩ g true hu1⟩

end

section
variable {N : Nat} {d : Design} {net : Net4 N} {b : Bands4 net} {rn : Fin N → RNode} {rank : Fin N → Nat}
  {rw fuel : Nat} {x : Fin d.n → Sig} {cv : Fin N → Sig}

/-- **The netlist-level verdict** (what a run of `xevents5` means). The
executable checks `Recog6`, `Net4.OK` and, per item, the data certificates
`backOK` / `exclOK` / `lineOK`; `cp`, `cxm`, `cl` record which items it certified.
Then for every per-pin behaviour `x` of the parsed netlist (constant wires,
reset high until `T`, H_ARB), every select sequence `sel` and every monotone
guarded count `gc`, there is a `Beh4` realising `x` such that — if that
realisation satisfies the bundling hypothesis SelOK, GuardOK, and the residual
obligations of the items the checker did NOT certify — every node, in
particular every real LUT wire, is its reset value flipped `M t j` times at
every time. With no residual items (a CLEAN verdict) the last hypotheses are
vacuous. -/
theorem design_verdict (hr : Recog6 d net b rn rank rw fuel) (hOK : net.OK)
    (back : (j : Fin N) → Fin (net.ar j) → DW) (line : (j : Fin N) → Fin (net.ar j) → DW)
    (xg xa0 xa1 : Fin N → Nat) (xD : Fin N → DW) (xu0 xu1 : Fin N → UA)
    (cp : (j : Fin N) → Fin (net.ar j) → Bool) (cxm : Fin N → Bool) (cl : (j : Fin N) → Fin (net.ar j) → Bool)
    (hcp : ∀ j p, cp j p = true → backOK b j p (back j p) = true)
    (hcx : ∀ m, cxm m = true → exclOK b m (xg m) (xa0 m) (xa1 m) (xD m) (xu0 m) (xu1 m) = true)
    (hcl : ∀ j p, cl j p = true → lineOK b j p (line j p) = true)
    (hsat : SatPinW d plG x) (h0 : ∀ t, x (d.wire 0) t = false) (h1 : ∀ t, x (d.wire 1) t = true)
    {T : Nat} (hT : 1 ≤ T) (hrst : ∀ t, x (d.wire rw) t = decide (t < T)) (harb : HARB net b rn x cv)
    (sel : Nat → Nat → Bool) (gc : (j : Fin N) → Fin (net.ar j) → Nat → Nat)
    (gcmono : ∀ j p a s, a ≤ s → gc j p a ≤ gc j p s) :
    ∃ bh : Beh4 net b sel, (∀ j t, bh.c j t = ccOf rn x cv j t) ∧
      (bh.SelOK → bh.GuardOK →
        (∀ j p s, net.mg j = false → net.pk j p ≠ PK.guard → cp j p = false → bh.P j p s ≤ bh.M (bh.Q j s) j + 1) →
        (∀ m s, net.mg m = true → cxm m = false → fodd (net.ar m) (fun p => bh.P m p s) ≤ 1) →
        (∀ j p s, net.pk j p = PK.multi → cl j p = false → ContigF (net.nc j p) (bh.cm j p s)) →
        ∀ t j, (rn j).virt = false →
          x (d.wire (gt d (rn j).lut).out) t = ph (net.v j) (bh.M t j)) := by
  obtain ⟨bh, hc, _, hreal⟩ := design_beh4 hsat h0 h1 hT hrst hr hOK harb sel gc gcmono
  refine ⟨bh, hc, fun hsel hguard rB rX rL t j hv => ?_⟩
  rw [← hreal j hv t]
  exact Beh4F.verdictR bh hOK cp cxm cl
    (fun j p _ _ h => backOK_sound b j p _ (hcp j p h))
    (fun m _ h => exclOK_sound b m _ _ _ _ _ _ (hcx m h))
    (fun j p _ h => lineOK_sound b j p _ (hcl j p h))
    rB rX rL hsel hguard t j

end

end Formal.Core.XAudit.Events6
