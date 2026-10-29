import Formal.Core.XAudit.Events8Beh

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
  {rw fuel : Nat} {x : Fin d.n → Sig} (hsat : SatPin d plG x)

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

end Formal.Core.XAudit.Events8Bridge
