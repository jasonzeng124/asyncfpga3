import Formal.Cells.FiniteNetWit2

/-!
# Probe Bfin3 (shard B): what C's unit-delay run `chW` cannot carry at gate level

Note: `formal/notes/B-finite-net-wit2.md`. Two obstructions, both about WIRING a B gate model
to the channel signal it drives on chW, for ANY delay bounds:

* `chW_src_unwired`: no node `O` of the REAL `bd_src` LUT (`¬ack`, any `Win lo hi`) drives a
  source's request channel of chW through any `Wire`. chW's sources offer one token and stop
  (C's sim: "wait forever", H_LUT_SI unbounded); their acknowledge ends low, so the real LUT
  excitation is `1` forever and the request must rise again. A gate-modelled source and a
  terminating gcd run are incompatible; the sources must stay contracts on chW, and any
  witness with gate-level sources is an infinite (re-requesting) run.
* `chW_steer_unwired`: no node of the REAL `bd_steer` `u` LUT (any `Win lo hi`, `1 ≤ lo`,
  H_PWR, ANY select trace) drives a branch output request of chW through any `Wire`, for
  every steer branch whose first request comes one tick after the input's first request
  (38 of the 53 branches that fire on chW, by the untrusted pre-check; `steer_fires` exhibits
  one in Lean): C's
  steer takes ONE tick from input request to branch request, B's LUT (≥ 1) plus wire (≥ 1)
  at least two. This is why `FiniteNetWit2.NW` leaves the gate-modelled nodes unwired.

**Assumed:** nothing. **Proved:** the two theorems, from kernel checks on chW's event lists
(`srcChk`; the event-list facts of `steer_fires`). Core Lean only.
-/

namespace Formal.Cells.FiniteNetSrc
open Formal.Cells
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapNet.Wit (CD cdA chW bv)
open Formal.Cells.WinFifo (Win)
open Formal.Cells.LutFbBridge2Env (Wire)
open Formal.Cells.FiniteRunsWit (sortedB bnd NB bv_tail bv_low bv_phase)
open Formal.Cells.FiniteNetWit2 (stTF ch_sorted)
open Formal.Net.Ops.Gen (genF steerF src_gate)
open Formal.Gen Formal.Gen.Cells

def srcChk : K NC → Bool
  | .src z _ _ => bnd (cdA z).rq && bnd (cdA z).ak && !bv (cdA z).rq NB && !bv (cdA z).ak NB
  | _ => true

set_option maxRecDepth 100000

theorem src_all : ops.all srcChk = true := by decide +kernel

/-- **No gate-level `bd_src` on chW**: for every source of gcd_hw and ANY delay bounds, no
node of the REAL source LUT drives chW's request through a wire. -/
theorem chW_src_unwired {o : Fin NO} {z : Fin NC} {w d : Nat} (h : opAt o = .src z w d)
    {O : Nat → Bool} {lo hi wl wh : Nat}
    (H_LUT_WIN : Win lo hi (fun t => genF bd_src_W2 "u" .O ["ack"] [(chW z).ack t]) O)
    (H_WIRE : Wire wl wh O (chW z).req) : False := by
  have hc := List.all_eq_true.mp src_all _ (getD_mem (o := o))
  rw [h] at hc
  simp only [srcChk, Bool.and_eq_true, Bool.not_eq_true'] at hc
  obtain ⟨⟨⟨hbr, hba⟩, hr⟩, ha⟩ := hc
  obtain ⟨s, s1, s2, e⟩ := H_WIRE.H_WIN (NB + hi + wh) (by omega)
  obtain ⟨u, u1, u2, e2⟩ := H_LUT_WIN s (by omega)
  have hu : (chW z).ack u = false := by
    show bv (cdA z).ak u = false; rw [bv_tail hba u (by omega)]; exact ha
  have hq : (chW z).req (NB + hi + wh) = false := by
    show bv (cdA z).rq _ = false; rw [bv_tail hbr _ (by omega)]; exact hr
  simp only at e2
  rw [hq, e2, hu, src_gate] at e
  cases e

/-- The steer's branch output channel. -/
def brC (t f : Fin NC) (b : Bool) : Fin NC := if b then t else f

/-- **No wired steer branch on chW**: for every steer of gcd_hw and every branch whose output
request first rises on chW one tick after the input request first rises (`hord`, a fact
about chW's event lists), no node of the REAL `bd_steer` `u` LUT (any `Win lo hi` with
`1 ≤ lo` and H_PWR, any select trace `s`) drives that request through any wire. -/
theorem chW_steer_unwired {o : Fin NO} {j t f : Fin NC} (_h : stTF (opAt o) = some (j, t, f))
    (b : Bool) (hfire : (cdA (brC t f b)).rq ≠ [])
    (hord : (cdA (brC t f b)).rq.getD 0 1 ≤ (cdA j).rq.getD 0 1 + 1) (s O : Nat → Bool)
    {lo hi wl wh : Nat}
    (H_LUT_WIN : Win lo hi (fun u => steerF b ((chW j).req u, s u)) O) (H_LUT_POS : 1 ≤ lo)
    (H_PWR : ∀ u, u < hi → O u = false)
    (H_WIRE : Wire wl wh O (chW (brC t f b)).req) : False := by
  have sc := (ch_sorted (brC t f b)).1
  have sj := (ch_sorted j).1
  have hpos : 0 < (cdA (brC t f b)).rq.length := List.length_pos_iff.2 hfire
  generalize he : (cdA (brC t f b)).rq.getD 0 1 = e at hord
  -- the branch request is high at `e + 1`
  have hi1 : (chW (brC t f b)).req (e + 1) = true := by
    show bv _ _ = true
    rw [bv_phase _ sc 0 (e + 1) 1 hpos (by omega) (fun h1 => by
      have := FiniteNetWit.sorted_succ _ sc 0 1 h1; omega)]; rfl
  have hwh : wh ≤ e + 1 := by
    apply Classical.byContradiction; intro hn
    rw [H_WIRE.H_PWR (e + 1) (by omega)] at hi1; cases hi1
  have hwl := H_WIRE.H_POS
  obtain ⟨u, u1, u2, eu⟩ := H_WIRE.H_WIN (e + 1) hwh
  rw [hi1] at eu
  by_cases hu : u < hi
  · rw [H_PWR u hu] at eu; cases eu
  · obtain ⟨v, v1, v2, ev⟩ := H_LUT_WIN u (by omega)
    have hj : (chW j).req v = false := by
      show bv _ _ = false
      exact bv_low _ sj v 1 (Or.inr (by omega))
    simp only at ev
    rw [ev, LutFbBridge2.steerF_gate, hj] at eu
    cases eu

/-- The obstruction is not vacuous: some steer branch fires on chW. -/
theorem steer_fires : ∃ (o : Fin NO) (j t f : Fin NC) (b : Bool),
    stTF (opAt o) = some (j, t, f) ∧ (cdA (brC t f b)).rq ≠ [] ∧
      (cdA (brC t f b)).rq.getD 0 1 ≤ (cdA j).rq.getD 0 1 + 1 :=
  ⟨⟨5, by decide⟩, 418, 12, 15, false, rfl, by decide +kernel, by decide +kernel⟩


/-! ## The source `bd_src`, truncated (`AssumeGuaranteeMux.src_segK`'s time-indexed form) -/

open Formal.Cells.WinFifoCausal (NoRevertI nt nt_lo nt_before)
open Formal.Cells.WinFifo (win_le)
open Formal.Cells.PipeTimed (Vph)
open Formal.Cells.FiniteNet (GPhT nt_found)
open Formal.Cells.AssumeGuaranteeMux (srcE)

/-- A `Win` LUT whose excitation shows `v` on `[c, b)` shows `v` from its edge
`nt O lo hi c v` to `b + lo` (no spacing needed: past `c + hi` the window reads `[c, b)`). -/
theorem phase_hold {x O : Nat → Bool} {lo hi c b : Nat} {v : Bool} (hW : Win lo hi x O)
    (hN : NoRevertI lo hi x O) (hx : ∀ s, c ≤ s → s < b → x s = v) (hc : hi ≤ c)
    {s : Nat} (h1 : nt O lo hi c v ≤ s) (h2 : s < b + lo) : O s = v := by
  have hlh := win_le hW
  by_cases hs : c + hi ≤ s
  · obtain ⟨u, u1, u2, e⟩ := hW s (by omega)
    rw [e]; exact hx u (by omega) (by omega)
  · have hf : nt O lo hi c v < c + hi + 1 := by omega
    have hv := nt_found hf
    have hl := nt_lo O c v hlh (hi := hi)
    exact hN c b v _ s hx (by omega) hl h1 h2 hv

/-- **The source, truncated** (the REAL `bd_src` `u`, LUT1 `¬ack`, no reset; H_PWR_SRC as in
`src_segK`). The acknowledge pin clean on `[0, T)` (edges `α`, edge set `La`, closed
downwards) gives the node clean on `[0, T + lo)`, with edges `srcE` (power-up rise, then
edge `k + 1` after acknowledge edge `k`), node edge `k + 1` existing iff acknowledge edge `k`
does. H_SPACE only for edges that exist. Consequence on a finite run: after the acknowledge's
last edge the node keeps its last phase forever, so an acknowledge that ends low leaves the
source requesting again (`chW_src_unwired`). -/
theorem tsrc {a O : Nat → Bool} {lo hi T : Nat} {α : Nat → Nat} {La : Nat → Prop}
    (H_LUT_WIN : Win lo hi (fun t => genF bd_src_W2 "u" .O ["ack"] [a t]) O)
    (H_NO_REVERT : NoRevertI lo hi (fun t => genF bd_src_W2 "u" .O ["ack"] [a t]) O)
    (H_LUT_POS : 1 ≤ lo)
    (H_PWR_SRC : ∀ t, t + 1 < hi → O (t + 1) ≠ O t → O (t + 1) = true)
    (H_SPACE0 : La 0 → hi ≤ α 0) (H_SPACE : ∀ j, La (j + 1) → α j + hi < α (j + 1) + lo)
    (H_DOWN : ∀ j, La (j + 1) → La j)
    (ha : GPhT a α La T) :
    GPhT O (srcE O lo hi α) (fun k => k = 0 ∨ La (k - 1)) (T + lo) := by
  classical
  have ex : (fun t => genF bd_src_W2 "u" .O ["ack"] [a t]) = fun t => !a t :=
    funext fun t => src_gate (a t)
  rw [ex] at H_LUT_WIN H_NO_REVERT
  have hlh := win_le H_LUT_WIN
  have am : ∀ j, La j → hi ≤ α j := by
    intro j
    induction j with
    | zero => exact H_SPACE0
    | succ j ih => intro h; have := ih (H_DOWN j h); have := H_SPACE j h; omega
  -- the excitation on phase `k` of the acknowledge, up to `b k`
  let b : Nat → Nat := fun k => if La (k + 1) then min (α (k + 1)) T else T
  have xk : ∀ k, La k → ∀ s, α k ≤ s → s < b k → (!a s) = Vph (k + 1) := by
    intro k hk s h1 h2
    have hT : s < T := by
      show s < T; simp only [b] at h2; split at h2 <;> omega
    rw [ha.ph k s hT hk h1 (fun hl => by simp only [b, if_pos hl] at h2; omega),
      PipeTimed.Vph_succ]
  have x0 : ∀ s, 0 ≤ s → s < (if La 0 then min (α 0) T else T) → (!a s) = true := by
    intro s _ h2
    have hT : s < T := by split at h2 <;> omega
    rw [ha.pre s hT (by
      by_cases hl : La 0
      · rw [if_pos hl] at h2; exact Or.inr (by omega)
      · exact Or.inl hl)]; rfl
  refine ⟨fun s hs h => ?_, fun k s hs hk h1 h2 => ?_⟩
  · rcases h with h | h
    · exact absurd (Or.inl rfl) h
    · exact nt_before O 0 hi 0 true s (by omega) h
  · match k, hk with
    | 0, _ =>
      -- the power-up phase
      show O s = Vph 0
      rw [PipeTimed.Vph_even 0]
      have h1' : nt O 0 hi 0 true ≤ s := h1
      let b0 := if La 0 then min (α 0) T else T
      have hhi : hi ≤ s → O hi = true := by
        intro hs'
        obtain ⟨u, u1, u2, e⟩ := H_LUT_WIN hi (Nat.le_refl _)
        rw [e]; refine x0 u (Nat.zero_le _) ?_
        by_cases hl : La 0
        · rw [if_pos hl]; have := H_SPACE0 hl; omega
        · rw [if_neg hl]; omega
      by_cases hsh : s < hi
      · -- before `hi` the output only rises
        have hle : nt O 0 hi 0 true ≤ s := h1'
        have hsp := PipeTimed.lfind_spec (fun t => decide (0 + 0 ≤ t) && (O t == true))
          (0 + hi + 1) (by unfold nt at hle; omega)
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hsp
        have rise : ∀ d, nt O 0 hi 0 true + d < hi → O (nt O 0 hi 0 true + d) = true := by
          intro d
          induction d with
          | zero => intro _; exact hsp.2
          | succ d ih =>
            intro h
            by_cases hc : O (nt O 0 hi 0 true + d + 1) = O (nt O 0 hi 0 true + d)
            · rw [show nt O 0 hi 0 true + (d + 1) = nt O 0 hi 0 true + d + 1 by omega, hc]
              exact ih (by omega)
            · rw [show nt O 0 hi 0 true + (d + 1) = nt O 0 hi 0 true + d + 1 by omega]
              exact H_PWR_SRC _ (by omega) hc
        have := rise (s - nt O 0 hi 0 true) (by omega)
        rwa [show nt O 0 hi 0 true + (s - nt O 0 hi 0 true) = s by omega] at this
      · by_cases hb : s < b0 + lo
        · exact H_NO_REVERT 0 b0 true hi s x0 (Nat.le_refl _) (by omega) (by omega) hb
            (hhi (by omega))
        · have hl : La 0 := by
            apply Classical.byContradiction; intro hl
            simp only [b0, if_neg hl] at hb; omega
          have hα : α 0 < T := by
            apply Classical.byContradiction; intro hn
            simp only [b0, if_pos hl] at hb; omega
          have h2' : s < nt O lo hi (α 0) (Vph 1) := h2 (Or.inr hl)
          have := nt_before O lo hi (α 0) (Vph 1) s (by simp only [b0, if_pos hl] at hb; omega) h2'
          rw [this, show (1 : Nat) = 0 + 1 from rfl, PipeTimed.Vph_succ, Bool.not_not,
            PipeTimed.Vph_even 0]
    | j + 1, hk =>
      have hj : La j := hk.elim (fun h => absurd h (by omega)) (fun h => by simpa using h)
      show O s = Vph (j + 1)
      have h1' : nt O lo hi (α j) (Vph (j + 1)) ≤ s := h1
      by_cases hb : s < b j + lo
      · exact phase_hold H_LUT_WIN H_NO_REVERT (xk j hj) (am j hj) h1' hb
      · have hl : La (j + 1) := by
          apply Classical.byContradiction; intro hl
          simp only [b, if_neg hl] at hb; omega
        have hα : α (j + 1) < T := by
          apply Classical.byContradiction; intro hn
          simp only [b, if_pos hl] at hb; omega
        have h2' : s < nt O lo hi (α (j + 1)) (Vph (j + 1 + 1)) := h2 (Or.inr hl)
        have := nt_before O lo hi (α (j + 1)) (Vph (j + 1 + 1)) s
          (by simp only [b, if_pos hl] at hb; omega) h2'
        rw [this, PipeTimed.Vph_succ, Bool.not_not]


namespace WitS

/-- One finite handshake: the acknowledge is high on `[3, 7)` and low forever after; the
REAL source LUT at unit delay. -/
def aW (t : Nat) : Bool := decide (3 ≤ t ∧ t < 7)
def OW (t : Nat) : Bool := if t = 0 then false else !aW (t - 1)
def αW : Nat → Nat
  | 0 => 3
  | _ => 7

theorem aW_gph (T : Nat) : GPhT aW αW (fun j => j < 2) T := by
  refine ⟨fun s _ h => ?_, fun j s _ hj h1 h2 => ?_⟩
  · have h' : s < 3 := h.elim (fun h => absurd (by omega) h) id
    unfold aW; simp only [decide_eq_false_iff_not]; omega
  · match j, hj with
    | 0, _ =>
      have h1' : 3 ≤ s := h1
      have h2' : s < 7 := h2 (by omega)
      unfold aW; rw [PipeTimed.Vph_even 0]; simp; omega
    | 1, _ =>
      have h1' : 7 ≤ s := h1
      unfold aW; rw [show (1 : Nat) = 2 * 0 + 1 from rfl, PipeTimed.Vph_odd]; simp; omega

/-- **Non-vacuity of `tsrc`**: every hypothesis holds; the conclusion's last phase (edge 2,
after the acknowledge falls) is high forever: the real source requests again. -/
theorem tsrc_witness (T : Nat) :
    GPhT OW (srcE OW 1 1 αW) (fun k => k = 0 ∨ (k - 1) < 2) (T + 1) ∧ OW 100 = true := by
  have hstep : ∀ t, OW (t + 1) = genF bd_src_W2 "u" .O ["ack"] [aW t] := fun t => by
    rw [src_gate]; rfl
  have sw := FiniteNetWit2.step_win hstep
  refine ⟨tsrc sw.1 sw.2 (Nat.le_refl 1) (fun t ht => by omega) (fun _ => by decide)
    (fun j hj => by have : j = 0 := by omega
                    subst this; decide) (fun j hj => by omega) (aW_gph T), by decide⟩

end WitS

end Formal.Cells.FiniteNetSrc
