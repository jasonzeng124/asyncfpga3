import Formal.Cells.FiniteRuns
import Formal.Cells.SelfAuditB8
import Formal.Cells.AssumeGuaranteeEndsCap
import Formal.Net.CapstoneWitness

/-!
# Probe Bfin (shard B): C's terminating gcd run meets the finite link model

Note: `formal/notes/B-finite-runs.md`. Companion of `FiniteRuns`.

## Assumed / proved / NOT covered

**Assumed:** nothing beyond the imported files (every check is kernel `decide`).

**Proved:**
1. `gcdNetOK_req_alternates`, `chW_no_gcdNet`: `AssumeGuaranteeEndsCap.gcd_hw_safe_net` has
   the same restriction as the two link theorems found by self-audit 5: its hypothesis
   `GcdNetOK ch N` yields `PhysLink` for every link (`physLink_of_net`), so every link's
   input request alternates forever, and NO elaboration `N` makes C's witness run `chW`
   meet `GcdNetOK` (the theorem has no joint witness on a terminating run).
2. `linkB_sound`: a kernel checker over two event-list channels (`x` into the link, `y` out
   of it) implies `FiniteRuns.FPhysLink x.ch y.ch`, with B's controller node read off the
   run (`cL y.rq`: the output request one tick earlier), LUT band `[1, 1]`, feedback wire
   `[1, 1]`, both outgoing wires `[1, 1]`, reset length `R = 2`, `Es = Ea = 3`, the
   request's and acknowledge's edges read off their event lists.
3. `chW_fin_links`: **C's witness run `Wit.chW` (a = 12, b = 18, quiet after 476 ticks)
   meets `FPhysLink` on all 175 links** (34 of them never see a request: `idle_links`).
   `chW_fin_not_phys`: on the same run `PhysLink` fails on every channel pair.
4. `gcd_hw_fin_links_witness`: one run (`chW`) meets ALL hypotheses of
   `FiniteRuns.gcd_hw_safe_fin_links` jointly (H_LINKS in the finite form, H_OTHER from C's
   `w_cells`, H_BUNDLE `w_held`, H_CM_FORCED from C's `gcd_hw_forced` and the token run
   `yW`), and out0 latches a token carrying 6; `gcd_hw_fin_links_consistent` applies the
   theorem to it. (The checks are in `FiniteRunsWitData`.)
5. `fcelG_witness`, `fcelG_witness_lutFb`: the finite C-element bridge on a quiet run of
   the real `bd_c2` (pins rise once at 3 and 4, disagree at 3, node rises once at 5);
   `flink_link_witness`, `flink_link_witness_env`: the finite link-to-link lemma on a
   one-token hand-over (A rises at 5, B at 7, then quiet).

**NOT covered:** the C-element and link-to-link witnesses are small hand-built runs with
unit delays; the gcd witness is ONE run with every delay exactly one tick (C's unit-delay
simulation): B's LUT and wire windows are met at width 0 (`lo = hi`), not at a real
prjxray band; the reset `R = 2` is B's per-link reset, chosen for the run (C's model has no
reset line). Nothing here says the silicon meets the hypotheses.
Core Lean only.
-/

namespace Formal.Cells.FiniteRunsWit
open Formal.Cells
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapSafe
open Formal.Net.CapNet.Wit (CD cntLt bv nv nvA chW cdA bv_zero)
open Formal.Cells.WinFifoCausal (Stage Timing1 cph τs nt nt_eq noRevertI_shift)
open Formal.Cells.WinFifo (Win)
open Formal.Cells.PipeTimed (Vph ex)
open Formal.Cells.LutFbBridge2Env (Wire PhysLink isLink)
open Formal.Cells.FiniteRuns (FPhysLink FEnv1)

/-! ## 1. `gcd_hw_safe_net` has the same restriction -/

section net
open Formal.Cells.AssumeGuaranteeEndsCap (GcdNet GcdNetOK physLink_of_net)

/-- **`GcdNetOK` forces every link's input request to alternate forever.** -/
theorem gcdNetOK_req_alternates {ch : Fin NC → Chan} {N : GcdNet} (H : GcdNetOK ch N)
    {o : Fin NO} {i o' : Fin NC} (h : opAt o = .link i o') :
    ∀ T, (∃ t, T ≤ t ∧ (ch i).req t = true) ∧ (∃ t, T ≤ t ∧ (ch i).req t = false) :=
  SelfAuditB8.physLink_req_alternates (physLink_of_net H h)

/-- **No gate-level elaboration makes C's witness run meet `GcdNetOK`**: the hypothesis of
`gcd_hw_safe_net` excludes C's terminating gcd run. -/
theorem chW_no_gcdNet : ¬ ∃ N : GcdNet, GcdNetOK chW N := by
  intro ⟨N, H⟩
  obtain ⟨o, i, o', e⟩ := SelfAuditB8.some_link
  exact SelfAuditB8.chW_not_physLink i o' (physLink_of_net H e)

end net

/-! ## 2. Event-list facts -/

/-- Strictly increasing event list. -/
def sortedB : List Nat → Bool
  | [] => true
  | a :: L => L.all (fun e => decide (a < e)) && sortedB L

theorem cnt_zero_of : ∀ (L : List Nat) (t : Nat), (∀ e ∈ L, t ≤ e) → cntLt L t = 0
  | [], _, _ => rfl
  | a :: L, t, h => by
    have ha := h a (List.mem_cons_self ..)
    have := cnt_zero_of L t (fun e he => h e (List.mem_cons_of_mem _ he))
    simp only [cntLt, this]; simp; omega

theorem getD_mem' : ∀ (L : List Nat) (j d : Nat), j < L.length → L.getD j d ∈ L
  | [], _, _, h => absurd h (by simp)
  | a :: L, 0, _, _ => by simp
  | a :: L, j + 1, d, h => by
    simp only [List.getD_cons_succ]
    exact List.mem_cons_of_mem _ (getD_mem' L j d (by simp at h; omega))

/-- Before the first event (or always, for an empty list) the count is 0. -/
theorem cnt_low (L : List Nat) (hs : sortedB L = true) (t : Nat) (d : Nat)
    (h : L.length = 0 ∨ t ≤ L.getD 0 d) : cntLt L t = 0 := by
  cases L with
  | nil => rfl
  | cons a L =>
    simp only [List.getD_cons_zero, List.length_cons] at h
    have h' : t ≤ a := by omega
    simp only [sortedB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hs
    exact cnt_zero_of _ t (fun e he => by
      rcases List.mem_cons.1 he with rfl | he
      · exact h'
      · have := hs.1 e he; omega)

/-- On `(L[j], L[j+1]]` the count is `j + 1`. -/
theorem cnt_phase : ∀ (L : List Nat), sortedB L = true → ∀ (j t d : Nat), j < L.length →
    L.getD j d < t → (j + 1 < L.length → t ≤ L.getD (j + 1) d) → cntLt L t = j + 1
  | [], _, _, _, _, h, _, _ => absurd h (by simp)
  | a :: L, hs, j, t, d, hj, h1, h2 => by
    simp only [sortedB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hs
    cases j with
    | zero =>
      simp only [List.getD_cons_zero] at h1
      have : cntLt L t = 0 := by
        cases L with
        | nil => rfl
        | cons b L =>
          have hb := h2 (by simp)
          simp only [List.getD_cons_succ, List.getD_cons_zero] at hb
          have hs2 := hs.2
          simp only [sortedB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hs2
          exact cnt_zero_of _ t (fun e he => by
            rcases List.mem_cons.1 he with rfl | he
            · exact hb
            · have := hs2.1 e he; omega)
      simp only [cntLt, this, if_pos h1]
    | succ j =>
      simp only [List.getD_cons_succ, List.length_cons] at h1 h2 hj
      have ih := cnt_phase L hs.2 j t d (by omega) h1 (fun h => h2 (by omega))
      have ha : a < t := by
        have := hs.1 _ (getD_mem' L j d (by omega)); omega
      simp only [cntLt, ih, if_pos ha]

theorem par_succ (j : Nat) : ((j + 1) % 2 == 1) = Vph j := by
  unfold Vph LinkTimed.Vph
  by_cases h : j % 2 = 0
  · have : (j + 1) % 2 = 1 := by omega
    simp [h, this]
  · have : (j + 1) % 2 = 0 := by omega
    simp [h, this]

theorem bv_phase (L : List Nat) (hs : sortedB L = true) (j t d : Nat) (hj : j < L.length)
    (h1 : L.getD j d < t) (h2 : j + 1 < L.length → t ≤ L.getD (j + 1) d) : bv L t = Vph j := by
  unfold bv; rw [cnt_phase L hs j t d hj h1 h2, par_succ]

theorem bv_low (L : List Nat) (hs : sortedB L = true) (t d : Nat)
    (h : L.length = 0 ∨ t ≤ L.getD 0 d) : bv L t = false := by
  unfold bv; rw [cnt_low L hs t d h]; rfl

/-- After the last event an event-list signal is constant. -/
theorem cnt_tail : ∀ (L : List Nat) (N t : Nat), L.all (fun e => decide (e < N)) = true →
    N ≤ t → cntLt L t = cntLt L N
  | [], _, _, _, _ => rfl
  | a :: L, N, t, h, ht => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [cntLt, cnt_tail L N t h.2 ht, if_pos h.1, if_pos (show a < t by omega)]

theorem bv_tail {L : List Nat} {N : Nat} (h : L.all (fun e => decide (e < N)) = true) (t : Nat)
    (ht : N ≤ t) : bv L t = bv L N := by
  unfold bv; rw [cnt_tail L N t h ht]

theorem nvA_tail : ∀ (L : List (Nat × Nat)) (N t acc : Nat),
    L.all (fun p => decide (p.1 < N)) = true → N ≤ t → nvA L t acc = nvA L N acc
  | [], _, _, _, _, _ => rfl
  | p :: L, N, t, acc, h, ht => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [nvA, if_pos h.1, if_pos (show p.1 < t by omega)]
    exact nvA_tail L N t _ h.2 ht

theorem nv_tail {L : List (Nat × Nat)} {N : Nat} (d : Nat)
    (h : L.all (fun p => decide (p.1 < N)) = true) (t : Nat) (ht : N ≤ t) :
    nv d L t = nv d L N := nvA_tail L N t d h ht

/-- A Boolean property checked on `[0, N]` and constant from `N` on holds everywhere. -/
theorem all_t {Q : Nat → Bool} (N : Nat) (h : (List.range (N + 1)).all Q = true)
    (ht : ∀ t, N ≤ t → Q t = Q N) : ∀ t, Q t = true := by
  intro t
  by_cases hN : t ≤ N
  · exact List.all_eq_true.1 h t (List.mem_range.2 (by omega))
  · rw [ht t (by omega)]; exact List.all_eq_true.1 h N (List.mem_range.2 (by omega))

/-! ## 3. The link checker -/

/-- The request's `j`-th edge (first instant at its new value); `R` = 2 for an empty list. -/
def ρL (L : List Nat) (j : Nat) : Nat := L.getD j 1 + 1

/-- The acknowledge's phase starts: `R = 2`, then its edges. -/
def αL (L : List Nat) : Nat → Nat
  | 0 => 2
  | j + 1 => L.getD j 0 + 1

/-- B's controller node, read off the run: the output request one tick earlier. -/
def cL (L : List Nat) (t : Nat) : Bool := bv L (t + 1)

theorem αL_zero (L : List Nat) : αL L 0 = 2 := rfl
theorem αL_succ (L : List Nat) (j : Nat) : αL L (j + 1) = L.getD j 0 + 1 := rfl

def rst2 (t : Nat) : Bool := decide (t < 2)

def c2nB (a b q r : Bool) : Bool := !r && ((a && !b) || (a && q) || (!b && q))

/-- A bound past every event of the run (the last is at tick 474). -/
abbrev NB : Nat := 640

def lutQ (x y : CD) (t : Nat) : Bool :=
  bv y.rq (t + 2) == c2nB (bv x.rq t) (bv y.ak t) (bv y.rq t) (decide (t < 2))

def datQ (x y : CD) (t : Nat) : Bool :=
  (!bv y.rq (t + 1) || nv y.d0 y.dt t == nv x.d0 x.dt t) &&
  (bv y.rq (t + 2) || nv y.d0 y.dt (t + 1) == nv y.d0 y.dt t)

def sndQ (x y : CD) (j : Nat) : Bool :=
  !decide (j + 1 < x.rq.length) || !decide (j ≤ y.ak.length) ||
  (cL y.rq (cph (ρL x.rq) (αL y.ak) j + 1) == Vph j &&
    decide (cph (ρL x.rq) (αL y.ak) j + 1 + 3 ≤ ρL x.rq (j + 1)))

def rcvQ (x y : CD) (j : Nat) : Bool :=
  !decide (j < y.ak.length) || !decide (j < x.rq.length) ||
  (cL y.rq (cph (ρL x.rq) (αL y.ak) j + 1) == Vph j &&
    decide (cph (ρL x.rq) (αL y.ak) j + 1 + 3 ≤ αL y.ak (j + 1)))

def bnd (L : List Nat) : Bool := L.all (fun e => decide (e < NB))
def bndD (L : List (Nat × Nat)) : Bool := L.all (fun p => decide (p.1 < NB))

/-- **The checker** for a link from channel `x` to channel `y`. -/
def linkB (x y : CD) : Bool :=
  (x.ak == y.rq) && bnd x.rq && bnd y.rq && bnd y.ak && bndD x.dt && bndD y.dt &&
  sortedB x.rq && sortedB y.ak && !bv y.rq 1 && decide (1 ≤ x.rq.getD 0 1) &&
  (List.range (NB + 1)).all (lutQ x y) && (List.range (NB + 1)).all (datQ x y) &&
  (List.range x.rq.length).all (sndQ x y) && (List.range y.ak.length).all (rcvQ x y)

theorem c2nB_eq (a b q r : Bool) : CElemTiming.exc CElemTiming.INIT_c2n a b q r = c2nB a b q r :=
  CElemTiming.c2n_eq a b q r

theorem wire_shift (L : List Nat) : Wire 1 1 (cL L) (bv L) where
  H_WIN := CElemTiming.transport_winDelay (Nat.le_refl 1) (Nat.le_refl 1) (fun _ => rfl)
  H_NO_REVERT := noRevertI_shift (fun t ht => by
    show bv L t = bv L (t - 1 + 1); rw [Nat.sub_add_cancel ht])
  H_POS := Nat.le_refl 1
  H_PWR := fun t ht => by have : t = 0 := by omega
                          subst this; exact bv_zero L

/-- **Soundness of the checker**: it implies B's finite physical link model. -/
theorem linkB_sound {x y : CD} (h : linkB x y = true) : FPhysLink x.ch y.ch := by
  simp only [linkB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hak, bx⟩, by1⟩, by2⟩, bdx⟩, bdy⟩, sx⟩, sy⟩, c0⟩, r0⟩, hlut⟩, hdat⟩, hsnd⟩,
    hrcv⟩ := h
  -- every instant, from the finite checks and the constant tails
  have hNB : NB = 640 := rfl
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
  have nt1 : ∀ j, cL y.rq (cph (ρL x.rq) (αL y.ak) j + 1) = Vph j →
      τs (cL y.rq) 1 1 (ρL x.rq) (αL y.ak) j = cph (ρL x.rq) (αL y.ak) j + 1 := fun j hj => by
    unfold τs; exact nt_eq _ (Nat.le_refl 1) hj
  refine ⟨rst2, cL y.rq, bv y.rq, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, x.rq.length, y.ak.length,
    ρL x.rq, αL y.ak, ?_, ?_, ⟨by decide, by decide, by decide⟩, Nat.le_refl 1, ?_, ?_,
    wire_shift y.rq, by decide, by decide, by decide, by decide, ?_, ?_⟩
  · -- Stage
    refine ⟨CElemTiming.transport_winDelay (Nat.le_refl 1) (Nat.le_refl 1) hex,
      noRevertI_shift (fun t ht => by
        have := hex (t - 1); rw [Nat.sub_add_cancel ht] at this; exact this),
      CElemTiming.transport_winDelay (Nat.le_refl 1) (Nat.le_refl 1) (fun _ => rfl), by decide⟩
  · -- FEnv1
    refine ⟨fun _ => rfl, fun t _ ht => ?_, fun j t hj h1 h2 => ?_, rfl, fun j t hj h1 h2 => ?_,
      ?_, fun j hj hj' => ?_, fun j hj hj' => ?_⟩
    · show bv x.rq t = false
      refine bv_low x.rq sx t 1 ?_
      rcases ht with ht | ht
      · exact Or.inl ht
      · exact Or.inr (by unfold ρL at ht; omega)
    · show bv x.rq t = Vph j
      exact bv_phase x.rq sx j t 1 hj (by unfold ρL at h1; omega)
        (fun h => by have := h2 h; unfold ρL at this; omega)
    · show bv y.ak t = !Vph j
      cases j with
      | zero =>
        rw [bv_low y.ak sy t 0 ?_]; · rfl
        by_cases hn : y.ak.length = 0
        · exact Or.inl hn
        · exact Or.inr (by have := h2 (by omega); rw [αL_succ] at this; omega)
      | succ k =>
        rw [bv_phase y.ak sy k t 0 (by omega) (by rw [αL_succ] at h1; omega)
          (fun h => by have := h2 h; rw [αL_succ] at this; omega), PipeTimed.Vph_succ, Bool.not_not]
    · unfold ρL; omega
    · have := List.all_eq_true.1 hsnd j (List.mem_range.2 (by omega))
      simp only [sndQ, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
        decide_eq_false_iff_not, Bool.and_eq_true, beq_iff_eq] at this
      rcases this with (h | h) | ⟨h1, h2⟩
      · exact absurd hj h
      · exact absurd hj' h
      · rw [nt1 j h1]; exact h2
    · have := List.all_eq_true.1 hrcv j (List.mem_range.2 hj)
      simp only [rcvQ, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
        decide_eq_false_iff_not, Bool.and_eq_true, beq_iff_eq] at this
      rcases this with (h | h) | ⟨h1, h2⟩
      · exact absurd hj h
      · exact absurd hj' h
      · rw [nt1 j h1]; exact h2
  · -- H_PWR
    intro t ht
    have : t = 0 := by omega
    subst this; exact c0
  · -- the acknowledge wire: `x.ak = y.rq`
    show Wire 1 1 (cL y.rq) (bv x.ak); rw [hak]; exact wire_shift y.rq
  · intro t hc
    have := datA t
    simp only [datQ, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at this
    rcases this.1 with h | h
    · exact absurd hc (by simp [cL, h])
    · exact h
  · intro t hc
    have := datA t
    simp only [datQ, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at this
    rcases this.2 with h | h
    · exact absurd hc (by simp [cL, h])
    · exact h

/-! ## 4. Non-vacuity of the finite C-element bridge -/

section celw
open Formal.Cells.LutFbBridge2 (CelG)
open Formal.Cells.AssumeGuaranteeEnds (GC2 lawC2 c2_gen)
open Formal.Cells.FiniteRuns (FEnvG fcelG_lutFb)

/-- Pin `i` of a 2-pin C-element rises once, at `3 + i`, and stays high. -/
def pw (t : Nat) (i : Fin 2) : Bool := decide (3 + i.val ≤ t)
def Ow (t : Nat) : Bool := decide (5 ≤ t)
def qw (t : Nat) : Bool := decide (6 ≤ t)
def rw3 (t : Nat) : Bool := decide (t < 3)
def ρw (i : Fin 2) (_ : Nat) : Nat := 3 + i.val

theorem xw (s : Nat) : GC2 (pw s) (qw s) (rw3 s) = decide (4 ≤ s) := by
  unfold GC2; rw [c2_gen]
  rcases (show s < 3 ∨ s = 3 ∨ 4 ≤ s by omega) with h | h | h
  · simp [rw3, h]; omega
  · subst h; decide
  · simp [pw, rw3, Formal.Net.Ops.Gen.cel2, show ¬ s < 3 by omega, show 3 ≤ s by omega,
      show 4 ≤ s by omega]

theorem tr1 {x y : Nat → Bool} (h : ∀ t, y (t + 1) = x t) : Win 1 1 x y :=
  CElemTiming.transport_winDelay (Nat.le_refl 1) (Nat.le_refl 1) h

/-- **`fcelG_lutFb` has a witness on a finite, quiet run**: the real `bd_c2` LUT (`GC2`),
LUT and feedback delays 1, reset 3; the pins rise at 3 and 4 and stay high (they DISAGREE
at `t = 3`, where the cell holds through its feedback); the node rises once, at 5, and
stays high. Every hypothesis of `fcelG_lutFb` holds (`n = 1`, `m i = 1`). -/
theorem fcelG_witness :
    CelG GC2 pw rw3 Ow qw 1 1 1 1 ∧ FEnvG pw rw3 Ow 1 1 3 ρw (fun _ => 1) (fun _ => 4) 1 1 ∧
    pw 3 0 ≠ pw 3 1 ∧ (∀ t, 5 ≤ t → Ow t = true) := by
  have C : CelG GC2 pw rw3 Ow qw 1 1 1 1 :=
    ⟨tr1 (fun t => by rw [xw]; simp [Ow]),
     noRevertI_shift (fun t ht => by
       rw [xw]; simp only [Ow, decide_eq_decide]; omega),
     tr1 (fun t => by simp [qw, Ow]), Nat.le_refl 1⟩
  refine ⟨C, ?_, by decide, fun t h => by simp [Ow]; omega⟩
  refine ⟨⟨0⟩, fun _ => rfl, fun i t h1 h2 => ?_, fun i j t hj h1 _ => ?_, fun _ => Nat.le_refl 1,
    ⟨0, rfl⟩, fun i j hj => ?_, fun j s hj hs => ?_, by decide, fun i j h _ => by omega⟩
  · rcases h2 with h2 | h2
    · exact absurd h2 (by decide)
    · simp only [ρw] at h2; simp [pw]; omega
  · have : j = 0 := by omega
    subst this; simp only [ρw] at h1; simp [pw, Vph, LinkTimed.Vph]; omega
  · have := i.isLt; simp only [ρw]; omega
  · exact ⟨1, by simp only [ρw]; omega⟩

/-- ... and so its conclusion: C's `LutFb`/`FbFirst` for the cell. -/
theorem fcelG_witness_lutFb :
    Formal.Net.Ops.Gen.LutFb (fun pv q => GC2 pv q false) pw qw Ow ∧
    Formal.Net.Ops.Gen.FbFirst qw Ow :=
  have h := fcelG_witness
  fcelG_lutFb lawC2 h.1 h.2.1 (by decide) (by decide) (fun t ht => by simp [Ow]; omega)

end celw

/-! ## 5. Non-vacuity of the finite link-to-link lemma: a one-token hand-over -/

section llw
open Formal.Cells.FiniteRuns (FPhases flink_link_env)

/-- A signal that rises once, at `o`, and stays high. -/
def st (o t : Nat) : Bool := decide (o ≤ t)

theorem st_phases (o : Nat) : FPhases (st o) (fun _ => o) 1 :=
  ⟨fun s h => by rcases h with h | h; · exact absurd h (by decide)
                 · simp [st]; omega,
   fun j s hj h1 _ => by
     have : j = 0 := by omega
     subst this; simp [st, Vph, LinkTimed.Vph]; omega⟩

theorem st_wire (o : Nat) : Wire 1 1 (st o) (st (o + 1)) where
  H_WIN := CElemTiming.transport_winDelay (Nat.le_refl 1) (Nat.le_refl 1)
    (fun t => by simp [st])
  H_NO_REVERT := noRevertI_shift (fun t ht => by simp [st]; omega)
  H_POS := Nat.le_refl 1
  H_PWR := fun t ht => by simp [st]; omega

theorem st_eps (o : Nat) : LutFbBridge2Env.ε (st (o + 1)) 1 1 (fun _ => o) 0 = o + 1 := by
  unfold LutFbBridge2Env.ε; exact nt_eq _ (Nat.le_refl 1) (by simp [st, Vph, LinkTimed.Vph])

/-- **`flink_link_env` has a witness on a finite, quiet run**: link `A`'s node rises once at
5, the request wire (delay 1) carries it to `B` at 6, `B`'s node rises once at 7, the
acknowledge wire carries it back to `A` at 8, then nothing moves (`nA = nB = 1`, reset 4,
LUT minimum delays 1). Every hypothesis holds (B's guarantee with equality), and so does
the conclusion. -/
theorem flink_link_witness :
    FPhases (st 5) (fun _ => 5) 1 ∧ FPhases (st 7) (fun _ => 7) 1 ∧
    Wire 1 1 (st 5) (st 6) ∧ Wire 1 1 (st 7) (st 8) ∧ 4 + 1 ≤ 5 ∧
    (∀ j, j < 1 → j < 1 ∧ LutFbBridge2Env.ε (st 6) 1 1 (fun _ => 5) j + 1 = 7) := by
  refine ⟨st_phases 5, st_phases 7, st_wire 5, st_wire 7, by decide, fun j hj => ?_⟩
  have : j = 0 := by omega
  subst this; exact ⟨hj, by rw [st_eps 5]⟩

/-- ... and its conclusion on that run (A's acknowledge-side H_RCV with `Ea = 3`, B's
request-side H_REQ, both DI wires). -/
theorem flink_link_witness_env :
    (∀ j t, j < 1 → LutFbBridge2Env.ε (st 6) 1 1 (fun _ => 5) j ≤ t →
      (j + 1 < 1 → t < LutFbBridge2Env.ε (st 6) 1 1 (fun _ => 5) (j + 1)) → st 6 t = Vph j) ∧
    (∀ j, j < 1 → 5 + (1 + 1 + 1) ≤
      LutFbBridge2Env.ash 4 (LutFbBridge2Env.ε (st 8) 1 1 (fun _ => 7)) (j + 1)) ∧
    (∀ t, st 6 (t + 1) ≠ st 6 t → st 6 (t + 1) = st 5 t) ∧
    (∀ t, st 8 (t + 1) ≠ st 8 t → st 8 (t + 1) = st 7 t) :=
  have h := flink_link_env (st_phases 5) (st_phases 7) (st_wire 5) (st_wire 7) (R := 4) (loA := 1)
    (loB := 1) (by decide) (fun j hj => absurd hj (by omega))
    (fun j hj => by
      have : j = 0 := by omega
      subst this; exact ⟨hj, by rw [st_eps 5]; decide⟩)
    (fun h => absurd h (by decide)) (by decide) (by decide)
  ⟨h.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

end llw

end Formal.Cells.FiniteRunsWit
