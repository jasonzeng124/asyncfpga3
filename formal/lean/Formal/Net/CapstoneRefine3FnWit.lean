import Formal.Net.CapstoneRefine3Fn
import Formal.Net.CapstoneRefineWit

/-!
# Probe C-8x3 (c): non-vacuity of `joinB_of_phys`

A one-input join whose output `wQ` is C-8x's witness channel slowed down so that a join can
produce it (`req` high on `6..10`, `ack` on `8..12` of each 20 ps period; C-8x's `wP` lowers
`req` 2 ticks after `ack↑`, too early for a join), with C-8x's netlist runs `wrun` (data settles
at 3, request at 6) as its tcheck obligation (DAG row `wcheck`). Input `wI`: `req` on `5..9`,
`ack` on `9..13`, bus = the token bit `bk k` for the whole period.

* `wjoin_hyps`: every hypothesis of `joinB_of_phys` holds (handshake half, protocol on both
  channels, input bundled, tcheck row + H_TXWIN, H_FN, H_LAUNCH) with `g = head`;
* `wjoin_field`: so the relaxed join field holds on `wQ` (derived, not assumed);
* `wjoin_old_fails`: the OLD all-time join field does NOT hold on `wQ` (at `t = 20` the output is
  idle and still shows the previous run's settled data, 0, while the input already carries 1).
-/

namespace Formal.Net.CapstoneRefine.Wit
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Timing Formal.Net.CapstoneRefine
open Formal.Net.OpsBusy

/-- The output channel: period 20 ps, req on `6..10`, ack on `8..12`. -/
def wQ : Chan where
  req := fun u => decide (6 ≤ u % 20 ∧ u % 20 ≤ 10)
  ack := fun u => decide (8 ≤ u % 20 ∧ u % 20 ≤ 12)
  dat := fun u => bv 1 (fun j => wsig (u / 20) ([1].getD j 0) (u % 20))

/-- The input channel: req on `5..9`, ack on `9..13`, bus = token bit of the period. -/
def wI : Chan where
  req := fun u => decide (5 ≤ u % 20 ∧ u % 20 ≤ 9)
  ack := fun u => decide (9 ≤ u % 20 ∧ u % 20 ≤ 13)
  dat := fun u => if bk (u / 20) then 1 else 0

theorem mod_succ (u : Nat) : (u + 1) % 20 = (u % 20 + 1) % 20 := by omega

theorem riseB_wQ (u : Nat) : riseB wQ.req u = (u % 20 == 5) := by
  have key : ∀ m, m < 20 →
      (!(decide (6 ≤ m ∧ m ≤ 10)) && decide (6 ≤ (m + 1) % 20 ∧ (m + 1) % 20 ≤ 10)) = (m == 5) := by
    decide
  simp only [riseB, wQ, mod_succ u]
  exact key _ (Nat.mod_lt _ (by decide))

theorem cnt_wQ (u : Nat) : cnt (riseB wQ.req) u = u / 20 + (if 5 < u % 20 then 1 else 0) := by
  induction u with
  | zero => rfl
  | succ u ih =>
    simp only [cnt, ih, riseB_wQ, beq_iff_eq]
    have hm := Nat.mod_lt u (show 20 > 0 by decide)
    have hd : (u + 1) / 20 = u / 20 + (if u % 20 = 19 then 1 else 0) := by
      by_cases h : u % 20 = 19
      · rw [if_pos h]; omega
      · rw [if_neg h]; omega
    have key : ∀ m, m < 20 → (if 5 < m then 1 else 0) + (if m = 5 then 1 else 0) =
        (if m = 19 then 1 else 0) + (if 5 < (m + 1) % 20 then 1 else 0) := by decide
    rw [hd, mod_succ u]
    have := key _ hm
    omega

theorem hasOff_wQ (k : Nat) : HasOff wQ k :=
  ⟨20 * k + 5, by rw [riseB_wQ]; simp [Nat.add_mod], by rw [cnt_wQ]; simp; omega⟩

def wXQ : TxWin wQ wsig [1] (fun k v => changes (wsig k 2) v) where
  τ k := 20 * k
  idle k _ := by simp [wQ, Nat.mul_mod_right]
  count k _ := by rw [cnt_wQ]; simp [Nat.mul_mod_right]
  reqIn k r ho := by
    have h1 := ho.1
    rw [riseB_wQ] at h1
    have h5 : r % 20 = 5 := by simpa using h1
    have h2 := ho.2
    rw [cnt_wQ, if_neg (by omega)] at h2
    rw [show r - 20 * k = 5 by omega]
    simp [changes, wsig]
  win k u _ h1 h2 := by
    have h2 := h2 (hasOff_wQ (k + 1))
    show bv 1 (fun j => wsig (u / 20) ([1].getD j 0) (u % 20)) = _
    rw [show u / 20 = k by omega, show u % 20 = u - 20 * k by omega]; rfl

theorem wQ_proto : Protocol wQ := by
  refine ⟨⟨rfl, rfl⟩, fun u => ⟨?_, ?_⟩⟩
  · have key : ∀ m, m < 20 →
        (decide (6 ≤ (m + 1) % 20 ∧ (m + 1) % 20 ≤ 10) ≠ decide (6 ≤ m ∧ m ≤ 10) →
          decide (6 ≤ m ∧ m ≤ 10) = decide (8 ≤ m ∧ m ≤ 12)) := by decide
    simp only [SendStep, wQ, mod_succ u]
    exact key _ (Nat.mod_lt _ (by decide))
  · have key : ∀ m, m < 20 →
        (decide (8 ≤ (m + 1) % 20 ∧ (m + 1) % 20 ≤ 12) ≠ decide (8 ≤ m ∧ m ≤ 12) →
          decide (8 ≤ m ∧ m ≤ 12) ≠ decide (6 ≤ m ∧ m ≤ 10)) := by decide
    simp only [RecvStep, wQ, mod_succ u]
    exact key _ (Nat.mod_lt _ (by decide))

theorem wI_proto : Protocol wI := by
  refine ⟨⟨rfl, rfl⟩, fun u => ⟨?_, ?_⟩⟩
  · have key : ∀ m, m < 20 →
        (decide (5 ≤ (m + 1) % 20 ∧ (m + 1) % 20 ≤ 9) ≠ decide (5 ≤ m ∧ m ≤ 9) →
          decide (5 ≤ m ∧ m ≤ 9) = decide (9 ≤ m ∧ m ≤ 13)) := by decide
    simp only [SendStep, wI, mod_succ u]
    exact key _ (Nat.mod_lt _ (by decide))
  · have key : ∀ m, m < 20 →
        (decide (9 ≤ (m + 1) % 20 ∧ (m + 1) % 20 ≤ 13) ≠ decide (9 ≤ m ∧ m ≤ 13) →
          decide (9 ≤ m ∧ m ≤ 13) ≠ decide (5 ≤ m ∧ m ≤ 9)) := by decide
    simp only [RecvStep, wI, mod_succ u]
    exact key _ (Nat.mod_lt _ (by decide))

theorem wI_held : Held wI := by
  intro u h0 h1
  have key : ∀ m, m < 20 → (decide (5 ≤ m ∧ m ≤ 9) || decide (9 ≤ m ∧ m ≤ 13)) = true →
      m ≠ 19 := by decide
  have hm := key _ (Nat.mod_lt u (by decide)) h0
  show (if bk ((u + 1) / 20) then 1 else 0) = (if bk (u / 20) then 1 else 0)
  rw [show (u + 1) / 20 = u / 20 by omega]

theorem wjoin_H : JoinH [wI] wQ := by
  refine ⟨by simp, ?_, ?_, rfl, ?_⟩
  · intro t hne i hi
    rw [List.mem_singleton.1 hi]
    have key : ∀ m, m < 20 →
        (decide (6 ≤ (m + 1) % 20 ∧ (m + 1) % 20 ≤ 10) ≠ decide (6 ≤ m ∧ m ≤ 10) →
          decide (5 ≤ m ∧ m ≤ 9) = decide (6 ≤ (m + 1) % 20 ∧ (m + 1) % 20 ≤ 10)) := by decide
    simp only [wQ, wI, mod_succ t] at hne ⊢
    exact key _ (Nat.mod_lt _ (by decide)) hne
  · intro i hi t hne
    rw [List.mem_singleton.1 hi] at hne ⊢
    have key : ∀ m, m < 20 →
        (decide (9 ≤ (m + 1) % 20 ∧ (m + 1) % 20 ≤ 13) ≠ decide (9 ≤ m ∧ m ≤ 13) →
          decide (9 ≤ (m + 1) % 20 ∧ (m + 1) % 20 ≤ 13) = decide (8 ≤ m ∧ m ≤ 12)) := by decide
    simp only [wQ, wI, mod_succ t] at hne ⊢
    exact key _ (Nat.mod_lt _ (by decide)) hne
  · intro i hi; rw [List.mem_singleton.1 hi]; rfl

/-- The cell function: a one-input join passes its input. -/
def ghead (l : List Nat) : Nat := l.headD 0

def wvin (k : Nat) : List Nat := [if bk k then 1 else 0]

theorem w_fn (k : Nat) : zdBus wrun [1] k = ghead (wvin k) := by
  rw [w_zdBus]; rfl

theorem w_launch (k r : Nat) (ho : OffAt wQ k r) : wvin k = [wI].map (fun i => i.dat (r + 1)) := by
  have h1 := ho.1
  rw [riseB_wQ] at h1
  have h5 : r % 20 = 5 := by simpa using h1
  have h2 := ho.2
  rw [cnt_wQ, if_neg (by omega)] at h2
  show [if bk k then 1 else 0] = [if bk ((r + 1) / 20) then 1 else 0]
  rw [show (r + 1) / 20 = k by omega]

/-- **Joint witness for `joinB_of_phys`**: all its hypotheses hold on (`wI`, `wQ`). -/
theorem wjoin_hyps :
    JoinH [wI] wQ ∧ Protocol wQ ∧ (∀ i ∈ [wI], Protocol i) ∧ (∀ i ∈ [wI], Held i) ∧
    wnet.WF ∧ checkArr wnet 2 [1] 0 = true ∧
    (∀ k, zdBus wrun [1] k = ghead (wvin k)) ∧
    (∀ k r, OffAt wQ k r → wvin k = [wI].map (fun i => i.dat (r + 1))) :=
  ⟨wjoin_H, wQ_proto, fun i hi => by rw [List.mem_singleton.1 hi]; exact wI_proto,
   fun i hi => by rw [List.mem_singleton.1 hi]; exact wI_held, wnet_wf, wcheck, w_fn, w_launch⟩

/-- The relaxed join field on `wQ`, derived from the physical data. -/
theorem wjoin_field : JoinB ghead [wI] wQ :=
  joinB_of_phys wjoin_H wQ_proto (fun i hi => by rw [List.mem_singleton.1 hi]; exact wI_proto)
    (fun i hi => by rw [List.mem_singleton.1 hi]; exact wI_held) wnet_wf wrun wXQ
    (sep_dag wnet_wf wcheck wrun) wvin w_fn w_launch

/-- The old (all-time) join field fails on `wQ`: the relaxation is used. -/
theorem wjoin_old_fails : ¬ ∀ t, wQ.dat t = ghead ([wI].map (fun i => i.dat t)) := by
  intro h
  have := h 20
  revert this
  decide

/-- `wQ` carries a tcheck DAG certificate (the `dag` constructor of `BCert`, exercised). -/
theorem wQ_bcert : BCert wQ := BCert.dag wnet 2 [1] 0 wsig wnet_wf wcheck wrun wXQ

end Formal.Net.CapstoneRefine.Wit
