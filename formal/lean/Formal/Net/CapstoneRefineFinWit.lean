import Formal.Net.CapstoneRefineNet
import Formal.Net.CapstoneRefineWit

/-!
# Audit P12a row 18: `TxWin` is satisfiable on a channel offered FINITELY often

Problem statement. The audit (P12a, `txwin_inf`) showed that the old `TxWin` demanded a `k`-th
transaction for EVERY `k`, so no channel of a terminating run (finitely many offers, e.g. any
single-start gcd computation) could carry a tcheck DAG/cert certificate: `BCert` collapsed to
`exempt` (assumed bundling). `TxWin` is now indexed by the transactions that occur
(`HasOff`). This file shows the repaired hypothesis is not vacuous on finite channels:

* `wF` is a physical channel with EXACTLY two transactions (offers at 5 and 25), idle from 32
  on forever (`wF_quiet`, `wF_hasOff_iff`: offer `k` exists iff `k < 2`);
* its bus carries different values in the two transactions (0, then 1);
* `wFX : TxWin wF wsig [1] _` is built over the same netlist/runs as `Wit.wX` (data arc
  [1,2], request arc [5,6], tcheck DAG verdict `wcheck` by `decide`);
* `wF_bcert_dag`: the certificate is the `dag` constructor (a real tcheck row), not `exempt`;
* `fin_witness`: `held_of_bcert` and `sampled_eq_zd_dag` then give Ops `Held` and the
  zero-delay value of every in-transaction sample on this finite channel.

What it does NOT show: that any channel of a real gcd_hw run meets `TxWin` (H_TXWIN is still
a hypothesis), nor that the capstone theorems phys4/phys5 now have a non-ghost witness. It
shows only that the obstruction found by the audit (finitely many offers ⇒ no tcheck
certificate) is gone. Toy netlist, two hand-made transactions.
-/

namespace Formal.Net.CapstoneRefine.FinWit
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Timing Formal.Net.CapstoneRefine
open Formal.Net.CapstoneRefine.Wit

/-- Two transactions, then idle forever: req high on [6,9] and [26,29], ack on [8,11] and
[28,31]; the bus is run 0 before 20 and run 1 (shifted by 20) from 20 on. -/
def wF : Chan where
  req := fun u => decide ((6 ≤ u ∧ u ≤ 9) ∨ (26 ≤ u ∧ u ≤ 29))
  ack := fun u => decide ((8 ≤ u ∧ u ≤ 11) ∨ (28 ≤ u ∧ u ≤ 31))
  dat := fun u => if u < 20 then bv 1 (fun j => wsig 0 ([1].getD j 0) u)
    else bv 1 (fun j => wsig 1 ([1].getD j 0) (u - 20))

theorem riseB_wF (u : Nat) : riseB wF.req u = (u == 5 || u == 25) := by
  simp only [riseB, wF]
  by_cases h5 : u = 5
  · subst h5; decide
  by_cases h25 : u = 25
  · subst h25; decide
  have hb : (u == 5 || u == 25) = false := by simp [h5, h25]
  rw [hb]
  cases h : decide ((6 ≤ u ∧ u ≤ 9) ∨ (26 ≤ u ∧ u ≤ 29)) with
  | true => simp
  | false =>
    have h' : ¬((6 ≤ u ∧ u ≤ 9) ∨ (26 ≤ u ∧ u ≤ 29)) := by simpa using h
    simp
    omega

theorem cnt_wF (u : Nat) :
    cnt (riseB wF.req) u = (if 5 < u then 1 else 0) + (if 25 < u then 1 else 0) := by
  induction u with
  | zero => rfl
  | succ u ih =>
    simp only [cnt, ih, riseB_wF]
    by_cases h5 : u = 5
    · subst h5; decide
    by_cases h25 : u = 25
    · subst h25; decide
    have hb : (u == 5 || u == 25) = false := by simp [h5, h25]
    rw [hb]
    simp only [show (5 < u + 1) = (5 < u) from propext (by omega),
      show (25 < u + 1) = (25 < u) from propext (by omega), Bool.false_eq_true, ite_false,
      Nat.add_zero]

/-- Offer `k` occurs iff `k < 2`: the channel is offered exactly twice. -/
theorem wF_hasOff_iff (k : Nat) : HasOff wF k ↔ k < 2 := by
  constructor
  · rintro ⟨r, h1, h2⟩
    rw [riseB_wF] at h1
    rw [cnt_wF] at h2
    have : r = 5 ∨ r = 25 := by simpa using h1
    rcases this with h | h <;> subst h <;> simp at h2 <;> omega
  · intro hk
    rcases (show k = 0 ∨ k = 1 by omega) with h | h <;> subst h
    · exact ⟨5, by rw [riseB_wF]; rfl, by rw [cnt_wF]; rfl⟩
    · exact ⟨25, by rw [riseB_wF]; rfl, by rw [cnt_wF]; rfl⟩

/-- From 32 on the channel is idle forever (finitely many events). -/
theorem wF_quiet (u : Nat) (hu : 32 ≤ u) : wF.req u = false ∧ wF.ack u = false := by
  simp only [wF, decide_eq_false_iff_not]; omega

theorem wF_offAt {k r : Nat} (ho : OffAt wF k r) : (k = 0 ∧ r = 5) ∨ (k = 1 ∧ r = 25) := by
  obtain ⟨h1, h2⟩ := ho
  rw [riseB_wF] at h1
  rw [cnt_wF] at h2
  have : r = 5 ∨ r = 25 := by simpa using h1
  rcases this with h | h <;> subst h <;> simp at h2 <;> omega

def wFX : TxWin wF wsig [1] (fun k v => changes (wsig k 2) v) where
  τ k := 20 * k
  idle k hk := by
    have := (wF_hasOff_iff k).1 hk
    rcases (show k = 0 ∨ k = 1 by omega) with h | h <;> subst h <;> decide
  count k hk := by
    have := (wF_hasOff_iff k).1 hk
    rcases (show k = 0 ∨ k = 1 by omega) with h | h <;> subst h <;> rw [cnt_wF] <;> rfl
  reqIn k r ho := by
    rcases wF_offAt ho with ⟨hk, hr⟩ | ⟨hk, hr⟩ <;> subst hk <;> subst hr <;>
      simp [changes, wsig]
  win k u hk h1 h2 := by
    have hk2 := (wF_hasOff_iff k).1 hk
    rcases (show k = 0 ∨ k = 1 by omega) with h | h <;> subst h
    · have hu : u < 20 := h2 ((wF_hasOff_iff 1).2 (by decide))
      show (if u < 20 then _ else _) = _
      rw [if_pos hu, Nat.sub_zero]; rfl
    · show (if u < 20 then _ else _) = _
      rw [if_neg (by omega)]; rfl

theorem wF_init : Init wF := ⟨rfl, rfl⟩

theorem wF_recv (u : Nat) : RecvStep wF u := by
  simp only [RecvStep, wF, ne_eq, decide_eq_decide]
  intro h; omega

/-- The certificate of the finite channel is a real tcheck DAG row, not `exempt`. -/
theorem wF_bcert_dag : BCert wF := BCert.dag wnet 2 [1] 0 wsig wnet_wf wcheck wrun wFX

/-- **Non-vacuity of the repaired H_TXWIN on a finite channel.** `wF` is offered exactly
twice and is idle forever after 32; its DAG certificate yields Ops `Held`, every
in-transaction sample equals the zero-delay value (`0` in transaction 0, `1` in transaction
1), and the two transactions do carry different values. -/
theorem fin_witness :
    (∀ k, HasOff wF k ↔ k < 2) ∧ (∀ u, 32 ≤ u → wF.req u = false ∧ wF.ack u = false) ∧
    Held wF ∧
    (∀ k r t, OffAt wF k r → r < t → (∀ s, r < s → s ≤ t → inTx wF s = true) →
      wF.dat t = if bk k then 1 else 0) ∧
    wF.dat 6 = 0 ∧ wF.dat 26 = 1 := by
  refine ⟨wF_hasOff_iff, wF_quiet, held_of_bcert wF_bcert_dag wF_init wF_recv, ?_,
    by decide, by decide⟩
  intro k r t ho hrt hb
  rw [sampled_eq_zd_dag wnet_wf wcheck wrun wFX ho hrt hb, w_zdBus]

end Formal.Net.CapstoneRefine.FinWit
