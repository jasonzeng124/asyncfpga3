import Formal.Net.CViewPS.IslandChk0
import Formal.Net.CViewPS.IslandChk1
import Formal.Net.CViewPS.IslandChk2
import Formal.Net.CViewPS.IslandChk3
import Formal.Net.CViewPS.IslandChk4
import Formal.Net.CViewPS.IslandChk5
import Formal.Net.CViewPS.IslandChk6
import Formal.Net.CViewPS.IslandChk7

/-!
# THE target stays idle when no pair is offered (shard C)

**Problem, plainly.** With no pair ever offered, must the circuit's handshake outputs stay low
for ever, whatever its 4,185 unreset data latches and 9 arbiter states hold, and whatever
delays (in Adm)? **Proved** (`island_PS`): in every behaviour of THE theorem's circuit (sane
`p`), at its corner: if reset is high on `[0, R)`, the shared input request (node 186985) and
`pend.ack` (104477) are low at all times, every island member's start and every storage member's
reset-pin arrival is at most `A`, every pin delay of a member is in `[1, M]` ps on its forcing
pins and at most `M` on all its pins, and `A + 87·M ≤ R - 1`, then every one of the 414 island
members is low from `R - 1 - M` on, for ever. The members include `a.ack` (104576), `b.ack`
(104695), `start.ack` (147972) and `out0.req` (160957). Kernel-checked per member: a logic node of
the circuit; its forcing pins' sources are members or the two environment nodes; those pins at 0
force its INIT to 0 (`ForcesP`), whatever its other pins (data latches, arbiter states) read;
combinational members' member sources have smaller rank (≤ 85); storage members are in
`resetList` with reset value 0.

**Not shown.** The delay hypotheses for a concrete `p` (bounds on 414 gates' composite arcs);
that this is `Correct` for `n = some 0` (assembled in `Idle0.lean`).
-/

namespace Formal.Net.CViewPS
open Formal.Target Formal.Target.DecodedPS Formal.Timing.SpecSettle Formal.Timing.SpecChain
  Formal.Timing.SpecChainM Formal.Timing.ChunkCM Formal.Timing.Huffman Formal.Timing.SpecLoop
  Formal.Timing.Island

theorem island_ok : islandList.all entryOK = true := by
  simp only [islandList, List.all_append, isl0_ok, isl1_ok, isl2_ok, isl3_ok, isl4_ok, isl5_ok, isl6_ok, isl7_ok, Bool.and_self]

theorem entry_of_mem {w : Nat} (h : memI w = true) : ∃ e ∈ islandList, e.1 = w ∧ entryOK e = true := by
  obtain ⟨e, he, hw⟩ := List.any_eq_true.mp h
  exact ⟨e, he, by simpa using hw, List.all_eq_true.mp island_ok e he⟩

theorem entry_facts {w : Nat} (h : memI w = true) :
    logicPS w ∧ (∀ j ∈ psI w, j < (gAt cs 2500 w).k ∧ (memI (srcPS w j) = true ∨ envI (srcPS w j) = true)) ∧
    ForcesP (gAt cs 2500 w).k (gAt cs 2500 w).init (asgOf srcPS valI w (psI w)) false = true ∧
    (storI w = true → ∃ r ∈ resetList, r.1 = w ∧ r.2.2 = false) ∧
    (storI w = false → (rkPS w).getD 0 ≤ 85 ∧ ∀ j ∈ psI w, memI (srcPS w j) = true → storI (srcPS w j) = false →
      (rkPS (srcPS w j)).getD 0 < (rkPS w).getD 0) := by
  obtain ⟨e, he, rfl, hok⟩ := entry_of_mem h
  simp only [entryOK, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨⟨hl, -⟩, hps⟩, hall⟩, hF⟩, hlast⟩ := hok
  rw [← hps] at hall hF hlast
  refine ⟨logicPS_of_B hl, fun j hj => ?_, hF, fun hs => ?_, fun hs => ?_⟩
  · have := List.all_eq_true.mp hall j hj
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at this
    exact this
  · rw [hs] at hlast; simp only [ite_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hlast
    obtain ⟨r, hr, h1, h2⟩ := hlast; exact ⟨r, hr, h1, h2⟩
  · rw [hs] at hlast
    simp only [Bool.false_eq_true, ite_false, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff] at hlast
    refine ⟨hlast.1, fun j hj hm hs' => ?_⟩
    rcases hlast.2 j hj with (h | h) | h
    · rw [hm] at h; cases h
    · simp at h; rw [hs'] at h; cases h
    · exact h

/-- **THE target stays idle.** -/
theorem island_PS {p : DelayPar} (hp : Sane p) {x : Beh} (hb : Behaves p (circuit net boundary) x) :
    ∃ c : ℚ, 0 ≤ c ∧ c ≤ 1 ∧ ∀ (R M A : Nat),
      (∀ t, t < R → x rstPS t = true) → 0 < R →
      (∀ t, x 186985 t = false) → (∀ t, x 104477 t = false) →
      (∀ w, memI w = true → startPS p w ≤ A) →
      (∀ w, memI w = true → ∀ i, i < (gAt cs 2500 w).k → sumMax p (arcsPS w i) ≤ M) →
      (∀ w, memI w = true → ∀ j ∈ psI w, 1 ≤ sumMin p (arcsPS w j)) →
      (∀ r ∈ resetList, memI r.1 = true → sumMax p (arcsPS r.1 r.2.1) ≤ A) →
      A + 87 * M ≤ R - 1 →
      ∀ w, memI w = true → ∀ t, R - 1 - M ≤ t → x w t = false := by
  obtain ⟨c, hc0, hc1, hall⟩ := collapsed hp hb
  refine ⟨c, hc0, hc1, fun R M A hR hR0 hreq hpa hS hM hmin hrs hRA => ?_⟩
  have hgate : ∀ w, memI w = true → (gAt cs 2500 w).out = w ∧
      CGateOK p c (gAt cs 2500 w) (srcPS w) (arcsPS w) (startPS p w) x := fun w hw =>
    ⟨gAt_out_logic (entry_facts hw).1, hall _ (mem_view_logic (entry_facts hw).1)⟩
  have hordI : ∀ w, memI w = true → ∀ i, i < (gAt cs 2500 w).k → ArcsOrd (arcsPS w i) :=
    fun w hw => ord_logic (entry_facts hw).1
  have henv : ∀ e, envI e = true → ∀ t, x e t = valI e := by
    intro e he t
    simp only [envI, Bool.or_eq_true, beq_iff_eq] at he
    rcases he with rfl | rfl
    · exact hreq t
    · exact hpa t
  -- storage members during reset
  have hstor : ∀ w, memI w = true → storI w = true → ∀ t, A ≤ t → t ≤ R - 1 → x w t = valI w := by
    intro w hw hs t h1 h2
    obtain ⟨r, hr, h1r, h2r⟩ := (entry_facts hw).2.2.2.1 hs
    have hok2 := List.all_eq_true.mp resetList_ok r hr
    simp only [resetOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok2
    obtain ⟨⟨⟨hl, hj⟩, hsrc⟩, hF⟩ := hok2
    have hwl := logicPS_of_B hl
    have hsA := hS w hw
    have hrA := hrs r hr (by rw [h1r]; exact hw)
    subst h1r
    have k := cgate_force_pin hp hc0 hc1 (ord_logic hwl) (hall _ (mem_view_logic hwl)) hj true r.2.2 hF 0 (R - 1)
      (fun t' _ b => by
        show x (srcPS r.1 r.2.1) t' = true
        rw [hsrc]; exact hR t' (by omega)) t (by dsimp only; simp only [startPS, pcsPS] at hsA; omega)
      (by simp only [arcsPS, pcsPS] at hrA ⊢; omega) (by omega)
    rw [gAt_out_logic hwl, h2r] at k
    exact k
  -- combinational members during reset
  have hcomb := settle_partial hp hc0 hc1 (fun w => memI w = true ∧ storI w = false)
    (fun r => (memI r = true ∧ storI r = true) ∨ envI r = true) (fun w => (rkPS w).getD 0)
    (gAt cs 2500) srcPS arcsPS (startPS p) M A (R - 1) valI psI
    (fun w hw => hgate w hw.1) (fun w hw => hordI w hw.1) (fun w hw => (entry_facts hw.1).2.2.1)
    (by
      intro w hw j hj
      obtain ⟨hjk, hsrc⟩ := (entry_facts hw.1).2.1 j hj
      refine ⟨hjk, ?_⟩
      rcases hsrc with hm | he
      · rcases Bool.eq_false_or_eq_true (storI (srcPS w j)) with hst | hst
        · exact Or.inl (Or.inl ⟨hm, hst⟩)
        · exact Or.inr ⟨⟨hm, hst⟩, ((entry_facts hw.1).2.2.2.2 hw.2).2 j hj hm hst⟩
      · exact Or.inl (Or.inr he))
    (fun w hw => hM w hw.1) (fun w hw => hS w hw.1)
    (by
      intro r hr t h1 h2
      rcases hr with ⟨hm, hs⟩ | he
      · exact hstor r hm hs t h1 h2
      · exact henv r he t)
  -- the island, from R - 1
  have hRM : M ≤ R - 1 := by omega
  apply island_forever hp hc0 hc1 (fun w => memI w = true) (fun e => envI e = true) (gAt cs 2500) srcPS arcsPS
    (startPS p) M (R - 1) hRM valI psI hgate hordI (fun w hw => (entry_facts hw).2.2.1)
    (by
      intro w hw j hj
      obtain ⟨hjk, hsrc⟩ := (entry_facts hw).2.1 j hj
      exact ⟨hjk, hsrc, hmin w hw j hj, hM w hw j hjk⟩)
    (fun w hw => by have := hS w hw; omega)
    (fun e he t _ => henv e he t)
  intro w hw t h1 h2
  rcases Bool.eq_false_or_eq_true (storI w) with hst | hst
  · exact hstor w hw hst t (by omega) h2
  · have hr := ((entry_facts hw).2.2.2.2 hst).1
    have hmul : ((rkPS w).getD 0 + 1) * M ≤ 86 * M := Nat.mul_le_mul_right M (by omega)
    exact hcomb w ⟨hw, hst⟩ t (by omega) h2

end Formal.Net.CViewPS
