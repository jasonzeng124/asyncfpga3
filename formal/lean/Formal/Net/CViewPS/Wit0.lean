import Formal.Net.CViewPS.W000
import Formal.Net.CViewPS.W001
import Formal.Net.CViewPS.W002
import Formal.Net.CViewPS.W003
import Formal.Net.CViewPS.W004
import Formal.Net.CViewPS.W005
import Formal.Net.CViewPS.W006
import Formal.Net.CViewPS.W007
import Formal.Net.CViewPS.W008
import Formal.Net.CViewPS.W009
import Formal.Net.CViewPS.W010
import Formal.Net.CViewPS.W011
import Formal.Net.CViewPS.W012
import Formal.Net.CViewPS.W013
import Formal.Net.CViewPS.W014
import Formal.Net.CViewPS.W015
import Formal.Net.CViewPS.W016
import Formal.Net.CViewPS.W017
import Formal.Net.CViewPS.W018
import Formal.Net.CViewPS.W019
import Formal.Net.CViewPS.W020
import Formal.Net.CViewPS.W021
import Formal.Net.CViewPS.W022
import Formal.Net.CViewPS.W023
import Formal.Net.CViewPS.W024
import Formal.Net.CViewPS.W025
import Formal.Net.CViewPS.W026
import Formal.Net.CViewPS.W027
import Formal.Net.CViewPS.W028
import Formal.Net.CViewPS.W029
import Formal.Net.CViewPS.W030
import Formal.Net.CViewPS.W031
import Formal.Net.CViewPS.W032
import Formal.Net.CViewPS.W033
import Formal.Net.CViewPS.W034
import Formal.Net.CViewPS.W035
import Formal.Net.CViewPS.W036
import Formal.Net.CViewPS.W037
import Formal.Net.CViewPS.W038
import Formal.Net.CViewPS.W039
import Formal.Net.CViewPS.W040
import Formal.Net.CViewPS.W041
import Formal.Net.CViewPS.W042
import Formal.Net.CViewPS.W043
import Formal.Net.CViewPS.W044
import Formal.Net.CViewPS.W045
import Formal.Net.CViewPS.W046
import Formal.Net.CViewPS.W047
import Formal.Net.CViewPS.W048
import Formal.Net.CViewPS.W049
import Formal.Net.CViewPS.W050
import Formal.Net.CViewPS.W051
import Formal.Net.CViewPS.W052
import Formal.Net.CViewPS.W053
import Formal.Net.CViewPS.W054
import Formal.Net.CViewPS.W055
import Formal.Net.CViewPS.W056
import Formal.Net.CViewPS.W057
import Formal.Net.CViewPS.W058
import Formal.Net.CViewPS.W059
import Formal.Net.CViewPS.W060
import Formal.Net.CViewPS.W061
import Formal.Net.CViewPS.W062
import Formal.Net.CViewPS.W063
import Formal.Net.CViewPS.W064
import Formal.Net.CViewPS.W065
import Formal.Net.CViewPS.W066
import Formal.Net.CViewPS.W067
import Formal.Net.CViewPS.W068
import Formal.Net.CViewPS.W069
import Formal.Net.CViewPS.W070
import Formal.Net.CViewPS.W071
import Formal.Net.CViewPS.W072
import Formal.Net.CViewPS.W073
import Formal.Net.CViewPS.W074
import Formal.Net.CViewPS.Idle0P1

/-!
# The zero-pair theorems are not vacuous: a witness behaviour of THE target (shard C)

**Problem, plainly.** `correct_n0_p1` says every behaviour of THE theorem's circuit with an idle
environment is correct. If no such behaviour existed, it would say nothing. **Proved**
(`witness_n0`): for every `su`, `Δo`, `va`, `vb` there is a behaviour `xW` with
`Behaves p1 (circuit DecodedPS.net DecodedPS.boundary) xW` and
`Env xW DecodedPS.boundary 400000 su Δo (some 0) va vb` (400,000 ps ≥ the 353,248 ps that
`correct_n0_p1` needs), so `Correct` holds of it (`witness_n0_correct`). The witness: a power-up
state consistent with every gate under reset (62,788 nodes high), reset released at 400 ns, every
pin read at its FAST_MIN; 3,604 nodes switch once, everything else is constant
(formal/tools/cview/witn0.py, untrusted; every gate is kernel-checked at its breakpoints, `W*.lean`).
-/

namespace Formal.Net.CViewPS
open Formal.Target Formal.Target.DecodedPS Formal.Timing.SpecSettle Formal.Timing.SpecChain
  Formal.Timing.ChunkCM

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem w_all : ∀ c, c < cs.length → (cs.getD c []).all (fun g => !keepPS g || gateW encW g) = true := by
  intro c hc
  rw [cs_len] at hc
  match c, hc with
  | 0, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w000_ok
  | 1, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w001_ok
  | 2, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w002_ok
  | 3, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w003_ok
  | 4, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w004_ok
  | 5, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w005_ok
  | 6, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w006_ok
  | 7, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w007_ok
  | 8, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w008_ok
  | 9, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w009_ok
  | 10, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w010_ok
  | 11, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w011_ok
  | 12, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w012_ok
  | 13, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w013_ok
  | 14, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w014_ok
  | 15, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w015_ok
  | 16, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w016_ok
  | 17, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w017_ok
  | 18, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w018_ok
  | 19, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w019_ok
  | 20, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w020_ok
  | 21, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w021_ok
  | 22, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w022_ok
  | 23, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w023_ok
  | 24, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w024_ok
  | 25, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w025_ok
  | 26, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w026_ok
  | 27, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w027_ok
  | 28, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w028_ok
  | 29, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w029_ok
  | 30, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w030_ok
  | 31, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w031_ok
  | 32, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w032_ok
  | 33, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w033_ok
  | 34, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w034_ok
  | 35, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w035_ok
  | 36, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w036_ok
  | 37, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w037_ok
  | 38, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w038_ok
  | 39, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w039_ok
  | 40, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w040_ok
  | 41, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w041_ok
  | 42, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w042_ok
  | 43, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w043_ok
  | 44, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w044_ok
  | 45, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w045_ok
  | 46, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w046_ok
  | 47, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w047_ok
  | 48, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w048_ok
  | 49, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w049_ok
  | 50, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w050_ok
  | 51, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w051_ok
  | 52, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w052_ok
  | 53, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w053_ok
  | 54, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w054_ok
  | 55, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w055_ok
  | 56, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w056_ok
  | 57, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w057_ok
  | 58, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w058_ok
  | 59, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w059_ok
  | 60, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w060_ok
  | 61, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w061_ok
  | 62, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w062_ok
  | 63, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w063_ok
  | 64, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w064_ok
  | 65, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w065_ok
  | 66, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w066_ok
  | 67, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w067_ok
  | 68, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w068_ok
  | 69, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w069_ok
  | 70, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w070_ok
  | 71, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w071_ok
  | 72, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w072_ok
  | 73, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w073_ok
  | 74, _ => simp only [cs, List.getD_cons_succ, List.getD_cons_zero]; exact w074_ok
  | n + 75, h => exact absurd h (by omega)

theorem smax_le_fold : ∀ (l : List Arc) (e : Arc), e ∈ l → e.smax ≤ (l.map fun e => e.smax).foldr max 0
  | [], _, h => by simp at h
  | a :: l, e, h => by
    simp only [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (smax_le_fold l e h) (le_max_right _ _)

/-- The witness behaviour. -/
def xW : Beh := fun n => sig1 (encW n)

theorem behaves_w : Behaves p1 (circuit net boundary) xW := by
  refine ⟨0, le_refl _, zero_le_one, fun g hg => ?_⟩
  have hwf := circuit_wf (N := net) (B := boundary) net_wf
  have hmem := hg
  rw [circuit_eq, List.mem_filter, List.mem_flatten] at hmem
  obtain ⟨⟨gc, hgc, hgg⟩, hk⟩ := hmem
  obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem hgc
  have hall := w_all c hc
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc, Option.getD_some] at hall
  have := List.all_eq_true.mp hall g hgg
  simp only [hk, Bool.not_true, Bool.false_or] at this
  apply gateOK_of_gateW _ g
  · intro i _
    have := hwf.1 g hg
    by_cases hi : i < g.arcs.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
      exact (this.2.2.2.2.2 _ (List.getElem_mem hi)).1
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; exact Nat.le_refl _
  · intro i hi
    have := hwf.1 g hg
    by_cases hia : i < g.arcs.length
    · have ha := this.2.2.2.2.2 _ (List.getElem_mem hia)
      have hle : (g.arcs[i]).smax ≤ startN g := smax_le_fold _ _ (List.getElem_mem hia)
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hia, Option.getD_some]
      omega
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; exact Nat.zero_le _
  · exact this

theorem w_vals : encW 186905 = some (2 * (400000 + 1) + 1) ∧ encW 186985 = none ∧ encW 104576 = none ∧
    encW 104695 = none ∧ encW 147972 = none ∧ encW 160957 = none ∧ encW 154859 = none ∧ encW 104477 = none := by
  decide +kernel

theorem w_false {n : Nat} (h : encW n = none) (t : Nat) : xW n t = false := by
  simp [xW, h, sig1]

theorem env_w (su Δo : Nat) (va vb : Nat → Nat) : Env xW boundary 400000 su Δo (some 0) va vb := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, -⟩ := bnd_facts
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := w_vals
  have rq : ∀ t, xW 186985 t = false := w_false e2
  have ein : ∀ (ch : InCh) (vals : Nat → Nat), ch.req = 186985 → (∀ t, xW ch.ack t = false) →
      EnvIn xW ch 400000 su (some 0) vals := by
    intro ch vals hq ha
    refine ⟨fun t _ => by rw [hq]; exact rq t, fun t _ h => ?_, fun t _ _ hc => ?_, fun t _ h => ?_,
      fun t _ _ h => ?_, fun t _ h => ?_⟩
    · rw [hq, rq, rq] at h; exact absurd rfl h
    · rw [hq, rq] at hc; simp [Offered] at hc
    · rw [hq, rq] at h; cases h
    · rw [hq, rq] at h; cases h
    · rw [hq, rq, ha] at h; simp at h
  have eout : ∀ (ch : OutCh), (∀ t, xW ch.req t = false) → (∀ t, xW ch.ack t = false) →
      EnvOut xW ch 400000 Δo := by
    intro ch hr ha
    refine ⟨fun t _ => ha t, fun t _ h => ?_, fun t _ h => ?_, fun t _ _ h => ?_⟩
    · rw [ha, ha] at h; exact absurd rfl h
    · rw [ha, hr] at h; exact absurd rfl h
    · rw [ha] at h; cases h
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun k hk => by simp [Offered] at hk, ein _ _ b2 (by rw [b5]; exact w_false e3),
    ein _ _ b3 (by rw [b6]; exact w_false e4), ein _ _ b4 (by rw [b7]; exact w_false e5),
    eout _ (by rw [b8]; exact w_false e6) (by rw [b9]; exact w_false e7),
    eout _ (by rw [b10]; exact rq) (by rw [b11]; exact w_false e8)⟩
  · rw [b1]; simp only [xW, e1, sig1]; simp; omega
  · rw [b1]; simp only [xW, e1, sig1]; simp; omega

/-- **The zero-pair hypotheses are satisfiable on THE target.** -/
theorem witness_n0 (su Δo : Nat) (va vb : Nat → Nat) :
    ∃ x : Beh, Behaves p1 (circuit net boundary) x ∧ Env x boundary 400000 su Δo (some 0) va vb :=
  ⟨xW, behaves_w, env_w su Δo va vb⟩

theorem witness_n0_correct (su Δo : Nat) (va vb : Nat → Nat) :
    Correct xW boundary 400000 Δo (some 0) va vb :=
  correct_n0_p1 400000 su Δo (by decide) xW va vb behaves_w (env_w su Δo va vb)

end Formal.Net.CViewPS
