import Formal.Target.PlanRPS
import Formal.Target.CertSpec

/-!
# Formal.Target.CertN1 — one pair's episode, from certificate facts to `StepCore` (shard A, 2026-11-10)

**Problem, plainly.** For the one-pair milestone (`PlanRPS.NetCorrectSeqOnN Q (· = some 1)`), what exactly must a
per-pair certificate deliver? `StepCore` asks for value facts on the boundary (four-phase moves, one out0 rise, the
gcd on out0's data, a low boundary and `IslR` at the end). A timed certificate (shard C's `AO.timedA_follows` /
`timedA_live`) delivers count facts: counts form an ideal at every time, each change is enabled at earlier counts, and
everything ends constant.

**Proved** (`stepCore_n1`): for THE target, a behaviour with `Env` offering one pair (`n = some 1`) and a rising
request at `t1 ≥ R` from a low boundary, if a certificate `C` (counts from `t1`) satisfies `EpN1` --
(all of it facts about the behaviour's own event counts on these nodes, which C's `timedA_follows` gives through
the ideal of `cntE` at every time, since boundary nodes are not data nodes)
* the handshake orders, possibly transitive (`CertSpec`): `a.ack`, `b.ack`, `start.ack` against the request
  (acknowledge side), `out0.req` against `out0.ack` and the request against `end.ack` (request side);
* every change of those five nodes enabled at counts no later than the previous instant;
* out0.req changes at most twice and has risen by `T`;
* from `T` on every boundary node and every island member is low;
* the data: from `Δo` after any out0 rise until out0's acknowledge, the out0 bus is gcd of the operands at `t1 + 1`;
-- then the episode `[t1, T + M + 1)` is a `StepCore` ending in `IslR`. With `PlanRPS.the_onN_of_stepR_all`,
such certificates for every behaviour give the one-pair statement.

**Not shown.** That THE target's certificate for a pair has these properties (C's instance), and the
fast-re-request chaining for `n ≥ 2` (notes/A-S6-chaining.md).
-/

namespace Formal.Target.CertN1
open Formal.Target Formal.Target.Assembly Formal.Target.DecodedPS Formal.Net.AO Formal.Net.OccNet.Timed
  Formal.Net.CViewPS Formal.Target.PlanPS Formal.Target.PlanRPS Formal.Target.CertSpec
  Formal.Timing.SpecSettle Formal.Timing.SpecChain Formal.Timing.SpecLoop

/-- What a one-pair certificate must deliver (count facts from `t1`, plus the data and the end state). -/
structure EpN1 (C : Cert Nat) (x : Beh) (t1 T Δo : Nat) : Prop where
  interA : ∀ s, cnt x t1 104576 s ≤ cnt x t1 186985 s ∧ cnt x t1 186985 s ≤ cnt x t1 104576 s + 1
  interB : ∀ s, cnt x t1 104695 s ≤ cnt x t1 186985 s ∧ cnt x t1 186985 s ≤ cnt x t1 104695 s + 1
  interS : ∀ s, cnt x t1 147972 s ≤ cnt x t1 186985 s ∧ cnt x t1 186985 s ≤ cnt x t1 147972 s + 1
  interO : ∀ s, cnt x t1 154859 s ≤ cnt x t1 160957 s ∧ cnt x t1 160957 s ≤ cnt x t1 154859 s + 1
  interP : ∀ s, cnt x t1 104477 s ≤ cnt x t1 186985 s ∧ cnt x t1 186985 s ≤ cnt x t1 104477 s + 1
  ordA : ∀ s k, ∀ alt ∈ C.causes 104576 k, AltIn (fun w => cnt x t1 w s) alt → k < cnt x t1 186985 s
  ordB : ∀ s k, ∀ alt ∈ C.causes 104695 k, AltIn (fun w => cnt x t1 w s) alt → k < cnt x t1 186985 s
  ordS : ∀ s k, ∀ alt ∈ C.causes 147972 k, AltIn (fun w => cnt x t1 w s) alt → k < cnt x t1 186985 s
  ordO : ∀ s k, ∀ alt ∈ C.causes 160957 (k + 1), AltIn (fun w => cnt x t1 w s) alt → k < cnt x t1 154859 s
  ordP : ∀ s k, ∀ alt ∈ C.causes 186985 (k + 1), AltIn (fun w => cnt x t1 w s) alt → k < cnt x t1 104477 s
  en : ∀ v ∈ [104576, 104695, 147972, 160957, 186985], ∀ s, t1 < s → x v s ≠ x v (s - 1) →
    ∃ n : Nat → Nat, (∀ w, n w ≤ cnt x t1 w (s - 1)) ∧ n v = cnt x t1 v (s - 1) ∧ Enabled C n v
  capO : ∀ s, cnt x t1 160957 s ≤ 2
  t1T : t1 ≤ T
  rose : 1 ≤ cnt x t1 160957 T
  endLow : ∀ v ∈ bnodes boundary, ∀ s, T ≤ s → x v s = false
  islEnd : ∀ w, memI w = true → ∀ s, T ≤ s → x w s = false
  data : ∀ t0, t1 ≤ t0 → edge (x 160957) t0 → ∀ t, t0 + 1 + Δo ≤ t →
    (∀ s, t0 + 1 ≤ s → s ≤ t → x 160957 s = true ∧ x 154859 s = false) →
    busVal x boundary.out0.data t = Nat.gcd (busVal x boundary.a.data (t1 + 1)) (busVal x boundary.b.data (t1 + 1))

theorem cnt_succ_change {x : Beh} {t1 u s : Nat} (hs : t1 ≤ s) (h : x u (s + 1) ≠ x u s) :
    cnt x t1 u (s + 1) = cnt x t1 u s + 1 := by
  simp only [cnt]
  rw [if_neg (show ¬ (s + 1 ≤ t1) by omega)]
  simp [h]

theorem cnt_succ_le {x : Beh} {t1 u s : Nat} : cnt x t1 u (s + 1) ≤ cnt x t1 u s + 1 := by
  simp only [cnt]
  split
  · omega
  · split <;> omega

/-- **One pair's episode is a `StepCore`.** -/
theorem stepCore_n1 {p : DelayPar} {R su Δo M A t1 T : Nat} {C : Cert Nat} {x : Beh} {va vb : Nat → Nat}
    (hp : Sane p) (hb : Behaves p (circuit net boundary) x) (hd : IslDelay p M A) (hAR : A ≤ R)
    (he : Env x boundary R su Δo (some 1) va vb) (hR : R ≤ t1) (hlow : Low x boundary t1)
    (hedge : edge (x boundary.a.req) t1) (hc : EpN1 C x t1 T Δo) :
    ∃ t2 t0, StepCore x boundary Δo (IslR p x) t1 t2 t0 := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩ := bnd_facts
  have hl : ∀ v ∈ bnodes boundary, x v t1 = false := hlow
  have l_req : x 186985 t1 = false := by rw [← b2]; exact hl _ (by simp [bnodes])
  have l_a : x 104576 t1 = false := by rw [← b5]; exact hl _ (by simp [bnodes])
  have l_b : x 104695 t1 = false := by rw [← b6]; exact hl _ (by simp [bnodes])
  have l_s : x 147972 t1 = false := by rw [← b7]; exact hl _ (by simp [bnodes])
  have l_o : x 160957 t1 = false := by rw [← b8]; exact hl _ (by simp [bnodes])
  have l_oa : x 154859 t1 = false := by rw [← b9]; exact hl _ (by simp [bnodes])
  have l_pa : x 104477 t1 = false := by rw [← b11]; exact hl _ (by simp [bnodes])
  have en := fun v hv => hc.en v hv
  have mA := ackMoves_of_certT C x t1 186985 104576 l_req l_a hc.interA hc.ordA (en _ (by simp))
  have mB := ackMoves_of_certT C x t1 186985 104695 l_req l_b hc.interB hc.ordB (en _ (by simp))
  have mS := ackMoves_of_certT C x t1 186985 147972 l_req l_s hc.interS hc.ordS (en _ (by simp))
  have mO := reqMoves_of_certT C x t1 160957 154859 l_o l_oa hc.interO hc.ordO (en _ (by simp))
  have mP := reqMoves_of_certT C x t1 186985 104477 l_req l_pa hc.interP hc.ordP (en _ (by simp))
  -- the first out0 rise
  have hex : ∃ s, 1 ≤ cnt x t1 160957 s := ⟨T, hc.rose⟩
  classical
  let s1 := Nat.find hex
  have hs1 : 1 ≤ cnt x t1 160957 s1 := Nat.find_spec hex
  have hs1min : ∀ s, s < s1 → cnt x t1 160957 s = 0 := fun s hs => by
    have := Nat.find_min hex hs; omega
  have hs1T : s1 ≤ T := Nat.find_min' hex hc.rose
  have hs1pos : t1 < s1 := by
    by_contra h
    have := cnt_le_t0 (x := x) (t0 := t1) 160957 s1 (by omega)
    omega
  obtain ⟨t0, ht0⟩ : ∃ t0, s1 = t0 + 1 := ⟨s1 - 1, by omega⟩
  have hc0 : cnt x t1 160957 t0 = 0 := hs1min t0 (by omega)
  have hc1 : cnt x t1 160957 (t0 + 1) = 1 := by
    have := cnt_succ_le (x := x) (t1 := t1) (u := 160957) (s := t0); rw [← ht0] at this ⊢; omega
  have par : ∀ s, t1 ≤ s → x 160957 s = (cnt x t1 160957 s % 2 == 1) :=
    fun s hs => Formal.Net.AO.EnvData.x_par x t1 160957 l_o s hs
  have hedge0 : edge (x 160957) t0 := by
    refine ⟨?_, ?_⟩
    · rw [par t0 (by omega), hc0]; rfl
    · rw [par (t0 + 1) (by omega), hc1]; rfl
  -- reqs rise at most once (one pair offered)
  obtain ⟨-, -, -, hEa, -, -, -, -⟩ := he
  obtain ⟨-, -, -, hoff, -, -⟩ := hEa
  have edge_req_t1 : edge (x 186985) t1 := by rw [← b2]; exact hedge
  have norise : ∀ t, t1 < t → ¬ edge (x 186985) t := by
    intro t ht ⟨h1, h2⟩
    have r1 := rises_edge (x 186985) (le_trans hR (le_refl _)) edge_req_t1
    have r2 := rises_edge (x 186985) (show R ≤ t by omega) ⟨h1, h2⟩
    have r3 := rises_mono (x 186985) R (t1 + 1) t (by omega)
    have := hoff (t + 1) (by omega) (by rw [b2]; exact h2)
    simp only [Offered] at this
    rw [b2] at this
    omega
  refine ⟨T + M + 1, t0, ?_⟩
  refine ⟨by have := hc.t1T; omega, ?_, ?_, ?_, by omega, by omega, by rw [b8]; exact hedge0, ?_, ?_, ?_, ?_⟩
  · intro t h1 h2; rw [b2]; exact norise t h1
  · intro ch hch t h1 h2 hne
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hch
    rcases hch with rfl | rfl | rfl
    · rw [b5] at hne; rw [b5, b2]; exact mA t h1 hne
    · rw [b6] at hne; rw [b6, b3]; exact mB t h1 hne
    · rw [b7] at hne; rw [b7, b4]; exact mS t h1 hne
  · intro ch hch t h1 h2 hne
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hch
    rcases hch with rfl | rfl
    · rw [b8] at hne; rw [b8, b9]; exact mO t h1 hne
    · rw [b10] at hne; rw [b10, b11]; exact mP t h1 hne
  · intro t h1 h2 he'
    rw [b8] at he'
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · -- an earlier rise: count already ≥ 1 before s1
      have := cnt_succ_change (x := x) (t1 := t1) (u := 160957) (s := t) h1 (by rw [he'.1, he'.2]; simp)
      have := hs1min (t + 1) (by omega)
      omega
    · -- a later rise: the count would pass the certificate's length 2
      have hct : 1 ≤ cnt x t1 160957 t := by
        have := cnt_mono (x := x) (t0 := t1) 160957 (t0 + 1) t (by omega); omega
      have hev : cnt x t1 160957 t % 2 = 0 := by
        have := par t (by omega); rw [he'.1] at this
        rcases Nat.mod_two_eq_zero_or_one (cnt x t1 160957 t) with h | h
        · exact h
        · simp [h] at this
      have h3 := cnt_succ_change (x := x) (t1 := t1) (u := 160957) (s := t) h1 (by rw [he'.1, he'.2]; simp)
      have hlen := hc.capO (t + 1)
      omega
  · intro t ht hw
    rw [b8, b9] at hw
    exact hc.data t0 (by omega) hedge0 t ht hw
  · intro v hv; exact hc.endLow v hv _ (by omega)
  · apply isl_islR hp hb hd (by omega)
    intro s h1 h2
    refine ⟨fun w hw => hc.islEnd w hw s (by omega), ?_, ?_⟩
    · rw [← b2]; exact hc.endLow _ (by simp [bnodes]) s (by omega)
    · rw [← b11]; exact hc.endLow _ (by simp [bnodes]) s (by omega)

/-- **The one-pair statement from one-pair certificates**: if in every behaviour meeting THE hypotheses with one pair
offered (satisfying `Q`), at its rising request from `IslR` and a low boundary, some certificate delivers `EpN1`,
then THE statement holds for every environment offering one pair satisfying `Q`, at any `g > 0`, `κ < 1` with the
reset bound. (`Q a b := a = 12 ∧ b = 18`: the milestone "every admissible delay computes gcd(12, 18)".) -/
theorem onN1_of_cert {Q : Nat → Nat → Prop} {p : DelayPar} {T R su Δo : Nat} (hp : Sane p) (hk : p.κ < 1)
    (hR : Cp p * A1 + 87 * (Cp p * M1) + 1 ≤ R)
    (hcert : ∀ (x : Beh) (va vb : Nat → Nat), Behaves p (circuit net boundary) x → ArbOK T arbs x →
      Env x boundary R su Δo (some 1) va vb → SeqEnv x boundary R → Q (va 0) (vb 0) →
      ∀ t1, R ≤ t1 → IslR p x t1 → Low x boundary t1 → edge (x boundary.a.req) t1 →
        ∃ (C : Cert Nat) (Tend : Nat), EpN1 C x t1 Tend Δo) :
    NetCorrectSeqOnN Q (· = some 1) p T R su Δo := by
  apply the_onN_of_stepR_all hp hk hR
  intro x n va vb hn hb ha he hs hQ t1 ht1 hI hlow hedge
  subst hn
  obtain ⟨C, Tend, hc⟩ := hcert x va vb hb ha he hs (hQ 0 (by simp [Offered])) t1 ht1 hI hlow hedge
  have hAR : Cp p * A1 ≤ R := by omega
  exact stepCore_n1 hp hb (islDelay_all hp hk) hAR he ht1 hlow hedge hc

end Formal.Target.CertN1
