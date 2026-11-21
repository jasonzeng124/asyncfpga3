import Formal.Target.Assembly
import Formal.Target.CertSpec

/-!
# Formal.Target.CertRun — THE statement from ONE run certificate started during reset (shard A, 2026-11-15)

**Problem, plainly.** `PlanRPS` reduces THE statement to a per-pair step that starts from a read island at each
request. A per-pair *certificate* (shard C's `TBehX`) needs a quiet start, and a fastest sequential environment
re-requests 1-4 ps after `out0.req` falls, while the circuit is still settling (notes/A-S6-chaining.md). So
per-pair certificates cannot be chained for `n ≥ 2` pairs. The way out (option 3 of that note) is one certificate
for the whole run, started during reset where the circuit IS quiet (`CViewPS.RIslAll.reset_quiet_all`), as the
unrolled word of C's `AO/Unroll*` with pair boundaries as letters. What must such a certificate deliver, in count
form, for THE statement to follow?

**Proved** (`netCorrectSeq_of_run`, generic in the netlist; `Assembly.OneReq` boundary): if every behaviour meeting
THE hypotheses (`Behaves`, `ArbOK`, `Env`, `SeqEnv`) has a count base `t0 ≤ R` and certificates `C s` (one per time
`s`, e.g. the prefix certificate of the pairs offered by `s`; constant for finitely many pairs) with `EpRun`:
* the boundary is low at `t0`;
* at every time the five boundary handshakes interleave in count form (`a.ack`, `b.ack`, `start.ack` against the
  shared request; `out0.req` against `out0.ack`; the shared request against `end.ack`);
* each change of `a.ack`, `b.ack`, `start.ack`, `out0.req` and the request is an event enabled at counts no later
  than the previous instant, and the cause lists order it after its partner (possibly transitively), as in
  `CertSpec`; `out0.req`'s rise number `k` (event `2k`) is ordered after the request's rise number `k`;
* the data: from `Δo` after an `out0` rise until its acknowledge, the `out0` bus is gcd of the operand buses at
  one past the latest request rise;
* the last episode ends: after a request rise with no later one, some later time has a low boundary and
  `out0.req` counted at least as often as the request;
then THE statement `NetCorrectSeq` holds, at every `p`, `T`, `R`, `su`, `Δo`, for every number of pairs. No
island, no reset bound and no per-pair quiet start are needed: the episode chaining is pure count reasoning plus
`Env` and `SeqEnv` (`plan_of_run` builds `Assembly.Plan` with the invariant "out0.req and the request have the
same count").

**Not shown.** That THE target has such certificates (shard C's instance: the unrolled word over pair
boundaries, `timedA_follows`/`timedA_live` from the reset island); this is a conditional reduction and
establishes nothing at any parameter by itself. It is false wherever THE statement is refuted (`κ ≥ 9/25` at
`g = 1`, `g ≥ 8/5`), since it implies THE statement.
-/

namespace Formal.Target.CertRun
open Formal.Target Formal.Target.Assembly Formal.Net.AO Formal.Net.OccNet.Timed Formal.Target.CertSpec

/-- What one run certificate (counts from `t0`, certificate `C s` in force at time `s`) must deliver. -/
structure EpRun (C : Nat → Cert Nat) (B : Boundary) (x : Beh) (t0 R Δo : Nat) : Prop where
  t0R : t0 ≤ R
  low0 : Low x B t0
  interA : ∀ s, cnt x t0 B.a.ack s ≤ cnt x t0 B.a.req s ∧ cnt x t0 B.a.req s ≤ cnt x t0 B.a.ack s + 1
  interB : ∀ s, cnt x t0 B.b.ack s ≤ cnt x t0 B.a.req s ∧ cnt x t0 B.a.req s ≤ cnt x t0 B.b.ack s + 1
  interS : ∀ s, cnt x t0 B.start.ack s ≤ cnt x t0 B.a.req s ∧ cnt x t0 B.a.req s ≤ cnt x t0 B.start.ack s + 1
  interO : ∀ s, cnt x t0 B.out0.ack s ≤ cnt x t0 B.out0.req s ∧ cnt x t0 B.out0.req s ≤ cnt x t0 B.out0.ack s + 1
  interP : ∀ s, cnt x t0 B.pend.ack s ≤ cnt x t0 B.a.req s ∧ cnt x t0 B.a.req s ≤ cnt x t0 B.pend.ack s + 1
  ordA : ∀ s k, ∀ alt ∈ (C s).causes B.a.ack k, AltIn (fun w => cnt x t0 w s) alt → k < cnt x t0 B.a.req s
  ordB : ∀ s k, ∀ alt ∈ (C s).causes B.b.ack k, AltIn (fun w => cnt x t0 w s) alt → k < cnt x t0 B.a.req s
  ordS : ∀ s k, ∀ alt ∈ (C s).causes B.start.ack k, AltIn (fun w => cnt x t0 w s) alt → k < cnt x t0 B.a.req s
  ordO : ∀ s k, ∀ alt ∈ (C s).causes B.out0.req (k + 1), AltIn (fun w => cnt x t0 w s) alt →
    k < cnt x t0 B.out0.ack s
  ordP : ∀ s k, ∀ alt ∈ (C s).causes B.a.req (k + 1), AltIn (fun w => cnt x t0 w s) alt →
    k < cnt x t0 B.pend.ack s
  ordQ : ∀ s k, ∀ alt ∈ (C s).causes B.out0.req (2 * k), AltIn (fun w => cnt x t0 w s) alt →
    2 * k < cnt x t0 B.a.req s
  en : ∀ v ∈ [B.a.ack, B.b.ack, B.start.ack, B.out0.req, B.a.req], ∀ s, t0 < s → x v s ≠ x v (s - 1) →
    ∃ n : Nat → Nat, (∀ w, n w ≤ cnt x t0 w (s - 1)) ∧ n v = cnt x t0 v (s - 1) ∧ Enabled (C (s - 1)) n v
  data : ∀ t1 tq, R ≤ t1 → edge (x B.a.req) t1 → t1 ≤ tq → edge (x B.out0.req) tq →
    (∀ t, t1 < t → t ≤ tq → ¬ edge (x B.a.req) t) → ∀ t, tq + 1 + Δo ≤ t →
    (∀ s, tq + 1 ≤ s → s ≤ t → x B.out0.req s = true ∧ x B.out0.ack s = false) →
    busVal x B.out0.data t = Nat.gcd (busVal x B.a.data (t1 + 1)) (busVal x B.b.data (t1 + 1))
  last : ∀ t1, R ≤ t1 → edge (x B.a.req) t1 → (∀ t, t1 < t → ¬ edge (x B.a.req) t) →
    ∃ T, t1 < T ∧ Low x B T ∧ cnt x t0 B.a.req T ≤ cnt x t0 B.out0.req T

/-! ## Count lemmas -/

theorem cnt_succ {x : Beh} {t0 u s : Nat} (hs : t0 ≤ s) :
    cnt x t0 u (s + 1) = cnt x t0 u s + (if x u (s + 1) != x u s then 1 else 0) := by
  simp only [cnt]
  rw [if_neg (show ¬ (s + 1 ≤ t0) by omega)]

/-- A node constant on `[t0, b]` has count 0 at `b`. -/
theorem cnt_zero_of_const {x : Beh} {t0 u : Nat} : ∀ b, (∀ s, t0 ≤ s → s ≤ b → x u s = x u t0) →
    cnt x t0 u b = 0
  | 0, _ => rfl
  | b + 1, h => by
    rcases Nat.lt_or_ge b t0 with hb | hb
    · exact cnt_le_t0 u (b + 1) (by omega)
    · rw [cnt_succ hb, cnt_zero_of_const b (fun s h1 h2 => h s h1 (by omega)), h (b + 1) (by omega) le_rfl,
        h b hb (by omega)]
      simp

/-- Rises counted from `R` are half the changes counted from `t0` (rounded up), for a node low at `t0` that has not
moved by `R`. -/
theorem rises_cnt {x : Beh} {t0 R u : Nat} (h0 : x u t0 = false) (ht0 : t0 ≤ R) (hR : cnt x t0 u R = 0) :
    ∀ t, R ≤ t → rises (x u) R t = (cnt x t0 u t + 1) / 2 := by
  intro t ht
  induction t with
  | zero =>
    rw [show R = 0 by omega] at hR; rw [hR]; rfl
  | succ t ih =>
    rcases Nat.lt_or_ge t R with htR | htR
    · rw [show R = t + 1 by omega] at hR ⊢
      rw [rises_self (x u) (t + 1) (t + 1) le_rfl, hR]
    · have ih := ih htR
      have hp := Formal.Net.AO.EnvData.x_par x t0 u h0 t (by omega)
      have hp1 := Formal.Net.AO.EnvData.x_par x t0 u h0 (t + 1) (by omega)
      rw [cnt_succ (by omega)] at hp1 ⊢
      simp only [rises]
      rw [ih]
      rcases Nat.mod_two_eq_zero_or_one (cnt x t0 u t) with hc | hc
      · rw [hc] at hp
        by_cases hch : x u (t + 1) = x u t
        · simp [hch]
        · have h1 : x u (t + 1) = true := by
            simp at hp; rw [hp] at hch; simpa using hch
          simp [hp, h1, htR]
          omega
      · rw [hc] at hp
        by_cases hch : x u (t + 1) = x u t
        · simp [hch]
        · have h1 : x u (t + 1) = false := by
            simp at hp; rw [hp] at hch; simpa using hch
          simp [hp, h1]
          omega

/-- Two edges in `[a, b)` (from `R` on) add at least two rises. -/
theorem rises_two {s : Sig} {R a b e1 e2 : Nat} (hR : R ≤ a) (h1 : a ≤ e1) (h12 : e1 < e2) (h2 : e2 < b)
    (he1 : edge s e1) (he2 : edge s e2) : rises s R a + 2 ≤ rises s R b := by
  have r1 := rises_edge s (show R ≤ e1 by omega) he1
  have r2 := rises_edge s (show R ≤ e2 by omega) he2
  have m1 := rises_mono s R a e1 h1
  have m2 := rises_mono s R (e1 + 1) e2 (by omega)
  have m3 := rises_mono s R (e2 + 1) b (by omega)
  omega

/-! ## Moves from per-time certificates (as `CertSpec`'s transitive forms, with the certificate indexed by time) -/

theorem ackMoves_run (C : Nat → Cert Nat) (x : Beh) (t0 r a : Nat) (h0r : x r t0 = false) (h0a : x a t0 = false)
    (hInter : ∀ s, cnt x t0 a s ≤ cnt x t0 r s ∧ cnt x t0 r s ≤ cnt x t0 a s + 1)
    (hAkT : ∀ s k, ∀ alt ∈ (C s).causes a k, AltIn (fun w => cnt x t0 w s) alt → k < cnt x t0 r s)
    (hen : ∀ s, t0 < s → x a s ≠ x a (s - 1) → ∃ n : Nat → Nat, (∀ w, n w ≤ cnt x t0 w (s - 1)) ∧
      n a = cnt x t0 a (s - 1) ∧ Enabled (C (s - 1)) n a) :
    AckMoves (x r) (x a) t0 := by
  intro t ht hne
  obtain ⟨n, hle, hna, -, alt, halt, hin⟩ := hen (t + 1) (by omega) (by simpa using hne)
  simp only [Nat.add_sub_cancel] at hle hna halt
  rw [hna] at halt
  have hra := hAkT t _ alt halt (altIn_mono hle hin)
  have hc := hInter t
  have heq : cnt x t0 r t = cnt x t0 a t + 1 := by omega
  rw [Formal.Net.AO.EnvData.x_par x t0 a h0a t ht, Formal.Net.AO.EnvData.x_par x t0 r h0r t ht, heq]
  exact parity_ne _

theorem reqMoves_run (C : Nat → Cert Nat) (x : Beh) (t0 r a : Nat) (h0r : x r t0 = false) (h0a : x a t0 = false)
    (hInter : ∀ s, cnt x t0 a s ≤ cnt x t0 r s ∧ cnt x t0 r s ≤ cnt x t0 a s + 1)
    (hRqT : ∀ s k, ∀ alt ∈ (C s).causes r (k + 1), AltIn (fun w => cnt x t0 w s) alt → k < cnt x t0 a s)
    (hen : ∀ s, t0 < s → x r s ≠ x r (s - 1) → ∃ n : Nat → Nat, (∀ w, n w ≤ cnt x t0 w (s - 1)) ∧
      n r = cnt x t0 r (s - 1) ∧ Enabled (C (s - 1)) n r) :
    ReqMoves (x r) (x a) t0 := by
  intro t ht hne
  obtain ⟨n, hle, hnr, -, alt, halt, hin⟩ := hen (t + 1) (by omega) (by simpa using hne)
  simp only [Nat.add_sub_cancel] at hle hnr halt
  have hc := hInter t
  have heq : cnt x t0 r t = cnt x t0 a t := by
    rcases Nat.eq_zero_or_pos (n r) with h0 | hpos
    · omega
    · obtain ⟨k, hk⟩ : ∃ k, n r = k + 1 := ⟨n r - 1, by omega⟩
      rw [hk] at halt
      have hak := hRqT t k alt halt (altIn_mono hle hin)
      omega
  rw [Formal.Net.AO.EnvData.x_par x t0 a h0a t ht, Formal.Net.AO.EnvData.x_par x t0 r h0r t ht, heq]

/-- `out0.req`'s rise number `k` comes after the request's: `⌈cnt out0.req / 2⌉ ≤ ⌈cnt req / 2⌉` at every time. -/
theorem pairO_run (C : Nat → Cert Nat) (x : Beh) (t0 o r : Nat)
    (hQ : ∀ s k, ∀ alt ∈ (C s).causes o (2 * k), AltIn (fun w => cnt x t0 w s) alt → 2 * k < cnt x t0 r s)
    (hen : ∀ s, t0 < s → x o s ≠ x o (s - 1) → ∃ n : Nat → Nat, (∀ w, n w ≤ cnt x t0 w (s - 1)) ∧
      n o = cnt x t0 o (s - 1) ∧ Enabled (C (s - 1)) n o) :
    ∀ s, (cnt x t0 o s + 1) / 2 ≤ (cnt x t0 r s + 1) / 2 := by
  intro s
  induction s with
  | zero => simp [cnt]
  | succ s ih =>
    rcases Nat.lt_or_ge s t0 with hs | hs
    · rw [cnt_le_t0 o (s + 1) (by omega), cnt_le_t0 r (s + 1) (by omega)]
    · have hmr := cnt_mono (x := x) (t0 := t0) r s (s + 1) (by omega)
      rw [cnt_succ (u := o) hs]
      by_cases hch : x o (s + 1) = x o s
      · simp only [hch, bne_self_eq_false, Bool.false_eq_true, if_false, Nat.add_zero]; omega
      · have hne : (x o (s + 1) != x o s) = true := by simpa using hch
        rw [if_pos hne]
        rcases Nat.mod_two_eq_zero_or_one (cnt x t0 o s) with hc | hc
        · obtain ⟨n, hle, hno, -, alt, halt, hin⟩ := hen (s + 1) (by omega) (by simpa using hch)
          simp only [Nat.add_sub_cancel] at hle hno halt
          obtain ⟨k, hk⟩ : ∃ k, cnt x t0 o s = 2 * k := ⟨cnt x t0 o s / 2, by omega⟩
          rw [hno, hk] at halt
          have := hQ s k alt halt (altIn_mono hle hin)
          omega
        · omega

/-! ## The plan -/

section plan
variable {B : Boundary} {x : Beh} {R su Δo : Nat} {n : Option Nat} {va vb : Nat → Nat} {C : Nat → Cert Nat}
  {t0 : Nat}

/-- **One run certificate gives `Assembly.Plan`** with the invariant "out0.req and the request have equal counts". -/
theorem plan_of_run (hreq : OneReq B) (he : EnvWF x B R su Δo n va vb) (hs : SeqEnv x B R)
    (hc : EpRun C B x t0 R Δo) :
    Plan x B R Δo (fun t => cnt x t0 B.out0.req t = cnt x t0 B.a.req t) := by
  classical
  obtain ⟨hbr, hsr, hpr⟩ := hreq
  have he' := he
  obtain ⟨-, -, -, hEa, hEb, hEs, hEo, hEp⟩ := he'
  obtain ⟨hq0, hqm, -, -, -, -⟩ := hEa
  obtain ⟨-, hqmB, -, -, -, -⟩ := hEb
  obtain ⟨-, hqmS, -, -, -, -⟩ := hEs
  obtain ⟨ho0, -, -, -⟩ := hEo
  have ht0 := hc.t0R
  -- abbreviations
  have hl0 : ∀ v ∈ bnodes B, x v t0 = false := hc.low0
  have l_r : x B.a.req t0 = false := hl0 _ (by simp [bnodes])
  have l_a : x B.a.ack t0 = false := hl0 _ (by simp [bnodes])
  have l_b : x B.b.ack t0 = false := hl0 _ (by simp [bnodes])
  have l_s : x B.start.ack t0 = false := hl0 _ (by simp [bnodes])
  have l_o : x B.out0.req t0 = false := hl0 _ (by simp [bnodes])
  have l_oa : x B.out0.ack t0 = false := hl0 _ (by simp [bnodes])
  have l_pa : x B.pend.ack t0 = false := hl0 _ (by simp [bnodes])
  have en := fun v hv => hc.en v hv
  have mA := ackMoves_run C x t0 B.a.req B.a.ack l_r l_a hc.interA hc.ordA (en _ (by simp))
  have mB := ackMoves_run C x t0 B.a.req B.b.ack l_r l_b hc.interB hc.ordB (en _ (by simp))
  have mS := ackMoves_run C x t0 B.a.req B.start.ack l_r l_s hc.interS hc.ordS (en _ (by simp))
  have mO := reqMoves_run C x t0 B.out0.req B.out0.ack l_o l_oa hc.interO hc.ordO (en _ (by simp))
  have mP := reqMoves_run C x t0 B.a.req B.pend.ack l_r l_pa hc.interP hc.ordP (en _ (by simp))
  have pO := pairO_run C x t0 B.out0.req B.a.req hc.ordQ (en _ (by simp))
  have par : ∀ u, x u t0 = false → ∀ s, t0 ≤ s → x u s = (cnt x t0 u s % 2 == 1) :=
    fun u h s hs => Formal.Net.AO.EnvData.x_par x t0 u h s hs
  have evn : ∀ u, x u t0 = false → ∀ s, t0 ≤ s → x u s = false → cnt x t0 u s % 2 = 0 := by
    intro u h s hs hx
    have := par u h s hs; rw [hx] at this
    rcases Nat.mod_two_eq_zero_or_one (cnt x t0 u s) with h' | h'
    · exact h'
    · simp [h'] at this
  have odd : ∀ u, x u t0 = false → ∀ s, t0 ≤ s → x u s = true → cnt x t0 u s % 2 = 1 := by
    intro u h s hs hx
    have := par u h s hs; rw [hx] at this
    rcases Nat.mod_two_eq_zero_or_one (cnt x t0 u s) with h' | h'
    · simp [h'] at this
    · exact h'
  -- counts at R
  have cr0 : cnt x t0 B.a.req R = 0 :=
    cnt_zero_of_const R (fun s h1 h2 => by rw [hq0 s h2, hq0 t0 (by omega)])
  have coa0 : cnt x t0 B.out0.ack R = 0 :=
    cnt_zero_of_const R (fun s h1 h2 => by rw [ho0 s h2, ho0 t0 (by omega)])
  have co0 : cnt x t0 B.out0.req R = 0 := by have := pO R; rw [cr0] at this; omega
  have rr := rises_cnt l_r ht0 cr0
  have roa := rises_cnt l_oa ht0 coa0
  have ro := rises_cnt l_o ht0 co0
  -- the request is low at every rise time of itself; acks follow the request at env moves
  -- the step, given an end point
  have stepEnd : ∀ t1 t2, R ≤ t1 → cnt x t0 B.out0.req t1 = cnt x t0 B.a.req t1 → Low x B t1 → edge (x B.a.req) t1 → t1 < t2 →
      Low x B t2 → (∀ t, t1 < t → t < t2 → ¬ edge (x B.a.req) t) → cnt x t0 B.a.req t2 ≤ cnt x t0 B.out0.req t2 →
      ∃ t2' tq, StepCore x B Δo (fun t => cnt x t0 B.out0.req t = cnt x t0 B.a.req t) t1 t2' tq := by
    intro t1 t2 hR1 hI hL1 he1 h12 hL2 hno hle
    have r1 : x B.a.req t1 = false := hL1 _ (by simp [bnodes])
    have r2 : x B.a.req t2 = false := hL2 _ (by simp [bnodes])
    have o2 : x B.out0.req t2 = false := hL2 _ (by simp [bnodes])
    obtain ⟨m, hm⟩ : ∃ m, cnt x t0 B.a.req t1 = 2 * m := ⟨cnt x t0 B.a.req t1 / 2, by
      have := evn B.a.req l_r t1 (by omega) r1; omega⟩
    -- request count at t2
    have rs1 := rr t1 hR1
    have rs2 := rr t2 (by omega)
    have rsE := rises_edge (x B.a.req) hR1 he1
    have rsC := rises_const (x B.a.req) R (t1 + 1) t2 (by omega) (fun t h1 h2 => hno t (by omega) h2)
    have ev2 := evn B.a.req l_r t2 (by omega) r2
    have hr2 : cnt x t0 B.a.req t2 = 2 * m + 2 := by omega
    have evo := evn B.out0.req l_o t2 (by omega) o2
    have pO2 := pO t2
    have ho2 : cnt x t0 B.out0.req t2 = 2 * m + 2 := by omega
    -- the out0 rise in [t1, t2)
    have ros1 := ro t1 hR1
    have ros2 := ro t2 (by omega)
    have hex : ∃ tq, t1 ≤ tq ∧ tq < t2 ∧ edge (x B.out0.req) tq := by
      by_contra hne
      push Not at hne
      have := rises_const (x B.out0.req) R t1 t2 (by omega) (fun t h1 h2 he => hne t h1 h2 he)
      omega
    obtain ⟨tq, hq1, hq2, hqe⟩ := hex
    refine ⟨t2, tq, ⟨h12, hno, ?_, ?_, hq1, hq2, hqe, ?_, ?_, hL2, by omega⟩⟩
    · intro ch hch t h1 h2 hne
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hch
      rcases hch with rfl | rfl | rfl
      · exact mA t (by omega) hne
      · rw [hbr]; exact mB t (by omega) hne
      · rw [hsr]; exact mS t (by omega) hne
    · intro ch hch t h1 h2 hne
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hch
      rcases hch with rfl | rfl
      · exact mO t (by omega) hne
      · rw [hpr] at hne ⊢; exact mP t (by omega) hne
    · intro t h1 h2 hte
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · have := rises_two (s := x B.out0.req) hR1 h1 hlt hq2 hte hqe; omega
      · have := rises_two (s := x B.out0.req) hR1 hq1 hgt h2 hqe hte; omega
    · intro t ht hw
      exact hc.data t1 tq hR1 he1 hq1 hqe (fun t h1 h2 => hno t h1 (by omega)) t ht hw
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- base invariant
    show cnt x t0 B.out0.req R = cnt x t0 B.a.req R
    rw [co0, cr0]
  · -- base: the circuit's outputs low at R
    intro v hv
    simp only [couts, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · rw [par _ l_a R ht0]; have := (hc.interA R).1; rw [cr0] at this
      rw [show cnt x t0 B.a.ack R = 0 by omega]; rfl
    · rw [par _ l_b R ht0]; have := (hc.interB R).1; rw [cr0] at this
      rw [show cnt x t0 B.b.ack R = 0 by omega]; rfl
    · rw [par _ l_s R ht0]; have := (hc.interS R).1; rw [cr0] at this
      rw [show cnt x t0 B.start.ack R = 0 by omega]; rfl
    · rw [par _ l_o R ht0, co0]; rfl
  · -- quiet: no request rise, the circuit's outputs stay low
    intro t hR hI hL hq
    have rt : x B.a.req t = false := hL _ (by simp [bnodes])
    have crt : cnt x t0 B.a.req (t + 1) = cnt x t0 B.a.req t := by
      rw [cnt_succ (by omega)]; simp [rt, show x B.a.req (t + 1) = false from hq]
    have er := evn B.a.req l_r t (by omega) rt
    have ackStay : ∀ u, x u t0 = false → x u t = false →
        (∀ s, cnt x t0 u s ≤ cnt x t0 B.a.req s ∧ cnt x t0 B.a.req s ≤ cnt x t0 u s + 1) → x u (t + 1) = false := by
      intro u hu0 hut hint
      have e1 := evn u hu0 t (by omega) hut
      have i1 := hint t
      have i2 := hint (t + 1)
      have mo := cnt_mono (x := x) (t0 := t0) u t (t + 1) (by omega)
      rw [par u hu0 (t + 1) (by omega), show cnt x t0 u (t + 1) = cnt x t0 u t by omega, e1]; rfl
    have hot : x B.out0.req t = false := hL _ (by simp [bnodes])
    have eo := evn B.out0.req l_o t (by omega) hot
    have po := pO (t + 1)
    have mo := cnt_mono (x := x) (t0 := t0) B.out0.req t (t + 1) (by omega)
    have co1 : cnt x t0 B.out0.req (t + 1) = cnt x t0 B.out0.req t := by rw [crt] at po; omega
    refine ⟨?_, ?_⟩
    · intro v hv
      simp only [couts, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · exact ackStay _ l_a (hL _ (by simp [bnodes])) hc.interA
      · exact ackStay _ l_b (hL _ (by simp [bnodes])) hc.interB
      · exact ackStay _ l_s (hL _ (by simp [bnodes])) hc.interS
      · rw [par B.out0.req l_o (t + 1) (by omega), co1, eo]; rfl
    · show cnt x t0 B.out0.req (t + 1) = cnt x t0 B.a.req (t + 1)
      rw [co1, crt]; exact hI
  · -- the step
    intro t1 hR1 hI hL1 he1
    by_cases hnext : ∃ t, t1 < t ∧ edge (x B.a.req) t
    · -- the next request rise ends the episode
      let t2 := Nat.find hnext
      have ht2 : t1 < t2 ∧ edge (x B.a.req) t2 := Nat.find_spec hnext
      have hmin : ∀ t, t1 < t → t < t2 → ¬ edge (x B.a.req) t := fun t h1 h2 he =>
        Nat.find_min hnext h2 ⟨h1, he⟩
      have hR2 : R ≤ t2 := by omega
      -- the environment's acks equal the request when it moves
      have rch : x B.a.req (t2 + 1) ≠ x B.a.req t2 := by rw [ht2.2.1, ht2.2.2]; simp
      have aEq := hqm t2 hR2 rch
      have bEq := hqmB t2 hR2 (by rw [hbr]; exact rch)
      have sEq := hqmS t2 hR2 (by rw [hsr]; exact rch)
      have pEq := mP t2 (by omega) rch
      obtain ⟨hseq, hso, hsoa⟩ := hs B.a (by simp) t2 hR2 ht2.2.1 ht2.2.2
      have hL2 : Low x B t2 := by
        intro v hv
        simp only [bnodes, List.mem_cons, List.not_mem_nil, or_false] at hv
        have r2 : x B.a.req t2 = false := ht2.2.1
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact r2
        · rw [← aEq]; exact r2
        · rw [hbr]; exact r2
        · rw [hbr] at bEq; rw [← bEq]; exact r2
        · rw [hsr]; exact r2
        · rw [hsr] at sEq; rw [← sEq]; exact r2
        · exact hso
        · exact hsoa
        · rw [hpr]; exact r2
        · rw [← pEq]; exact r2
      -- counts at t2: the request has risen once more, out0's acknowledge as often (SeqEnv)
      have rs1 := rr t1 hR1
      have rs2 := rr t2 hR2
      have rsE := rises_edge (x B.a.req) hR1 he1
      have rsC := rises_const (x B.a.req) R (t1 + 1) t2 (by omega) (fun t h1 h2 => hmin t (by omega) h2)
      have roa2 := roa t2 hR2
      have eoa := evn B.out0.ack l_oa t2 (by omega) hsoa
      have io := (hc.interO t2).1
      have hseq' : rises (x B.a.req) R t2 ≤ rises (x B.out0.ack) R t2 := hseq
      have hle : cnt x t0 B.a.req t2 ≤ cnt x t0 B.out0.req t2 := by
        have ev2 := evn B.a.req l_r t2 (by omega) ht2.2.1
        omega
      exact stepEnd t1 t2 hR1 hI hL1 he1 ht2.1 hL2 hmin hle
    · -- the last request: the certificate's end
      push Not at hnext
      obtain ⟨T, hT1, hLT, hle⟩ := hc.last t1 hR1 he1 (fun t h1 h2 => hnext t h1 h2)
      exact stepEnd t1 T hR1 hI hL1 he1 hT1 hLT (fun t h1 _ h2 => hnext t h1 h2) hle

end plan

/-- **THE statement from one run certificate per behaviour** (generic in the netlist, `OneReq` boundary). -/
theorem netCorrectSeq_of_run {N : Net} {B : Boundary} {A : List ArbNodes} {p : DelayPar} {T R su Δo : Nat}
    (hreq : OneReq B)
    (h : ∀ (x : Beh) (n : Option Nat) (va vb : Nat → Nat), Behaves p (circuit N B) x → ArbOK T A x →
      Env x B R su Δo n va vb → SeqEnv x B R → ∃ (C : Nat → Cert Nat) (t0 : Nat), EpRun C B x t0 R Δo) :
    NetCorrectSeq N B A p T R su Δo := by
  apply netCorrectSeq_of_plan hreq
  intro x n va vb hb ha he hs
  obtain ⟨C, t0, hc⟩ := h x n va vb hb ha he hs
  exact ⟨_, plan_of_run hreq (envWF_of_env he) hs hc⟩

/-- **The weak-fairness statement (`SpecWF`) from one run certificate per behaviour** (shard A, 2026-11-16). -/
theorem netCorrectSeqWF_of_run {N : Net} {B : Boundary} {A : List ArbNodes} {p : DelayPar} {T R su Δo : Nat}
    (hreq : OneReq B)
    (h : ∀ (x : Beh) (n : Option Nat) (va vb : Nat → Nat), Behaves p (circuit N B) x → ArbOK T A x →
      EnvWF x B R su Δo n va vb → SeqEnv x B R → ∃ (C : Nat → Cert Nat) (t0 : Nat), EpRun C B x t0 R Δo) :
    NetCorrectSeqWF N B A p T R su Δo := by
  apply netCorrectSeqWF_of_plan hreq
  intro x n va vb hb ha he hs
  obtain ⟨C, t0, hc⟩ := h x n va vb hb ha he hs
  exact ⟨_, plan_of_run hreq he hs hc⟩

end Formal.Target.CertRun
