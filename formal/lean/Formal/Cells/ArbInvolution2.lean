import Formal.Cells.ArbInvolution

/-!
# Track 7, probe 7n: finishing the involution arbiter

Continues probe 7m (`Formal.Cells.ArbInvolution`, read-only here). Same cell, same
gate model: the REAL INITs of `bd_arbcell` (`stF`, `gr1`, `gr2` via `lutB`/`o5B`/`o6B`)
applied in zero time, followed by shard A's involution channels (`InvolutionPair`,
`tent`) through probe 5e's signal-level fragment `InvChanF`.

Contents.
1. **Resolving gaps** (open item 1). For EVERY gap `0 < s < δ∞↑`:
   * `grants_resolve`: if the loop resolves (not `Osc`), then in every solution `q`,
     `g1`, `g2` are eventually constant with `g1 = q` and `g2 = ¬q` at the end. A final
     cancellation in a grant channel removes a PAIR of edges, so it never leaves a
     grant stuck at the wrong value, and no grant pulses forever.
   * `grants_exclusive`: under `BBM`, `g1 ∧ g2` is never true, at every gap (both the
     oscillating and the resolving case, including final cancellations in either
     grant channel).
2. **H_GRANT_PASS derived** (open item 4). `Margin P g` (a property of the loop channel
   alone) gives a lower bound `g` on every pulse of `q` except the last two of a
   resolving orbit (`margin_orb`); `margin_exists`: such `g > 0` always exists
   (continuity of A's delay functions, proved in 5e). `Passes G g` (an isolated pulse of
   width `g` survives `G`, both polarities) then rules out every interior cancellation
   (`tent_step`). Hence `grants_exist_all`: for EVERY gap, if both grant channels pass
   pulses of width `g`, the full cell has a solution; the exclusion theorems are not
   vacuous.
3. **Mirror scenario** (open item 2). Reset `q = 1`, `r2` first at `0`, `r1` at `s`.
   `swapP` (δ↑ ↔ δ↓) is again an involution pair, and the complement of a channel
   idle at 1 is the `swapP` channel idle at 0 (`H_CH1`). The INIT is symmetric under
   `r1 ↔ r2, q ↔ ¬q` (`stF_mirror`, `gr_mirror1/2`), so every mirror solution is a 7m
   solution for `swapP P` with the grants exchanged (`toA`, `toAG`). All results transfer;
   the mirror critical gap is the one of `swapP P`, in `(δ∞↓ - δ↓(0), δ∞↓)`.
4. **A concrete overlapping triple** (open item 3). `hyp A B k` is an explicit rational
   involution pair (`δ↑ T = A - k/(T+B)`, `δ↓ T = B - k/(T+A)`). With `P = hyp 1 1 (3/8)`
   the critical gap is EXACTLY `s* = 3/4` (`Pc_orb`: `q` toggles every `1/4` forever).
   With `G5 = hyp (1/4) (1/4) (1/128)`, `G6 = hyp (5/16) (5/16) (1/128)` (O6 25% slower
   than O5), `overlap_reachable`: the cell has a solution, in every solution both grants
   pulse forever AND are simultaneously high at some time, and `BBM G5 G6` fails.
-/

namespace Formal.Cells.ArbInvolution2
open Formal.Cells
open Formal.Cells.CElemInvolution
open Formal.Cells.ArbInvolution
open Formal.Cells.ArbBinary (stF gr1 gr2 stF_eq gr1_eq gr2_eq)
open Formal.Core.DelayInvolution
open Filter Topology

/-! ## 0. Helpers -/

/-- Pad a finite prefix `o 0 .. o (m-1)` to an infinite strictly increasing sequence
(only used to apply A's `dom_ok`/`tent_le`, which want a total sequence; tentative
outputs of the prefix do not depend on the padding, `tent_congr`). -/
noncomputable def ext (o : ℕ → ℝ) (m : ℕ) (n : ℕ) : ℝ :=
  if n < m then o n else o (m - 1) + ((n : ℝ) - m + 1)

theorem ext_lt {o : ℕ → ℝ} {m n : ℕ} (h : n < m) : ext o m n = o n := ite_eq_left h

theorem ext_incr {o : ℕ → ℝ} {m : ℕ} (h : ∀ j, j + 1 < m → o j < o (j + 1)) :
    ∀ n, ext o m n < ext o m (n + 1) := by
  intro n
  unfold ext
  by_cases h1 : n + 1 < m
  · rw [ite_eq_left (by omega), ite_eq_left h1]; exact h n h1
  · rw [ite_eq_right h1]
    by_cases h2 : n < m
    · rw [ite_eq_left h2]
      have e : m - 1 = n := by omega
      have hm : (m : ℝ) = n + 1 := by exact_mod_cast (by omega : m = n + 1)
      rw [e, hm]; push_cast; linarith
    · rw [ite_eq_right h2]; push_cast; linarith

theorem ext_zero {o : ℕ → ℝ} {m : ℕ} {s : ℝ} (h : s < o 0) : s < ext o m 0 := by
  unfold ext
  by_cases h1 : 0 < m
  · rw [ite_eq_left h1]; exact h
  · rw [ite_eq_right h1]
    have e : m = 0 := by omega
    subst e; simp; linarith

theorem cons1_incr {o : ℕ → ℝ} {s : ℝ} (h0 : s < o 0) (h : ∀ n, o n < o (n + 1)) :
    ∀ n, cons1 s o n < cons1 s o (n + 1) := by
  intro n
  match n with
  | 0 => exact h0
  | k + 1 => exact h k

theorem tent_congr_lt (G : InvolutionPair) {t t' : ℕ → ℝ} {K : ℕ} (h : ∀ n < K, t n = t' n) :
    ∀ n < K, G.tent t n = G.tent t' n := fun n hn =>
  tent_congr G (N := n) (fun j hj => h j (by omega)) n le_rfl

/-- 7m's `interleave` for an ARBITRARY strictly increasing `q`-edge sequence `o`
(with the `r2` rise `s` before `o 0`): under `BBM`, `b (n+1) < a n` at even `n`
and `a n < b (n+1)` at odd `n`, where `a = G5.tent o`, `b = G6.tent (s :: o)`. -/
theorem interleaveG {G5 G6 : InvolutionPair} (H : BBM G5 G6) {s : ℝ} (o : ℕ → ℝ)
    (hs0 : s < o 0) (hinc : ∀ n, o n < o (n + 1)) :
    ∀ n, (n % 2 = 0 → G6.tent (cons1 s o) (n + 1) < G5.tent o n) ∧
      (n % 2 = 1 → G5.tent o n < G6.tent (cons1 s o) (n + 1)) := by
  set a := G5.tent o with ha
  set b := G6.tent (cons1 s o) with hb
  have hinc1 := cons1_incr hs0 hinc
  have domA : ∀ n, -G5.infAt n < o (n + 1) - a n := fun n => G5.dom_ok o hinc n
  have domB : ∀ n, -G6.infAt n < o n - b n := fun n => G6.dom_ok (cons1 s o) hinc1 n
  have ea : ∀ n, a (n + 1) = o (n + 1) + G5.delayAt (n + 1) (o (n + 1) - a n) := fun _ => rfl
  have eb : ∀ n, b (n + 1) = o n + G6.delayAt (n + 1) (o n - b n) := fun _ => rfl
  intro n
  induction n with
  | zero =>
    refine ⟨fun _ => ?_, fun h => absurd h (by decide)⟩
    have ha0 : a 0 = o 0 + G5.infUp := rfl
    have hd0 := domB 0
    rw [infAt_even G6 (by rfl)] at hd0
    rw [eb 0, delayAt_odd G6 (by rfl), ha0]
    set x := o 0 - b 0
    have h1 := H.H_BBM1 x (max x 0 + 1) hd0 (by linarith [le_max_left x 0])
      (by linarith [le_max_right x 0, G5.infDown_pos])
    have h2 := G5.up_lt (max x 0 + 1) (by linarith [le_max_right x 0, G5.infDown_pos])
    linarith
  | succ n ih =>
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn
    · have hI := ih.1 hn
      refine ⟨fun h => absurd h (by omega), fun _ => ?_⟩
      have dA := domA n
      rw [infAt_even G5 hn] at dA
      have dB := domB (n + 1)
      rw [infAt_odd G6 (by omega)] at dB
      rw [ea n, eb (n + 1), delayAt_odd G5 (by omega), delayAt_even G6 (by omega)]
      have := H.H_BBM2 (o (n + 1) - a n) (o (n + 1) - b (n + 1)) dA (by linarith) dB
      linarith
    · have hI := ih.2 hn
      refine ⟨fun _ => ?_, fun h => absurd h (by omega)⟩
      have dA := domA n
      rw [infAt_odd G5 hn] at dA
      have dB := domB (n + 1)
      rw [infAt_even G6 (by omega)] at dB
      rw [ea n, eb (n + 1), delayAt_even G5 (by omega), delayAt_odd G6 (by omega)]
      have := H.H_BBM1 (o (n + 1) - b (n + 1)) (o (n + 1) - a n) dB (by linarith) dA
      linarith

/-- **A grant channel on a finite input.** If the input has exactly `K` transitions
(at `o 0 < ... < o (K-1)`), every `InvChanF` run has output `den (tent o) (· < k)`
with either `k = K` (no cancellation) or `k + 2 = K` (the LAST two tentative outputs
annihilate). Interior cancellations are outside the fragment (no run). -/
theorem run_fin (G : InvolutionPair) {o : ℕ → ℝ} {K : ℕ}
    (hinc : ∀ n, n + 1 < K → o n < o (n + 1)) {y g : Sig}
    (hy : y = den o (· < K)) (hch : InvChanF G y g) :
    ∃ k, g = den (G.tent o) (· < k) ∧
      ((k = K ∧ ∀ n, n + 1 < K → G.tent o n < G.tent o (n + 1)) ∨
       (k + 2 = K ∧ (∀ n < k, G.tent o n < G.tent o (n + 1)) ∧
         G.tent o (k + 1) ≤ G.tent o k)) := by
  obtain ⟨t, ok, okO, R, hx, hg⟩ := hch
  have hdK : DownC (fun n : ℕ => n < K) := fun n h => by omega
  have hiK : Incr o (fun n : ℕ => n < K) := fun n h => hinc n h
  have hinj := den_inj R.down R.incr hdK hiK (hx.symm.trans hy)
  have hok : ∀ n, ok n ↔ n < K := fun n => (hinj n).1
  have ht : ∀ n < K, t n = o n := fun n h => (hinj n).2 ((hok n).mpr h)
  have hT := tent_congr_lt G ht
  rcases R.out with ⟨hall, _, _⟩ | ⟨m, hm1, hm2, hm3, hm4⟩ | ⟨N, hN1, hN2, hN3⟩
  · exact absurd ((hok K).mp (hall K)) (lt_irrefl K)
  · have hK : m + 2 = K := by
      have a := (hok (m + 1)).mp ((hm1 (m + 1)).mpr (by omega))
      have b : ¬ (m + 2 < K) := fun h => by
        have := (hm1 (m + 2)).mp ((hok (m + 2)).mpr h); omega
      omega
    refine ⟨m, ?_, Or.inr ⟨hK, fun n hn => ?_, ?_⟩⟩
    · rw [hg]; exact den_congr hm2 (fun n hn => hT n (by have := (hm2 n).mp hn; omega))
    · rw [← hT n (by omega), ← hT (n + 1) (by omega)]; exact hm3 n hn
    · rw [← hT m (by omega), ← hT (m + 1) (by omega)]; exact hm4
  · have hK : N = K := by
      rcases lt_trichotomy N K with h | h | h
      · exact absurd ((hN1 N).mp ((hok N).mpr h)) (lt_irrefl N)
      · exact h
      · exact absurd ((hok K).mp ((hN1 K).mpr h)) (lt_irrefl K)
    subst hK
    refine ⟨N, ?_, Or.inl ⟨rfl, fun n hn => ?_⟩⟩
    · rw [hg]; exact den_congr hN2 (fun n hn => hT n ((hN2 n).mp hn))
    · rw [← hT n (by omega), ← hT (n + 1) hn]; exact hN3 n hn

/-- A finite alternating signal with `k` transitions ends at `k mod 2`. -/
theorem den_final {z : ℕ → ℝ} {k : ℕ} (hz : ∀ n, n + 1 < k → z n < z (n + 1)) :
    ∃ T, ∀ u, T ≤ u → den z (· < k) u = decide (k % 2 = 1) := by
  have hd : DownC (fun n : ℕ => n < k) := fun n h => by omega
  have hi : Incr z (fun n : ℕ => n < k) := fun n h => hz n h
  rcases k with _ | j
  · refine ⟨0, fun u _ => ?_⟩
    rw [show decide ((0 : ℕ) % 2 = 1) = false from rfl, Bool.eq_false_iff]
    intro hh
    exact hi_before hd hi (fun h => absurd h (by omega)) (den_true.mp hh)
  · refine ⟨z j, fun u hu => ?_⟩
    rw [Bool.eq_iff_iff, den_true, decide_eq_true_iff]
    exact (hi_iff hd hi (n := j) (by omega) hu (fun h => absurd h (by omega))).trans
      ⟨fun h => by omega, fun h => by omega⟩

/-- **Combinatorial core of exclusion on a finite (resolving) run.** `a`, `b` are the
tentative O5/O6 edges, interleaved as `BBM` forces; O5 has `k1 ∈ {m, m-2}` real edges
and O6 has `k2 ∈ {m+1, m-1}`, with the cancelling last pair if any. Then the grants
are never high together. -/
theorem excl_fin {a b : ℕ → ℝ} {m k1 k2 : ℕ}
    (Ie : ∀ n, n % 2 = 0 → b (n + 1) < a n) (Io : ∀ n, n % 2 = 1 → a n < b (n + 1))
    (S5 : (k1 = m ∧ ∀ n, n + 1 < m → a n < a (n + 1)) ∨
      (k1 + 2 = m ∧ (∀ n < k1, a n < a (n + 1)) ∧ a (k1 + 1) ≤ a k1))
    (S6 : (k2 = m + 1 ∧ ∀ n, n + 1 < m + 1 → b n < b (n + 1)) ∨
      (k2 + 2 = m + 1 ∧ (∀ n < k2, b n < b (n + 1)) ∧ b (k2 + 1) ≤ b k2))
    (u : ℝ) : ¬ (Hi a (· < k1) u ∧ Hi b (· < k2) u) := by
  have hd1 : DownC (fun n : ℕ => n < k1) := fun n h => by omega
  have hd2 : DownC (fun n : ℕ => n < k2) := fun n h => by omega
  have hi1 : Incr a (fun n : ℕ => n < k1) := by
    intro n hn
    have hn : n + 1 < k1 := hn
    rcases S5 with ⟨e, h⟩ | ⟨_, h, _⟩
    · exact h n (by omega)
    · exact h n (by omega)
  have hi2 : Incr b (fun n : ℕ => n < k2) := by
    intro n hn
    have hn : n + 1 < k2 := hn
    rcases S6 with ⟨e, h⟩ | ⟨_, h, _⟩
    · exact h n (by omega)
    · exact h n (by omega)
  have k1m : k1 ≤ m := by rcases S5 with ⟨e, _⟩ | ⟨e, _⟩ <;> omega
  have k2m : k2 ≤ m + 1 := by rcases S6 with ⟨e, _⟩ | ⟨e, _⟩ <;> omega
  rintro ⟨⟨n, pn, hn, h1, h2⟩, ⟨n', pn', hn', h1', h2'⟩⟩
  have hn : n < k1 := hn
  have hn' : n' < k2 := hn'
  rcases le_or_gt n' n with hle | hlt
  · by_cases c : n' + 1 < k2
    · have x1 := h2' c
      have x2 := Ie n' pn'
      have x3 := s_le hd1 hi1 (i := n') (j := n) hn hle
      linarith
    · rcases S6 with ⟨e, _⟩ | ⟨e, _, hc6⟩
      · omega
      · have hk2 : k2 = n' + 1 := by omega
        have hnn : n = n' := by omega
        subst hnn; subst hk2
        rcases S5 with ⟨e5, i5⟩ | ⟨e5, _, _⟩
        · have x1 := i5 n (by omega)
          have x2 := Io (n + 1) (by omega)
          have x3 := Ie n pn
          have x4 : b (n + 1 + 1) ≤ b (n + 1) := hc6
          linarith
        · omega
  · by_cases c : n + 1 < k1
    · have x1 := h2 c
      have x2 := Io (n + 1) (by omega)
      have x3 := s_le hd2 hi2 (i := n + 1 + 1) (j := n') hn' (by omega)
      linarith
    · rcases S5 with ⟨e, _⟩ | ⟨e, _, hc5⟩
      · omega
      · have hk1 : k1 = n + 1 := by omega
        have hnn : n' = n + 2 := by omega
        subst hk1; subst hnn
        rcases S6 with ⟨e6, i6⟩ | ⟨e6, _, _⟩
        · have x1 := Io (n + 1) (by omega)
          have x2 := i6 (n + 2) (by omega)
          have x3 := Ie (n + 2) (by omega)
          have x4 : a (n + 1 + 1) ≤ a (n + 1) := hc5
          linarith
        · omega

/-! ## 1. Resolving gaps: grant behaviour and exclusion at every gap -/

section resolve
variable (P : InvolutionPair)

/-- `r1 ∧ q` on a resolving orbit, as the padded finite sequence. -/
theorem in1_fin {s : ℝ} {m : ℕ} (hch : s ∈ chainS P m) (u : ℝ) :
    gr1 (decide (0 ≤ u)) (decide (s ≤ u)) (den (orb P s) (· < m) u)
      = den (ext (orb P s) m) (· < m) u := by
  have hd : DownC (fun n : ℕ => n < m) := fun n h => by omega
  have hi : Incr (orb P s) (fun n : ℕ => n < m) := fun n h => hch n (by
    have : n + 1 < m := h
    omega)
  rw [gr1_eq, den_r1 hd hi (fun _ => P.infUp_pos) u]
  exact congrFun (den_congr (fun _ => Iff.rfl) (fun n hn => (ext_lt hn).symm)) u

/-- `r2 ∧ ¬q` on a resolving orbit: transitions `s, o 0, ..., o (m-1)`. -/
theorem in2_fin {s : ℝ} (hsI : s < P.infUp) {m : ℕ} (hch : s ∈ chainS P m) (u : ℝ) :
    gr2 (decide (0 ≤ u)) (decide (s ≤ u)) (den (orb P s) (· < m) u)
      = den (cons1 s (ext (orb P s) m)) (· < m + 1) u := by
  have hd : DownC (fun n : ℕ => n < m) := fun n h => by omega
  have hi : Incr (orb P s) (fun n : ℕ => n < m) := fun n h => hch n (by
    have : n + 1 < m := h
    omega)
  rw [gr2_eq, den_r2 hd hi (fun _ => hsI) (fun _ => ⟨m, Or.inl (lt_irrefl m)⟩) u]
  refine congrFun (den_congr (fun n => ?_) (fun n hn => ?_)) u
  · match n with
    | 0 => exact ⟨fun _ => by omega, fun _ => trivial⟩
    | k + 1 => exact ⟨fun h => by
                  have : k < m := h
                  omega, fun h => (by omega : k < m)⟩
  · match n, hn with
    | 0, _ => rfl
    | k + 1, hn => exact (ext_lt (show k < m from hn)).symm

theorem orb_fin_incr {s : ℝ} {m : ℕ} (hch : s ∈ chainS P m) :
    ∀ j, j + 1 < m → orb P s j < orb P s (j + 1) := fun j h => hch j (by omega)

/-- **Resolving gaps: the grants settle to `(q, ¬q)`.** For every gap `0 < s < δ∞↑`
at which the loop does NOT oscillate forever, in every solution of the cell with its
grant LUT, there is a time after which `q`, `g1`, `g2` are constant, with `g1 = q` and
`g2 = ¬q`. So no grant is left stuck high by a final cancellation in its channel (a
cancellation removes a PAIR of edges and keeps the final value), and no grant pulses
forever: exactly the winner's grant is eventually held. No `BBM` needed. -/
theorem grants_resolve {G5 G6 : InvolutionPair} {s : ℝ} (hs : 0 < s) (hsI : s < P.infUp)
    (hno : ¬ Osc P s) {r1 r2 x qp y1 y2 g1 g2 : Sig}
    (A : AGrant P G5 G6 s r1 r2 x qp y1 y2 g1 g2) :
    ∃ T : ℝ, ∃ c : Bool, ∀ u, T ≤ u → qp u = c ∧ g1 u = c ∧ g2 u = !c := by
  rcases arb_q_orb P hs hsI A.loop with ⟨hosc, _⟩ | ⟨m, hch, _, hq⟩
  · exact absurd hosc hno
  set e := ext (orb P s) m with he
  have hinc : ∀ n, e n < e (n + 1) := ext_incr (orb_fin_incr P hch)
  have hinc1 := cons1_incr (ext_zero (m := m) (o := orb P s) hsI) hinc
  have hy1 : y1 = den e (· < m) := by
    funext u; rw [A.H_GLUT1, A.loop.H_R1, A.loop.H_R2, hq]; exact in1_fin P hch u
  have hy2 : y2 = den (cons1 s e) (· < m + 1) := by
    funext u; rw [A.H_GLUT2, A.loop.H_R1, A.loop.H_R2, hq]; exact in2_fin P hsI hch u
  obtain ⟨k1, e1, S5⟩ := run_fin G5 (fun n _ => hinc n) hy1 A.H_G5
  obtain ⟨k2, e2, S6⟩ := run_fin G6 (fun n _ => hinc1 n) hy2 A.H_G6
  have hqe : qp = den e (· < m) := by
    rw [hq]; exact den_congr (fun _ => Iff.rfl) (fun n hn => (ext_lt hn).symm)
  obtain ⟨T0, f0⟩ := den_final (z := e) (k := m) (fun n _ => hinc n)
  obtain ⟨T1, f1⟩ := den_final (z := G5.tent e) (k := k1) (fun n hn => by
    rcases S5 with ⟨h, i⟩ | ⟨h, i, _⟩
    · exact i n (by omega)
    · exact i n (by omega))
  obtain ⟨T2, f2⟩ := den_final (z := G6.tent (cons1 s e)) (k := k2) (fun n hn => by
    rcases S6 with ⟨h, i⟩ | ⟨h, i, _⟩
    · exact i n (by omega)
    · exact i n (by omega))
  refine ⟨max T0 (max T1 T2), decide (m % 2 = 1), fun u hu => ⟨?_, ?_, ?_⟩⟩
  · rw [hqe]; exact f0 u (le_trans (le_max_left _ _) hu)
  · rw [e1, f1 u (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hu)]
    have : k1 % 2 = m % 2 := by rcases S5 with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    rw [this]
  · rw [e2, f2 u (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hu)]
    have : k2 % 2 = (m + 1) % 2 := by rcases S6 with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    rw [this]
    rcases Nat.mod_two_eq_zero_or_one m with h | h
    · rw [decide_eq_true (by omega), decide_eq_false (by omega)]; rfl
    · rw [decide_eq_false (by omega), decide_eq_true (by omega)]; rfl

/-- **Exclusion at EVERY gap under `BBM`.** For every request gap `0 < s < δ∞↑`
(oscillating or resolving; any final cancellation in either grant channel), in every
solution of the cell with its grant LUT, `g1` and `g2` are never high at the same time,
provided the O5/O6 channels are break-before-make. -/
theorem grants_exclusive {G5 G6 : InvolutionPair} (H : BBM G5 G6) {s : ℝ} (hs : 0 < s)
    (hsI : s < P.infUp) {r1 r2 x qp y1 y2 g1 g2 : Sig}
    (A : AGrant P G5 G6 s r1 r2 x qp y1 y2 g1 g2) : ∀ u, (g1 u && g2 u) = false := by
  by_cases hosc : Osc P s
  · exact (arb_grants_eternal P hs hsI hosc A).2 H
  rcases arb_q_orb P hs hsI A.loop with ⟨hosc', _⟩ | ⟨m, hch, _, hq⟩
  · exact absurd hosc' hosc
  set e := ext (orb P s) m with he
  have hinc : ∀ n, e n < e (n + 1) := ext_incr (orb_fin_incr P hch)
  have hs0 : s < e 0 := ext_zero (m := m) (o := orb P s) hsI
  have hinc1 := cons1_incr hs0 hinc
  have hy1 : y1 = den e (· < m) := by
    funext u; rw [A.H_GLUT1, A.loop.H_R1, A.loop.H_R2, hq]; exact in1_fin P hch u
  have hy2 : y2 = den (cons1 s e) (· < m + 1) := by
    funext u; rw [A.H_GLUT2, A.loop.H_R1, A.loop.H_R2, hq]; exact in2_fin P hsI hch u
  obtain ⟨k1, e1, S5⟩ := run_fin G5 (fun n _ => hinc n) hy1 A.H_G5
  obtain ⟨k2, e2, S6⟩ := run_fin G6 (fun n _ => hinc1 n) hy2 A.H_G6
  have I := interleaveG H e hs0 hinc
  intro u
  rw [Bool.eq_false_iff]
  intro hh
  rw [Bool.and_eq_true, e1, e2, den_true, den_true] at hh
  exact excl_fin (fun n hn => (I n).1 hn) (fun n hn => (I n).2 hn) S5 S6 u hh

end resolve

/-! ## 2. Deriving H_GRANT_PASS from channel properties -/

/-- **H_PASS** (a property of one grant output's channel `G`): an ISOLATED pulse of
width `h`, of either polarity, survives `G` (A's `pulseWidth h > 0` for the high
pulse, and its mirror for the low pulse). Test: the pulse-shrink curve of that LUT
output, at input width `h`, both polarities. -/
structure Passes (G : InvolutionPair) (h : ℝ) : Prop where
  H_POS : 0 < h
  H_PASS_HI : 0 < (h - G.infUp) + G.down (h - G.infUp)
  H_PASS_LO : 0 < (h - G.infDown) + G.up (h - G.infDown)

/-- If input edges `n` and `n+1` are at least `h` apart and `G` passes isolated
`h`-pulses, tentative outputs `n` and `n+1` do not cancel (whatever the history). -/
theorem tent_step (G : InvolutionPair) {t : ℕ → ℝ} (ht : ∀ n, t n < t (n + 1)) {h : ℝ}
    (hp : Passes G h) (n : ℕ) (hn : h ≤ t (n + 1) - t n) :
    G.tent t n < G.tent t (n + 1) := by
  have hle := G.tent_le t ht n
  have e : G.tent t (n + 1) = t (n + 1) + G.delayAt (n + 1) (t (n + 1) - G.tent t n) := rfl
  rcases Nat.mod_two_eq_zero_or_one n with hpar | hpar
  · rw [infAt_even G hpar] at hle
    rw [e, delayAt_odd G (by omega)]
    have hm : G.down (h - G.infUp) ≤ G.down (t (n + 1) - G.tent t n) := by
      rcases eq_or_lt_of_le (show h - G.infUp ≤ t (n + 1) - G.tent t n by linarith) with q | q
      · rw [q]
      · exact le_of_lt (G.down_strictMono _ _ (by linarith [hp.H_POS]) q)
    linarith [hp.H_PASS_HI]
  · rw [infAt_odd G hpar] at hle
    rw [e, delayAt_even G (by omega)]
    have hm : G.up (h - G.infDown) ≤ G.up (t (n + 1) - G.tent t n) := by
      rcases eq_or_lt_of_le (show h - G.infDown ≤ t (n + 1) - G.tent t n by linarith) with q | q
      · rw [q]
      · exact le_of_lt (G.up_strictMono _ _ (by linarith [hp.H_POS]) q)
    linarith [hp.H_PASS_LO]

/-- A pulse-width margin `g` of the LOOP channel `P` (a definition, not an assumption;
`margin_exists` shows one always exists): a `q` pulse narrower than `g` makes the next
one so wide that the one after it cancels. -/
structure Margin (P : InvolutionPair) (g : ℝ) : Prop where
  pos : 0 < g
  ltU : g < P.infUp
  ltD : g < P.infDown
  condU : P.down (-(P.up (-g) - g)) ≤ P.up (-g) - g
  condD : P.up (-(P.down (-g) - g)) ≤ P.down (-g) - g

section margin
variable (P : InvolutionPair)

theorem margin_cond {g : ℝ} (hM : Margin P g) (n : ℕ) :
    g < P.infAt (n + 1) ∧
      P.delayAt (n + 1) (-(P.delayAt n (-g) - g)) ≤ P.delayAt n (-g) - g := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [infAt_odd P (by omega), delayAt_even P h, delayAt_odd P (by omega)]
    exact ⟨hM.ltD, hM.condU⟩
  · rw [infAt_even P (by omega), delayAt_odd P h, delayAt_even P (by omega)]
    exact ⟨hM.ltU, hM.condD⟩

/-- Two steps of the pulse-width map `v ↦ δ(-v) - v`: a pulse `0 < v < g` is followed
by a pulse whose successor has non-positive width (a cancellation). -/
theorem two_step (n : ℕ) {g v : ℝ} (hg : g < P.infAt (n + 1)) (hv0 : 0 < v) (hvg : v < g)
    (hc : P.delayAt (n + 1) (-(P.delayAt n (-g) - g)) ≤ P.delayAt n (-g) - g) :
    P.delayAt (n + 1) (-(P.delayAt n (-v) - v)) - (P.delayAt n (-v) - v) < 0 := by
  have d1 : P.delayAt n (-g) < P.delayAt n (-v) := dA_strictMono P n (by linarith) (by linarith)
  have l1 : P.delayAt n (-v) < P.infAt n := dA_lt P n (by linarith)
  have i2 : P.infAt (n + 1 + 1) = P.infAt n := infAt_add_two P n
  have d2 : P.delayAt (n + 1) (-(P.delayAt n (-v) - v))
      < P.delayAt (n + 1) (-(P.delayAt n (-g) - g)) :=
    dA_strictMono P (n + 1) (by rw [i2]; linarith) (by linarith)
  linarith

theorem gap_succ (s : ℝ) (n : ℕ) :
    orb P s (n + 2) - orb P s (n + 1)
      = P.delayAt n (-(orb P s (n + 1) - orb P s n)) - (orb P s (n + 1) - orb P s n) := by
  rw [orb_ss, show orb P s n - orb P s (n + 1) = -(orb P s (n + 1) - orb P s n) by ring]
  ring

/-- **Every `q` pulse except the last two is at least `g` wide.** On a chain of `M`
non-cancelled loop transitions, every gap `orb (n+1) - orb n` with `n + 2 < M` is at
least `g`, and so is the initial gap `δ∞↑ - s` (`r2`'s rise to `q`'s first rise, the
first pulse of `r2 ∧ ¬q`) if `M ≥ 2`. On an oscillating orbit this holds for ALL gaps. -/
theorem margin_orb {g : ℝ} (hM : Margin P g) {s : ℝ} (hsI : s < P.infUp) {M : ℕ}
    (hch : s ∈ chainS P M) :
    (∀ n, n + 2 < M → g ≤ orb P s (n + 1) - orb P s n) ∧ (1 < M → g ≤ P.infUp - s) := by
  constructor
  · intro n hn
    by_contra hlt
    push Not at hlt
    have hv0 : 0 < orb P s (n + 1) - orb P s n := by have := hch n (by omega); linarith
    obtain ⟨hg, hc⟩ := margin_cond P hM n
    have k := two_step P n hg hv0 hlt hc
    have e1 := gap_succ P s n
    have e2 : orb P s (n + 3) - orb P s (n + 2) = P.delayAt (n + 1)
        (-(orb P s (n + 2) - orb P s (n + 1))) - (orb P s (n + 2) - orb P s (n + 1)) :=
      gap_succ P s (n + 1)
    rw [e1] at e2
    have := hch (n + 2) (by omega)
    linarith
  · intro hM1
    by_contra hlt
    push Not at hlt
    obtain ⟨hg, hc⟩ := margin_cond P hM 1
    have k := two_step P 1 hg (by linarith : 0 < P.infUp - s) hlt hc
    have e0 : orb P s 1 - orb P s 0 = P.delayAt 1 (-(P.infUp - s)) - (P.infUp - s) := by
      show s + P.down (s - P.infUp) - P.infUp = _
      rw [delayAt_odd P (by rfl), show s - P.infUp = -(P.infUp - s) by ring]; ring
    have e1 := gap_succ P s 0
    rw [e0, show P.delayAt 0 = P.delayAt (1 + 1) from (delayAt_add_two P 0).symm] at e1
    have := hch 1 (by omega)
    linarith

/-- **A margin always exists** (continuity of A's delay functions on their domains,
proved in 5e from strict monotonicity; no extra hypothesis). -/
theorem margin_exists : ∃ g, Margin P g := by
  have hu : ContinuousAt P.up (-(0 : ℝ)) := up_contAt P (by rw [neg_zero]; linarith [P.infDown_pos])
  have hd : ContinuousAt P.down (-(0 : ℝ)) := down_contAt P (by rw [neg_zero]; linarith [P.infUp_pos])
  have c1 : ContinuousAt (fun g : ℝ => P.up (-g) - g) 0 := (hu.comp continuousAt_neg).sub continuousAt_id
  have c2 : ContinuousAt (fun g : ℝ => P.down (-g) - g) 0 := (hd.comp continuousAt_neg).sub continuousAt_id
  have hd' : ContinuousAt P.down (-((fun g : ℝ => P.up (-g) - g) 0)) :=
    down_contAt P (by simp only [neg_zero, sub_zero]; linarith [P.up_lt 0 (by linarith [P.infDown_pos])])
  have hu' : ContinuousAt P.up (-((fun g : ℝ => P.down (-g) - g) 0)) :=
    up_contAt P (by simp only [neg_zero, sub_zero]; linarith [P.down_lt 0 (by linarith [P.infUp_pos])])
  have c3 : ContinuousAt (fun g : ℝ => P.down (-(P.up (-g) - g)) - (P.up (-g) - g)) 0 :=
    (ContinuousAt.comp (g := P.down) (f := fun g : ℝ => -(P.up (-g) - g)) (x := 0) hd' c1.neg).sub c1
  have c4 : ContinuousAt (fun g : ℝ => P.up (-(P.down (-g) - g)) - (P.down (-g) - g)) 0 :=
    (ContinuousAt.comp (g := P.up) (f := fun g : ℝ => -(P.down (-g) - g)) (x := 0) hu' c2.neg).sub c2
  have v3 : (fun g : ℝ => P.down (-(P.up (-g) - g)) - (P.up (-g) - g)) 0 < (fun _ => (0 : ℝ)) 0 := by
    have := P.down_neg_up (T := 0) (by linarith [P.infDown_pos])
    simp only [neg_zero, sub_zero] at this ⊢
    rw [this]; linarith [P.up_causal]
  have v4 : (fun g : ℝ => P.up (-(P.down (-g) - g)) - (P.down (-g) - g)) 0 < (fun _ => (0 : ℝ)) 0 := by
    have := P.up_neg_down (T := 0) (by linarith [P.infUp_pos])
    simp only [neg_zero, sub_zero] at this ⊢
    rw [this]; linarith [P.down_causal]
  have ev := (c3.eventually_lt continuousAt_const v3).and (c4.eventually_lt continuousAt_const v4)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp ev
  set g := min (ε / 2) (min (P.infUp / 2) (P.infDown / 2)) with hgdef
  have g1 : g ≤ ε / 2 := min_le_left _ _
  have g2 : g ≤ P.infUp / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have g3 : g ≤ P.infDown / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  have gpos : 0 < g := lt_min (by linarith) (lt_min (by linarith [P.infUp_pos])
    (by linarith [P.infDown_pos]))
  obtain ⟨b3, b4⟩ := hball (y := g) (by rw [Real.dist_eq, sub_zero, abs_of_pos gpos]; linarith)
  exact ⟨g, gpos, by linarith [P.infUp_pos], by linarith [P.infDown_pos],
    by simp only at b3; linarith, by simp only at b4; linarith⟩

end margin

/-- Build a fragment run on a finite input whose interior tentative outputs do not
cancel: the last pair either cancels (shape 2) or not (shape 3). -/
theorem run_of_prefix (G : InvolutionPair) {t : ℕ → ℝ} {K : ℕ}
    (ht : ∀ n, n + 1 < K → t n < t (n + 1))
    (hpre : ∀ n, n + 2 < K → G.tent t n < G.tent t (n + 1)) :
    ∃ okO, InvRun G t (· < K) okO := by
  have hd : DownC (fun n : ℕ => n < K) := fun n h => by omega
  have hi : Incr t (fun n : ℕ => n < K) := fun n h => ht n h
  rcases K with _ | _ | j
  · exact ⟨(· < 0), hd, hi, Or.inr (Or.inr ⟨0, fun _ => Iff.rfl, fun _ => Iff.rfl,
      fun n h => absurd h (by omega)⟩)⟩
  · exact ⟨(· < 1), hd, hi, Or.inr (Or.inr ⟨1, fun _ => Iff.rfl, fun _ => Iff.rfl,
      fun n h => absurd h (by omega)⟩)⟩
  · by_cases c : G.tent t (j + 1) ≤ G.tent t j
    · exact ⟨(· < j), hd, hi, Or.inr (Or.inl ⟨j, fun _ => Iff.rfl, fun _ => Iff.rfl,
        fun n hn => hpre n (by omega), c⟩)⟩
    · refine ⟨(· < j + 2), hd, hi, Or.inr (Or.inr ⟨j + 2, fun _ => Iff.rfl, fun _ => Iff.rfl,
        fun n hn => ?_⟩)⟩
      by_cases h : n < j
      · exact hpre n (by omega)
      · have : n = j := by omega
        subst this; exact not_le.mp c

section exist
variable (P : InvolutionPair)

/-- **Non-vacuity at EVERY gap, `H_GRANT_PASS` derived.** Let `g` be a margin of the
loop channel (`margin_exists`). If both grant outputs pass isolated pulses of width
`g` (`Passes`, per output), then for every gap `0 < s < δ∞↑` the cell with its grant
LUT has a solution. At an oscillating gap this discharges 7m's `H_GRANT_PASS5/6`;
at a resolving gap the only cancellation the grant channels can make is of the last
`q` pulse, which the fragment covers. -/
theorem grants_exist_all {G5 G6 : InvolutionPair} {g : ℝ} (hM : Margin P g)
    (p5 : Passes G5 g) (p6 : Passes G6 g) {s : ℝ} (hs : 0 < s) (hsI : s < P.infUp) :
    ∃ x qp y1 y2 g1 g2 : Sig, AGrant P G5 G6 s r1R (r2R s) x qp y1 y2 g1 g2 := by
  by_cases hosc : Osc P s
  · have mg : ∀ n, g ≤ orb P s (n + 1) - orb P s n := fun n =>
      (margin_orb P hM hsI (M := n + 3) (fun j _ => hosc j)).1 n (by omega)
    have mw : g ≤ P.infUp - s := (margin_orb P hM hsI (M := 2) (fun j _ => hosc j)).2 (by omega)
    refine grants_exist P hs hsI hosc (fun n => tent_step G5 hosc p5 n (mg n))
      (fun n => tent_step G6 (cons1_incr hsI hosc) p6 n ?_)
    match n with
    | 0 => exact mw
    | k + 1 => exact mg k
  · obtain ⟨x, qp, L⟩ := arb_exists P hs hsI
    rcases arb_q_orb P hs hsI L with ⟨h, _⟩ | ⟨m, hch, _, hq⟩
    · exact absurd h hosc
    have mg := margin_orb P hM hsI hch
    set e := ext (orb P s) m with he
    have hinc : ∀ n, e n < e (n + 1) := ext_incr (orb_fin_incr P hch)
    have hinc1 := cons1_incr (ext_zero (m := m) (o := orb P s) hsI) hinc
    obtain ⟨ok5, R5⟩ := run_of_prefix G5 (t := e) (K := m) (fun n _ => hinc n)
      (fun n hn => tent_step G5 hinc p5 n (by
        rw [he, ext_lt (by omega), ext_lt (by omega)]; exact mg.1 n hn))
    obtain ⟨ok6, R6⟩ := run_of_prefix G6 (t := cons1 s e) (K := m + 1) (fun n _ => hinc1 n)
      (fun n hn => tent_step G6 hinc1 p6 n (by
        match n, hn with
        | 0, hn =>
          show g ≤ e 0 - s
          rw [he, ext_lt (by omega)]; exact mg.2 (by omega)
        | k + 1, hn =>
          show g ≤ e (k + 1) - e k
          rw [he, ext_lt (by omega), ext_lt (by omega)]; exact mg.1 k (by omega)))
    refine ⟨x, qp, den e (· < m), den (cons1 s e) (· < m + 1), den (G5.tent e) ok5,
      den (G6.tent (cons1 s e)) ok6, L, fun u => ?_, fun u => ?_,
      ⟨e, _, _, R5, rfl, rfl⟩, ⟨_, _, _, R6, rfl, rfl⟩⟩
    · rw [hq]; exact (in1_fin P hch u).symm
    · rw [hq]; exact (in2_fin P hsI hch u).symm

/-- The same with the margin chosen automatically: there is `g > 0`, depending only on
the loop channel `P`, such that any grant channels passing `g`-pulses give a solution
at every gap. -/
theorem grants_exist_auto : ∃ g > 0, ∀ G5 G6 : InvolutionPair, Passes G5 g → Passes G6 g →
    ∀ s, 0 < s → s < P.infUp →
      ∃ x qp y1 y2 g1 g2 : Sig, AGrant P G5 G6 s r1R (r2R s) x qp y1 y2 g1 g2 := by
  obtain ⟨g, hM⟩ := margin_exists P
  exact ⟨g, hM.pos, fun G5 G6 p5 p6 s hs hsI => grants_exist_all P hM p5 p6 hs hsI⟩

end exist

/-! ## 3. The mirror scenario: reset `q = 1`, `r2` first -/

/-- The involution pair with `δ↑` and `δ↓` exchanged (again an involution pair: A's
fields map to each other). -/
def swapP (P : InvolutionPair) : InvolutionPair where
  up := P.down
  down := P.up
  infUp := P.infDown
  infDown := P.infUp
  infUp_pos := P.infDown_pos
  infDown_pos := P.infUp_pos
  up_lt := P.down_lt
  down_lt := P.up_lt
  up_strictMono := P.down_strictMono
  down_strictMono := P.up_strictMono
  inv_up := P.inv_down
  inv_down := P.inv_up
  up_causal := P.down_causal
  down_causal := P.up_causal

/-- The REAL `bd_c2n_set` INIT is symmetric under `r1 ↔ r2`, `q ↔ ¬q`. -/
theorem stF_mirror (a b q : Bool) : (!stF a b q) = stF b a (!q) := by
  cases a <;> cases b <;> cases q <;> rfl

/-- The REAL grant INIT exchanges O5 and O6 under the same symmetry. -/
theorem gr_mirror1 (a b q : Bool) : gr1 a b q = gr2 b a (!q) := by
  cases a <;> cases b <;> cases q <;> rfl

theorem gr_mirror2 (a b q : Bool) : gr2 a b q = gr1 b a (!q) := by
  cases a <;> cases b <;> cases q <;> rfl

theorem bbm_comm {G5 G6 : InvolutionPair} (H : BBM G5 G6) : BBM G6 G5 := ⟨H.H_BBM2, H.H_BBM1⟩

/-- **The mirror loop.** Every field is a named hypothesis.
* `H_R1`, `H_R2`: `r2` rises first at `0`, `r1` at `s` (both from idle).
* `H_LUT`: the REAL INIT `stF`, zero time (as 7m).
* `H_CH1`: the LUT+feedback channel `P`, with `q` idle at 1 (reset value 1, the last
  winner was side 1). A channel idle at 1 is modelled through complements: `¬x ↦ ¬q`
  is A's channel with `δ↑ ↔ δ↓` (`swapP P`), idle at 0. Physically: the first edge
  of the run is a FALL of `x`, and it gets the falling delay `δ∞↓`. -/
structure ALoopM (P : InvolutionPair) (s : ℝ) (r1 r2 x qp : Sig) : Prop where
  H_R1 : ∀ u, r1 u = decide (s ≤ u)
  H_R2 : ∀ u, r2 u = decide (0 ≤ u)
  H_LUT : ∀ u, x u = stF (r1 u) (r2 u) (qp u)
  H_CH1 : InvChanF (swapP P) (fun u => !x u) (fun u => !qp u)

/-- The mirror cell with its grant LUT (fields as in 7m's `AGrant`). The grants are
idle at 0 also in the mirror (`r1 = r2 = 0`), so their channels are unchanged. -/
structure AGrantM (P G5 G6 : InvolutionPair) (s : ℝ) (r1 r2 x qp y1 y2 g1 g2 : Sig) : Prop where
  loop : ALoopM P s r1 r2 x qp
  H_GLUT1 : ∀ u, y1 u = gr1 (r1 u) (r2 u) (qp u)
  H_GLUT2 : ∀ u, y2 u = gr2 (r1 u) (r2 u) (qp u)
  H_G5 : InvChanF G5 y1 g1
  H_G6 : InvChanF G6 y2 g2

section mirror
variable (P : InvolutionPair)

/-- Every mirror loop solution is a 7m loop solution for `swapP P`, with requests
exchanged and `x`, `q` complemented. -/
theorem toA {s : ℝ} {r1 r2 x qp : Sig} (L : ALoopM P s r1 r2 x qp) :
    ALoop (swapP P) s r2 r1 (fun u => !x u) (fun u => !qp u) :=
  ⟨L.H_R2, L.H_R1, fun u => by
    show (!x u) = stF (r2 u) (r1 u) (!qp u)
    rw [L.H_LUT, stF_mirror], L.H_CH1⟩

/-- Every mirror cell solution is a 7m cell solution for `swapP P` with O5/O6 (and
`G5`/`G6`, `g1`/`g2`) exchanged. -/
theorem toAG {G5 G6 : InvolutionPair} {s : ℝ} {r1 r2 x qp y1 y2 g1 g2 : Sig}
    (A : AGrantM P G5 G6 s r1 r2 x qp y1 y2 g1 g2) :
    AGrant (swapP P) G6 G5 s r2 r1 (fun u => !x u) (fun u => !qp u) y2 y1 g2 g1 :=
  ⟨toA P A.loop, fun u => by rw [A.H_GLUT2, gr_mirror2], fun u => by rw [A.H_GLUT1, gr_mirror1],
    A.H_G6, A.H_G5⟩

theorem not_not_fun (f : Sig) : (fun u => !!f u) = f := funext fun _ => Bool.not_not _

/-- Mirror existence: every gap `0 < s < δ∞↓` has a mirror loop solution. -/
theorem arbM_exists {s : ℝ} (hs : 0 < s) (hsI : s < P.infDown) :
    ∃ x qp : Sig, ALoopM P s (r2R s) r1R x qp := by
  obtain ⟨x, qp, L⟩ := arb_exists (swapP P) hs hsI
  refine ⟨fun u => !x u, fun u => !qp u, fun _ => rfl, fun _ => rfl, fun u => ?_, ?_⟩
  · show (!x u) = stF (r2R s u) (r1R u) (!qp u)
    rw [L.H_LUT, stF_mirror]
  · rw [not_not_fun, not_not_fun]; exact L.H_CH

/-- **Mirror goal 1.** There is a critical gap `s*' ∈ (δ∞↓ - δ↓(0), δ∞↓)` (the one of
`swapP P`; it differs from 7m's `s*` unless `δ↑ = δ↓`) at which the mirror loop has a
solution, and in every solution `q` takes both values after every time bound. -/
theorem arbM_eternal : ∃ s, lft (swapP P) < s ∧ s < P.infDown ∧
    (∃ x qp : Sig, ALoopM P s (r2R s) r1R x qp) ∧
    ∀ r1 r2 x qp : Sig, ALoopM P s r1 r2 x qp →
      ∀ B : ℝ, (∃ u, B < u ∧ qp u = true) ∧ (∃ u, B < u ∧ qp u = false) := by
  obtain ⟨c, h1, h2, _, hall⟩ := arb_eternal (swapP P)
  have hc0 : 0 < c := lt_trans (lft_pos _) h1
  refine ⟨c, h1, h2, arbM_exists P hc0 h2, fun r1 r2 x qp L B => ?_⟩
  obtain ⟨⟨u, hu, e⟩, ⟨v, hv, f⟩⟩ := hall _ _ _ _ (toA P L) B
  exact ⟨⟨v, hv, by simpa using f⟩, ⟨u, hu, by simpa using e⟩⟩

/-- **Mirror goal 2.** Arbitrarily close below the mirror critical gap, every solution
resolves with `q` eventually 1 (`r1`, the LATER request, wins), yet `q` is still 0
after any given time `B`. -/
theorem arbM_slow_resolution : ∃ c, lft (swapP P) < c ∧ c < P.infDown ∧ Osc (swapP P) c ∧
    ∀ ε > 0, ∀ B : ℝ, ∃ s, c - ε < s ∧ s < c ∧
      (∃ x qp : Sig, ALoopM P s (r2R s) r1R x qp) ∧
      ∀ r1 r2 x qp : Sig, ALoopM P s r1 r2 x qp →
        (∃ u, B < u ∧ qp u = false) ∧ (∃ T, ∀ u, T ≤ u → qp u = true) := by
  obtain ⟨c, h1, h2, hosc, hall⟩ := arb_slow_resolution (swapP P)
  refine ⟨c, h1, h2, hosc, fun ε hε B => ?_⟩
  have hcl : 0 < c - lft (swapP P) := by linarith
  obtain ⟨s, hs1, hs2, _, hsol⟩ := hall (min ε (c - lft (swapP P))) (lt_min hε hcl) B
  have hm1 : min ε (c - lft (swapP P)) ≤ ε := min_le_left _ _
  have hm2 : min ε (c - lft (swapP P)) ≤ c - lft (swapP P) := min_le_right _ _
  have hs0 : 0 < s := by linarith [lft_pos (swapP P)]
  have h2' : c < P.infDown := h2
  have hsI : s < P.infDown := by linarith
  refine ⟨s, by linarith, hs2, arbM_exists P hs0 hsI, fun r1 r2 x qp L => ?_⟩
  obtain ⟨⟨u, hu, e⟩, ⟨T, hT⟩⟩ := hsol _ _ _ _ (toA P L)
  exact ⟨⟨u, hu, by simpa using e⟩, ⟨T, fun v hv => by simpa using hT v hv⟩⟩

/-- **Mirror goal 3 and exclusion.** At an oscillating mirror gap both grants pulse
forever; at EVERY mirror gap `0 < s < δ∞↓`, `BBM G5 G6` (equivalently `BBM G6 G5`)
excludes `g1 ∧ g2`; at a resolving mirror gap the grants settle to `(q, ¬q)`. -/
theorem grantsM_eternal {G5 G6 : InvolutionPair} {s : ℝ} (hs : 0 < s) (hsI : s < P.infDown)
    (hosc : Osc (swapP P) s) {r1 r2 x qp y1 y2 g1 g2 : Sig}
    (A : AGrantM P G5 G6 s r1 r2 x qp y1 y2 g1 g2) :
    ∀ B : ℝ, (∃ u, B < u ∧ g1 u = true) ∧ (∃ u, B < u ∧ g1 u = false) ∧
      (∃ u, B < u ∧ g2 u = true) ∧ (∃ u, B < u ∧ g2 u = false) := by
  intro B
  obtain ⟨a, b, c, d⟩ := (arb_grants_eternal (swapP P) hs hsI hosc (toAG P A)).1 B
  exact ⟨c, d, a, b⟩

theorem grantsM_exclusive {G5 G6 : InvolutionPair} (H : BBM G5 G6) {s : ℝ} (hs : 0 < s)
    (hsI : s < P.infDown) {r1 r2 x qp y1 y2 g1 g2 : Sig}
    (A : AGrantM P G5 G6 s r1 r2 x qp y1 y2 g1 g2) : ∀ u, (g1 u && g2 u) = false := by
  intro u
  rw [Bool.and_comm]
  exact grants_exclusive (swapP P) (bbm_comm H) hs hsI (toAG P A) u

theorem grantsM_resolve {G5 G6 : InvolutionPair} {s : ℝ} (hs : 0 < s) (hsI : s < P.infDown)
    (hno : ¬ Osc (swapP P) s) {r1 r2 x qp y1 y2 g1 g2 : Sig}
    (A : AGrantM P G5 G6 s r1 r2 x qp y1 y2 g1 g2) :
    ∃ T : ℝ, ∃ c : Bool, ∀ u, T ≤ u → qp u = c ∧ g1 u = c ∧ g2 u = !c := by
  obtain ⟨T, c, h⟩ := grants_resolve (swapP P) hs hsI hno (toAG P A)
  refine ⟨T, !c, fun u hu => ?_⟩
  obtain ⟨h1, h2, h3⟩ := h u hu
  have h1' : qp u = !c := by rw [← h1]; simp
  exact ⟨h1', h3, by rw [h2]; simp⟩

/-- Mirror non-vacuity: with a margin of `swapP P` and grant channels passing it,
every mirror gap has a solution. -/
theorem grantsM_exist_auto : ∃ g > 0, ∀ G5 G6 : InvolutionPair, Passes G5 g → Passes G6 g →
    ∀ s, 0 < s → s < P.infDown →
      ∃ x qp y1 y2 g1 g2 : Sig, AGrantM P G5 G6 s (r2R s) r1R x qp y1 y2 g1 g2 := by
  obtain ⟨g, gpos, hall⟩ := grants_exist_auto (swapP P)
  refine ⟨g, gpos, fun G5 G6 p5 p6 s hs hsI => ?_⟩
  obtain ⟨x, qp, y2, y1, g2, g1, A⟩ := hall G6 G5 p6 p5 s hs hsI
  refine ⟨fun u => !x u, fun u => !qp u, y1, y2, g1, g2,
    ⟨⟨fun _ => rfl, fun _ => rfl, fun u => ?_, ?_⟩, fun u => ?_, fun u => ?_, A.H_G6, A.H_G5⟩⟩
  · show (!x u) = stF (r2R s u) (r1R u) (!qp u)
    rw [A.loop.H_LUT, A.loop.H_R1, A.loop.H_R2, stF_mirror]
  · rw [not_not_fun, not_not_fun]; exact A.loop.H_CH
  · show y1 u = gr1 (r2R s u) (r1R u) (!qp u)
    rw [A.H_GLUT2, A.loop.H_R1, A.loop.H_R2, gr_mirror2]
  · show y2 u = gr2 (r2R s u) (r1R u) (!qp u)
    rw [A.H_GLUT1, A.loop.H_R1, A.loop.H_R2, gr_mirror1]

end mirror

/-! ## 4. A concrete triple with an exact critical gap and a reachable overlap -/

/-- **A hyperbolic involution pair** (explicit, rational): `δ↑ T = A - k/(T+B)`,
`δ↓ T = B - k/(T+A)`, `δ∞↑ = A`, `δ∞↓ = B`, causal iff `k < A·B`. All of A's fields are
proved. It is NOT A's exp-channel (that one is only abstract, `ExpLog`, in claimed
code); it is a member of A's channel class chosen because every quantity is rational,
so orbits and first edges can be computed exactly. -/
noncomputable def hyp (A B k : ℝ) (hA : 0 < A) (hB : 0 < B) (hk : 0 < k) (hkAB : k < A * B) :
    InvolutionPair where
  up := fun T => A - k / (T + B)
  down := fun T => B - k / (T + A)
  infUp := A
  infDown := B
  infUp_pos := hA
  infDown_pos := hB
  up_lt := fun T hT => by have : 0 < k / (T + B) := div_pos hk (by linarith); linarith
  down_lt := fun T hT => by have : 0 < k / (T + A) := div_pos hk (by linarith); linarith
  up_strictMono := fun a b ha hab => by
    have := div_lt_div_of_pos_left hk (by linarith : 0 < a + B) (by linarith : a + B < b + B)
    linarith
  down_strictMono := fun a b ha hab => by
    have := div_lt_div_of_pos_left hk (by linarith : 0 < a + A) (by linarith : a + A < b + A)
    linarith
  inv_up := fun T _ => by
    show -(A - k / (-(B - k / (T + A)) + B)) = T
    rw [show -(B - k / (T + A)) + B = k / (T + A) by ring, div_div_cancel₀ hk.ne']
    ring
  inv_down := fun T _ => by
    show -(B - k / (-(A - k / (T + B)) + A)) = T
    rw [show -(A - k / (T + B)) + A = k / (T + B) by ring, div_div_cancel₀ hk.ne']
    ring
  up_causal := by
    show 0 < A - k / (0 + B)
    rw [zero_add]
    have := (div_lt_iff₀ hB).mpr hkAB
    linarith
  down_causal := by
    show 0 < B - k / (0 + A)
    rw [zero_add]
    have := (div_lt_iff₀ hA).mpr (show k < B * A by rw [mul_comm]; exact hkAB)
    linarith

/-- Loop channel: symmetric, `δ∞ = 1`, `k = 3/8` (`δ(0) = 5/8`). -/
noncomputable def Pc : InvolutionPair := hyp 1 1 (3 / 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
/-- O5 channel: symmetric, `δ∞ = 1/4`, `k = 1/128`. -/
noncomputable def G5c : InvolutionPair :=
  hyp (1 / 4) (1 / 4) (1 / 128) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
/-- O6 channel: symmetric, `δ∞ = 5/16` (25% slower than O5), `k = 1/128`. -/
noncomputable def G6c : InvolutionPair :=
  hyp (5 / 16) (5 / 16) (1 / 128) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem Pc_delay (n : ℕ) (T : ℝ) : Pc.delayAt n T = 1 - 3 / 8 / (T + 1) := by
  unfold InvolutionPair.delayAt
  split_ifs <;> rfl

/-- **The critical gap of `Pc` is exactly `3/4`**: the loop orbit is `q` edges at
`1 + n/4`, a square wave of half-period `1/4`, forever. -/
theorem Pc_orb : ∀ n : ℕ, orb Pc (3 / 4) n = 1 + (n : ℝ) / 4 := by
  have h : ∀ n : ℕ, orb Pc (3 / 4) n = 1 + (n : ℝ) / 4 ∧
      orb Pc (3 / 4) (n + 1) = 1 + ((n : ℝ) + 1) / 4 := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_⟩
      · show (1 : ℝ) = 1 + ((0 : ℕ) : ℝ) / 4
        simp
      · show (3 / 4 : ℝ) + (1 - 3 / 8 / ((3 / 4 - 1) + 1)) = 1 + (((0 : ℕ) : ℝ) + 1) / 4
        norm_num
    | succ n ih =>
      refine ⟨by rw [ih.2]; push_cast; ring, ?_⟩
      have e : orb Pc (3 / 4) (n + 1 + 1) = orb Pc (3 / 4) n
          + Pc.delayAt n (orb Pc (3 / 4) n - orb Pc (3 / 4) (n + 1)) := orb_ss Pc _ n
      rw [e, Pc_delay, ih.1, ih.2,
        show 1 + (n : ℝ) / 4 - (1 + ((n : ℝ) + 1) / 4) + 1 = 3 / 4 by ring]
      push_cast
      ring
  exact fun n => (h n).1

theorem Pc_gap (n : ℕ) : orb Pc (3 / 4) (n + 1) - orb Pc (3 / 4) n = 1 / 4 := by
  rw [Pc_orb, Pc_orb]; push_cast; ring

theorem Pc_osc : Osc Pc (3 / 4) := fun n => by linarith [Pc_gap n]

theorem Pc_sI : (3 / 4 : ℝ) < Pc.infUp := by show (3 / 4 : ℝ) < 1; norm_num

theorem G5c_pass : Passes G5c (1 / 4) :=
  ⟨by norm_num,
   by show (0 : ℝ) < (1 / 4 - 1 / 4) + (1 / 4 - 1 / 128 / ((1 / 4 - 1 / 4) + 1 / 4)); norm_num,
   by show (0 : ℝ) < (1 / 4 - 1 / 4) + (1 / 4 - 1 / 128 / ((1 / 4 - 1 / 4) + 1 / 4)); norm_num⟩

theorem G6c_pass : Passes G6c (1 / 4) :=
  ⟨by norm_num,
   by show (0 : ℝ) < (1 / 4 - 5 / 16) + (5 / 16 - 1 / 128 / ((1 / 4 - 5 / 16) + 5 / 16)); norm_num,
   by show (0 : ℝ) < (1 / 4 - 5 / 16) + (5 / 16 - 1 / 128 / ((1 / 4 - 5 / 16) + 5 / 16)); norm_num⟩

theorem c_pass5 : ∀ n, G5c.tent (orb Pc (3 / 4)) n < G5c.tent (orb Pc (3 / 4)) (n + 1) :=
  fun n => tent_step G5c Pc_osc G5c_pass n (le_of_eq (Pc_gap n).symm)

theorem c_pass6 : ∀ n, G6c.tent (cons1 (3 / 4) (orb Pc (3 / 4))) n
    < G6c.tent (cons1 (3 / 4) (orb Pc (3 / 4))) (n + 1) := by
  intro n
  refine tent_step G6c (cons1_incr Pc_sI Pc_osc) G6c_pass n ?_
  match n with
  | 0 =>
    show (1 / 4 : ℝ) ≤ orb Pc (3 / 4) 0 - 3 / 4
    rw [Pc_orb]; norm_num
  | k + 1 => exact le_of_eq (Pc_gap k).symm

/-- **Overlap is reachable.** For the concrete loop `Pc` at its critical gap `3/4`
and the concrete O5/O6 channels `G5c`, `G6c` (both symmetric hyperbolic, O6 25% slower):
* the cell with its grant LUT has a solution (`H_GRANT_PASS` discharged by `Passes`);
* in EVERY solution both grants pulse forever, and `g1`, `g2` are high at the same
  time (first edge: `g1` rises at `5/4`, `g2` falls at `41/32`; `g2` rose at `17/16`
  and `g1` falls at `47/32`);
* consequently `BBM G5c G6c` fails. -/
theorem overlap_reachable :
    Osc Pc (3 / 4) ∧
    (∃ x qp y1 y2 g1 g2 : Sig, AGrant Pc G5c G6c (3 / 4) r1R (r2R (3 / 4)) x qp y1 y2 g1 g2) ∧
    (∀ r1 r2 x qp y1 y2 g1 g2 : Sig, AGrant Pc G5c G6c (3 / 4) r1 r2 x qp y1 y2 g1 g2 →
      (∀ B : ℝ, (∃ u, B < u ∧ g1 u = true) ∧ (∃ u, B < u ∧ g1 u = false) ∧
        (∃ u, B < u ∧ g2 u = true) ∧ (∃ u, B < u ∧ g2 u = false)) ∧
      ∃ u, g1 u = true ∧ g2 u = true) ∧
    ¬ BBM G5c G6c := by
  have hs : (0 : ℝ) < 3 / 4 := by norm_num
  have hex := grants_exist Pc hs Pc_sI Pc_osc c_pass5 c_pass6
  have hab : G5c.tent (orb Pc (3 / 4)) 0 < G6c.tent (cons1 (3 / 4) (orb Pc (3 / 4))) 1 := by
    rw [first_edge_iff]
    show (1 / 4 : ℝ) < 5 / 16 - 1 / 128 / ((1 - (3 / 4 + 5 / 16)) + 5 / 16)
    norm_num
  have hba : G6c.tent (cons1 (3 / 4) (orb Pc (3 / 4))) 0 < G5c.tent (orb Pc (3 / 4)) 1 := by
    show (3 / 4 : ℝ) + 5 / 16 < orb Pc (3 / 4) 1
      + G5c.delayAt 1 (orb Pc (3 / 4) 1 - (orb Pc (3 / 4) 0 + 1 / 4))
    rw [delayAt_odd G5c (by rfl), Pc_orb, Pc_orb]
    show (3 / 4 : ℝ) + 5 / 16 < (1 + ((1 : ℕ) : ℝ) / 4)
      + (1 / 4 - 1 / 128 / (((1 + ((1 : ℕ) : ℝ) / 4) - ((1 + ((0 : ℕ) : ℝ) / 4) + 1 / 4)) + 1 / 4))
    norm_num
  have hall : ∀ r1 r2 x qp y1 y2 g1 g2 : Sig,
      AGrant Pc G5c G6c (3 / 4) r1 r2 x qp y1 y2 g1 g2 →
      (∀ B : ℝ, (∃ u, B < u ∧ g1 u = true) ∧ (∃ u, B < u ∧ g1 u = false) ∧
        (∃ u, B < u ∧ g2 u = true) ∧ (∃ u, B < u ∧ g2 u = false)) ∧
      ∃ u, g1 u = true ∧ g2 u = true := fun r1 r2 x qp y1 y2 g1 g2 A =>
    ⟨(arb_grants_eternal Pc hs Pc_sI Pc_osc A).1,
      first_edge_overlap Pc hs Pc_sI Pc_osc A hab hba⟩
  refine ⟨Pc_osc, hex, hall, fun H => ?_⟩
  obtain ⟨x, qp, y1, y2, g1, g2, A⟩ := hex
  obtain ⟨u, h1, h2⟩ := (hall _ _ _ _ _ _ _ _ A).2
  have := (arb_grants_eternal Pc hs Pc_sI Pc_osc A).2 H u
  rw [h1, h2] at this
  exact Bool.noConfusion this

end Formal.Cells.ArbInvolution2
