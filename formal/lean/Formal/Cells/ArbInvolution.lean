import Formal.Cells.CElemInvolution
import Formal.Cells.ArbBinary

/-!
# Track 7, probe 7m: arbiter metastability from the binary gate model (involution channel)

Cells (real INITs, through `Prelim.lutB` / `o5B` / `o6B`, as decoded in probe 7a's
`Formal.Cells.ArbBinary`):
* `bd_arbcell` state node `q` = `bd_c2n_set`, INIT `0xFFB2FFB2FFB2FFB2`, pins
  `I0=r1 I1=r2 I2=q I3=rst(=0)`; `stF_eq`: `q' = r1.~r2 + q.~(~r1.r2)` = `C(r1, ~r2)`.
* grant LUT6_2 INIT `0x0C0C0C0CA0A0A0A0`, pins `I0=r1 I1=r2 I2=q I5=1`,
  `O5 = g1 = r1.q`, `O6 = g2 = r2.~q` (`gr1_eq`, `gr2_eq`).

Gate model (Fuegger, Najvirt, Nowak, Schmid): a ZERO-TIME Boolean function followed
by an involution channel (shard A's `InvolutionPair`, transition semantics `tent`,
signal-level fragment relation `InvChanF` of probe 5e).

Input scenario (probe 7a's runt): both requests rise from idle, `r1` at `0`, `r2` at
`s`, `0 < s < δ∞↑` (less than one loop delay). Before `0` the loop is idle with
`q = 0` (every `den` signal is 0 at `-∞`).

Contents.
1. `stF_runt`: on this input the state LUT computes exactly the OR loop of probe 5e,
   `bR s ∨ q` with `bR s = [0, s)`: the set literal `r1.~r2` is a runt of width `s`
   and afterwards `r1 = r2 = 1` holds `q`. Hence (`to_CLoop`) every arbiter loop
   solution IS a 5e `CLoop`, and all of 5e's loop theorems transfer:
   `arb_q_orb`, `arb_exists`, `arb_eternal` (goal 1), `arb_slow_resolution` (goal 2).
2. The grant LUT (`AGrant`): O5 and O6 are two involution channels `G5`, `G6` fed by
   the zero-time grant functions of the same pins `r1`, `r2`, `q`.
   * `grants_osc`: at the critical gap, the grant inputs are `den (orb)` and
     `den (s :: orb)`, every grant-channel run is cancellation-free, and the grants
     are `den (G5.tent orb)` and `den (G6.tent (s :: orb))`.
   * `interleave`: under `H_BBM` (fall-before-rise between the two outputs), the
     tentative grant edges interleave `b(2k) < b(2k+1) < a(2k) < a(2k+1) < b(2k+2)`.
   * `arb_grants_eternal` (goal 3): at the critical gap both grants pulse forever,
     and under `H_BBM` they are NEVER simultaneously high.
   * `sym_bbm`: identical symmetric O5/O6 channels (e.g. A's exp-channel,
     `exp_bbm`) satisfy `H_BBM`.
   * `first_edge_overlap`: if the first `q` rise makes `g1` rise before `g2` falls
     (a violation of `H_BBM` at the first edge), `g1` and `g2` ARE both high.
   * `grants_exist`: at the critical gap the grant equations have a solution if
     neither grant channel cancels (`H_GRANT_PASS`); by `grants_osc` this is
     also necessary, so without it the grant theorems are vacuous (the
     fragment `InvChanF` has no run with an interior cancellation).
-/

namespace Formal.Cells.ArbInvolution
open Formal.Cells
open Formal.Cells.CElemInvolution
open Formal.Cells.CElemTiming (exc INIT_c2)
open Formal.Cells.ArbBinary (stF gr1 gr2 stF_eq gr1_eq gr2_eq)
open Formal.Core.DelayInvolution

/-! ## 1. The state loop is 5e's OR loop -/

/-- The request pins: `r1` rises at `0`, `r2` rises at `s` (same sense, both from idle). -/
noncomputable def r1R : Sig := fun u => decide (0 ≤ u)
noncomputable def r2R (s : ℝ) : Sig := fun u => decide (s ≤ u)

/-- On the runt input, the REAL `bd_c2n_set` INIT computes the same function of time
and `q` as `bd_c2` with `a = 1`, `b = [0, s)`, `rst = 0` (5e's loop): `[0,s) ∨ q`. -/
theorem stF_runt {s : ℝ} (hs : 0 < s) (u : ℝ) (q : Bool) :
    stF (r1R u) (r2R s u) q = exc INIT_c2 true (bR s u) q false := by
  rw [exc_or, stF_eq]
  unfold r1R r2R bR
  rcases lt_or_ge u 0 with h | h
  · have h1 : decide (0 ≤ u) = false := decide_eq_false (by intro hh; linarith)
    have h2 : decide (s ≤ u) = false := decide_eq_false (by intro hh; linarith)
    have h3 : decide (0 ≤ u ∧ u < s) = false := decide_eq_false (by intro hh; linarith [hh.1])
    rw [h1, h2, h3]; cases q <;> rfl
  · rcases lt_or_ge u s with h' | h'
    · have h1 : decide (0 ≤ u) = true := decide_eq_true h
      have h2 : decide (s ≤ u) = false := decide_eq_false (by intro hh; linarith)
      have h3 : decide (0 ≤ u ∧ u < s) = true := decide_eq_true ⟨h, h'⟩
      rw [h1, h2, h3]; cases q <;> rfl
    · have h1 : decide (0 ≤ u) = true := decide_eq_true h
      have h2 : decide (s ≤ u) = true := decide_eq_true h'
      have h3 : decide (0 ≤ u ∧ u < s) = false := decide_eq_false (by intro hh; linarith [hh.2])
      rw [h1, h2, h3]; cases q <;> rfl

/-- **The `bd_arbcell` state loop, Fuegger gate model.** Every field is a named
hypothesis.
* `H_R1`, `H_R2`: the request pins (as seen at the state LUT): `r1` rises at `0`,
  `r2` at `s`. Both from idle; the idle `q = 0` is built into `InvChanF` (signals
  start at 0). (`rst` is the constant 0 inside `stF`.)
* `H_LUT`: the state LUT applies the REAL INIT `0xFFB2..` (`stF`, via `lutB`) in
  ZERO time.
* `H_CH`: LUT + feedback route to `I2` are ONE involution channel `P`
  (5e's `InvChanF` fragment). Test: pulse-shrink curve of LUT + route (A's notes). -/
structure ALoop (P : InvolutionPair) (s : ℝ) (r1 r2 x qp : Sig) : Prop where
  H_R1 : ∀ u, r1 u = decide (0 ≤ u)
  H_R2 : ∀ u, r2 u = decide (s ≤ u)
  H_LUT : ∀ u, x u = stF (r1 u) (r2 u) (qp u)
  H_CH : InvChanF P x qp

section loop
variable (P : InvolutionPair)

/-- Every arbiter loop solution is a solution of 5e's `bd_c2` OR loop with runt width `s`. -/
theorem to_CLoop {s : ℝ} (hs : 0 < s) {r1 r2 x qp : Sig} (L : ALoop P s r1 r2 x qp) :
    CLoop P s aR (bR s) rstR x qp :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun u => by
      rw [L.H_LUT, L.H_R1, L.H_R2]
      exact stF_runt hs u (qp u),
    L.H_CH⟩

/-- **Derived recurrence**: for `0 < s < δ∞↑`, every solution's `q` has the
transition times `orb P s` (5e's orbit), forever or up to the first cancellation. -/
theorem arb_q_orb {s : ℝ} (hs : 0 < s) (hsI : s < P.infUp) {r1 r2 x qp : Sig}
    (L : ALoop P s r1 r2 x qp) :
    (Osc P s ∧ qp = den (orb P s) (fun _ => True)) ∨
    (∃ m, s ∈ chainS P m ∧ orb P s (m + 1) ≤ orb P s m ∧
      qp = den (orb P s) (fun n => n < m)) :=
  loop_orb P hs hsI (to_CLoop P hs L)

/-- **Existence**: for every gap `0 < s < δ∞↑` the arbiter loop has a solution. -/
theorem arb_exists {s : ℝ} (hs : 0 < s) (hsI : s < P.infUp) :
    ∃ x qp : Sig, ALoop P s r1R (r2R s) x qp := by
  obtain ⟨x, qp, L⟩ := loop_exists P hs hsI
  refine ⟨x, qp, fun _ => rfl, fun _ => rfl, fun u => ?_, L.H_CH⟩
  rw [stF_runt hs u (qp u)]
  exact L.H_LUT u

/-- **Goal 1: eternal oscillation of the arbiter's q.** There is a critical gap
`s* ∈ (δ∞↑ - δ↑(0), δ∞↑)` between the two same-sense request rises such that the
arbiter loop has a solution, and in EVERY solution `q` takes both values after
every time bound `B`. -/
theorem arb_eternal : ∃ s, lft P < s ∧ s < P.infUp ∧
    (∃ x qp : Sig, ALoop P s r1R (r2R s) x qp) ∧
    ∀ r1 r2 x qp : Sig, ALoop P s r1 r2 x qp →
      ∀ B : ℝ, (∃ u, B < u ∧ qp u = true) ∧ (∃ u, B < u ∧ qp u = false) := by
  obtain ⟨c, hlc, hcI, _, hall⟩ := c2_eternal P
  have hc0 : 0 < c := lt_trans (lft_pos P) hlc
  exact ⟨c, hlc, hcI, arb_exists P hc0 hcI,
    fun r1 r2 x qp L => hall _ _ _ _ _ (to_CLoop P hc0 L)⟩

/-- **Goal 2: unbounded resolution time.** With `s*` the critical gap (it oscillates
forever), for every `ε > 0` and every time `B` there is a gap `s ∈ (s* - ε, s*)`
whose loop has a solution, and in EVERY solution `q` is eventually 0 (the runt is
LOST: `r2`, the LATER request, wins) yet `q` is still 1 at some time after `B`. -/
theorem arb_slow_resolution : ∃ c, lft P < c ∧ c < P.infUp ∧ Osc P c ∧
    ∀ ε > 0, ∀ B : ℝ, ∃ s, c - ε < s ∧ s < c ∧
      (∃ x qp : Sig, ALoop P s r1R (r2R s) x qp) ∧
      ∀ r1 r2 x qp : Sig, ALoop P s r1 r2 x qp →
        (∃ u, B < u ∧ qp u = true) ∧ (∃ T, ∀ u, T ≤ u → qp u = false) := by
  obtain ⟨c, hlc, hcI, hosc, hall⟩ := c2_slow_resolution P
  refine ⟨c, hlc, hcI, hosc, fun ε hε B => ?_⟩
  have hcl : 0 < c - lft P := by linarith
  obtain ⟨s, h1, h2, _, h4⟩ := hall (min ε (c - lft P)) (lt_min hε hcl) B
  have hm1 : min ε (c - lft P) ≤ ε := min_le_left _ _
  have hm2 : min ε (c - lft P) ≤ c - lft P := min_le_right _ _
  have hs0 : 0 < s := by linarith [lft_pos P]
  have hsI : s < P.infUp := by linarith
  exact ⟨s, by linarith, h2, arb_exists P hs0 hsI,
    fun r1 r2 x qp L => h4 _ _ _ _ _ (to_CLoop P hs0 L)⟩

end loop

/-! ## 2. The grant LUT -/

/-- Prepend one input transition (the rise of `r2 ∧ ¬q` at `s`). -/
def cons1 (a : ℝ) (o : ℕ → ℝ) : ℕ → ℝ
  | 0 => a
  | n + 1 => o n

def ok1 (ok : ℕ → Prop) : ℕ → Prop
  | 0 => True
  | n + 1 => ok n

section sig
variable {o : ℕ → ℝ} {ok : ℕ → Prop}

theorem down_ok1 (hd : DownC ok) : DownC (ok1 ok) := by
  intro n hn
  match n, hn with
  | 0, _ => trivial
  | k + 1, hn => exact hd k hn

theorem incr_cons1 {s : ℝ} (hs : ok 0 → s < o 0) (hi : Incr o ok) : Incr (cons1 s o) (ok1 ok) := by
  intro n hn
  match n, hn with
  | 0, hn => exact hs hn
  | k + 1, hn => exact hi k hn

/-- Locate a time between two consecutive active transitions. -/
theorem locate {u : ℝ} (h0 : ok 0) (hu : o 0 ≤ u)
    (hfin : ∃ n, ¬ ok n ∨ u < o n) : ∃ n, ok n ∧ o n ≤ u ∧ (ok (n + 1) → u < o (n + 1)) := by
  classical
  have hN := Nat.find_spec hfin
  obtain ⟨k, hk⟩ : ∃ k, Nat.find hfin = k + 1 := by
    rcases h : Nat.find hfin with _ | k
    · rw [h] at hN
      rcases hN with hN | hN
      · exact absurd h0 hN
      · linarith
    · exact ⟨k, rfl⟩
  have hmin := Nat.find_min hfin (show k < Nat.find hfin by omega)
  rw [hk] at hN
  push Not at hmin
  exact ⟨k, hmin.1, hmin.2, fun o1 => hN.resolve_left (fun h => h o1)⟩

/-- `r1 ∧ q = q` when `q` only rises after `0`. -/
theorem den_r1 (hd : DownC ok) (hi : Incr o ok) (h0 : ok 0 → 0 < o 0) (u : ℝ) :
    (decide (0 ≤ u) && den o ok u) = den o ok u := by
  by_cases h : 0 ≤ u
  · rw [decide_eq_true h, Bool.true_and]
  · rw [decide_eq_false h, Bool.false_and, eq_comm, Bool.eq_false_iff]
    intro hh
    exact hi_before hd hi (fun o0 => by have := h0 o0; push Not at h; linarith) (den_true.mp hh)

/-- `r2 ∧ ¬q` is the signal with transitions `s, o 0, o 1, ...`. -/
theorem den_r2 {s : ℝ} (hd : DownC ok) (hi : Incr o ok) (hs : ok 0 → s < o 0)
    (hcov : ∀ u, ∃ n, ¬ ok n ∨ u < o n) (u : ℝ) :
    (decide (s ≤ u) && !den o ok u) = den (cons1 s o) (ok1 ok) u := by
  have hd1 := down_ok1 hd
  have hi1 := incr_cons1 hs hi
  by_cases hb : ok 0 ∧ o 0 ≤ u
  · obtain ⟨n, okn, h1, h2⟩ := locate hb.1 hb.2 (hcov u)
    have hsu : s ≤ u := by linarith [hs hb.1, s_le hd hi okn (Nat.zero_le n)]
    have e1 : Hi o ok u ↔ n % 2 = 0 := hi_iff hd hi okn h1 h2
    have e2 : Hi (cons1 s o) (ok1 ok) u ↔ (n + 1) % 2 = 0 :=
      hi_iff hd1 hi1 (n := n + 1) okn h1 h2
    have q1 : den o ok u = decide (n % 2 = 0) := by
      rw [Bool.eq_iff_iff, den_true, decide_eq_true_iff]; exact e1
    have q2 : den (cons1 s o) (ok1 ok) u = decide ((n + 1) % 2 = 0) := by
      rw [Bool.eq_iff_iff, den_true, decide_eq_true_iff]; exact e2
    rw [decide_eq_true hsu, Bool.true_and, q1, q2]
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · rw [decide_eq_true h, decide_eq_false (by omega)]; rfl
    · rw [decide_eq_false (by omega), decide_eq_true (by omega)]; rfl
  · have hq : ¬ Hi o ok u := hi_before hd hi (fun o0 => by
      push Not at hb; exact hb o0)
    rw [Bool.eq_false_iff.mpr (fun h => hq (den_true.mp h)), Bool.not_false, Bool.and_true]
    by_cases hsu : s ≤ u
    · rw [decide_eq_true hsu, eq_comm, den_true]
      refine (hi_iff hd1 hi1 (n := 0) trivial hsu (fun o0 => ?_)).mpr rfl
      push Not at hb; exact hb o0
    · rw [decide_eq_false hsu, eq_comm, Bool.eq_false_iff]
      intro hh
      exact hi_before hd1 hi1 (fun _ => by push Not at hsu; exact hsu) (den_true.mp hh)

end sig

/-- **The arbiter cell with its grant LUT.** Every field is a named hypothesis.
* `loop`: the state loop (`ALoop`).
* `H_GLUT1`, `H_GLUT2`: the grant LUT applies the REAL INIT `0x0C0C0C0CA0A0A0A0`
  (`gr1` = O5, `gr2` = O6 via `o5B`/`o6B`) in ZERO time to the SAME request
  signals and the SAME `q` signal as the state LUT reads (H_NO_PIN_SKEW: no
  routing skew between the two LUTs' copies of `r1`, `r2`, `q`; all of a LUT's
  delay is in its output channels). Test: routed SDF, the two `q` and request
  arcs into `ustate` / `ugrant`.
* `H_G5`, `H_G6`: O5 and O6 are separate involution channels `G5`, `G6`
  (`InvChanF`). Test: pulse-shrink curves per output and edge. -/
structure AGrant (P G5 G6 : InvolutionPair) (s : ℝ) (r1 r2 x qp y1 y2 g1 g2 : Sig) : Prop where
  loop : ALoop P s r1 r2 x qp
  H_GLUT1 : ∀ u, y1 u = gr1 (r1 u) (r2 u) (qp u)
  H_GLUT2 : ∀ u, y2 u = gr2 (r1 u) (r2 u) (qp u)
  H_G5 : InvChanF G5 y1 g1
  H_G6 : InvChanF G6 y2 g2

/-- **H_BBM** (break before make between O5 and O6): at a `q` rise the O6 fall
beats the O5 rise, at a `q` fall the O5 fall beats the O6 rise, whenever the
falling output's history argument is the smaller one. Physical content: each
output's fall delay is not longer than the other output's rise delay at the same
history. Test: rise/fall arcs of `ugrant` O5/O6 (SDF, pulse-shrink curves). -/
structure BBM (G5 G6 : InvolutionPair) : Prop where
  H_BBM1 : ∀ x y, -G6.infUp < x → x < y → -G5.infDown < y → G6.down x < G5.up y
  H_BBM2 : ∀ x y, -G5.infUp < x → x < y → -G6.infDown < y → G5.down x < G6.up y

/-- Identical, symmetric (`δ↑ = δ↓`) O5/O6 channels satisfy `H_BBM`. -/
theorem sym_bbm (G : InvolutionPair) (hsym : G.up = G.down) : BBM G G := by
  refine ⟨fun x y hx hxy _ => ?_, fun x y hx hxy _ => ?_⟩
  · rw [hsym]; exact G.down_strictMono x y hx hxy
  · rw [hsym]; exact G.down_strictMono x y hx hxy

/-- In particular A's exp-channel (first-order RC + pure delay, same for both
outputs) satisfies `H_BBM`. -/
theorem exp_bbm (X : ExpLog) (Tp : ℝ) (hTp : 0 < Tp) :
    BBM (X.expPair Tp hTp) (X.expPair Tp hTp) := sym_bbm _ rfl

section grants
variable (P : InvolutionPair)

/-- Tentative outputs only depend on the inputs up to the same index. -/
theorem tent_congr (G : InvolutionPair) {t t' : ℕ → ℝ} {N : ℕ} (h : ∀ n ≤ N, t n = t' n) :
    ∀ n ≤ N, G.tent t n = G.tent t' n := by
  intro n
  induction n with
  | zero => intro _; show t 0 + G.infUp = t' 0 + G.infUp; rw [h 0 (Nat.zero_le _)]
  | succ n ih =>
    intro hn
    show t (n + 1) + G.delayAt (n + 1) (t (n + 1) - G.tent t n)
      = t' (n + 1) + G.delayAt (n + 1) (t' (n + 1) - G.tent t' n)
    rw [h (n + 1) hn, ih (by omega)]

/-- An output that never cancels lags its input: `tent t n > t n`. -/
theorem tent_gt (G : InvolutionPair) {t : ℕ → ℝ} (hc : ∀ n, G.tent t n < G.tent t (n + 1)) :
    ∀ n, t n < G.tent t n := by
  intro n
  induction n with
  | zero => show t 0 < t 0 + G.infUp; linarith [G.infUp_pos]
  | succ n ih =>
    by_cases h : G.tent t n ≤ t (n + 1)
    · have hm : G.delayAt (n + 1) 0 ≤ G.delayAt (n + 1) (t (n + 1) - G.tent t n) :=
        dA_mono G (n + 1) (by linarith [infAt_pos G (n + 1 + 1)]) (by linarith)
      have hp := dA_pos G (n + 1)
      show t (n + 1) < t (n + 1) + G.delayAt (n + 1) (t (n + 1) - G.tent t n)
      linarith
    · push Not at h; linarith [hc n]

/-- At the critical (oscillating) gap: the grant channel inputs are `den (orb)`
and `den (s :: orb)`, both grant runs are cancellation-free, and the grants are
the alternating signals of `G5.tent orb` and `G6.tent (s :: orb)`. -/
theorem grants_osc {G5 G6 : InvolutionPair} {s : ℝ} (hs : 0 < s) (hsI : s < P.infUp)
    (hosc : Osc P s) {r1 r2 x qp y1 y2 g1 g2 : Sig}
    (A : AGrant P G5 G6 s r1 r2 x qp y1 y2 g1 g2) :
    (∀ n, G5.tent (orb P s) n < G5.tent (orb P s) (n + 1)) ∧
    (∀ n, G6.tent (cons1 s (orb P s)) n < G6.tent (cons1 s (orb P s)) (n + 1)) ∧
    g1 = den (G5.tent (orb P s)) (fun _ => True) ∧
    g2 = den (G6.tent (cons1 s (orb P s))) (fun _ => True) := by
  have hqp : qp = den (orb P s) (fun _ => True) := by
    rcases arb_q_orb P hs hsI A.loop with ⟨_, h⟩ | ⟨m, _, hf, _⟩
    · exact h
    · exact absurd (hosc m) (not_lt.mpr hf)
  have hd : DownC (fun _ : ℕ => True) := fun _ _ => trivial
  have hi : Incr (orb P s) (fun _ => True) := fun n _ => hosc n
  have h00 : (0 : ℝ) < orb P s 0 := P.infUp_pos
  have hcov : ∀ u, ∃ n, ¬ (fun _ : ℕ => True) n ∨ u < orb P s n := by
    intro u
    obtain ⟨k, hk⟩ := osc_unbounded P hosc u
    exact ⟨2 * k, Or.inr hk⟩
  have hy1 : y1 = den (orb P s) (fun _ => True) := by
    funext u
    rw [A.H_GLUT1, gr1_eq, A.loop.H_R1, hqp]
    exact den_r1 hd hi (fun _ => h00) u
  have hy2 : y2 = den (cons1 s (orb P s)) (ok1 (fun _ => True)) := by
    funext u
    rw [A.H_GLUT2, gr2_eq, A.loop.H_R2, hqp]
    exact den_r2 hd hi (fun _ => hsI) hcov u
  have hd1 : DownC (ok1 (fun _ : ℕ => True)) := down_ok1 hd
  have hi1 : Incr (cons1 s (orb P s)) (ok1 (fun _ => True)) := incr_cons1 (fun _ => hsI) hi
  have hall1 : ∀ n, ok1 (fun _ : ℕ => True) n := fun n => by
    match n with
    | 0 => trivial
    | _ + 1 => trivial
  -- a channel run whose input denotes an infinite sequence is cancellation-free
  have key : ∀ (G : InvolutionPair) (o : ℕ → ℝ) (oko : ℕ → Prop) (y g : Sig),
      DownC oko → Incr o oko → (∀ n, oko n) → y = den o oko → InvChanF G y g →
      (∀ n, G.tent o n < G.tent o (n + 1)) ∧ g = den (G.tent o) (fun _ => True) := by
    intro G o oko y g hdo hio hallo hy hch
    obtain ⟨t, ok, okO, R, hx, hg⟩ := hch
    have hinj := den_inj R.down R.incr hdo hio (hx.symm.trans hy)
    have hok : ∀ n, ok n := fun n => (hinj n).1.mpr (hallo n)
    have ht : t = o := funext fun n => (hinj n).2 (hok n)
    subst ht
    rcases R.out with ⟨_, hallO, hinc⟩ | ⟨m, hm1, _, _, _⟩ | ⟨N, hN1, _, _⟩
    · exact ⟨hinc, hg.trans (den_congr (fun n => ⟨fun _ => trivial, fun _ => hallO n⟩)
        (fun _ _ => rfl))⟩
    · exact absurd ((hm1 (m + 2)).mp (hok _)) (by omega)
    · exact absurd ((hN1 N).mp (hok _)) (by omega)
  obtain ⟨c1, e1⟩ := key G5 _ _ y1 g1 hd hi (fun _ => trivial) hy1 A.H_G5
  obtain ⟨c2, e2⟩ := key G6 _ _ y2 g2 hd1 hi1 hall1 hy2 A.H_G6
  exact ⟨c1, c2, e1, e2⟩

/-- **Interleaving of the tentative grant edges** under `H_BBM`: writing
`a = G5.tent orb` (g1) and `b = G6.tent (s :: orb)` (g2), at every `q` edge `n`
the falling grant moves first: `b (n+1) < a n` for a `q` rise (even `n`),
`a n < b (n+1)` for a `q` fall (odd `n`). -/
theorem interleave {G5 G6 : InvolutionPair} (H : BBM G5 G6) {s : ℝ} (hsI : s < P.infUp)
    (hosc : Osc P s) :
    ∀ n, (n % 2 = 0 → G6.tent (cons1 s (orb P s)) (n + 1) < G5.tent (orb P s) n) ∧
      (n % 2 = 1 → G5.tent (orb P s) n < G6.tent (cons1 s (orb P s)) (n + 1)) := by
  set o := orb P s with ho
  set a := G5.tent o with ha
  set b := G6.tent (cons1 s o) with hb
  have hinc : ∀ n, o n < o (n + 1) := hosc
  have hinc1 : ∀ n, cons1 s o n < cons1 s o (n + 1) := by
    intro n
    match n with
    | 0 => exact hsI
    | k + 1 => exact hinc k
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
    · -- `n` even: `q` fell at `n + 1`: g1 falls before g2 rises
      have hI := ih.1 hn
      refine ⟨fun h => absurd h (by omega), fun _ => ?_⟩
      have dA := domA n
      rw [infAt_even G5 hn] at dA
      have dB := domB (n + 1)
      rw [infAt_odd G6 (by omega)] at dB
      rw [ea n, eb (n + 1), delayAt_odd G5 (by omega), delayAt_even G6 (by omega)]
      have := H.H_BBM2 (o (n + 1) - a n) (o (n + 1) - b (n + 1)) dA (by linarith) dB
      linarith
    · -- `n` odd: `q` rose at `n + 1`: g2 falls before g1 rises
      have hI := ih.2 hn
      refine ⟨fun _ => ?_, fun h => absurd h (by omega)⟩
      have dA := domA n
      rw [infAt_odd G5 hn] at dA
      have dB := domB (n + 1)
      rw [infAt_even G6 (by omega)] at dB
      rw [ea n, eb (n + 1), delayAt_even G5 (by omega), delayAt_odd G6 (by omega)]
      have := H.H_BBM1 (o (n + 1) - b (n + 1)) (o (n + 1) - a n) dB (by linarith) dA
      linarith

/-- **Goal 3: during the eternal oscillation both grants pulse forever, and
under `H_BBM` they are never high together.** At the critical gap `s*` of
`arb_eternal`: in every solution of the cell with its grant LUT, `g1` and `g2`
each take both values after every time bound; if moreover `H_BBM` holds, then
`g1 u && g2 u = false` at every time `u`. -/
theorem arb_grants_eternal {G5 G6 : InvolutionPair} {s : ℝ} (hs : 0 < s) (hsI : s < P.infUp)
    (hosc : Osc P s) {r1 r2 x qp y1 y2 g1 g2 : Sig}
    (A : AGrant P G5 G6 s r1 r2 x qp y1 y2 g1 g2) :
    (∀ B : ℝ, (∃ u, B < u ∧ g1 u = true) ∧ (∃ u, B < u ∧ g1 u = false) ∧
      (∃ u, B < u ∧ g2 u = true) ∧ (∃ u, B < u ∧ g2 u = false)) ∧
    (BBM G5 G6 → ∀ u, (g1 u && g2 u) = false) := by
  obtain ⟨c1, c2, e1, e2⟩ := grants_osc P hs hsI hosc A
  set o := orb P s
  set a := G5.tent o
  set b := G6.tent (cons1 s o)
  have hd : DownC (fun _ : ℕ => True) := fun _ _ => trivial
  have hia : Incr a (fun _ => True) := fun n _ => c1 n
  have hib : Incr b (fun _ => True) := fun n _ => c2 n
  have gta : ∀ n, o n < a n := tent_gt G5 c1
  have gtb : ∀ n, o n < b (n + 1) := fun n => tent_gt G6 c2 (n + 1)
  have val : ∀ (z : ℕ → ℝ), Incr z (fun _ => True) → ∀ n,
      den z (fun _ => True) (z n) = decide (n % 2 = 0) := by
    intro z hz n
    rw [Bool.eq_iff_iff, den_true, decide_eq_true_iff]
    exact hi_iff hd hz trivial (le_refl _) (fun _ => hz n trivial)
  refine ⟨fun B => ?_, fun H u => ?_⟩
  · obtain ⟨k, hk⟩ := osc_unbounded P hosc B
    refine ⟨⟨a (2 * k), by linarith [gta (2 * k)], ?_⟩,
      ⟨a (2 * k + 1), by linarith [gta (2 * k), c1 (2 * k)], ?_⟩,
      ⟨b (2 * k + 2), by linarith [gtb (2 * k + 1), hosc (2 * k)], ?_⟩,
      ⟨b (2 * k + 3), by linarith [gtb (2 * k + 1), hosc (2 * k), c2 (2 * k + 2)], ?_⟩⟩
    · rw [e1, val a hia]; exact decide_eq_true (by omega)
    · rw [e1, val a hia]; exact decide_eq_false (by omega)
    · rw [e2, val b hib]; exact decide_eq_true (by omega)
    · rw [e2, val b hib]; exact decide_eq_false (by omega)
  · have I := interleave P H hsI hosc
    rw [Bool.eq_false_iff]
    intro hh
    rw [Bool.and_eq_true, e1, e2, den_true, den_true] at hh
    obtain ⟨⟨n, pn, _, h1, h2⟩, ⟨n', pn', _, h1', h2'⟩⟩ := hh
    have h2 := h2 trivial
    have h2' := h2' trivial
    rcases le_or_gt n' n with hle | hlt
    · have := s_le hd hib (i := n' + 1) (j := n + 1) trivial (by omega)
      have := (I n).1 pn
      linarith
    · have := s_le hd hib (i := n + 2) (j := n') trivial (by omega)
      have := (I (n + 1)).2 (by omega)
      linarith

/-- **The first edge decides whether `H_BBM` can be dropped.** If at the first `q`
rise the O5 rise `a 0` comes before the O6 fall `b 1`, and `g2` has risen before
`g1`'s first fall, then `g1` and `g2` ARE both high (at `max (a 0) (b 0)`). This
happens iff `G5.δ∞↑ < G6.δ↓(δ∞↑(P) - s - G6.δ∞↑)` (with the second condition):
O6's fall slower than O5's saturated rise, i.e. O5/O6 skew. -/
theorem first_edge_overlap {G5 G6 : InvolutionPair} {s : ℝ} (hs : 0 < s) (hsI : s < P.infUp)
    (hosc : Osc P s) {r1 r2 x qp y1 y2 g1 g2 : Sig}
    (A : AGrant P G5 G6 s r1 r2 x qp y1 y2 g1 g2)
    (hab : G5.tent (orb P s) 0 < G6.tent (cons1 s (orb P s)) 1)
    (hba : G6.tent (cons1 s (orb P s)) 0 < G5.tent (orb P s) 1) :
    ∃ u, g1 u = true ∧ g2 u = true := by
  obtain ⟨c1, c2, e1, e2⟩ := grants_osc P hs hsI hosc A
  set a := G5.tent (orb P s)
  set b := G6.tent (cons1 s (orb P s))
  have hd : DownC (fun _ : ℕ => True) := fun _ _ => trivial
  refine ⟨max (a 0) (b 0), ?_, ?_⟩
  · rw [e1, den_true]
    exact (hi_iff hd (fun n _ => c1 n) trivial (le_max_left _ _)
      (fun _ => max_lt (c1 0) hba)).mpr rfl
  · rw [e2, den_true]
    exact (hi_iff hd (fun n _ => c2 n) trivial (le_max_right _ _)
      (fun _ => max_lt hab (c2 0))).mpr rfl

/-- `a 0 < b 1` in channel terms. -/
theorem first_edge_iff {G5 G6 : InvolutionPair} {s : ℝ} :
    G5.tent (orb P s) 0 < G6.tent (cons1 s (orb P s)) 1 ↔
      G5.infUp < G6.down (P.infUp - (s + G6.infUp)) := by
  show P.infUp + G5.infUp < P.infUp + G6.delayAt 1 (P.infUp - (s + G6.infUp)) ↔ _
  rw [delayAt_odd G6 (by rfl)]
  constructor <;> intro h <;> linarith

/-- **Non-vacuity of the grant theorems.** At an oscillating gap, if neither grant
channel cancels on its input (`H_GRANT_PASS`: the tentative edges of O5 on `orb`
and of O6 on `s :: orb` are increasing), the cell with its grant LUT has a
solution. (Every solution is cancellation-free, `grants_osc`; so
`H_GRANT_PASS` is also necessary.) -/
theorem grants_exist {G5 G6 : InvolutionPair} {s : ℝ} (hs : 0 < s) (hsI : s < P.infUp)
    (hosc : Osc P s)
    (H_GRANT_PASS5 : ∀ n, G5.tent (orb P s) n < G5.tent (orb P s) (n + 1))
    (H_GRANT_PASS6 : ∀ n, G6.tent (cons1 s (orb P s)) n < G6.tent (cons1 s (orb P s)) (n + 1)) :
    ∃ x qp y1 y2 g1 g2 : Sig, AGrant P G5 G6 s r1R (r2R s) x qp y1 y2 g1 g2 := by
  obtain ⟨x, qp, L⟩ := arb_exists P hs hsI
  have hqp : qp = den (orb P s) (fun _ => True) := by
    rcases arb_q_orb P hs hsI L with ⟨_, h⟩ | ⟨m, _, hf, _⟩
    · exact h
    · exact absurd (hosc m) (not_lt.mpr hf)
  have hd : DownC (fun _ : ℕ => True) := fun _ _ => trivial
  have hi : Incr (orb P s) (fun _ => True) := fun n _ => hosc n
  have hcov : ∀ u, ∃ n, ¬ (fun _ : ℕ => True) n ∨ u < orb P s n := by
    intro u
    obtain ⟨k, hk⟩ := osc_unbounded P hosc u
    exact ⟨2 * k, Or.inr hk⟩
  have hall1 : ∀ n, ok1 (fun _ : ℕ => True) n := fun n => by
    match n with
    | 0 => trivial
    | _ + 1 => trivial
  refine ⟨x, qp, den (orb P s) (fun _ => True), den (cons1 s (orb P s)) (fun _ => True),
    den (G5.tent (orb P s)) (fun _ => True), den (G6.tent (cons1 s (orb P s))) (fun _ => True),
    L, fun u => ?_, fun u => ?_, ?_, ?_⟩
  · rw [gr1_eq, hqp]
    exact (den_r1 hd hi (fun _ => P.infUp_pos) u).symm
  · rw [gr2_eq, hqp]
    show _ = (decide (s ≤ u) && !den (orb P s) (fun _ => True) u)
    rw [den_r2 hd hi (fun _ => hsI) hcov u]
    exact congrFun (den_congr (fun n => ⟨fun _ => hall1 n, fun _ => trivial⟩) (fun _ _ => rfl)) u
  · exact ⟨orb P s, _, _, ⟨hd, hi, Or.inl ⟨fun _ => trivial, fun _ => trivial, H_GRANT_PASS5⟩⟩,
      rfl, rfl⟩
  · refine ⟨cons1 s (orb P s), _, _, ⟨hd, fun n _ => ?_,
      Or.inl ⟨fun _ => trivial, fun _ => trivial, H_GRANT_PASS6⟩⟩, rfl, rfl⟩
    exact incr_cons1 (ok := fun _ => True) (fun _ => hsI) hi n (hall1 _)

end grants

end Formal.Cells.ArbInvolution
