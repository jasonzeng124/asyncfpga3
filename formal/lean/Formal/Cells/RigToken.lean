import Formal.Cells.ResetContract
import Formal.Net.Handshake

/-!
# Probe Bu (shard B): the rig's initial token `uenv1` and C's H_START_ONCE

Notes: `formal/notes/B-rig-token.md`.

## The ring (cells/hw/gcd_rig.v)

    bd_c2n     uenv0 (.a(res_req), .b(env_c),  .rst(rst), .q(env_c0));   // reset 0
    bd_c2n_set uenv1 (.a(env_c0),  .b(in_ack), .rst(rst), .q(env_c));    // reset 1
    assign res_ack = env_c0;  assign out0_ack = res_ack;
    bd_fork #(3) ufork (.req(env_c), .ack(in_ack), ...);   // start_req = a_req = b_req = env_c (wires)
    bd_delay #(16) urdly (.a(out0_req), .z(res_req));

Both cells are one LUT6 with feedback `O -> I2` and `rst` on `I3` (INITs
`00B2..`/`FFB2..`, `ResetContract.I_c2n`/`I_c2n_set`): `uenv1 = rst + C(env_c0, ~in_ack)`,
`uenv0 = ~rst . C(res_req, ~env_c)`. In C's channel terms `start.req = env_c` and
`out0.ack = env_c0` (= `q` below): a rise of `q` is the environment accepting one result.

## Results

* §1 Counting (`N`, `par`, `cell_count`): a cell whose output moves only to the value
  its pin shows of the OTHER cell (read through any monotone causal map) cannot get
  more than its initial excitation ahead of that cell, counted in transitions.
* §2 `ring_alternation` (step model, FIFO reads, ANY kernel): from a quiet start
  (`env_c = 1`, `q = 0`), the transition counts satisfy `N q ≤ N env_c ≤ N q + 1`
  forever.  Hypotheses per cell: H_LUT_FIFO, H_FB_FIRST (the RT_FB race, C's
  `FbFirst` in read form), H_RST_ONE_FALL, H_WIRE_FIFO.  The kernel's `in_ack` and
  `res_req` are arbitrary traces.
* §3 C's vocabulary (`start_per_result`, `start_once_prefix`): with C's `cnt`/`riseB`
  on the time-shifted traces, `#start rises ≤ #out0.ack rises + 1` and
  `#out0.ack rises ≤ #start rises` at every time; in particular H_START_ONCE holds on
  every prefix before the first returned result.
* §4 Release, timed (B's `LoopG` window channels, real INITs, any power-up):
  `uenv1_release` (= `ResetContract.c2n_set_reset`) and `uenv0_release` (new: forced
  by rst OR by its own inputs).  No ordering between the rst falls of the cells is
  needed.  H_UENV1_RELEASE is exactly: rst at uenv1's I3 high for its loop bound
  `dlmax + dwmax`, and `in_ack = 0 ∨ env_c0 = 1` at its pins until the kernel acks.
* §5 `rig_token` composes §4 and §3; `rig_token_nonvacuous` is a periodic run (with a
  reset prefix) that meets every hypothesis and completes 2 laps by t = 20.
* §6 Counter-runs: `short_rst_many_starts` (rst at uenv1 shorter than its loop:
  start offered infinitely often with no result, B's runt construction), `no_rst_no_token`
  (zero tokens), `stale_fb_extra_start` (H_FB_FIRST dropped at uenv1: 3 start offers
  against 1 result, and `start.req` rises while the kernel's ack is high).

Core Lean only.
-/

namespace Formal.Cells.RigToken
open Formal.Cells

/-! ## 1. Transition counting -/

/-- `x` changes at step `s → s+1`. -/
def chg (x : Nat → Bool) (s : Nat) : Bool := x s != x (s + 1)

/-- Number of transitions of `x` at steps `s ∈ [T0, t)`. -/
def N (x : Nat → Bool) (T0 : Nat) : Nat → Nat
  | 0 => 0
  | t + 1 => N x T0 t + (if T0 ≤ t ∧ chg x t = true then 1 else 0)

theorem N_succ (x : Nat → Bool) (T0 t : Nat) :
    N x T0 (t + 1) = N x T0 t + (if T0 ≤ t ∧ chg x t = true then 1 else 0) := rfl

theorem N_mono (x : Nat → Bool) (T0 : Nat) {a b : Nat} (h : a ≤ b) : N x T0 a ≤ N x T0 b := by
  induction b with
  | zero => rw [Nat.le_zero.mp h]; exact Nat.le_refl _
  | succ b ih =>
    rcases Nat.lt_or_eq_of_le h with h | h
    · have := ih (Nat.le_of_lt_succ h); rw [N_succ]; omega
    · rw [h]; exact Nat.le_refl _

theorem N_pre (x : Nat → Bool) (T0 : Nat) : ∀ t, t ≤ T0 → N x T0 t = 0 := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro h
    rw [N_succ, ih (by omega)]
    simp only [show ¬ T0 ≤ t by omega, false_and, ite_false]

/-- **Parity.** From `T0` on, `x` is its `T0` value flipped once per counted
transition. Before `T0` it is that value wherever `x` is quiet. -/
theorem par (x : Nat → Bool) (T0 Tq : Nat) (hq : ∀ s, Tq ≤ s → s ≤ T0 → x s = x T0) :
    ∀ t, Tq ≤ t → x t = xor (x T0) (decide (N x T0 t % 2 = 1)) := by
  intro t ht
  by_cases hT : t ≤ T0
  · rw [hq t ht hT, N_pre x T0 t hT]; simp
  · have key : ∀ d, x (T0 + d) = xor (x T0) (decide (N x T0 (T0 + d) % 2 = 1)) := by
      intro d
      induction d with
      | zero => rw [Nat.add_zero, N_pre x T0 T0 (Nat.le_refl _)]; simp
      | succ d ih =>
        rw [show T0 + (d + 1) = T0 + d + 1 by omega, N_succ]
        have hle : T0 ≤ T0 + d := by omega
        by_cases hc : chg x (T0 + d) = true
        · simp only [hle, hc, and_self, ite_true]
          simp only [chg, bne_iff_ne, ne_eq] at hc
          have hx : x (T0 + d + 1) = !x (T0 + d) := by
            cases h1 : x (T0 + d) <;> cases h2 : x (T0 + d + 1) <;> simp [h1, h2] at hc ⊢
          rw [hx, ih]
          cases x T0 <;> by_cases hp : N x T0 (T0 + d) % 2 = 1 <;>
            simp [hp, show ((N x T0 (T0 + d) + 1) % 2 = 1) ↔ ¬ (N x T0 (T0 + d) % 2 = 1) by omega]
        · have hc' : chg x (T0 + d) = false := by simpa using hc
          simp only [hc', Bool.false_eq_true, and_false, ite_false, Nat.add_zero]
          simp only [chg, bne_eq_false_iff_eq] at hc'
          rw [← hc', ih]
    have := key (t - T0)
    rwa [show T0 + (t - T0) = t by omega] at this

/-- **One cell, counted.** `y` is a cell output that, at every move from `T0` on,
moves to `xor (x (φ t)) c`: the value its pin shows of the other cell's output `x`,
read at `φ t` (a monotone, causal read map that does not reach before the quiet
window `[Tq, T0]`). `k = 0` if the cell is not excited at `T0`, else `1`. Then
`y` never has more than `k` transitions more than `x` had by the read time. -/
theorem cell_count (y x : Nat → Bool) (T0 Tq : Nat) (φ : Nat → Nat) (c : Bool) (k : Nat)
    (hφm : ∀ t t', T0 ≤ t → t ≤ t' → φ t ≤ φ t')
    (hφ1 : ∀ t, T0 ≤ t → φ t ≤ t)
    (hφ0 : ∀ t, T0 ≤ t → Tq ≤ φ t)
    (hq : ∀ s, Tq ≤ s → s ≤ T0 → x s = x T0)
    (hmove : ∀ t, T0 ≤ t → y (t + 1) ≠ y t → xor (x (φ t)) c = y (t + 1))
    (hk : k = if xor (x T0) c = y T0 then 0 else 1) :
    ∀ t, T0 ≤ t → N y T0 (t + 1) ≤ N x T0 (φ t) + k := by
  have parx := par x T0 Tq hq
  have pary := par y T0 T0 (fun s h1 h2 => by rw [show s = T0 by omega])
  have main : ∀ d, N y T0 (T0 + d + 1) ≤ N x T0 (φ (T0 + d)) + k := by
    intro d
    induction d with
    | zero =>
      rw [Nat.add_zero, N_succ, N_pre y T0 T0 (Nat.le_refl _)]
      by_cases hc : chg y T0 = true
      · simp only [Nat.le_refl, hc, and_self, ite_true, Nat.zero_add]
        simp only [chg, bne_iff_ne, ne_eq] at hc
        have hm := hmove T0 (Nat.le_refl _) (Ne.symm hc)
        have hx : x (φ T0) = x T0 := hq _ (hφ0 T0 (Nat.le_refl _)) (hφ1 T0 (Nat.le_refl _))
        rw [hx] at hm
        have hk1 : k = 1 := by
          rw [hk, hm]; cases h1 : y T0 <;> cases h2 : y (T0 + 1) <;> simp [h1, h2] at hc ⊢
        omega
      · have hc' : chg y T0 = false := by simpa using hc
        simp only [hc', Bool.false_eq_true, and_false, ite_false]
        omega
    | succ d ih =>
      have e1 : T0 + (d + 1) = T0 + d + 1 := by omega
      rw [e1, N_succ]
      have ht : T0 ≤ T0 + d := by omega
      have hmono := N_mono x T0 (hφm (T0 + d) (T0 + d + 1) ht (Nat.le_succ _))
      by_cases hc : chg y (T0 + d + 1) = true
      · simp only [show T0 ≤ T0 + d + 1 by omega, hc, and_self, ite_true]
        simp only [chg, bne_iff_ne, ne_eq] at hc
        have hm := hmove (T0 + d + 1) (by omega) (Ne.symm hc)
        have hy1 := pary (T0 + d + 1) (by omega)
        have hy2 : y (T0 + d + 1 + 1) = !y (T0 + d + 1) := by
          cases h1 : y (T0 + d + 1) <;> cases h2 : y (T0 + d + 1 + 1) <;> simp [h1, h2] at hc ⊢
        have hx := parx (φ (T0 + d + 1)) (hφ0 (T0 + d + 1) (by omega))
        rw [hy2, hy1, hx] at hm
        revert hm hk
        generalize N y T0 (T0 + d + 1) = m at ih ⊢
        generalize N x T0 (φ (T0 + d + 1)) = n at hmono ⊢
        generalize N x T0 (φ (T0 + d)) = n0 at ih hmono
        intro hk hm
        cases hx0 : x T0 <;> cases hc0 : c <;> cases hy0 : y T0 <;>
          simp only [hx0, hc0, hy0] at hm hk <;>
          by_cases hn : n % 2 = 1 <;> by_cases hmm : m % 2 = 1 <;>
          simp [hn, hmm] at hm hk <;> omega
      · have hc' : chg y (T0 + d + 1) = false := by simpa using hc
        simp only [hc', Bool.false_eq_true, and_false, ite_false, Nat.add_zero]
        omega
  intro t ht
  have := main (t - T0)
  rwa [show T0 + (t - T0) = t by omega] at this

/-! ## 2. The ring, counted (step model, any kernel) -/

/-- **Alternation.** `e` = `env_c` (uenv1's output = `start.req`), `q` = `env_c0`
(uenv0's output = `out0.ack`). Quiet start on `[Tq, T0]`: `e = 1`, `q = 0` (the
reset values). From `T0` on, `e` moves only to the value uenv1's pin shows of
`q` (`M1`, the `a` half of `C(env_c0, ~in_ack)`) and `q` only to the complement
of what uenv0's pin shows of `e` (`M0`, the `b` half of `C(res_req, ~env_c)`),
both read through monotone causal maps. Then, whatever the kernel does with
`in_ack` and `res_req`: `N q ≤ N e ≤ N q + 1` at every time. -/
theorem ring_alternation (e q : Nat → Bool) (T0 Tq : Nat) (φ1 φ0 : Nat → Nat)
    (H_INIT_E : ∀ s, Tq ≤ s → s ≤ T0 → e s = true)
    (H_INIT_Q : ∀ s, Tq ≤ s → s ≤ T0 → q s = false)
    (hφ1m : ∀ t t', T0 ≤ t → t ≤ t' → φ1 t ≤ φ1 t') (hφ1c : ∀ t, T0 ≤ t → φ1 t ≤ t)
    (hφ1q : ∀ t, T0 ≤ t → Tq ≤ φ1 t)
    (hφ0m : ∀ t t', T0 ≤ t → t ≤ t' → φ0 t ≤ φ0 t') (hφ0c : ∀ t, T0 ≤ t → φ0 t ≤ t)
    (hφ0q : ∀ t, T0 ≤ t → Tq ≤ φ0 t)
    (M1 : ∀ t, T0 ≤ t → e (t + 1) ≠ e t → q (φ1 t) = e (t + 1))
    (M0 : ∀ t, T0 ≤ t → q (t + 1) ≠ q t → e (φ0 t) = !q (t + 1)) :
    ∀ t, N q T0 t ≤ N e T0 t ∧ N e T0 t ≤ N q T0 t + 1 := by
  have hTq : Tq ≤ T0 := by
    have := hφ1q T0 (Nat.le_refl _); have := hφ1c T0 (Nat.le_refl _); omega
  have eT : e T0 = true := H_INIT_E T0 hTq (Nat.le_refl _)
  have qT : q T0 = false := H_INIT_Q T0 hTq (Nat.le_refl _)
  have C1 := cell_count e q T0 Tq φ1 false 1 hφ1m hφ1c hφ1q
    (fun s h1 h2 => by rw [H_INIT_Q s h1 h2, qT])
    (fun t ht hne => by rw [Bool.xor_false]; exact M1 t ht hne)
    (by rw [qT, eT]; rfl)
  have C0 := cell_count q e T0 Tq φ0 true 0 hφ0m hφ0c hφ0q
    (fun s h1 h2 => by rw [H_INIT_E s h1 h2, eT])
    (fun t ht hne => by rw [M0 t ht hne]; cases q (t + 1) <;> rfl)
    (by rw [qT, eT]; rfl)
  intro t
  cases t with
  | zero => simp [N]
  | succ t =>
    by_cases ht : T0 ≤ t
    · have a1 := C1 t ht
      have a0 := C0 t ht
      have m1 := N_mono q T0 (hφ1c t ht)
      have m0 := N_mono e T0 (hφ0c t ht)
      have s1 := N_mono q T0 (show t ≤ t + 1 by omega)
      have s0 := N_mono e T0 (show t ≤ t + 1 by omega)
      omega
    · rw [N_pre q T0 (t + 1) (by omega), N_pre e T0 (t + 1) (by omega)]; omega

/-! ### The cells give M1/M0: step form of the real INITs under H_LUT_FIFO,
H_FB_FIRST and H_RST_ONE_FALL -/

open Formal.Cells.CElemTiming (exc INIT_c2n c2n_eq)
open Formal.Cells.ResetContract (I_c2n I_c2n_set c2n_set_eq)

/-- **uenv1 (`bd_c2n_set`, INIT `FFB2..`) in step form.** Hypotheses, all on
the one cell:
* `H_LUT_FIFO`: from `T0` on, the output is the LUT function of its pins read
  at ONE instant `σ t`, `σ` monotone (B's `PipeTimed.Ret`, FifoFidelity);
* `H_RST_ONE_FALL`: from `Tr` on (and every read is at or after `Tr`), rst at
  the pin is high only on an initial segment (one fall, never re-asserted);
* `H_FB_FIRST` (the RT_FB race, C's `FbFirst` at the read instant): when the
  output moves, the feedback pin read for that move already shows the old
  output.
Then every move goes to the C-element value: `a = O'` and `b = ¬O'` at the read. -/
theorem set_move {a b rst O qp : Nat → Bool} {σ : Nat → Nat} {T0 Tr : Nat}
    (H_LUT_FIFO : ∀ t, T0 ≤ t → O t = exc I_c2n_set (a (σ t)) (b (σ t)) (qp (σ t)) (rst (σ t)))
    (hσm : ∀ t t', t ≤ t' → σ t ≤ σ t')
    (hσr : ∀ t, T0 ≤ t → Tr ≤ σ t)
    (H_RST_ONE_FALL : ∀ s s', Tr ≤ s → s ≤ s' → rst s' = true → rst s = true)
    (H_FB_FIRST : ∀ t, T0 ≤ t → O (t + 1) ≠ O t → qp (σ (t + 1)) = O t) :
    ∀ t, T0 ≤ t → O (t + 1) ≠ O t → a (σ (t + 1)) = O (t + 1) ∧ b (σ (t + 1)) = !O (t + 1) := by
  intro t ht hne
  have h1 := H_LUT_FIFO (t + 1) (by omega)
  have h0 := H_LUT_FIFO t ht
  cases hr : rst (σ (t + 1))
  · rw [hr, H_FB_FIRST t ht hne, c2n_set_eq] at h1
    revert hne h1
    generalize a (σ (t + 1)) = A
    generalize b (σ (t + 1)) = B
    generalize O t = P
    generalize O (t + 1) = P'
    cases A <;> cases B <;> cases P <;> cases P' <;> decide
  · have hr0 := H_RST_ONE_FALL (σ t) (σ (t + 1)) (hσr t ht) (hσm t (t + 1) (Nat.le_succ t)) hr
    rw [hr, c2n_set_eq] at h1
    rw [hr0, c2n_set_eq] at h0
    exact absurd (by rw [h1, h0]; rfl) hne

/-- **uenv0 (`bd_c2n`, INIT `00B2..`) in step form**, same hypotheses. -/
theorem c2n_move {a b rst O qp : Nat → Bool} {σ : Nat → Nat} {T0 Tr : Nat}
    (H_LUT_FIFO : ∀ t, T0 ≤ t → O t = exc I_c2n (a (σ t)) (b (σ t)) (qp (σ t)) (rst (σ t)))
    (hσm : ∀ t t', t ≤ t' → σ t ≤ σ t')
    (hσr : ∀ t, T0 ≤ t → Tr ≤ σ t)
    (H_RST_ONE_FALL : ∀ s s', Tr ≤ s → s ≤ s' → rst s' = true → rst s = true)
    (H_FB_FIRST : ∀ t, T0 ≤ t → O (t + 1) ≠ O t → qp (σ (t + 1)) = O t) :
    ∀ t, T0 ≤ t → O (t + 1) ≠ O t → a (σ (t + 1)) = O (t + 1) ∧ b (σ (t + 1)) = !O (t + 1) := by
  intro t ht hne
  have h1 := H_LUT_FIFO (t + 1) (by omega)
  have h0 := H_LUT_FIFO t ht
  have eI : I_c2n = INIT_c2n := rfl
  rw [eI] at h1 h0
  cases hr : rst (σ (t + 1))
  · rw [hr, H_FB_FIRST t ht hne, c2n_eq] at h1
    revert hne h1
    generalize a (σ (t + 1)) = A
    generalize b (σ (t + 1)) = B
    generalize O t = P
    generalize O (t + 1) = P'
    cases A <;> cases B <;> cases P <;> cases P' <;> decide
  · have hr0 := H_RST_ONE_FALL (σ t) (σ (t + 1)) (hσr t ht) (hσm t (t + 1) (Nat.le_succ t)) hr
    rw [hr, c2n_eq] at h1
    rw [hr0, c2n_eq] at h0
    exact absurd (by rw [h1, h0]; rfl) hne

/-! ## 3. In C's vocabulary (`Formal.Net.Handshake.cnt`, `riseB`) -/

open Formal.Net.Handshake (cnt riseB cnt_mono cnt_succ_of)

/-- Rises of `x` at steps `s ∈ [T0, t)`. -/
def R (x : Nat → Bool) (T0 : Nat) : Nat → Nat
  | 0 => 0
  | t + 1 => R x T0 t + (if T0 ≤ t ∧ riseB x t = true then 1 else 0)

theorem R_pre (x : Nat → Bool) (T0 : Nat) : ∀ t, t ≤ T0 → R x T0 t = 0 := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro h
    show R x T0 t + _ = 0
    rw [ih (by omega)]
    simp only [show ¬ T0 ≤ t by omega, false_and, ite_false]

/-- Rises from transitions: half of them, rounded by the start value. -/
theorem R_of_N (x : Nat → Bool) (T0 : Nat) :
    ∀ d, R x T0 (T0 + d) = if x T0 then N x T0 (T0 + d) / 2 else (N x T0 (T0 + d) + 1) / 2 := by
  have px := par x T0 T0 (fun s h1 h2 => by rw [show s = T0 by omega])
  intro d
  induction d with
  | zero =>
    rw [Nat.add_zero, R_pre x T0 T0 (Nat.le_refl _), N_pre x T0 T0 (Nat.le_refl _)]
    cases x T0 <;> rfl
  | succ d ih =>
    rw [show T0 + (d + 1) = T0 + d + 1 by omega, N_succ]
    show R x T0 (T0 + d) + _ = _
    rw [ih]
    have hp := px (T0 + d) (by omega)
    have hle : T0 ≤ T0 + d := by omega
    simp only [hle, true_and]
    revert hp
    generalize N x T0 (T0 + d) = n
    unfold riseB chg
    generalize x (T0 + d + 1) = x1
    generalize x (T0 + d) = x0
    cases x T0 <;> cases x0 <;> cases x1 <;> by_cases hn : n % 2 = 1 <;> simp [hn] <;> omega

/-- C's time origin: tick 0 is a virtual "before release" with `req = 0`
(C's `Src.iz`), tick `u ≥ 1` is rig time `T0 + u - 1`. -/
def shiftC (x : Nat → Bool) (T0 : Nat) : Nat → Bool := fun u => if u = 0 then false else x (T0 + (u - 1))

theorem cnt_shift (x : Nat → Bool) (T0 : Nat) :
    ∀ u, cnt (riseB (shiftC x T0)) (u + 1) = (if x T0 then 1 else 0) + R x T0 (T0 + u) := by
  intro u
  induction u with
  | zero =>
    rw [show T0 + 0 = T0 from rfl, R_pre x T0 T0 (Nat.le_refl _)]
    show cnt _ 0 + _ = _
    simp [cnt, riseB, shiftC]
  | succ u ih =>
    show cnt _ (u + 1) + _ = _
    rw [ih, show T0 + (u + 1) = T0 + u + 1 by omega]
    show _ = _ + (R x T0 (T0 + u) + _)
    have hle : T0 ≤ T0 + u := by omega
    simp only [hle, true_and]
    have : riseB (shiftC x T0) (u + 1) = riseB x (T0 + u) := by
      simp only [riseB, shiftC]
      simp only [show u + 1 ≠ 0 by omega, show u + 1 + 1 ≠ 0 by omega, ite_false]
      rw [show u + 1 - 1 = u by omega, show u + 1 + 1 - 1 = u + 1 by omega, Nat.add_assoc]
    rw [this]; omega

/-- **One start per returned result, in C's terms.** Under `ring_alternation`'s
hypotheses, with `start.req := shiftC e T0` and `out0.ack := shiftC q T0`, at
every C-time `u`: `#rises(start.req) ≤ #rises(out0.ack) + 1` and
`#rises(out0.ack) ≤ #rises(start.req)`. -/
theorem start_per_result (e q : Nat → Bool) (T0 Tq : Nat) (φ1 φ0 : Nat → Nat)
    (H_INIT_E : ∀ s, Tq ≤ s → s ≤ T0 → e s = true)
    (H_INIT_Q : ∀ s, Tq ≤ s → s ≤ T0 → q s = false)
    (hφ1m : ∀ t t', T0 ≤ t → t ≤ t' → φ1 t ≤ φ1 t') (hφ1c : ∀ t, T0 ≤ t → φ1 t ≤ t)
    (hφ1q : ∀ t, T0 ≤ t → Tq ≤ φ1 t)
    (hφ0m : ∀ t t', T0 ≤ t → t ≤ t' → φ0 t ≤ φ0 t') (hφ0c : ∀ t, T0 ≤ t → φ0 t ≤ t)
    (hφ0q : ∀ t, T0 ≤ t → Tq ≤ φ0 t)
    (M1 : ∀ t, T0 ≤ t → e (t + 1) ≠ e t → q (φ1 t) = e (t + 1))
    (M0 : ∀ t, T0 ≤ t → q (t + 1) ≠ q t → e (φ0 t) = !q (t + 1)) :
    ∀ u, cnt (riseB (shiftC e T0)) u ≤ cnt (riseB (shiftC q T0)) u + 1 ∧
      cnt (riseB (shiftC q T0)) u ≤ cnt (riseB (shiftC e T0)) u := by
  have hTq : Tq ≤ T0 := by
    have := hφ1q T0 (Nat.le_refl _); have := hφ1c T0 (Nat.le_refl _); omega
  have eT : e T0 = true := H_INIT_E T0 hTq (Nat.le_refl _)
  have qT : q T0 = false := H_INIT_Q T0 hTq (Nat.le_refl _)
  have A := ring_alternation e q T0 Tq φ1 φ0 H_INIT_E H_INIT_Q hφ1m hφ1c hφ1q hφ0m hφ0c hφ0q M1 M0
  intro u
  cases u with
  | zero => simp [cnt]
  | succ u =>
    rw [cnt_shift e T0 u, cnt_shift q T0 u, R_of_N e T0 u, R_of_N q T0 u, eT, qT]
    have := A (T0 + u)
    simp only [ite_true, ite_false, Bool.false_eq_true]
    omega

/-- **H_START_ONCE on every prefix before the first returned result.** -/
theorem start_once_prefix (e q : Nat → Bool) (T0 Tq : Nat) (φ1 φ0 : Nat → Nat)
    (H_INIT_E : ∀ s, Tq ≤ s → s ≤ T0 → e s = true)
    (H_INIT_Q : ∀ s, Tq ≤ s → s ≤ T0 → q s = false)
    (hφ1m : ∀ t t', T0 ≤ t → t ≤ t' → φ1 t ≤ φ1 t') (hφ1c : ∀ t, T0 ≤ t → φ1 t ≤ t)
    (hφ1q : ∀ t, T0 ≤ t → Tq ≤ φ1 t)
    (hφ0m : ∀ t t', T0 ≤ t → t ≤ t' → φ0 t ≤ φ0 t') (hφ0c : ∀ t, T0 ≤ t → φ0 t ≤ t)
    (hφ0q : ∀ t, T0 ≤ t → Tq ≤ φ0 t)
    (M1 : ∀ t, T0 ≤ t → e (t + 1) ≠ e t → q (φ1 t) = e (t + 1))
    (M0 : ∀ t, T0 ≤ t → q (t + 1) ≠ q t → e (φ0 t) = !q (t + 1)) :
    ∀ u, cnt (riseB (shiftC q T0)) u = 0 → cnt (riseB (shiftC e T0)) u ≤ 1 := by
  intro u hu
  have := (start_per_result e q T0 Tq φ1 φ0 H_INIT_E H_INIT_Q hφ1m hφ1c hφ1q hφ0m hφ0c hφ0q
    M1 M0 u).1
  omega

/-! ## 4. Release, timed (B's window-channel loops, real INITs, any power-up)

No hypothesis below relates the rst fall at one cell to the rst fall at another:
the release is order-free. What IS needed per cell is stated exactly. -/

open Formal.Cells.CTreeTimed (LoopG O_heldG qp_heldG)

/-- **uenv1 creates and holds the token** (`ResetContract.c2n_set_reset`).
H_UENV1_HOLD: rst at uenv1's I3 high for its loop bound `dlmax + dwmax` from
`t1` (from ANY power-up value of the loop); H_ACK_QUIET: until `t2`, uenv1's
pins show `env_c0 = 1` or `in_ack = 0` (the kernel has not acknowledged all three
inputs). After the hold, rst at uenv1 may fall at any time, in any order with
the other cells, and may even glitch: the excitation is 1 either way. -/
theorem uenv1_release {a b rst O qp : Nat → Bool} {dlmin dlmax dwmin dwmax : Nat}
    (L : LoopG (fun t q => exc I_c2n_set (a t) (b t) q (rst t)) O qp dlmin dlmax dwmin dwmax)
    (t1 t2 : Nat)
    (H_UENV1_HOLD : ∀ s, t1 ≤ s → s < t1 + (dlmax + dwmax) → rst s = true)
    (H_ACK_QUIET : ∀ s, t1 ≤ s → s ≤ t2 → a s = true ∨ b s = false) :
    (∀ t, t1 + dlmax ≤ t → t ≤ t2 + dlmin → O t = true) ∧
    (∀ t, t1 + (dlmax + dwmax) ≤ t → t ≤ t2 + (dlmin + dwmin) → qp t = true) :=
  ResetContract.c2n_set_reset L t1 t2 H_UENV1_HOLD H_ACK_QUIET

/-- **uenv0 comes up empty.** Its reset value 0 is forced by rst OR by its own
inputs (`res_req = 0 ∧ env_c = 1`): H_UENV0_FORCE for its loop bound, then
H_RES_QUIET (`res_req = 0 ∨ env_c = 1` at its pins) up to `t2`. -/
theorem uenv0_release {a b rst O qp : Nat → Bool} {dlmin dlmax dwmin dwmax : Nat}
    (L : LoopG (fun t q => exc I_c2n (a t) (b t) q (rst t)) O qp dlmin dlmax dwmin dwmax)
    (t0 t2 : Nat)
    (H_UENV0_FORCE : ∀ s, t0 ≤ s → s < t0 + (dlmax + dwmax) →
      rst s = true ∨ (a s = false ∧ b s = true))
    (H_RES_QUIET : ∀ s, t0 ≤ s → s ≤ t2 → a s = false ∨ b s = true) :
    (∀ t, t0 + dlmax ≤ t → t ≤ t2 + dlmin → O t = false) ∧
    (∀ t, t0 + (dlmax + dwmax) ≤ t → t ≤ t2 + (dlmin + dwmin) → qp t = false) := by
  have eI : I_c2n = INIT_c2n := rfl
  have hforce : ∀ s, t0 ≤ s → s < t0 + (dlmax + dwmax) →
      ∀ q, exc I_c2n (a s) (b s) q (rst s) = false := by
    intro s h1 h2 q
    rw [eI, c2n_eq]
    rcases H_UENV0_FORCE s h1 h2 with h | ⟨ha, hb⟩
    · rw [h]; rfl
    · rw [ha, hb]; cases q <;> cases rst s <;> rfl
  have hfix : ∀ s, t0 ≤ s → s < t2 + 1 → exc I_c2n (a s) (b s) false (rst s) = false := by
    intro s h1 h2
    rw [eI, c2n_eq]
    rcases H_RES_QUIET s h1 (by omega) with h | h <;> rw [h] <;> cases a s <;> cases b s <;>
      cases rst s <;> rfl
  exact ⟨fun t h1 h2 => O_heldG L false t0 (t2 + 1) hforce hfix t h1 (by omega),
    fun t h1 h2 => qp_heldG L false t0 (t2 + 1) hforce hfix t h1 (by omega)⟩

/-! ## 5. The composed theorem -/

/-- **The rig's token, release to steady state, in C's terms.**

Cells (real INITs): uenv1 = `e` (feedback `qp1`, pins `a1` = its copy of
`env_c0`, `b1` = `in_ack`, `rst1`); uenv0 = `q` (feedback `qp0`, pins `a0` =
`res_req`, `b0` = its copy of `env_c`, `rst0`). Wires `env_c0 → a1`,
`env_c → b0` are FIFO reads `ψ1`, `ψ0` (H_WIRE_FIFO). `in_ack`, `res_req` (the
kernel) are arbitrary.

Assumed: (timed, §4) B's window loops `L1`, `L0` with H_UENV1_HOLD,
H_ACK_QUIET, H_UENV0_FORCE, H_RES_QUIET, whose hold windows cover the quiet
window `[Tq, T0]`; (step, §2) each cell's H_LUT_FIFO, H_RST_ONE_FALL and
H_FB_FIRST from `T0` (reads at or after `Tr`), with the composed reads
`ψ (σ (t+1))` causal and inside `[Tq, t]`.

Proved: at every C-time `u` (`shiftC`, origin just before `T0`),
`#rises(start.req) ≤ #rises(out0.ack) + 1` and `#rises(out0.ack) ≤ #rises(start.req)`. -/
theorem rig_token
    {e qp1 a1 b1 rst1 q qp0 a0 b0 rst0 : Nat → Bool}
    {dl1 Dl1 dw1 Dw1 dl0 Dl0 dw0 Dw0 t1 t2 t0 t2' Tq T0 Tr : Nat}
    {σ1 σ0 ψ1 ψ0 : Nat → Nat}
    -- timed release (§4)
    (L1 : LoopG (fun t x => exc I_c2n_set (a1 t) (b1 t) x (rst1 t)) e qp1 dl1 Dl1 dw1 Dw1)
    (L0 : LoopG (fun t x => exc I_c2n (a0 t) (b0 t) x (rst0 t)) q qp0 dl0 Dl0 dw0 Dw0)
    (H_UENV1_HOLD : ∀ s, t1 ≤ s → s < t1 + (Dl1 + Dw1) → rst1 s = true)
    (H_ACK_QUIET : ∀ s, t1 ≤ s → s ≤ t2 → a1 s = true ∨ b1 s = false)
    (H_UENV0_FORCE : ∀ s, t0 ≤ s → s < t0 + (Dl0 + Dw0) →
      rst0 s = true ∨ (a0 s = false ∧ b0 s = true))
    (H_RES_QUIET : ∀ s, t0 ≤ s → s ≤ t2' → a0 s = false ∨ b0 s = true)
    (hW1 : t1 + Dl1 ≤ Tq ∧ T0 ≤ t2 + dl1) (hW0 : t0 + Dl0 ≤ Tq ∧ T0 ≤ t2' + dl0)
    -- steady state (§2)
    (F1 : ∀ t, T0 ≤ t → e t = exc I_c2n_set (a1 (σ1 t)) (b1 (σ1 t)) (qp1 (σ1 t)) (rst1 (σ1 t)))
    (F0 : ∀ t, T0 ≤ t → q t = exc I_c2n (a0 (σ0 t)) (b0 (σ0 t)) (qp0 (σ0 t)) (rst0 (σ0 t)))
    (hσ1m : ∀ t t', t ≤ t' → σ1 t ≤ σ1 t') (hσ0m : ∀ t t', t ≤ t' → σ0 t ≤ σ0 t')
    (hσ1r : ∀ t, T0 ≤ t → Tr ≤ σ1 t) (hσ0r : ∀ t, T0 ≤ t → Tr ≤ σ0 t)
    (H_RST1_ONE_FALL : ∀ s s', Tr ≤ s → s ≤ s' → rst1 s' = true → rst1 s = true)
    (H_RST0_ONE_FALL : ∀ s s', Tr ≤ s → s ≤ s' → rst0 s' = true → rst0 s = true)
    (H_FB_FIRST1 : ∀ t, T0 ≤ t → e (t + 1) ≠ e t → qp1 (σ1 (t + 1)) = e t)
    (H_FB_FIRST0 : ∀ t, T0 ≤ t → q (t + 1) ≠ q t → qp0 (σ0 (t + 1)) = q t)
    (H_WIRE1 : ∀ s, a1 s = q (ψ1 s)) (H_WIRE0 : ∀ s, b0 s = e (ψ0 s))
    (hψ1m : ∀ s s', s ≤ s' → ψ1 s ≤ ψ1 s') (hψ0m : ∀ s s', s ≤ s' → ψ0 s ≤ ψ0 s')
    (hR1 : ∀ t, T0 ≤ t → Tq ≤ ψ1 (σ1 (t + 1)) ∧ ψ1 (σ1 (t + 1)) ≤ t)
    (hR0 : ∀ t, T0 ≤ t → Tq ≤ ψ0 (σ0 (t + 1)) ∧ ψ0 (σ0 (t + 1)) ≤ t) :
    ∀ u, cnt (riseB (shiftC e T0)) u ≤ cnt (riseB (shiftC q T0)) u + 1 ∧
      cnt (riseB (shiftC q T0)) u ≤ cnt (riseB (shiftC e T0)) u := by
  have A1 := (uenv1_release L1 t1 t2 H_UENV1_HOLD H_ACK_QUIET).1
  have A0 := (uenv0_release L0 t0 t2' H_UENV0_FORCE H_RES_QUIET).1
  have m1 := set_move F1 hσ1m hσ1r H_RST1_ONE_FALL H_FB_FIRST1
  have m0 := c2n_move F0 hσ0m hσ0r H_RST0_ONE_FALL H_FB_FIRST0
  exact start_per_result e q T0 Tq (fun t => ψ1 (σ1 (t + 1))) (fun t => ψ0 (σ0 (t + 1)))
    (fun s h1 h2 => A1 s (by omega) (by omega)) (fun s h1 h2 => A0 s (by omega) (by omega))
    (fun t t' _ h => hψ1m _ _ (hσ1m _ _ (by omega))) (fun t ht => (hR1 t ht).2)
    (fun t ht => (hR1 t ht).1)
    (fun t t' _ h => hψ0m _ _ (hσ0m _ _ (by omega))) (fun t ht => (hR0 t ht).2)
    (fun t ht => (hR0 t ht).1)
    (fun t ht hne => by rw [← H_WIRE1]; exact (m1 t ht hne).1)
    (fun t ht hne => by rw [← H_WIRE0]; exact (m0 t ht hne).2)

/-! ### Non-vacuity: a run that meets every hypothesis of `rig_token`

Phase `p t` (0..11): ticks 0..3 are a reset prefix (rst high on `[0, 2)` at both
cells), then an 8-tick lap repeats forever:
`in_ack↑ res_req↑ (k=2) · env_c↓ (3) · env_c0↑ (4) · in_ack↓ res_req↓ (5) ·
env_c↑ (6) · env_c0↓ (7)`. LUT delay 1 tick (transport), feedback 0 ticks,
wires 0 ticks. The kernel obeys the four-phase rules on both channels. -/

namespace Wit

def p (t : Nat) : Nat := if t < 4 then t else 4 + (t - 4) % 8
def nxt (i : Nat) : Nat := if i < 11 then i + 1 else 4

theorem p_lt (t : Nat) : p t < 12 := by
  unfold p; split <;> omega

theorem p_succ (t : Nat) : p (t + 1) = nxt (p t) := by
  unfold p nxt
  by_cases h : t < 3
  · simp [show t + 1 < 4 by omega, show t < 4 by omega]; omega
  · by_cases h3 : t = 3
    · subst h3; rfl
    · simp only [show ¬ (t + 1 < 4) by omega, show ¬ (t < 4) by omega, ite_false]
      split <;> omega

def eL : List Bool := [true, true, true, true, true, true, true, false, false, false, true, true]
def qL : List Bool := [false, false, false, false, false, false, false, false, true, true, true, false]
def kL : List Bool := [false, false, false, false, false, false, true, true, true, false, false, false]
def rL : List Bool := [true, true, false, false, false, false, false, false, false, false, false, false]

def e (t : Nat) : Bool := eL.getD (p t) false
def q (t : Nat) : Bool := qL.getD (p t) false
/-- the kernel: `in_ack` and `res_req` (same waveform here) -/
def k (t : Nat) : Bool := kL.getD (p t) false
def rst (t : Nat) : Bool := rL.getD (p t) false

theorem rst_eq (t : Nat) : rst t = decide (t < 2) := by
  unfold rst p
  by_cases h : t < 4
  · simp only [h, ite_true]
    have : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> rfl
  · simp only [h, ite_false]
    have h8 : (t - 4) % 8 < 8 := Nat.mod_lt _ (by omega)
    have : ∀ i, i < 8 → rL.getD (4 + i) false = false := by decide
    rw [this _ h8]; simp; omega

theorem tbl1 : ∀ i, i < 12 →
    eL.getD (nxt i) false = exc I_c2n_set (qL.getD i false) (kL.getD i false) (eL.getD i false)
      (rL.getD i false) := by decide
theorem tbl0 : ∀ i, i < 12 →
    qL.getD (nxt i) false = exc I_c2n (kL.getD i false) (eL.getD i false) (qL.getD i false)
      (rL.getD i false) := by decide

theorem lut1 (t : Nat) : e (t + 1) = exc I_c2n_set (q t) (k t) (e t) (rst t) := by
  unfold e q k rst; rw [p_succ]; exact tbl1 _ (p_lt t)
theorem lut0 (t : Nat) : q (t + 1) = exc I_c2n (k t) (e t) (q t) (rst t) := by
  unfold e q k rst; rw [p_succ]; exact tbl0 _ (p_lt t)

theorem L1 : LoopG (fun t x => exc I_c2n_set (q t) (k t) x (rst t)) e e 1 1 0 0 :=
  { H_LUT := CElemTiming.transport_winDelay (Nat.le_refl _) (Nat.le_refl _) (fun t => (lut1 t).symm ▸ rfl)
    H_FB := CElemTiming.transport_winDelay (Nat.le_refl _) (Nat.le_refl _) (fun t => rfl)
    H_LOOP_POS := by decide }
theorem L0 : LoopG (fun t x => exc I_c2n (k t) (e t) x (rst t)) q q 1 1 0 0 :=
  { H_LUT := CElemTiming.transport_winDelay (Nat.le_refl _) (Nat.le_refl _) (fun t => (lut0 t).symm ▸ rfl)
    H_FB := CElemTiming.transport_winDelay (Nat.le_refl _) (Nat.le_refl _) (fun t => rfl)
    H_LOOP_POS := by decide }

theorem k_early : ∀ t, t ≤ 5 → k t = false := by decide

/-- Every hypothesis of `rig_token` holds (σ = t - 1, ψ = id, `[Tq, T0] = [2, 4]`,
`t1 = t0 = 0`, `t2 = t2' = 5`, `Tr = 0`), and the run is not degenerate: by
C-time 20 the environment has offered start 3 times and taken 2 results. -/
theorem rig_token_nonvacuous :
    (∀ u, cnt (riseB (shiftC e 4)) u ≤ cnt (riseB (shiftC q 4)) u + 1 ∧
      cnt (riseB (shiftC q 4)) u ≤ cnt (riseB (shiftC e 4)) u) ∧
    cnt (riseB (shiftC e 4)) 20 = 3 ∧ cnt (riseB (shiftC q 4)) 20 = 2 := by
  refine ⟨?_, by decide, by decide⟩
  refine rig_token (a1 := q) (b1 := k) (a0 := k) (b0 := e) (rst1 := rst) (rst0 := rst)
    (qp1 := e) (qp0 := q)
    (t1 := 0) (t2 := 5) (t0 := 0) (t2' := 5) (Tq := 2) (Tr := 0)
    (σ1 := fun t => t - 1) (σ0 := fun t => t - 1) (ψ1 := id) (ψ0 := id)
    L1 L0 ?_ ?_ ?_ ?_ (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro s h1 h2; rw [rst_eq]; simp; omega
  · intro s _ h2; right; exact k_early s h2
  · intro s h1 h2; left; rw [rst_eq]; simp; omega
  · intro s _ h2; left; exact k_early s h2
  · intro t ht
    have := lut1 (t - 1); rw [show t - 1 + 1 = t by omega] at this; exact this
  · intro t ht
    have := lut0 (t - 1); rw [show t - 1 + 1 = t by omega] at this; exact this
  · intro t t' h; omega
  · intro t t' h; omega
  · intro t _; omega
  · intro t _; omega
  · intro s s' _ h hr; rw [rst_eq] at hr ⊢; simp at hr ⊢; omega
  · intro s s' _ h hr; rw [rst_eq] at hr ⊢; simp at hr ⊢; omega
  · intro t _ _; simp
  · intro t _ _; simp
  · intro s; rfl
  · intro s; rfl
  · intro s s' h; exact h
  · intro s s' h; exact h
  · intro t ht; simp only [id]; omega
  · intro t ht; simp only [id]; omega

open Formal.Net.Handshake (Chan SendStep RecvStep) in
/-- The witness kernel and environment obey the four-phase rules on `start`
(`req = env_c`, `ack = in_ack`) and on `out0` (`req = res_req`, `ack = env_c0`). -/
theorem four_phase (t : Nat) :
    SendStep ⟨e, k, fun _ => 0⟩ t ∧ RecvStep ⟨e, k, fun _ => 0⟩ t ∧
    SendStep ⟨k, q, fun _ => 0⟩ t ∧ RecvStep ⟨k, q, fun _ => 0⟩ t := by
  have h : ∀ i, i < 12 →
      ((eL.getD (nxt i) false ≠ eL.getD i false → eL.getD i false = kL.getD i false) ∧
       (kL.getD (nxt i) false ≠ kL.getD i false → kL.getD i false ≠ eL.getD i false) ∧
       (kL.getD (nxt i) false ≠ kL.getD i false → kL.getD i false = qL.getD i false) ∧
       (qL.getD (nxt i) false ≠ qL.getD i false → qL.getD i false ≠ kL.getD i false)) := by decide
  have := h (p t) (p_lt t)
  simp only [SendStep, RecvStep, e, k, q, p_succ]
  exact this

end Wit

/-! ## 6. Counter-runs -/

theorem exists_rise (x : Nat → Bool) (a : Nat) (ha : x a = false) :
    ∀ b, a ≤ b → x b = true → ∃ t, a ≤ t ∧ t < b ∧ riseB x t = true := by
  intro b
  induction b with
  | zero => intro h hb; rw [show a = 0 by omega] at ha; rw [ha] at hb; exact absurd hb (by decide)
  | succ b ih =>
    intro h hb
    by_cases hab : a = b + 1
    · subst hab; rw [ha] at hb; exact absurd hb (by decide)
    · cases hx : x b
      · exact ⟨b, by omega, by omega, by simp [riseB, hx, hb]⟩
      · obtain ⟨t, h1, h2, h3⟩ := ih (by omega) hx
        exact ⟨t, h1, by omega, h3⟩

theorem two_rises {x : Nat → Bool} {t1 t2 : Nat} (h1 : riseB x t1 = true) (h2 : riseB x t2 = true)
    (h : t1 < t2) : 2 ≤ cnt (riseB x) (t2 + 1) := by
  have a := cnt_succ_of h1
  have b := cnt_mono (riseB x) (show t1 + 1 ≤ t2 by omega)
  have c := cnt_succ_of h2
  omega

/-- uenv1's INIT with `env_c0 = 0`, `in_ack = 0` is `rst ∨ q`: the same OR loop as
5b's `bd_c2` with `a = 1`. -/
theorem set_hold_as_c2 : ∀ x r : Bool,
    exc I_c2n_set false false x r = exc CElemTiming.INIT_c2 true r x false := by decide

/-- **H_UENV1_HOLD is necessary (exact at every fixed delay).** rst at uenv1's
pin is a pulse of width `0 < w < dl + dw` (shorter than its loop), from power-up
0, while the kernel has not answered (`env_c0 = 0`, `in_ack = 0` forever; uenv0 is
never set, so no result is ever taken). These traces satisfy B's window-loop
relations of the real INIT with fixed transport delays (`dl`, `dw`), and after
rst has fallen `start.req = env_c` rises in EVERY period `[t0+dl+D n + w,
t0+dl+D(n+1))`: infinitely many start offers, zero results. In particular two
rises: C's H_START_ONCE fails in every time origin before the first. -/
theorem short_rst_many_starts (dl dw w t0 : Nat) (hw0 : 0 < w) (hw : w < dl + dw) :
    LoopG (fun t x => exc I_c2n_set false false x (CElemTiming.bR w t0 t))
      (CElemTiming.OR dl dw w t0) (CElemTiming.qpR dl dw w t0) dl dl dw dw ∧
    (∀ t, t0 + w ≤ t → CElemTiming.bR w t0 t = false) ∧
    (∀ n, ∃ t, t0 + dl + (dl + dw) * n + w ≤ t ∧ t < t0 + dl + (dl + dw) * (n + 1) ∧
      riseB (CElemTiming.OR dl dw w t0) t = true) ∧
    2 ≤ cnt (riseB (CElemTiming.OR dl dw w t0)) (t0 + dl + (dl + dw) * 2) := by
  have L := CElemTiming.runt_loop dl dw w t0 hw (by omega)
  have hF : (fun t => exc I_c2n_set false false (CElemTiming.qpR dl dw w t0 t)
      (CElemTiming.bR w t0 t)) =
      (fun t => exc CElemTiming.INIT_c2 (CElemTiming.aR t) (CElemTiming.bR w t0 t)
        (CElemTiming.qpR dl dw w t0 t) (CElemTiming.rstR t)) := by
    funext t; exact set_hold_as_c2 _ _
  have osc := (CElemTiming.runt_oscillates dl dw w t0 hw0 hw).2.2
  have rises : ∀ n, ∃ t, t0 + dl + (dl + dw) * n + w ≤ t ∧ t < t0 + dl + (dl + dw) * (n + 1) ∧
      riseB (CElemTiming.OR dl dw w t0) t = true := by
    intro n
    have h0 := (osc n).2
    have h1 := (osc (n + 1)).1
    exact exists_rise _ _ h0 _ (by rw [Nat.mul_succ]; omega) h1
  refine ⟨⟨by show CElemTiming.WinDelay dl dl _ _; rw [hF]; exact L.H_LUT, L.H_FB, L.H_LOOP_POS⟩,
    ?_, rises, ?_⟩
  · intro t ht; simp [CElemTiming.bR]; omega
  · obtain ⟨ta, a1, a2, a3⟩ := rises 0
    obtain ⟨tb, b1, b2, b3⟩ := rises 1
    have := two_rises a3 b3 (by rw [Nat.mul_succ] at a2; omega)
    have := cnt_mono (riseB (CElemTiming.OR dl dw w t0)) (show tb + 1 ≤ t0 + dl + (dl + dw) * 2 by
      rw [show (1 : Nat) + 1 = 2 from rfl] at b2; omega)
    omega

/-- **No hold at all: zero tokens.** If rst never reaches uenv1 and the loop
powers up at 0, the constant-0 run satisfies the window-loop relations (with the
kernel idle): `start.req` never rises, the kernel is never started. -/
theorem no_rst_no_token (dl dw : Nat) (hpos : 0 < dl + dw) :
    LoopG (fun _ x => exc I_c2n_set false false x false) (fun _ => false) (fun _ => false)
      dl dl dw dw ∧ ∀ t, riseB (fun _ => false) t = false := by
  refine ⟨⟨?_, ?_, hpos⟩, fun t => rfl⟩
  · intro t ht
    exact ⟨t - dl, by omega, by omega, by show false = exc I_c2n_set false false false false; decide⟩
  · intro t ht; exact ⟨t - dw, by omega, by omega, rfl⟩

/-! ### H_FB_FIRST dropped at uenv1 (the RT_FB race lost): an extra start

Step model, tick = one LUT delay: each cell's output is its LUT function of
the pins one tick earlier (H_LUT_FIFO with `σ t = t - 1`), rst low, wires zero
delay, uenv0's feedback zero delay. Only uenv1's feedback is slow: a transport
wire of 3 ticks (a legal FIFO wire; this is the pin-1 feedback of the routed
`urig.uenv1`, slower than the one-hop response through uenv0). The kernel acks
`start` and presents its result at tick 2 and is slow to see `start.req` fall
(it holds both until tick 14, which no kernel hypothesis here forbids). -/

namespace Stale

structure St where
  e : Bool
  q : Bool
  h1 : Bool
  h2 : Bool
  h3 : Bool

/-- the kernel: `in_ack` = `res_req` -/
def kK (t : Nat) : Bool := decide (2 ≤ t ∧ t < 14)

def sim : Nat → St
  | 0 => ⟨true, false, true, true, true⟩
  | t + 1 =>
    let s := sim t
    ⟨exc I_c2n_set s.q (kK t) s.h3 false, exc I_c2n (kK t) s.e s.q false, s.e, s.h1, s.h2⟩

def e (t : Nat) : Bool := (sim t).e
def q (t : Nat) : Bool := (sim t).q
/-- uenv1's feedback pin -/
def fb (t : Nat) : Bool := (sim t).h3

theorem fb_wire (t : Nat) : fb (t + 3) = e t := rfl

theorem lut1 (t : Nat) : e t = exc I_c2n_set (q (t - 1)) (kK (t - 1)) (fb (t - 1)) false := by
  cases t with
  | zero => decide
  | succ t => rfl
theorem lut0 (t : Nat) : q t = exc I_c2n (kK (t - 1)) (e (t - 1)) (q (t - 1)) false := by
  cases t with
  | zero => decide
  | succ t => rfl

/-- uenv0 meets its step hypotheses (H_LUT_FIFO, zero-delay feedback so
H_FB_FIRST, rst low), so `M0` holds at every tick. -/
theorem stale_M0 : ∀ t, q (t + 1) ≠ q t → e t = !q (t + 1) := by
  intro t hne
  have := (c2n_move (a := kK) (b := e) (rst := fun _ => false) (O := q) (qp := q)
    (σ := fun t => t - 1) (T0 := 0) (Tr := 0) (fun t _ => lut0 t) (fun _ _ _ => by omega)
    (fun _ _ => Nat.zero_le _) (fun _ _ _ _ h => h) (fun _ _ _ => rfl) t (Nat.zero_le _) hne).2
  simpa using this

/-- **The counter-run.** Every hypothesis of §2's cell lemmas holds (uenv1:
`lut1` = H_LUT_FIFO, rst low, `fb_wire` a FIFO feedback wire; uenv0: `stale_M0`)
except H_FB_FIRST at uenv1, which fails at tick 4 (the feedback pin still shows
1 although `env_c` fell at tick 3). Consequences: `M1` fails at tick 6 (uenv1
falls while its `env_c0` pin is still 1); `start.req` re-rises at tick 4 → 5
while the kernel's ack is still high (the start channel's SendStep is broken);
and by C-time 11 it has risen 3 times (counting the release offer) against ONE
returned result, which `start_per_result` forbids. -/
theorem stale_fb_extra_start :
    (e 5 ≠ e 4 ∧ fb 4 ≠ e 4) ∧
    (e 7 ≠ e 6 ∧ q 6 ≠ e 7) ∧
    (riseB e 4 = true ∧ kK 4 = true) ∧
    cnt (riseB (shiftC e 0)) 11 = 3 ∧ cnt (riseB (shiftC q 0)) 11 = 1 := by
  decide

end Stale

end Formal.Cells.RigToken
