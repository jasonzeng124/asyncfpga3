import Formal.Cells.Prelim
import Formal.Cells.ArbKleene
import Formal.Cells.TernarySound

/-!
# Probe 7i: multi-phase ternary soundness, the remaining 7b scenarios, and a
first exactness result

Builds on probe 7f (`TernarySound.lean`: networks `Circ`, binary runs `Run` in
the GMW model with per-pin wire delays, bounds `Bounded D W`, Algorithms A/B).

1. **Multi-phase soundness** (`phase_cov`, `phases_sound`). A run goes through
   a list of input phases. Phase `p` has a window vector `p.u` (`x` on the
   inputs that change), a final vector `p.a`, a ternary state `p.s` closed
   under the window step (`stepK u s ⊑ s`, e.g. the Algorithm A fixed point),
   a number `p.m` of B iterates, a window start `p.S` and the time `p.F` from
   which the inputs are final. Phase `q` after `p` must start from something
   covering `p`'s B result (`p.res ⊑ q.s`) and its window may only open once
   `p` has settled and the wires have flushed: `p.F + p.m·(D+W+1) + W ≤ q.S`.
   Then every phase's A state covers the run on its whole interval and its B
   result covers the run from `F + m·(D+W+1)` to the next window.
2. **The remaining 7b scenarios as trace theorems** on the arbiter network
   `arbNet` of 7f: `arb_tie_acked`, `arb_runt_held`, `arb_a0_fall_ordered`
   (with H_A0_FORK as an explicit constraint on the traces of the two A0 fork
   nodes), and for `sc_a0_fall_skewed` the NEGATIVE statement
   `arb_a0_fall_skewed_early_ack`: a concrete bounded run (unit gate delay,
   every wire 0 steps except A0's branch into `ua2`, 3 steps) in which A0
   falls once and never rises again, yet A2 rises and stays high: client 2 is
   acknowledged for a transaction the server never began. With the
   companion run `arb_a0_fall_noskew` (all wires 0, A2 stays 0) this also
   shows the `x` on A2 in `sc_a0_fall_skewed` is exact: both values occur.
3. **Exactness for the C-element in hold with a runt** (`cel_*`). The real
   `bd_c2` INIT with its output fed back to I2 through a wire. Ternary: a runt
   on `b` while `a = 1` (phase A: `b = x`) drives `q` from 0 to `x` and phase B
   (`b = 0`, hold) keeps it `x`. Three bounded binary runs (unit gate delay,
   feedback wire 1 step) with the same input phases: one ends `q = 0` for
   ever, one ends `q = 1` for ever, and one oscillates for ever (the runt's
   pulse circulates in the loop). So the `x` is genuinely reachable: it is
   both "settles differently" and "does not settle".
   The same for the arbiter's tie (`arb_tie_exact`): `sc_tie_rising`'s `x` on
   q, g1, g2 is witnessed by bounded runs where client 1 wins, client 2 wins,
   and q oscillates for ever with the grants alternating.

The run construction (`dsim`) is a unit-gate-delay binary simulation with a
fixed delay per pin, proved to be a `Run` with `Bounded _ _ _ 0 W`
(`dsim_run`, `dsim_bounded`); `dsim_periodic` lifts a finite check of a
window of `W + 1` steps to "for ever".
-/

namespace Formal.Cells.TernaryPhases
open Formal.Cells Formal.Cells.TernarySound

/-! ## (1) One phase, with a start time -/

/-- Inputs of `v` at step `k` are admitted by the ternary vector `u`. -/
def InputsIn (N : Circ) (v : Nat → Nat → Bool) (u : Nat → K3) (k : Nat) : Prop :=
  ∀ n, N.node n = .input → K3.admits (u n) (v k n) = true

/-- **One phase.** `s` is closed under the window step for `u`. At the window
start `S` the run is covered by `s` on the last `W + 1` steps (`Entry`); the
inputs are inside `u` on `(S, E]` and inside `a` on `[F, E]`. Then `s` covers
the run on `[S, E]` and the `m`-th B iterate covers it on
`[F + m·(D+W+1), E]`. -/
theorem phase_cov (N : Circ) (u a s : Nat → K3) (hpost : sle (stepK N u s) s)
    {v : Nat → Nat → Bool} (R : Run N v) {D W : Nat} (hB : Bounded N v R D W)
    (S F E : Nat) (hSF : S ≤ F)
    (hent : ∀ k, k ≤ S → S ≤ k + W → covers s (v k))
    (hu : ∀ k, S < k → k ≤ E → InputsIn N v u k)
    (ha : ∀ k, F < k → k ≤ E → InputsIn N v a k) :
    (∀ k, S ≤ k + W → k ≤ E → covers s (v k)) ∧
    (∀ m k, F + m * (D + W + 1) ≤ k → k ≤ E → covers (iter N a m s) (v k)) := by
  have hA : ∀ k, S ≤ k + W → k ≤ E → covers s (v k) := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      intro hk hkE
      rcases Nat.lt_or_ge S k with hlt | hle
      · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        intro n
        have hp := hpost n
        unfold stepK at hp
        cases hn : N.node n with
        | input =>
          rw [hn] at hp
          exact admits_of_le hp (hu (k' + 1) hlt hkE n hn)
        | gate init pins =>
          rw [hn] at hp
          rcases R.gate k' n init pins hn with h | h
          · rw [h]; exact ih k' (by omega) (by omega) (by omega) n
          · rw [h]
            apply admits_of_le hp
            apply lutK_sound
            apply pins_forall2
            intro p i
            have h1 := R.rd_le k' n p
            have h2 := hB.wire k' n p
            exact ih _ (by omega) (by omega) (by omega) i
      · exact hent k hle hk
  refine ⟨hA, ?_⟩
  intro m
  induction m with
  | zero => intro k hk hkE; exact hA k (by omega) hkE
  | succ m ih =>
    intro k hk hkE n
    rw [Nat.succ_mul] at hk
    rw [iter_succ']
    unfold stepK
    cases hn : N.node n with
    | input => exact ha k (by omega) hkE n hn
    | gate init pins =>
      dsimp only
      have hexc : ∀ i, F + m * (D + W + 1) + W ≤ i → i ≤ E →
          K3.admits (lutK init (pins.map (srcK (iter N a m s)))) (R.exc init pins i n) = true := by
        intro i hi hiE
        apply lutK_sound
        apply pins_forall2
        intro p q
        have := hB.wire i n p
        have := R.rd_le i n p
        exact ih _ (by omega) (by omega) q
      have key : ∀ b, lutK init (pins.map (srcK (iter N a m s))) = K3.ofBool b →
          v k n = b := by
        intro b hz
        have hb : ∀ i, F + m * (D + W + 1) + W ≤ i → i ≤ E → R.exc init pins i n = b := by
          intro i hi hiE
          have := hexc i hi hiE; rw [hz] at this
          exact (admits_ofBool_iff b _).1 this
        obtain ⟨i, hi1, hi2, hvi⟩ := hB.gate (F + m * (D + W + 1) + W) n init pins b hn
          (fun i h1 h2 => hb i h1 (by omega))
        have hold : ∀ d, i + d ≤ k → v (i + d) n = b := by
          intro d
          induction d with
          | zero => intro _; exact hvi
          | succ d ihd =>
            intro hd
            rcases R.gate (i + d) n init pins hn with h | h
            · rw [← Nat.add_assoc, h, ihd (by omega)]
            · rw [← Nat.add_assoc, h]; exact hb (i + d) (by omega) (by omega)
        have : k = i + (k - i) := by omega
        rw [this]; exact hold _ (by omega)
      cases hz : lutK init (pins.map (srcK (iter N a m s))) with
      | X => rfl
      | one => rw [key true hz]; rfl
      | zero => rw [key false hz]; rfl

/-! ## (1) Many phases -/

/-- An input phase together with the ternary data that certifies it. -/
structure Phase where
  /-- window vector: `x` on the inputs that change in this phase -/
  u : Nat → K3
  /-- final input vector -/
  a : Nat → K3
  /-- ternary state closed under the window step (Algorithm A result) -/
  s : Nat → K3
  /-- number of B iterates -/
  m : Nat
  /-- window start (inputs leave the previous final vector after `S`) -/
  S : Nat
  /-- inputs are final from `F` on -/
  F : Nat

/-- The phase's B result. -/
def Phase.res (N : Circ) (p : Phase) : Nat → K3 := iter N p.a p.m p.s

/-- Time from which the B result covers the run. -/
def Phase.ready (D W : Nat) (p : Phase) : Nat := p.F + p.m * (D + W + 1)

/-- Ternary certificate of each phase: closed under its window step, `S ≤ F`. -/
def Closed (N : Circ) (ps : List Phase) : Prop :=
  ∀ p ∈ ps, sle (stepK N p.u p.s) p.s ∧ p.S ≤ p.F

/-- Consecutive phases chain: the B result of `p` is below the A state of
`q`, and `q`'s window opens only after `p` has settled and every wire has
flushed (`p.ready + W ≤ q.S`). -/
def Links (N : Circ) (D W : Nat) : List Phase → Prop
  | [] => True
  | [_] => True
  | p :: q :: ps => sle (p.res N) q.s ∧ p.ready D W + W ≤ q.S ∧ Links N D W (q :: ps)

/-- The run's inputs follow the phases: in phase `p` (until the next window
start, for ever for the last phase) inputs are inside `p.u` after `p.S` and
inside `p.a` from `p.F`. -/
def Follows (N : Circ) (v : Nat → Nat → Bool) : List Phase → Prop
  | [] => True
  | [p] => ∀ k, p.S < k → InputsIn N v p.u k ∧ (p.F ≤ k → InputsIn N v p.a k)
  | p :: q :: ps =>
    (∀ k, p.S < k → k ≤ q.S → InputsIn N v p.u k ∧ (p.F ≤ k → InputsIn N v p.a k)) ∧
    Follows N v (q :: ps)

/-- What the run satisfies: in every phase, the A state covers the run from
the window start to the next window start, and the B result from `ready` to
the next window start; for the last phase, for ever. -/
def Good (N : Circ) (D W : Nat) (v : Nat → Nat → Bool) : List Phase → Prop
  | [] => True
  | [p] => (∀ k, p.S ≤ k → covers p.s (v k)) ∧ (∀ k, p.ready D W ≤ k → covers (p.res N) (v k))
  | p :: q :: ps =>
    (∀ k, p.S ≤ k → k ≤ q.S → covers p.s (v k)) ∧
    (∀ k, p.ready D W ≤ k → k ≤ q.S → covers (p.res N) (v k)) ∧ Good N D W v (q :: ps)

/-- **Multi-phase soundness.** For every bounded run whose inputs follow a
chained list of phases and whose state at the first window start (and the
`W` steps before it) is covered by the first phase's A state, every phase's
A state and B result cover the run on their intervals. -/
theorem phases_sound (N : Circ) {v : Nat → Nat → Bool} (R : Run N v) {D W : Nat}
    (hB : Bounded N v R D W) :
    ∀ (p : Phase) (ps : List Phase), Closed N (p :: ps) → Links N D W (p :: ps) →
      Follows N v (p :: ps) →
      (∀ k, k ≤ p.S → p.S ≤ k + W → covers p.s (v k)) →
      Good N D W v (p :: ps) := by
  intro p ps
  induction ps generalizing p with
  | nil =>
    intro hC _ hF hent
    have hc := hC p (List.mem_cons_self ..)
    have one := fun E => phase_cov N p.u p.a p.s hc.1 R hB p.S p.F E hc.2 hent
      (fun k h1 _ => (hF k h1).1) (fun k h1 _ => (hF k (by have := hc.2; omega)).2 (Nat.le_of_lt h1))
    exact ⟨fun k hk => (one k).1 k (by omega) (Nat.le_refl _),
      fun k hk => (one k).2 p.m k hk (Nat.le_refl _)⟩
  | cons q qs ih =>
    intro hC hL hF hent
    have hc := hC p (List.mem_cons_self ..)
    have one := phase_cov N p.u p.a p.s hc.1 R hB p.S p.F q.S hc.2 hent
      (fun k h1 h2 => (hF.1 k h1 h2).1)
      (fun k h1 h2 => (hF.1 k (by have := hc.2; omega) h2).2 (Nat.le_of_lt h1))
    refine ⟨fun k hk hk2 => one.1 k (by omega) hk2,
      fun k hk hk2 => one.2 p.m k hk hk2, ?_⟩
    apply ih q (fun r hr => hC r (List.mem_cons_of_mem _ hr)) hL.2.2 hF.2
    intro k hk1 hk2
    have hr := hL.2.1
    exact covers_of_sle hL.1 (one.2 p.m k (by unfold Phase.ready at hr; omega) (by omega))

/-! ## Bounded runs with fixed per-pin delays (run construction) -/

/-- Unit-gate-delay binary simulation where pin `p` of gate `j` reads its
source `dl j p` steps late. Returns the history, newest first. -/
def dsim (N : Circ) (dl : Nat → Nat → Nat) (inp : Nat → Nat → Bool) (c0 : Nat → Bool) :
    Nat → List (Nat → Bool)
  | 0 => [fun n => match N.node n with
      | .input => inp 0 n
      | .gate _ _ => c0 n]
  | k + 1 =>
    let h := dsim N dl inp c0 k
    (fun n => match N.node n with
      | .input => inp (k + 1) n
      | .gate init pins =>
        lutB init (pinsB (fun p i => (h.getD (dl n p) (h.getD k c0)) i) pins 0)) :: h

/-- The trace of `dsim`. -/
def dv (N : Circ) (dl : Nat → Nat → Nat) (inp : Nat → Nat → Bool) (c0 : Nat → Bool)
    (k : Nat) : Nat → Bool :=
  (dsim N dl inp c0 k).headD c0

theorem dsim_length (N : Circ) (dl : Nat → Nat → Nat) (inp : Nat → Nat → Bool)
    (c0 : Nat → Bool) : ∀ k, (dsim N dl inp c0 k).length = k + 1 := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => simp [dsim, ih]

/-- Entry `i` of the history at step `k` is the state at step `k - i`
(clamped at 0). -/
theorem dsim_getD (N : Circ) (dl : Nat → Nat → Nat) (inp : Nat → Nat → Bool)
    (c0 : Nat → Bool) : ∀ k i d, i ≤ k →
      (dsim N dl inp c0 k).getD i d = dv N dl inp c0 (k - i) := by
  intro k
  induction k with
  | zero => intro i d hi; rw [Nat.le_zero.1 hi]; rfl
  | succ k ih =>
    intro i d hi
    cases i with
    | zero => rfl
    | succ i =>
      show (dsim N dl inp c0 k).getD i d = _
      rw [ih i d (by omega)]
      congr 1; omega

theorem dsim_read (N : Circ) (dl : Nat → Nat → Nat) (inp : Nat → Nat → Bool)
    (c0 : Nat → Bool) (k j p : Nat) :
    (dsim N dl inp c0 k).getD (dl j p) ((dsim N dl inp c0 k).getD k c0) =
      dv N dl inp c0 (k - dl j p) := by
  rcases Nat.lt_or_ge k (dl j p) with h | h
  · have hlen := dsim_length N dl inp c0 k
    have hd : (dsim N dl inp c0 k).getD (dl j p) ((dsim N dl inp c0 k).getD k c0) =
        (dsim N dl inp c0 k).getD k c0 := by simp [show (dsim N dl inp c0 k).length ≤ dl j p by omega]
    rw [hd, dsim_getD N dl inp c0 k k c0 (Nat.le_refl _)]
    congr 1; omega
  · exact dsim_getD N dl inp c0 k _ _ h

theorem dv_succ_gate (N : Circ) (dl : Nat → Nat → Nat) (inp : Nat → Nat → Bool)
    (c0 : Nat → Bool) (k j init : Nat) (pins : List Src) (hj : N.node j = .gate init pins) :
    dv N dl inp c0 (k + 1) j =
      lutB init (pinsB (fun p i => dv N dl inp c0 (k - dl j p) i) pins 0) := by
  show (match N.node j with
      | .input => inp (k + 1) j
      | .gate init pins => lutB init (pinsB (fun p i =>
          ((dsim N dl inp c0 k).getD (dl j p) ((dsim N dl inp c0 k).getD k c0)) i) pins 0)) = _
  rw [hj]
  simp only [dsim_read]

theorem dv_input (N : Circ) (dl : Nat → Nat → Nat) (inp : Nat → Nat → Bool)
    (c0 : Nat → Bool) (k n : Nat) (hn : N.node n = .input) : dv N dl inp c0 k n = inp k n := by
  cases k with
  | zero =>
    show (match N.node n with | .input => inp 0 n | .gate _ _ => c0 n) = _
    rw [hn]
  | succ k =>
    show (match N.node n with
      | .input => inp (k + 1) n
      | .gate init pins => lutB init (pinsB (fun p i =>
          ((dsim N dl inp c0 k).getD (dl n p) ((dsim N dl inp c0 k).getD k c0)) i) pins 0)) = _
    rw [hn]

/-- `dsim` is a run: read times `k - dl j p`, every gate takes its LUT value
in every step. -/
def dsim_run (N : Circ) (dl : Nat → Nat → Nat) (inp : Nat → Nat → Bool) (c0 : Nat → Bool) :
    Run N (dv N dl inp c0) where
  rd k j p := k - dl j p
  rd_le _ _ _ := Nat.sub_le _ _
  gate k j init pins h := Or.inr (dv_succ_gate N dl inp c0 k j init pins h)

/-- ... with gate bound `D = 0` and wire bound `W` when every pin delay is at
most `W` (non-vacuous instance of `Bounded`). -/
theorem dsim_bounded (N : Circ) (dl : Nat → Nat → Nat) (inp : Nat → Nat → Bool)
    (c0 : Nat → Bool) (W : Nat) (hW : ∀ j p, dl j p ≤ W) :
    Bounded N (dv N dl inp c0) (dsim_run N dl inp c0) 0 W where
  wire k j p := by have := hW j p; show k ≤ k - dl j p + W; omega
  gate k j init pins b h hb := by
    refine ⟨k + 1, Nat.le_succ k, Nat.le_refl _, ?_⟩
    rw [dv_succ_gate N dl inp c0 k j init pins h]
    exact hb k (Nat.le_refl _) (by omega)

/-- **Periodicity from a finite window.** If the inputs are `P`-periodic from
`k0` on, every gate node `< size` repeats with period `P` on the `W + 1`
steps `[k0, k0 + W]`, nodes `≥ size` are inputs, and every pin delay is at
most `W`, then the whole state is `P`-periodic from `k0` on. (`P = 1`: the
run has settled for ever.) -/
theorem dsim_periodic (N : Circ) (hN : ∀ n, N.size ≤ n → N.node n = .input)
    (dl : Nat → Nat → Nat) (inp : Nat → Nat → Bool) (c0 : Nat → Bool) (W P k0 : Nat)
    (hW : ∀ j p, dl j p ≤ W)
    (hinp : ∀ k n, k0 ≤ k → N.node n = .input → inp (k + P) n = inp k n)
    (hwin : ∀ i, i < W + 1 → ∀ n, n < N.size →
      dv N dl inp c0 (k0 + i + P) n = dv N dl inp c0 (k0 + i) n) :
    ∀ k, k0 ≤ k → ∀ n, dv N dl inp c0 (k + P) n = dv N dl inp c0 k n := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro hk n
    cases hn : N.node n with
    | input => rw [dv_input N dl inp c0 _ n hn, dv_input N dl inp c0 _ n hn]; exact hinp k n hk hn
    | gate init pins =>
      rcases Nat.lt_or_ge k (k0 + W + 1) with hlt | hge
      · have hsz : n < N.size := by
          apply Classical.byContradiction; intro h
          rw [hN n (by omega)] at hn; cases hn
        have := hwin (k - k0) (by omega) n hsz
        rw [show k0 + (k - k0) = k by omega] at this
        exact this
      · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        rw [show k' + 1 + P = (k' + P) + 1 by omega, dv_succ_gate N dl inp c0 _ n init pins hn,
          dv_succ_gate N dl inp c0 _ n init pins hn]
        congr 2
        funext p i
        have := hW n p
        rw [show k' + P - dl n p = (k' - dl n p) + P by omega]
        exact ih _ (by omega) (by omega) i


/-- Corollary of `dsim_periodic` with `P = 1`: the run keeps its state at
`k0` for ever. -/
theorem dsim_const (N : Circ) (hN : ∀ n, N.size ≤ n → N.node n = .input)
    (dl : Nat → Nat → Nat) (inp : Nat → Nat → Bool) (c0 : Nat → Bool) (W k0 : Nat)
    (hW : ∀ j p, dl j p ≤ W)
    (hinp : ∀ k n, k0 ≤ k → N.node n = .input → inp (k + 1) n = inp k n)
    (hwin : ∀ i, i < W + 1 → ∀ n, n < N.size →
      dv N dl inp c0 (k0 + i + 1) n = dv N dl inp c0 (k0 + i) n) :
    ∀ d n, dv N dl inp c0 (k0 + d) n = dv N dl inp c0 k0 n := by
  have hp := dsim_periodic N hN dl inp c0 W 1 k0 hW hinp hwin
  intro d
  induction d with
  | zero => intro n; rfl
  | succ d ih => intro n; rw [← Nat.add_assoc, hp _ (by omega) n, ih n]

/-! ## (2) The arbiter: helpers on 7b's encoding -/

open ArbKleene in
/-- Information order on K3 as a Boolean (for `decide`). -/
def kle (a b : K3) : Bool := decide (a = b) || decide (b = .x)

theorem kle_le {a b : K3} (h : kle a b = true) : le a b := by
  unfold kle at h
  cases a <;> cases b <;> first | exact Or.inl rfl | exact Or.inr rfl | simp at h

def nle (s s' : ArbKleene.Net) : Bool :=
  kle s.q s'.q && kle s.g1 s'.g1 && kle s.g2 s'.g2 && kle s.r0 s'.r0 && kle s.a1 s'.a1 &&
    kle s.a2 s'.a2

def ile (i i' : ArbKleene.Inp) : Bool :=
  kle i.r1 i'.r1 && kle i.r2 i'.r2 && kle i.a0 i'.a0 && kle i.a0c i'.a0c && kle i.rst i'.rst

theorem enc_sle {i i' : ArbKleene.Inp} {s s' : ArbKleene.Net} (hi : ile i i' = true)
    (hs : nle s s' = true) : sle (enc i s) (enc i' s') := by
  simp only [ile, nle, Bool.and_eq_true] at hi hs
  intro n
  match n with
  | 0 => exact kle_le hi.1.1.1.1 | 1 => exact kle_le hi.1.1.1.2
  | 2 => exact kle_le hi.1.1.2 | 3 => exact kle_le hi.1.2 | 4 => exact kle_le hi.2
  | 5 => exact kle_le hs.1.1.1.1.1 | 6 => exact kle_le hs.1.1.1.1.2
  | 7 => exact kle_le hs.1.1.1.2 | 8 => exact kle_le hs.1.1.2
  | 9 => exact kle_le hs.1.2 | 10 => exact kle_le hs.2
  | _ + 11 => exact le_refl _

theorem enc_closed (i : ArbKleene.Inp) (s : ArbKleene.Net) (h : ArbKleene.step i s = s) :
    sle (stepK arbNet (encU i) (enc i s)) (enc i s) := by
  rw [stepK_enc, h]; exact fun _ => le_refl _

theorem inputs_enc {v : Nat → Nat → Bool} (i : ArbKleene.Inp) (k : Nat)
    (h0 : K3.admits i.r1 (v k 0) = true) (h1 : K3.admits i.r2 (v k 1) = true)
    (h2 : K3.admits i.a0 (v k 2) = true) (h3 : K3.admits i.a0c (v k 3) = true)
    (h4 : K3.admits i.rst (v k 4) = true) : InputsIn arbNet v (encU i) k := by
  intro n hn
  rcases (arb_input_iff n).1 hn with h | h
  · match n, h with
    | 0, _ => exact h0 | 1, _ => exact h1 | 2, _ => exact h2 | 3, _ => exact h3
    | 4, _ => exact h4
  · match n, h with
    | k + 11, _ => rfl

theorem ad_f {b : Bool} (h : b = false) : K3.admits .f b = true := by rw [h]; rfl
theorem ad_t {b : Bool} (h : b = true) : K3.admits .t b = true := by rw [h]; rfl
theorem ad_x (b : Bool) : K3.admits .x b = true := rfl

/-- Read a definite node value off a covering `enc` state. -/
theorem cov_f {s : Nat → K3} {c : Nat → Bool} (h : covers s c) (n : Nat) (hn : s n = .f) :
    c n = false := by
  have := h n; rw [hn] at this; simpa [K3.admits] using this
theorem cov_t {s : Nat → K3} {c : Nat → Bool} (h : covers s c) (n : Nat) (hn : s n = .t) :
    c n = true := by
  have := h n; rw [hn] at this; simpa [K3.admits] using this

/-! ### `sc_tie_acked` -/

open ArbKleene K3 in
/-- 7b's state after the server's A0 window on a tie: everything `x` but R0. -/
def tieAck : ArbKleene.Net := ⟨x, x, x, t, x, x⟩
open ArbKleene K3 in
def winAck : ArbKleene.Inp := I t t x f
open ArbKleene K3 in
def finAck : ArbKleene.Inp := I t t t f

theorem tieAck_fix : ArbKleene.step winAck tieAck = tieAck := by decide
theorem tieAck_finfix : ArbKleene.step finAck tieAck = tieAck := ArbKleene.sc_tie_acked.2

/-- **`sc_tie_acked` on every bounded trace.** Both requests change from
time 0 and are both high from `F1` (a tie, any skew); the server stays idle
(A0 = 0 on both fork branches) until `S2`, which is at least
`F1 + 4·(D+W+1) + W`; then A0 does anything and is high on both branches
from `F2`; no reset; both acks start low. Then the acks stay low until
`S2`, and R0 = 1 from `F1 + 4·(D+W+1)` on FOR EVER, through the server's ack
and any A0 waveform. (7b's `x` on A1, A2, q, g1, g2 means the model claims
nothing about them; that they really can go either way is an exactness
question, see section (3) for the C-element.) -/
theorem arb_tie_acked {v : Nat → Nat → Bool} (R : Run arbNet v) {D W : Nat}
    (hB : Bounded arbNet v R D W) (F1 S2 F2 : Nat)
    (hS2 : F1 + 4 * (D + W + 1) + W ≤ S2) (hF2 : S2 ≤ F2)
    (hrst : ∀ k, v k 4 = false)
    (hr : ∀ k, F1 ≤ k → v k 0 = true ∧ v k 1 = true)
    (hidle : ∀ k, k ≤ S2 → v k 2 = false ∧ v k 3 = false)
    (hack : ∀ k, F2 ≤ k → v k 2 = true ∧ v k 3 = true)
    (hA0 : v 0 9 = false) (hA0' : v 0 10 = false) :
    (∀ k, k ≤ S2 → v k 9 = false ∧ v k 10 = false) ∧
    (∀ k, F1 + 4 * (D + W + 1) ≤ k → v k 8 = true) := by
  let p1 : Phase := ⟨encU winA, encU finTie, enc winA stA, 4, 0, F1⟩
  let p2 : Phase := ⟨encU winAck, encU finAck, enc winAck tieAck, 1, S2, F2⟩
  have hres1 : p1.res arbNet = enc finTie ⟨.x, .x, .x, .t, .f, .f⟩ := by
    show iter arbNet (encU finTie) (3 + 1) (enc winA stA) = _
    have hfin : ArbKleene.settle 3 finTie stA = ⟨.x, .x, .x, .t, .f, .f⟩ :=
      ArbKleene.sc_tie_rising.2.1
    rw [iterB_enc winA finTie stA ArbKleene.sc_runt_opposite.2.1 3, hfin]
  have hC : Closed arbNet [p1, p2] := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact ⟨enc_closed _ _ ArbKleene.sc_runt_opposite.2.1, Nat.zero_le _⟩
    · exact ⟨enc_closed _ _ tieAck_fix, hF2⟩
  have hL : Links arbNet D W [p1, p2] := by
    refine ⟨?_, ?_, trivial⟩
    · rw [hres1]; exact enc_sle (by decide) (by decide)
    · show F1 + 4 * (D + W + 1) + W ≤ S2; exact hS2
  have hF : Follows arbNet v [p1, p2] := by
    refine ⟨?_, ?_⟩
    · intro k _ hk
      have hi := hidle k hk
      refine ⟨inputs_enc _ k (ad_x _) (ad_x _) (ad_f hi.1) (ad_f hi.2) (ad_f (hrst k)), ?_⟩
      intro hk1
      have hq := hr k hk1
      exact inputs_enc _ k (ad_t hq.1) (ad_t hq.2) (ad_f hi.1) (ad_f hi.2) (ad_f (hrst k))
    · intro k hk
      have hk' : S2 < k := hk
      have hq := hr k (by omega)
      refine ⟨inputs_enc _ k (ad_t hq.1) (ad_t hq.2) (ad_x _) (ad_x _) (ad_f (hrst k)), ?_⟩
      intro hk2
      have ha := hack k hk2
      exact inputs_enc _ k (ad_t hq.1) (ad_t hq.2) (ad_t ha.1) (ad_t ha.2) (ad_f (hrst k))
  have hent : ∀ k, k ≤ p1.S → p1.S ≤ k + W → covers p1.s (v k) := by
    intro k hk _
    have hk0 : k = 0 := Nat.le_zero.1 hk
    subst hk0
    have hi := hidle 0 (Nat.zero_le _)
    intro n
    match n with
    | 0 => rfl | 1 => rfl
    | 2 => exact ad_f hi.1 | 3 => exact ad_f hi.2 | 4 => exact ad_f (hrst 0)
    | 5 => rfl | 6 => rfl | 7 => rfl | 8 => rfl
    | 9 => exact ad_f hA0 | 10 => exact ad_f hA0'
    | _ + 11 => rfl
  have hG := phases_sound arbNet R hB p1 [p2] hC hL hF hent
  obtain ⟨hA1, hB1, hA2, _⟩ := hG
  refine ⟨fun k hk => ⟨cov_f (hA1 k (Nat.zero_le _) hk) 9 rfl,
    cov_f (hA1 k (Nat.zero_le _) hk) 10 rfl⟩, ?_⟩
  intro k hk
  rcases Nat.lt_or_ge S2 k with h | h
  · exact cov_t (hA2 k (Nat.le_of_lt h)) 8 rfl
  · have := hB1 k hk h; rw [hres1] at this; exact cov_t this 8 rfl

/-! ### `sc_runt_held` -/

open ArbKleene K3 in
def winHeld : ArbKleene.Inp := I x x t f
open ArbKleene K3 in
def heldA : ArbKleene.Net := ⟨t, x, f, x, t, f⟩

/-- **`sc_runt_held` on every trace, unbounded delays.** While the server
acknowledges client 1 (A0 = 1 on both fork branches, no reset), starting
from q = 1, g2 = 0, A1 = 1, A2 = 0, the requests may do anything (runts,
ties): q stays 1, g2 stays 0, A1 stays 1 and A2 stays 0 at every step, for
every gate and wire delay (GMW, per-pin delays). The hold shields the state. -/
theorem arb_runt_held {v : Nat → Nat → Bool} (R : Run arbNet v)
    (ha0 : ∀ k, v k 2 = true ∧ v k 3 = true) (hrst : ∀ k, v k 4 = false)
    (hq : v 0 5 = true) (hg2 : v 0 7 = false) (ha1 : v 0 9 = true) (ha2 : v 0 10 = false) :
    ∀ k, v k 5 = true ∧ v k 7 = false ∧ v k 9 = true ∧ v k 10 = false := by
  have h0 : covers (enc winHeld heldA) (v 0) := by
    intro n
    match n with
    | 0 => rfl | 1 => rfl
    | 2 => exact ad_t (ha0 0).1 | 3 => exact ad_t (ha0 0).2 | 4 => exact ad_f (hrst 0)
    | 5 => exact ad_t hq | 6 => rfl | 7 => exact ad_f hg2 | 8 => rfl
    | 9 => exact ad_t ha1 | 10 => exact ad_f ha2
    | _ + 11 => rfl
  have hin : ∀ k n, arbNet.node n = .input → K3.admits (encU winHeld n) (v k n) = true :=
    fun k => inputs_enc winHeld k (ad_x _) (ad_x _) (ad_t (ha0 k).1) (ad_t (ha0 k).2)
      (ad_f (hrst k))
  intro k
  have hc := A_invariant arbNet (encU winHeld) (enc winHeld heldA)
    (enc_closed _ _ ArbKleene.sc_runt_held.2) R hin h0 k
  exact ⟨cov_t hc 5 rfl, cov_f hc 7 rfl, cov_t hc 9 rfl, cov_f hc 10 rfl⟩

/-! ### `sc_a0_fall_ordered` (H_A0_FORK as a trace constraint) -/

open ArbKleene K3 in
def ordU1 : ArbKleene.Inp := ⟨f, t, t, x, f⟩
open ArbKleene K3 in
def ordA1 : ArbKleene.Inp := ⟨f, t, t, f, f⟩
open ArbKleene K3 in
def ordU2 : ArbKleene.Inp := ⟨f, t, x, f, f⟩
open ArbKleene K3 in
def ordA2 : ArbKleene.Inp := ⟨f, t, f, f, f⟩
open ArbKleene K3 in
def ordS1 : ArbKleene.Net := ⟨t, f, f, f, x, f⟩
open ArbKleene K3 in
def ordS2 : ArbKleene.Net := ⟨x, f, x, x, f, f⟩

theorem ordS1_fix : ArbKleene.step ordU1 ordS1 = ordS1 := by decide
theorem ordS2_fix : ArbKleene.step ordU2 ordS2 = ordS2 := by decide
theorem ord_res1 : ArbKleene.settle 3 ordA1 ordS1 = ⟨.t, .f, .f, .f, .f, .f⟩ := by decide
theorem ord_res2 : ArbKleene.settle 3 ordA2 ordS2 = ⟨.f, .f, .t, .t, .f, .f⟩ := by decide

/-- **`sc_a0_fall_ordered` on every bounded trace, with H_A0_FORK as a
constraint on the two fork nodes.** Client 2 waits (r1 = 0, r2 = 1), no
reset; at time 0 the arbiter is in 7b's `done1` (q = 1, g1 = g2 = R0 = 0,
A2 = 0; A1 arbitrary). The server drops A0. **H_A0_FORK (trace form)**: the
branch into the ack C-elements (node 3) is low from `F1` on, while the branch
into `ustate.I4` (node 2) is still high up to `S2 ≥ F1 + 4·(D+W+1) + W`; node 2
is low from `F2` on. Then A2 = 0 at EVERY step (no early ack), and from
`F2 + 4·(D+W+1)` on q = 0, g1 = 0, g2 = 1, R0 = 1, A1 = A2 = 0. -/
theorem arb_a0_fall_ordered {v : Nat → Nat → Bool} (R : Run arbNet v) {D W : Nat}
    (hB : Bounded arbNet v R D W) (F1 S2 F2 : Nat)
    (hfork : F1 + 4 * (D + W + 1) + W ≤ S2) (hF2 : S2 ≤ F2)
    (hr1 : ∀ k, v k 0 = false) (hr2 : ∀ k, v k 1 = true) (hrst : ∀ k, v k 4 = false)
    (hst : ∀ k, k ≤ S2 → v k 2 = true) (hst' : ∀ k, F2 ≤ k → v k 2 = false)
    (hc : ∀ k, F1 ≤ k → v k 3 = false)
    (hq : v 0 5 = true) (hg1 : v 0 6 = false) (hg2 : v 0 7 = false) (hr0 : v 0 8 = false)
    (ha2 : v 0 10 = false) :
    (∀ k, v k 10 = false) ∧
    ∀ k, F2 + 4 * (D + W + 1) ≤ k →
      v k 5 = false ∧ v k 6 = false ∧ v k 7 = true ∧ v k 8 = true ∧ v k 9 = false ∧
        v k 10 = false := by
  let p1 : Phase := ⟨encU ordU1, encU ordA1, enc ordU1 ordS1, 4, 0, F1⟩
  let p2 : Phase := ⟨encU ordU2, encU ordA2, enc ordU2 ordS2, 4, S2, F2⟩
  have hres1 : p1.res arbNet = enc ordA1 ⟨.t, .f, .f, .f, .f, .f⟩ := by
    show iter arbNet (encU ordA1) (3 + 1) (enc ordU1 ordS1) = _
    rw [iterB_enc ordU1 ordA1 ordS1 ordS1_fix 3, ord_res1]
  have hres2 : p2.res arbNet = enc ordA2 ⟨.f, .f, .t, .t, .f, .f⟩ := by
    show iter arbNet (encU ordA2) (3 + 1) (enc ordU2 ordS2) = _
    rw [iterB_enc ordU2 ordA2 ordS2 ordS2_fix 3, ord_res2]
  have hC : Closed arbNet [p1, p2] := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact ⟨enc_closed _ _ ordS1_fix, Nat.zero_le _⟩
    · exact ⟨enc_closed _ _ ordS2_fix, hF2⟩
  have hL : Links arbNet D W [p1, p2] := by
    refine ⟨?_, ?_, trivial⟩
    · rw [hres1]; exact enc_sle (by decide) (by decide)
    · show F1 + 4 * (D + W + 1) + W ≤ S2; exact hfork
  have hF : Follows arbNet v [p1, p2] := by
    refine ⟨?_, ?_⟩
    · intro k _ hk
      refine ⟨inputs_enc _ k (ad_f (hr1 k)) (ad_t (hr2 k)) (ad_t (hst k hk)) (ad_x _)
        (ad_f (hrst k)), ?_⟩
      intro hk1
      exact inputs_enc _ k (ad_f (hr1 k)) (ad_t (hr2 k)) (ad_t (hst k hk)) (ad_f (hc k hk1))
        (ad_f (hrst k))
    · intro k hk
      have hk' : S2 < k := hk
      refine ⟨inputs_enc _ k (ad_f (hr1 k)) (ad_t (hr2 k)) (ad_x _) (ad_f (hc k (by omega)))
        (ad_f (hrst k)), ?_⟩
      intro hk2
      exact inputs_enc _ k (ad_f (hr1 k)) (ad_t (hr2 k)) (ad_f (hst' k hk2))
        (ad_f (hc k (by omega))) (ad_f (hrst k))
  have hent : ∀ k, k ≤ p1.S → p1.S ≤ k + W → covers p1.s (v k) := by
    intro k hk _
    have hk0 : k = 0 := Nat.le_zero.1 hk
    subst hk0
    intro n
    match n with
    | 0 => exact ad_f (hr1 0) | 1 => exact ad_t (hr2 0)
    | 2 => exact ad_t (hst 0 (Nat.zero_le _)) | 3 => rfl | 4 => exact ad_f (hrst 0)
    | 5 => exact ad_t hq | 6 => exact ad_f hg1 | 7 => exact ad_f hg2 | 8 => exact ad_f hr0
    | 9 => rfl | 10 => exact ad_f ha2
    | _ + 11 => rfl
  have hG := phases_sound arbNet R hB p1 [p2] hC hL hF hent
  obtain ⟨hA1, _, hA2, hB2⟩ := hG
  refine ⟨?_, ?_⟩
  · intro k
    rcases Nat.lt_or_ge S2 k with h | h
    · exact cov_f (hA2 k (Nat.le_of_lt h)) 10 rfl
    · exact cov_f (hA1 k (Nat.zero_le _) h) 10 rfl
  · intro k hk
    have := hB2 k hk
    rw [hres2] at this
    exact ⟨cov_f this 5 rfl, cov_f this 6 rfl, cov_t this 7 rfl, cov_t this 8 rfl,
      cov_f this 9 rfl, cov_f this 10 rfl⟩


/-! ### `sc_a0_fall_skewed`: what soundness still gives, and a concrete
early-ack run -/

open ArbKleene K3 in
def skU : ArbKleene.Inp := I f t x f
open ArbKleene K3 in
def skA : ArbKleene.Inp := I f t f f
open ArbKleene K3 in
def skS : ArbKleene.Net := ⟨x, f, x, x, x, x⟩

theorem skS_fix : ArbKleene.step skU skS = skS := by decide
theorem sk_res : ArbKleene.settle 3 skA skS = ⟨.f, .f, .t, .t, .f, .x⟩ := by decide

/-- **`sc_a0_fall_skewed`, soundness half.** Client 2 waits, no reset, g1 = 0
at time 0; A0 does anything on both fork branches (any skew) and is low on
both from `F` on. Then from `F + 4·(D+W+1)` on q = 0, g1 = 0, g2 = 1, R0 = 1,
A1 = 0. A2 is NOT determined (7b: `x`), and `arb_a0_fall_skewed_early_ack` /
`arb_a0_fall_noskew` below show both of its values really occur. -/
theorem arb_a0_fall_skewed {v : Nat → Nat → Bool} (R : Run arbNet v) {D W : Nat}
    (hB : Bounded arbNet v R D W) (F : Nat)
    (hr1 : ∀ k, v k 0 = false) (hr2 : ∀ k, v k 1 = true) (hrst : ∀ k, v k 4 = false)
    (ha0 : ∀ k, F ≤ k → v k 2 = false ∧ v k 3 = false) (hg1 : v 0 6 = false) :
    ∀ k, F + 4 * (D + W + 1) ≤ k →
      v k 5 = false ∧ v k 6 = false ∧ v k 7 = true ∧ v k 8 = true ∧ v k 9 = false := by
  let p : Phase := ⟨encU skU, encU skA, enc skU skS, 4, 0, F⟩
  have hres : p.res arbNet = enc skA ⟨.f, .f, .t, .t, .f, .x⟩ := by
    show iter arbNet (encU skA) (3 + 1) (enc skU skS) = _
    rw [iterB_enc skU skA skS skS_fix 3, sk_res]
  have hC : Closed arbNet [p] := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    subst hq
    exact ⟨enc_closed _ _ skS_fix, Nat.zero_le _⟩
  have hF : Follows arbNet v [p] := by
    intro k _
    refine ⟨inputs_enc _ k (ad_f (hr1 k)) (ad_t (hr2 k)) (ad_x _) (ad_x _) (ad_f (hrst k)), ?_⟩
    intro hk
    exact inputs_enc _ k (ad_f (hr1 k)) (ad_t (hr2 k)) (ad_f (ha0 k hk).1) (ad_f (ha0 k hk).2)
      (ad_f (hrst k))
  have hent : ∀ k, k ≤ p.S → p.S ≤ k + W → covers p.s (v k) := by
    intro k hk _
    have hk0 : k = 0 := Nat.le_zero.1 hk
    subst hk0
    intro n
    match n with
    | 0 => exact ad_f (hr1 0) | 1 => exact ad_t (hr2 0)
    | 2 => rfl | 3 => rfl | 4 => exact ad_f (hrst 0)
    | 5 => rfl | 6 => exact ad_f hg1 | 7 => rfl | 8 => rfl | 9 => rfl | 10 => rfl
    | _ + 11 => rfl
  have hG := phases_sound arbNet R hB p [] hC trivial hF hent
  intro k hk
  have := hG.2 k hk
  rw [hres] at this
  exact ⟨cov_f this 5 rfl, cov_f this 6 rfl, cov_t this 7 rfl, cov_t this 8 rfl,
    cov_f this 9 rfl⟩

/-- Inputs of the concrete A0-fall runs: r1 = 0, r2 = 1, rst = 0; A0 is high at
step 0 on both fork branches and falls at step 1, for ever (the server never
raises A0 again, i.e. never begins client 2's transaction). -/
def skInp (k n : Nat) : Bool :=
  match n with
  | 1 => true
  | 2 => k == 0
  | 3 => k == 0
  | _ => false

/-- 7b's `done1` as a binary state: q = 1, A1 = 1, everything else 0. -/
def done1B (n : Nat) : Bool :=
  match n with
  | 5 => true
  | 9 => true
  | _ => false

/-- Pin delays of the early-ack run: every wire 0 steps, except the A0 branch
into `ua2` (gate 10, pin I1), 3 steps. -/
def skDl (j p : Nat) : Nat := if j = 10 ∧ p = 1 then 3 else 0

theorem skDl_le (j p : Nat) : skDl j p ≤ 3 := by unfold skDl; split <;> omega

theorem arb_hN : ∀ n, arbNet.size ≤ n → arbNet.node n = .input :=
  fun n h => (arb_input_iff n).2 (Or.inr h)

theorem skInp_const (k n : Nat) (hk : 1 ≤ k) : skInp (k + 1) n = skInp k n := by
  unfold skInp
  split <;> simp <;> omega

theorem skInp_spec (k : Nat) (hk : 1 ≤ k) :
    skInp k 0 = false ∧ skInp k 1 = true ∧ skInp k 2 = false ∧ skInp k 3 = false ∧
      skInp k 4 = false := by
  simp [skInp]; omega

/-- **`sc_a0_fall_skewed`, the negative statement: a concrete bounded binary
run with an early acknowledge.** In `dsim` with unit gate delay (`D = 0`) and
the pin delays `skDl` (`W = 3`: only the A0 branch into `ua2` is slow, by
3 gate delays), started in `done1` with client 2 waiting: A0 falls at step 1
on BOTH fork nodes and stays low for ever, so the server never begins client
2's transaction; yet q falls (step 2), g2 rises (step 3) and A2 rises at
step 4 and stays high for ever. The fork nodes carry identical traces here:
the skew is all in the routed branch, which is why H_A0_FORK must budget the
wire delay (`+ W` in `arb_a0_fall_ordered`). -/
theorem arb_a0_fall_skewed_early_ack :
    Bounded arbNet (dv arbNet skDl skInp done1B) (dsim_run arbNet skDl skInp done1B) 0 3 ∧
    (∀ k, 1 ≤ k →
      dv arbNet skDl skInp done1B k 0 = false ∧ dv arbNet skDl skInp done1B k 1 = true ∧
      dv arbNet skDl skInp done1B k 2 = false ∧ dv arbNet skDl skInp done1B k 3 = false ∧
      dv arbNet skDl skInp done1B k 4 = false) ∧
    (dv arbNet skDl skInp done1B 0 2 = true ∧ dv arbNet skDl skInp done1B 0 3 = true) ∧
    (∀ n, n < 11 → dv arbNet skDl skInp done1B 0 n = done1B n ||
      (n == 2 || n == 3 || n == 1)) ∧
    dv arbNet skDl skInp done1B 2 5 = false ∧ dv arbNet skDl skInp done1B 3 7 = true ∧
    dv arbNet skDl skInp done1B 3 10 = false ∧
    (∀ k, 4 ≤ k → dv arbNet skDl skInp done1B k 10 = true) := by
  refine ⟨dsim_bounded arbNet skDl skInp done1B 3 skDl_le, ?_, by decide, by decide, by decide,
    by decide, by decide, ?_⟩
  · intro k hk
    have hs := skInp_spec k hk
    rw [dv_input arbNet skDl skInp done1B k 0 rfl, dv_input arbNet skDl skInp done1B k 1 rfl,
      dv_input arbNet skDl skInp done1B k 2 rfl, dv_input arbNet skDl skInp done1B k 3 rfl,
      dv_input arbNet skDl skInp done1B k 4 rfl]
    exact hs
  · have hc := dsim_const arbNet arb_hN skDl skInp done1B 3 4 skDl_le
      (fun k n hk _ => skInp_const k n (by omega)) (by decide)
    intro k hk
    have := hc (k - 4) 10
    rw [show 4 + (k - 4) = k by omega] at this
    rw [this]; decide

/-- The companion run with all wires 0 steps (no fork skew): same inputs and
start, A2 stays 0 for ever. So both values of the `x` on A2 in
`sc_a0_fall_skewed` occur in bounded runs: that `x` is exact. -/
theorem arb_a0_fall_noskew :
    Bounded arbNet (dv arbNet (fun _ _ => 0) skInp done1B)
      (dsim_run arbNet (fun _ _ => 0) skInp done1B) 0 0 ∧
    (∀ k, dv arbNet (fun _ _ => 0) skInp done1B k 10 = false) ∧
    (∀ k, 4 ≤ k → dv arbNet (fun _ _ => 0) skInp done1B k 7 = true) := by
  have hc := dsim_const arbNet arb_hN (fun _ _ => 0) skInp done1B 0 4 (fun _ _ => Nat.le_refl _)
      (fun k n hk _ => skInp_const k n (by omega)) (by decide)
  refine ⟨dsim_bounded arbNet _ skInp done1B 0 (fun _ _ => Nat.le_refl _), ?_, ?_⟩
  · intro k
    rcases Nat.lt_or_ge k 4 with h | h
    · have : ∀ k, k < 4 → dv arbNet (fun _ _ => 0) skInp done1B k 10 = false := by decide
      exact this k h
    · have := hc (k - 4) 10
      rw [show 4 + (k - 4) = k by omega] at this
      rw [this]; decide
  · intro k hk
    have := hc (k - 4) 7
    rw [show 4 + (k - 4) = k by omega] at this
    rw [this]; decide

/-! ## (3) Exactness for one LUT with a feedback wire: the C-element in hold
with a runt -/

open ArbKleene in
/-- `bd_c2` (real INIT `C2_INIT`, pins I0 a, I1 b, I2 own output via a routed
feedback wire, I3 rst, I4 = I5 = 0) as a network: inputs 0 a, 1 b, 2 rst;
gate 3 q. -/
def cNet : Circ where
  size := 4
  node n := match n with
    | 3 => .gate C2_INIT [.node 0, .node 1, .node 3, .node 2, .const false, .const false]
    | _ => .input

theorem c_hN : ∀ n, cNet.size ≤ n → cNet.node n = .input := by
  intro n hn
  show (match n with
    | 3 => Node.gate ArbKleene.C2_INIT [.node 0, .node 1, .node 3, .node 2, .const false,
        .const false]
    | _ => .input) = _
  split
  · exact absurd hn (by decide)
  · rfl

/-- Ternary vectors: a = 1, rst = 0, b and q given. -/
def cS (q b : K3) (n : Nat) : K3 :=
  match n with
  | 0 => .t
  | 1 => b
  | 2 => .f
  | 3 => q
  | _ => .x

/-- **Ternary side.** Algorithm A for a runt on b (`b = x`) from the stable
hold state q = 0 (a = 1, b = 0) reaches `q = x` in two Jacobi steps and is a
fixed point there; Algorithm B with b = 0 again (hold) keeps `q = x` in every
iterate. So the A-then-B result is `x` on the C-element output. -/
theorem cel_ternary :
    (∀ n, stepK cNet (cS .f .f) (cS .f .f) n = cS .f .f n) ∧
    (∀ n, iter cNet (cS .x .x) 2 (cS .f .f) n = cS .x .x n) ∧
    (∀ n, stepK cNet (cS .x .x) (cS .x .x) n = cS .x .x n) ∧
    (∀ m, iter cNet (cS .x .f) (m + 1) (cS .x .x) 3 = .x) := by
  have hB1 : ∀ n, stepK cNet (cS .x .f) (cS .x .x) n = cS .x .f n := by
    intro n; match n with
    | 0 => rfl | 1 => rfl | 2 => rfl | 3 => decide | _ + 4 => rfl
  have hB2 : ∀ n, stepK cNet (cS .x .f) (cS .x .f) n = cS .x .f n := by
    intro n; match n with
    | 0 => rfl | 1 => rfl | 2 => rfl | 3 => decide | _ + 4 => rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n; match n with
    | 0 => rfl | 1 => rfl | 2 => rfl | 3 => decide | _ + 4 => rfl
  · intro n; match n with
    | 0 => rfl | 1 => rfl | 2 => rfl | 3 => decide | _ + 4 => rfl
  · intro n; match n with
    | 0 => rfl | 1 => rfl | 2 => rfl | 3 => decide | _ + 4 => rfl
  · intro m
    have hfix : ∀ m, iter cNet (cS .x .f) m (cS .x .f) = cS .x .f := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih => rw [iter_succ', ih]; funext n; exact hB2 n
    show iter cNet (cS .x .f) m (stepK cNet (cS .x .f) (cS .x .x)) 3 = .x
    rw [show stepK cNet (cS .x .f) (cS .x .x) = cS .x .f from funext hB1, hfix]
    rfl

/-- Feedback wire delay 1 step (pin I2 of gate 3); all other wires 0. -/
def cDl (j p : Nat) : Nat := if j = 3 ∧ p = 2 then 1 else 0

theorem cDl_le (j p : Nat) : cDl j p ≤ 1 := by unfold cDl; split <;> omega

/-- Inputs: a = 1, rst = 0, b given by `b`. -/
def cInp (b : Nat → Bool) (k n : Nat) : Bool :=
  match n with
  | 0 => true
  | 1 => b k
  | _ => false

/-- No runt reaches the pin. -/
def bNone (_ : Nat) : Bool := false
/-- A runt of two steps (steps 1, 2). -/
def bLong (k : Nat) : Bool := decide (1 ≤ k ∧ k ≤ 2)
/-- A runt of one step (step 1). -/
def bShort (k : Nat) : Bool := decide (k = 1)

def cv (b : Nat → Bool) : Nat → Nat → Bool := dv cNet cDl (cInp b) (fun _ => false)

/-- The three runs follow the two input phases of `cel_ternary`: q = 0 at
step 0 (the stable hold state), a = 1 and rst = 0 throughout, b anything in
the window and b = 0 from step 3 on; and each is a bounded run (`D = 0`,
`W = 1`). -/
theorem cel_runs_follow (b : Nat → Bool) (hb : ∀ k, 3 ≤ k → b k = false) :
    Bounded cNet (cv b) (dsim_run cNet cDl (cInp b) (fun _ => false)) 0 1 ∧
    cv b 0 3 = false ∧
    (∀ k, InputsIn cNet (cv b) (cS .x .x) k) ∧
    (∀ k, 3 ≤ k → InputsIn cNet (cv b) (cS .x .f) k) := by
  have hin : ∀ k n, cNet.node n = .input → cv b k n = cInp b k n :=
    fun k n hn => dv_input cNet cDl (cInp b) _ k n hn
  refine ⟨dsim_bounded cNet cDl (cInp b) _ 1 cDl_le, rfl, ?_, ?_⟩
  · intro k n hn
    rw [hin k n hn]
    match n, hn with
    | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | _ + 4, _ => rfl
  · intro k hk n hn
    rw [hin k n hn]
    match n, hn with
    | 0, _ => rfl | 2, _ => rfl | _ + 4, _ => rfl
    | 1, _ => show K3.admits .f (b k) = true; rw [hb k hk]; rfl

theorem cInp_periodic (b : Nat → Bool) (P k0 : Nat) (hb : ∀ k, k0 ≤ k → b (k + P) = b k) :
    ∀ k n, k0 ≤ k → cNet.node n = .input → cInp b (k + P) n = cInp b k n := by
  intro k n hk _
  unfold cInp
  split
  · rfl
  · exact hb k hk
  · rfl

/-- **Exactness of the `x`, three witnesses.** With the same input phases
(window: b = x; then b = 0, hold) and the same bounds (`D = 0`, `W = 1`):
* no runt: q = 0 for ever;
* a 2-step runt: q = 1 from step 2 on, for ever;
* a 1-step runt: q oscillates for ever with period 2 (the pulse circulates
  in the feedback loop), i.e. the run never settles.
So the ternary `x` of `cel_ternary` is genuinely reachable both as "settles
to different values" and as "does not settle": the binary-trace content of
"the loop may not settle". -/
theorem cel_x_exact :
    (∀ k, cv bNone k 3 = false) ∧
    (∀ k, 2 ≤ k → cv bLong k 3 = true) ∧
    (∀ k, 2 ≤ k → cv bShort k 3 = (k % 2 == 0)) := by
  unfold cv
  refine ⟨?_, ?_, ?_⟩
  · have hc := dsim_const cNet c_hN cDl (cInp bNone) (fun _ => false) 1 0 cDl_le
      (cInp_periodic bNone 1 0 (fun _ _ => rfl)) (by decide)
    intro k
    have := hc k 3
    rw [Nat.zero_add] at this
    rw [this]; rfl
  · have hc := dsim_const cNet c_hN cDl (cInp bLong) (fun _ => false) 1 3 cDl_le
      (cInp_periodic bLong 1 3 (fun k hk => by unfold bLong; rw [decide_eq_false (by omega), decide_eq_false (by omega)])) (by decide)
    intro k hk
    rcases Nat.lt_or_ge k 3 with h | h
    · have : k = 2 := by omega
      subst this; decide
    · have := hc (k - 3) 3
      rw [show 3 + (k - 3) = k by omega] at this
      rw [this]; decide
  · have hp := dsim_periodic cNet c_hN cDl (cInp bShort) (fun _ => false) 1 2 2 cDl_le
      (cInp_periodic bShort 2 2 (fun k hk => by unfold bShort; rw [decide_eq_false (by omega), decide_eq_false (by omega)])) (by decide)
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      intro hk
      rcases Nat.lt_or_ge k 4 with h | h
      · have h' : k = 2 ∨ k = 3 := by omega
        rcases h' with rfl | rfl <;> decide
      · have e := hp (k - 2) (by omega) 3
        rw [show k - 2 + 2 = k by omega] at e
        rw [e, ih (k - 2) (by omega) (by omega)]
        congr 1
        omega


/-! ### Exactness of the tie: `sc_tie_rising`'s `x` on q, g1, g2 -/

/-- Two sequences that agree on two consecutive steps from `k0` and are both
2-periodic from `k0` agree from `k0` on. -/
theorem period2 (f g : Nat → Bool) (k0 : Nat) (hf : ∀ k, k0 ≤ k → f (k + 2) = f k)
    (hg : ∀ k, g (k + 2) = g k) (h0 : f k0 = g k0) (h1 : f (k0 + 1) = g (k0 + 1)) :
    ∀ k, k0 ≤ k → f k = g k := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro hk
    rcases Nat.lt_or_ge k (k0 + 2) with h | h
    · rcases (show k = k0 ∨ k = k0 + 1 by omega) with rfl | rfl
      · exact h0
      · exact h1
    · have e1 := hf (k - 2) (by omega)
      have e2 := hg (k - 2)
      rw [show k - 2 + 2 = k by omega] at e1 e2
      rw [e1, e2]; exact ih (k - 2) (by omega) (by omega)

theorem odd2 (k : Nat) : ((k + 2) % 2 == 1) = (k % 2 == 1) := by
  rw [Nat.add_mod_right]
theorem even2 (k : Nat) : ((k + 2) % 2 == 0) = (k % 2 == 0) := by
  rw [Nat.add_mod_right]

/-- Inputs of the tie runs: r1 rises at `t1`, r2 at `t2`, A0 = rst = 0. -/
def tieInp (t1 t2 : Nat) (k n : Nat) : Bool :=
  match n with
  | 0 => decide (t1 ≤ k)
  | 1 => decide (t2 ≤ k)
  | _ => false

/-- 7b's `idle1` as a binary state: q = 1, everything else 0. -/
def idle1B (n : Nat) : Bool := n == 5

/-- The q feedback wire (gate 5, pin I2) is 1 step; every other wire 0. -/
def tDl (j p : Nat) : Nat := if j = 5 ∧ p = 2 then 1 else 0

theorem tDl_le (j p : Nat) : tDl j p ≤ 1 := by unfold tDl; split <;> omega

theorem tieInp_periodic (t1 t2 P k0 : Nat) (h1 : t1 ≤ k0) (h2 : t2 ≤ k0) :
    ∀ k n, k0 ≤ k → arbNet.node n = .input → tieInp t1 t2 (k + P) n = tieInp t1 t2 k n := by
  intro k n hk _
  unfold tieInp
  split
  · rw [decide_eq_true (by omega), decide_eq_true (by omega)]
  · rw [decide_eq_true (by omega), decide_eq_true (by omega)]
  · rfl

def tv (t1 t2 : Nat) : Nat → Nat → Bool := dv arbNet tDl (tieInp t1 t2) idle1B

/-- Each tie run is a bounded run (`D = 0`, `W = 1`) that satisfies the
hypotheses of `arb_tie_rising` with `T0 = max t1 t2`: server idle, no reset,
acks low at step 0, both requests high from `T0` on. -/
theorem tie_runs_ok (t1 t2 : Nat) :
    Bounded arbNet (tv t1 t2) (dsim_run arbNet tDl (tieInp t1 t2) idle1B) 0 1 ∧
    IdleServer (tv t1 t2) ∧
    (∀ k, t1 ≤ k → t2 ≤ k → tv t1 t2 k 0 = true ∧ tv t1 t2 k 1 = true) := by
  have hin : ∀ k n, arbNet.node n = .input → tv t1 t2 k n = tieInp t1 t2 k n :=
    fun k n hn => dv_input arbNet tDl (tieInp t1 t2) idle1B k n hn
  refine ⟨dsim_bounded arbNet tDl _ idle1B 1 tDl_le, ⟨?_, ?_, ?_, rfl, rfl⟩, ?_⟩
  · intro k; rw [hin k 2 rfl]; rfl
  · intro k; rw [hin k 3 rfl]; rfl
  · intro k; rw [hin k 4 rfl]; rfl
  · intro k h1 h2
    rw [hin k 0 rfl, hin k 1 rfl]
    exact ⟨decide_eq_true h1, decide_eq_true h2⟩

/-- **Exactness of the tie, three witnesses.** From `idle1`, server idle, wire
bounds `D = 0`, `W = 1` (only the q feedback wire takes a step), both requests
rise (all three runs satisfy `arb_tie_rising`'s hypotheses with `T0 = 3`, and
indeed R0 = 1 in all of them, as that theorem says):
* r1 one step before r2: client 1 wins for ever (q = 1, g1 = 1, g2 = 0);
* r2 two steps before r1: client 2 wins for ever (q = 0, g1 = 0, g2 = 1);
* r2 ONE step before r1: the reset pulse is caught in the q loop and q
  oscillates for ever, the grants alternating (g1 at even steps, g2 at odd
  steps): the run never settles. This is the binary, bounded-delay shadow of
  metastability in the state loop. It needs a pure (transport) feedback wire
  that can carry a one-step pulse; an inertial wire would filter it.
So the `x` on q, g1, g2 in `sc_tie_rising` is exact in both senses. -/
theorem arb_tie_exact :
    (∀ k, 2 ≤ k → tv 1 2 k 5 = true ∧ tv 1 2 k 6 = true ∧ tv 1 2 k 7 = false ∧
      tv 1 2 k 8 = true) ∧
    (∀ k, 3 ≤ k → tv 3 1 k 5 = false ∧ tv 3 1 k 6 = false ∧ tv 3 1 k 7 = true ∧
      tv 3 1 k 8 = true) ∧
    (∀ k, 3 ≤ k → tv 2 1 k 5 = (k % 2 == 1) ∧ tv 2 1 k 6 = (k % 2 == 0) ∧
      tv 2 1 k 7 = (k % 2 == 1) ∧ tv 2 1 k 8 = true) := by
  unfold tv
  refine ⟨?_, ?_, ?_⟩
  · have hc := dsim_const arbNet arb_hN tDl (tieInp 1 2) idle1B 1 2 tDl_le
      (tieInp_periodic 1 2 1 2 (by omega) (by omega)) (by decide)
    intro k hk
    have e := fun n => hc (k - 2) n
    rw [show 2 + (k - 2) = k by omega] at e
    rw [e 5, e 6, e 7, e 8]; decide
  · have hc := dsim_const arbNet arb_hN tDl (tieInp 3 1) idle1B 1 3 tDl_le
      (tieInp_periodic 3 1 1 3 (by omega) (by omega)) (by decide)
    intro k hk
    have e := fun n => hc (k - 3) n
    rw [show 3 + (k - 3) = k by omega] at e
    rw [e 5, e 6, e 7, e 8]; decide
  · have hp := dsim_periodic arbNet arb_hN tDl (tieInp 2 1) idle1B 1 2 3 tDl_le
      (tieInp_periodic 2 1 2 3 (by omega) (by omega)) (by decide)
    intro k hk
    exact ⟨period2 (fun k => dv arbNet tDl (tieInp 2 1) idle1B k 5) (fun k => k % 2 == 1) 3 (fun k hk => hp k hk 5) odd2
        (by decide) (by decide) k hk,
      period2 (fun k => dv arbNet tDl (tieInp 2 1) idle1B k 6) (fun k => k % 2 == 0) 3 (fun k hk => hp k hk 6) even2
        (by decide) (by decide) k hk,
      period2 (fun k => dv arbNet tDl (tieInp 2 1) idle1B k 7) (fun k => k % 2 == 1) 3 (fun k hk => hp k hk 7) odd2
        (by decide) (by decide) k hk,
      period2 (fun k => dv arbNet tDl (tieInp 2 1) idle1B k 8) (fun _ => true) 3 (fun k hk => hp k hk 8) (fun _ => rfl)
        (by decide) (by decide) k hk⟩

end Formal.Cells.TernaryPhases
