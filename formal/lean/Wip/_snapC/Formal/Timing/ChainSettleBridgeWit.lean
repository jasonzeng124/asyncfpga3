import Formal.Timing.ChainSettleBridgeO4

/-!
# C-10o2: witness and counterexample for the bridge

* `pulse_inertial`: when an inertial arc carries a pulse to a pulse (conditions on the
  edges), the pair is an 8d `Inertial` channel. Used to build explicit inertial runs.
* **`bridge_witness`** (non-vacuity of every hypothesis of `genChain_of_check` at once):
  the N = 2 FASTFALL chain of 10o's `settled_example` (head `[300,400]`, ripple
  `[200,300]`, tap `[150,250]`, pulse `F = 1000`, `T = 600`): the checker's verdict is decided
  (`bridge = true`), an explicit inertial quiet run exists, and its tail satisfies O4's
  `GenChain`.
* **`settled_not_genChain`** (10o's `Settled`, i.e. chainck's exact PASS, does NOT imply O4's
  H_CHAIN_SETTLED): head `[1,10]`, ripple `[1,8]`, tap `[3,3]`, pulse `F = 1`, `T = 5`. The
  checker's exact verdict PASSES (forced set of the tail = one interval `[4, 9)`, `B = 9 ≥
  F + T + Lrip = 8`, so 10o's `Settled z 4 8` holds), but D fails (`d = false`), and an
  explicit inertial quiet run has the tail rise at 9 and FALL again at 14 while the input is
  1 (the slow head held its fall until the input's return; the lagging ripple pin lands after
  the tap released the tail). So O4's `GenChain` fails on that run. 10o's criterion only
  forbids an early rise inside `[A, B)`; a late re-fall after `B` is outside its window. D is
  the extra (sufficient) condition that excludes it.
-/

namespace Formal.Timing.ChainSettleBridgeWit
open Formal.Net Formal.Timing Formal.Timing.ChainSettle Formal.Timing.ChainSettleBridge
open Formal.Timing.ChainSettleExe Formal.Timing.ChainSettleBridgeO4
open Formal.Net.CellBind.Ops
open Formal.Net.Bridge (Inertial)

theorem pF {F T t : Nat} (h : F ≤ t ∧ t < F + T) : pulse F T t = false := (pulse_false F T t).2 h

theorem pT {F T t : Nat} (h : ¬ (F ≤ t ∧ t < F + T)) : pulse F T t = true := by
  cases e : pulse F T t with
  | true => rfl
  | false => exact absurd ((pulse_false F T t).1 e) h

theorem pulse_inertial {lo hi F T F' T' : Nat} (h1 : 1 ≤ lo) (hT : 1 ≤ T) (_hT' : 1 ≤ T')
    (ha : F + lo ≤ F') (hb : F' ≤ F + hi) (hc : F' ≤ F + T) (hd : F + T + lo ≤ F' + T')
    (he : F' + T' ≤ F + T + hi) : Inertial lo hi (pulse F T) (pulse F' T') where
  lo_pos := h1
  cause := by
    intro t hch
    have hch' : pulse F' T' (t + 1) ≠ pulse F' T' t := fun e => hch e.symm
    rcases pulse_chg hch' with e | e
    · refine ⟨by omega, fun u a b => ?_⟩
      rw [pF (by omega), pF (by omega)]
    · refine ⟨by omega, fun u a b => ?_⟩
      rw [pT (by omega), pT (by omega)]
  settle := by
    intro t ht hs
    have st : ∀ u, t - hi ≤ u → u ≤ t → pulse F T u = pulse F T (t - hi) := hs
    by_cases c1 : t < F
    · rw [pT (by omega), pT (by omega)]
    · by_cases c2 : t < F + T
      · have hlo : F' ≤ t := by
          apply Classical.byContradiction; intro hn
          have := st t (by omega) (Nat.le_refl _)
          rw [pF (by omega), pT (by omega)] at this; exact Bool.noConfusion this
        rw [pF (by omega), pF (by omega)]
      · have hhi : t < F' ∨ F' + T' ≤ t := by
          apply Classical.byContradiction; intro hn
          by_cases c3 : F ≤ t - hi
          · have := st t (by omega) (Nat.le_refl _)
            rw [pT (by omega), pF (by omega)] at this; exact Bool.noConfusion this
          · have := st F (by omega) (by omega)
            rw [pF (by omega), pT (by omega)] at this; exact Bool.noConfusion this
        rw [pT (by omega), pT (by omega)]

/-! ## A three-arc chain `0 → 1 → 2`, `0 → 2` (N = 2 FASTFALL) with explicit pin pulses -/

def net3 (hl hh rl rh pl ph : Nat) : List Arc := [⟨0, 1, hl, hh⟩, ⟨1, 2, rl, rh⟩, ⟨0, 2, pl, ph⟩]

/-- Pins: arc 0 (head), arc 1 (ripple), arc 2 (tap), each a pulse. -/
def pin3 (P0 P1 P2 : Trace) : Nat → Trace
  | 0 => P0
  | 1 => P1
  | 2 => P2
  | _ => fun _ => true

def sig3 (inp P0 P1 P2 : Trace) : Nat → Trace
  | 0 => inp
  | 1 => P0
  | 2 => fun t => P1 t && P2 t
  | _ => fun _ => true

def run3 {hl hh rl rh pl ph : Nat} {inp P0 P1 P2 : Trace}
    (i0 : Inertial hl hh inp P0) (i1 : Inertial rl rh P0 P1) (i2 : Inertial pl ph inp P2) :
    InRun ⟨net3 hl hh rl rh pl ph⟩ inp (sig3 inp P0 P1 P2) where
  pin := pin3 P0 P1 P2
  src := fun _ => rfl
  inert := by
    intro k a hk
    match k, hk with
    | 0, hk => simp [net3] at hk; subst hk; exact i0
    | 1, hk => simp [net3] at hk; subst hk; exact i1
    | 2, hk => simp [net3] at hk; subst hk; exact i2
    | k + 3, hk => simp [net3] at hk
  node := by
    intro v hv t
    constructor
    · intro h k a hk hd
      match k, hk with
      | 0, hk => simp [net3] at hk; subst hk; simp at hd; subst hd; exact h
      | 1, hk =>
        simp [net3] at hk; subst hk; simp at hd; subst hd
        simp only [sig3, Bool.and_eq_true] at h; exact h.1
      | 2, hk =>
        simp [net3] at hk; subst hk; simp at hd; subst hd
        simp only [sig3, Bool.and_eq_true] at h; exact h.2
      | k + 3, hk => simp [net3] at hk
    · intro h
      match v, hv with
      | 1, _ => exact h 0 ⟨0, 1, hl, hh⟩ rfl rfl
      | 2, _ =>
        simp only [sig3, Bool.and_eq_true]
        exact ⟨h 1 ⟨1, 2, rl, rh⟩ rfl rfl, h 2 ⟨0, 2, pl, ph⟩ rfl rfl⟩
      | v + 3, _ => rfl

theorem quiet3 {P0 P1 P2 : Trace} (h0 : P0 0 = true) (h1 : P1 0 = true) (h2 : P2 0 = true)
    {hl hh rl rh pl ph : Nat} :
    ∀ (k : Nat) (a : Arc), (net3 hl hh rl rh pl ph)[k]? = some a → pin3 P0 P1 P2 k 0 = true := by
  intro k a hk
  match k, hk with
  | 0, _ => exact h0
  | 1, _ => exact h1
  | 2, _ => exact h2
  | k + 3, hk => simp [net3] at hk

/-! ## Witness: realistic numbers, bridge PASS, explicit run, GenChain -/

def rowW : Row := { arcs := net3 300 400 200 300 150 250, N := 2, z := 2, F := 1000, T := 600, taps := [2] }

theorem rowW_verdict : verdict rowW = ⟨true, true, 1, 1250, 2100, 500, true, true, true⟩ := by decide +kernel

/-- **Non-vacuity**: every hypothesis of `genChain_of_check` holds on one run, and its
conclusion (O4's `GenChain`) follows. -/
theorem bridge_witness :
    ∃ sig, ∃ run : InRun rowW.net (pulse 1000 600) sig,
      (∀ (k : Nat) (a : Arc), rowW.net.arcs[k]? = some a → run.pin k 0 = true) ∧
      GenChain (pulse 1000 600) (sig 2) := by
  have i0 : Inertial 300 400 (pulse 1000 600) (pulse 1350 600) :=
    pulse_inertial (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have i1 : Inertial 200 300 (pulse 1350 600) (pulse 1600 600) :=
    pulse_inertial (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have i2 : Inertial 150 250 (pulse 1000 600) (pulse 1200 600) :=
    pulse_inertial (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  let run := run3 i0 i1 i2
  have hq := quiet3 (pulse_zero (by decide) : pulse 1350 600 0 = true)
    (pulse_zero (by decide) : pulse 1600 600 0 = true) (pulse_zero (by decide) : pulse 1200 600 0 = true)
    (hl := 300) (hh := 400) (rl := 200) (rh := 300) (pl := 150) (ph := 250)
  exact ⟨_, run, hq, genChain_of_check rowW_verdict (by decide) _ run hq⟩

/-! ## Counterexample: 10o `Settled` (chainck exact PASS) without O4's `GenChain` -/

def rowX : Row := { arcs := net3 1 10 1 8 3 3, N := 2, z := 2, F := 1, T := 5, taps := [2] }

theorem rowX_verdict : verdict rowX = ⟨true, true, 1, 4, 9, 2, true, true, false⟩ := by decide +kernel

theorem settled_not_genChain :
    ∃ sig, ∃ run : InRun rowX.net (pulse 1 5) sig,
      (∀ (k : Nat) (a : Arc), rowX.net.arcs[k]? = some a → run.pin k 0 = true) ∧
      Settled rowX.net (pulse 1 5) 2 4 8 ∧
      sig 2 9 = true ∧ sig 2 14 = false ∧ pulse 1 5 13 = true ∧
      ¬ GenChain (pulse 1 5) (sig 2) := by
  -- head: the input's fall held until its return; rises 10 after
  have i0 : Inertial 1 10 (pulse 1 5) (pulse 6 10) :=
    pulse_inertial (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  -- ripple pin: falls 8 after the head, rises 1 after it
  have i1 : Inertial 1 8 (pulse 6 10) (pulse 14 3) :=
    pulse_inertial (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have i2 : Inertial 3 3 (pulse 1 5) (pulse 4 5) :=
    pulse_inertial (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  let run := run3 i0 i1 i2
  have hq := quiet3 (pulse_zero (by decide) : pulse 6 10 0 = true)
    (pulse_zero (by decide) : pulse 14 3 0 = true) (pulse_zero (by decide) : pulse 4 5 0 = true)
    (hl := 1) (hh := 10) (rl := 1) (rh := 8) (pl := 3) (ph := 3)
  have hS := (exact_sound rowX_verdict rfl rfl rfl).1
  refine ⟨_, run, hq, hS, by decide, by decide, by decide, fun hg => ?_⟩
  have := ((genChain_iff _ _).1 hg).1 13 (by decide)
  exact absurd this (by decide)

end Formal.Timing.ChainSettleBridgeWit
