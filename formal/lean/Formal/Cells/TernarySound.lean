import Formal.Cells.Prelim
import Formal.Cells.MuxTree
import Formal.Cells.ArbKleene

/-!
# Probe 7f: soundness of two-phase ternary simulation (Eichelberger A/B)

Probe 7b (`ArbKleene.lean`) computes ternary scenarios for the arbiter and
leaves their meaning for binary runs to a prose hypothesis H_TERNARY_SIM.
This file proves that hypothesis for a general network of LUT gates and then
uses it to turn two 7b scenarios into theorems about ALL binary traces of the
arbiter network.

## The network

A `Circ` has nodes `0, 1, 2, ...` (`size` bounds the interesting ones; every
node is either an `input` or a `gate init pins`). A gate is a LUT: `lutB`
(binary) / `lutK` (Kleene, H_KLEENE_LUT) of its real INIT over its pin list;
a pin reads a node or a tied constant.

## The delay model (binary traces, discrete time `ℕ`)

A binary trace is `v : ℕ → ℕ → Bool` (`v k n` = node `n` at step `k`). A
`Run` of the network is a trace together with read times `rd k j p` such that

* **H_WIRE_CAUSAL** (`Run.rd_le`): at step `k`, pin `p` of gate `j` sees the
  value its source node had at some time `rd k j p ≤ k`. Nothing else is
  assumed: each pin has its own wire, the delay is unbounded, may vary from
  step to step and need not even be FIFO. This is strictly weaker than any
  bounded/pure/inertial wire-delay model, so it covers them all.
* **H_GMW_GATE** (`Run.gate`): in each step a gate output either keeps its
  value or takes the value of its LUT function on what its pins currently
  see. Each gate independently, any subset per step: this is Brzozowski and
  Seger's general multiple-winner (GMW) model with unbounded gate delays and
  (by the per-pin reads) unbounded wire delays.

Because every pin reads its own (stale) time, the output of a gate may be the
LUT function of ANY mixture of old and new pin values: this includes the
transient outputs of the pass-transistor mux tree during a multi-input change
(Core's `LutTree` proves those are within the Kleene closure of the
in-transit inputs, i.e. exactly such mixtures). So internal LUT hazards are
covered, not assumed away.

For the convergence result (Algorithm B) we add two bounds (`Bounded`):
* **H_WIRE_BOUND** `W`: `k ≤ rd k j p + W` (a wire is at most `W` steps old).
* **H_GATE_BOUND** `D`: a gate whose LUT function has been `b` at every step
  of `[k, k + D]` has output `b` at some step of `[k, k + D + 1]`.
`unitDelay_run` shows the hypotheses are satisfiable (the unit-delay binary
simulation is a `Run` with `D = W = 0`), so nothing below is vacuous.

## Results

1. `lutK_mono`: `lutK` is monotone in the information order (`x` on top).
   `lutK_sound`: `lutB` of a completion is admitted by `lutK`.
2. Algorithm A. `A_invariant`: any ternary state `s` with
   `stepK u s ⊑ s` (pointwise less defined) that covers the initial binary
   state covers EVERY state of every run whose inputs stay inside `u`.
   `algA_sound`: the A iteration from a state `s0 ⊑ stepK u s0` (e.g. a
   stable state for the old inputs, `stable_old_le`), once it reaches a fixed
   point, is such an `s`. `algA_terminates`: on a finite network that fixed
   point is reached within `size + 1` steps; `algA` packages both.
3. Algorithm B. `algB_stable`: every stable binary state (all gates
   quiescent, inputs final) that a run can reach is covered by every B
   iterate: a definite A-then-B node value is the value of that node in every
   reachable stable state (unbounded GMW model). `algB_bounded`: with the
   bounds `D`, `W`, after the inputs are final at `T0`, every state at time
   `≥ T0 + m·(D + W + 1)` is covered by the `m`-th B iterate: every definite
   node of the B result is reached and then held by every run.
4. The arbiter (`bd_arbiter` + ack C-elements, the 7b network, real INITs):
   `arb_acks_quiet` (any request waveform, A0 = rst = 0, acks start 0 ⇒
   acks stay 0 forever, unbounded delays), `arb_runt_opposite` and
   `arb_tie_rising` (scenarios `sc_runt_opposite`, `sc_tie_rising` as
   theorems on all bounded-delay traces), `arb_runt_opposite_stable`,
   `arb_tie_rising_stable` (unbounded delays: every reachable stable state).
-/

namespace Formal.Cells.TernarySound
open Formal.Cells

/-! ## Information order and the two LUT facts -/

/-- Information order: `le a b` iff `b` is `a` or `x` (`b` covers `a`). -/
def le (a b : K3) : Prop := a = b ∨ b = .x

instance (a b : K3) : Decidable (le a b) := inferInstanceAs (Decidable (_ ∨ _))

theorem le_refl (a : K3) : le a a := Or.inl rfl

theorem le_trans {a b c : K3} (h1 : le a b) (h2 : le b c) : le a c := by
  rcases h1 with rfl | rfl
  · exact h2
  · rcases h2 with rfl | rfl <;> exact Or.inr rfl

theorem admits_of_le {a b : K3} {c : Bool} (h : le a b) (ha : K3.admits a c = true) :
    K3.admits b c = true := by
  rcases h with rfl | rfl
  · exact ha
  · rfl

theorem admits_ofBool (b : Bool) : K3.admits (K3.ofBool b) b = true := by
  cases b <;> rfl

theorem admits_ofBool_iff (b c : Bool) : K3.admits (K3.ofBool b) c = true ↔ c = b := by
  cases b <;> cases c <;> decide

/-- Pointwise relation between two lists (core Lean has no `List.Forall2`). -/
inductive Pw {α β : Type} (r : α → β → Prop) : List α → List β → Prop where
  | nil : Pw r [] []
  | cons {a b as bs} : r a b → Pw r as bs → Pw r (a :: as) (b :: bs)

theorem completions_ne_nil (zs : List K3) : completions zs ≠ [] := by
  induction zs with
  | nil => simp [completions]
  | cons a as ih => cases a <;> simp [completions, K3.admits, ih]

/-- A Boolean vector admitted pin by pin is a completion. -/
theorem mem_completions_of_forall2 {zs : List K3} {bs : List Bool}
    (h : Pw (fun z b => K3.admits z b = true) zs bs) : bs ∈ completions zs := by
  induction h with
  | nil => simp [completions]
  | @cons a b as bs hab _ ih =>
    simp only [completions, List.mem_append]
    cases b
    · left; simp [hab, ih]
    · right; simp [hab, ih]

/-- Information-order-below input vectors have fewer completions. -/
theorem completions_mono {zs zs' : List K3} (h : Pw le zs zs') :
    ∀ c ∈ completions zs, c ∈ completions zs' := by
  induction h with
  | nil => intro c hc; exact hc
  | @cons a a' as as' haa _ ih =>
    intro c hc
    simp only [completions, List.mem_append] at hc ⊢
    rcases hc with hc | hc
    · left
      split at hc
      · next hadm =>
        simp only [admits_of_le haa hadm, ↓reduceIte]
        obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hc
        exact List.mem_map.2 ⟨w, ih w hw, rfl⟩
      · simp at hc
    · right
      split at hc
      · next hadm =>
        simp only [admits_of_le haa hadm, ↓reduceIte]
        obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hc
        exact List.mem_map.2 ⟨w, ih w hw, rfl⟩
      · simp at hc

/-- `lutK` is `t` exactly when every completion gives 1. -/
theorem lutK_eq_t_iff (init : Nat) (zs : List K3) :
    lutK init zs = .t ↔ ∀ c ∈ completions zs, lutB init c = true := by
  rw [MuxTree.lutK_eq_closure]; dsimp only
  constructor
  · intro h c hc
    split at h
    · next h1 =>
      have := List.all_eq_true.1 h1 (lutB init c) (List.mem_map.2 ⟨c, hc, rfl⟩)
      simpa using this
    · split at h <;> cases h
  · intro h
    have : ((completions zs).map (lutB init)).all id = true := by
      apply List.all_eq_true.2
      intro y hy
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hy
      simpa using h c hc
    simp [this]

/-- `lutK` is `f` exactly when every completion gives 0. -/
theorem lutK_eq_f_iff (init : Nat) (zs : List K3) :
    lutK init zs = .f ↔ ∀ c ∈ completions zs, lutB init c = false := by
  have hne := completions_ne_nil zs
  rw [MuxTree.lutK_eq_closure]; dsimp only
  constructor
  · intro h c hc
    split at h
    · cases h
    · split at h
      · next h2 =>
        have := List.all_eq_true.1 h2 (lutB init c) (List.mem_map.2 ⟨c, hc, rfl⟩)
        simpa using this
      · cases h
  · intro h
    have h2 : ((completions zs).map (lutB init)).all (!·) = true := by
      apply List.all_eq_true.2
      intro y hy
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hy
      simp [h c hc]
    have h1 : ((completions zs).map (lutB init)).all id = false := by
      match hcs : completions zs, hne with
      | c :: cs, _ =>
        have := h c (by rw [hcs]; exact List.mem_cons_self ..)
        simp [this]
    simp [h1, h2]

/-- **(1) Monotonicity.** If each input is information-below the
corresponding input of another vector (`x` above everything), the outputs
are ordered the same way. -/
theorem lutK_mono (init : Nat) {zs zs' : List K3} (h : Pw le zs zs') :
    le (lutK init zs) (lutK init zs') := by
  cases h' : lutK init zs' with
  | X => exact Or.inr rfl
  | one =>
    left
    rw [lutK_eq_t_iff] at h' ⊢
    exact fun c hc => h' c (completions_mono h c hc)
  | zero =>
    left
    rw [lutK_eq_f_iff] at h' ⊢
    exact fun c hc => h' c (completions_mono h c hc)

/-- Soundness of the closure: a Boolean vector admitted by a K3 vector gives
a LUT value admitted by the Kleene LUT. -/
theorem lutK_sound (init : Nat) {zs : List K3} {bs : List Bool}
    (h : Pw (fun z b => K3.admits z b = true) zs bs) :
    K3.admits (lutK init zs) (lutB init bs) = true := by
  have hm := mem_completions_of_forall2 h
  cases h' : lutK init zs with
  | X => rfl
  | one => rw [lutK_eq_t_iff] at h'; simp [K3.admits, h' bs hm]
  | zero => rw [lutK_eq_f_iff] at h'; simp [K3.admits, h' bs hm]

/-! ## Networks -/

/-- A LUT pin reads a node or a tied constant. -/
inductive Src where
  | node (i : Nat)
  | const (b : Bool)
  deriving DecidableEq, Repr

inductive Node where
  | input
  | gate (init : Nat) (pins : List Src)
  deriving Repr

/-- A finite network of LUT gates. Nodes `≥ size` are meant to be unused
inputs; `size` is only documentation here (no result depends on it). -/
structure Circ where
  size : Nat
  node : Nat → Node

/-- Ternary value of a pin. -/
def srcK (s : Nat → K3) : Src → K3
  | .node i => s i
  | .const b => K3.ofBool b

/-- One unit-delay (Jacobi) ternary step: inputs from `u`, every gate
re-evaluated by `lutK` from the previous state. -/
def stepK (N : Circ) (u s : Nat → K3) (n : Nat) : K3 :=
  match N.node n with
  | .input => u n
  | .gate init pins => lutK init (pins.map (srcK s))

/-- `m` Jacobi steps with inputs `u` (same recursion shape as 7b's `settle`). -/
def iter (N : Circ) (u : Nat → K3) : Nat → (Nat → K3) → (Nat → K3)
  | 0, s => s
  | m + 1, s => iter N u m (stepK N u s)

theorem iter_succ' (N : Circ) (u : Nat → K3) (m : Nat) (s : Nat → K3) :
    iter N u (m + 1) s = stepK N u (iter N u m s) := by
  induction m generalizing s with
  | zero => rfl
  | succ m ih => exact ih (stepK N u s)

/-- Binary value of a pin, `rv p i` = what pin `p` sees of node `i`. -/
def srcB (rv : Nat → Nat → Bool) (p : Nat) : Src → Bool
  | .node i => rv p i
  | .const b => b

/-- Binary pin vector; pin positions counted from `p`. -/
def pinsB (rv : Nat → Nat → Bool) : List Src → Nat → List Bool
  | [], _ => []
  | s :: ss, p => srcB rv p s :: pinsB rv ss (p + 1)

/-- A ternary state covers a binary state. -/
def covers (s : Nat → K3) (c : Nat → Bool) : Prop := ∀ n, K3.admits (s n) (c n) = true

/-- Pointwise information order on states. -/
def sle (s s' : Nat → K3) : Prop := ∀ n, le (s n) (s' n)

theorem covers_of_sle {s s' : Nat → K3} {c : Nat → Bool} (h : sle s s') (hc : covers s c) :
    covers s' c := fun n => admits_of_le (h n) (hc n)

theorem pins_forall2 (s : Nat → K3) (rv : Nat → Nat → Bool)
    (hv : ∀ p i, K3.admits (s i) (rv p i) = true) (pins : List Src) (p0 : Nat) :
    Pw (fun z b => K3.admits z b = true) (pins.map (srcK s)) (pinsB rv pins p0) := by
  induction pins generalizing p0 with
  | nil => exact Pw.nil
  | cons a as ih =>
    refine Pw.cons ?_ (ih (p0 + 1))
    cases a with
    | node i => exact hv p0 i
    | const b => exact admits_ofBool b

theorem pins_le (s s' : Nat → K3) (h : sle s s') (pins : List Src) :
    Pw le (pins.map (srcK s)) (pins.map (srcK s')) := by
  induction pins with
  | nil => exact Pw.nil
  | cons a as ih =>
    refine Pw.cons ?_ ih
    cases a with
    | node i => exact h i
    | const b => exact le_refl _

/-- The ternary step is monotone in inputs and state. -/
theorem stepK_mono (N : Circ) {u u' s s' : Nat → K3} (hu : sle u u') (hs : sle s s') :
    sle (stepK N u s) (stepK N u' s') := by
  intro n
  unfold stepK
  cases N.node n with
  | input => exact hu n
  | gate init pins => exact lutK_mono init (pins_le s s' hs pins)

/-! ## Runs: the binary delay model -/

/-- A binary trace of the network in the GMW model with per-pin unbounded
wire delays. -/
structure Run (N : Circ) (v : Nat → Nat → Bool) where
  /-- `rd k j p`: the time whose value pin `p` of gate `j` sees at step `k`. -/
  rd : Nat → Nat → Nat → Nat
  /-- **H_WIRE_CAUSAL**: a wire shows a past (or current) value of its
  source. Physical fact: causality of routing. Test: none needed. -/
  rd_le : ∀ k j p, rd k j p ≤ k
  /-- **H_GMW_GATE**: a gate output holds or takes its current LUT value.
  Physical fact: a LUT output, viewed as a binary signal, only moves to a
  value its mux tree can produce from the pin levels it currently sees (with
  the per-pin reads, any mixture of old/new levels: the tree's transients).
  Test: GLS with swept routed delays; every recorded output transition must
  be to `lutB` of some mixture of recent pin values. -/
  gate : ∀ k j init pins, N.node j = .gate init pins →
    v (k + 1) j = v k j ∨
      v (k + 1) j = lutB init (pinsB (fun p i => v (rd k j p) i) pins 0)

/-- The LUT value gate `j` sees at step `k` in run `R`. -/
def Run.exc {N : Circ} {v : Nat → Nat → Bool} (R : Run N v) (init : Nat) (pins : List Src)
    (k j : Nat) : Bool :=
  lutB init (pinsB (fun p i => v (R.rd k j p) i) pins 0)

/-- Delay bounds, used only for the convergence statement of Algorithm B. -/
structure Bounded (N : Circ) (v : Nat → Nat → Bool) (R : Run N v) (D W : Nat) : Prop where
  /-- **H_WIRE_BOUND**: a wire is at most `W` steps old. Physical fact: max
  routed wire delay (prjxray slow-max) ≤ `W` steps. Test: routed SDF. -/
  wire : ∀ k j p, k ≤ R.rd k j p + W
  /-- **H_GATE_BOUND**: a gate whose LUT value is `b` throughout `[k, k+D]`
  shows `b` by `k + D + 1`. Physical fact: LUT propagation delay (slow max)
  ≤ `D + 1` steps, and no gate is stuck. Test: routed SDF / GLS. -/
  gate : ∀ k j init pins b, N.node j = .gate init pins →
    (∀ i, k ≤ i → i ≤ k + D → R.exc init pins i j = b) →
    ∃ i, k ≤ i ∧ i ≤ k + D + 1 ∧ v i j = b

/-! ## Non-vacuity: unit-delay binary simulation is a bounded run -/

/-- Synchronous unit-delay binary simulation from `c0` with input trace `inp`. -/
def simB (N : Circ) (inp : Nat → Nat → Bool) (c0 : Nat → Bool) : Nat → Nat → Bool
  | 0 => c0
  | k + 1 => fun n =>
    match N.node n with
    | .input => inp (k + 1) n
    | .gate init pins => lutB init (pinsB (fun _ i => simB N inp c0 k i) pins 0)

def unitRun (N : Circ) (inp : Nat → Nat → Bool) (c0 : Nat → Bool) : Run N (simB N inp c0) where
  rd k _ _ := k
  rd_le _ _ _ := Nat.le_refl _
  gate k j init pins h := by
    right
    show (match N.node j with
      | .input => inp (k + 1) j
      | .gate init pins => lutB init (pinsB (fun _ i => simB N inp c0 k i) pins 0)) = _
    rw [h]

theorem unitDelay_run (N : Circ) (inp : Nat → Nat → Bool) (c0 : Nat → Bool) :
    Bounded N (simB N inp c0) (unitRun N inp c0) 0 0 where
  wire k _ _ := Nat.le_refl k
  gate k j init pins b h hb := by
    refine ⟨k + 1, Nat.le_succ k, Nat.le_refl _, ?_⟩
    have := hb k (Nat.le_refl k) (Nat.le_refl _)
    rw [← this]
    show (match N.node j with
      | .input => inp (k + 1) j
      | .gate init pins => lutB init (pinsB (fun _ i => simB N inp c0 k i) pins 0)) = _
    rw [h]; rfl

/-! ## (2) Algorithm A -/

/-- **Core of Algorithm A.** A ternary state `s` that is closed under the
step with inputs `u` (`stepK u s ⊑ s`) and covers the initial state covers
every state the run passes through, as long as the inputs stay inside `u`.
No delay bound is used. -/
theorem A_invariant (N : Circ) (u s : Nat → K3) (hpost : sle (stepK N u s) s)
    {v : Nat → Nat → Bool} (R : Run N v)
    (hin : ∀ k n, N.node n = .input → K3.admits (u n) (v k n) = true)
    (h0 : covers s (v 0)) : ∀ k, covers s (v k) := by
  have key : ∀ k, ∀ k' ≤ k, covers s (v k') := by
    intro k
    induction k with
    | zero => intro k' hk; rw [Nat.le_zero.1 hk]; exact h0
    | succ k ih =>
      intro k' hk
      rcases Nat.lt_or_ge k' (k + 1) with hlt | hge
      · exact ih k' (Nat.lt_succ_iff.1 hlt)
      · have : k' = k + 1 := Nat.le_antisymm hk hge
        subst this
        intro n
        have hp := hpost n
        unfold stepK at hp
        cases hn : N.node n with
        | input =>
          rw [hn] at hp
          exact admits_of_le hp (hin (k + 1) n hn)
        | gate init pins =>
          rw [hn] at hp
          rcases R.gate k n init pins hn with h | h
          · rw [h]; exact ih k (Nat.le_refl k) n
          · rw [h]
            apply admits_of_le hp
            apply lutK_sound
            apply pins_forall2
            intro p i
            exact ih _ (R.rd_le k n p) i
  intro k
  exact key k k (Nat.le_refl k)

/-- A state stable for the old inputs `a` (Algorithm A's start) satisfies the
chain condition for any `u ⊒ a`. -/
theorem stable_old_le (N : Circ) {a u s0 : Nat → K3} (hs : ∀ n, stepK N a s0 n = s0 n)
    (hau : sle a u) : sle s0 (stepK N u s0) := by
  intro n
  rw [← hs n]
  exact stepK_mono N hau (fun _ => le_refl _) n

/-- The A iteration from `s0 ⊑ stepK u s0` is an increasing chain. -/
theorem iter_chain (N : Circ) (u s0 : Nat → K3) (hs0 : sle s0 (stepK N u s0)) :
    ∀ m, sle (iter N u m s0) (iter N u (m + 1) s0) := by
  intro m
  induction m with
  | zero => exact hs0
  | succ m ih =>
    have ih' := ih
    rw [iter_succ' N u m] at ih'
    rw [iter_succ' N u (m + 1), iter_succ' N u m]
    exact stepK_mono N (fun _ => le_refl _) ih'

theorem iter_above (N : Circ) (u s0 : Nat → K3) (hs0 : sle s0 (stepK N u s0)) :
    ∀ m, sle s0 (iter N u m s0) := by
  intro m
  induction m with
  | zero => exact fun _ => le_refl _
  | succ m ih => exact fun n => le_trans (ih n) (iter_chain N u s0 hs0 m n)

/-- **(2) Algorithm A soundness.** Start from `s0` covering the initial binary
state with `s0 ⊑ stepK u s0` (e.g. `stable_old_le`); `u` covers every value
the inputs take during the change (`x` on changing inputs). If the A iteration
reaches a fixed point at `m`, its result covers every state every run passes
through. -/
theorem algA_sound (N : Circ) (u s0 : Nat → K3) (hs0 : sle s0 (stepK N u s0)) (m : Nat)
    (hfix : ∀ n, iter N u (m + 1) s0 n = iter N u m s0 n)
    {v : Nat → Nat → Bool} (R : Run N v)
    (hin : ∀ k n, N.node n = .input → K3.admits (u n) (v k n) = true)
    (h0 : covers s0 (v 0)) : ∀ k, covers (iter N u m s0) (v k) := by
  apply A_invariant N u _ _ R hin (covers_of_sle (iter_above N u s0 hs0 m) h0)
  intro n
  rw [← iter_succ', hfix n]
  exact le_refl _


/-! ### Termination of the A iteration -/

theorem countP_mono' {α : Type} (p q : α → Bool) :
    ∀ l : List α, (∀ a ∈ l, p a = true → q a = true) → l.countP p ≤ l.countP q := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a l ih =>
    intro h
    have := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have ha := h a (List.mem_cons_self ..)
    simp only [List.countP_cons]
    cases hp : p a <;> cases hq : q a <;> simp_all <;> omega

theorem countP_lt' {α : Type} (p q : α → Bool) :
    ∀ l : List α, (∀ a ∈ l, p a = true → q a = true) →
      (∃ a ∈ l, q a = true ∧ p a = false) → l.countP p < l.countP q := by
  intro l
  induction l with
  | nil => intro _ h; simp at h
  | cons a l ih =>
    intro h hex
    have hle := countP_mono' p q l (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have ha := h a (List.mem_cons_self ..)
    simp only [List.countP_cons]
    rcases hex with ⟨b, hb, hqb, hpb⟩
    rcases List.mem_cons.1 hb with rfl | hb'
    · rw [hqb, hpb]; simp; omega
    · have := ih (fun c hc => h c (List.mem_cons_of_mem _ hc)) ⟨b, hb', hqb, hpb⟩
      cases hp : p a <;> cases hq : q a <;> simp_all <;> omega

/-- **Algorithm A terminates.** If every node `≥ size` is an input, the A
iteration from `s0 ⊑ stepK u s0` reaches a fixed point within `size + 1`
steps (each gate node can only go from definite to `x`, once). With
`algA_sound` this gives the full Algorithm A theorem. -/
theorem algA_terminates (N : Circ) (hN : ∀ n, N.size ≤ n → N.node n = .input)
    (u s0 : Nat → K3) (hs0 : sle s0 (stepK N u s0)) :
    ∃ m, m ≤ N.size + 1 ∧ ∀ n, iter N u (m + 1) s0 n = iter N u m s0 n := by
  let cnt : Nat → Nat := fun m =>
    (List.range N.size).countP (fun n => decide (iter N u m s0 n = .x))
  have hch := iter_chain N u s0 hs0
  -- a non-fixed step (after the first) strictly increases the x count
  have hstep : ∀ m, 1 ≤ m → ¬ (∀ n, iter N u (m + 1) s0 n = iter N u m s0 n) →
      cnt m < cnt (m + 1) := by
    intro m hm hnf
    apply countP_lt'
    · intro n _ hp
      have := hch m n
      simp only [decide_eq_true_eq] at hp ⊢
      rcases this with h | h
      · rw [← h]; exact hp
      · exact h
    · apply Classical.byContradiction
      intro hne
      apply hnf
      intro n
      rcases Nat.lt_or_ge n N.size with hlt | hge
      · have hl := hch m n
        rcases hl with h | h
        · exact h.symm
        · apply Classical.byContradiction
          intro hd
          apply hne
          refine ⟨n, List.mem_range.2 hlt, by simp [h], ?_⟩
          simp only [decide_eq_false_iff_not]
          intro hx; exact hd (by rw [h, hx])
      · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        rw [iter_succ', iter_succ' N u m']
        unfold stepK
        rw [hN n hge]
  have hbound : ∀ m, cnt m ≤ N.size := by
    intro m
    have := List.countP_le_length (p := fun n => decide (iter N u m s0 n = .x))
      (l := List.range N.size)
    simpa [List.length_range] using this
  apply Classical.byContradiction
  intro hno
  have hgrow : ∀ j, j ≤ N.size + 1 → j ≤ cnt (j + 1) := by
    intro j
    induction j with
    | zero => intro _; exact Nat.zero_le _
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have h2 := hstep (j + 1) (by omega) (fun hf => hno ⟨j + 1, hj, hf⟩)
      omega
  have := hgrow (N.size + 1) (Nat.le_refl _)
  have := hbound (N.size + 1 + 1)
  omega

/-- **(2) Algorithm A, complete form.** On a finite network the A iteration
from `s0 ⊑ stepK u s0` reaches, within `size + 1` steps, a fixed point that
covers every state of every run whose inputs stay inside `u` and whose initial
state `s0` covers. -/
theorem algA (N : Circ) (hN : ∀ n, N.size ≤ n → N.node n = .input)
    (u s0 : Nat → K3) (hs0 : sle s0 (stepK N u s0))
    {v : Nat → Nat → Bool} (R : Run N v)
    (hin : ∀ k n, N.node n = .input → K3.admits (u n) (v k n) = true)
    (h0 : covers s0 (v 0)) :
    ∃ m, m ≤ N.size + 1 ∧ (∀ n, iter N u (m + 1) s0 n = iter N u m s0 n) ∧
      ∀ k, covers (iter N u m s0) (v k) := by
  obtain ⟨m, hm, hfix⟩ := algA_terminates N hN u s0 hs0
  exact ⟨m, hm, hfix, algA_sound N u s0 hs0 m hfix R hin h0⟩

/-! ## (3) Algorithm B -/

/-- A binary state is stable for final inputs `a`: inputs inside `a`, every
gate quiescent (its LUT value on the state itself is its output). -/
def StableB (N : Circ) (a : Nat → K3) (c : Nat → Bool) : Prop :=
  (∀ n, N.node n = .input → K3.admits (a n) (c n) = true) ∧
  ∀ j init pins, N.node j = .gate init pins → c j = lutB init (pinsB (fun _ i => c i) pins 0)

/-- **(3a) Algorithm B, unbounded delays.** Every stable state covered by the
A result `t0` (in particular every stable state any run reaches, by
`A_invariant`) is covered by every B iterate: a definite node of the B result
has that value in every such stable state. -/
theorem algB_stable (N : Circ) (a t0 : Nat → K3) (c : Nat → Bool) (hc : StableB N a c)
    (h0 : covers t0 c) : ∀ m, covers (iter N a m t0) c := by
  intro m
  induction m with
  | zero => exact h0
  | succ m ih =>
    rw [iter_succ']
    intro n
    unfold stepK
    cases hn : N.node n with
    | input => exact hc.1 n hn
    | gate init pins =>
      rw [hc.2 n init pins hn]
      exact lutK_sound init (pins_forall2 _ _ (fun _ i => ih i) pins 0)

/-- **(3b) Algorithm B, bounded delays.** Phase A as in `A_invariant`
(`sA` closed for `u`, inputs always inside `u`); from `T0` on the inputs are
inside `a`. Then every state at a time `≥ T0 + m·(D + W + 1)` is covered by
the `m`-th B iterate from `sA`. -/
theorem algB_bounded (N : Circ) (u a sA : Nat → K3) (hpost : sle (stepK N u sA) sA)
    {v : Nat → Nat → Bool} (R : Run N v) {D W : Nat} (hB : Bounded N v R D W)
    (hin : ∀ k n, N.node n = .input → K3.admits (u n) (v k n) = true)
    (h0 : covers sA (v 0)) (T0 : Nat)
    (hfin : ∀ k n, T0 ≤ k → N.node n = .input → K3.admits (a n) (v k n) = true) :
    ∀ m k, T0 + m * (D + W + 1) ≤ k → covers (iter N a m sA) (v k) := by
  have hA := A_invariant N u sA hpost R hin h0
  intro m
  induction m with
  | zero => intro k _; exact hA k
  | succ m ih =>
    intro k hk n
    rw [iter_succ']
    unfold stepK
    cases hn : N.node n with
    | input => exact hfin k n (by rw [Nat.succ_mul] at hk; omega) hn
    | gate init pins =>
      dsimp only
      -- from `k0` on, every read is at a time covered by the m-th iterate
      have hexc : ∀ i, T0 + m * (D + W + 1) + W ≤ i →
          K3.admits (lutK init (pins.map (srcK (iter N a m sA)))) (R.exc init pins i n) = true := by
        intro i hi
        apply lutK_sound
        apply pins_forall2
        intro p q
        have := hB.wire i n p
        exact ih _ (by omega) q
      cases hz : lutK init (pins.map (srcK (iter N a m sA))) with
      | X => rfl
      | one =>
        have hb : ∀ i, T0 + m * (D + W + 1) + W ≤ i → R.exc init pins i n = true := by
          intro i hi
          have := hexc i hi; rw [hz] at this
          simpa [K3.admits] using this
        obtain ⟨i, hi1, hi2, hvi⟩ := hB.gate (T0 + m * (D + W + 1) + W) n init pins true hn
          (fun i h1 _ => hb i h1)
        have hold : ∀ d, v (i + d) n = true := by
          intro d
          induction d with
          | zero => exact hvi
          | succ d ihd =>
            rcases R.gate (i + d) n init pins hn with h | h
            · rw [← Nat.add_assoc, h, ihd]
            · rw [← Nat.add_assoc, h]; exact hb (i + d) (by omega)
        have : k = i + (k - i) := by rw [Nat.succ_mul] at hk; omega
        rw [this, hold]; rfl
      | zero =>
        have hb : ∀ i, T0 + m * (D + W + 1) + W ≤ i → R.exc init pins i n = false := by
          intro i hi
          have := hexc i hi; rw [hz] at this
          simpa [K3.admits] using this
        obtain ⟨i, hi1, hi2, hvi⟩ := hB.gate (T0 + m * (D + W + 1) + W) n init pins false hn
          (fun i h1 _ => hb i h1)
        have hold : ∀ d, v (i + d) n = false := by
          intro d
          induction d with
          | zero => exact hvi
          | succ d ihd =>
            rcases R.gate (i + d) n init pins hn with h | h
            · rw [← Nat.add_assoc, h, ihd]
            · rw [← Nat.add_assoc, h]; exact hb (i + d) (by omega)
        have : k = i + (k - i) := by rw [Nat.succ_mul] at hk; omega
        rw [this, hold]; rfl

/-- Reading off (3b): a definite node of the `m`-th B iterate is the value of
that node in every run from `T0 + m·(D+W+1)` on. -/
theorem algB_settles (N : Circ) (u a sA : Nat → K3) (hpost : sle (stepK N u sA) sA)
    {v : Nat → Nat → Bool} (R : Run N v) {D W : Nat} (hB : Bounded N v R D W)
    (hin : ∀ k n, N.node n = .input → K3.admits (u n) (v k n) = true)
    (h0 : covers sA (v 0)) (T0 : Nat)
    (hfin : ∀ k n, T0 ≤ k → N.node n = .input → K3.admits (a n) (v k n) = true)
    (m n : Nat) (b : Bool) (hdef : iter N a m sA n = K3.ofBool b) :
    ∀ k, T0 + m * (D + W + 1) ≤ k → v k n = b := by
  intro k hk
  have := algB_bounded N u a sA hpost R hB hin h0 T0 hfin m k hk n
  rw [hdef] at this
  exact (admits_ofBool_iff b _).1 this

/-! ## (4) The arbiter network of probe 7b, as a `Circ`

Nodes: inputs 0 r1, 1 r2, 2 A0 (as `ustate.I4` sees it), 3 A0 (as the ack
C-elements see it), 4 rst; gates 5 q (`ustate` O6, fed back to its own I2),
6 g1 (`ugrant` O5), 7 g2 (`ugrant` O6), 8 R0 (`ustate` O5), 9 A1, 10 A2
(`bd_c2`). INITs and pin maps are 7b's (real RTL). O5 is the LUT of the low
32 INIT bits over I0..I4, a separate gate node with its own pin reads (an
over-approximation: on silicon O5/O6 share the input buffers). -/

open ArbKleene in
def arbNet : Circ where
  size := 11
  node n := match n with
    | 5 => .gate ST_INIT [.node 0, .node 1, .node 5, .node 4, .node 2, .const true]
    | 6 => .gate (GR_INIT % 2 ^ 32) [.node 0, .node 1, .node 5, .const false, .const false]
    | 7 => .gate GR_INIT [.node 0, .node 1, .node 5, .const false, .const false, .const true]
    | 8 => .gate (ST_INIT % 2 ^ 32) [.node 0, .node 1, .node 5, .node 4, .node 2]
    | 9 => .gate C2_INIT [.node 6, .node 3, .node 9, .node 4, .const false, .const false]
    | 10 => .gate C2_INIT [.node 7, .node 3, .node 10, .node 4, .const false, .const false]
    | _ => .input

/-- 7b's (input, state) pair as a ternary node vector. -/
def enc (i : ArbKleene.Inp) (s : ArbKleene.Net) : Nat → K3
  | 0 => i.r1
  | 1 => i.r2
  | 2 => i.a0
  | 3 => i.a0c
  | 4 => i.rst
  | 5 => s.q
  | 6 => s.g1
  | 7 => s.g2
  | 8 => s.r0
  | 9 => s.a1
  | 10 => s.a2
  | _ => .x

def encU (i : ArbKleene.Inp) : Nat → K3 := enc i ⟨.x, .x, .x, .x, .x, .x⟩

/-- The generic ternary step on `arbNet` is 7b's `step` (gates read the
previous inputs, so a new input vector shows up one step later). -/
theorem stepK_enc (i i' : ArbKleene.Inp) (s : ArbKleene.Net) :
    stepK arbNet (encU i') (enc i s) = enc i' (ArbKleene.step i s) := by
  funext n
  match n with
  | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl | 4 => rfl
  | 5 => rfl | 6 => rfl | 7 => rfl | 8 => rfl | 9 => rfl | 10 => rfl
  | _ + 11 => rfl

theorem iter_enc (i : ArbKleene.Inp) :
    ∀ (m : Nat) (s : ArbKleene.Net),
      iter arbNet (encU i) m (enc i s) = enc i (ArbKleene.settle m i s) := by
  intro m
  induction m with
  | zero => intro s; rfl
  | succ m ih => intro s; show iter _ _ m _ = _; rw [stepK_enc]; exact ih _

theorem arb_input_iff (n : Nat) : arbNet.node n = .input ↔ (n ≤ 4 ∨ 11 ≤ n) := by
  match n with
  | 0 => simp [arbNet] | 1 => simp [arbNet] | 2 => simp [arbNet] | 3 => simp [arbNet]
  | 4 => simp [arbNet]
  | 5 => simp [arbNet] | 6 => simp [arbNet] | 7 => simp [arbNet] | 8 => simp [arbNet]
  | 9 => simp [arbNet] | 10 => simp [arbNet]
  | k + 11 => simp [arbNet]

/-- The phase-A state shared by both scenarios (7b: `sc_runt_opposite`,
`sc_tie_rising`): requests `x`, A0 = rst = 0. -/
def winA : ArbKleene.Inp := ArbKleene.I .x .x .f .f
def stA : ArbKleene.Net := ⟨.x, .x, .x, .x, .f, .f⟩

theorem stA_post : sle (stepK arbNet (encU winA) (enc winA stA)) (enc winA stA) := by
  rw [stepK_enc]
  have : ArbKleene.step winA stA = stA := ArbKleene.sc_runt_opposite.2.1
  rw [this]
  exact fun _ => le_refl _

/-- Hypotheses on a binary arbiter trace common to the scenario theorems:
server idle and no reset throughout (A0 low on both fork branches, rst low),
both acks low at time 0. The requests are unconstrained (any waveform: runts,
glitches, ties). -/
structure IdleServer (v : Nat → Nat → Bool) : Prop where
  a0 : ∀ k, v k 2 = false
  a0c : ∀ k, v k 3 = false
  rst : ∀ k, v k 4 = false
  a1_0 : v 0 9 = false
  a2_0 : v 0 10 = false

theorem idle_hin {v : Nat → Nat → Bool} (h : IdleServer v) :
    ∀ k n, arbNet.node n = .input → K3.admits (encU winA n) (v k n) = true := by
  intro k n hn
  rcases (arb_input_iff n).1 hn with h4 | h11
  · match n, h4 with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => simp [encU, enc, winA, ArbKleene.I, h.a0 k, K3.admits]
    | 3, _ => simp [encU, enc, winA, ArbKleene.I, h.a0c k, K3.admits]
    | 4, _ => simp [encU, enc, winA, ArbKleene.I, h.rst k, K3.admits]
  · match n, h11 with
    | k + 11, _ => rfl

theorem idle_h0 {v : Nat → Nat → Bool} (h : IdleServer v) : covers (enc winA stA) (v 0) := by
  intro n
  match n with
  | 0 => rfl | 1 => rfl
  | 2 => simp [enc, winA, ArbKleene.I, h.a0 0, K3.admits]
  | 3 => simp [enc, winA, ArbKleene.I, h.a0c 0, K3.admits]
  | 4 => simp [enc, winA, ArbKleene.I, h.rst 0, K3.admits]
  | 5 => rfl | 6 => rfl | 7 => rfl | 8 => rfl
  | 9 => simp [enc, stA, h.a1_0, K3.admits]
  | 10 => simp [enc, stA, h.a2_0, K3.admits]
  | k + 11 => rfl

/-- **Arbiter, phase A as a trace theorem (unbounded delays).** With the
server idle (A0 = 0) and no reset, if both acks start low they stay low
FOREVER, whatever the two requests do (any waveform, runts, ties) and
whatever the gate and wire delays are (GMW, per-pin wire delays). -/
theorem arb_acks_quiet {v : Nat → Nat → Bool} (R : Run arbNet v) (h : IdleServer v) :
    ∀ k, v k 9 = false ∧ v k 10 = false := by
  intro k
  have hc := A_invariant arbNet (encU winA) (enc winA stA) stA_post R (idle_hin h) (idle_h0 h) k
  have h9 := hc 9
  have h10 := hc 10
  simp only [enc, stA, K3.admits] at h9 h10
  simp_all

/-- Generic lift of a 7b A-then-B pair: the `m+1`-th generic B iterate from the
A state is 7b's `settle m` in phase B (one extra step for the inputs). -/
theorem iterB_enc (iA iB : ArbKleene.Inp) (s : ArbKleene.Net)
    (hs : ArbKleene.step iA s = s) (m : Nat) :
    iter arbNet (encU iB) (m + 1) (enc iA s) = enc iB (ArbKleene.settle m iB s) := by
  show iter _ _ m (stepK _ _ _) = _
  rw [stepK_enc, hs, iter_enc]

def finRunt : ArbKleene.Inp := ArbKleene.I .f .t .f .f
def finTie : ArbKleene.Inp := ArbKleene.I .t .t .f .f

theorem fin_hin (iB : ArbKleene.Inp) (r1 r2 : Bool) (hiB : iB = ArbKleene.I (K3.ofBool r1) (K3.ofBool r2) .f .f)
    {v : Nat → Nat → Bool} (h : IdleServer v) (T0 : Nat)
    (h1 : ∀ k, T0 ≤ k → v k 0 = r1) (h2 : ∀ k, T0 ≤ k → v k 1 = r2) :
    ∀ k n, T0 ≤ k → arbNet.node n = .input → K3.admits (encU iB n) (v k n) = true := by
  subst hiB
  intro k n hk hn
  rcases (arb_input_iff n).1 hn with h4 | h11
  · match n, h4 with
    | 0, _ => simp only [encU, enc, ArbKleene.I]; rw [h1 k hk]; exact admits_ofBool r1
    | 1, _ => simp only [encU, enc, ArbKleene.I]; rw [h2 k hk]; exact admits_ofBool r2
    | 2, _ => simp [encU, enc, ArbKleene.I, h.a0 k, K3.admits]
    | 3, _ => simp [encU, enc, ArbKleene.I, h.a0c k, K3.admits]
    | 4, _ => simp [encU, enc, ArbKleene.I, h.rst k, K3.admits]
  · match n, h11 with
    | k + 11, _ => rfl

/-- **Scenario `sc_runt_opposite` as a theorem on all bounded-delay traces.**
Server idle, no reset, acks start low; the requests do anything until `T0`
(e.g. r1 falling while r2 rises, with runts), and from `T0` on r1 = 0,
r2 = 1. Then for every run with gate bound `D` and wire bound `W`, from
`T0 + 4·(D+W+1)` on: q = 0, g1 = 0, g2 = 1, R0 = 1, A1 = A2 = 0. -/
theorem arb_runt_opposite {v : Nat → Nat → Bool} (R : Run arbNet v) {D W : Nat}
    (hB : Bounded arbNet v R D W) (h : IdleServer v) (T0 : Nat)
    (hr1 : ∀ k, T0 ≤ k → v k 0 = false) (hr2 : ∀ k, T0 ≤ k → v k 1 = true) :
    ∀ k, T0 + 4 * (D + W + 1) ≤ k →
      v k 5 = false ∧ v k 6 = false ∧ v k 7 = true ∧ v k 8 = true ∧
      v k 9 = false ∧ v k 10 = false := by
  intro k hk
  have hc := algB_bounded arbNet (encU winA) (encU finRunt) (enc winA stA) stA_post R hB
    (idle_hin h) (idle_h0 h) T0 (fin_hin finRunt false true rfl h T0 hr1 hr2) 4 k hk
  have hfin : ArbKleene.settle 3 finRunt stA = ⟨.f, .f, .t, .t, .f, .f⟩ :=
    ArbKleene.sc_runt_opposite.2.2.1
  rw [iterB_enc winA finRunt stA ArbKleene.sc_runt_opposite.2.1 3, hfin] at hc
  have h5 := hc 5; have h6 := hc 6; have h7 := hc 7; have h8 := hc 8
  have h9 := hc 9; have h10 := hc 10
  simp only [enc, K3.admits] at h5 h6 h7 h8 h9 h10
  simp_all

/-- **Scenario `sc_tie_rising` as a theorem on all bounded-delay traces.**
Same, but from `T0` on r1 = r2 = 1 (both requests rose within the window,
any skew). Every run has R0 = 1 and A1 = A2 = 0 from `T0 + 4·(D+W+1)` on; q,
g1, g2 are `x` in the ternary result, i.e. NOT determined by the model (some
runs give client 1, some client 2: the tie). -/
theorem arb_tie_rising {v : Nat → Nat → Bool} (R : Run arbNet v) {D W : Nat}
    (hB : Bounded arbNet v R D W) (h : IdleServer v) (T0 : Nat)
    (hr1 : ∀ k, T0 ≤ k → v k 0 = true) (hr2 : ∀ k, T0 ≤ k → v k 1 = true) :
    ∀ k, T0 + 4 * (D + W + 1) ≤ k → v k 8 = true ∧ v k 9 = false ∧ v k 10 = false := by
  intro k hk
  have hc := algB_bounded arbNet (encU winA) (encU finTie) (enc winA stA) stA_post R hB
    (idle_hin h) (idle_h0 h) T0 (fin_hin finTie true true rfl h T0 hr1 hr2) 4 k hk
  have hfin : ArbKleene.settle 3 finTie stA = ⟨.x, .x, .x, .t, .f, .f⟩ :=
    ArbKleene.sc_tie_rising.2.1
  rw [iterB_enc winA finTie stA ArbKleene.sc_runt_opposite.2.1 3, hfin] at hc
  have h8 := hc 8; have h9 := hc 9; have h10 := hc 10
  simp only [enc, K3.admits] at h8 h9 h10
  simp_all

/-- The same two scenarios in the UNBOUNDED GMW model: any stable state a run
reaches after the window (inputs final) is the 7b result on every node it
makes definite. -/
theorem arb_runt_opposite_stable {v : Nat → Nat → Bool} (R : Run arbNet v)
    (h : IdleServer v) (K : Nat) (hst : StableB arbNet (encU finRunt) (v K)) :
    v K 5 = false ∧ v K 6 = false ∧ v K 7 = true ∧ v K 8 = true ∧
      v K 9 = false ∧ v K 10 = false := by
  have hA := A_invariant arbNet (encU winA) (enc winA stA) stA_post R (idle_hin h) (idle_h0 h) K
  have hc := algB_stable arbNet (encU finRunt) (enc winA stA) (v K) hst hA 4
  have hfin : ArbKleene.settle 3 finRunt stA = ⟨.f, .f, .t, .t, .f, .f⟩ :=
    ArbKleene.sc_runt_opposite.2.2.1
  rw [iterB_enc winA finRunt stA ArbKleene.sc_runt_opposite.2.1 3, hfin] at hc
  have h5 := hc 5; have h6 := hc 6; have h7 := hc 7; have h8 := hc 8
  have h9 := hc 9; have h10 := hc 10
  simp only [enc, K3.admits] at h5 h6 h7 h8 h9 h10
  simp_all

theorem arb_tie_rising_stable {v : Nat → Nat → Bool} (R : Run arbNet v)
    (h : IdleServer v) (K : Nat) (hst : StableB arbNet (encU finTie) (v K)) :
    v K 8 = true ∧ v K 9 = false ∧ v K 10 = false := by
  have hA := A_invariant arbNet (encU winA) (enc winA stA) stA_post R (idle_hin h) (idle_h0 h) K
  have hc := algB_stable arbNet (encU finTie) (enc winA stA) (v K) hst hA 4
  have hfin : ArbKleene.settle 3 finTie stA = ⟨.x, .x, .x, .t, .f, .f⟩ :=
    ArbKleene.sc_tie_rising.2.1
  rw [iterB_enc winA finTie stA ArbKleene.sc_runt_opposite.2.1 3, hfin] at hc
  have h8 := hc 8; have h9 := hc 9; have h10 := hc 10
  simp only [enc, K3.admits] at h8 h9 h10
  simp_all

end Formal.Cells.TernarySound
