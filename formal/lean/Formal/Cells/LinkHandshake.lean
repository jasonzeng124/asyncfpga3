import Formal.Core.LutList
open Formal.Core.LutList

/-!
# Track 6, probe 6b: `bd_link` / `bd_pipe` four-phase handshake

Cells: `bd_link_ctl` = `bd_c2n` (`cells/rtl/bd_ce.v`, INIT `0x00B200B200B200B2`,
pins `I0=req_in I1=c_next I2=c I3=rst`), `bd_latch` (INITs `0xB8B8...`,
`0xFF33CC00B8B8B8B8`), `bd_link_dctl` (four INITs). Every gate is evaluated
from its INIT with `lutB`/`lutK` (Prelim); equations are proved, not assumed.

1. INITs.
2. `bd_pipe` of `N` stages + four-phase environment, interleaving model with
   atomic gate firings and **isochronic forks** (hypothesis **H_ISO_FORK**: node
   `C_i` reaches its three readers -- `C_{i+1}`'s `I0` / `req_out`, `C_{i-1}`'s
   `I1` / `ack_in`, the latch enables -- at the same instant). For every `N`:
   four-phase compliance of every channel (`node_moves`, `env_moves`), speed
   independence (`persist`), token conservation (`conservation`), occupancy
   bound (`bounded`), deadlock freedom (`deadlock_free`), no starvation of
   sender or receiver (`send_progress`, `recv_progress`). Scope (claude/audit
   REPORT row 21): "for every N" holds only in this model, i.e. atomic gates
   (H_FB_FAST) AND isochronic forks (H_ISO_FORK); with independent fork-branch
   delays the control is checked only for N ≤ 3 (Section 3).
3. The same with a separate unbounded delay on every fork branch, N = 1, 2, 3,
   by a finite kernel check: H_ISO_FORK is NOT needed by the control
   (`di_pipe1..3`). It is needed only on the latch-enable branch (Section 5).
4. The controller's own feedback wire: hypothesis **H_FB_FAST** (fundamental
   mode of the loop). Sufficient (`fb_refines`), and needed (`fb_hazard`).
5. Data path: latch LUT facts (binary and Kleene), a timed latch-capture
   theorem (`latch_capture`), pipe data correctness (`pipe_data`), and the
   bundling condition SETUP derived as a SUFFICIENT condition (`latch_capture`,
   `pipe_data`); `setup_iff` only unfolds SETUP's `max` recursion into explicit
   per-stage terms (an arithmetic identity, not a necessity result). Classical
   "request after data" is a sufficient special case (`arr_classical`).
   Necessity is shown on ONE trace only (`setup_needed`, L = F = 1). The audit's
   `setup_not_necessary` (claude/audit `audit/lean/B/W_Data.lean`, REPORT row
   20) gives a run that violates SETUP (7 > 5) with every other hypothesis of
   `latch_capture` and the conclusion still true (old token = new token): SETUP
   is exact only as a worst-case-data condition.
   Hypotheses **H_LUT_TRANSPORT**, **H_WIRE_TRANSPORT** (pure delays).
6. `bd_link_dctl`: INIT = header equations; hazard- and deadlock-free under
   the header's one timing assumption (**H_LT_FIRST**), N = 1, both `BROAD`;
   a hazard without it (`dctl_si_hazard`).

Not modelled: reset sequencing (states start at the reset values), the
`DELAY`/`DACK`/`SDELAY` lines as separate gates (they are buffers on one fork
branch each, i.e. covered by Section 3's branch delays for the control, and by
`e_i`/`w` in Section 5 for timing), and any link between the timed model of
Section 5 and the untimed models of Sections 2-3 (the event times `o, c, z` are
inputs to Section 5, not derived from Section 2).
-/

namespace Formal.Cells.LinkHandshake
open Formal.Cells

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

/-! ## 1. INITs -/

/-- `bd_c2n` (cells/rtl/bd_ce.v), used verbatim by `bd_link_ctl`:
pins `I0=a=req_in  I1=b=c_next  I2=q=c (own output, fed back)  I3=rst  I4=0  I5=0`. -/
def INIT_C2N : Nat := 0x00B200B200B200B2

/-- The controller LUT, evaluated from its INIT. -/
def ctlB (req cnext q rst : Bool) : Bool :=
  lutB INIT_C2N [req, cnext, q, rst, false, false]

theorem ctlB_eq (req cnext q : Bool) :
    ctlB req cnext q false = ((req && !cnext) || (q && (req || !cnext))) := by
  cases req <;> cases cnext <;> cases q <;> decide

theorem ctlB_rst (req cnext q : Bool) : ctlB req cnext q true = false := by
  cases req <;> cases cnext <;> cases q <;> decide


/-! ## 2. The N-stage pipe, interleaving model

Atomic firing of a gate = its LUT reads all pins, including its own fed-back
output, in one instant (H_FB_FAST, Section 4). A node's value is seen by all
its readers at once (H_ISO_FORK; discharged for the control in Section 3).
The environment is any four-phase sender and receiver: the sender may toggle
`req_in` exactly when `ack_in = C_0` equals it, the receiver may copy
`req_out` into `ack_out`; "may" -- the interleaving lets them wait forever,
which is how a general compliant environment is covered. Gates fire only when
excited (the LUT output differs from the node). -/

/-- A state of `bd_pipe` of `N` stages plus its environment:
`x 0` = the sender's `req_in`, `x (i+1)` = node `C_i` (`i < N`),
`x (N+1)` = the receiver's `ack_out`. Indices above `N+1` are unused. -/
abbrev St := Nat → Bool

def upd (x : Nat → Bool) (p : Nat) (v : Bool) : Nat → Bool :=
  fun j => if j = p then v else x j

/-- The reset state: every node and both environment wires low. -/
def reset : St := fun _ => false

inductive Lbl where
  | send
  | gate (i : Nat)
  | recv
  deriving DecidableEq

/-- One atomic transition. -/
inductive Step (N : Nat) : Lbl → St → St → Prop
  | send (x : St) : x 0 = x 1 → Step N .send x (upd x 0 (!x 0))
  | gate (x : St) (i : Nat) : 1 ≤ i → i ≤ N →
      ctlB (x (i-1)) (x (i+1)) (x i) false ≠ x i →
      Step N (.gate i) x (upd x i (ctlB (x (i-1)) (x (i+1)) (x i) false))
  | recv (x : St) : x (N+1) ≠ x N → Step N .recv x (upd x (N+1) (x N))

/-- Enabledness in clean form. -/
def En (N : Nat) : Lbl → St → Prop
  | .send, x => x 0 = x 1
  | .gate i, x => 1 ≤ i ∧ i ≤ N ∧ x (i-1) ≠ x i ∧ x i = x (i+1)
  | .recv, x => x (N+1) ≠ x N

theorem ctl_excited_iff (p n q : Bool) :
    ctlB p n q false ≠ q ↔ (p ≠ q ∧ q = n) := by
  cases p <;> cases n <;> cases q <;> decide

theorem ctl_excited_val (p n q : Bool) (h : ctlB p n q false ≠ q) :
    ctlB p n q false = p ∧ p = !q := by
  revert h; cases p <;> cases n <;> cases q <;> decide

theorem step_en {N l x y} (h : Step N l x y) : En N l x := by
  cases h with
  | send _ h => exact h
  | gate _ i h1 h2 h3 => exact ⟨h1, h2, (ctl_excited_iff _ _ _).1 h3⟩
  | recv _ h => exact h

theorem en_step {N l x} (h : En N l x) : ∃ y, Step N l x y := by
  cases l with
  | send => exact ⟨_, Step.send x h⟩
  | recv => exact ⟨_, Step.recv x h⟩
  | gate i =>
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨_, Step.gate x i h1 h2 ((ctl_excited_iff _ _ _).2 h3)⟩

/-- Every transition flips exactly one wire: the one its label names. -/
def pos (N : Nat) : Lbl → Nat
  | .send => 0
  | .gate i => i
  | .recv => N + 1

theorem step_eq {N l x y} (h : Step N l x y) : y = upd x (pos N l) (!x (pos N l)) := by
  cases h with
  | send _ _ => rfl
  | gate _ i _ _ h3 =>
    have := ctl_excited_val _ _ _ h3
    simp only [pos]; rw [this.1, this.2]
  | recv _ h =>
    simp only [pos]
    have : x N = !x (N+1) := by revert h; cases x N <;> cases x (N+1) <;> decide
    rw [this]


theorem upd_ne {x : Nat → Bool} {p j : Nat} (v : Bool) (h : j ≠ p) : upd x p v j = x j := by
  simp [upd, h]

theorem upd_eq (x : Nat → Bool) (p : Nat) (v : Bool) : upd x p v p = v := by
  simp [upd]

/-! ### 2a. Four-phase compliance of every channel (protocol refinement) -/

/-- **Every node moves by the four-phase rules of both its channels.** If node
`C_{i-1}` (wire `i`, `1 ≤ i ≤ N`) changes, the step was its own gate, and:
it rises only while its request (`x (i-1)`) is high and its acknowledge
(`x (i+1)`, the next node or the receiver's `ack_out`) is low, and falls only
while the request is low and the acknowledge is high. Read on the output
channel (`i = N`: `req_out = C_{N-1}`, `ack = ack_out`) this is "req rises only
when ack low, falls only when ack high"; read on the input channel (`i = 1`:
`ack_in = C_0`) it is "ack_in rises only after req_in rose, falls only after it
fell". -/
theorem node_moves {N l x y i} (hs : Step N l x y) (h1 : 1 ≤ i) (hN : i ≤ N)
    (hc : y i ≠ x i) :
    l = .gate i ∧ y i = x (i-1) ∧ x (i+1) = !y i := by
  have hy := step_eq hs
  have hen := step_en hs
  subst hy
  cases l with
  | send => exfalso; apply hc; exact upd_ne _ (by simp [pos]; omega)
  | recv => exfalso; apply hc; exact upd_ne _ (by simp [pos]; omega)
  | gate j =>
    simp only [pos] at hc ⊢
    by_cases hji : i = j
    · subst hji
      obtain ⟨_, _, h3, h4⟩ := hen
      refine ⟨rfl, ?_, ?_⟩
      · rw [upd_eq]; revert h3; cases x (i-1) <;> cases x i <;> decide
      · rw [upd_eq, ← h4]; cases x i <;> rfl
    · exact absurd (upd_ne _ hji) hc

/-- The environment wires move only by their owners, and by the four-phase
rules: the sender toggles `req_in` only when `ack_in = C_0` equals it (rise when
both low, fall when both high), the receiver copies `req_out` into `ack_out`. -/
theorem env_moves {N l x y} (hs : Step N l x y) :
    (y 0 ≠ x 0 → l = .send ∧ x 0 = x 1) ∧
    (y (N+1) ≠ x (N+1) → l = .recv ∧ y (N+1) = x N) := by
  have hy := step_eq hs
  have hen := step_en hs
  subst hy
  cases l with
  | send =>
    refine ⟨fun _ => ⟨rfl, hen⟩, fun h => absurd (upd_ne _ (by simp [pos])) h⟩
  | recv =>
    refine ⟨fun h => absurd (upd_ne _ (by simp [pos])) h, fun _ => ⟨rfl, ?_⟩⟩
    simp only [pos, upd_eq]
    simp only [En] at hen
    revert hen; cases x N <;> cases x (N+1) <;> decide
  | gate j =>
    obtain ⟨h1, h2, _, _⟩ := hen
    refine ⟨fun h => absurd (upd_ne _ (by simp [pos]; omega)) h,
            fun h => absurd (upd_ne _ (by simp [pos]; omega)) h⟩

/-! ### 2b. Speed independence: no enabled transition is ever disabled -/

/-- **Persistence (semi-modularity).** An enabled transition stays enabled when
any other transition fires. For a gate this is hazard freedom of the controller
LUT in the interleaving model: once `C_i` is excited, nothing withdraws the
excitation before it fires. For the environment it says the circuit never
withdraws a request or acknowledge it has offered. -/
theorem persist {N l l' x y} (hl : En N l x) (hs : Step N l' x y) (hne : l' ≠ l) :
    En N l y := by
  have hy := step_eq hs
  have hl' := step_en hs
  subst hy
  cases l with
  | send =>
    cases l' with
    | send => exact absurd rfl hne
    | recv =>
      simp only [En, pos] at *
      by_cases hN : N = 0
      · subst hN; exact absurd hl (Ne.symm hl')
      · rw [upd_ne (j := 0) _ (by omega), upd_ne (j := 1) _ (by omega)]; exact hl
    | gate j =>
      obtain ⟨h1, _, h3, _⟩ := hl'
      simp only [En, pos] at *
      rw [upd_ne _ (by omega)]
      by_cases hj : 1 = j
      · subst hj; exact absurd hl h3
      · rw [upd_ne _ hj]; exact hl
  | recv =>
    cases l' with
    | recv => exact absurd rfl hne
    | send =>
      simp only [En, pos] at *
      rw [upd_ne _ (by omega)]
      by_cases hN : N = 0
      · subst hN; exact absurd hl' (Ne.symm hl)
      · rw [upd_ne _ (by omega)]; exact hl
    | gate j =>
      obtain ⟨h1, h2, h3, h4⟩ := hl'
      simp only [En, pos] at *
      rw [upd_ne _ (by omega)]
      by_cases hj : N = j
      · subst hj; exact absurd h4 (Ne.symm hl)
      · rw [upd_ne _ hj]; exact hl
  | gate i =>
    obtain ⟨g1, g2, g3, g4⟩ := hl
    have hli : l' ≠ .gate i := hne
    cases l' with
    | send =>
      simp only [En, pos] at *
      refine ⟨g1, g2, ?_, ?_⟩
      · by_cases h : i = 1
        · subst h; exact absurd hl' g3
        · rw [upd_ne _ (by omega), upd_ne _ (by omega)]; exact g3
      · rw [upd_ne _ (by omega), upd_ne _ (by omega)]; exact g4
    | recv =>
      simp only [En, pos] at *
      refine ⟨g1, g2, ?_, ?_⟩
      · rw [upd_ne _ (by omega), upd_ne _ (by omega)]; exact g3
      · by_cases h : i = N
        · subst h; exact absurd g4.symm hl'
        · rw [upd_ne _ (by omega), upd_ne _ (by omega)]; exact g4
    | gate j =>
      have hji : j ≠ i := fun h => hli (by rw [h])
      obtain ⟨h1, h2, h3, h4⟩ := hl'
      simp only [En, pos] at *
      refine ⟨g1, g2, ?_, ?_⟩
      · by_cases h : j = i - 1
        · subst h
          have : i - 1 + 1 = i := by omega
          rw [this] at h4; exact absurd h4 g3
        · rw [upd_ne _ (by omega), upd_ne _ (by omega)]; exact g3
      · by_cases h : j = i + 1
        · subst h
          have : i + 1 - 1 = i := by omega
          rw [this] at h3; exact absurd g4 h3
        · rw [upd_ne _ (by omega), upd_ne _ (by omega)]; exact g4


/-! ### 2c. Tokens: the boundary-difference picture

`d x j` (`j = 0..N`) is true when wire `j` and wire `j+1` differ: a transition
has been sent across boundary `j` and not yet answered. `d x 0` is the input
channel (`req_in` vs `C_0`), `d x (i+1)` is stage `i`'s output (`C_i` vs the
next node, or `ack_out` for the last stage). One such difference is one
*half token* (one phase of the four-phase cycle; a data token is a rising
difference followed by a falling one). A gate moves a difference one boundary
forward, the sender creates one at boundary `0`, the receiver absorbs one at
boundary `N`. -/

def d (x : St) (j : Nat) : Bool := x j != x (j+1)

/-- Weighted count of the true entries of `e` below `k`. -/
def S (w : Nat → Nat) (e : Nat → Bool) : Nat → Nat
  | 0 => 0
  | k+1 => S w e k + (if e k then w k else 0)

theorem S_upd (w : Nat → Nat) (e : Nat → Bool) (p : Nat) (v : Bool) (k : Nat) :
    S w (upd e p v) k + (if p < k then (if e p then w p else 0) else 0) =
    S w e k + (if p < k then (if v then w p else 0) else 0) := by
  induction k with
  | zero => simp [S]
  | succ k ih =>
    simp only [S]
    by_cases hk : k = p
    · subst hk
      have h1 : ¬ k < k := Nat.lt_irrefl k
      simp only [h1, if_false, Nat.add_zero] at ih
      simp only [Nat.lt_succ_self, if_true, upd_eq, ih]
      omega
    · rw [upd_ne _ hk]
      by_cases hp : p < k
      · have hp' : p < k + 1 := by omega
        simp only [hp, hp', if_true] at ih ⊢
        omega
      · have hp' : ¬ p < k + 1 := by omega
        simp only [hp, hp', if_false] at ih ⊢
        omega

theorem S_le (e : Nat → Bool) (k : Nat) : S (fun _ => 1) e k ≤ k := by
  induction k with
  | zero => simp [S]
  | succ k ih => simp only [S]; split <;> omega

theorem S_false (w : Nat → Nat) (k : Nat) : S w (fun _ => false) k = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [S, ih]

/-- Number of half tokens in flight (input wire plus the `N` stages). -/
def cnt (N : Nat) (x : St) : Nat := S (fun _ => 1) (d x) (N+1)

/-- How each transition moves the differences. -/
theorem d_send {x : St} (h : x 0 = x 1) : d (upd x 0 (!x 0)) = upd (d x) 0 true := by
  funext j
  by_cases hj : j = 0
  · subst hj; simp [d, upd, h]
  · rw [upd_ne _ hj]; simp only [d, upd]
    rw [if_neg hj, if_neg (by omega)]

theorem d_recv {N} {x : St} (h : x (N+1) ≠ x N) (j : Nat) (hj0 : j ≤ N) :
    d (upd x (N+1) (x N)) j = upd (d x) N false j := by
  by_cases hj : j = N
  · subst hj; simp [d, upd]
  · rw [upd_ne _ hj]; simp only [d, upd]
    rw [if_neg (by omega), if_neg (by omega)]

theorem d_gate {x : St} {i} (h1 : 1 ≤ i) (h3 : x (i-1) ≠ x i) (h4 : x i = x (i+1)) :
    d (upd x i (!x i)) = upd (upd (d x) (i-1) false) i true := by
  funext j
  by_cases hj : j = i
  · subst hj; simp only [upd_eq, d, upd, if_neg (show j + 1 ≠ j by omega), if_true]
    rw [← h4]; cases x j <;> rfl
  · rw [upd_ne _ hj]
    by_cases hj' : j = i - 1
    · subst hj'; rw [upd_eq]
      have : i - 1 + 1 = i := by omega
      simp only [d, upd, this, if_true, if_neg (show i - 1 ≠ i by omega)]
      revert h3; cases x (i-1) <;> cases x i <;> decide
    · rw [upd_ne _ hj']; simp only [d, upd]
      rw [if_neg hj, if_neg (by omega)]

theorem S_congr (w : Nat → Nat) {e e' : Nat → Bool} (k : Nat)
    (h : ∀ j, j < k → e j = e' j) : S w e k = S w e' k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [S]
    rw [ih (fun j hj => h j (by omega)), h k (by omega)]

/-- Enabledness read on the differences. -/
theorem en_d {N l x} : En N l x ↔ match l with
    | .send => d x 0 = false
    | .gate i => 1 ≤ i ∧ i ≤ N ∧ d x (i-1) = true ∧ d x i = false
    | .recv => d x N = true := by
  cases l with
  | send => simp only [En, d]; cases x 0 <;> cases x 1 <;> decide
  | recv => simp only [En, d]; cases x N <;> cases x (N+1) <;> decide
  | gate i =>
    simp only [En, d]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      have : i - 1 + 1 = i := by omega
      rw [this]; refine ⟨h1, h2, ?_, ?_⟩
      · revert h3; cases x (i-1) <;> cases x i <;> decide
      · rw [h4]; cases x (i+1) <;> rfl
    · rintro ⟨h1, h2, h3, h4⟩
      have : i - 1 + 1 = i := by omega
      rw [this] at h3; refine ⟨h1, h2, ?_, ?_⟩
      · revert h3; cases x (i-1) <;> cases x i <;> decide
      · revert h4; cases x i <;> cases x (i+1) <;> decide

/-- Generic: weighted count after a transition. -/
theorem S_step {N l x y} (w : Nat → Nat) (hs : Step N l x y) :
    match l with
    | .send => S w (d y) (N+1) = S w (d x) (N+1) + w 0
    | .gate i => S w (d y) (N+1) + w (i-1) = S w (d x) (N+1) + w i
    | .recv => S w (d y) (N+1) + w N = S w (d x) (N+1) := by
  have hen := en_d.1 (step_en hs)
  cases hs with
  | send _ h =>
    simp only at hen ⊢; rw [d_send h]
    have := S_upd w (d x) 0 true (N+1)
    simp only [show 0 < N + 1 by omega, if_true, hen, Bool.false_eq_true, ↓reduceIte] at this
    omega
  | recv _ h =>
    simp only at hen ⊢
    rw [S_congr w (N+1) (fun j hj => d_recv h j (by omega))]
    have := S_upd w (d x) N false (N+1)
    simp only [show N < N + 1 by omega, if_true, hen, Bool.false_eq_true, ↓reduceIte] at this
    omega
  | gate _ i g1 g2 g3 =>
    simp only at hen ⊢
    obtain ⟨h1, h2, h3, h4⟩ := hen
    have hv := ctl_excited_val _ _ _ g3
    obtain ⟨_, _, e3, e4⟩ := step_en (Step.gate x i g1 g2 g3)
    rw [hv.1, hv.2, d_gate h1 e3 e4]
    have A := S_upd w (upd (d x) (i-1) false) i true (N+1)
    have B := S_upd w (d x) (i-1) false (N+1)
    rw [upd_ne _ (show i ≠ i - 1 by omega), h4] at A
    simp only [show i < N + 1 by omega, show i - 1 < N + 1 by omega, if_true, h3,
      Bool.false_eq_true, ↓reduceIte] at A B
    omega

/-- **Probe item (1), one stage.** `bd_link` between a four-phase sender and
receiver: `req_out = ack_in = C_0`. `C_0` rises only while `req_in` is high and
`ack_out` low, falls only while `req_in` is low and `ack_out` high; so the
output pair `(req_out, ack_out)` is four-phase (req rises only when ack low,
falls only when ack high) and so is the input pair `(req_in, ack_in)`. -/
theorem link1_four_phase {l x y} (hs : Step 1 l x y) (hc : y 1 ≠ x 1) :
    (y 1 = true → x 0 = true ∧ x 2 = false) ∧ (y 1 = false → x 0 = false ∧ x 2 = true) := by
  obtain ⟨_, h1, h2⟩ := node_moves hs (Nat.le_refl 1) (Nat.le_refl 1) hc
  simp only [Nat.sub_self] at h1
  constructor
  · intro hy; rw [hy] at h1 h2; exact ⟨h1.symm, h2⟩
  · intro hy; rw [hy] at h1 h2; exact ⟨h1.symm, h2⟩

/-- Reachability from reset, counting sender and receiver transitions. -/
inductive Reach (N : Nat) : St → Nat → Nat → Prop
  | init : Reach N reset 0 0
  | send {x y s r} : Reach N x s r → Step N .send x y → Reach N y (s+1) r
  | gate {x y s r i} : Reach N x s r → Step N (.gate i) x y → Reach N y s r
  | recv {x y s r} : Reach N x s r → Step N .recv x y → Reach N y s (r+1)

/-- **No token is lost or duplicated.** In every reachable state, the half
tokens in flight are exactly the sender's transitions minus the receiver's. -/
theorem conservation {N x s r} (h : Reach N x s r) : cnt N x + r = s := by
  induction h with
  | init =>
    have : d reset = fun _ => false := by funext j; rfl
    simp [cnt, this, S_false]
  | send _ hs ih => have := S_step (fun _ => 1) hs; simp only [cnt] at *; omega
  | gate _ hs ih => have := S_step (fun _ => 1) hs; simp only [cnt] at *; omega
  | recv _ hs ih => have := S_step (fun _ => 1) hs; simp only [cnt] at *; omega

/-- **Bounded occupancy.** At most `N+1` half tokens in flight: one per stage
(half a data token per stage) plus one on the input channel. So the sender is
never more than `N+1` transitions ahead of the receiver, i.e. the receiver
never sees a transition that was not sent (`r ≤ s`) and the sender cannot run
away (`s ≤ r + N + 1`). -/
theorem bounded {N x s r} (h : Reach N x s r) : r ≤ s ∧ s ≤ r + (N + 1) := by
  have h1 := conservation h
  have h2 := S_le (d x) (N+1)
  simp only [cnt] at h1
  omega


/-! ### 2d. Deadlock freedom and progress -/

theorem ivt (e : Nat → Bool) (n : Nat) (h0 : e 0 = true) (hn : e n = false) :
    ∃ i, 1 ≤ i ∧ i ≤ n ∧ e (i-1) = true ∧ e i = false := by
  induction n with
  | zero => rw [h0] at hn; cases hn
  | succ n ih =>
    cases h : e n with
    | true => exact ⟨n+1, by omega, by omega, by simpa using h, hn⟩
    | false =>
      obtain ⟨i, h1, h2, h3, h4⟩ := ih h
      exact ⟨i, h1, by omega, h3, h4⟩

/-- **Deadlock freedom.** In EVERY state (reachable or not) of a pipe of
`N` stages, some transition is enabled: the sender may send, the receiver
may consume, or some controller is excited. With an environment that always
sends when the protocol lets it and always consumes, the system never stops.
Scope: this is the Section 2 model (atomic gates, H_FB_FAST; isochronic forks,
H_ISO_FORK). With a delay on every fork branch it is checked only for N ≤ 3
(`di_pipe1..3`). -/
theorem deadlock_free (N : Nat) (x : St) : ∃ l y, Step N l x y := by
  cases h0 : d x 0 with
  | false => exact ⟨.send, en_step (en_d.2 h0)⟩
  | true =>
    cases hn : d x N with
    | true => exact ⟨.recv, en_step (en_d.2 hn)⟩
    | false =>
      obtain ⟨i, h1, h2, h3, h4⟩ := ivt (d x) N h0 hn
      exact ⟨.gate i, en_step (en_d.2 ⟨h1, h2, h3, h4⟩)⟩

/-- Potential for "a send must come": position-weighted half tokens. -/
def Phi (N : Nat) (x : St) : Nat := S (fun j => N + 1 - j) (d x) (N+1)

theorem S_compl (w : Nat → Nat) (e : Nat → Bool) (k : Nat) :
    S w e k + S w (fun j => !e j) k = S w (fun _ => true) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [S]
    by_cases h : e k = true
    · simp [h]; omega
    · simp [h]; omega

/-- Potential for "a receive must come": position-weighted empty boundaries. -/
def Psi (N : Nat) (x : St) : Nat := S (fun j => j + 1) (fun j => !d x j) (N+1)

theorem Phi_dec {N l x y} (hs : Step N l x y) (hl : l ≠ .send) : Phi N y < Phi N x := by
  have := S_step (fun j => N + 1 - j) hs
  have hen := step_en hs
  cases l with
  | send => exact absurd rfl hl
  | recv => simp only [Phi] at *; omega
  | gate i => obtain ⟨h1, h2, _, _⟩ := hen; simp only [Phi] at *; omega

theorem Psi_dec {N l x y} (hs : Step N l x y) (hl : l ≠ .recv) : Psi N y < Psi N x := by
  have := S_step (fun j => j + 1) hs
  have hen := step_en hs
  have cx := S_compl (fun j => j + 1) (d x) (N+1)
  have cy := S_compl (fun j => j + 1) (d y) (N+1)
  cases l with
  | recv => exact absurd rfl hl
  | send => simp only [Psi] at *; omega
  | gate i => obtain ⟨h1, h2, _, _⟩ := hen; simp only [Psi] at *; omega

/-- A path of `n` transitions whose labels all satisfy `P`. -/
inductive Path (N : Nat) (P : Lbl → Prop) : St → Nat → Prop
  | nil (x : St) : Path N P x 0
  | cons {l x y n} : Step N l x y → P l → Path N P y n → Path N P x (n+1)

theorem S_mono (w : Nat → Nat) (e : Nat → Bool) (k : Nat) :
    S w e k ≤ S w (fun _ => true) k := by
  have := S_compl w e k; omega

/-- **The sender is never starved.** No run of more than `Phi N x` transitions
avoids the sender; `Phi N x ≤ 1 + 2 + ... + (N+1)`. -/
theorem send_progress {N x n} (h : Path N (· ≠ .send) x n) : n ≤ Phi N x := by
  induction h with
  | nil => exact Nat.zero_le _
  | cons hs hl _ ih => have := Phi_dec hs hl; omega

/-- **The receiver is never starved.** No run of more than `Psi N x` transitions
avoids the receiver; `Psi N x ≤ 1 + 2 + ... + (N+1)`. Together with
`deadlock_free`: with a greedy environment every run is infinite and, in it,
sends and receives each recur within every window of
`(N+1)(N+2)/2 + 1` transitions. -/
theorem recv_progress {N x n} (h : Path N (· ≠ .recv) x n) : n ≤ Psi N x := by
  induction h with
  | nil => exact Nat.zero_le _
  | cons hs hl _ ih => have := Psi_dec hs hl; omega

theorem Phi_le (N : Nat) (x : St) : Phi N x ≤ S (fun j => N + 1 - j) (fun _ => true) (N+1) :=
  S_mono _ _ _

theorem Psi_le (N : Nat) (x : St) : Psi N x ≤ S (fun j => j + 1) (fun _ => true) (N+1) :=
  S_mono _ _ _

/-! ### 2e. N = 1, 2, 3 -/

/-- The window bound evaluated: 3 for one stage, 6 for two, 10 for three. -/
example : S (fun j => 1 + 1 - j) (fun _ => true) (1+1) = 3 := rfl
example : S (fun j => 2 + 1 - j) (fun _ => true) (2+1) = 6 := rfl
example : S (fun j => 3 + 1 - j) (fun _ => true) (3+1) = 10 := rfl
example : S (fun j => j + 1) (fun _ => true) (3+1) = 10 := rfl

theorem pipe2_bounded {x s r} (h : Reach 2 x s r) : r ≤ s ∧ s ≤ r + 3 := bounded h
theorem pipe3_bounded {x s r} (h : Reach 3 x s r) : r ≤ s ∧ s ≤ r + 4 := bounded h
theorem pipe2_live (x : St) : ∃ l y, Step 2 l x y := deadlock_free 2 x
theorem pipe3_live (x : St) : ∃ l y, Step 3 l x y := deadlock_free 3 x

/-- The occupancy bound is attained: two stages can hold three half tokens
(one on the input wire, one in each stage) when the receiver stalls. -/
theorem pipe2_full : ∃ x, Reach 2 x 3 0 ∧ cnt 2 x = 3 :=
  ⟨_, Reach.send (Reach.gate (Reach.send (Reach.gate (Reach.gate
      (Reach.send Reach.init (Step.send _ (by decide)))
      (Step.gate _ 1 (by decide) (by decide) (by decide)))
      (Step.gate _ 2 (by decide) (by decide) (by decide)))
      (Step.send _ (by decide)))
      (Step.gate _ 1 (by decide) (by decide) (by decide)))
      (Step.send _ (by decide)), by decide⟩



/-! ## 3. Wire delays on every fork branch: N = 1, 2, 3 by finite check

Section 2 lets a node's fork reach all its readers at once (isochronic forks).
Here every branch of every fork is its own wire with an unbounded delay, an
interleaving variable that copies its driver ("a buffer"): this is the
delay-insensitive model of the control network. Bit layout of a state `s`
(`V = 3N+4` bits): `0 r` (sender's req), `1 rw` (req as seen at `C_0`), then per
stage `i`: `2+3i c_i` (the node), `3+3i f_i` (`c_i` at the next stage's `I0`, or
at the receiver), `4+3i b_i` (`c_i` at the previous stage's `I1`, or at the
sender); `3N+2 a` (receiver's ack), `3N+3 aw` (ack as seen at `C_{N-1}`).
The node's own feedback pin still reads `c_i` itself (atomic gate: hypothesis
`H_FB_FAST`, Section 4). The latch-enable branch is not read by any control
gate, so it does not affect this check (it is the data-path issue of
Section 5).

The reachable set is given as a bitmask `maskN` (computed outside Lean); the
kernel checks that it contains reset and is closed under every enabled
transition, so it over-approximates the reachable states, and checks the
properties on all of it. Pure kernel evaluation (`decide +kernel`, which
adds no axiom; checked with `#print axioms`). -/

def diNext (N s v : Nat) : Bool :=
  if v = 0 then (if s.testBit 0 = s.testBit 4 then !s.testBit 0 else s.testBit 0)
  else if v = 1 then s.testBit 0
  else if v = 3*N+2 then s.testBit (3*(N-1)+3)
  else if v = 3*N+3 then s.testBit (3*N+2)
  else if (v-2) % 3 = 0 then
      ctlB (if (v-2)/3 = 0 then s.testBit 1 else s.testBit (3*((v-2)/3-1)+3))
           (if (v-2)/3 = N-1 then s.testBit (3*N+3) else s.testBit (3*((v-2)/3+1)+4))
           (s.testBit v) false
  else s.testBit (3*((v-2)/3)+2)

/-! ### Generic finite checker

A model is `V` Boolean variables packed in a `Nat`, a next-value function `nx`
(variable `v` is excited in `s` when `nx s v` differs from bit `v`; firing
flips the bit), an initial state, and a scheduling filter `allow s v` (which
excited variables may fire; `true` everywhere = pure interleaving / unbounded
delays). -/

def gEx (nx : Nat → Nat → Bool) (s v : Nat) : Bool := nx s v != s.testBit v
def gFire (s v : Nat) : Nat := s ^^^ (2^v)

inductive GReach (V : Nat) (nx : Nat → Nat → Bool) (allow : Nat → Nat → Bool) (s0 : Nat) :
    Nat → Prop
  | init : GReach V nx allow s0 s0
  | step {s v} : GReach V nx allow s0 s → v < V → gEx nx s v = true → allow s v = true →
      GReach V nx allow s0 (gFire s v)

def allBelow (n : Nat) (p : Nat → Bool) : Bool := (List.range n).all p

theorem allBelow_spec {n p} (h : allBelow n p = true) {k} (hk : k < n) : p k = true :=
  List.all_eq_true.1 h k (List.mem_range.2 hk)

/-- Per-state obligations: closure under every allowed firing; every allowed
firing leaves every OTHER excited variable excited (persistence; this is
checked against all excited variables, allowed or not); some allowed variable
is excited (no deadlock). -/
def gOk (V : Nat) (nx : Nat → Nat → Bool) (allow : Nat → Nat → Bool) (mask s : Nat) : Bool :=
  allBelow V (fun v => !(gEx nx s v && allow s v) || mask.testBit (gFire s v)) &&
  allBelow V (fun u => !(gEx nx s u && allow s u) ||
    allBelow V (fun v => u == v || !gEx nx s v || gEx nx (gFire s u) v)) &&
  (List.range V).any (fun v => gEx nx s v && allow s v)

def gCheck (V : Nat) (nx : Nat → Nat → Bool) (allow : Nat → Nat → Bool) (s0 mask : Nat) : Bool :=
  decide (s0 < 2^V) && mask.testBit s0 &&
  allBelow (2^V) (fun s => !mask.testBit s || gOk V nx allow mask s)

theorem gReach_lt {V nx allow s0 s} (h0 : s0 < 2^V) (h : GReach V nx allow s0 s) : s < 2^V := by
  induction h with
  | init => exact h0
  | step _ hv _ _ ih => exact Nat.xor_lt_two_pow ih (Nat.pow_lt_pow_right (by decide) hv)

theorem g_sound {V nx allow s0 mask} (hc : gCheck V nx allow s0 mask = true) {s}
    (h : GReach V nx allow s0 s) : mask.testBit s = true ∧ gOk V nx allow mask s = true := by
  simp only [gCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨h0, hm0⟩, hall⟩ := hc
  induction h with
  | init =>
    refine ⟨hm0, ?_⟩
    have := allBelow_spec hall h0
    simpa [hm0] using this
  | @step s' v hr hv he ha ih =>
    have hm : mask.testBit (gFire s' v) = true := by
      have := (allBelow_spec (by simp only [gOk, Bool.and_eq_true] at ih; exact ih.2.1.1) hv)
      simpa [he, ha] using this
    refine ⟨hm, ?_⟩
    have := allBelow_spec hall (gReach_lt h0 (GReach.step hr hv he ha))
    simpa [hm] using this

/-- What a successful check gives, for every reachable state: persistence of
every excited variable against every other allowed firing, and liveness. -/
theorem g_props {V nx allow s0 mask} (hc : gCheck V nx allow s0 mask = true) {s}
    (h : GReach V nx allow s0 s) :
    (∀ u v, u < V → v < V → u ≠ v → gEx nx s u = true → allow s u = true →
       gEx nx s v = true → gEx nx (gFire s u) v = true) ∧
    (∃ v, v < V ∧ gEx nx s v = true ∧ allow s v = true) := by
  have hok := (g_sound hc h).2
  simp only [gOk, Bool.and_eq_true] at hok
  refine ⟨fun u v hu hv huv eu au ev => ?_, ?_⟩
  · have h1 := allBelow_spec hok.1.2 hu
    simp only [eu, au, Bool.and_self, Bool.not_true, Bool.false_or] at h1
    have h2 := allBelow_spec h1 hv
    simpa [huv, ev] using h2
  · obtain ⟨v, hv, ev⟩ := List.any_eq_true.1 hok.2
    simp only [Bool.and_eq_true] at ev
    exact ⟨v, List.mem_range.1 hv, ev.1, ev.2⟩

/-- No scheduling constraint. -/
def anyOrder : Nat → Nat → Bool := fun _ _ => true

def mask1 : Nat := 0xd1018b0b0001000bd0008000d0d1808b

theorem diCheck1 : gCheck (3*1+4) (diNext 1) anyOrder 0 mask1 = true := by decide +kernel

/-- **1 stage(s), every fork branch delayed independently, unbounded gate and
wire delays:** in every reachable state no excited wire or gate is ever
disabled by another firing (speed independence of the control network under
these wire delays) and something is excited (no deadlock). -/
theorem di_pipe1 {s} (h : GReach (3*1+4) (diNext 1) anyOrder 0 s) :
    (∀ u v, u < 3*1+4 → v < 3*1+4 → u ≠ v → gEx (diNext 1) s u = true →
       anyOrder s u = true → gEx (diNext 1) s v = true →
       gEx (diNext 1) (gFire s u) v = true) ∧
    (∃ v, v < 3*1+4 ∧ gEx (diNext 1) s v = true ∧ anyOrder s v = true) :=
  g_props diCheck1 h

def mask2 : Nat := 0xd1018b0b0001000b000000000001000bd0008000d0d1808b00000000d0d1808b0000000000000000000000000001000b000000000000000000000000d0d1808bd1018b0b000000000000000000000000d0008000000000000000000000000000d1018b0b00000000d1018b0b0001000bd000800000000000d0008000d0d1808b

theorem diCheck2 : gCheck (3*2+4) (diNext 2) anyOrder 0 mask2 = true := by decide +kernel

/-- **2 stage(s), every fork branch delayed independently, unbounded gate and
wire delays:** in every reachable state no excited wire or gate is ever
disabled by another firing (speed independence of the control network under
these wire delays) and something is excited (no deadlock). -/
theorem di_pipe2 {s} (h : GReach (3*2+4) (diNext 2) anyOrder 0 s) :
    (∀ u v, u < 3*2+4 → v < 3*2+4 → u ≠ v → gEx (diNext 2) s u = true →
       anyOrder s u = true → gEx (diNext 2) s v = true →
       gEx (diNext 2) (gFire s u) v = true) ∧
    (∃ v, v < 3*2+4 ∧ gEx (diNext 2) s v = true ∧ anyOrder s v = true) :=
  g_props diCheck2 h

def mask3 : Nat := 0xd1018b0b0001000b000000000001000bd0008000d0d1808b00000000d0d1808b0000000000000000000000000001000b000000000000000000000000d0d1808b00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000b000000000000000000000000d0d1808bd1018b0b000000000000000000000000d0008000000000000000000000000000d1018b0b00000000d1018b0b0001000bd000800000000000d0008000d0d1808b0000000000000000000000000000000000000000000000000000000000000000d1018b0b00000000d1018b0b0001000bd000800000000000d0008000d0d1808b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000b000000000000000000000000d0d1808b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d1018b0b00000000d1018b0b0001000bd000800000000000d0008000d0d1808bd1018b0b0001000b000000000001000bd0008000d0d1808b00000000d0d1808b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d1018b0b000000000000000000000000d0008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d1018b0b0001000b000000000001000bd0008000d0d1808b00000000d0d1808b0000000000000000000000000000000000000000000000000000000000000000d1018b0b0001000b000000000001000bd0008000d0d1808b00000000d0d1808b0000000000000000000000000001000b000000000000000000000000d0d1808bd1018b0b000000000000000000000000d00080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d1018b0b000000000000000000000000d0008000000000000000000000000000d1018b0b00000000d1018b0b0001000bd000800000000000d0008000d0d1808b

theorem diCheck3 : gCheck (3*3+4) (diNext 3) anyOrder 0 mask3 = true := by decide +kernel

/-- **3 stage(s), every fork branch delayed independently, unbounded gate and
wire delays:** in every reachable state no excited wire or gate is ever
disabled by another firing (speed independence of the control network under
these wire delays) and something is excited (no deadlock). -/
theorem di_pipe3 {s} (h : GReach (3*3+4) (diNext 3) anyOrder 0 s) :
    (∀ u v, u < 3*3+4 → v < 3*3+4 → u ≠ v → gEx (diNext 3) s u = true →
       anyOrder s u = true → gEx (diNext 3) s v = true →
       gEx (diNext 3) (gFire s u) v = true) ∧
    (∃ v, v < 3*3+4 ∧ gEx (diNext 3) s v = true ∧ anyOrder s v = true) :=
  g_props diCheck3 h

/-! ## 4. The controller's own feedback wire: hypothesis `H_FB_FAST`

Sections 2 and 3 fire a controller atomically: the LUT reads its own output
on pin `I2` with no delay. Physically `O -> I2` is a routed wire. Here it is a
separate variable `fb i` with its own unbounded delay. The model then needs the
named hypothesis

* **H_FB_FAST** (fundamental mode of the controller loop): after node `C_i`
  changes, its feedback pin sees the new value before any other wire of the
  network changes. Physically: the `O -> I2` feedback wire delay is shorter than
  the fastest round trip from `C_i` through a neighbour and back to a pin of
  `C_i` (`C_i` -> wire -> sender/neighbour controller -> wire -> `I0`, and
  likewise through `I1`). Test: routed GLS / prjxray timing, feedback net max
  delay against that round trip's min; on the board, a ring oscillator built
  from the cell with the neighbour path shortened until it glitches.

`fb_refines`: under H_FB_FAST (as a schedule) the model is exactly the atomic
one. `fb_hazard`: without it, a one-stage link produces a runt on `req_out`,
violating four-phase on the output channel. -/

structure FSt where
  x : St
  fb : St

inductive FStep (N : Nat) : FSt → FSt → Prop
  | send (σ : FSt) : σ.x 0 = σ.x 1 → FStep N σ ⟨upd σ.x 0 (!σ.x 0), σ.fb⟩
  | gate (σ : FSt) (i : Nat) : 1 ≤ i → i ≤ N →
      ctlB (σ.x (i-1)) (σ.x (i+1)) (σ.fb i) false ≠ σ.x i →
      FStep N σ ⟨upd σ.x i (ctlB (σ.x (i-1)) (σ.x (i+1)) (σ.fb i) false), σ.fb⟩
  | recv (σ : FSt) : σ.x (N+1) ≠ σ.x N → FStep N σ ⟨upd σ.x (N+1) (σ.x N), σ.fb⟩
  | fbw (σ : FSt) (i : Nat) : σ.fb i ≠ σ.x i → FStep N σ ⟨σ.x, upd σ.fb i (σ.x i)⟩

def Synced (N : Nat) (σ : FSt) : Prop := ∀ i, 1 ≤ i → i ≤ N → σ.fb i = σ.x i

/-- Runs of the feedback-wire model; with `hfb = true` every transition that
moves a network wire happens in a state whose feedback pins are all up to date
(H_FB_FAST). -/
inductive FReach (N : Nat) (hfb : Bool) : FSt → Prop
  | init : FReach N hfb ⟨reset, reset⟩
  | step {σ τ} : FReach N hfb σ → FStep N σ τ → (hfb = true → τ.x ≠ σ.x → Synced N σ) →
      FReach N hfb τ

/-- Reachable states of the atomic model (Section 2). -/
inductive AReach (N : Nat) : St → Prop
  | init : AReach N reset
  | step {x y l} : AReach N x → Step N l x y → AReach N y

theorem fb_refines {N σ} (h : FReach N true σ) : AReach N σ.x := by
  induction h with
  | init => exact AReach.init
  | @step σ τ _ hs hsync ih =>
    cases hs with
    | send h0 => exact AReach.step ih (Step.send _ h0)
    | recv h0 => exact AReach.step ih (Step.recv _ h0)
    | fbw i _ => exact ih
    | gate i h1 h2 h3 =>
      have hne : upd σ.x i (ctlB (σ.x (i-1)) (σ.x (i+1)) (σ.fb i) false) ≠ σ.x := by
        intro he; apply h3
        have := congrFun he i; rw [upd_eq] at this; exact this
      have hs := hsync rfl hne i h1 h2
      simp only at hs ⊢
      rw [hs] at h3 ⊢
      exact AReach.step ih (Step.gate _ i h1 h2 h3)

/-- **Without H_FB_FAST, a one-stage link violates four-phase.** Sender raises
`req_in`, `C_0` rises, the sender sees `ack_in = C_0` high and lowers `req_in`
while `C_0`'s feedback pin still reads `0`; the LUT then computes `0` and
`C_0` falls although the receiver's `ack_out` is still low (and the receiver
was excited to acknowledge): a runt pulse on `req_out`. -/
theorem fb_hazard : ∃ σ τ, FReach 1 false σ ∧ FStep 1 σ τ ∧
    σ.x 1 = true ∧ τ.x 1 = false ∧ σ.x 2 = false := by
  have r3 := FReach.step (FReach.step (FReach.step (N := 1) (hfb := false) FReach.init
    (FStep.send _ (by decide)) (by intro h; cases h))
    (FStep.gate _ 1 (by decide) (by decide) (by decide)) (by intro h; cases h))
    (FStep.send _ (by decide)) (by intro h; cases h)
  exact ⟨_, _, r3, FStep.gate _ 1 (by decide) (by decide) (by decide),
    by decide, by decide, by decide⟩

/-! ## 5. Data path: latch enable = `C_i`, bundling as a derived timing condition

### 5a. The latch LUT -/

/-- `bd_latch`, odd bit: `LUT6 INIT 0xB8B8B8B8B8B8B8B8`,
`I0=d I1=en I2=q (own output, fed back) I3=I4=I5=0`. -/
def INIT_LAT : Nat := 0xB8B8B8B8B8B8B8B8
/-- `bd_latch`, bit pair: `LUT6_2 INIT 0xFF33CC00B8B8B8B8`,
`I0=d[i] I1=en I2=q[i] I3=d[i+1] I4=q[i+1] I5=1`, `O5=q[i]`, `O6=q[i+1]`. -/
def INIT_PAIR : Nat := 0xFF33CC00B8B8B8B8

theorem lat_eq (d en q : Bool) :
    lutB INIT_LAT [d, en, q, false, false, false] = (if en then d else q) := by
  cases d <;> cases en <;> cases q <;> decide

theorem pair_eq (di en qi dj qj : Bool) :
    o5B INIT_PAIR [di, en, qi, dj, qj, true] = (if en then di else qi) ∧
    o6B INIT_PAIR [di, en, qi, dj, qj, true] = (if en then dj else qj) := by
  cases di <;> cases en <;> cases qi <;> cases dj <;> cases qj <;> decide

/-- The latch bit, Kleene (H_KLEENE_LUT of Prelim). -/
def latK (d en q : K3) : K3 := lutK INIT_LAT [d, en, q, .f, .f, .f]

theorem latK_open (d q : K3) : latK d .t q = d := by
  cases d <;> cases q <;> decide
theorem latK_shut (d q : K3) : latK d .f q = q := by
  cases d <;> cases q <;> decide
/-- Closing is glitch-free when `D = Q` at the pins, whatever the enable does
(including an intermediate level while it falls). -/
theorem latK_keep (v : Bool) (e : K3) : latK (K3.ofBool v) e (K3.ofBool v) = K3.ofBool v := by
  cases v <;> cases e <;> decide
/-- Hold violation: if `D` already differs from `Q` while the enable is in
transit, the loop is driven to `X`. -/
theorem latK_race (v : Bool) : latK (K3.ofBool (!v)) .x (K3.ofBool v) = .x := by
  cases v <;> decide

/-- The same three facts for each half of the fractured pair, whatever the
other bit's pins carry (they cannot disturb this bit, even at `X`). -/
theorem pairK_keep (v : Bool) (e d2 q2 : K3) :
    o5K INIT_PAIR [K3.ofBool v, e, K3.ofBool v, d2, q2, .t] = K3.ofBool v ∧
    o6K INIT_PAIR [d2, e, q2, K3.ofBool v, K3.ofBool v, .t] = K3.ofBool v := by
  cases v <;> cases e <;> cases d2 <;> cases q2 <;> decide

/-! ### 5b. One latch bit in time

Time is `Nat` (e.g. ps). Hypothesis **H_LUT_TRANSPORT**: the LUT output at
`t + L` is the Kleene LUT function of its pins at `t`, the feedback pin seeing
the output through a wire of delay `F` (pure transport delays, fixed per arc).
This is the coarsest delay model that still has the loop in it; a range of
delays per event (bounded-delay relation) is the next refinement (Track 3). -/

def LatchRec (L F : Nat) (D en Q : Nat → K3) : Prop :=
  ∀ t, F ≤ t → Q (t + L) = latK (D t) (en t) (Q (t - F))

/-- **Latch capture.** The enable (at this bit's LUT pin) is high on `[a, c)`,
in transit (any value, `X` included) on `[c, c+h)`, low on `[c+h, z)`. If `D`
carries `v` from `a` until the enable has finished falling (`c + h`: HOLD), and
the value has had time to cross the LUT and come round the feedback wire before
the enable starts to fall (`a + L + F ≤ c`: SETUP), then `Q = v` from `a + L`
until `z + L` (the next opening, plus one arc). -/
theorem latch_capture {L F : Nat} {D en Q : Nat → K3} (hrec : LatchRec L F D en Q)
    (hL : 1 ≤ L) {v : Bool} {a c h z : Nat} (hFa : F ≤ a)
    (hopen : ∀ τ, a ≤ τ → τ < c → en τ = .t)
    (hshut : ∀ τ, c + h ≤ τ → τ < z → en τ = .f)
    (hD : ∀ τ, a ≤ τ → τ < c + h → D τ = K3.ofBool v)
    (hsetup : a + L + F ≤ c) :
    ∀ τ, a + L ≤ τ → τ < z + L → Q τ = K3.ofBool v := by
  suffices H : ∀ n τ, τ < n → a + L ≤ τ → τ < z + L → Q τ = K3.ofBool v from
    fun τ h1 h2 => H (τ+1) τ (by omega) h1 h2
  intro n
  induction n with
  | zero => intro τ h; omega
  | succ n ih =>
    intro τ hn h1 h2
    obtain ⟨t, rfl⟩ : ∃ t, τ = t + L := ⟨τ - L, by omega⟩
    rw [hrec t (by omega)]
    by_cases hc : t < c
    · rw [hopen t (by omega) hc, latK_open]; exact hD t (by omega) (by omega)
    · have hq : Q (t - F) = K3.ofBool v := ih (t - F) (by omega) (by omega) (by omega)
      by_cases hh : t < c + h
      · rw [hD t (by omega) hh, hq, latK_keep]
      · rw [hshut t (by omega) (by omega), latK_shut, hq]

/-- **SETUP can be needed** (a concrete counterexample, `L = F = 1`): the enable is
high until `6`, in transit at `6`, low after; `D` changes to `1` at `5`, so
`a + L + F = 7 > 6 = c`. The loop captures an `X` (it then circulates as a
`1, X` pattern in the two-delay loop): the stage hands on garbage. This shows
necessity on this one trace only; SETUP is not necessary in general (the
audit's `setup_not_necessary`, claude/audit `audit/lean/B/W_Data.lean`: SETUP
violated, 7 > 5, capture still correct because the data does not change). -/
def cxD (t : Nat) : K3 := if t < 5 then .f else .t
def cxEn (t : Nat) : K3 := if t < 6 then .t else if t = 6 then .x else .f
def cxQ : Nat → K3
  | 0 => .f
  | 1 => .f
  | t+2 => latK (cxD (t+1)) (cxEn (t+1)) (cxQ t)

theorem setup_needed : LatchRec 1 1 cxD cxEn cxQ ∧
    (∀ τ, 5 ≤ τ → τ < 8 → cxD τ = .t) ∧ cxQ 9 = .x ∧ cxQ 11 = .x := by
  refine ⟨?_, ?_, by decide, by decide⟩
  · intro t ht
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    rfl
  · intro τ h1 _; simp only [cxD]; rw [if_neg (by omega)]

/-! ### 5c. A pipe of latches, one bit, one token

Stage `i`'s latch bit: enable at its LUT pin high on `[o i, c i)`, in transit
on `[c i, c i + h)`, low on `[c i + h, z i)`. In terms of the controller:
`o i = t(C_i rise) + e_i`, `c i = t(C_i fall) + e_i`, `z i = t(next C_i rise) + e_i`,
`e_i` the enable wire delay from node `C_i` to this bit's latch LUT (it differs
per bit: the 150..1125 ps fan-out of the header), `h` the enable's transit time
at the pin. `w (i+1)` is the data wire from `Q_i` to `D_{i+1}` of this bit
(**H_WIRE_TRANSPORT**: a pure delay). The source puts `v` on `D_0` at `a0`.

The data of stage `i` is valid at its output from `arr i + L`, where `arr` is
the data-wave recursion: a latch passes its input one arc after the later of
"input arrived" and "enable opened". -/

def arr (L a0 : Nat) (o w : Nat → Nat) : Nat → Nat
  | 0 => max (o 0) a0
  | i+1 => max (o (i+1)) (arr L a0 o w i + L + w (i+1))

/-- **Pipe data correctness.** With SETUP at every stage
(`arr i + L + F ≤ c i`: the data wave beats the closing of stage `i`) and HOLD at
every internal boundary (`c (i+1) + h ≤ z i + L + w (i+1)`: stage `i+1` has
finished closing before stage `i`'s NEXT value can reach it), every stage
latches `v`, and holds it until its next opening. -/
theorem pipe_data {L F h : Nat} (hL : 1 ≤ L) {D en Q : Nat → Nat → K3}
    {o c z w : Nat → Nat} {a0 : Nat} {v : Bool} (N : Nat)
    (hrec : ∀ i, LatchRec L F (D i) (en i) (Q i))
    (hwire : ∀ i τ, w (i+1) ≤ τ → D (i+1) τ = Q i (τ - w (i+1)))
    (hopen : ∀ i τ, o i ≤ τ → τ < c i → en i τ = .t)
    (hshut : ∀ i τ, c i + h ≤ τ → τ < z i → en i τ = .f)
    (hFo : ∀ i, F ≤ o i)
    (hsrc : ∀ τ, a0 ≤ τ → τ < c 0 + h → D 0 τ = K3.ofBool v)
    (hsetup : ∀ i, i < N → arr L a0 o w i + L + F ≤ c i)
    (hhold : ∀ i, i + 1 < N → c (i+1) + h ≤ z i + L + w (i+1)) :
    ∀ i, i < N → ∀ τ, arr L a0 o w i + L ≤ τ → τ < z i + L → Q i τ = K3.ofBool v := by
  intro i
  induction i with
  | zero =>
    intro hN
    apply latch_capture (hrec 0) hL (c := c 0) (h := h)
    · exact Nat.le_trans (hFo 0) (Nat.le_max_left _ _)
    · intro τ h1 h2; exact hopen 0 τ (Nat.le_trans (Nat.le_max_left _ _) h1) h2
    · exact hshut 0
    · intro τ h1 h2; exact hsrc τ (Nat.le_trans (Nat.le_max_right _ _) h1) h2
    · exact hsetup 0 hN
  | succ i ih =>
    intro hN
    have hq := ih (by omega)
    have hA : arr L a0 o w i + L + w (i+1) ≤ arr L a0 o w (i+1) := Nat.le_max_right _ _
    have hO : o (i+1) ≤ arr L a0 o w (i+1) := Nat.le_max_left _ _
    have hH := hhold i hN
    apply latch_capture (hrec (i+1)) hL (c := c (i+1)) (h := h)
    · exact Nat.le_trans (hFo _) hO
    · intro τ h1 h2; exact hopen _ τ (Nat.le_trans hO h1) h2
    · exact hshut _
    · intro τ h1 h2
      rw [hwire i τ (by omega)]
      exact hq (τ - w (i+1)) (by omega) (by omega)
    · exact hsetup _ hN

/-- Sum of `L + w m` for `m = j+1 .. i` (the data wave's travel time from
stage `j`'s latch to stage `i`'s). -/
def seg (L : Nat) (w : Nat → Nat) (j : Nat) : Nat → Nat
  | 0 => 0
  | i+1 => if j ≤ i then seg L w j i + (L + w (i+1)) else 0

theorem seg_self (L : Nat) (w : Nat → Nat) (i : Nat) : seg L w i i = 0 := by
  cases i with
  | zero => rfl
  | succ i => simp only [seg]; rw [if_neg (by omega)]

theorem arr_le_iff (L a0 : Nat) (o w : Nat → Nat) (i : Nat) : ∀ K T,
    arr L a0 o w i + K ≤ T ↔
      (a0 + seg L w 0 i + K ≤ T ∧ ∀ j, j ≤ i → o j + seg L w j i + K ≤ T) := by
  induction i with
  | zero =>
    intro K T
    simp only [arr, seg]
    constructor
    · intro h; refine ⟨by omega, fun j hj => ?_⟩
      have : j = 0 := by omega
      subst this; omega
    · intro ⟨h1, h2⟩; have := h2 0 (Nat.le_refl _); omega
  | succ i ih =>
    intro K T
    simp only [arr]
    have e0 : seg L w 0 (i+1) = seg L w 0 i + (L + w (i+1)) := by
      simp [seg]
    have ej : ∀ j, j ≤ i → seg L w j (i+1) = seg L w j i + (L + w (i+1)) := by
      intro j hj; simp [seg, hj]
    have ei : seg L w (i+1) (i+1) = 0 := seg_self L w (i+1)
    have key := ih (L + w (i+1) + K) T
    constructor
    · intro h
      have h1 : o (i+1) + K ≤ T := by omega
      have h2 : arr L a0 o w i + (L + w (i+1) + K) ≤ T := by omega
      obtain ⟨k1, k2⟩ := key.1 h2
      refine ⟨by rw [e0]; omega, fun j hj => ?_⟩
      by_cases hji : j ≤ i
      · have := k2 j hji; rw [ej j hji]; omega
      · have : j = i + 1 := by omega
        subst this; rw [ei]; omega
    · intro ⟨h1, h2⟩
      have k : arr L a0 o w i + (L + w (i+1) + K) ≤ T := by
        refine key.2 ⟨by rw [e0] at h1; omega, fun j hj => ?_⟩
        have := h2 j (by omega); rw [ej j hj] at this; omega
      have := h2 (i+1) (Nat.le_refl _); rw [ei] at this
      omega

/-- **The derived (sufficient) bundling condition, unfolded.** SETUP at stage
`i` holds iff, for the source and for every upstream stage `j ≤ i`, the data
launched there reaches and settles in stage `i`'s latch before stage `i`'s
enable starts to fall at this bit. The `iff` is between SETUP and its unfolding
over `arr`'s `max` recursion (arithmetic); SETUP itself is proved sufficient
(`latch_capture`, `pipe_data`), necessary only on one trace (`setup_needed`),
and not necessary in general (audit `setup_not_necessary`, REPORT row 20). It
is exact only as a worst-case-data condition:

* `a0 + Σ_{m=1..i}(L + w m) + L + F ≤ c i` (source data wave),
* `o j + Σ_{m=j+1..i}(L + w m) + L + F ≤ c i` for every `j ≤ i`.

The `j = i` term is the enable pulse width (`C_i` high at the pin for at least
one latch arc plus one feedback wire). The `j < i` terms are the fill race of
the header ("the closing wave gains on the data wave"): `C_i` may fall as soon
as `C_{i-1}` fell and `C_{i+1}` rose, i.e. a few controller arcs after `C_j`
rose, while the data opened by `C_j` needs `i - j` latch arcs and data wires
to get here. -/
theorem setup_iff (L F a0 : Nat) (o w c : Nat → Nat) (i : Nat) :
    arr L a0 o w i + L + F ≤ c i ↔
      (a0 + seg L w 0 i + (L + F) ≤ c i ∧ ∀ j, j ≤ i → o j + seg L w j i + (L + F) ≤ c i) := by
  rw [← arr_le_iff]; omega

/-- **Classical "request after data" is sufficient, not necessary.** If the
data reaches every latch input before that latch opens (`a0 ≤ o 0`, and
`o i + L + w (i+1) ≤ o (i+1)`: stage `i+1`'s enable rises at this bit no earlier
than stage `i`'s output plus the data wire), the data wave is the enable wave
(`arr i = o i`), and SETUP reduces to the pulse-width term alone. The Muller
pipe does not provide this ordering by itself: `C_{i+1}` rises one controller
arc after `C_i`, while the data needs a latch arc plus a data wire. (The
header of `bd_link.v` quotes ~56 ps vs ~152 ps; those are FAST_MAX of O6 and
SLOW_MAX of O5, two different prjxray corners, makesdf.py:63. At one corner the
arcs are comparable, e.g. 124 vs 152 ps at SLOW_MAX, and the data wire still
breaks the ordering.) That is why the sufficient condition SETUP, unfolded in
`setup_iff` (rule I), is what the router must meet, with `SDELAY` as the
knob. -/
theorem arr_classical (L a0 : Nat) (o w : Nat → Nat) (h0 : a0 ≤ o 0)
    (hb : ∀ i, o i + L + w (i+1) ≤ o (i+1)) : ∀ i, arr L a0 o w i = o i := by
  intro i
  induction i with
  | zero => simp [arr]; omega
  | succ i ih => simp only [arr, ih]; have := hb i; omega


/-! ## 6. `bd_link_dctl` (the decoupled controller), one stage, finite check

Four LUT6, INITs and pins verbatim from `cells/rtl/bd_link.v` (`LDN = 0`, so
`s = 1`; `BROAD` selects `gate = ack_out` or `0`). Variables: `0 req_in`
(sender), `1 b` (= `req_out`, `DELAY = 0`), `2 a` (= `ack_in`, `DACK = 0`),
`3 ld`, `4 lt`, `5 ack_out` (receiver). Reset holds `b = a = ld = 0`; `lt` is
combinational and starts at its value `1` (state `16`). -/

def INIT_DB  : Nat := 0x0000F3200000F320
def INIT_DA  : Nat := 0x0000FA800000FA80
def INIT_DLD : Nat := 0x00000F0800000F08
def INIT_DLT : Nat := 0x0101010101010101

def dNext (broad : Bool) (s v : Nat) : Bool :=
  let req := s.testBit 0; let b := s.testBit 1; let a := s.testBit 2
  let ld := s.testBit 3; let lt := s.testBit 4; let ack := s.testBit 5
  if v = 0 then (if req = a then !req else req)          -- four-phase sender
  else if v = 1 then lutB INIT_DB [req, ack, ld, b, false, false]
  else if v = 2 then lutB INIT_DA [req, b, ld, a, false, false]
  else if v = 3 then lutB INIT_DLD [lt, true, a, ld, false, false]
  else if v = 4 then lutB INIT_DLT [b, a, (if broad then ack else false), false, false, false]
  else b                                                -- four-phase receiver

/-- The INITs are the header's set/reset equations. -/
theorem dctl_eqs (req ack ld b a lt : Bool) :
    lutB INIT_DB [req, ack, ld, b, false, false] = (req && ld && !ack || b && !(ack && !ld)) ∧
    lutB INIT_DA [req, b, ld, a, false, false] = (req && b && ld || a && !(!req && !ld)) ∧
    lutB INIT_DLD [lt, true, a, ld, false, false] = (lt && !a || ld && !a) ∧
    lutB INIT_DLT [b, a, ack, false, false, false] = (!b && !a && !ack) := by
  cases req <;> cases ack <;> cases ld <;> cases b <;> cases a <;> cases lt <;> decide

/-- **H_LT_FIRST** as a schedule: while `lt` is excited, neither neighbour
(sender, receiver) fires. Physically: `lt` settles (one LUT arc from `b` or
`a`) before a neighbouring controller can respond to `b` or `a` (a wire, its
LUTs, and a wire back). The header's one assumption. Test: GLS/board, measure
`b`/`a` -> `lt` at the LUT against the round trip `b` -> `ack_out` and
`a` -> `req_in`. -/
def ltFirst (s v : Nat) : Bool := !(gEx (dNext true) s 4) || (v != 0 && v != 5)
def ltFirst0 (s v : Nat) : Bool := !(gEx (dNext false) s 4) || (v != 0 && v != 5)

def dmask1 : Nat := 0xc8ff8b83c8ff
def dmask0 : Nat := 0x303c8ff8b83c8fd

theorem dctlCheck1 : gCheck 6 (dNext true) ltFirst 16 dmask1 = true := by decide +kernel
theorem dctlCheck0 : gCheck 6 (dNext false) ltFirst0 16 dmask0 = true := by decide +kernel

/-- **bd_link_dctl, BROAD = 1, under H_LT_FIRST:** hazard-free (every excited
variable stays excited through every other allowed firing) and deadlock-free,
against a four-phase sender and receiver. -/
theorem dctl_ok1 {s} (h : GReach 6 (dNext true) ltFirst 16 s) :
    (∀ u v, u < 6 → v < 6 → u ≠ v → gEx (dNext true) s u = true → ltFirst s u = true →
       gEx (dNext true) s v = true → gEx (dNext true) (gFire s u) v = true) ∧
    (∃ v, v < 6 ∧ gEx (dNext true) s v = true ∧ ltFirst s v = true) := g_props dctlCheck1 h

/-- Same for BROAD = 0. -/
theorem dctl_ok0 {s} (h : GReach 6 (dNext false) ltFirst0 16 s) :
    (∀ u v, u < 6 → v < 6 → u ≠ v → gEx (dNext false) s u = true → ltFirst0 s u = true →
       gEx (dNext false) s v = true → gEx (dNext false) (gFire s u) v = true) ∧
    (∃ v, v < 6 ∧ gEx (dNext false) s v = true ∧ ltFirst0 s v = true) := g_props dctlCheck0 h

/-- **Without H_LT_FIRST the decoupled controller is not speed independent.**
A reachable state (pure interleaving, any delays) in which `lt` is still the
stale `1` after a whole handshake and is excited to fall, and the firing of
`a` withdraws that excitation: a hazard on the latch enable. This is the
header's "every hazard it reports is lt still stale after a whole handshake". -/
theorem dctl_si_hazard : ∃ s, GReach 6 (dNext true) anyOrder 16 s ∧
    gEx (dNext true) s 4 = true ∧ gEx (dNext true) s 2 = true ∧
    gEx (dNext true) (gFire s 2) 4 = false :=
  ⟨_, (GReach.step (v := 0) (GReach.step (v := 5) (GReach.step (v := 1) (GReach.step (v := 3) (GReach.step (v := 2) (GReach.step (v := 5) (GReach.step (v := 1) (GReach.step (v := 0) (GReach.step (v := 3) GReach.init (by decide) (by decide +kernel) rfl) (by decide) (by decide +kernel) rfl) (by decide) (by decide +kernel) rfl) (by decide) (by decide +kernel) rfl) (by decide) (by decide +kernel) rfl) (by decide) (by decide +kernel) rfl) (by decide) (by decide +kernel) rfl) (by decide) (by decide +kernel) rfl) (by decide) (by decide +kernel) rfl), by decide +kernel, by decide +kernel, by decide +kernel⟩

end Formal.Cells.LinkHandshake
