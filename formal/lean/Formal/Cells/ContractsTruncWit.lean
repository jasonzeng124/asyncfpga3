import Formal.Cells.ContractsTruncSteer

/-!
# Probe G1, part 3: non-vacuity of the steer's causal step

A unit-delay run (every LUT and wire `Ret.shift 1`, as `OpsTimed.SteerWit`)
whose sender keeps the select at its driver for the whole port window
`[ρ (2k), K (2k+1))` (the zero-lead H_BUNDLE convention of `Port`;
`OpsTimed.SteerWit`'s select changes before ack-fall, so it is not reused).
First request at 9, receivers answer one wire later.

`step_witness`: every hypothesis of `steer_step_ports` holds, at every `N`, so
its conclusion holds at every `N`; `witness_routes`: the run is not degenerate
(token 0 goes to branch 0 only, token 1 to branch 1 only, both acknowledged).
-/

namespace Formal.Cells.Contracts.TruncWit
open Formal.Net Formal.Net.Handshake
open Formal.Cells.Contracts
open Formal.Cells.OpsTimed (Tok Enum rx rx_e rx_o rx_0 orEdges SteerRun SteerGates steer_fwd)
open Formal.Cells.OpsTimed.SteerWit (u fu sv)
open Formal.Cells.LibCtlMergeMux (req0B req1B or2B)

def run : SteerRun where
  Wq := u
  L5 := u
  L6 := u
  W0 := u
  W1 := u
  Wa0 := u
  Wa1 := u
  La := u
  Wk := u
  ρ j := 8 * j + 9
  A j := 8 * j + 13
  sv := sv

/-- The bus: token `k` (value `k`) from its request rise `16k + 9` to its
acknowledge fall `16k + 24`. -/
def dat (t : Nat) : Nat := (t - 9) / 16
/-- The select at the sender's driver: `sel` of the bus. -/
def s (t : Nat) : Bool := sv (dat t)
def req (t : Nat) : Bool := decide (9 ≤ t ∧ (t - 9) % 16 < 8)
def su (t : Nat) : Bool := s (t - 1)
def rqu (t : Nat) : Bool := req (t - 1)
def o5 (t : Nat) : Bool := req0B (rqu (t - 1)) (su (t - 1))
def o6 (t : Nat) : Bool := req1B (rqu (t - 1)) (su (t - 1))
def r0 (t : Nat) : Bool := o5 (t - 1)
def r1 (t : Nat) : Bool := o6 (t - 1)
def a0 (t : Nat) : Bool := r0 (t - 1)
def a1 (t : Nat) : Bool := r1 (t - 1)
def a0u (t : Nat) : Bool := a0 (t - 1)
def a1u (t : Nat) : Bool := a1 (t - 1)
def ao (t : Nat) : Bool := or2B (a0u (t - 1)) (a1u (t - 1))
def ack (t : Nat) : Bool := ao (t - 1)

def cin : Chan := ⟨req, ack, dat⟩
def cout (b : Bool) : Chan := ⟨if b then r1 else r0, if b then a1 else a0, fun _ => 0⟩
def κ (b : Bool) (m : Nat) : Nat := if b then 2 * m + 1 else 2 * m

theorem gates : SteerGates run req rqu su o5 o6 r0 r1 a0 a1 a0u a1u ao ack where
  H_WQ _ _ := rfl
  H_U5 _ _ := rfl
  H_U6 _ _ := rfl
  H_W0 _ _ := rfl
  H_W1 _ _ := rfl
  H_WA0 _ _ := rfl
  H_WA1 _ _ := rfl
  H_UA _ _ := rfl
  H_WK _ _ := rfl

theorem qr_eq (j : Nat) : run.qr j = 8 * j + 10 := by
  unfold SteerRun.qr; rw [show run.Wq = u from rfl, fu _ (by show 1 ≤ 8 * j + 9; omega)]; rfl
theorem R0_eq (j : Nat) : run.R0 j = 8 * j + 12 := by
  unfold SteerRun.R0; rw [qr_eq, show run.L5 = u from rfl, show run.W0 = u from rfl,
    fu (8 * j + 10) (by omega), fu (8 * j + 10 + 1) (by omega)]
theorem R1_eq (j : Nat) : run.R1 j = 8 * j + 12 := by
  unfold SteerRun.R1; rw [qr_eq, show run.L6 = u from rfl, show run.W1 = u from rfl,
    fu (8 * j + 10) (by omega), fu (8 * j + 10 + 1) (by omega)]
theorem Rb_eq (b : Bool) (j : Nat) : Rb run b j = 8 * j + 12 := by
  cases b <;> simp [Rb, R0_eq, R1_eq]
theorem K_eq (j : Nat) : run.K j = 8 * j + 16 := by
  unfold SteerRun.K SteerRun.au orEdges
  rw [show run.Wa0 = u from rfl, show run.Wa1 = u from rfl, show run.La = u from rfl,
    show run.Wk = u from rfl]
  dsimp only
  have hA : run.A j = 8 * j + 13 := rfl
  split <;> rw [hA, fu (8 * j + 13) (by omega), fu (8 * j + 13 + 1) (by omega),
    fu (8 * j + 13 + 1 + 1) (by omega)]

theorem req_tok : Tok 0 req run.ρ (fun _ => true) := by
  refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
  · have h2 : t < 8 * 0 + 9 := h2
    simp only [req, decide_eq_false_iff_not]; omega
  · have h1 : 8 * (2 * k) + 9 ≤ t := h1; have h2 : t < 8 * (2 * k + 1) + 9 := h2
    simp only [req, decide_eq_true_eq]; omega
  · have h1 : 8 * (2 * k + 1) + 9 ≤ t := h1; have h2 : t < 8 * (2 * k + 2) + 9 := h2
    simp only [req, decide_eq_false_iff_not]; omega

theorem s_pin : ∀ k t, run.qr (2 * k) ≤ t → t < run.qr (2 * k + 1) → su t = run.sv k := by
  intro k t h1 h2
  rw [qr_eq] at h1 h2
  show sv ((t - 1 - 9) / 16) = sv k
  rw [show (t - 1 - 9) / 16 = k by omega]

theorem fwd : Tok (run.T1 0) r0 run.R0 (fun k => !run.sv k) ∧ Tok (run.T1 0) r1 run.R1 run.sv :=
  steer_fwd gates req_tok s_pin

theorem a0_tok : Tok 6 a0 run.A (fun k => !run.sv k) :=
  ((fwd.1.fifo u (y := a0) (fun _ _ => rfl)).mono (T' := 6) (by decide)).congr
    (fun j => by show u.fst (run.R0 j) = 8 * j + 13; rw [R0_eq, fu (8 * j + 12) (by omega)])

theorem a1_tok : Tok 6 a1 run.A run.sv :=
  ((fwd.2.fifo u (y := a1) (fun _ _ => rfl)).mono (T' := 6) (by decide)).congr
    (fun j => by show u.fst (run.R1 j) = 8 * j + 13; rw [R1_eq, fu (8 * j + 12) (by omega)])

theorem enum0 : Enum (fun k => !run.sv k) (κ false) where
  mono m := by show 2 * m < 2 * (m + 1); omega
  hit m := by show (!decide ((2 * m) % 2 = 1)) = true; simp
  all k hk := ⟨k / 2, by
    have : (!decide (k % 2 = 1)) = true := hk
    simp at this; show 2 * (k / 2) = k; omega⟩

theorem enum1 : Enum run.sv (κ true) where
  mono m := by show 2 * m + 1 < 2 * (m + 1) + 1; omega
  hit m := by show decide ((2 * m + 1) % 2 = 1) = true; simp
  all k hk := ⟨k / 2, by
    have : decide (k % 2 = 1) = true := hk
    simp at this; show 2 * (k / 2) + 1 = k; omega⟩

theorem rxA (b : Bool) (j : Nat) : rx run.A (κ b) j = 8 * (2 * κ b (j / 2) + j % 2) + 13 := rfl

theorem quiet_a : ∀ t, t < 6 → a0 t = false ∧ a1 t = false := by decide

theorem branch_ack (b : Bool) : Tok 0 (if b then a1 else a0) (rx run.A (κ b)) (fun _ => true) := by
  have hm : ∀ j, rx run.A (κ b) 0 ≤ rx run.A (κ b) j := fun j => by
    rw [rxA, rxA]; cases b <;> simp [κ] <;> omega
  cases b
  · exact tok_from0 (a0_tok.reindex enum0) (fun t ht => (quiet_a t ht).1)
      (by rw [rxA]; simp [κ]) hm
  · exact tok_from0 (a1_tok.reindex enum1) (fun t ht => (quiet_a t ht).2)
      (by rw [rxA]; simp [κ]) hm

theorem branch_ackUpTo (b : Bool) (N : Nat) :
    AckUpTo (cout b) (rx (Rb run b) (κ b)) (rx run.A (κ b)) N where
  ack := by
    have := TokN.of_tok (branch_ack b) N
    cases b <;> exact this
  ra j _ := by
    rw [rxA]; unfold rx; rw [Rb_eq]; omega

theorem req_upTo (N : Nat) : ReqUpTo cin run.ρ run.K N where
  req := TokN.of_tok req_tok N
  start := by show 0 < 8 * 0 + 9; omega
  ar j _ := by rw [K_eq]; show _ < 8 * (j + 1) + 9; omega

theorem dat_upTo (N : Nat) : DatUpTo cin run.ρ run.K (fun k => k) N := by
  intro k t _ h1 h2
  rw [K_eq] at h2
  have h1 : 8 * (2 * k) + 9 ≤ t := h1
  show (t - 9) / 16 = k
  omega

theorem quiet_fwd : ∀ t, t < run.T1 0 → r0 t = false ∧ r1 t = false := by
  show ∀ t, t < 5 → r0 t = false ∧ r1 t = false
  decide

theorem quiet_ack : ∀ t, t < run.T2 0 → ack t = false := by
  show ∀ t, t < 4 → ack t = false
  decide

/-- **Non-vacuity of `steer_step_ports`**: at every `N`, all its hypotheses
hold on this run (so its conclusion does). -/
theorem step_witness (N : Nat) :
    AckUpTo cin run.ρ run.K (N + 1 + u.lo + u.lo) ∧
    ∀ b, ReqUpTo (cout b) (rx (Rb run b) (κ b)) (rx run.A (κ b)) (N + 1 + 2) :=
  steer_step_ports (dq := 1) (Lm := 2) (Wm := 1) (s := s) (sel := sv) u gates
    (fun _ _ => rfl) (cin := cin) rfl rfl (req_upTo N) (dat_upTo N) (fun _ => rfl) (fun _ => rfl)
    κ enum0 enum1 (cout := cout) (fun _ => rfl) (fun _ => rfl) (fun b => branch_ackUpTo b N)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    quiet_fwd quiet_ack (by decide) (by decide)

/-- The run is not degenerate: token 0 (`s = 0`) reaches only branch 0, token
1 (`s = 1`) only branch 1, and the sender sees an acknowledge for each. -/
theorem witness_routes :
    r0 12 = true ∧ r1 12 = false ∧ r0 28 = false ∧ r1 28 = true ∧ ack 16 = true ∧ ack 32 = true := by
  decide

end Formal.Cells.Contracts.TruncWit
