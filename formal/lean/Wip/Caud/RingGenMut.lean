-- Wip/Caud: MUTANT: INIT bit 0 of the generated bd_c2n flipped (0x..B2 -> 0x..B3; address a=b=q=rst=0). Expected: does NOT compile (gen_c2n_run is false, so ring_three_gen/k_tokens_gen lose their proof).
import Formal.Net.Ring
import Formal.Gen.Cells

/-!
# `ring_three` / `k_tokens` over the GENERATED `bd_c2n` netlist (audit answer, probe C-aud)

Audit C.md row 9 / REPORT "with real bd_c2n INITs" (OVERSTATED, mild): Ring.lean's
`ring_three` and `k_tokens` are stated over the hand-written `ctl`; the real LUT enters
only through the bridge `excited_gate`, so a flipped INIT bit breaks the bridge but not
the headline theorems.

Here the transition system itself is built from the yosys-generated netlists
`Formal.Gen.Cells.bd_c2n` (here: the local copy `bd_c2n_m`) / `bd_c2n_set` (`formal/tools/gen/gen.sh`, from
`cells/rtl/bd_ce.v`, INIT and pin -> net map as synthesized), read by the generic
netlist interpreter `Netlist.next boolSem` (feedback net `q` as state, inputs in port
order `a, b, rst`). Each stage `i` is the generated cell with `a = c[i-1]`,
`b = c[i+1]` (tb_ring.v's wiring), the first `K` stages being `bd_c2n_set`.
The reset state is DEFINED as what the generated cells drive while `rst = 1`.

`ring_three_gen` and `k_tokens_gen` are stated only in terms of `excitedG` / `ReachG` /
`resetG`, all of which unfold to the generated `Netlist` literals. Their proofs go
through four `decide +kernel` facts on those literals (`gen_c2n_run`, ...); with one
INIT bit flipped in the generated netlist that fact is false and these theorems no
longer compile (demonstrated by `Wip/Caud/RingGenMut.lean`).

Hypotheses, as in Ring.lean: H_SI (one excited gate fires at a time), H_RESET_CLEAN.
Not covered: timing, the routed ring (the generated netlist is the synthesized cell,
not a placed one), whether `gen.sh --check` is run (drift between `cells/rtl` and the
generated file is caught by that script, not by Lean).
-/

namespace Wip.Caud.RingGenMut
open Formal.Gen Formal.Net.Ring

/-- MUTANT: INIT bit 0 of the generated bd_c2n flipped (0x..B2 -> 0x..B3; address a=b=q=rst=0). Expected: does NOT compile (gen_c2n_run is false, so ring_three_gen/k_tokens_gen lose their proof). -/
def bd_c2n_m : Netlist :=
  { Cells.bd_c2n with cells := Cells.bd_c2n.cells.map (fun c => { c with init := c.init ^^^ 1 }) }

/-- One step of a generated one-LUT cell with ports `[a, b, rst]` and state `[q]`. -/
def stepOf (nl : Netlist) (a b q rst : Bool) : Bool :=
  match nl.next boolSem [a, b, rst] [q] with
  | some [q'] => q'
  | _ => q

/-- Stage `i` of `ring #(N, K)` as the GENERATED cell. -/
def gateG (n K : Nat) (rst : Bool) (s : State) (i : Nat) : Bool :=
  if i < K then stepOf Cells.bd_c2n_set (s (prv n i)) (s (nxt n i)) (s i) rst
  else stepOf bd_c2n_m (s (prv n i)) (s (nxt n i)) (s i) rst

/-- Excitation read from the generated cells (run mode, `rst = 0`). -/
def excitedG (n K : Nat) (s : State) (i : Nat) : Prop :=
  i < n ∧ gateG n K false s i ≠ s i

/-- H_SI reachability with the generated cells' excitation. -/
inductive ReachG (n K : Nat) (s0 : State) : State → Prop
  | refl : ReachG n K s0 s0
  | step {s : State} (i : Nat) : ReachG n K s0 s → excitedG n K s i → ReachG n K s0 (fire s i)

/-- H_RESET_CLEAN: the state at release is what every generated cell drives while
`rst = 1` (from an arbitrary state; `gen_rst_indep` shows it does not matter). -/
def resetG (n K : Nat) : State := fun i => gateG n K true (fun _ => false) i

/-! ## The only facts about the generated literals (kernel-evaluated) -/

theorem gen_c2n_run : ∀ a b q : Bool, stepOf bd_c2n_m a b q false = ctl a b q := by
  decide +kernel
theorem gen_c2nset_run : ∀ a b q : Bool, stepOf Cells.bd_c2n_set a b q false = ctl a b q := by
  decide +kernel
theorem gen_c2n_rst : ∀ a b q : Bool, stepOf bd_c2n_m a b q true = false := by
  decide +kernel
theorem gen_c2nset_rst : ∀ a b q : Bool, stepOf Cells.bd_c2n_set a b q true = true := by
  decide +kernel

/-! ## Bridge to Ring.lean's system -/

theorem gateG_run (n K : Nat) (s : State) (i : Nat) :
    gateG n K false s i = ctl (s (prv n i)) (s (nxt n i)) (s i) := by
  unfold gateG; split <;> simp [gen_c2n_run, gen_c2nset_run]

theorem gateG_rst (n K : Nat) (s : State) (i : Nat) :
    gateG n K true s i = resetState K i := by
  unfold gateG resetState; split <;> simp_all [gen_c2n_rst, gen_c2nset_rst]

theorem gen_rst_indep (n K : Nat) (s : State) : (fun i => gateG n K true s i) = resetG n K := by
  funext i; unfold resetG; rw [gateG_rst, gateG_rst]

theorem resetG_eq (n K : Nat) : resetG n K = resetState K := by
  funext i; unfold resetG; rw [gateG_rst]

theorem excitedG_iff (n K : Nat) (s : State) (i : Nat) : excitedG n K s i ↔ excited n s i := by
  unfold excitedG excited; rw [gateG_run]

theorem reachG_iff (n K : Nat) (s0 s : State) : ReachG n K s0 s ↔ Reach n s0 s := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | step i _ he ih => exact .step i ih ((excitedG_iff n K _ i).1 he)
  · intro h
    induction h with
    | refl => exact .refl
    | step i _ he ih => exact .step i ih ((excitedG_iff n K _ i).2 he)

/-! ## The headline theorems, over the generated cells -/

/-- **`ring_three` over the generated `bd_c2n`/`bd_c2n_set` netlists.** A ring of `N`
generated `bd_link_ctl` cells released from (generated) reset with `0 < K < N` stages
holding is live in every H_SI-reachable state iff `N ≥ 3`. -/
theorem ring_three_gen (n K : Nat) (hK0 : 0 < K) (hKn : K < n) :
    (∀ s, ReachG n K (resetG n K) s → ∃ i, excitedG n K s i) ↔ 3 ≤ n := by
  rw [← ring_three n K hK0 hKn, resetG_eq]
  constructor
  · intro h s hs
    obtain ⟨i, hi⟩ := h s ((reachG_iff n K _ _).2 hs)
    exact ⟨i, (excitedG_iff n K s i).1 hi⟩
  · intro h s hs
    obtain ⟨i, hi⟩ := h s ((reachG_iff n K _ _).1 hs)
    exact ⟨i, (excitedG_iff n K s i).2 hi⟩

/-- **`k_tokens` over the generated cells.** From any state carrying `2k` wavefronts
(`k ≥ 1` four-phase tokens), every state reachable under the generated cells'
excitation is live iff `N ≥ 2k+1`. (`K` only selects which stages are `_set` cells;
in run mode both cells compute the same function.) -/
theorem k_tokens_gen (n K k : Nat) (hk : 1 ≤ k) (s0 : State) (h0 : D n s0 = 2 * k) :
    (∀ s, ReachG n K s0 s → ∃ i, excitedG n K s i) ↔ 2 * k + 1 ≤ n := by
  rw [← k_tokens n k hk s0 h0]
  constructor
  · intro h s hs
    obtain ⟨i, hi⟩ := h s ((reachG_iff n K _ _).2 hs)
    exact ⟨i, (excitedG_iff n K s i).1 hi⟩
  · intro h s hs
    obtain ⟨i, hi⟩ := h s ((reachG_iff n K _ _).1 hs)
    exact ⟨i, (excitedG_iff n K s i).2 hi⟩

/-- Safety from generated reset: one loop token (two wavefronts) forever. -/
theorem ring_safe_gen {n K : Nat} (hn : 3 ≤ n) (hK0 : 0 < K) (hKn : K < n) {s : State}
    (hs : ReachG n K (resetG n K) s) : D n s = 2 := by
  rw [resetG_eq] at hs
  exact ring_safe hn hK0 hKn ((reachG_iff n K _ _).1 hs)

/-- Non-vacuity: the 3-ring from generated reset with `K = 1` has an excited stage. -/
example : ∃ i, excitedG 3 1 (resetG 3 1) i :=
  (ring_three_gen 3 1 (by decide) (by decide)).2 (by decide) _ .refl

end Wip.Caud.RingGenMut

#print axioms Wip.Caud.RingGenMut.ring_three_gen
#print axioms Wip.Caud.RingGenMut.k_tokens_gen
