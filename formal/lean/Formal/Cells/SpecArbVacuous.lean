import Formal.Target.Spec
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Shard B check of the FROZEN Spec's H_ARB(T) (`ArbOK`): it excludes the held arbiter's handover

Against `Formal.Target.Spec` as frozen (shard A, 2026-11-01 07:55 UTC; `ArbOK` unchanged
from the v1 draft that `Wip/Bspec/ArbOKVacuous.lean` checked). Built by lake.

## Problem, plainly
Spec v1 states H_ARB(T) as: whenever an arbiter's two request nodes are constant on
`[t1, t2]`, its state node `q` is constant on `[t1 + T, t2]`. But the held `bd_arbiter`'s
state LUT (`ustate`, `cells/rtl/bd_arb.v`, INIT `64'hFFF0_FFB2_ACAC_ACAC`, O6 = q with
I5 tied high) also reads `A0` (and `rst`): q is frozen while A0 is high, and flips at
A0's fall. In a normal handover (client 1 released, client 2 waiting) both requests are
constant across A0's fall, and q MUST flip then. So `ArbOK` together with the gate
relation is contradictory for every behaviour where the server holds A0 for `T` or more
after the requests last moved, and `NetCorrect` holds vacuously for all of them. The
server's A0 depends on the downstream and, through `out0`, on the environment, which
H_ENV does not bound: for every `T`, such behaviours exist.

## Lean
* `arbOK_excludes_handover`: for ANY delay parameters, corner and arcs: the q gate holding
  (`GateOK`), requests r1 = 0, r2 = 1 and rst = 0 throughout, A0 high until `ta` and low
  after, q high at time `T`, and `ArbOK T` for this arbiter: `False`.
* `handover_gate_ok`: the same scenario has a behaviour of the q gate (exact delay 10 ps on
  every arc, g = 1, κ = 0, corner 0): q high until `ta + 10`, low after. With `T < ta + 10`
  it meets the scenario's premises, so the contradiction comes from `ArbOK`, not from an
  empty scenario.
* `arbOK_vacuous_for_every_T`: for every `T` there is a behaviour of the q gate (a handover
  whose server wait is longer than `T`) that `GateOK` admits and `ArbOK T` forbids.

## Suggested repair (for shard A; not checked against a proof)
State H_ARB(T) over ALL non-feedback inputs of the state LUT, as its pins read them:
"whenever r1, r2, A0 and rst are constant on `[t1, t2]`, q is constant on `[t1 + T, t2]`"
(and T must be at least the state gate's slowest arc, else `ArbOK` contradicts an ordinary
set/reset transition in the same way).
-/

open Formal.Target

namespace Formal.Cells.SpecArbVacuous

/-- ustate's O6 table with I5 tied high: `INIT[63:32]` of `64'hFFF0_FFB2_ACAC_ACAC`,
pins I0..I4 = r1, r2, q, rst, A0. -/
def qInit : Nat := 0xFFF0FFB2

/-- Reset address (r1 = 0, r2 = 1, rst = 0, A0 = 0), either q: output 0. -/
theorem qInit_reset (b : Bool) : qInit.testBit (2 + (if b then 4 else 0)) = false := by
  cases b <;> decide

/-- Hold address with A0 = 1 (r1 = 0, r2 = 1, rst = 0): output = q. -/
theorem qInit_hold (b : Bool) : qInit.testBit (2 + (if b then 4 else 0) + 16) = b := by
  cases b <;> decide

/-- A read delay admissible for an arc is at most some `M` fixed by the arc and `g`. -/
theorem delay_bound (p : DelayPar) (e : Arc) : ∃ M : Nat, ∀ c d, Adm p c e d → d ≤ M := by
  obtain ⟨M, hM⟩ := exists_nat_ge ((e.smax : ℚ) * p.g)
  refine ⟨M, fun c d h => ?_⟩
  have h1 : (d : ℚ) ≤ e.smax * p.g := h.2.1
  exact_mod_cast le_trans h1 hM

theorem arbOK_excludes_handover (p : DelayPar) (c : ℚ) (g : Gate) (x : Beh)
    (r1 r2 q rst a0 : Nat) (T ta : Nat)
    (hk : g.k = 5) (hins : g.ins = [r1, r2, q, rst, a0]) (hinit : g.init = qInit)
    (hout : g.out = q) (hg : GateOK p c g x)
    (h1 : ∀ t, x r1 t = false) (h2 : ∀ t, x r2 t = true) (hr : ∀ t, x rst t = false)
    (ha : ∀ t, x a0 t = decide (t < ta)) (hq : x q T = true)
    (harb : ArbOK T [⟨r1, r2, q⟩] x) : False := by
  obtain ⟨f, _, hrel⟩ := hg
  obtain ⟨M, hM⟩ := delay_bound p (g.arcs.getD 4 default)
  set t := max (g.start p) (ta + T + M)
  have ht : g.start p ≤ t := le_max_left _ _
  obtain ⟨hreads, hval⟩ := hrel t ht
  have h4 := hreads 4 (by omega)
  have hd : t - f 4 t ≤ M := hM c _ h4.2
  have htM : ta + T + M ≤ t := le_max_right _ _
  have hfa : ¬ (f 4 t < ta) := by omega
  -- q at t is the reset value
  have hqt : x q t = false := by
    rw [← hout, hval, hk, hinit, hins]
    have e : (addr 5 fun i => x ([r1, r2, q, rst, a0].getD i 0) (f i t)) =
        2 + (if x q (f 2 t) then 4 else 0) := by
      simp [addr, h1, h2, hr, ha, hfa]
    rw [e, qInit_reset]
  -- ArbOK: requests constant everywhere, so q is constant on [T, t]
  have hc := harb ⟨r1, r2, q⟩ (List.mem_singleton_self _) 0 t
    (fun s _ _ => by simp [h1]) (fun s _ _ => by simp [h2])
  have := hc t (by omega) le_rfl
  simp only [Nat.zero_add] at this
  rw [hqt, hq] at this
  exact Bool.false_ne_true this

/-! ## The scenario is a behaviour of the gate (so `ArbOK` is what excludes it) -/

/-- One arc with every number 10 ps. -/
def arc10 : Arc := ⟨10, 10, 10, 10⟩

/-- The q gate with exact 10 ps arcs, pins at nodes 0..4 (r1, r2, q, rst, A0), output node 2. -/
def gq : Gate := ⟨"ustate.O6", 5, qInit, [0, 1, 2, 3, 4], [arc10, arc10, arc10, arc10, arc10], 2⟩

def p1 : DelayPar := ⟨1, 0⟩

/-- The handover behaviour: r1 = 0, r2 = 1, rst = 0, A0 high until `ta`, q high until
`ta + 10` and low after. -/
def hb (ta : Nat) : Beh := fun n t =>
  if n = 0 then false else if n = 1 then true else if n = 2 then decide (t < ta + 10)
  else if n = 3 then false else decide (t < ta)

theorem gq_start : gq.start p1 = 10 := by
  simp [Gate.start, gq, p1, arc10]
  rfl

theorem handover_gate_ok (ta : Nat) : GateOK p1 0 gq (hb ta) := by
  refine ⟨fun _ t => t - 10, fun _ _ _ _ hab => Nat.sub_le_sub_right hab 10, ?_⟩
  intro t ht
  rw [gq_start] at ht
  refine ⟨fun i hi => ⟨Nat.sub_le t 10, ?_⟩, ?_⟩
  · have hi' : gq.arcs.getD i default = arc10 := by
      simp only [gq] at hi ⊢
      rcases i with _ | _ | _ | _ | _ | i <;> first | rfl | (exfalso; omega)
    rw [hi']
    have e : t - (t - 10) = 10 := by omega
    rw [e]
    simp [Adm, arc10, p1, lerp]
  · show decide (t < ta + 10) = qInit.testBit (addr 5 fun i => hb ta ([0, 1, 2, 3, 4].getD i 0) (t - 10))
    by_cases hlt : t - 10 < ta
    · have e : (addr 5 fun i => hb ta ([0, 1, 2, 3, 4].getD i 0) (t - 10)) =
          2 + (if true then 4 else 0) + 16 := by
        have hq' : t - 10 < ta + 10 := by omega
        simp [addr, hb, hlt, hq']
      rw [e, qInit_hold]
      simp; omega
    · have e : (addr 5 fun i => hb ta ([0, 1, 2, 3, 4].getD i 0) (t - 10)) =
          2 + (if decide (t - 10 < ta + 10) then 4 else 0) := by
        simp [addr, hb, hlt]
      rw [e, qInit_reset]
      simp; omega

/-- **For every `T`**: a handover whose server holds A0 past `T` is a behaviour of the q
gate (`GateOK`) that `ArbOK T` forbids. -/
theorem arbOK_vacuous_for_every_T (T : Nat) :
    ∃ ta, GateOK p1 0 gq (hb ta) ∧ ¬ ArbOK T [⟨0, 1, 2⟩] (hb ta) := by
  refine ⟨T, handover_gate_ok T, fun harb => ?_⟩
  exact arbOK_excludes_handover p1 0 gq (hb T) 0 1 2 3 4 T T rfl rfl rfl rfl
    (handover_gate_ok T) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun t => by simp [hb]) (by simp [hb]) harb

end Formal.Cells.SpecArbVacuous
