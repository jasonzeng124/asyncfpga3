import Formal.Target.Spec
import Formal.Cells.ArbT
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Formal.Cells.ArbTSpec — the arbiter's double acknowledge, as a behaviour of the frozen Spec

Shard B, THE goal. `ArbT.double_ack` was stated over B's read-time gates. Here the same
trace is a behaviour of the frozen `Formal.Target.Spec`: six Spec `Gate`s (ustate O6/O5,
ugrant O5/O6, ua1, ua2, real INITs with tied pins folded), `Behaves` at the slow corner
with g = 1, κ = 0, and the frozen `ArbOK T` for every `T ≥ 9`.

## Problem, plainly
Does the frozen statement's H_ARB(T) prevent an arbiter from acknowledging both clients
in one server transaction? **No**: `spec_double_ack`. With H_ARB(T) as frozen (q constant
`T` after the two requests are), a near-tie leaves q oscillating until 20 while the server
raises A0 at 18 (6 ps after R0 rose); A1 rises at 19 and A2 at 20. Every gate relation
holds (monotone read maps, every read delay admissible).

## What it means
THE theorem cannot be proved from H_ARB(T) by treating the arbiter as safe: the proof
must derive that every arbiter's q is settled before its A0 rises at ua (ArbT.one_ack), a
timing obligation through the server path. For T at least the shortest such path in the
target, this shape is a candidate counterexample there.

Node numbering: 0 r1, 1 r2, 2 q, 3 rst, 4 A0, 5 R0, 6 g1, 7 g2, 8 A1, 9 A2.
-/

namespace Formal.Cells.ArbTSpec

open Formal.Target
open Formal.Cells.ArbT (qInit r0Init g1Init g2Init uaInit cr1 cr2 crst ca0 cq cR0 cg1 cg2 cA1 cA2
  qread pins)

theorem addr_same : ∀ (k : Nat) (v : Nat → Bool), Formal.Target.addr k v = Formal.Cells.ArbT.addr k v
  | 0, _ => rfl
  | k + 1, v => by simp only [Formal.Target.addr, Formal.Cells.ArbT.addr, addr_same k v]

def e1 : Arc := ⟨1, 1, 1, 1⟩
def eq : Arc := ⟨2, 2, 2, 3⟩

def gQ : Gate := ⟨"ustate.O6", 5, qInit, [0, 1, 2, 3, 4], [e1, e1, eq, e1, e1], 2⟩
def gR0 : Gate := ⟨"ustate.O5", 5, r0Init, [0, 1, 2, 3, 4], [e1, e1, e1, e1, e1], 5⟩
def gG1 : Gate := ⟨"ugrant.O5", 3, g1Init, [0, 1, 2], [e1, e1, e1], 6⟩
def gG2 : Gate := ⟨"ugrant.O6", 3, g2Init, [0, 1, 2], [e1, e1, e1], 7⟩
def gA1 : Gate := ⟨"ua1", 4, uaInit, [6, 4, 8, 3], [e1, e1, e1, e1], 8⟩
def gA2 : Gate := ⟨"ua2", 4, uaInit, [7, 4, 9, 3], [e1, e1, e1, e1], 9⟩

def arbNet : Net := ⟨10, ["r1", "r2", "q", "rst", "A0", "R0", "g1", "g2", "A1", "A2"],
  [gQ, gR0, gG1, gG2, gA1, gA2]⟩

/-- The trace of `ArbT.double_ack` on the ten nodes. -/
def beh : Beh := fun n =>
  if n = 0 then cr1 else if n = 1 then cr2 else if n = 2 then cq else if n = 3 then crst
  else if n = 4 then ca0 else if n = 5 then cR0 else if n = 6 then cg1 else if n = 7 then cg2
  else if n = 8 then cA1 else cA2

def p1 : DelayPar := ⟨1, 0⟩

theorem adm_e1 (d : Nat) : Adm p1 1 e1 d ↔ d = 1 := by
  simp only [Adm, p1, e1, lerp]
  constructor
  · rintro ⟨h1, h2, -, -⟩
    have : (d : ℚ) = 1 := le_antisymm (by simpa using h2) (by simpa using h1)
    exact_mod_cast this
  · rintro rfl; norm_num

theorem adm_eq (d : Nat) : Adm p1 1 eq d ↔ 2 ≤ d ∧ d ≤ 3 := by
  simp only [Adm, p1, eq, lerp]
  constructor
  · rintro ⟨h1, h2, -, -⟩
    constructor
    · have : (2 : ℚ) ≤ d := by simpa using h1
      exact_mod_cast this
    · have : (d : ℚ) ≤ 3 := by simpa using h2
      exact_mod_cast this
  · rintro ⟨h1, h2⟩
    have h1' : (2 : ℚ) ≤ d := by exact_mod_cast h1
    have h2' : (d : ℚ) ≤ 3 := by exact_mod_cast h2
    refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num <;> linarith

theorem startQ : gQ.start p1 = 3 := by simp [Gate.start, gQ, e1, eq, p1]; decide
/-- A gate all of whose arcs are `e1` and whose start is 1, read with unit delay, holds as
soon as its value equation holds from 1 on. -/
theorem unit_gate (g : Gate) (hs : g.start p1 = 1) (harc : ∀ i, i < g.k → g.arcs.getD i default = e1)
    (hv : ∀ t, 1 ≤ t → beh g.out t = g.init.testBit (Formal.Target.addr g.k fun i => beh (g.ins.getD i 0) (t - 1))) :
    GateOK p1 1 g beh := by
  refine ⟨fun _ t => t - 1, fun _ _ _ _ hab => Nat.sub_le_sub_right hab 1, fun t ht => ⟨fun i hi => ?_, hv t ?_⟩⟩
  · rw [hs] at ht
    refine ⟨by simp, ?_⟩
    rw [harc i hi, adm_e1]; simp; omega
  · rw [hs] at ht; exact ht

theorem gateOK_all : ∀ g ∈ arbNet.gates, GateOK p1 1 g beh := by
  intro g hg
  simp only [arbNet, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · -- q: the read map of ArbT, with the resolving read at 21
    refine ⟨qread, fun i _ a b hab => ?_, fun t ht => ⟨fun i hi => ?_, ?_⟩⟩
    · show qread i a ≤ qread i b
      unfold qread; repeat' split
      all_goals omega
    · rw [startQ] at ht
      have hk : gQ.k = 5 := rfl
      rw [hk] at hi
      rcases i with _ | _ | _ | _ | _ | i
      · exact ⟨by simp [qread], by rw [show gQ.arcs.getD 0 default = e1 from rfl, adm_e1]; simp [qread]; omega⟩
      · exact ⟨by simp [qread], by rw [show gQ.arcs.getD 1 default = e1 from rfl, adm_e1]; simp [qread]; omega⟩
      · rw [show gQ.arcs.getD 2 default = eq from rfl, adm_eq]
        by_cases h21 : t = 21 <;> simp [qread, h21] <;> omega
      · exact ⟨by simp [qread], by rw [show gQ.arcs.getD 3 default = e1 from rfl, adm_e1]; simp [qread]; omega⟩
      · exact ⟨by simp [qread], by rw [show gQ.arcs.getD 4 default = e1 from rfl, adm_e1]; simp [qread]; omega⟩
      · omega
    · rw [startQ] at ht
      show cq t = qInit.testBit (Formal.Target.addr 5 fun i => beh ([0, 1, 2, 3, 4].getD i 0) (qread i t))
      rw [addr_same, Formal.Cells.ArbT.cex_q t ht]
      rfl
  all_goals
    apply unit_gate _ (by simp [Gate.start, gR0, gG1, gG2, gA1, gA2, e1, p1]; decide) (by decide)
    intro t ht
    by_cases h3 : t < 3
    · rcases (show t = 1 ∨ t = 2 by omega) with rfl | rfl <;> decide
    · rw [addr_same]
      first
        | exact Formal.Cells.ArbT.cex_R0 t (by omega)
        | exact Formal.Cells.ArbT.cex_g1 t (by omega)
        | exact Formal.Cells.ArbT.cex_g2 t (by omega)
        | exact Formal.Cells.ArbT.cex_A1 t (by omega)
        | exact Formal.Cells.ArbT.cex_A2 t (by omega)

theorem behaves : Behaves p1 arbNet beh := ⟨1, by norm_num, le_refl _, gateOK_all⟩

/-- The frozen H_ARB(T), for this arbiter, for every `T ≥ 9`. -/
theorem arbOK (T : Nat) (hT : 9 ≤ T) : ArbOK T [⟨0, 1, 2⟩] beh := by
  intro a ha t1 t2 h1 h2 t ht1 ht2
  simp only [List.mem_singleton] at ha
  subst ha
  show cq t = cq (t1 + T)
  by_cases hlate : 20 ≤ t1 + T
  · simp only [cq]; simp [show ¬ (t < 20) by omega, show ¬ (t1 + T < 20) by omega]
  · by_cases hearly : t2 ≤ 10
    · simp only [cq]; simp [show ¬ (11 ≤ t) by omega, show ¬ (11 ≤ t1 + T) by omega]
    · exfalso
      by_cases a : t1 ≤ 9
      · have := h1 10 (by omega) (by omega); simp [beh, cr1] at this; omega
      · have := h2 11 (by omega) (by omega); simp [beh, cr2] at this; omega

/-- **Double acknowledge under the frozen Spec.** The six arbiter gates hold (`Behaves`,
slow corner, g = 1, κ = 0), the frozen H_ARB(T) holds for every `T ≥ 9`, R0 rises once (at
12) and stays high, the server raises A0 at 18, and both A1 (19) and A2 (20) rise. -/
theorem spec_double_ack (T : Nat) (hT : 9 ≤ T) :
    Behaves p1 arbNet beh ∧ ArbOK T [⟨0, 1, 2⟩] beh ∧
    (∀ t, beh 5 t = decide (12 ≤ t)) ∧ (∀ t, beh 4 t = decide (18 ≤ t)) ∧
    beh 8 18 = false ∧ beh 8 19 = true ∧ beh 9 19 = false ∧ beh 9 20 = true :=
  ⟨behaves, arbOK T hT, fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, rfl⟩

end Formal.Cells.ArbTSpec
