import Formal.Target.Spec
import Formal.Cells.ArbT
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Formal.Cells.ArbTSpec — the arbiter's double acknowledge, as a behaviour of the frozen Spec

Shard B, THE goal. `ArbT.double_ack` was stated over B's read-time gates. Here the same
trace is a behaviour of the frozen `Formal.Target.Spec`: six Spec `Gate`s (ustate O6/O5,
ugrant O5/O6, ua1, ua2, real INITs with tied pins folded), `Behaves` at the slow corner
with g = 1, κ = 0, and the Spec's `ArbOK T` (as repaired by shard A at 08:11: q constant `T`
after all four non-feedback inputs of the state LUT are) for every `T ≥ 7`.

## Problem, plainly
Does the frozen statement's H_ARB(T) prevent an arbiter from acknowledging both clients
in one server transaction? **No**: `spec_double_ack`. With H_ARB(T) as repaired (q constant
`T` after all four non-feedback inputs of the state LUT are), a near-tie leaves q oscillating until 20 while the server
raises A0 at 18 (6 ps after R0 rose); A1 rises at 19 and A2 at 20. Every gate relation
holds (monotone read maps, every read delay admissible).

## What it means
THE theorem cannot be proved from H_ARB(T) by treating the arbiter as safe: the proof
must derive that every arbiter's q is settled before its A0 rises at ua (ArbT.one_ack), a
timing obligation through the server path. Whether this shape is reachable on the target is
open: in simulation (JOURNAL-B, 2026-11-01, 16 rig vectors, adversarial in-band skew) no arbiter of
the target ever sees two requests closer than ~50 ns, so no near-tie arises there.

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
  · rintro ⟨h1, h2⟩
    norm_num at h1 h2
    omega
  · rintro rfl; norm_num

theorem adm_eq (d : Nat) : Adm p1 1 eq d ↔ 2 ≤ d ∧ d ≤ 3 := by
  simp only [Adm, p1, eq, lerp]
  constructor
  · rintro ⟨h1, h2⟩
    norm_num at h1 h2
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  · rintro ⟨h1, h2⟩
    have h1' : (2 : ℚ) ≤ d := by exact_mod_cast h1
    have h2' : (d : ℚ) ≤ 3 := by exact_mod_cast h2
    refine ⟨?_, ?_⟩ <;> norm_num <;> linarith

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

/-- The arbiter's nodes for the Spec's (repaired, 08:11) H_ARB: q 2; inputs r1 0, r2 1, rst 3, A0 4. -/
def arbN : ArbNodes := ⟨2, [0, 1, 3, 4]⟩

/-- The Spec's H_ARB(T) (repaired form), for this arbiter, for every `T ≥ 7`. -/
theorem arbOK (T : Nat) (hT : 7 ≤ T) : ArbOK T [arbN] beh := by
  intro a ha t1 t2 hc
  simp only [List.mem_singleton] at ha
  subst ha
  exact Formal.Cells.ArbT.cex_arb T hT t1 t2 (hc 0 (by simp [arbN])) (hc 1 (by simp [arbN]))
    (hc 3 (by simp [arbN])) (hc 4 (by simp [arbN]))

/-- **Double acknowledge under the frozen Spec.** The six arbiter gates hold (`Behaves`,
slow corner, g = 1, κ = 0), the Spec's H_ARB(T) (repaired form) holds for every `T ≥ 7`, R0 rises once (at
12) and stays high, the server raises A0 at 18, and both A1 (19) and A2 (20) rise. -/
theorem spec_double_ack (T : Nat) (hT : 7 ≤ T) :
    Behaves p1 arbNet beh ∧ ArbOK T [arbN] beh ∧
    (∀ t, beh 5 t = decide (12 ≤ t)) ∧ (∀ t, beh 4 t = decide (18 ≤ t)) ∧
    beh 8 18 = false ∧ beh 8 19 = true ∧ beh 9 19 = false ∧ beh 9 20 = true :=
  ⟨behaves, arbOK T hT, fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, rfl⟩

end Formal.Cells.ArbTSpec

/-! ## Bridge: Spec gates are read-time gates, so `ArbT`'s positive results apply -/

namespace Formal.Cells.ArbTSpec

open Formal.Target
open Formal.Cells.ArbT (g2Init uaInit pins)

/-- A Spec gate (with Nat bounds implied by `Adm`) is a `ArbT.RGate` on its pin nodes. -/
theorem rgate_of_gateOK {p : DelayPar} {c : ℚ} {g : Gate} {x : Beh} (hg : GateOK p c g x)
    {lo hi : Nat → Nat} (hb : ∀ i, i < g.k → ∀ d, Adm p c (g.arcs.getD i default) d → lo i ≤ d ∧ d ≤ hi i) :
    Formal.Cells.ArbT.RGate g.k g.init (fun i => x (g.ins.getD i 0)) lo hi (g.start p) (x g.out) := by
  obtain ⟨f, _, hf⟩ := hg
  refine ⟨f, fun t ht => ⟨fun i hi' => ?_, ?_⟩⟩
  · have h := (hf t ht).1 i hi'
    have hd := hb i hi' _ h.2
    omega
  · rw [(hf t ht).2, addr_same]; rfl

/-- **One acknowledge per server transaction, for Spec gates.** ugrant's O6 gate `gg2`
(table `g2Init`, pins r1, r2, q) and ua2's gate `ga2` (table `uaInit`, pins g2, A0, A2, rst),
with Nat bounds on their arcs: if q is high on every instant g2's gate reads during
`[s - hi_a0, e]` (q settled before A0 rises), and A2 is low on its feedback window before `s`,
then A2 stays low on `[s, e]` whatever A0 does. -/
theorem spec_one_ack {p : DelayPar} {c : ℚ} {gg2 ga2 : Gate} {x : Beh}
    (h2 : GateOK p c gg2 x) (ha : GateOK p c ga2 x)
    (hk2 : gg2.k = 3) (hi2 : gg2.init = g2Init) (hka : ga2.k = 4) (hia : ga2.init = uaInit)
    (hwire : ga2.ins.getD 0 0 = gg2.out) (hself : ga2.ins.getD 2 0 = ga2.out)
    {log hig loa hia' : Nat → Nat}
    (hb2 : ∀ i, i < gg2.k → ∀ d, Adm p c (gg2.arcs.getD i default) d → log i ≤ d ∧ d ≤ hig i)
    (hba : ∀ i, i < ga2.k → ∀ d, Adm p c (ga2.arcs.getD i default) d → loa i ≤ d ∧ d ≤ hia' i)
    (hlo : 1 ≤ loa 2) {s e : Nat} (hs : max (gg2.start p) (ga2.start p) + hia' 0 ≤ s)
    (hq : ∀ u, s ≤ u + hia' 0 + hig 2 → u ≤ e → x (gg2.ins.getD 2 0) u = true)
    (hpre : ∀ t, s ≤ t + hia' 2 → t < s → x ga2.out t = false) :
    ∀ t, s ≤ t → t ≤ e → x ga2.out t = false := by
  have r2 := rgate_of_gateOK h2 hb2
  have ra := rgate_of_gateOK ha hba
  rw [hk2, hi2] at r2
  rw [hka, hia] at ra
  -- re-express the pin functions as `pins` lists
  obtain ⟨f2, hf2⟩ := r2
  obtain ⟨fa, hfa⟩ := ra
  have r2' : Formal.Cells.ArbT.RGate 3 g2Init
      (pins [x (gg2.ins.getD 0 0), x (gg2.ins.getD 1 0), x (gg2.ins.getD 2 0)]) log hig (max (gg2.start p) (ga2.start p)) (x gg2.out) :=
    ⟨f2, fun t ht => ⟨(hf2 t (by omega)).1, by rw [(hf2 t (by omega)).2]; rfl⟩⟩
  have ra' : Formal.Cells.ArbT.RGate 4 uaInit
      (pins [x gg2.out, x (ga2.ins.getD 1 0), x ga2.out, x (ga2.ins.getD 3 0)]) loa hia' (max (gg2.start p) (ga2.start p)) (x ga2.out) :=
    ⟨fa, fun t ht => ⟨(hfa t (by omega)).1, by rw [(hfa t (by omega)).2, ← hwire, ← hself]; rfl⟩⟩
  exact Formal.Cells.ArbT.one_ack r2' ra' hlo hs hq hpre

end Formal.Cells.ArbTSpec
