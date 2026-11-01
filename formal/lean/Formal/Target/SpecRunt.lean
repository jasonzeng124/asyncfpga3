import Formal.Target.Spec

/-!
# Formal.Target.SpecRunt — a runt-filtering variant of the statement (H_RUNT(w)), for the owner's decision

Shard A, 2026-11-01. An ADDITION next to the frozen `Spec.lean` (it changes no definition there).

**Why.** Under the frozen H_PRIM (`GateOK`: every pin reads its input at a monotone time inside its delay
band) a LUT pin may read a pulse of any width, so a runt in a LUT feedback loop can circulate for ever. Shard B
found (JOURNAL-B 09:47-10:20) that this alone sets the sequential statement's scatter margin at κ ≈ 0.155 on the
target, while with narrow pulses not propagated the same delays are harmless. Whether silicon kills such pulses
is a fact about the fabric, so it can only enter as a named hypothesis. This file states it, so that the owner
can choose between `Spec.NetCorrectSeq` (pessimistic, as PROGRAM asks) and `NetCorrectSeqRunt w`.

**H_RUNT(w), plainly.** No gate pin ever reads its input inside a pulse narrower than `w` ps: if the input holds a
value on `[a, b)` only (different just before `a` and at `b`) with `b - a < w`, no read time lands in `[a, b)`.
It is a restriction on the read maps, so every `GateOKRunt` behaviour is a `GateOK` behaviour (`gateOK_of_runt`):
`NetCorrectSeq` implies `NetCorrectSeqRunt w` for every `w`, never the other way round. `w = 0` is the frozen
statement (`runt_zero`).

**Not shown here.** That the fabric has such a `w`, or its value: that is the test in `formal/FOR-RESEARCH.md` 3.
-/

namespace Formal.Target

/-- `s` holds a pulse on `[a, b)`: constant there, different just before `a` (or `a = 0`) and at `b`. -/
def Pulse (s : Sig) (a b : Nat) : Prop :=
  a < b ∧ (∀ t, a ≤ t → t < b → s t = s a) ∧ (0 < a → s (a - 1) ≠ s a) ∧ s b ≠ s a

/-- **H_RUNT(w)** for one read map: read time `u` of input `s` never lands in a pulse narrower than `w`. -/
def NoRuntRead (w : Nat) (s : Sig) (u : Nat) : Prop :=
  ∀ a b, Pulse s a b → b - a < w → ¬ (a ≤ u ∧ u < b)

/-- `GateOK` with every pin read obeying H_RUNT(w). -/
def GateOKRunt (w : Nat) (p : DelayPar) (c : ℚ) (g : Gate) (x : Beh) : Prop :=
  ∃ f : Nat → Nat → Nat,
    (∀ i, i < g.k → Monotone (f i)) ∧
    ∀ t, g.start p ≤ t →
      (∀ i, i < g.k → f i t ≤ t ∧ Adm p c (g.arcs.getD i default) (t - f i t) ∧
        NoRuntRead w (x (g.ins.getD i 0)) (f i t)) ∧
      x g.out t = g.init.testBit (addr g.k fun i => x (g.ins.getD i 0) (f i t))

def BehavesRunt (w : Nat) (p : DelayPar) (N : Net) (x : Beh) : Prop :=
  ∃ c : ℚ, 0 ≤ c ∧ c ≤ 1 ∧ ∀ g ∈ N.gates, GateOKRunt w p c g x

/-- **The sequential statement under H_RUNT(w).** -/
def NetCorrectSeqRunt (w : Nat) (N : Net) (B : Boundary) (A : List ArbNodes) (p : DelayPar) (T R su Δo : Nat) : Prop :=
  ∀ (x : Beh) (n : Option Nat) (va vb : Nat → Nat),
    BehavesRunt w p (circuit N B) x → ArbOK T A x → Env x B R su Δo n va vb → SeqEnv x B R →
      Correct x B R Δo n va vb

theorem gateOK_of_runt {w : Nat} {p : DelayPar} {c : ℚ} {g : Gate} {x : Beh} (h : GateOKRunt w p c g x) :
    GateOK p c g x := by
  obtain ⟨f, hm, ht⟩ := h
  exact ⟨f, hm, fun t h0 => ⟨fun i hi => ⟨(ht t h0).1 i hi |>.1, (ht t h0).1 i hi |>.2.1⟩, (ht t h0).2⟩⟩

theorem behaves_of_runt {w : Nat} {p : DelayPar} {N : Net} {x : Beh} (h : BehavesRunt w p N x) : Behaves p N x := by
  obtain ⟨c, h0, h1, hg⟩ := h
  exact ⟨c, h0, h1, fun g hg' => gateOK_of_runt (hg g hg')⟩

/-- The frozen sequential statement implies its runt-filtered variant for every `w`. -/
theorem seqRunt_of_seq (w : Nat) {N : Net} {B : Boundary} {A : List ArbNodes} {p : DelayPar} {T R su Δo : Nat}
    (h : NetCorrectSeq N B A p T R su Δo) : NetCorrectSeqRunt w N B A p T R su Δo :=
  fun x n va vb hb ha he hs => h x n va vb (behaves_of_runt hb) ha he hs

theorem noRunt_zero (s : Sig) (u : Nat) : NoRuntRead 0 s u := fun a b _ hw => absurd hw (Nat.not_lt_zero _)

/-- `w = 0` is the frozen statement. -/
theorem runt_zero {N : Net} {B : Boundary} {A : List ArbNodes} {p : DelayPar} {T R su Δo : Nat} :
    NetCorrectSeqRunt 0 N B A p T R su Δo ↔ NetCorrectSeq N B A p T R su Δo := by
  refine ⟨fun h x n va vb hb ha he hs => h x n va vb ?_ ha he hs, seqRunt_of_seq 0⟩
  obtain ⟨c, h0, h1, hg⟩ := hb
  refine ⟨c, h0, h1, fun g hg' => ?_⟩
  obtain ⟨f, hm, ht⟩ := hg g hg'
  exact ⟨f, hm, fun t h2 => ⟨fun i hi => ⟨((ht t h2).1 i hi).1, ((ht t h2).1 i hi).2, noRunt_zero _ _⟩, (ht t h2).2⟩⟩

end Formal.Target
