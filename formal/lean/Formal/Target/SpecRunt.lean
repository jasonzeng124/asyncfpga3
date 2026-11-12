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

**H_RUNT(w), plainly (corrected 2026-11-06, audit row T9).** No LUT input pin ever reads its input inside a
pulse narrower than `w` ps: if the input holds a value on `[a, b)` only (different just before `a` and at `b`)
with `b - a < w`, no read time of a LUT pin lands in `[a, b)`. The owner's wording is "a LUT input pulse narrower
than w ps does not propagate to its output", so the restriction applies to LUT gates only (`lutGate`: the
decoder names a LUT output `<site>.<A-D>LUT.O6` / `.O5`). The first version (2026-11-01) put it on EVERY gate pin,
including zero-delay pips and site hops, whose read time is forced to the present (`Adm` with a zero arc): there it
did not filter a pulse but FORBADE it on the read node, so the statement could not see an output glitch narrower
than `w` (e.g. an `out0_req` runt, a `ReqMoves` violation). The audit proved this (audit/lean/T9/ZeroPinRunt.lean).
That version is kept as `NetCorrectSeqRuntAll` for the record and must not be used.
It is a restriction on the read maps, so every `GateOKRunt` behaviour is a `GateOK` behaviour (`gateOK_of_runt`):
`NetCorrectSeq` implies `NetCorrectSeqRunt w` for every `w`, never the other way round. `w = 0` is the frozen
statement (`runt_zero`). Filtering fewer pins admits more behaviours, so `NetCorrectSeqRunt w` (LUT pins) implies
`NetCorrectSeqRuntAll w` (`seqRuntAll_of_seqRunt`): the corrected statement is the stronger one.

**Not shown here.** That the fabric has such a `w`, or its value: that is the test in `formal/FOR-RESEARCH.md` 3.
-/

namespace Formal.Target

/-- `s` holds a pulse on `[a, b)`: constant there, different just before `a` (or `a = 0`) and at `b`. -/
def Pulse (s : Sig) (a b : Nat) : Prop :=
  a < b ∧ (∀ t, a ≤ t → t < b → s t = s a) ∧ (0 < a → s (a - 1) ≠ s a) ∧ s b ≠ s a

/-- **H_RUNT(w)** for one read map: read time `u` of input `s` never lands in a pulse narrower than `w`. -/
def NoRuntRead (w : Nat) (s : Sig) (u : Nat) : Prop :=
  ∀ a b, Pulse s a b → b - a < w → ¬ (a ≤ u ∧ u < b)

/-- `l` is a prefix of `m` (kernel-reducible, unlike `String.endsWith`). -/
def prefN : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a == b && prefN as bs

/-- A LUT gate of the decoded netlist: its name ends in `LUT.O6` or `LUT.O5` (bytes of `6O.TUL` / `5O.TUL` read backwards; decoder convention,
`formal/tools-A/target/decode_base.py`; e.g. `SLICE_X0Y16.ALUT.O6`). Pips (`TILE.DST.SRC`), site hops (`hop ..`,
`~..`), MUXF7/F8, CARRY4 and constant gates are not LUT gates. -/
def lutGate (g : Gate) : Bool :=
  let r := (g.name.toByteArray.data.toList.map UInt8.toNat).reverse
  prefN [54, 79, 46, 84, 85, 76] r || prefN [53, 79, 46, 84, 85, 76] r

/-- `GateOK` with every pin read of a gate in class `L` obeying H_RUNT(w); other gates are plain `GateOK`. -/
def GateOKRuntOn (L : Gate → Bool) (w : Nat) (p : DelayPar) (c : ℚ) (g : Gate) (x : Beh) : Prop :=
  ∃ f : Nat → Nat → Nat,
    (∀ i, i < g.k → Monotone (f i)) ∧
    ∀ t, g.start p ≤ t →
      (∀ i, i < g.k → f i t ≤ t ∧ Adm p c (g.arcs.getD i default) (t - f i t) ∧
        (L g = true → NoRuntRead w (x (g.ins.getD i 0)) (f i t))) ∧
      x g.out t = g.init.testBit (addr g.k fun i => x (g.ins.getD i 0) (f i t))

/-- H_RUNT(w) on LUT pins only (the owner's hypothesis). -/
abbrev GateOKRunt (w : Nat) (p : DelayPar) (c : ℚ) (g : Gate) (x : Beh) : Prop := GateOKRuntOn lutGate w p c g x

def BehavesRuntOn (L : Gate → Bool) (w : Nat) (p : DelayPar) (N : Net) (x : Beh) : Prop :=
  ∃ c : ℚ, 0 ≤ c ∧ c ≤ 1 ∧ ∀ g ∈ N.gates, GateOKRuntOn L w p c g x

abbrev BehavesRunt (w : Nat) (p : DelayPar) (N : Net) (x : Beh) : Prop := BehavesRuntOn lutGate w p N x

def NetCorrectSeqRuntOn (L : Gate → Bool) (w : Nat) (N : Net) (B : Boundary) (A : List ArbNodes) (p : DelayPar)
    (T R su Δo : Nat) : Prop :=
  ∀ (x : Beh) (n : Option Nat) (va vb : Nat → Nat),
    BehavesRuntOn L w p (circuit N B) x → ArbOK T A x → Env x B R su Δo n va vb → SeqEnv x B R →
      Correct x B R Δo n va vb

/-- **The sequential statement under H_RUNT(w)**, the filter on LUT input pins only. -/
abbrev NetCorrectSeqRunt (w : Nat) (N : Net) (B : Boundary) (A : List ArbNodes) (p : DelayPar) (T R su Δo : Nat) :
    Prop := NetCorrectSeqRuntOn lutGate w N B A p T R su Δo

/-- The WITHDRAWN 2026-11-01 form (filter on every pin, including zero-delay pips and hops; audit T9: it forbids
sub-`w` pulses on read nodes instead of filtering them). Kept only so that the comparison below can be stated. -/
abbrev NetCorrectSeqRuntAll (w : Nat) (N : Net) (B : Boundary) (A : List ArbNodes) (p : DelayPar) (T R su Δo : Nat) :
    Prop := NetCorrectSeqRuntOn (fun _ => true) w N B A p T R su Δo

theorem gateOK_of_runt {L : Gate → Bool} {w : Nat} {p : DelayPar} {c : ℚ} {g : Gate} {x : Beh}
    (h : GateOKRuntOn L w p c g x) : GateOK p c g x := by
  obtain ⟨f, hm, ht⟩ := h
  exact ⟨f, hm, fun t h0 => ⟨fun i hi => ⟨(ht t h0).1 i hi |>.1, (ht t h0).1 i hi |>.2.1⟩, (ht t h0).2⟩⟩

theorem behaves_of_runt {L : Gate → Bool} {w : Nat} {p : DelayPar} {N : Net} {x : Beh}
    (h : BehavesRuntOn L w p N x) : Behaves p N x := by
  obtain ⟨c, h0, h1, hg⟩ := h
  exact ⟨c, h0, h1, fun g hg' => gateOK_of_runt (hg g hg')⟩

/-- The frozen sequential statement implies its runt-filtered variant for every `w`. -/
theorem seqRunt_of_seq (L : Gate → Bool) (w : Nat) {N : Net} {B : Boundary} {A : List ArbNodes} {p : DelayPar}
    {T R su Δo : Nat} (h : NetCorrectSeq N B A p T R su Δo) : NetCorrectSeqRuntOn L w N B A p T R su Δo :=
  fun x n va vb hb ha he hs => h x n va vb (behaves_of_runt hb) ha he hs

theorem noRunt_zero (s : Sig) (u : Nat) : NoRuntRead 0 s u := fun a b _ hw => absurd hw (Nat.not_lt_zero _)

/-- `w = 0` is the frozen statement. -/
theorem runt_zero {L : Gate → Bool} {N : Net} {B : Boundary} {A : List ArbNodes} {p : DelayPar} {T R su Δo : Nat} :
    NetCorrectSeqRuntOn L 0 N B A p T R su Δo ↔ NetCorrectSeq N B A p T R su Δo := by
  refine ⟨fun h x n va vb hb ha he hs => h x n va vb ?_ ha he hs, seqRunt_of_seq L 0⟩
  obtain ⟨c, h0, h1, hg⟩ := hb
  refine ⟨c, h0, h1, fun g hg' => ?_⟩
  obtain ⟨f, hm, ht⟩ := hg g hg'
  exact ⟨f, hm, fun t h2 => ⟨fun i hi => ⟨((ht t h2).1 i hi).1, ((ht t h2).1 i hi).2, fun _ => noRunt_zero _ _⟩, (ht t h2).2⟩⟩

/-- Filtering a smaller class of pins is a weaker hypothesis: if `L ≤ L'` then every `L'`-filtered behaviour is
`L`-filtered, so the `L` statement implies the `L'` statement. -/
theorem seqRuntOn_mono {L L' : Gate → Bool} (hLL : ∀ g, L g = true → L' g = true) (w : Nat) {N : Net} {B : Boundary}
    {A : List ArbNodes} {p : DelayPar} {T R su Δo : Nat} (h : NetCorrectSeqRuntOn L w N B A p T R su Δo) :
    NetCorrectSeqRuntOn L' w N B A p T R su Δo := by
  intro x n va vb hb ha he hs
  refine h x n va vb ?_ ha he hs
  obtain ⟨c, h0, h1, hg⟩ := hb
  refine ⟨c, h0, h1, fun g hg' => ?_⟩
  obtain ⟨f, hm, ht⟩ := hg g hg'
  exact ⟨f, hm, fun t h2 => ⟨fun i hi => ⟨((ht t h2).1 i hi).1, ((ht t h2).1 i hi).2.1,
    fun hL => ((ht t h2).1 i hi).2.2 (hLL g hL)⟩, (ht t h2).2⟩⟩

/-- The corrected (LUT-pin) statement implies the withdrawn all-pin one. -/
theorem seqRuntAll_of_seqRunt (w : Nat) {N : Net} {B : Boundary} {A : List ArbNodes} {p : DelayPar}
    {T R su Δo : Nat} (h : NetCorrectSeqRunt w N B A p T R su Δo) : NetCorrectSeqRuntAll w N B A p T R su Δo :=
  seqRuntOn_mono (fun _ _ => rfl) w h

/-- A copy gate (pip or hop) is not a LUT gate, so H_RUNT never constrains its read. -/
example : lutGate ⟨"INT_R_X1Y19.SS2BEG3.LOGIC_OUTS11", 1, 2, [9], [⟨49, 69, 108, 141⟩], 10⟩ = false := by decide
example : lutGate ⟨"SLICE_X0Y16.ALUT.O6", 0, 0, [], [], 0⟩ = true := by decide

end Formal.Target
