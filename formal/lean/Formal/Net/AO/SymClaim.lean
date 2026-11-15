import Formal.Net.TimedOccDecX
import Formal.Net.TimedOccU

/-!
# Claims with symbolic values: one finite check for every instantiation (shard C, 2026-11-15; piece 3, step 2.1)

**Problem, plainly.** A per-kind window certificate must hold for every operand pair. Its control claims have fixed
values, but the claims on register latch outputs and on the datapath carry register *bits*, which differ from pair to
pair (and window to window). With literal Boolean values the per-kind checks would have to be repeated per pair
(2^62 pairs). Can a claim carry a *symbolic* value (a literal, or a register-bit symbol possibly negated), with the
claim proofs checked once, for every assignment of the symbols?

**The model.** `TClaim α V`: a claim whose value is an `SVal V` (`lit b`, or `sym v neg`: the symbol `v` xor
`neg`); `inst ρ` turns it into an ordinary `Claim` under an assignment `ρ : V → Bool` (for a pair: the token run's
register bits). The timing fields are untouched.

**Proved.**
* `valSB` (a Boolean check over the symbols that the claim and its covering claims mention, and the gate's pins) and
  `valOK_inst`: if `valSB` passes, then `ValOK` holds for the instantiated claim list and claim under EVERY `ρ`.
* `GateProofS` (value check `valSB`, timing and cover facts on the templates) and `gateProof_inst`: it gives
  `TimedOccU.GateProof` for the instantiated claims under every `ρ`. So a GateProof-proved template claim is proved
  for every pair at once.
* `inst_timing`: instantiation changes only values (node and window are the template's).

**Not shown.** The union/chain rules (`ChainUOK`) on templates (they compare values: equal `SVal`s suffice, not
written); the unrolled form (per-window symbol renaming); the instance; that the token run's register bits are what
the latches hold (the window invariant, step 2.3).
-/

namespace Formal.Net.AO.Sym
open Formal.Net.OccNet Formal.Net.OccNet.Timed Formal.Net.OccNet.TimedX Formal.Net.OccNet.TimedDecX
  Formal.Net.OccNet.TimedU

variable {α V : Type} [DecidableEq α] [DecidableEq V]

/-- A symbolic claim value: a literal, or a symbol xor `neg`. -/
inductive SVal (V : Type) where
  | lit (b : Bool)
  | sym (v : V) (neg : Bool)
  deriving DecidableEq

def SVal.eval (ρ : V → Bool) : SVal V → Bool
  | .lit b => b
  | .sym v n => xor (ρ v) n

def SVal.syms : SVal V → List V
  | .lit _ => []
  | .sym v _ => [v]

theorem SVal.eval_congr {ρ ρ' : V → Bool} (s : SVal V) (h : ∀ v ∈ s.syms, ρ v = ρ' v) : s.eval ρ = s.eval ρ' := by
  cases s with
  | lit b => rfl
  | sym v n => simp only [eval]; rw [h v (by simp [syms])]

/-- A claim template: a claim whose value is symbolic. -/
structure TClaim (α V : Type) where
  z : α
  sv : SVal V
  A : Option (α × Nat)
  a : Int
  B : Option (α × Nat)
  b : Nat

/-- The claim under the assignment `ρ`. -/
def TClaim.inst (ρ : V → Bool) (c : TClaim α V) : Claim α := ⟨c.z, c.sv.eval ρ, c.A, c.a, c.B, c.b⟩

def instL (ρ : V → Bool) (tcl : List (TClaim α V)) : List (Claim α) := tcl.map (TClaim.inst ρ)

omit [DecidableEq α] [DecidableEq V] in
theorem inst_timing (ρ : V → Bool) (c : TClaim α V) :
    (c.inst ρ).z = c.z ∧ (c.inst ρ).A = c.A ∧ (c.inst ρ).a = c.a ∧ (c.inst ρ).B = c.B ∧ (c.inst ρ).b = c.b :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

omit [DecidableEq α] [DecidableEq V] in
theorem instL_get (ρ : V → Bool) (tcl : List (TClaim α V)) (i : Nat) :
    (instL ρ tcl)[i]? = (tcl[i]?).map (TClaim.inst ρ) := by
  simp [instL]

/-- The symbolic value a cover stands for. -/
def covSV (s0 : α → Bool) (tcl : List (TClaim α V)) (u : α) : Cov → Option (SVal V)
  | .ex k => some (.lit (xor (s0 u) (k % 2 == 1)))
  | .cl i => (tcl[i]?).map TClaim.sv
  | .X => none

theorem covWin_inst (s0 : α → Bool) (tcl : List (TClaim α V)) (ρ : V → Bool) (u : α) (cv : Cov) (w : Claim α)
    (h : covWin s0 (instL ρ tcl) u cv = some w) : ∃ s, covSV s0 tcl u cv = some s ∧ w.val = s.eval ρ := by
  cases cv with
  | ex k =>
    simp only [covWin, Option.some.injEq] at h
    subst h
    exact ⟨_, rfl, rfl⟩
  | cl i =>
    simp only [covWin, instL_get] at h
    cases ht : tcl[i]? with
    | none => rw [ht] at h; simp at h
    | some c =>
      rw [ht] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      exact ⟨c.sv, by simp [covSV, ht], rfl⟩
  | X => simp [covWin] at h

theorem asg_map' (Z : List α) (bb : α → Bool) : ∀ z ∈ Z, asg Z (Z.map bb) z = bb z := by
  induction Z with
  | nil => intro z hz; simp at hz
  | cons a Z ih =>
    intro z hz
    simp only [asg, List.map_cons, List.zip_cons_cons, List.find?_cons]
    by_cases h : a = z
    · subst h; simp
    · have hz' : z ∈ Z := by
        rcases List.mem_cons.mp hz with h' | h'
        · exact absurd h'.symm h
        · exact h'
      have := ih z hz'
      simp only [asg] at this
      have hb : (a == z) = false := by simp [h]
      rw [hb]; exact this

/-- The symbols a claim proof reads: the claim's own and its covering claims'. -/
def symsOf (N : TNet α) (s0 : α → Bool) (tcl : List (TClaim α V)) (c : TClaim α V) (cov : α → Cov) : List V :=
  c.sv.syms ++ (N.pins c.z).flatMap fun u => match covSV s0 tcl u (cov u) with
    | some s => s.syms
    | none => []

/-- **The symbolic value check**: for every assignment of the symbols read and every pin assignment agreeing with
the covered (symbolic) values, the gate gives the claim's (symbolic) value. -/
def valSB (N : TNet α) (s0 : α → Bool) (tcl : List (TClaim α V)) (c : TClaim α V) (cov : α → Cov) : Bool :=
  let P := N.pins c.z
  let S := symsOf N s0 tcl c cov
  (allBools S.length).all fun ss => (allBools P.length).all fun bs =>
    !(P.all fun u => match covSV s0 tcl u (cov u) with
      | some s => asg P bs u == s.eval (asg S ss)
      | none => true) ||
    (N.F c.z (P.map (asg P bs)) == c.sv.eval (asg S ss))

/-- **The symbolic check gives `ValOK` under every assignment.** -/
theorem valOK_inst (N : TNet α) (s0 : α → Bool) (tcl : List (TClaim α V)) (c : TClaim α V) (cov : α → Cov)
    (h : valSB N s0 tcl c cov = true) (ρ : V → Bool) :
    ValOK N s0 (instL ρ tcl) (c.inst ρ) cov := by
  intro bb hbb
  let P := N.pins c.z
  let S := symsOf N s0 tcl c cov
  have hS : ∀ v ∈ S, asg S (S.map ρ) v = ρ v := asg_map' S ρ
  have h1 := List.all_eq_true.1 h (S.map ρ) (by have := mem_allBools (S.map ρ); simpa using this)
  have h2 := List.all_eq_true.1 h1 (P.map bb) (by have := mem_allBools (P.map bb); simpa using this)
  have hP : ∀ u ∈ P, asg P (P.map bb) u = bb u := asg_map' P bb
  have hcons : (P.all fun u => match covSV s0 tcl u (cov u) with
      | some s => asg P (P.map bb) u == s.eval (asg S (S.map ρ))
      | none => true) = true := by
    apply List.all_eq_true.2
    intro u hu
    cases hcs : covSV s0 tcl u (cov u) with
    | none => rfl
    | some s =>
      simp only [beq_iff_eq]
      rw [hP u hu]
      have hsS : ∀ v ∈ s.syms, asg S (S.map ρ) v = ρ v := by
        intro v hv
        apply hS
        simp only [S, symsOf, List.mem_append, List.mem_flatMap]
        right
        exact ⟨u, hu, by rw [hcs]; exact hv⟩
      rw [s.eval_congr hsS]
      -- the covered value under ρ
      cases hcw : covWin s0 (instL ρ tcl) u (cov u) with
      | none =>
        exfalso
        revert hcs hcw
        cases cov u with
        | ex k => intro _ h; simp [covWin] at h
        | cl i =>
          intro hcs hcw
          simp only [covSV] at hcs
          simp only [covWin, instL_get] at hcw
          cases ht : tcl[i]? with
          | none => rw [ht] at hcs; simp at hcs
          | some c' => rw [ht] at hcw; simp at hcw
        | X => intro h; simp [covSV] at h
      | some w =>
        obtain ⟨s', hs', hv⟩ := covWin_inst s0 tcl ρ u (cov u) w hcw
        rw [hcs] at hs'
        cases hs'
        rw [← hv]
        exact hbb u hu w hcw
  have h3 := h2
  rw [hcons] at h3
  simp only [Bool.not_true, Bool.false_or, beq_iff_eq] at h3
  have hcS : ∀ v ∈ c.sv.syms, asg S (S.map ρ) v = ρ v := by
    intro v hv; apply hS; simp only [S, symsOf, List.mem_append]; left; exact hv
  rw [c.sv.eval_congr hcS] at h3
  have hm : P.map (asg P (P.map bb)) = P.map bb := List.map_congr_left (fun u hu => hP u hu)
  rw [hm] at h3
  exact h3

/-- A template claim proved by a data gate: the symbolic value check plus the value-free facts. -/
def GateProofS (N : TNet α) (dat : α → Bool) (Sep : α → Nat → α → Nat → Option Nat) (s0 : α → Bool)
    (tcl : List (TClaim α V)) (c : TClaim α V) : Prop :=
  N.gate c.z = true ∧ 0 ≤ c.a ∧ ∃ cov : α → Cov, valSB N s0 tcl c cov = true ∧
    (∀ u ∈ N.pins c.z, ∀ w, covWin s0 (instL (fun _ => false) tcl) u (cov u) = some w →
      CovTime Sep (c.inst (fun _ => false)) w (N.hi c.z u) (N.lo c.z u)) ∧
    (∀ u ∈ N.pins c.z, (∀ k, cov u = .ex k → dat u = false) ∧ (∀ i w, cov u = .cl i → tcl[i]? = some w → w.z = u))

omit [DecidableEq α] [DecidableEq V] in
/-- `CovTime` reads only the timing fields. -/
theorem covTime_congr {Sep : α → Nat → α → Nat → Option Nat} {c c' w w' : Claim α} {hi lo : Nat}
    (hc : c.A = c'.A ∧ c.a = c'.a ∧ c.B = c'.B ∧ c.b = c'.b) (hw : w.A = w'.A ∧ w.a = w'.a ∧ w.B = w'.B ∧ w.b = w'.b)
    (h : CovTime Sep c w hi lo) : CovTime Sep c' w' hi lo := by
  obtain ⟨c1, c2, c3, c4⟩ := hc
  obtain ⟨w1, w2, w3, w4⟩ := hw
  unfold CovTime at *
  rw [← c1, ← c2, ← c3, ← c4, ← w1, ← w2, ← w3, ← w4]
  exact h

omit [DecidableEq α] [DecidableEq V] in
/-- Covered windows under two assignments have the same timing fields. -/
theorem covWin_timing (s0 : α → Bool) (tcl : List (TClaim α V)) (ρ ρ' : V → Bool) (u : α) (cv : Cov) (w : Claim α)
    (h : covWin s0 (instL ρ tcl) u cv = some w) :
    ∃ w', covWin s0 (instL ρ' tcl) u cv = some w' ∧ w'.A = w.A ∧ w'.a = w.a ∧ w'.B = w.B ∧ w'.b = w.b := by
  cases cv with
  | ex k =>
    simp only [covWin, Option.some.injEq] at h
    subst h
    exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
  | cl i =>
    simp only [covWin, instL_get] at h ⊢
    cases ht : tcl[i]? with
    | none => rw [ht] at h; simp at h
    | some c =>
      rw [ht] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      exact ⟨c.inst ρ', rfl, rfl, rfl, rfl, rfl⟩
  | X => simp [covWin] at h

/-- **A GateProof-proved template is proved under every assignment.** -/
theorem gateProof_inst {N : TNet α} {dat : α → Bool} {Sep : α → Nat → α → Nat → Option Nat} {s0 : α → Bool}
    {tcl : List (TClaim α V)} {c : TClaim α V} (h : GateProofS N dat Sep s0 tcl c) (ρ : V → Bool) :
    GateProof N dat Sep s0 (instL ρ tcl) (c.inst ρ) := by
  obtain ⟨hg, ha, cov, hv, hct, hcf⟩ := h
  refine ⟨hg, ha, cov, valOK_inst N s0 tcl c cov hv ρ, ?_, ?_⟩
  · intro u hu w hw
    obtain ⟨w', hw', e1, e2, e3, e4⟩ := covWin_timing s0 tcl ρ (fun _ => false) u (cov u) w hw
    exact covTime_congr ⟨rfl, rfl, rfl, rfl⟩ ⟨e1, e2, e3, e4⟩ (hct u hu w' hw')
  · intro u hu
    refine ⟨(hcf u hu).1, fun i w hci hw => ?_⟩
    rw [instL_get] at hw
    cases ht : tcl[i]? with
    | none => rw [ht] at hw; simp at hw
    | some c' =>
      rw [ht] at hw
      simp only [Option.map_some, Option.some.injEq] at hw
      subst hw
      exact (hcf u hu).2 i c' hci ht



/-! ## Non-vacuity: a latch passes a symbolic bit through capture and hold -/
namespace Toy

/-- Nodes: 0 = data `d` (a register bit, symbolic), 1 = enable `en` (exact, low at the start), 2 = latch `q`
(`q := en ? d : q`). -/
def N : TNet Nat where
  gate := fun v => v == 2
  pins := fun v => if v == 2 then [0, 1, 2] else []
  F := fun _ bs => match bs with
    | [d, en, q] => if en then d else q
    | _ => false
  lo := fun _ _ => 1
  hi := fun _ _ => 2

/-- Claims: `d = s0` (symbol 0); `q = s0` while `en` is high (capture); `q = s0` while `en` is low again (hold);
and a wrong claim `q = ¬ s0`. -/
def c0 : TClaim Nat Nat := ⟨0, .sym 0 false, none, 0, none, 0⟩
def c1 : TClaim Nat Nat := ⟨2, .sym 0 false, some (1, 0), 2, some (1, 1), 1⟩
def c2 : TClaim Nat Nat := ⟨2, .sym 0 false, some (1, 1), 2, none, 0⟩
def c3 : TClaim Nat Nat := ⟨2, .sym 0 true, some (1, 0), 2, some (1, 1), 1⟩
def tcl : List (TClaim Nat Nat) := [c0, c1, c2, c3]

def covCap : Nat → Cov := fun u => if u = 0 then .cl 0 else if u = 1 then .ex 1 else .X
def covHold : Nat → Cov := fun u => if u = 0 then .X else if u = 1 then .ex 2 else .cl 1

/-- Capture and hold pass the symbolic check (so they are proved for both values of the bit at once); the wrong
claim does not. -/
theorem toy_valSB :
    valSB N (fun _ => false) tcl c1 covCap = true ∧
    valSB N (fun _ => false) tcl c2 covHold = true ∧
    valSB N (fun _ => false) tcl c3 covCap = false := by decide

/-- Hence capture and hold are `ValOK` for every value of the register bit. -/
theorem toy_valOK (ρ : Nat → Bool) :
    ValOK N (fun _ => false) (instL ρ tcl) (c1.inst ρ) covCap ∧ ValOK N (fun _ => false) (instL ρ tcl) (c2.inst ρ) covHold :=
  ⟨valOK_inst N _ tcl c1 covCap toy_valSB.1 ρ, valOK_inst N _ tcl c2 covHold toy_valSB.2.1 ρ⟩

end Toy
end Formal.Net.AO.Sym
