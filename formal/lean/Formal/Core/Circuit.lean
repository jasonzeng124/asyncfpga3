/-!
# Circuit layer: gates are relations, a circuit is their conjunction

This file is the generic "circuit layer" of the owner's model (PROGRAM.md,
"The model the owner has in mind", item 1):

* **Signals** live in an arbitrary type `σ` (a parameter). For the timing
  model `σ` is a trace type (`ℝ → Bool`, an event list, `ℕ → Bool`, a
  three-valued trace, ...). Nothing here depends on that choice.
* **Wires** are an arbitrary type `W`. A **behaviour** (`Beh W σ`) assigns a
  signal to every wire.
* A **gate** is a relation on behaviours (`Gate W σ := Beh W σ → Prop`).
  Typically it mentions only a few wires (its inputs and output), e.g.
  `Gate.rel2 R a b o` says `R (v a) (v b) (v o)`; it is a relation, not a
  function, because delays are only known to lie in a range.
* A **circuit** is a list of gates; `Circuit.Sat c v` says every gate relation
  holds of `v`. Composition is list append (gates over one shared wire type);
  circuits written over their own wire types are first moved into a common
  wire type with `Circuit.rename` (that is how "disjoint union with shared
  wires" is expressed: the two renaming maps identify the shared wires).
* A **spec** is a predicate on behaviours. `Refines c S` says every behaviour
  satisfying all gates satisfies `S` — exactly the theorem form
  "for all traces satisfying every gate relation, P".
* **Hiding** internal wires is existential projection along an interface map
  `ext : E → W` (`Circuit.Obs`); `RefinesObs` is refinement at the interface.

Compositional lemmas proved here:
* `Circuit.sat_append`  : Sat of a composition is the conjunction of Sats.
* `Circuit.sat_rename`  : renaming wires commutes with Sat.
* `Refines.append`      : C1 ⊑ S1 and C2 ⊑ S2 give C1 ++ C2 ⊑ S1 ∧ S2.
* `Refines.compose`     : the same for circuits on their own wire types,
  glued by renaming maps.
* `Refines.toObs`, `RefinesObs.compose` : hiding.
* `Refines.series`      : the generic two-stage "channel" lemma — two gates
  `R1 a b`, `R2 b c` with the middle wire `b` hidden refine `R a c` whenever
  `R1 ∘ R2 ⊆ R` (relational composition). Delay-channel composition (bench
  B2) is an instance.

Caveat (vacuity): a circuit whose gate relations are unsatisfiable refines
every spec. `Circuit.Receptive` states the sanity condition that rules this
out (every input behaviour extends to a satisfying one); a refinement theorem
should be read together with a receptiveness argument for the delay model.

Only Lean core is used.
-/

namespace Formal.Core

universe u v w

/-- A behaviour: a signal (of type `σ`) on every wire (of type `W`). -/
abbrev Beh (W : Type u) (σ : Type v) := W → σ

/-- A gate is a relation on behaviours. A gate normally constrains only its
own input and output wires; see `Gate.rel1`, `Gate.rel2`, `Gate.DependsOn`. -/
abbrev Gate (W : Type u) (σ : Type v) := Beh W σ → Prop

/-- A specification: a property of behaviours. -/
abbrev Spec (W : Type u) (σ : Type v) := Beh W σ → Prop

/-- A circuit is a finite collection of gates (their conjunction). -/
abbrev Circuit (W : Type u) (σ : Type v) := List (Gate W σ)

namespace Gate

variable {W : Type u} {σ : Type v}

/-- A one-input gate (a buffer/inverter/channel): relation between the
signal on wire `a` (input) and on wire `o` (output). -/
def rel1 (R : σ → σ → Prop) (a o : W) : Gate W σ := fun v => R (v a) (v o)

/-- A two-input gate: relation between inputs `a`, `b` and output `o`. -/
def rel2 (R : σ → σ → σ → Prop) (a b o : W) : Gate W σ :=
  fun v => R (v a) (v b) (v o)

/-- A gate with a list of inputs and one output. -/
def relN (R : List σ → σ → Prop) (ins : List W) (o : W) : Gate W σ :=
  fun v => R (ins.map v) (v o)

/-- The gate only looks at the wires in `S`. -/
def DependsOn (g : Gate W σ) (S : W → Prop) : Prop :=
  ∀ v v' : Beh W σ, (∀ w, S w → v w = v' w) → (g v ↔ g v')

theorem rel1_dependsOn (R : σ → σ → Prop) (a o : W) :
    (rel1 R a o).DependsOn (fun w => w = a ∨ w = o) := by
  intro v v' h
  simp only [rel1, h a (Or.inl rfl), h o (Or.inr rfl)]

theorem rel2_dependsOn (R : σ → σ → σ → Prop) (a b o : W) :
    (rel2 R a b o).DependsOn (fun w => w = a ∨ w = b ∨ w = o) := by
  intro v v' h
  simp only [rel2, h a (Or.inl rfl), h b (Or.inr (Or.inl rfl)),
    h o (Or.inr (Or.inr rfl))]

/-- Move a gate written over wires `W₁` into wire type `W` along `f`
(wire `x` of the gate is connected to wire `f x` of the host). -/
def rename {W₁ : Type w} (f : W₁ → W) (g : Gate W₁ σ) : Gate W σ :=
  fun v => g (v ∘ f)

end Gate

namespace Circuit

variable {W : Type u} {σ : Type v}

/-- All gate relations hold. -/
def Sat (c : Circuit W σ) (v : Beh W σ) : Prop := ∀ g ∈ c, g v

/-- Parallel composition over a shared wire type: the conjunction. -/
def compose (c₁ c₂ : Circuit W σ) : Circuit W σ := List.append c₁ c₂

/-- Move a circuit into wire type `W` along the wire map `f`. Wires of two
circuits mapped to the same host wire are thereby connected. -/
def rename {W₁ : Type w} (f : W₁ → W) (c : Circuit W₁ σ) : Circuit W σ :=
  c.map (Gate.rename f)

@[simp] theorem sat_nil (v : Beh W σ) : Sat ([] : Circuit W σ) v :=
  fun _ h => nomatch h

@[simp] theorem sat_cons (g : Gate W σ) (c : Circuit W σ) (v : Beh W σ) :
    Sat (g :: c) v ↔ g v ∧ Sat c v := by
  constructor
  · intro h
    exact ⟨h g (List.mem_cons_self ..), fun g' hg' => h g' (List.mem_cons_of_mem _ hg')⟩
  · rintro ⟨h1, h2⟩ g' hg'
    rcases List.mem_cons.mp hg' with rfl | hg'
    · exact h1
    · exact h2 g' hg'

/-- **Sat of a composition is the conjunction of the Sats.** -/
@[simp] theorem sat_append (c₁ c₂ : Circuit W σ) (v : Beh W σ) :
    Sat (List.append c₁ c₂) v ↔ Sat c₁ v ∧ Sat c₂ v := by
  constructor
  · intro h
    exact ⟨fun g hg => h g (List.mem_append_left _ hg),
           fun g hg => h g (List.mem_append_right _ hg)⟩
  · rintro ⟨h1, h2⟩ g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact h1 g hg
    · exact h2 g hg

theorem sat_compose (c₁ c₂ : Circuit W σ) (v : Beh W σ) :
    Sat (compose c₁ c₂) v ↔ Sat c₁ v ∧ Sat c₂ v :=
  sat_append c₁ c₂ v

/-- Renaming commutes with satisfaction. -/
@[simp] theorem sat_rename {W₁ : Type w} (f : W₁ → W) (c : Circuit W₁ σ)
    (v : Beh W σ) : Sat (rename f c) v ↔ Sat c (v ∘ f) := by
  constructor
  · intro h g hg
    exact h (Gate.rename f g) (List.mem_map_of_mem hg)
  · intro h g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    exact h g' hg'

/-- Adding gates only removes behaviours. -/
theorem Sat.left {c₁ c₂ : Circuit W σ} {v : Beh W σ}
    (h : Sat (List.append c₁ c₂) v) : Sat c₁ v := ((sat_append _ _ _).mp h).1

theorem Sat.right {c₁ c₂ : Circuit W σ} {v : Beh W σ}
    (h : Sat (List.append c₁ c₂) v) : Sat c₂ v := ((sat_append _ _ _).mp h).2

/-- Observable behaviours at an interface `ext : E → W`: the internal wires
are hidden by existential projection. -/
def Obs {E : Type w} (c : Circuit W σ) (ext : E → W) (e : Beh E σ) : Prop :=
  ∃ v : Beh W σ, Sat c v ∧ v ∘ ext = e

/-- Receptiveness (non-vacuity): every assignment of the input wires
`inp : I → W` extends to a behaviour satisfying all gates. A refinement
theorem about a non-receptive circuit may be vacuous. -/
def Receptive {I : Type w} (c : Circuit W σ) (inp : I → W) : Prop :=
  ∀ e : Beh I σ, ∃ v : Beh W σ, Sat c v ∧ v ∘ inp = e

/-- **Feed-forward composition preserves receptiveness.** If `c₁` is
receptive, only reads the wires in `D` (which include the inputs), and `c₂`
can always be satisfied by choosing only wires outside `D` (its own outputs
and internal wires), then `c₁ ++ c₂` is receptive. -/
theorem receptive_append {I : Type w} {c₁ c₂ : Circuit W σ} {inp : I → W}
    {D : W → Prop} (h₁ : Receptive c₁ inp) (hD : ∀ g ∈ c₁, g.DependsOn D)
    (hinp : ∀ i, D (inp i))
    (h₂ : ∀ v, Sat c₁ v → ∃ v', (∀ w, D w → v' w = v w) ∧ Sat c₂ v') :
    Receptive (List.append c₁ c₂) inp := by
  intro e
  obtain ⟨v, hv, rfl⟩ := h₁ e
  obtain ⟨v', hv'D, hv'⟩ := h₂ v hv
  refine ⟨v', (sat_append _ _ _).mpr ⟨fun g hg => ?_, hv'⟩, ?_⟩
  · exact (hD g hg v' v hv'D).mpr (hv g hg)
  · funext i
    exact hv'D _ (hinp i)

end Circuit

/-- `c` refines `S`: every behaviour satisfying all gate relations satisfies
`S`. This is the theorem form "∀ traces satisfying every gate, P". -/
def Refines {W : Type u} {σ : Type v} (c : Circuit W σ) (S : Spec W σ) : Prop :=
  ∀ v, Circuit.Sat c v → S v

/-- Refinement at an interface `ext : E → W` (internal wires hidden). -/
def RefinesObs {W : Type u} {σ : Type v} {E : Type w} (c : Circuit W σ)
    (ext : E → W) (S : Spec E σ) : Prop :=
  ∀ e, Circuit.Obs c ext e → S e

namespace Refines

variable {W : Type u} {σ : Type v}

/-- Weakening the spec. -/
theorem mono {c : Circuit W σ} {S S' : Spec W σ} (h : Refines c S)
    (hS : ∀ v, S v → S' v) : Refines c S' := fun v hv => hS v (h v hv)

/-- Every circuit refines the specs implied by one of its gates. -/
theorem of_mem {c : Circuit W σ} {g : Gate W σ} (hg : g ∈ c) :
    Refines c g := fun _ hv => hv g hg

/-- Adding gates on the right preserves refinement. -/
theorem append_right {c₁ : Circuit W σ} (c₂ : Circuit W σ) {S : Spec W σ}
    (h : Refines c₁ S) : Refines (List.append c₁ c₂) S :=
  fun v hv => h v hv.left

/-- Adding gates on the left preserves refinement. -/
theorem append_left (c₁ : Circuit W σ) {c₂ : Circuit W σ} {S : Spec W σ}
    (h : Refines c₂ S) : Refines (List.append c₁ c₂) S :=
  fun v hv => h v hv.right

/-- Conjunction of specs refined by the same circuit. -/
theorem and {c : Circuit W σ} {S₁ S₂ : Spec W σ} (h₁ : Refines c S₁)
    (h₂ : Refines c S₂) : Refines c (fun v => S₁ v ∧ S₂ v) :=
  fun v hv => ⟨h₁ v hv, h₂ v hv⟩

/-- **Compositional refinement** (shared wire type): if `C1 ⊑ S1` and
`C2 ⊑ S2` then `C1 ++ C2 ⊑ S1 ∧ S2`. -/
theorem append {c₁ c₂ : Circuit W σ} {S₁ S₂ : Spec W σ}
    (h₁ : Refines c₁ S₁) (h₂ : Refines c₂ S₂) :
    Refines (List.append c₁ c₂) (fun v => S₁ v ∧ S₂ v) :=
  and (append_right c₂ h₁) (append_left c₁ h₂)

/-- Assume-guarantee chaining: if `c₂` guarantees `S₂` assuming `S₁`, and
`c₁` guarantees `S₁`, the composition guarantees `S₂`. -/
theorem chain {c₁ c₂ : Circuit W σ} {S₁ S₂ : Spec W σ}
    (h₁ : Refines c₁ S₁) (h₂ : ∀ v, Circuit.Sat c₂ v → S₁ v → S₂ v) :
    Refines (List.append c₁ c₂) S₂ :=
  fun v hv => h₂ v hv.right (h₁ v hv.left)

/-- Renaming transports refinement. -/
theorem rename {W₁ : Type w} (f : W₁ → W) {c : Circuit W₁ σ} {S : Spec W₁ σ}
    (h : Refines c S) : Refines (Circuit.rename f c) (fun v => S (v ∘ f)) :=
  fun v hv => h _ ((Circuit.sat_rename f c v).mp hv)

/-- **Compositional refinement** for circuits written over their own wire
types `W₁`, `W₂` and connected into `W` by `f₁`, `f₂` (wires with a common
image are shared). -/
theorem compose {W₁ : Type w} {W₂ : Type w} {c₁ : Circuit W₁ σ}
    {c₂ : Circuit W₂ σ} {S₁ : Spec W₁ σ} {S₂ : Spec W₂ σ}
    (f₁ : W₁ → W) (f₂ : W₂ → W) (h₁ : Refines c₁ S₁) (h₂ : Refines c₂ S₂) :
    Refines (List.append (Circuit.rename f₁ c₁) (Circuit.rename f₂ c₂))
      (fun v => S₁ (v ∘ f₁) ∧ S₂ (v ∘ f₂)) :=
  append (rename f₁ h₁) (rename f₂ h₂)

/-- Hiding: a refinement whose spec only reads the interface gives an
interface refinement. -/
theorem toObs {E : Type w} {c : Circuit W σ} (ext : E → W) {S : Spec E σ}
    (h : Refines c (fun v => S (v ∘ ext))) : RefinesObs c ext S := by
  rintro e ⟨v, hv, rfl⟩
  exact h v hv

/-- Conversely, interface refinement is refinement of the pulled-back spec. -/
theorem ofObs {E : Type w} {c : Circuit W σ} (ext : E → W) {S : Spec E σ}
    (h : RefinesObs c ext S) : Refines c (fun v => S (v ∘ ext)) :=
  fun v hv => h _ ⟨v, hv, rfl⟩

/-- **Series composition of two one-input relations, middle wire hidden.**
If `R₁ ∘ R₂ ⊆ R` (relationally), the circuit `R₁ a b ; R₂ b c` refines
`R a c` at the interface `{a, c}` (here `ext` maps `true ↦ a`, `false ↦ c`).
Instantiate `R₁, R₂, R` with delay channels to compose channels (bench B2). -/
theorem series {R₁ R₂ R : σ → σ → Prop} (a b c : W)
    (hR : ∀ x y z, R₁ x y → R₂ y z → R x z) :
    RefinesObs [Gate.rel1 R₁ a b, Gate.rel1 R₂ b c]
      (fun i : Bool => if i then a else c) (fun e => R (e true) (e false)) := by
  rintro e ⟨v, hv, rfl⟩
  exact hR _ _ _ (hv _ (List.mem_cons_self ..))
    (hv _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

end Refines

namespace RefinesObs

variable {W : Type u} {σ : Type v} {E : Type w}

theorem mono {c : Circuit W σ} {ext : E → W} {S S' : Spec E σ}
    (h : RefinesObs c ext S) (hS : ∀ e, S e → S' e) : RefinesObs c ext S' :=
  fun e he => hS e (h e he)

/-- Interface refinements compose: if `C1` refines `S1` at interface `x₁`
and `C2` refines `S2` at `x₂`, then the composition refines `S1 ∧ S2` at the
combined interface `E₁ ⊕ E₂` (all other wires hidden). -/
theorem compose {E₁ E₂ : Type w} {c₁ c₂ : Circuit W σ} {x₁ : E₁ → W}
    {x₂ : E₂ → W} {S₁ : Spec E₁ σ} {S₂ : Spec E₂ σ}
    (h₁ : RefinesObs c₁ x₁ S₁) (h₂ : RefinesObs c₂ x₂ S₂) :
    RefinesObs (List.append c₁ c₂) (fun i => Sum.elim x₁ x₂ i)
      (fun e => S₁ (e ∘ Sum.inl) ∧ S₂ (e ∘ Sum.inr)) := by
  rintro e ⟨v, hv, rfl⟩
  exact ⟨h₁ _ ⟨v, hv.left, rfl⟩, h₂ _ ⟨v, hv.right, rfl⟩⟩

/-- Hiding more wires: if a circuit refines `S` at interface `x`, and `y`
factors through `x` (`y = x ∘ p`), it refines the projected spec
`∃ e, S e ∧ e ∘ p = e'` at `y`. -/
theorem restrict {E' : Type w} {c : Circuit W σ} {x : E → W} {S : Spec E σ}
    (h : RefinesObs c x S) (p : E' → E) :
    RefinesObs c (x ∘ p) (fun e' => ∃ e, S e ∧ e ∘ p = e') := by
  rintro e' ⟨v, hv, rfl⟩
  exact ⟨v ∘ x, h _ ⟨v, hv, rfl⟩, rfl⟩

end RefinesObs

/-! ### Sanity example

Zero-delay Boolean gates over an arbitrary time domain `T` (signals
`T → Bool`): with `b` held at `true`, the output of `AND(a, b)` equals `a`.
This only illustrates the plumbing; the timed versions use delay-channel
relations for `σ`. -/

section Example

/-- Zero-delay AND as a gate relation on signals `T → Bool`. -/
def andZ {T : Type} : (T → Bool) → (T → Bool) → (T → Bool) → Prop :=
  fun x y z => ∀ t, z t = (x t && y t)

example {T : Type} :
    Refines [Gate.rel2 andZ (0 : Nat) 1 2]
      (fun v => (∀ t : T, v 1 t = true) → v 2 = v 0) := by
  intro v hv hb
  have h := hv _ (List.mem_cons_self ..)
  funext t
  simp only [Gate.rel2, andZ] at h
  rw [h t, hb t, Bool.and_true]

end Example

end Formal.Core
