import Formal.Core.Ternary

/-!
# Wip.Ternary — UNPROVED statements around ternary simulation (sorry allowed here)

Everything here is a statement with `sorry`, clearly marked. The proved part is
`Formal/Core/Ternary.lean`. Checked only for well-formedness (by concatenating
with the proved file in /tmp; this file is never built).
-/

namespace Formal.Core.Ternary.Wip

open Formal.Core.Ternary
open Formal.Core.Ternary.K3

variable {ι ν : Type}

/-! ## W1. Completeness (Brzozowski–Seger 1987 / Eichelberger)

Soundness (proved) says: binary in `resultA` ⇒ never changes. The converse
holds for the GMW model **with a delay element on every wire** ("wire-delay
expansion"), started from a stable state: `X` in `resultA` ⇒ some behaviour
changes the node. With ideal wires (our `Net` read literally) it is only
conservative: a LUT with pins `I0 = I1 = x` and table `I0 ∧ ¬I1` never glitches
if both pins see the same ideal wire, but `kext` treats the pins independently
and says `X` when `x` changes. (On silicon each LUT pin has its own input buffer
and route, so the wire-delay reading is the faithful one.) -/

/-- Wire-delay expansion of a LUT network: every LUT pin gets its own buffer node. -/
def wired (L : LutNet ι ν) : LutNet ι (ν ⊕ (Σ i : ν, Fin (L.arity i))) where
  arity
    | .inl i => L.arity i
    | .inr _ => 1
  pin
    | .inl i => fun p => .inr (.inr ⟨i, p⟩)
    | .inr ⟨i, p⟩ => fun _ => match L.pin i p with
        | .inl x => .inl x
        | .inr j => .inr (.inl j)
  tbl
    | .inl i => L.tbl i
    | .inr _ => fun x => x 0

/-- W1 (sorry): completeness of algorithm A for the wire-delay expansion, GMW
semantics, stable start. -/
theorem completeA_wired (L : LutNet ι ν) (l : List (ν ⊕ (Σ i : ν, Fin (L.arity i))))
    (hl : ∀ i, i ∈ l) (a b : ι → Bool) (s0 : ν ⊕ (Σ i : ν, Fin (L.arity i)) → Bool)
    (hstable : ∀ i, (wired L).toNet.fb a s0 i = s0 i)
    (i : ν ⊕ (Σ i : ν, Fin (L.arity i)))
    (hX : resultA (wired L).toNet l a b s0 i = X) :
    ∃ (σ : Nat → _ → Bool) (T : Nat), σ 0 = s0 ∧
      (∀ t, GStep (wired L).toNet b (σ t) (σ (t + 1))) ∧ σ T i ≠ s0 i := by
  sorry

/-- W1' (sorry): completeness of algorithm B (wire-delay expansion, GMW): a node
`X` in `resultB` can end in either value, or oscillate. -/
theorem completeB_wired (L : LutNet ι ν) (l : List (ν ⊕ (Σ i : ν, Fin (L.arity i))))
    (hl : ∀ i, i ∈ l) (a b : ι → Bool) (s0 : ν ⊕ (Σ i : ν, Fin (L.arity i)) → Bool)
    (hstable : ∀ i, (wired L).toNet.fb a s0 i = s0 i)
    (i : ν ⊕ (Σ i : ν, Fin (L.arity i)))
    (hX : resultB (wired L).toNet l a b s0 i = X) :
    ∀ v : Bool, ∃ (σ : Nat → _ → Bool), σ 0 = s0 ∧
      (∀ t, GStep (wired L).toNet b (σ t) (σ (t + 1))) ∧
      ∀ T, ∃ t, T ≤ t ∧ σ t i = v := by
  sorry

/-! ## W2. Settling under *unbounded* delay with fairness (no `D`)

`settleB` needs bounded staleness. In the pure GMW model with weak fairness
(every node fires infinitely often) the same argument gives "eventually". -/

/-- W2 (sorry; the proof is the `settleB` induction with rounds in place of `D`). -/
theorem settleB_fair (N : Net ι ν) (l : List ν) (hl : ∀ i, i ∈ l)
    (a b : ι → Bool) (s0 : ν → Bool) (σ : Nat → ν → Bool) (fire : Nat → ν → Bool)
    (hstep : ∀ t i, σ (t + 1) i = if fire t i then N.fb b (σ t) i else σ t i)
    (hfair : ∀ t i, ∃ t', t ≤ t' ∧ fire t' i = true) (h0 : σ 0 = s0)
    (i : ν) (v : Bool) (hv : resultB N l a b s0 i = ofBool v) :
    ∃ T, ∀ t, T ≤ t → σ t i = v := by
  sorry

/-! ## W3. A generic decision procedure for every cell

`bdc2_single_input_ok` is one `decide`. The generic version: for a one-LUT
feedback cell with `m` inputs, enumerate stable states and single-input flips,
run A and B, and return `true` iff every transition settles (B binary) and
every static transition (B = old value) is glitch-free (A binary). The
soundness theorem is `noGlitchA` + `settleResultB` per enumerated case. -/

/-- All Boolean vectors of length `m` (as `Fin m → Bool`). -/
def allVecs : (m : Nat) → List (Fin m → Bool)
  | 0 => [fun i => i.elim0]
  | m + 1 => (allVecs m).flatMap fun x => [vcons false x, vcons true x]

/-- W3 (sorry): `allVecs` is complete. -/
theorem mem_allVecs (m : Nat) (x : Fin m → Bool) : x ∈ allVecs m := by
  sorry

/-! ## W4. Inertial gates and `Stale`

An inertial channel after an ideal gate (Formal/Core/Delay/Inertial.lean) gives
`y u = (f ∘ x) τ` for some `τ ≤ u - Δ`: all inputs sampled at one past time, so
the behaviour is `Causal` (soundness applies unchanged). It is **not** `Stale`
in general: if `f ∘ x` keeps changing faster than the rejection window the
output holds an arbitrarily old value. W4: `Stale` holds from the time every
node's excitation has been constant for `ρ` — the bounded-inertial settling
statement. Not stated formally yet (needs the real-time trace bridge,
Formal/Core/Trace/Bridge.lean). -/

end Formal.Core.Ternary.Wip
