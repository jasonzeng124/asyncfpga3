import Formal.Net.Ops

/-!
# Probe C-8l: `bd_src` as an Ops operator

`cells/rtl/bd_end.v`: `bd_src #(W, VAL)`: `req = LUT1(~ack)`, `data = VAL`. It is a
free-running four-phase source: it offers `VAL` again whenever its acknowledge is low. bdc
emits it for every `source` op. In gcd_hw these are the chains C-8i collapsed under
H_SOURCE_ETERNAL.

Gate model `Src z v`: H_LUT_SI (the inverter moves only to `¬ ack` of the previous tick,
unbounded inertial delay), `z.dat = v` at every tick (a constant bus), reset `req = 0`.
`src_op`: an operator with no inputs and the token equation `σ z k = v` for all k.
-/

namespace Formal.Net.Capstone
open Formal.Net Formal.Net.Handshake Formal.Net.Ops

structure Src (z : Chan) (v : Nat) : Prop where
  H_LUT_SI : ∀ t, z.req (t + 1) ≠ z.req t → z.req (t + 1) = !z.ack t
  dat : ∀ t, z.dat t = v
  iz : z.req 0 = false

variable {C : Type}

def srcEq (cz : C) (v : Nat) (σ : C → Nat → Nat) : Prop := ∀ k, σ cz k = v

theorem src_op (ch : C → Chan) (cz : C) (v : Nat) (S : Src (ch cz) v) :
    OpProto ch [] [cz] ∧ OpData ch [] [cz] (srcEq cz v) := by
  refine ⟨⟨fun t _ _ _ _ => ⟨fun c hc => absurd hc (List.not_mem_nil), fun c hc => ?_⟩,
    fun c hc => absurd hc (List.not_mem_nil), fun c hc => ?_⟩, ?_⟩
  · rw [List.mem_singleton.1 hc]
    intro hne
    have h := S.H_LUT_SI t hne
    revert hne h
    cases (ch cz).req t <;> cases (ch cz).req (t + 1) <;> cases (ch cz).ack t <;> simp
  · rw [List.mem_singleton.1 hc]; exact S.iz
  · intro _ _ c hc k r _ σ _ hE
    rw [List.mem_singleton.1 hc, hE k, S.dat]

end Formal.Net.Capstone
