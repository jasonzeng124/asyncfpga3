import Formal.Net.OpsCM

/-!
# Probe C-8l: the control_merge equation restricted to offered tokens (the O1 interface)

`CM.amerge_op`'s token equation is relative to `winner (ch z)`, the circuit's own index bits,
and it must hold for EVERY index `k`. For a token `k` the circuit never offers, `winner` is
`false` by definition. One invocation offers finitely many tokens, so a solution built from the
token run (periodic labels, O2) can never satisfy it: a hypothesis "the circuit's winners equal
the token labels for all k" would be FALSE for every real circuit, and a theorem resting on it
would be vacuous.

`amerge_op_forced` fixes the interface:
* the equation `amergeOff` constrains only the tokens the circuit offers;
* the oracle is any fixed stream `ω` (meant: the token run's labels);
* the premise H_CM_FORCED says the circuit's winner of every OFFERED token is `ω`. That is
  satisfiable, and it is exactly obligation O1 (C-8l notes).

It is derived from `amerge_op` as a black box: a stream that satisfies the restricted equation
is patched on the never-offered output indices into one that satisfies the full equation.
-/

namespace Formal.Net.Capstone
open Formal.Net Formal.Net.Handshake Formal.Net.Ops
open Formal.Net.Ops.CM (AMerge winner amergeEq amerge_op cnt_congr_lt cnt_ge_aux)

variable {C : Type}

/-- The merge's equation at one index. -/
def amergeAt (ω : Nat → Bool) (cx cy cz : C) (σ : C → Nat → Nat) (k : Nat) : Prop :=
  σ cz k = 2 * (if ω k then σ cy (cnt ω k) else σ cx (cnt (fun i => !ω i) k)) +
    Formal.Net.Ops.Mux.b2n (ω k)

/-- The merge's equation on the tokens the circuit offers on `z` only. -/
def amergeOff (z : Chan) (ω : Nat → Bool) (cx cy cz : C) (σ : C → Nat → Nat) : Prop :=
  ∀ k, (∃ r, OffAt z k r) → amergeAt ω cx cy cz σ k

/-- Offers are sequential: if token `k` is offered, every earlier token is. -/
theorem offered_below {c : Chan} {k r : Nat} (h : OffAt c k r) {i : Nat} (hi : i < k) :
    ∃ r', OffAt c i r' := by
  obtain ⟨e, _, hf, hc⟩ := cnt_ge_aux (riseB c.req) r i (by rw [h.2]; omega)
  exact ⟨e, hf, hc⟩

theorem amergeAt_congr {ω ω' : Nat → Bool} {cx cy cz : C} {σ : C → Nat → Nat} {k : Nat}
    (h : ∀ i, i ≤ k → ω i = ω' i) : amergeAt ω cx cy cz σ k ↔ amergeAt ω' cx cy cz σ k := by
  have c1 : cnt ω k = cnt ω' k := cnt_congr_lt k (fun i hi => h i (by omega))
  have c0 : cnt (fun i => !ω i) k = cnt (fun i => !ω' i) k :=
    cnt_congr_lt k (fun i hi => by rw [h i (by omega)])
  unfold amergeAt; rw [c1, c0, h k (Nat.le_refl _)]

/-- `amerge_op` with the oracle fixed in advance and the equation restricted to offered
tokens, under H_CM_FORCED (the circuit's winner of every offered token is `ω`). -/
theorem amerge_op_forced [DecidableEq C] (ch : C → Chan) (cx cy cz : C) (g1 g2 : Trace)
    (M : AMerge (ch cx) (ch cy) (ch cz) g1 g2) (hx : cx ≠ cz) (hy : cy ≠ cz)
    (ω : Nat → Bool)
    (H_CM_FORCED : ∀ k r, OffAt (ch cz) k r → winner (ch cz) k = ω k) :
    OpProto ch [cx, cy] [cz] ∧ OpData ch [cx, cy] [cz] (amergeOff (ch cz) ω cx cy cz) := by
  classical
  obtain ⟨hp, hd⟩ := amerge_op ch cx cy cz g1 g2 M
  refine ⟨hp, ?_⟩
  intro hin hout c hc k r hoff σ hag hE
  have hcz : c = cz := List.mem_singleton.1 hc
  subst hcz
  let W := winner (ch c)
  let Off : Nat → Prop := fun i => ∃ r, OffAt (ch c) i r
  let σ' : C → Nat → Nat := fun c' i =>
    if c' = c ∧ ¬ Off i then
      2 * (if W i then σ cy (cnt W i) else σ cx (cnt (fun j => !W j) i)) +
        Formal.Net.Ops.Mux.b2n (W i)
    else σ c' i
  have hsx : ∀ i, σ' cx i = σ cx i := by intro i; simp [σ', hx]
  have hsy : ∀ i, σ' cy i = σ cy i := by intro i; simp [σ', hy]
  have hsz : ∀ i, Off i → σ' c i = σ c i := by intro i hi; simp [σ', hi]
  -- the forcing, on every index up to an offered one
  have hforce : ∀ i, Off i → ∀ j, j ≤ i → W j = ω j := by
    intro i ⟨ri, hri⟩ j hj
    rcases Nat.lt_or_ge j i with hlt | hge
    · obtain ⟨rj, hrj⟩ := offered_below hri hlt
      exact H_CM_FORCED j rj hrj
    · have : j = i := by omega
      subst this; exact H_CM_FORCED j ri hri
  have hE' : amergeEq W cx cy c σ' := by
    intro i
    by_cases ho : Off i
    · have h1 := (amergeAt_congr (cx := cx) (cy := cy) (cz := c) (σ := σ) (hforce i ho)).2 (hE i ho)
      unfold amergeAt at h1
      rw [hsz i ho, hsx, hsy, h1]
    · show σ' c i = _
      simp only [σ', ho, not_false_eq_true, and_self, ite_true, hsx, hsy]
  have hag' : Agree ch σ' r := by
    intro c' i r' hr' ho'
    by_cases hc' : c' = c
    · subst hc'; rw [hsz i ⟨r', ho'⟩]; exact hag _ i r' hr' ho'
    · have : σ' c' i = σ c' i := by simp [σ', hc']
      rw [this]; exact hag c' i r' hr' ho'
  have := hd hin hout c (List.mem_singleton_self _) k r hoff σ' hag' hE'
  rw [← hsz k ⟨r, hoff⟩]; exact this

/-- A total solution of the full equation with the oracle `ω` (what O2 provides) satisfies
the restricted one. -/
theorem amergeOff_of_eq (z : Chan) (ω : Nat → Bool) (cx cy cz : C) (σ : C → Nat → Nat)
    (h : amergeEq ω cx cy cz σ) : amergeOff z ω cx cy cz σ := fun k _ => h k

end Formal.Net.Capstone
