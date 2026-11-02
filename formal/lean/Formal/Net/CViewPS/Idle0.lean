import Formal.Net.CViewPS.IslandPS

/-!
# THE theorem's conclusion for zero pairs (shard C)

**Problem, plainly.** `Spec.Correct` is THE theorem's conclusion. Its simplest instance: the
environment offers no pair at all (`n = some 0`). Then the circuit must keep every handshake
output low after reset, and the boundary must end idle.

**Proved** (`correct_n0`): for every delay parameter `p` with `0 ≤ κ ≤ 1`, `0 < g`, and reset length
`R`, margins `su`, `Δo`: if the island's delay conditions hold for some `M`, `A` (every island
member's start and every storage member's reset arrival at most `A`, island pin delays at most `M`,
forcing pins at least 1 ps, and `A + 87·M + 1 ≤ R`), then every behaviour of THE theorem's circuit
(the decoded gcd_ps netlist, `Spec.circuit DecodedPS.net DecodedPS.boundary`) with an environment
obeying `Spec.Env` for `n = some 0` satisfies `Spec.Correct` for `n = some 0`. No arbiter
hypothesis (H_ARB) and no sequential-env hypothesis are used. Standard axioms only.

**Not shown.** `n ≥ 1` (the real theorem); the delay conditions for a concrete `p` (bounds over
the island's 414 gates, decidable for a given `p`).
-/

namespace Formal.Net.CViewPS
open Formal.Target Formal.Target.DecodedPS Formal.Timing.SpecSettle Formal.Timing.SpecChain
  Formal.Timing.SpecChainM Formal.Timing.ChunkCM Formal.Timing.Huffman Formal.Timing.SpecLoop
  Formal.Timing.Island

theorem bnd_facts : boundary.rst = 186905 ∧ boundary.a.req = 186985 ∧ boundary.b.req = 186985 ∧
    boundary.start.req = 186985 ∧ boundary.a.ack = 104576 ∧ boundary.b.ack = 104695 ∧
    boundary.start.ack = 147972 ∧ boundary.out0.req = 160957 ∧ boundary.out0.ack = 154859 ∧
    boundary.pend.req = 186985 ∧ boundary.pend.ack = 104477 ∧ rstPS = 186905 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem rises_zero (s : Sig) (R : Nat) (h : ∀ t, R ≤ t → s t = false) : ∀ t, rises s R t = 0
  | 0 => rfl
  | t + 1 => by
    simp only [rises, rises_zero s R h t, Nat.zero_add]
    split
    · rename_i hc; have := h (t + 1) (by omega); rw [this] at hc; simp at hc
    · rfl

/-- An acknowledge the environment holds low until `R` and moves only when it differs from its
request stays low while the request does. -/
theorem ack_low (r a : Sig) (R : Nat) (h0 : ∀ t, t ≤ R → a t = false) (hm : AckMoves r a R)
    (hr : ∀ t, R ≤ t → r t = false) : ∀ t, a t = false := by
  intro t
  induction t with
  | zero => exact h0 0 (Nat.zero_le _)
  | succ t ih =>
    by_cases ht : t + 1 ≤ R
    · exact h0 _ ht
    · by_contra hne
      have := hm t (by omega) (by rw [ih]; exact hne)
      rw [ih, hr t (by omega)] at this; exact this rfl

theorem req_low {x : Beh} {ch : InCh} {R su : Nat} {vals : Nat → Nat} (h : EnvIn x ch R su (some 0) vals) :
    ∀ t, x ch.req t = false := by
  intro t
  obtain ⟨h0, -, -, h4, -⟩ := h
  by_cases ht : t ≤ R
  · exact h0 t ht
  · cases hv : x ch.req t
    · rfl
    · have := h4 t (by omega) hv; simp [Offered] at this

/-- **`Correct` for zero pairs, on THE target.** -/
theorem correct_n0 {p : DelayPar} (hp : Sane p) (R su Δo M A : Nat)
    (hS : ∀ w, memI w = true → startPS p w ≤ A)
    (hM : ∀ w, memI w = true → ∀ i, i < (gAt cs 2500 w).k → sumMax p (arcsPS w i) ≤ M)
    (hmin : ∀ w, memI w = true → ∀ j ∈ psI w, 1 ≤ sumMin p (arcsPS w j))
    (hrs : ∀ r ∈ resetList, memI r.1 = true → sumMax p (arcsPS r.1 r.2.1) ≤ A)
    (hRA : A + 87 * M + 1 ≤ R) :
    ∀ (x : Beh) (va vb : Nat → Nat), Behaves p (circuit net boundary) x →
      Env x boundary R su Δo (some 0) va vb → Correct x boundary R Δo (some 0) va vb := by
  intro x va vb hb henv
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩ := bnd_facts
  obtain ⟨hrst, -, -, hEa, hEb, hEs, hEo, hEp⟩ := henv
  have hreq : ∀ t, x 186985 t = false := by rw [← b2]; exact req_low hEa
  have hR0 : 0 < R := by omega
  have hpa : ∀ t, x 104477 t = false := by
    rw [← b11]
    obtain ⟨h0, hm, -, -⟩ := hEp
    exact ack_low _ _ R h0 hm (fun t _ => by rw [b10]; exact hreq t)
  obtain ⟨c, -, -, hisl⟩ := island_PS hp hb
  have hI := hisl R M A (fun t ht => by rw [b12, ← b1]; exact hrst t ht) hR0 hreq hpa hS hM hmin hrs (by omega)
  have mem4 : memI 104576 = true ∧ memI 104695 = true ∧ memI 147972 = true ∧ memI 160957 = true := by
    decide +kernel
  have low : ∀ w, memI w = true → ∀ t, R ≤ t → x w t = false := fun w hw t ht => hI w hw t (by omega)
  have haA := low _ mem4.1
  have hbA := low _ mem4.2.1
  have hsA := low _ mem4.2.2.1
  have hoR := low _ mem4.2.2.2
  have hoA : ∀ t, x 154859 t = false := by
    rw [← b9]
    obtain ⟨h0, hm, -, -⟩ := hEo
    exact ack_low _ _ R h0 hm (fun t ht => by rw [b8]; exact hoR t ht)
  -- input channels: the acknowledge never moves from R on
  have cin : ∀ (ch : InCh), ch.req = 186985 → (∀ t, R ≤ t → x ch.ack t = false) → CircIn x ch R := by
    intro ch hq ha
    refine ⟨ha R (le_refl _), fun t ht hne => ?_, fun t ht hne => ?_⟩
    · exact absurd (by rw [ha t ht, ha (t + 1) (by omega)]) hne
    · exact absurd (by rw [ha t ht, hq, hreq]) hne
  have cout : ∀ (ch : OutCh), (∀ t, R ≤ t → x ch.req t = false) → CircOut x ch R (some 0) := by
    intro ch hq
    refine ⟨hq R (le_refl _), fun t ht hne => ?_, fun t ht _ hc => ?_, fun t ht hr => ?_⟩
    · exact absurd (by rw [hq t ht, hq (t + 1) (by omega)]) hne
    · rcases hc with hc | hc
      · rw [hq t ht] at hc; cases hc
      · simp [Offered] at hc
    · rw [hq t ht] at hr; cases hr
  refine ⟨cin _ b2 (by rw [b5]; exact haA), cin _ b3 (by rw [b6]; exact hbA),
    cin _ b4 (by rw [b7]; exact hsA), cout _ (by rw [b8]; exact hoR),
    cout _ (fun t _ => by rw [b10]; exact hreq t), ?_, ?_⟩
  · intro t0 t ht0 h1 h2
    rw [b8, hoR (t0 + 1) (by omega)] at h2; cases h2
  · intro m hm
    simp only [Option.some.injEq] at hm; subst hm
    refine ⟨R, fun t ht => ⟨?_, ?_, ?_⟩⟩
    · intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rw [b2, b3, b4, b5, b6, b7, b8, b9, b10, b11] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hreq t
      · exact haA t ht
      · exact hreq t
      · exact hbA t ht
      · exact hreq t
      · exact hsA t ht
      · exact hoR t ht
      · exact hoA t
      · exact hreq t
      · exact hpa t
    · rw [b8]; exact rises_zero _ R hoR t
    · rw [b10]; exact rises_zero _ R (fun t _ => hreq t) t

end Formal.Net.CViewPS
