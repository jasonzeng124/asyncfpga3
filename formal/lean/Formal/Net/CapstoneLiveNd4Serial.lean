/-!
# Probe C-8z4 (1): simultaneous gate firings serialize when disabling is acyclic

Generic, core Lean only. A gate system on `N` bits: gate `i` writes bit `i`, and
`ex i v s` says gate `i` is excited toward `v` in state `s`. The *interleaving* semantics fires
one excited gate per step (`Step`, `Reach`).

The timed models of the gcd_hw proofs (8u/8z/8z2) change several gate outputs in one tick.
`serial` gives a sufficient condition for one timed tick `s → s'` to be reproduced by single
firings: every changed bit `i` is excited toward `s' i` in every intermediate state in which
no changed bit that may *disable* it (`Dis j i`) has already fired, and `Dis` restricted to the
changed bits is ranked (`Dis j i → r i < r j`, i.e. acyclic). Then `Reach ex s s'`: fire the
changed bits in increasing rank.

`trace_reach` iterates it along a trace: a timed run all of whose ticks satisfy the condition
visits only interleaving-reachable states. So a deadlock-freedom fact about the interleaving
system (e.g. an exhaustive search, C-8z4's `Wip/C8z4/explore.py`) transfers to the timed run.

Why `Dis` and a rank: in gcd_hw, 8z3 proved every gate persistent except (a) the mux input
acknowledges, whose falling excitation is withdrawn only by `z_ack` rising (fire the
acknowledge first: `Dis z_ack x_ack`), and (b) contested arbiter grants (never contested,
8r/8s). This file does NOT instantiate the condition for gcd_hw (see the note).
-/

namespace Formal.Net.CapNet.Live.Nd4

variable {N : Nat}

/-- Update one bit. -/
def upd (s : Fin N → Bool) (i : Fin N) (v : Bool) : Fin N → Bool :=
  fun j => if j = i then v else s j

/-- One interleaving step: one excited gate takes its target value. -/
def Step (ex : Fin N → Bool → (Fin N → Bool) → Prop) (s s' : Fin N → Bool) : Prop :=
  ∃ i, ex i (!s i) s ∧ s' = upd s i (!s i)

/-- Interleaving reachability. -/
inductive Reach (ex : Fin N → Bool → (Fin N → Bool) → Prop) : (Fin N → Bool) → (Fin N → Bool) → Prop
  | refl (s) : Reach ex s s
  | head {s u w} : Step ex s u → Reach ex u w → Reach ex s w

theorem Reach.trans {ex : Fin N → Bool → (Fin N → Bool) → Prop} {s u w : Fin N → Bool}
    (h1 : Reach ex s u) (h2 : Reach ex u w) : Reach ex s w := by
  induction h1 with
  | refl => exact h2
  | head hs _ ih => exact Reach.head hs (ih h2)

/-- The state between `s` and `s'` in which exactly the bits outside `L` show `s'`. -/
def mixL (s s' : Fin N → Bool) (L : List (Fin N)) : Fin N → Bool :=
  fun j => if j ∈ L then s j else s' j

/-- A minimal-rank element of a nonempty list. -/
theorem exists_min (r : Fin N → Nat) : ∀ (b : Nat) (L : List (Fin N)),
    (∃ i ∈ L, r i ≤ b) → ∃ i ∈ L, ∀ j ∈ L, r i ≤ r j
  | 0, L, ⟨i, hi, hr⟩ => ⟨i, hi, fun j _ => by omega⟩
  | b + 1, L, ⟨i, hi, hr⟩ => by
    by_cases h : ∃ k ∈ L, r k ≤ b
    · exact exists_min r b L h
    · refine ⟨i, hi, fun j hj => ?_⟩
      have : ¬ r j ≤ b := fun hjb => h ⟨j, hj, hjb⟩
      omega

/-- **Serialization of one timed tick.** -/
theorem serial (ex : Fin N → Bool → (Fin N → Bool) → Prop) (s s' : Fin N → Bool)
    (Dis : Fin N → Fin N → Prop) (r : Fin N → Nat)
    (hrank : ∀ i j, s i ≠ s' i → s j ≠ s' j → Dis j i → r i < r j)
    (hex : ∀ (L : List (Fin N)) (i : Fin N), s i ≠ s' i → i ∈ L →
      (∀ j, j ∉ L → s j ≠ s' j → ¬ Dis j i) → ex i (s' i) (mixL s s' L)) :
    Reach ex s s' := by
  -- generalized claim, by induction on the length of the pending list
  have key : ∀ (n : Nat) (L : List (Fin N)), L.length ≤ n →
      (∀ j ∈ L, s j ≠ s' j) →
      (∀ i ∈ L, ∀ j, j ∉ L → s j ≠ s' j → ¬ Dis j i) →
      Reach ex (mixL s s' L) s' := by
    intro n
    induction n with
    | zero =>
      intro L hl _ _
      have : L = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this
      have : mixL s s' [] = s' := by funext j; simp [mixL]
      rw [this]; exact Reach.refl _
    | succ n ih =>
      intro L hl hch hcl
      cases L with
      | nil =>
        have : mixL s s' [] = s' := by funext j; simp [mixL]
        rw [this]; exact Reach.refl _
      | cons a L0 =>
        obtain ⟨i, hi, hmin⟩ := exists_min r (r a) (a :: L0) ⟨a, List.mem_cons_self, Nat.le_refl _⟩
        let L' := (a :: L0).filter (fun j => decide (j ≠ i))
        have hmem' : ∀ j, j ∈ L' ↔ j ∈ a :: L0 ∧ j ≠ i := by
          intro j; simp [L']
        have hlen : L'.length ≤ n := by
          have h1 : L'.length < (a :: L0).length := by
            apply List.length_filter_lt_length_iff_exists.mpr
            exact ⟨i, hi, by simp⟩
          omega
        have hci := hch i hi
        -- the step fires `i`
        have hstep : Step ex (mixL s s' (a :: L0)) (mixL s s' L') := by
          refine ⟨i, ?_, ?_⟩
          · have hv : (!mixL s s' (a :: L0) i) = s' i := by
              simp only [mixL, if_pos hi]
              cases h1 : s i <;> cases h2 : s' i <;> simp_all
            rw [hv]
            exact hex (a :: L0) i hci hi (hcl i hi)
          · funext j
            simp only [upd, mixL]
            by_cases hj : j = i
            · subst hj
              have : ¬ j ∈ L' := fun h => ((hmem' j).mp h).2 rfl
              simp only [if_neg this, if_pos hi, if_true]
              cases h1 : s j <;> cases h2 : s' j <;> simp_all
            · simp only [if_neg hj]
              by_cases hjm : j ∈ a :: L0
              · have : j ∈ L' := (hmem' j).mpr ⟨hjm, hj⟩
                simp only [if_pos this, if_pos hjm]
              · have : ¬ j ∈ L' := fun h => hjm ((hmem' j).mp h).1
                simp only [if_neg this, if_neg hjm]
        refine Reach.head hstep (ih L' hlen ?_ ?_)
        · intro j hj; exact hch j ((hmem' j).mp hj).1
        · intro i2 hi2 j hj hcj hd
          have hi2' := (hmem' i2).mp hi2
          by_cases hji : j = i
          · subst hji
            have := hrank i2 j (hch i2 hi2'.1) hcj hd
            have := hmin i2 hi2'.1
            omega
          · have hjL : j ∉ a :: L0 := fun h => hj ((hmem' j).mpr ⟨h, hji⟩)
            exact hcl i2 hi2'.1 j hjL hcj hd
  let L := (List.finRange N).filter (fun j => decide (s j ≠ s' j))
  have hL : ∀ j, j ∈ L ↔ s j ≠ s' j := by intro j; simp [L, List.mem_finRange]
  have h0 : mixL s s' L = s := by
    funext j; simp only [mixL]
    by_cases h : j ∈ L
    · rw [if_pos h]
    · rw [if_neg h]
      exact Classical.byContradiction fun hn => h ((hL j).mpr (Ne.symm hn))
  have := key L.length L (Nat.le_refl _) (fun j hj => (hL j).mp hj)
    (fun i _ j hj hc _ => hj ((hL j).mpr hc))
  rw [h0] at this; exact this

/-- The serialization condition for one tick of a trace. -/
def SerOK (ex : Fin N → Bool → (Fin N → Bool) → Prop) (s s' : Fin N → Bool) : Prop :=
  ∃ (Dis : Fin N → Fin N → Prop) (r : Fin N → Nat),
    (∀ i j, s i ≠ s' i → s j ≠ s' j → Dis j i → r i < r j) ∧
    (∀ (L : List (Fin N)) (i : Fin N), s i ≠ s' i → i ∈ L →
      (∀ j, j ∉ L → s j ≠ s' j → ¬ Dis j i) → ex i (s' i) (mixL s s' L))

/-- **A timed trace whose every tick serializes stays in the interleaving-reachable set.** -/
theorem trace_reach (ex : Fin N → Bool → (Fin N → Bool) → Prop) (S : Nat → Fin N → Bool)
    (h : ∀ t, SerOK ex (S t) (S (t + 1))) : ∀ t, Reach ex (S 0) (S t) := by
  intro t
  induction t with
  | zero => exact Reach.refl _
  | succ t ih =>
    obtain ⟨Dis, r, hr, hx⟩ := h t
    exact ih.trans (serial ex (S t) (S (t + 1)) Dis r hr hx)

/-- Deadlock transfer: if no interleaving-reachable state is dead before the goal, the same
holds along every serializable timed trace. -/
theorem trace_nodead (ex : Fin N → Bool → (Fin N → Bool) → Prop) (S : Nat → Fin N → Bool)
    (Goal Dead : (Fin N → Bool) → Prop)
    (H_INTERLEAVE : ∀ u, Reach ex (S 0) u → ¬ Goal u → ¬ Dead u)
    (h : ∀ t, SerOK ex (S t) (S (t + 1))) : ∀ t, ¬ Goal (S t) → ¬ Dead (S t) :=
  fun t hg => H_INTERLEAVE (S t) (trace_reach ex S h t) hg

/-! ## Sanity: the condition has content -/

/-- Two gates that disable each other (a contested arbiter: each grant's rise needs the other
grant low) do not serialize when both fire in one tick: the state `11` is not reachable from
`00` in the interleaving semantics. So the rank hypothesis of `serial` cannot be dropped. -/
def arbEx : Fin 2 → Bool → (Fin 2 → Bool) → Prop :=
  fun i v s => v = true ∧ s (1 - i) = false ∨ v = false

theorem arb_not_reach : ¬ Reach arbEx (fun _ => false) (fun _ => true) := by
  -- invariant: never both bits true
  have inv : ∀ s u, Reach arbEx s u → ¬ (s 0 = true ∧ s 1 = true) → ¬ (u 0 = true ∧ u 1 = true) := by
    intro s u h
    induction h with
    | refl => exact id
    | head hs _ ih =>
      intro hn
      apply ih
      obtain ⟨i, he, rfl⟩ := hs
      rename_i s0 _ _
      intro ⟨h0, h1⟩
      apply hn
      revert he h0 h1
      have hi : i = 0 ∨ i = 1 := by omega
      rcases hi with rfl | rfl <;>
        cases e0 : s0 0 <;> cases e1 : s0 1 <;> simp [arbEx, upd, e0, e1]
  intro h
  exact inv _ _ h (by simp) (by simp)

end Formal.Net.CapNet.Live.Nd4
