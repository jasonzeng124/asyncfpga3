import Formal.Cells.ContractsTrunc

/-!
# Probe G1, part 4: the timed C-element in prefix form

Shard B, Phase 3. Notes: `formal/notes/B-contracts-trunc.md`.

The mux, the 3-way mux, the merge's acknowledge side, the joins and the link
controllers of B's timed theorems are all built on one primitive:
`OpsTimedMux.cel_run`, the four-phase run of a gated C-element (a feedback LUT
whose REAL INIT is proved `~rst · C(a, b)`, a FIFO LUT arc, a window feedback
wire). Its statement is whole-run (`Tok` inputs for all time ⇒ `Tok`
excitation for all time). This file restates it on prefixes:

* `cel_runN`: inputs `TokN T N` and the input latency (H_ENV_LATENCY,
  `hdep`) for the input edges that have happened by `N` ⇒ the excitation is a
  `TokN 0 N` on `max (ea j) (eb j)`, gate `ga k && gb k`;
* `cel_nodeN`: the node, through the LUT's FIFO arc, up to `N + L.lo`.

The excitation at `t` reads the inputs at `t` and the node's own feedback
(strictly earlier, `H_LOOP_POS`), so nothing after `N` is used; the causal
delay of the cell is the LUT arc's `L.lo` (and then its output wires). This
is the building block for the mux / muxn3 / link prefix theorems, which are
NOT done here (see the notes).
-/

namespace Formal.Cells.Contracts
open Formal.Net (Trace)
open Formal.Cells.PipeTimed (Ret Vph)
open Formal.Cells.OpsTimed (CEl exc_hold)

namespace TokN
variable {T N : Nat} {x : Trace} {e : Nat → Nat} {g : Nat → Bool}

/-- Value of a prefix in phase `j`. -/
theorem at_phase (h : TokN T N x e g) (j t : Nat) (hT : T ≤ t) (hN : t ≤ N) (h1 : e j ≤ t)
    (h2 : t < e (j + 1)) : x t = (Vph j && g (j / 2)) := by
  rcases Nat.mod_two_eq_zero_or_one j with hj | hj
  · have ej : j = 2 * (j / 2) := by omega
    have hv : Vph j = true := by show decide (j % 2 = 0) = true; simp [hj]
    rw [hv, Bool.true_and]
    exact h.hi (j / 2) t hT hN (by rw [← ej]; exact h1)
      (by rw [show 2 * (j / 2) + 1 = j + 1 by omega]; exact h2)
  · have hv : Vph j = false := by show decide (j % 2 = 0) = false; simp [hj]
    rw [hv, Bool.false_and]
    exact h.lo (j / 2) t hT hN (by rw [show 2 * (j / 2) + 1 = j by omega]; exact h1)
      (by rw [show 2 * (j / 2) + 2 = j + 1 by omega]; exact h2)

end TokN

section cel
variable {a b rst O qp ex : Trace} {L : Ret} {wl wh : Nat}

/-- **Four-phase run of a gated C-element, prefix form** (`cel_run` on
`[0, N]`). The reset is released at `R` (`rst` high before, low on
`[R, N]`); every input edge that has happened by `N` departs at least
`L.hi + wh` after the phase start (H_ENV_LATENCY, `hdep`, only for edges
`≤ N`); the first edges, if they have happened by `N`, are after `R`. -/
theorem cel_runN (C : CEl a b rst O qp ex L wl wh) {T R N : Nat} {ea eb : Nat → Nat}
    {ga gb : Nat → Bool} (ha : TokN T N a ea ga) (hb : TokN T N b eb gb)
    (hrh : ∀ t, t < R → rst t = true) (hrl : ∀ t, R ≤ t → t ≤ N → rst t = false)
    (hT : T ≤ R) (hR : L.hi + wh ≤ R) (hRa : ea 0 ≤ N → R ≤ ea 0) (hRb : eb 0 ≤ N → R ≤ eb 0)
    (hdep : ∀ j, (ea (j + 1) ≤ N → max (ea j) (eb j) + L.hi + wh ≤ ea (j + 1)) ∧
      (eb (j + 1) ≤ N → max (ea j) (eb j) + L.hi + wh ≤ eb (j + 1))) :
    TokN 0 N ex (fun j => max (ea j) (eb j)) (fun k => ga k && gb k) := by
  have cR : ∀ j, max (ea j) (eb j) ≤ N → R ≤ max (ea j) (eb j) := by
    intro j
    induction j with
    | zero => intro h; have := hRa (by omega); have := hRb (by omega); omega
    | succ j ih =>
      intro h
      have := (hdep j).1 (by omega)
      have := ih (by omega)
      omega
  have hpre : ∀ s, s < max (ea 0) (eb 0) → s ≤ N → ex s = false := by
    intro s h1 h2
    exact exc_hold C false 0 R (min (max (ea 0) (eb 0)) (N + 1))
      (fun s _ h => by rw [C.H_EX, hrh s h]; rfl)
      (fun s h1 h2 => ⟨hrl s h1 (by omega), Or.inr ⟨by
        by_cases h3 : s < ea 0
        · exact Or.inl (ha.pre s (by omega) (by omega) h3)
        · exact Or.inr (hb.pre s (by omega) (by omega) (by omega)), by omega⟩⟩) s
      (Nat.zero_le _) (by omega)
  have step : ∀ j c', max (ea j) (eb j) ≤ N → c' + L.hi + wh ≤ max (ea j) (eb j) →
      (j % 2 = 0 → ∀ s, c' ≤ s → s < max (ea j) (eb j) → ex s = false) →
      ∀ s, max (ea j) (eb j) ≤ s → s < max (ea (j + 1)) (eb (j + 1)) → s ≤ N →
        ex s = (Vph j && (ga (j / 2) && gb (j / 2))) := by
    intro j c' hjN hc' hprev
    have d1 := hdep j; have d2 := hdep (j + 1)
    have cRj := cR j hjN
    have va : ∀ s, max (ea j) (eb j) ≤ s → s < max (ea (j + 1)) (eb (j + 1)) → s ≤ N →
        (s < ea (j + 1) → a s = (Vph j && ga (j / 2))) ∧
        (ea (j + 1) ≤ s → a s = (Vph (j + 1) && ga ((j + 1) / 2))) := fun s h1 h2 hN =>
      ⟨fun h3 => ha.at_phase j s (by omega) hN (by omega) h3,
        fun h3 => ha.at_phase (j + 1) s (by omega) hN h3 (by omega)⟩
    have vb : ∀ s, max (ea j) (eb j) ≤ s → s < max (ea (j + 1)) (eb (j + 1)) → s ≤ N →
        (s < eb (j + 1) → b s = (Vph j && gb (j / 2))) ∧
        (eb (j + 1) ≤ s → b s = (Vph (j + 1) && gb ((j + 1) / 2))) := fun s h1 h2 hN =>
      ⟨fun h3 => hb.at_phase j s (by omega) hN (by omega) h3,
        fun h3 => hb.at_phase (j + 1) s (by omega) hN h3 (by omega)⟩
    by_cases hA : (Vph j && ga (j / 2)) = (Vph j && (ga (j / 2) && gb (j / 2))) ∧
        (Vph j && gb (j / 2)) = (Vph j && (ga (j / 2) && gb (j / 2)))
    · intro s0 h01 h02 h0N
      exact exc_hold C _ (max (ea j) (eb j)) (max (ea j) (eb j))
        (min (max (ea (j + 1)) (eb (j + 1))) (N + 1)) (fun s h1 h2 => by omega)
        (fun s h1 h2 => ⟨hrl s (by omega) (by omega), by
          have h2' : s < max (ea (j + 1)) (eb (j + 1)) := by omega
          have hN : s ≤ N := by omega
          by_cases e1 : s < ea (j + 1)
          · by_cases e2 : s < eb (j + 1)
            · exact Or.inl ⟨((va s h1 h2' hN).1 e1).trans hA.1, ((vb s h1 h2' hN).1 e2).trans hA.2⟩
            · exact Or.inr ⟨Or.inl (((va s h1 h2' hN).1 e1).trans hA.1), by omega⟩
          · have e2 : s < eb (j + 1) := by omega
            exact Or.inr ⟨Or.inr (((vb s h1 h2' hN).1 e2).trans hA.2), by omega⟩⟩) s0 h01 (by omega)
    · have hj : j % 2 = 0 := by
        apply Classical.byContradiction; intro hn
        have : Vph j = false := by show decide (j % 2 = 0) = false; simp; omega
        rw [this] at hA; simp at hA
      have hV : Vph j = true := by show decide (j % 2 = 0) = true; simp; omega
      have hV1 : Vph (j + 1) = false := by show decide ((j + 1) % 2 = 0) = false; simp; omega
      rw [hV] at hA ⊢
      have hlow : ∀ s, max (ea j) (eb j) ≤ s → s < max (ea (j + 1)) (eb (j + 1)) → s ≤ N →
          a s = false ∨ b s = false := by
        intro s h1 h2 hN
        cases hga : ga (j / 2) <;> cases hgb : gb (j / 2) <;> rw [hga, hgb] at hA <;> simp at hA
        · by_cases e1 : s < ea (j + 1)
          · left; rw [(va s h1 h2 hN).1 e1, hV, hga]; rfl
          · left; rw [(va s h1 h2 hN).2 (by omega), hV1]; rfl
        · by_cases e1 : s < eb (j + 1)
          · right; rw [(vb s h1 h2 hN).1 e1, hV, hgb]; rfl
          · right; rw [(vb s h1 h2 hN).2 (by omega), hV1]; rfl
      have htg : (true && (ga (j / 2) && gb (j / 2))) = false := by
        cases hga : ga (j / 2) <;> cases hgb : gb (j / 2) <;> rw [hga, hgb] at hA <;> simp at hA
          <;> rfl
      rw [htg]
      intro s h1 h2 hN
      exact exc_hold C false c' (max (ea j) (eb j)) (min (max (ea (j + 1)) (eb (j + 1))) (N + 1))
        (hprev hj)
        (fun s h1 h2 => ⟨hrl s (by omega) (by omega), Or.inr ⟨by
          rcases hlow s h1 (by omega) (by omega) with h | h
          · exact Or.inl h
          · exact Or.inr h, by omega⟩⟩) s (by omega) (by omega)
  have phase : ∀ j s, max (ea j) (eb j) ≤ s → s < max (ea (j + 1)) (eb (j + 1)) → s ≤ N →
      ex s = (Vph j && (ga (j / 2) && gb (j / 2))) := by
    intro j
    induction j with
    | zero =>
      intro s h1 h2 hN
      exact step 0 0 (by omega) (by have := cR 0 (by omega); omega)
        (fun _ s _ h => hpre s h (by omega)) s h1 h2 hN
    | succ j ih =>
      intro s h1 h2 hN
      exact step (j + 1) (max (ea j) (eb j)) (by omega)
        (by have := (hdep j).1 (by omega); omega) (fun hj s' h1' h2' => by
          have hjN : max (ea j) (eb j) ≤ N := by have := (hdep j).1 (by omega); omega
          rw [ih s' h1' h2' (by omega)]
          have : Vph j = false := by show decide (j % 2 = 0) = false; simp; omega
          rw [this]; rfl) s h1 h2 hN
  refine ⟨fun t _ hN h2 => hpre t h2 hN, fun k t _ hN h1 h2 => ?_, fun k t _ hN h1 h2 => ?_⟩
  · rw [phase (2 * k) t h1 h2 hN, show 2 * k / 2 = k by omega]
    have : Vph (2 * k) = true := by show decide (2 * k % 2 = 0) = true; simp
    rw [this]; rfl
  · rw [phase (2 * k + 1) t h1 h2 hN]
    have : Vph (2 * k + 1) = false := by show decide ((2 * k + 1) % 2 = 0) = false; simp
    rw [this]; rfl

/-- The node of a gated C-element, prefix form: up to `N + L.lo`. -/
theorem cel_nodeN (C : CEl a b rst O qp ex L wl wh) {N : Nat} {e : Nat → Nat} {g : Nat → Bool}
    (h : TokN 0 N ex e g) : TokN L.hi (N + L.lo) O (fun j => L.fst (e j)) g := by
  have := h.fifo L C.H_LUT_FIFO; simpa using this

/-- **Consistency with the whole-run theorem**: `cel_runN` at every `N`
gives back `OpsTimedMux.cel_run`'s conclusion (under its whole-run
hypotheses). -/
theorem cel_run_of_N (C : CEl a b rst O qp ex L wl wh) {T R : Nat} {ea eb : Nat → Nat}
    {ga gb : Nat → Bool} (ha : Formal.Cells.OpsTimed.Tok T a ea ga)
    (hb : Formal.Cells.OpsTimed.Tok T b eb gb)
    (hrh : ∀ t, t < R → rst t = true) (hrl : ∀ t, R ≤ t → rst t = false)
    (hT : T ≤ R) (hR : L.hi + wh ≤ R) (hRa : R ≤ ea 0) (hRb : R ≤ eb 0)
    (hdep : ∀ j, max (ea j) (eb j) + L.hi + wh ≤ ea (j + 1) ∧
      max (ea j) (eb j) + L.hi + wh ≤ eb (j + 1)) :
    Formal.Cells.OpsTimed.Tok 0 ex (fun j => max (ea j) (eb j)) (fun k => ga k && gb k) :=
  TokN.tok_iff.1 fun N => cel_runN C (TokN.of_tok ha N) (TokN.of_tok hb N) hrh
    (fun t h _ => hrl t h) hT hR (fun _ => hRa) (fun _ => hRb)
    (fun j => ⟨fun _ => (hdep j).1, fun _ => (hdep j).2⟩)

end cel

end Formal.Cells.Contracts
