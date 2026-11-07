import Formal.Cells.ContractsB

/-!
# Probe G1, part 1: time-truncated port contracts and causal composition

Shard B, Phase 3. Notes: `formal/notes/B-contracts-trunc.md`.

`Contracts.opSpec_of_ports` / `net_refines_ports` take a `Port` on EVERY channel
for the whole run. B's timed cell theorems derive a cell's driven wires from its
partners' wires for all time. In a closed graph that is circular (gap G1 of
`B-contracts.md`). This file supplies the causal (prefix) form that breaks the
circle:

* `TokN T N x e g`: B's `Tok` restricted to the instants `t ≤ N` (a prefix);
  `TokN.tok_iff`: `Tok` is `TokN` for every `N`. The `Tok` toolkit in prefix
  form: `fifo` (a FIFO arc with minimum delay `lo` turns a prefix up to `N` into
  a prefix up to `N + lo`), `gate`, `low_*`, `or_tok` (with the pin-skew
  condition itself only up to `N`), `reindex`, `from0`.
* The port split into the halves each side drives: `ReqUpTo` (the producer's
  request wire, its start and "next request only after the acknowledge"),
  `DatUpTo` (the producer's bus in the H_BUNDLE window), `AckUpTo` (the
  consumer's acknowledge and "acknowledge only after the request"), each up to
  time `N`; `PortUpTo` = all three.
* `port_iff`: `Port c ρ α v ↔ ∀ N, PortUpTo c ρ α v N` (the limit lemma);
  `PortUpTo.down` (prefixes are downward closed); `PortUpTo.quiet` (base case:
  a channel whose wires are low and that has no edge up to `N`).
* `causal_closure`: generic well-founded induction on time. If every wire half
  is driven by a cell whose (prefix up to `N` of everything) ⇒ (its outputs up
  to `N + d`), `d ≥ 1`, and everything holds at a base time `N0`, everything
  holds up to every `N`.
* `ports_of_causal`, `net_refines_causal`: the closed-graph composition. Every
  channel is a `Port`, hence (with each operator's `EarlierDet`) C's
  `net_refines` applies. No port is assumed for the whole run any more: the
  only whole-run inputs are the base state and the per-cell causal steps.

The per-cell causal steps for `bd_steer` are in
`Formal.Cells.ContractsTruncSteer`.

What this does NOT remove: the edge sequences `ρ α` are still given up front as
functions `Nat → Nat` (the run's edge times). A prefix theorem says nothing
about edges after `N`, so the sequences may be chosen as the actual edges of
the run; but their existence for every index (infinitely many tokens on every
channel) is still presupposed: that is G4 (finite token streams), not G1.
-/

namespace Formal.Cells.Contracts
open Formal.Net Formal.Net.Handshake Formal.Net.Ops
open Formal.Cells.OpsTimed (Tok Enum rx rx_e rx_o rx_e2 rx_0 orEdges)
open Formal.Cells.PipeTimed (Ret Vph)
open Formal.Net (Trace)

/-! ## 1. Token traces up to time `N` -/

/-- `Tok T x e g` restricted to the instants `t ≤ N`. -/
structure TokN (T N : Nat) (x : Trace) (e : Nat → Nat) (g : Nat → Bool) : Prop where
  pre : ∀ t, T ≤ t → t ≤ N → t < e 0 → x t = false
  hi : ∀ k t, T ≤ t → t ≤ N → e (2 * k) ≤ t → t < e (2 * k + 1) → x t = g k
  lo : ∀ k t, T ≤ t → t ≤ N → e (2 * k + 1) ≤ t → t < e (2 * k + 2) → x t = false

namespace TokN
variable {T N : Nat} {x : Trace} {e : Nat → Nat} {g : Nat → Bool}

theorem of_tok (h : Tok T x e g) (N : Nat) : TokN T N x e g :=
  ⟨fun t h1 _ h2 => h.pre t h1 h2, fun k t h1 _ => h.hi k t h1, fun k t h1 _ => h.lo k t h1⟩

/-- **The limit lemma for one wire.** -/
theorem tok_iff : (∀ N, TokN T N x e g) ↔ Tok T x e g :=
  ⟨fun h => ⟨fun t h1 h2 => (h t).pre t h1 (Nat.le_refl _) h2,
    fun k t h1 => (h t).hi k t h1 (Nat.le_refl _), fun k t h1 => (h t).lo k t h1 (Nat.le_refl _)⟩,
   fun h N => of_tok h N⟩

theorem down (h : TokN T N x e g) {N' : Nat} (hN : N' ≤ N) : TokN T N' x e g :=
  ⟨fun t h1 h2 => h.pre t h1 (by omega), fun k t h1 h2 => h.hi k t h1 (by omega),
    fun k t h1 h2 => h.lo k t h1 (by omega)⟩

theorem mono (h : TokN T N x e g) {T' : Nat} (hT : T ≤ T') : TokN T' N x e g :=
  ⟨fun t h1 => h.pre t (by omega), fun k t h1 => h.hi k t (by omega),
    fun k t h1 => h.lo k t (by omega)⟩

theorem congr (h : TokN T N x e g) {e' : Nat → Nat} (he : ∀ j, e j = e' j) : TokN T N x e' g :=
  ⟨fun t h1 hN h2 => h.pre t h1 hN (by rw [he]; exact h2),
    fun k t h1 hN h2 h3 => h.hi k t h1 hN (by rw [he]; exact h2) (by rw [he]; exact h3),
    fun k t h1 hN h2 h3 => h.lo k t h1 hN (by rw [he]; exact h2) (by rw [he]; exact h3)⟩

/-- **FIFO transfer, prefix form.** The output at `t` reads the input at
`σ t ≤ t - lo`; so a prefix up to `N` at the input is a prefix up to
`N + lo` at the output. This is the whole source of causality: the minimum
delay of the arc. -/
theorem fifo (r : Ret) {y : Trace} (hy : ∀ t, r.hi ≤ t → y t = x (r.σ t)) (h : TokN T N x e g) :
    TokN (T + r.hi) (N + r.lo) y (fun j => r.fst (e j)) g := by
  refine ⟨fun t h1 hN h2 => ?_, fun k t h1 hN h2 h3 => ?_, fun k t h1 hN h2 h3 => ?_⟩
  · have := r.ge t; have := r.le t
    rw [hy t (by omega)]; exact h.pre _ (by omega) (by omega) (r.fst_before h2)
  · have := r.ge t; have := r.le t
    rw [hy t (by omega)]; exact h.hi k _ (by omega) (by omega) (r.fst_after h2) (r.fst_before h3)
  · have := r.ge t; have := r.le t
    rw [hy t (by omega)]; exact h.lo k _ (by omega) (by omega) (r.fst_after h2) (r.fst_before h3)

/-- Gated function of a token trace and a bundled bit, prefix form. -/
theorem gate (h : TokN T N x e (fun _ => true)) (f : Bool → Bool → Bool)
    (hf : ∀ b, f false b = false) {s : Trace} {sv : Nat → Bool}
    (hs : ∀ k t, T ≤ t → t ≤ N → e (2 * k) ≤ t → t < e (2 * k + 1) → s t = sv k) :
    TokN T N (fun t => f (x t) (s t)) e (fun k => f true (sv k)) := by
  refine ⟨fun t h1 hN h2 => ?_, fun k t h1 hN h2 h3 => ?_, fun k t h1 hN h2 h3 => ?_⟩
  · show f (x t) (s t) = false; rw [h.pre t h1 hN h2, hf]
  · show f (x t) (s t) = f true (sv k); rw [h.hi k t h1 hN h2 h3, hs k t h1 hN h2 h3]
  · show f (x t) (s t) = false; rw [h.lo k t h1 hN h2 h3, hf]

open Formal.Cells.OpsTimed.Tok (SlotLow slotLow_odd slotLow_even slotLow_even2) in
theorem low_slot (h : TokN T N x e g) (j t : Nat) (hj : SlotLow g j) (hT : T ≤ t) (hN : t ≤ N)
    (h1 : e j ≤ t) (h2 : t < e (j + 1)) : x t = false := by
  rcases Nat.mod_two_eq_zero_or_one j with hj2 | hj2
  · have ej : j = 2 * (j / 2) := by omega
    have := h.hi (j / 2) t hT hN (by rw [← ej]; exact h1)
      (by rw [show 2 * (j / 2) + 1 = j + 1 by omega]; exact h2)
    rcases hj with hj | hj
    · omega
    · rw [this, hj]
  · exact h.lo (j / 2) t hT hN (by rw [show 2 * (j / 2) + 1 = j by omega]; exact h1)
      (by rw [show 2 * (j / 2) + 2 = j + 1 by omega]; exact h2)

open Formal.Cells.OpsTimed.Tok (SlotLow) in
theorem low_range (h : TokN T N x e g) : ∀ b a t, a ≤ b → (∀ j, a ≤ j → j < b → SlotLow g j) →
    T ≤ t → t ≤ N → e a ≤ t → t < e b → x t = false := by
  intro b
  induction b with
  | zero => intro a t hab _ _ _ h1 h2; have : a = 0 := by omega
            subst this; omega
  | succ b ih =>
    intro a t hab hs hT hN h1 h2
    by_cases hb : t < e b
    · by_cases ha : a ≤ b
      · exact ih a t ha (fun j h3 h4 => hs j h3 (by omega)) hT hN h1 hb
      · have : a = b + 1 := by omega
        subst this; omega
    · exact h.low_slot b t (hs b (by
        by_cases ha : a ≤ b
        · exact ha
        · have : a = b + 1 := by omega
          subst this; omega) (by omega)) hT hN (by omega) h2

open Formal.Cells.OpsTimed.Tok (SlotLow) in
theorem low_pre (h : TokN T N x e g) : ∀ b t, (∀ j, j < b → SlotLow g j) →
    T ≤ t → t ≤ N → t < e b → x t = false := by
  intro b
  induction b with
  | zero => intro t _ hT hN h2; exact h.pre t hT hN h2
  | succ b ih =>
    intro t hs hT hN h2
    by_cases hb : t < e b
    · exact ih t (fun j hj => hs j (by omega)) hT hN hb
    · exact h.low_slot b t (hs b (by omega)) hT hN (by omega) h2

/-- **OR of exclusive token traces, prefix form.** As `OpsTimed.or_tok`, with
the pin-skew condition (H_OR_SKEW) itself needed only for the edges that have
happened by `N`: "if the later edge is by `N`, the earlier one precedes it". -/
theorem or_tok {x y : Trace} {e e' : Nat → Nat} {g : Nat → Bool}
    (hx : TokN T N x e g) (hy : TokN T N y e' (fun k => !g k))
    (hs1 : ∀ j, e' (j + 1) ≤ N → e j ≤ e' (j + 1)) (hs2 : ∀ j, e (j + 1) ≤ N → e' j ≤ e (j + 1)) :
    TokN T N (fun t => x t || y t) (orEdges g e e') (fun _ => true) := by
  have dk : ∀ k, 2 * k / 2 = k := fun k => by omega
  have dk1 : ∀ k, (2 * k + 1) / 2 = k := fun k => by omega
  have dk2 : ∀ k, (2 * k + 2) / 2 = k + 1 := fun k => by omega
  refine ⟨fun t hT hN h2 => ?_, fun k t hT hN h1 h2 => ?_, fun k t hT hN h1 h2 => ?_⟩
  · cases hg : g 0
    · have h2' : t < e' 0 := by simpa [orEdges, hg] using h2
      have h3 : e 1 ≤ N → e' 0 ≤ e 1 := hs2 0
      have a1 : x t = false := hx.low_pre 1 t (fun j hj => by
        have : j = 0 := by omega
        subst this; exact Formal.Cells.OpsTimed.Tok.slotLow_even (k := 0) hg) hT hN (by omega)
      have a2 : y t = false := hy.pre t hT hN h2'
      simp [a1, a2]
    · have h2' : t < e 0 := by simpa [orEdges, hg] using h2
      have h3 : e' 1 ≤ N → e 0 ≤ e' 1 := hs1 0
      have a1 : x t = false := hx.pre t hT hN h2'
      have a2 : y t = false := hy.low_pre 1 t (fun j hj => by
        have : j = 0 := by omega
        subst this; exact Formal.Cells.OpsTimed.Tok.slotLow_even (k := 0)
          (g := fun k => !g k) (by simp [hg])) hT hN (by omega)
      simp [a1, a2]
  · cases hg : g k
    · have h1' : e' (2 * k) ≤ t := by simpa [orEdges, dk, hg] using h1
      have h2' : t < e' (2 * k + 1) := by simpa [orEdges, dk1, hg] using h2
      have := hy.hi k t hT hN h1' h2'; simp [hg] at this; simp [this]
    · have h1' : e (2 * k) ≤ t := by simpa [orEdges, dk, hg] using h1
      have h2' : t < e (2 * k + 1) := by simpa [orEdges, dk1, hg] using h2
      have := hx.hi k t hT hN h1' h2'; simp [hg] at this; simp [this]
  · have s1 : e' (2 * k + 1) ≤ N → e (2 * k) ≤ e' (2 * k + 1) := hs1 (2 * k)
    have s2 : e (2 * k + 1) ≤ N → e' (2 * k) ≤ e (2 * k + 1) := hs2 (2 * k)
    have s3 : e' (2 * k + 3) ≤ N → e (2 * k + 2) ≤ e' (2 * k + 3) := hs1 (2 * k + 2)
    have s4 : e (2 * k + 3) ≤ N → e' (2 * k + 2) ≤ e (2 * k + 3) := hs2 (2 * k + 2)
    have s5 : e' (2 * k + 2) ≤ N → e (2 * k + 1) ≤ e' (2 * k + 2) := hs1 (2 * k + 1)
    have s6 : e (2 * k + 2) ≤ N → e' (2 * k + 1) ≤ e (2 * k + 2) := hs2 (2 * k + 1)
    cases hg : g k <;> cases hg' : g (k + 1)
    · have h1 : e' (2 * k + 1) ≤ t := by simpa [orEdges, dk1, hg] using h1
      have h2 : t < e' (2 * k + 2) := by simpa [orEdges, dk2, hg'] using h2
      have a2 := hy.lo k t hT hN h1 h2
      have a1 := hx.low_range (2 * k + 3) (2 * k) t (by omega) (fun j h3 h4 => by
        rcases (show j = 2 * k ∨ j = 2 * k + 1 ∨ j = 2 * k + 2 by omega) with r | r | r <;> subst r
        · exact Formal.Cells.OpsTimed.Tok.slotLow_even hg
        · exact Formal.Cells.OpsTimed.Tok.slotLow_odd _ k
        · exact Formal.Cells.OpsTimed.Tok.slotLow_even2 hg') hT hN (by omega) (by omega)
      simp [a1, a2]
    · have h1 : e' (2 * k + 1) ≤ t := by simpa [orEdges, dk1, hg] using h1
      have h2 : t < e (2 * k + 2) := by simpa [orEdges, dk2, hg'] using h2
      have a1 := hx.low_range (2 * k + 2) (2 * k) t (by omega) (fun j h3 h4 => by
        rcases (show j = 2 * k ∨ j = 2 * k + 1 by omega) with r | r <;> subst r
        · exact Formal.Cells.OpsTimed.Tok.slotLow_even hg
        · exact Formal.Cells.OpsTimed.Tok.slotLow_odd _ k) hT hN (by omega) h2
      have a2 := hy.low_range (2 * k + 3) (2 * k + 1) t (by omega) (fun j h3 h4 => by
        rcases (show j = 2 * k + 1 ∨ j = 2 * k + 2 by omega) with r | r <;> subst r
        · exact Formal.Cells.OpsTimed.Tok.slotLow_odd _ k
        · exact Formal.Cells.OpsTimed.Tok.slotLow_even2 (g := fun k => !g k) (by simp [hg']))
          hT hN h1 (by omega)
      simp [a1, a2]
    · have h1 : e (2 * k + 1) ≤ t := by simpa [orEdges, dk1, hg] using h1
      have h2 : t < e' (2 * k + 2) := by simpa [orEdges, dk2, hg'] using h2
      have a1 := hx.low_range (2 * k + 3) (2 * k + 1) t (by omega) (fun j h3 h4 => by
        rcases (show j = 2 * k + 1 ∨ j = 2 * k + 2 by omega) with r | r <;> subst r
        · exact Formal.Cells.OpsTimed.Tok.slotLow_odd _ k
        · exact Formal.Cells.OpsTimed.Tok.slotLow_even2 hg') hT hN h1 (by omega)
      have a2 := hy.low_range (2 * k + 2) (2 * k) t (by omega) (fun j h3 h4 => by
        rcases (show j = 2 * k ∨ j = 2 * k + 1 by omega) with r | r <;> subst r
        · exact Formal.Cells.OpsTimed.Tok.slotLow_even (g := fun k => !g k) (by simp [hg])
        · exact Formal.Cells.OpsTimed.Tok.slotLow_odd _ k) hT hN (by omega) h2
      simp [a1, a2]
    · have h1 : e (2 * k + 1) ≤ t := by simpa [orEdges, dk1, hg] using h1
      have h2 : t < e (2 * k + 2) := by simpa [orEdges, dk2, hg'] using h2
      have a1 := hx.lo k t hT hN h1 h2
      have a2 := hy.low_range (2 * k + 3) (2 * k) t (by omega) (fun j h3 h4 => by
        rcases (show j = 2 * k ∨ j = 2 * k + 1 ∨ j = 2 * k + 2 by omega) with r | r | r <;> subst r
        · exact Formal.Cells.OpsTimed.Tok.slotLow_even (g := fun k => !g k) (by simp [hg])
        · exact Formal.Cells.OpsTimed.Tok.slotLow_odd _ k
        · exact Formal.Cells.OpsTimed.Tok.slotLow_even2 (g := fun k => !g k) (by simp [hg']))
          hT hN (by omega) (by omega)
      simp [a1, a2]

/-- **Reindex to a sub-sequence, prefix form** (as `OpsTimedMux.Tok.reindex`). -/
theorem reindex {κ : Nat → Nat} (h : TokN T N x e g) (hE : Enum g κ) :
    TokN T N x (rx e κ) (fun _ => true) := by
  refine ⟨fun t hT hN h2 => ?_, fun m t hT hN h1 h2 => ?_, fun m t hT hN h1 h2 => ?_⟩
  · rw [rx_0] at h2
    exact h.low_pre (2 * κ 0) t (fun j hj => by
      rcases Nat.mod_two_eq_zero_or_one j with hj2 | hj2
      · exact Or.inr (hE.before (k := j / 2) (by omega))
      · exact Or.inl hj2) hT hN h2
  · rw [rx_e] at h1; rw [rx_o] at h2
    have := h.hi (κ m) t hT hN h1 h2; rw [hE.hit] at this; exact this
  · rw [rx_o] at h1; rw [rx_e2] at h2
    have hm := hE.mono m
    exact h.low_range (2 * κ (m + 1)) (2 * κ m + 1) t (by omega) (fun j h3 h4 => by
      rcases Nat.mod_two_eq_zero_or_one j with hj2 | hj2
      · exact Or.inr (hE.gap (m := m) (k := j / 2) (by omega) (by omega))
      · exact Or.inl hj2) hT hN h1 h2

/-- **Lift from a sub-sequence, prefix form** (as `OpsTimedMux.Tok.lift`). A
clean prefix on the sub-sequence edges `rx E κ` is, on `E`, the gated prefix,
provided `E` is monotone on the edges that have happened by `N`. -/
theorem lift {E : Nat → Nat} {κ : Nat → Nat} (h : TokN T N x (rx E κ) (fun _ => true))
    (hE : Enum g κ) (Em : ∀ a b, a ≤ b → E b ≤ N → E a ≤ E b) : TokN T N x E g := by
  have hpre : ∀ t, T ≤ t → t ≤ N → t < E (2 * κ 0) → x t = false := fun t hT hN h2 =>
    h.pre t hT hN (by rw [rx_0]; exact h2)
  have hlo : ∀ m t, T ≤ t → t ≤ N → E (2 * κ m + 1) ≤ t → t < E (2 * κ (m + 1)) → x t = false :=
    fun m t hT hN h1 h2 => h.lo m t hT hN (by rw [rx_o]; exact h1) (by rw [rx_e2]; exact h2)
  -- `t < E a`, `a ≤ b` ⇒ `t < E b` for `t ≤ N`
  have up : ∀ a b t, a ≤ b → t ≤ N → t < E a → t < E b := fun a b t hab hN ht => by
    by_cases hb : E b ≤ N
    · have := Em a b hab hb; omega
    · omega
  refine ⟨fun t hT hN h2 => hpre t hT hN (up 0 _ t (by omega) hN h2),
    fun k t hT hN h1 h2 => ?_, fun k t hT hN h1 h2 => ?_⟩
  · cases hg : g k
    · rcases hE.bracket k with hb | ⟨m, hb1, hb2⟩
      · exact hpre t hT hN (up (2 * k + 1) _ t (by omega) hN h2)
      · have hne : κ m ≠ k := fun e => by rw [← e, hE.hit] at hg; exact absurd hg (by simp)
        exact hlo m t hT hN (by have := Em (2 * κ m + 1) (2 * k) (by omega) (by omega); omega)
          (up (2 * k + 1) _ t (by omega) hN h2)
    · obtain ⟨m, rfl⟩ := hE.all k hg
      exact h.hi m t hT hN (by rw [rx_e]; exact h1) (by rw [rx_o]; exact h2)
  · rcases hE.bracket k with hb | ⟨m, hb1, hb2⟩
    · exact hpre t hT hN (up (2 * k + 2) _ t (by omega) hN h2)
    · exact hlo m t hT hN (by have := Em (2 * κ m + 1) (2 * k + 1) (by omega) (by omega); omega)
        (up (2 * k + 2) _ t (by omega) hN h2)

/-- **Start a prefix at time 0** (as `ContractsB.tok_from0`): the wire is low
before `T` (reset quiet), and the first edge, if it has happened by `N`, is
not before `T` and not after any other edge that has happened by `N`. -/
theorem from0 (h : TokN T N x e g) (hq : ∀ t, t < T → x t = false)
    (hT : e 0 ≤ N → T ≤ e 0) (hm : ∀ j, e j ≤ N → e 0 ≤ e j) : TokN 0 N x e g := by
  refine ⟨fun t _ hN h2 => ?_, fun k t _ hN h2 h3 => ?_, fun k t _ hN h2 h3 => ?_⟩
  · by_cases hT' : T ≤ t
    · exact h.pre t hT' hN h2
    · exact hq t (by omega)
  · have := hm (2 * k) (by omega); exact h.hi k t (by omega) hN h2 h3
  · have := hm (2 * k + 1) (by omega); exact h.lo k t (by omega) hN h2 h3

end TokN

/-! ## 2. The port, split into the halves each side drives, up to time `N` -/

/-- **The producer's request half, up to `N`.** The request wire is a clean
four-phase prefix on `ρ`; the first request is not at time 0; and every
request edge that has happened by `N` follows the previous acknowledge edge
(the producer waits for the acknowledge: "next request only after ack"). -/
structure ReqUpTo (c : Chan) (ρ α : Nat → Nat) (N : Nat) : Prop where
  req : TokN 0 N c.req ρ (fun _ => true)
  start : 0 < ρ 0
  ar : ∀ j, ρ (j + 1) ≤ N → α j < ρ (j + 1)

/-- **The producer's bus half, up to `N`** (H_BUNDLE, `Port.dat` restricted). -/
def DatUpTo (c : Chan) (ρ α v : Nat → Nat) (N : Nat) : Prop :=
  ∀ k t, t ≤ N → ρ (2 * k) ≤ t → t < α (2 * k + 1) → c.dat t = v k

/-- **The consumer's acknowledge half, up to `N`.** The acknowledge wire is a
clean four-phase prefix on `α`, and every acknowledge edge that has happened by
`N` follows its request edge. -/
structure AckUpTo (c : Chan) (ρ α : Nat → Nat) (N : Nat) : Prop where
  ack : TokN 0 N c.ack α (fun _ => true)
  ra : ∀ j, α j ≤ N → ρ j < α j

/-- **The port up to time `N`.** -/
structure PortUpTo (c : Chan) (ρ α v : Nat → Nat) (N : Nat) : Prop where
  rq : ReqUpTo c ρ α N
  dt : DatUpTo c ρ α v N
  ak : AckUpTo c ρ α N

section halves
variable {c : Chan} {ρ α v : Nat → Nat} {N : Nat}

theorem ReqUpTo.down (h : ReqUpTo c ρ α N) {N' : Nat} (hN : N' ≤ N) : ReqUpTo c ρ α N' :=
  ⟨h.req.down hN, h.start, fun j hj => h.ar j (by omega)⟩
theorem DatUpTo.down (h : DatUpTo c ρ α v N) {N' : Nat} (hN : N' ≤ N) : DatUpTo c ρ α v N' :=
  fun k t ht => h k t (by omega)
theorem AckUpTo.down (h : AckUpTo c ρ α N) {N' : Nat} (hN : N' ≤ N) : AckUpTo c ρ α N' :=
  ⟨h.ack.down hN, fun j hj => h.ra j (by omega)⟩
theorem PortUpTo.down (h : PortUpTo c ρ α v N) {N' : Nat} (hN : N' ≤ N) : PortUpTo c ρ α v N' :=
  ⟨h.rq.down hN, h.dt.down hN, h.ak.down hN⟩

/-- **The limit lemma.** A port is exactly a port prefix up to every time. -/
theorem port_iff : Port c ρ α v ↔ ∀ N, PortUpTo c ρ α v N := by
  constructor
  · intro P N
    exact ⟨⟨TokN.of_tok P.req N, P.start, fun j _ => P.ar j⟩, fun k t _ => P.dat k t,
      ⟨TokN.of_tok P.ack N, fun j _ => P.ra j⟩⟩
  · intro h
    exact { req := TokN.tok_iff.1 fun N => (h N).rq.req
            ack := TokN.tok_iff.1 fun N => (h N).ak.ack
            start := (h 0).rq.start
            ra := fun j => (h (α j)).ak.ra j (Nat.le_refl _)
            ar := fun j => (h (ρ (j + 1))).rq.ar j (Nat.le_refl _)
            dat := fun k t => (h t).dt k t (Nat.le_refl _) }

/-- **Base case: a quiet channel.** If both wires are low on `[0, N]` and no
edge of either has happened by `N`, the port holds up to `N` (whatever the
bus does). This is the shape of the reset/release state: `ResetGcd`'s
`gcd_release_quiet` proves every control net of gcd_hw at its reset value
(0 for every request/acknowledge net) on `[k0, T]` until a frontier link
controller moves; with the edges of the run counted from that release, every
channel is `PortUpTo … N0` for `N0 < ` its first edge. (The net-name map from
`gNet` nodes to channel wires is not done here: it is the same missing map as
for `ContractsB`'s H_QUIET_*.) -/
theorem PortUpTo.quiet (hr : ∀ t, t ≤ N → c.req t = false) (ha : ∀ t, t ≤ N → c.ack t = false)
    (hρ : ∀ j, N < ρ j) (hα : ∀ j, N < α j) : PortUpTo c ρ α v N := by
  refine ⟨⟨⟨fun t _ hN _ => hr t hN, fun k t _ hN h1 _ => ?_, fun k t _ hN h1 _ => ?_⟩,
      by have := hρ 0; omega, fun j hj => ?_⟩, fun k t hN h1 _ => ?_,
    ⟨⟨fun t _ hN _ => ha t hN, fun k t _ hN h1 _ => ?_, fun k t _ hN h1 _ => ?_⟩, fun j hj => ?_⟩⟩
  all_goals first
    | (have := hρ (2 * k); omega)
    | (have := hρ (2 * k + 1); omega)
    | (have := hα (2 * k); omega)
    | (have := hα (2 * k + 1); omega)
    | (have := hρ (j + 1); omega)
    | (have := hα j; omega)

/-- Monotone request edges up to `N`: with the producer's and consumer's
halves up to `N`, the request edges that have happened by `N` increase. -/
theorem rho_lt_upTo (hr : ReqUpTo c ρ α N) (ha : AckUpTo c ρ α N) :
    ∀ a b, a < b → ρ b ≤ N → ρ a < ρ b := by
  intro a b hab
  induction b with
  | zero => omega
  | succ b ih =>
    intro hb
    have h1 := hr.ar b hb
    have h2 := ha.ra b (by omega)
    by_cases h : a < b
    · have := ih h (by omega); omega
    · have : a = b := by omega
      subst this; omega

end halves

/-! ## 3. Causal composition: well-founded induction on time -/

/-- **Generic causal closure.** `Q w N` is "wire half `w` is correct up to
time `N`", downward closed in `N`. If everything holds at a base time `N0`
(reset/release), and from everything up to `N` (any `N ≥ N0`) every wire half
follows up to `N + 1`, then every wire half holds up to every time. -/
theorem causal_closure {W : Type} (Q : W → Nat → Prop)
    (down : ∀ w N N', N' ≤ N → Q w N → Q w N') (N0 : Nat) (base : ∀ w, Q w N0)
    (step : ∀ N, N0 ≤ N → (∀ w, Q w N) → ∀ w, Q w (N + 1)) : ∀ w N, Q w N := by
  have up : ∀ n w, Q w (N0 + n) := by
    intro n
    induction n with
    | zero => exact base
    | succ n ih => exact step (N0 + n) (by omega) ih
  intro w N
  by_cases h : N ≤ N0
  · exact down w N0 N h (base w)
  · have := up (N - N0) w; rwa [show N0 + (N - N0) = N by omega] at this

/-- **Cell form of the causal closure.** Each wire half `w` is driven by one
cell `drv w`; each cell has a minimum delay `d o ≥ 1` (the sum of the minimum
delays of its LUT and wire arcs along its shortest input-to-output path,
H_DMIN_POS); and each cell maps "every wire half up to `N`" to "its own
outputs up to `N + d`". -/
theorem causal_closure_cells {W D : Type} (Q : W → Nat → Prop)
    (down : ∀ w N N', N' ≤ N → Q w N → Q w N') (N0 : Nat) (base : ∀ w, Q w N0)
    (drv : W → D) (d : D → Nat) (H_DMIN_POS : ∀ o, 1 ≤ d o)
    (step : ∀ N, N0 ≤ N → (∀ w, Q w N) → ∀ w, Q w (N + d (drv w))) : ∀ w N, Q w N :=
  causal_closure Q down N0 base fun N hN h w =>
    down w _ _ (by have := H_DMIN_POS (drv w); omega) (step N hN h w)

/-- The wire halves of a network on channels `C`: per channel, the request
(producer), the bus (producer) and the acknowledge (consumer). -/
inductive Half (C : Type) where
  | rq (c : C)
  | dt (c : C)
  | ak (c : C)

/-- What "half `w` correct up to `N`" means. -/
def QPort {C : Type} (ch : C → Chan) (ρ α v : C → Nat → Nat) : Half C → Nat → Prop
  | .rq c, N => ReqUpTo (ch c) (ρ c) (α c) N
  | .dt c, N => DatUpTo (ch c) (ρ c) (α c) (v c) N
  | .ak c, N => AckUpTo (ch c) (ρ c) (α c) N

theorem qport_all {C : Type} {ch : C → Chan} {ρ α v : C → Nat → Nat} {N : Nat} :
    (∀ w, QPort ch ρ α v w N) ↔ ∀ c, PortUpTo (ch c) (ρ c) (α c) (v c) N :=
  ⟨fun h c => ⟨h (.rq c), h (.dt c), h (.ak c)⟩, fun h w => by
    cases w with
    | rq c => exact (h c).rq
    | dt c => exact (h c).dt
    | ak c => exact (h c).ak⟩

/-- **Every channel of a causal closed graph is a port.** -/
theorem ports_of_causal {C D : Type} (ch : C → Chan) (ρ α v : C → Nat → Nat) (N0 : Nat)
    (base : ∀ c, PortUpTo (ch c) (ρ c) (α c) (v c) N0)
    (drv : Half C → D) (d : D → Nat) (H_DMIN_POS : ∀ o, 1 ≤ d o)
    (step : ∀ N, N0 ≤ N → (∀ c, PortUpTo (ch c) (ρ c) (α c) (v c) N) →
      ∀ w, QPort ch ρ α v w (N + d (drv w))) :
    ∀ c, Port (ch c) (ρ c) (α c) (v c) := by
  have h := causal_closure_cells (QPort ch ρ α v)
    (fun w N N' hN hq => by
      cases w with
      | rq c => exact ReqUpTo.down hq hN
      | dt c => exact DatUpTo.down hq hN
      | ak c => exact AckUpTo.down hq hN)
    N0 (qport_all.2 base) drv d H_DMIN_POS (fun N hN hall => step N hN (qport_all.1 hall))
  exact fun c => port_iff.2 fun N => qport_all.1 (fun w => h w N) c

/-- **Closed-graph composition without whole-run port assumptions.** Base
state, per-cell causal steps (prefix up to `N` ⇒ own outputs up to `N + d`)
and each operator's event data contract give C's `net_refines` conclusion:
every solution of the token equations is the value carried on every channel. -/
theorem net_refines_causal {C D O : Type} (Nt : Net C O) (ch : C → Chan)
    (E : O → (C → Nat → Nat) → Prop) (ρ α v : C → Nat → Nat) (N0 : Nat)
    (base : ∀ c, PortUpTo (ch c) (ρ c) (α c) (v c) N0)
    (drv : Half C → D) (d : D → Nat) (H_DMIN_POS : ∀ o, 1 ≤ d o)
    (step : ∀ N, N0 ≤ N → (∀ c, PortUpTo (ch c) (ρ c) (α c) (v c) N) →
      ∀ w, QPort ch ρ α v w (N + d (drv w)))
    (hD : ∀ o, EarlierDet ρ v (Nt.outs o) (E o))
    (ref : C → Nat → Nat) (href : ∀ o, E o ref) : ∀ c k, ref c k = v c k :=
  net_refines_ports Nt ch E (ports_of_causal ch ρ α v N0 base drv d H_DMIN_POS step) hD ref href

end Formal.Cells.Contracts
