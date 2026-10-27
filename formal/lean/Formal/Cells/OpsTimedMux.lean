import Formal.Cells.OpsTimed

/-!
# Shard B Phase 2, probe Lt (part 2): timed `bd_mux` and `bd_merge`

Part 1 (`OpsTimed.lean`) has the vocabulary (`Tok`, `Tok.fifo`, `Tok.gate`,
`or_tok`) and `bd_steer`. This part adds:

* **Sub-sequences of tokens** (`Enum`, `rx`, `Tok.reindex`, `Tok.lift`). The
  mux's control tokens are indexed by `k`; input x's tokens by `m`; the `m`-th
  x token is consumed by control token `κ0 m`, the `m`-th token whose
  condition selects x. `Tok.reindex` turns a control-indexed trace that is
  low in every slot not selecting x into an x-indexed clean trace;
  `Tok.lift` goes back.
* **A timed C-element with gated inputs** (`CEl`, `cel_run`). A feedback LUT
  whose REAL INIT is proved to be `~rst · C(a, b)` (here `bd_c2` for
  `uxa`/`uya`, and the mux joins `uj0`/`uj1`, whose INIT is
  `~rst · C(x_req, ctl_req · ~s)`), with a FIFO LUT arc and a window feedback
  wire (6e's `Ctl`, generalised to any two inputs). If its inputs are token
  traces on edge sequences `ea`, `eb` with gates `ga`, `gb`, every input
  departs at least `L.hi + wh` after the phase start (the generic
  **H_ENV_LATENCY**, 5b/6e), and reset is released before the first edge, then
  its excitation is the token trace on `max (ea j) (eb j)` with gate
  `ga k && gb k`: in a slot where only one input pulses (a server
  transaction for the other input) the C-element stays low. This is where
  bd_mux's **H_MUX_RTZ** lives (`MuxRtzTimed`): it is the `j = 2k+1` instance
  of the departure condition at `uxa`.
* **`bd_mux`** (`mux_ok`) and **`bd_merge`** (`merge_ok`), and a unit-delay
  non-vacuity witness for each.
-/

namespace Formal.Cells.OpsTimed
open Formal.Cells
open Formal.Cells.PipeTimed (Ret Trace lfind lfind_le lfind_spec lfind_min Vph)
open Formal.Cells.LibCtlMergeMux (or2B c2B j0B j1B cSpec or2_spec c2_spec j0_spec j1_spec)

/-! ## 1. Sub-sequences of tokens -/

/-- `κ` enumerates, in increasing order, exactly the tokens `k` with `g k`. -/
structure Enum (g : Nat → Bool) (κ : Nat → Nat) : Prop where
  mono : ∀ m, κ m < κ (m + 1)
  hit : ∀ m, g (κ m) = true
  all : ∀ k, g k = true → ∃ m, κ m = k

namespace Enum
variable {g : Nat → Bool} {κ : Nat → Nat}

theorem lt_of_lt (h : Enum g κ) : ∀ a b, a < b → κ a < κ b := by
  intro a b hab
  induction b with
  | zero => omega
  | succ b ih =>
    have := h.mono b
    by_cases hb : a < b
    · have := ih hb; omega
    · have : a = b := by omega
      subst this; omega

theorem le_of_le (h : Enum g κ) {a b : Nat} (hab : a ≤ b) : κ a ≤ κ b := by
  rcases Nat.eq_or_lt_of_le hab with e | e
  · subst e; omega
  · have := h.lt_of_lt a b e; omega

theorem lt_rev (h : Enum g κ) {a b : Nat} (hab : κ a < κ b) : a < b := by
  apply Classical.byContradiction; intro hn
  have := h.le_of_le (a := b) (b := a) (by omega); omega

theorem self_le (h : Enum g κ) : ∀ m, m ≤ κ m := by
  intro m
  induction m with
  | zero => omega
  | succ m ih => have := h.mono m; omega

theorem bracket (h : Enum g κ) : ∀ k, k < κ 0 ∨ ∃ m, κ m ≤ k ∧ k < κ (m + 1) := by
  intro k
  induction k with
  | zero =>
    by_cases h0 : 0 < κ 0
    · exact Or.inl h0
    · exact Or.inr ⟨0, by omega, by have := h.mono 0; omega⟩
  | succ k ih =>
    rcases ih with h1 | ⟨m, h1, h2⟩
    · by_cases h3 : k + 1 < κ 0
      · exact Or.inl h3
      · exact Or.inr ⟨0, by omega, by have := h.mono 0; omega⟩
    · by_cases h3 : k + 1 < κ (m + 1)
      · exact Or.inr ⟨m, by omega, h3⟩
      · exact Or.inr ⟨m + 1, by omega, by have := h.mono (m + 1); omega⟩

/-- A token selected by `g` is not strictly between two consecutive
enumerated ones, nor before the first. -/
theorem gap (h : Enum g κ) {m k : Nat} (h1 : κ m < k) (h2 : k < κ (m + 1)) : g k = false := by
  cases hk : g k
  · rfl
  · obtain ⟨m', rfl⟩ := h.all k hk
    have := h.lt_rev h1; have := h.lt_rev h2; omega

theorem before (h : Enum g κ) {k : Nat} (h1 : k < κ 0) : g k = false := by
  cases hk : g k
  · rfl
  · obtain ⟨m', rfl⟩ := h.all k hk
    have := h.lt_rev h1; omega

end Enum

theorem lfind_eq (p : Nat → Bool) {n m : Nat} (hm : m < n) (hp : p m = true)
    (hmin : ∀ m', m' < m → p m' = false) : lfind p n = m := by
  have h1 := lfind_le p n
  rcases Nat.lt_trichotomy (lfind p n) m with h | h | h
  · have := lfind_spec p n (by omega); rw [hmin _ h] at this; exact absurd this (by simp)
  · exact h
  · have := lfind_min p n m h; rw [hp] at this; exact absurd this (by simp)

/-- Index of control token `k` in the enumeration (the number of enumerated
tokens before `k`). -/
def idx (κ : Nat → Nat) (k : Nat) : Nat := lfind (fun m => decide (k ≤ κ m)) (k + 1)

theorem idx_κ {g : Nat → Bool} {κ : Nat → Nat} (h : Enum g κ) (m : Nat) : idx κ (κ m) = m := by
  unfold idx
  apply lfind_eq
  · have := h.self_le m; omega
  · simp
  · intro m' hm'; have := h.lt_of_lt m' m hm'; simp; omega

theorem κ_idx {g : Nat → Bool} {κ : Nat → Nat} (h : Enum g κ) {k : Nat} (hk : g k = true) :
    κ (idx κ k) = k := by
  obtain ⟨m, rfl⟩ := h.all k hk; rw [idx_κ h]

/-- Edges of the sub-sequence: sub-token `m`'s edges are control token
`κ m`'s. -/
def rx (e : Nat → Nat) (κ : Nat → Nat) (j : Nat) : Nat := e (2 * κ (j / 2) + j % 2)

theorem rx_e (e κ : Nat → Nat) (m : Nat) : rx e κ (2 * m) = e (2 * κ m) := by
  unfold rx; rw [show 2 * m / 2 = m by omega, show 2 * m % 2 = 0 by omega]; rfl
theorem rx_o (e κ : Nat → Nat) (m : Nat) : rx e κ (2 * m + 1) = e (2 * κ m + 1) := by
  unfold rx; rw [show (2 * m + 1) / 2 = m by omega, show (2 * m + 1) % 2 = 1 by omega]
theorem rx_e2 (e κ : Nat → Nat) (m : Nat) : rx e κ (2 * m + 2) = e (2 * κ (m + 1)) := by
  unfold rx; rw [show (2 * m + 2) / 2 = m + 1 by omega, show (2 * m + 2) % 2 = 0 by omega]; rfl
theorem rx_0 (e κ : Nat → Nat) : rx e κ 0 = e (2 * κ 0) := rx_e e κ 0

namespace Tok
variable {T : Nat} {x : Trace}

/-- **Reindex to a sub-sequence.** A control-indexed trace whose gate is
`g` becomes, on the enumeration of `g`, a clean four-phase trace. -/
theorem reindex {e : Nat → Nat} {g : Nat → Bool} {κ : Nat → Nat} (h : Tok T x e g)
    (hE : Enum g κ) : Tok T x (rx e κ) (fun _ => true) := by
  refine ⟨fun t hT h2 => ?_, fun m t hT h1 h2 => ?_, fun m t hT h1 h2 => ?_⟩
  · rw [rx_0] at h2
    exact h.low_pre (2 * κ 0) t (fun j hj => by
      rcases Nat.mod_two_eq_zero_or_one j with hj2 | hj2
      · exact Or.inr (hE.before (k := j / 2) (by omega))
      · exact Or.inl hj2) hT h2
  · rw [rx_e] at h1; rw [rx_o] at h2
    have := h.hi (κ m) t hT h1 h2; rw [hE.hit] at this; exact this
  · rw [rx_o] at h1; rw [rx_e2] at h2
    have hm := hE.mono m
    exact h.low_range (2 * κ (m + 1)) (2 * κ m + 1) t (by omega) (fun j h3 h4 => by
      rcases Nat.mod_two_eq_zero_or_one j with hj2 | hj2
      · exact Or.inr (hE.gap (m := m) (k := j / 2) (by omega) (by omega))
      · exact Or.inl hj2) hT h1 h2

/-- **Lift from a sub-sequence.** A clean trace on the sub-sequence edges
`rx E κ` of a nondecreasing control-indexed sequence `E` is, on `E`, the
control-indexed trace with gate `g`. -/
theorem lift {E : Nat → Nat} {g : Nat → Bool} {κ : Nat → Nat}
    (h : Tok T x (rx E κ) (fun _ => true)) (hE : Enum g κ) (hmono : ∀ j, E j ≤ E (j + 1)) :
    Tok T x E g := by
  have Em : ∀ a b, a ≤ b → E a ≤ E b := by
    intro a b hab
    induction b with
    | zero => have : a = 0 := by omega
              subst this; omega
    | succ b ih =>
      by_cases h' : a ≤ b
      · have := ih h'; have := hmono b; omega
      · have : a = b + 1 := by omega
        subst this; omega
  have hpre : ∀ t, T ≤ t → t < E (2 * κ 0) → x t = false := fun t hT h2 =>
    h.pre t hT (by rw [rx_0]; exact h2)
  have hlo : ∀ m t, T ≤ t → E (2 * κ m + 1) ≤ t → t < E (2 * κ (m + 1)) → x t = false :=
    fun m t hT h1 h2 => h.lo m t hT (by rw [rx_o]; exact h1) (by rw [rx_e2]; exact h2)
  refine ⟨fun t hT h2 => hpre t hT (by have := Em 0 (2 * κ 0) (by omega); omega),
    fun k t hT h1 h2 => ?_, fun k t hT h1 h2 => ?_⟩
  · cases hg : g k
    · rcases hE.bracket k with hb | ⟨m, hb1, hb2⟩
      · exact hpre t hT (by have := Em (2 * k + 1) (2 * κ 0) (by omega); omega)
      · have hne : κ m ≠ k := fun e => by rw [← e, hE.hit] at hg; exact absurd hg (by simp)
        exact hlo m t hT (by have := Em (2 * κ m + 1) (2 * k) (by omega); omega)
          (by have := Em (2 * k + 1) (2 * κ (m + 1)) (by omega); omega)
    · obtain ⟨m, rfl⟩ := hE.all k hg
      exact h.hi m t hT (by rw [rx_e]; exact h1) (by rw [rx_o]; exact h2)
  · rcases hE.bracket k with hb | ⟨m, hb1, hb2⟩
    · exact hpre t hT (by have := Em (2 * k + 2) (2 * κ 0) (by omega); omega)
    · exact hlo m t hT (by have := Em (2 * κ m + 1) (2 * k + 1) (by omega); omega)
        (by have := Em (2 * k + 2) (2 * κ (m + 1)) (by omega); omega)

end Tok

/-! ## 2. A timed C-element with gated inputs -/

/-- **Gate relations of one C-element-type feedback LUT.** `ex` is the LUT's
Boolean function of its pins; `H_EX` is a THEOREM for each instance (from the
real INIT via `c2_spec` / `j0_spec` / `j1_spec`), not an assumption. -/
structure CEl (a b rst O qp ex : Trace) (L : Ret) (wl wh : Nat) : Prop where
  H_EX : ∀ t, ex t = (!rst t && cSpec [a t, b t] (qp t))
  /-- **H_LUT_FIFO** (6e). -/
  H_LUT_FIFO : ∀ t, L.hi ≤ t → O t = ex (L.σ t)
  /-- **H_FB**: the routed feedback wire `O → own pin`, window channel. -/
  H_FB : CElemTiming.WinDelay wl wh O qp
  /-- **H_LOOP_POS**. -/
  H_LOOP_POS : 1 ≤ L.lo + wl

section cel
variable {a b rst O qp ex : Trace} {L : Ret} {wl wh : Nat}

/-- **Hold lemma.** If the excitation is `v` on `[c', c)` and on `[c, d)` the
reset is low and, at every instant, both inputs are at `v`, or one is at `v`
and the loop has had `L.hi + wh` since `c'`, then the excitation stays `v`
on `[c', d)`. -/
theorem exc_hold (C : CEl a b rst O qp ex L wl wh) (v : Bool) (c' c d : Nat)
    (hprev : ∀ s, c' ≤ s → s < c → ex s = v)
    (hin : ∀ s, c ≤ s → s < d → rst s = false ∧
      ((a s = v ∧ b s = v) ∨ ((a s = v ∨ b s = v) ∧ c' + L.hi + wh ≤ s))) :
    ∀ s, c' ≤ s → s < d → ex s = v := by
  intro s
  induction s using Nat.strongRecOn with
  | _ s ih =>
    intro h1 h2
    by_cases hc : s < c
    · exact hprev s h1 hc
    obtain ⟨hr, hab⟩ := hin s (by omega) h2
    rw [C.H_EX, hr]
    simp only [Bool.not_false, Bool.true_and]
    rcases hab with ⟨ha, hb⟩ | ⟨hab, hs⟩
    · rw [ha, hb]; cases v <;> cases qp s <;> rfl
    · have hq : qp s = v := by
        have hwl := CElemTiming.winDelay_le C.H_FB
        have hll := L.lo_le_hi
        have hpos := C.H_LOOP_POS
        obtain ⟨u, hu1, hu2, e⟩ := C.H_FB s (by omega)
        have g1 := L.ge u; have g2 := L.le u
        rw [e, C.H_LUT_FIFO u (by omega)]
        exact ih (L.σ u) (by omega) (by omega) (by omega)
      rw [hq]
      rcases hab with h | h <;> rw [h] <;> cases v <;> cases a s <;> cases b s <;> rfl

/-- **Four-phase run of a gated C-element.** See the module doc. The
conclusion is the excitation as a token trace from time 0; the node follows
through `L` (`cel_node`). -/
theorem cel_run (C : CEl a b rst O qp ex L wl wh) {T R : Nat} {ea eb : Nat → Nat}
    {ga gb : Nat → Bool} (ha : Tok T a ea ga) (hb : Tok T b eb gb)
    (hrh : ∀ t, t < R → rst t = true) (hrl : ∀ t, R ≤ t → rst t = false)
    (hT : T ≤ R) (hR : L.hi + wh ≤ R) (hRa : R ≤ ea 0) (hRb : R ≤ eb 0)
    (hdep : ∀ j, max (ea j) (eb j) + L.hi + wh ≤ ea (j + 1) ∧
      max (ea j) (eb j) + L.hi + wh ≤ eb (j + 1)) :
    Tok 0 ex (fun j => max (ea j) (eb j)) (fun k => ga k && gb k) := by
  -- the phase starts
  have cR : ∀ j, R ≤ max (ea j) (eb j) := by
    intro j
    induction j with
    | zero => omega
    | succ j ih => have := hdep j; omega
  have hpre : ∀ s, 0 ≤ s → s < max (ea 0) (eb 0) → ex s = false :=
    exc_hold C false 0 R (max (ea 0) (eb 0))
      (fun s _ h => by rw [C.H_EX, hrh s h]; rfl)
      (fun s h1 h2 => ⟨hrl s h1, Or.inr ⟨by
        by_cases h3 : s < ea 0
        · exact Or.inl (ha.pre s (by omega) h3)
        · exact Or.inr (hb.pre s (by omega) (by omega)), by omega⟩⟩)
  -- one phase, given the excitation is 0 just before it when it starts an even phase
  have step : ∀ j c', c' + L.hi + wh ≤ max (ea j) (eb j) →
      (j % 2 = 0 → ∀ s, c' ≤ s → s < max (ea j) (eb j) → ex s = false) →
      ∀ s, max (ea j) (eb j) ≤ s → s < max (ea (j + 1)) (eb (j + 1)) →
        ex s = (Vph j && (ga (j / 2) && gb (j / 2))) := by
    intro j c' hc' hprev
    have d1 := hdep j; have d2 := hdep (j + 1)
    -- input values across the phase
    have va : ∀ s, max (ea j) (eb j) ≤ s → s < max (ea (j + 1)) (eb (j + 1)) →
        (s < ea (j + 1) → a s = (Vph j && ga (j / 2))) ∧
        (ea (j + 1) ≤ s → a s = (Vph (j + 1) && ga ((j + 1) / 2))) := fun s h1 h2 =>
      ⟨fun h3 => ha.at_phase j s (by have := cR j; omega) (by omega) h3,
        fun h3 => ha.at_phase (j + 1) s (by have := cR j; omega) h3 (by omega)⟩
    have vb : ∀ s, max (ea j) (eb j) ≤ s → s < max (ea (j + 1)) (eb (j + 1)) →
        (s < eb (j + 1) → b s = (Vph j && gb (j / 2))) ∧
        (eb (j + 1) ≤ s → b s = (Vph (j + 1) && gb ((j + 1) / 2))) := fun s h1 h2 =>
      ⟨fun h3 => hb.at_phase j s (by have := cR j; omega) (by omega) h3,
        fun h3 => hb.at_phase (j + 1) s (by have := cR j; omega) h3 (by omega)⟩
    by_cases hA : (Vph j && ga (j / 2)) = (Vph j && (ga (j / 2) && gb (j / 2))) ∧
        (Vph j && gb (j / 2)) = (Vph j && (ga (j / 2) && gb (j / 2)))
    · -- both inputs move to the target: an ordinary phase
      exact exc_hold C _ (max (ea j) (eb j)) (max (ea j) (eb j)) _ (fun s h1 h2 => by omega)
        (fun s h1 h2 => ⟨hrl s (by have := cR j; omega), by
          by_cases e1 : s < ea (j + 1)
          · by_cases e2 : s < eb (j + 1)
            · exact Or.inl ⟨((va s h1 h2).1 e1).trans hA.1, ((vb s h1 h2).1 e2).trans hA.2⟩
            · exact Or.inr ⟨Or.inl (((va s h1 h2).1 e1).trans hA.1), by omega⟩
          · have e2 : s < eb (j + 1) := by omega
            exact Or.inr ⟨Or.inr (((vb s h1 h2).1 e2).trans hA.2), by omega⟩⟩)
    · -- one gate is off in an even phase: that input stays low across it
      have hj : j % 2 = 0 := by
        apply Classical.byContradiction; intro hn
        have : Vph j = false := by show decide (j % 2 = 0) = false; simp; omega
        rw [this] at hA; simp at hA
      have hV : Vph j = true := by show decide (j % 2 = 0) = true; simp; omega
      have hV1 : Vph (j + 1) = false := by show decide ((j + 1) % 2 = 0) = false; simp; omega
      rw [hV] at hA ⊢
      have hlow : ∀ s, max (ea j) (eb j) ≤ s → s < max (ea (j + 1)) (eb (j + 1)) →
          a s = false ∨ b s = false := by
        intro s h1 h2
        cases hga : ga (j / 2) <;> cases hgb : gb (j / 2) <;> rw [hga, hgb] at hA <;> simp at hA
        · by_cases e1 : s < ea (j + 1)
          · left; rw [(va s h1 h2).1 e1, hV, hga]; rfl
          · left; rw [(va s h1 h2).2 (by omega), hV1]; rfl
        · by_cases e1 : s < eb (j + 1)
          · right; rw [(vb s h1 h2).1 e1, hV, hgb]; rfl
          · right; rw [(vb s h1 h2).2 (by omega), hV1]; rfl
      have htg : (true && (ga (j / 2) && gb (j / 2))) = false := by
        cases hga : ga (j / 2) <;> cases hgb : gb (j / 2) <;> rw [hga, hgb] at hA <;> simp at hA
          <;> rfl
      rw [htg]
      intro s h1 h2
      exact exc_hold C false c' (max (ea j) (eb j)) _ (hprev hj)
        (fun s h1 h2 => ⟨hrl s (by have := cR j; omega), Or.inr ⟨by
          rcases hlow s h1 h2 with h | h
          · exact Or.inl h
          · exact Or.inr h, by omega⟩⟩) s (by omega) h2
  have phase : ∀ j s, max (ea j) (eb j) ≤ s → s < max (ea (j + 1)) (eb (j + 1)) →
      ex s = (Vph j && (ga (j / 2) && gb (j / 2))) := by
    intro j
    induction j with
    | zero => exact step 0 0 (by have := cR 0; omega) (fun _ => hpre)
    | succ j ih =>
      exact step (j + 1) (max (ea j) (eb j)) (by have := hdep j; omega) (fun hj s h1 h2 => by
        rw [ih s h1 h2]
        have : Vph j = false := by show decide (j % 2 = 0) = false; simp; omega
        rw [this]; rfl)
  refine ⟨fun t _ h2 => hpre t (by omega) h2, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
  · rw [phase (2 * k) t h1 h2, show 2 * k / 2 = k by omega]
    have : Vph (2 * k) = true := by show decide (2 * k % 2 = 0) = true; simp
    rw [this]; rfl
  · rw [phase (2 * k + 1) t h1 h2]
    have : Vph (2 * k + 1) = false := by show decide ((2 * k + 1) % 2 = 0) = false; simp
    rw [this]; rfl

/-- The node of a gated C-element: its excitation through the FIFO LUT. -/
theorem cel_node (C : CEl a b rst O qp ex L wl wh) {e : Nat → Nat} {g : Nat → Bool}
    (h : Tok 0 ex e g) : Tok L.hi O (fun j => L.fst (e j)) g := by
  have := h.fifo L C.H_LUT_FIFO; simpa using this

end cel

theorem Tok.gcongr {T : Nat} {x : Trace} {e : Nat → Nat} {g g' : Nat → Bool} (h : Tok T x e g)
    (hg : ∀ k, g k = g' k) : Tok T x e g' :=
  ⟨h.pre, fun k t h1 h2 h3 => by rw [← hg]; exact h.hi k t h1 h2 h3, h.lo⟩

/-! ## 3. `bd_mux`

`cells/rtl/bd_mux.v`:

    uj0: LUT6 0000_AE08_0000_AE08 (I0 x_req, I1 ctl_req, I2 s, I3 j0, I4 rst, I5 0) -> j0
    uj1: LUT6 0000_EA80_0000_EA80 (I0 y_req, I1 ctl_req, I2 s, I3 j1, I4 rst, I5 0) -> j1
    uor: LUT2 E (j0, j1) -> either;   udly: bd_delay (either -> z_req)
    uxa: bd_c2 (j0, z_ack) -> x_ack;  uya: bd_c2 (j1, z_ack) -> y_ack;  ctl_ack = z_ack

Control token `k` carries the condition `sv k` (`s`; 0 selects x). x's
`m`-th token is consumed by control token `κ0 m` (the `m`-th with `s = 0`),
y's by `κ1 m`. The environment's port edges: `ξ` (x_req), `η` (y_req),
`γ` (ctl_req), `ζ` (z_ack, the server). Every other edge is derived. -/

/-- Delay realisation of one run of a mux, plus the environment's event
times and the two enumerations. -/
structure MuxRun where
  /-- wires `x_req → uj0.I0`, `y_req → uj1.I0`, `ctl_req → uj0.I1`, `ctl_req → uj1.I1` -/
  Wx : Ret
  Wy : Ret
  Wc0 : Ret
  Wc1 : Ret
  /-- join LUT arcs and their feedback-wire windows -/
  Lj0 : Ret
  Lj1 : Ret
  wj0l : Nat
  wj0h : Nat
  wj1l : Nat
  wj1h : Nat
  /-- wires `j0 → uor.I0`, `j1 → uor.I1`, `j0 → uxa.I0`, `j1 → uya.I0` -/
  W0o : Ret
  W1o : Ret
  W0x : Ret
  W1y : Ret
  /-- `uor` arc; `bd_delay` (DELAY LUT1 hops + wires, FASTFALL = 0) plus the wire to the server -/
  Lor : Ret
  Dz : Ret
  /-- wires `z_ack → uxa.I1`, `z_ack → uya.I1` -/
  Wzx : Ret
  Wzy : Ret
  /-- acknowledge C-element arcs and feedback windows -/
  Lxa : Ret
  Lya : Ret
  wxal : Nat
  wxah : Nat
  wyal : Nat
  wyah : Nat
  /-- wires `x_ack → x client`, `y_ack → y client` -/
  Wxa : Ret
  Wya : Ret
  ξ : Nat → Nat
  η : Nat → Nat
  γ : Nat → Nat
  ζ : Nat → Nat
  sv : Nat → Bool
  κ0 : Nat → Nat
  κ1 : Nat → Nat

namespace MuxRun
variable (P : MuxRun)
/-- x_req, y_req at the joins (x-, y-indexed). -/
def Xp (j : Nat) : Nat := P.Wx.fst (P.ξ j)
def Yp (j : Nat) : Nat := P.Wy.fst (P.η j)
/-- ctl_req at each join (control-indexed). -/
def C0 (j : Nat) : Nat := P.Wc0.fst (P.γ j)
def C1 (j : Nat) : Nat := P.Wc1.fst (P.γ j)
/-- The decode `ctl_req · ~s` at uj0 on x's tokens (and `ctl_req · s` at uj1). -/
def D0 : Nat → Nat := rx P.C0 P.κ0
def D1 : Nat → Nat := rx P.C1 P.κ1
/-- Phase starts of the joins and their node edges (x-, y-indexed). -/
def c0 (j : Nat) : Nat := max (P.Xp j) (P.D0 j)
def c1 (j : Nat) : Nat := max (P.Yp j) (P.D1 j)
def τ0 (j : Nat) : Nat := P.Lj0.fst (P.c0 j)
def τ1 (j : Nat) : Nat := P.Lj1.fst (P.c1 j)
/-- The selected join's node edges, control-indexed. -/
def E (j : Nat) : Nat :=
  if P.sv (j / 2) then P.τ1 (2 * idx P.κ1 (j / 2) + j % 2) else P.τ0 (2 * idx P.κ0 (j / 2) + j % 2)
/-- j0, j1 at uor's pins; z_req at the server's pin. -/
def O0 (j : Nat) : Nat := P.W0o.fst (P.E j)
def O1 (j : Nat) : Nat := P.W1o.fst (P.E j)
def Z (j : Nat) : Nat := P.Dz.fst (P.Lor.fst (orEdges (fun k => !P.sv k) P.O0 P.O1 j))
/-- At the acknowledge C-elements' pins, their phase starts, and the
acknowledges at the clients' pins. -/
def A0 (j : Nat) : Nat := P.W0x.fst (P.E j)
def A1 (j : Nat) : Nat := P.W1y.fst (P.E j)
def ZA0 (j : Nat) : Nat := P.Wzx.fst (P.ζ j)
def ZA1 (j : Nat) : Nat := P.Wzy.fst (P.ζ j)
def cx (j : Nat) : Nat := max (P.A0 j) (P.ZA0 j)
def cy (j : Nat) : Nat := max (P.A1 j) (P.ZA1 j)
def XA (j : Nat) : Nat := P.Wxa.fst (P.Lxa.fst (P.cx j))
def YA (j : Nat) : Nat := P.Wya.fst (P.Lya.fst (P.cy j))
/-- Start of z_req's clean window, and of x_ack's / y_ack's. -/
def Tz : Nat := P.Lj0.hi + P.W0o.hi + (P.Lj1.hi + P.W1o.hi) + P.Lor.hi + P.Dz.hi
def Tx : Nat := P.Lxa.hi + P.Wxa.hi
def Ty : Nat := P.Lya.hi + P.Wya.hi
end MuxRun

/-- **The mux's gate relations** (one field per primitive; LUTs evaluated
from their REAL INITs). -/
structure MuxGates (P : MuxRun) (rst x y ctl za xj yj cj0 cj1 sx0 sx1 j0 q0 j1 q1 e0 e1 ei zr
    j0x j1y zx zy xa qa ya qb xak yak : Trace) : Prop where
  H_WX : ∀ t, P.Wx.hi ≤ t → xj t = x (P.Wx.σ t)
  H_WY : ∀ t, P.Wy.hi ≤ t → yj t = y (P.Wy.σ t)
  H_WC0 : ∀ t, P.Wc0.hi ≤ t → cj0 t = ctl (P.Wc0.σ t)
  H_WC1 : ∀ t, P.Wc1.hi ≤ t → cj1 t = ctl (P.Wc1.σ t)
  /-- **H_LUT_FIFO** for `uj0`, REAL INIT `0x0000AE080000AE08` (`j0B`). -/
  H_UJ0 : ∀ t, P.Lj0.hi ≤ t →
    j0 t = j0B (xj (P.Lj0.σ t)) (cj0 (P.Lj0.σ t)) (sx0 (P.Lj0.σ t)) (q0 (P.Lj0.σ t)) (rst (P.Lj0.σ t))
  /-- **H_FB** for `uj0` (the `(* keep *)` O → I3 net). -/
  H_UJ0_FB : CElemTiming.WinDelay P.wj0l P.wj0h j0 q0
  H_UJ0_POS : 1 ≤ P.Lj0.lo + P.wj0l
  /-- **H_LUT_FIFO** for `uj1`, REAL INIT `0x0000EA800000EA80` (`j1B`). -/
  H_UJ1 : ∀ t, P.Lj1.hi ≤ t →
    j1 t = j1B (yj (P.Lj1.σ t)) (cj1 (P.Lj1.σ t)) (sx1 (P.Lj1.σ t)) (q1 (P.Lj1.σ t)) (rst (P.Lj1.σ t))
  H_UJ1_FB : CElemTiming.WinDelay P.wj1l P.wj1h j1 q1
  H_UJ1_POS : 1 ≤ P.Lj1.lo + P.wj1l
  H_W0O : ∀ t, P.W0o.hi ≤ t → e0 t = j0 (P.W0o.σ t)
  H_W1O : ∀ t, P.W1o.hi ≤ t → e1 t = j1 (P.W1o.σ t)
  /-- **H_LUT_FIFO** for `uor` (`4'hE`). -/
  H_UOR : ∀ t, P.Lor.hi ≤ t → ei t = or2B (e0 (P.Lor.σ t)) (e1 (P.Lor.σ t))
  /-- **H_LINE_FIFO**: `bd_delay` with FASTFALL = 0 is a symmetric chain of
  LUT1 buffers, a FIFO channel by `PipeTimed.fifo_comp`; FASTFALL = 1 is not
  covered here. -/
  H_DZ : ∀ t, P.Dz.hi ≤ t → zr t = ei (P.Dz.σ t)
  H_W0X : ∀ t, P.W0x.hi ≤ t → j0x t = j0 (P.W0x.σ t)
  H_W1Y : ∀ t, P.W1y.hi ≤ t → j1y t = j1 (P.W1y.σ t)
  H_WZX : ∀ t, P.Wzx.hi ≤ t → zx t = za (P.Wzx.σ t)
  H_WZY : ∀ t, P.Wzy.hi ≤ t → zy t = za (P.Wzy.σ t)
  /-- **H_LUT_FIFO** for `uxa`, `bd_c2` REAL INIT `0x00E800E800E800E8`. -/
  H_UXA : ∀ t, P.Lxa.hi ≤ t →
    xa t = c2B (j0x (P.Lxa.σ t)) (zx (P.Lxa.σ t)) (qa (P.Lxa.σ t)) (rst (P.Lxa.σ t))
  H_UXA_FB : CElemTiming.WinDelay P.wxal P.wxah xa qa
  H_UXA_POS : 1 ≤ P.Lxa.lo + P.wxal
  H_UYA : ∀ t, P.Lya.hi ≤ t →
    ya t = c2B (j1y (P.Lya.σ t)) (zy (P.Lya.σ t)) (qb (P.Lya.σ t)) (rst (P.Lya.σ t))
  H_UYA_FB : CElemTiming.WinDelay P.wyal P.wyah ya qb
  H_UYA_POS : 1 ≤ P.Lya.lo + P.wyal
  H_WXA : ∀ t, P.Wxa.hi ≤ t → xak t = xa (P.Wxa.σ t)
  H_WYA : ∀ t, P.Wya.hi ≤ t → yak t = ya (P.Wya.σ t)

/-- **The mux's environment**: four clean four-phase partners and the
control channel's bundling. -/
structure MuxEnv (P : MuxRun) (rst x y ctl za sx0 sx1 : Trace) (R : Nat) : Prop where
  /-- **H_RST**: reset high on `[0, R)`, low from `R`. -/
  H_RST_HI : ∀ t, t < R → rst t = true
  H_RST_LO : ∀ t, R ≤ t → rst t = false
  /-- **H_SND_CLEAN** for x, y and the control sender; **H_SRV_CLEAN** for the
  server's acknowledge. -/
  H_X : Tok 0 x P.ξ (fun _ => true)
  H_Y : Tok 0 y P.η (fun _ => true)
  H_CTL : Tok 0 ctl P.γ (fun _ => true)
  H_ZA : Tok 0 za P.ζ (fun _ => true)
  /-- The enumerations of the tokens selecting x and y. -/
  H_ENUM0 : Enum (fun k => !P.sv k) P.κ0
  H_ENUM1 : Enum P.sv P.κ1
  /-- **H_BUNDLED_S_PIN** at both joins: `s` at the join's I2 shows the
  token's condition while `ctl_req` is high at the join's I1. JSON:
  `bd_mux.bundled_s_setup` + `bd_mux.bundled_s_hold` (pin form; their static
  forms as in `steer_s_pin_of_wire`). -/
  H_S_PIN0 : ∀ k t, P.C0 (2 * k) ≤ t → t < P.C0 (2 * k + 1) → sx0 t = P.sv k
  H_S_PIN1 : ∀ k t, P.C1 (2 * k) ≤ t → t < P.C1 (2 * k + 1) → sx1 t = P.sv k

/-- **The mux's timing obligations**, each an inequality between derived
event times (the port-level causality of the four partners is folded in:
each is discharged by a causal chain, see the notes). -/
structure MuxTiming (P : MuxRun) (R : Nat) : Prop where
  /-- **H_RST_LONG**: reset outlasts each wire's and each loop's maximum delay
  (so every pin is clean and every C-element cleared before release). -/
  H_RST_LONG : P.Wx.hi ≤ R ∧ P.Wy.hi ≤ R ∧ P.Wc0.hi ≤ R ∧ P.Wc1.hi ≤ R ∧
    P.Lj0.hi + P.wj0h ≤ R ∧ P.Lj1.hi + P.wj1h ≤ R ∧ P.Lj0.hi + P.W0x.hi ≤ R ∧
    P.Lj1.hi + P.W1y.hi ≤ R ∧ P.Wzx.hi ≤ R ∧ P.Wzy.hi ≤ R ∧ P.Lxa.hi + P.wxah ≤ R ∧
    P.Lya.hi + P.wyah ≤ R
  /-- **H_RST_EARLY**: no first edge reaches a C-element before reset is released. -/
  H_RST_EARLY : R ≤ P.Xp 0 ∧ R ≤ P.D0 0 ∧ R ≤ P.Yp 0 ∧ R ≤ P.D1 0 ∧ R ≤ P.A0 0 ∧
    R ≤ P.ZA0 0 ∧ R ≤ P.A1 0 ∧ R ≤ P.ZA1 0
  /-- **H_DEP_J0 / H_DEP_J1** (join env latency): x_req (resp. the decode)
  leaves its phase value at uj0's pin only `Lj0.hi + wj0h` after the phase
  started. The x client drops x_req after seeing x_ack, the control sender
  drops ctl_req after seeing ctl_ack = z_ack: both loops pass through uxa or
  the server, so this is the C-element's `env_latency` with the whole loop as
  slack. JSON: `bd_c2.env_latency` instantiated at uj0/uj1 (no `bd_mux`
  entry; reported). -/
  H_DEP_J0 : ∀ j, P.c0 j + P.Lj0.hi + P.wj0h ≤ P.Xp (j + 1) ∧ P.c0 j + P.Lj0.hi + P.wj0h ≤ P.D0 (j + 1)
  H_DEP_J1 : ∀ j, P.c1 j + P.Lj1.hi + P.wj1h ≤ P.Yp (j + 1) ∧ P.c1 j + P.Lj1.hi + P.wj1h ≤ P.D1 (j + 1)
  /-- **H_CTL_SEQ**: the next control token's ctl_req reaches its join only
  after the previous token's join node fell (the control sender raises it
  after ctl_ack = z_ack fell, which follows z_req's fall, which follows the
  join's). Together with `H_DEP_J*` it makes the joins' edges one monotone
  sequence (`mux_E_mono`). JSON: `bd_mux.isochronic_forks` (the
  `ctl_req -> {uj0, uj1}` branch must not lag a half handshake) is this, in
  timed form; reported as a refinement. -/
  H_CTL_SEQ : ∀ k, P.E (2 * k + 1) ≤ (if P.sv (k + 1) then P.C1 (2 * k + 2) else P.C0 (2 * k + 2))
  /-- **H_OR_SKEW** at uor's pins. JSON: none (reported missing). -/
  H_OR_SKEW : ∀ j, P.O0 j ≤ P.O1 (j + 1) ∧ P.O1 j ≤ P.O0 (j + 1)
  /-- **H_DEP_XA / H_DEP_YA** (acknowledge C-element env latency). The
  `j = 2k+1` instance against `ZA0 (2k+2)` (the next z_ack rise, for ANY
  input) is **H_MUX_RTZ** (`bd_mux.uxa_rtz`, `bd_mux.uxa_rtz_env`); against
  `A0 (2k+2)` it is the generic `bd_c2.env_latency`; the `j = 2k` instance
  against `A0 (2k+1)` and the cross-slot instances (z_ack's fall reaching uxa
  before j0's next rise) are the `z_ack -> {uxa, uya, ctl}` fork of
  `bd_mux.isochronic_forks`. -/
  H_DEP_XA : ∀ j, P.cx j + P.Lxa.hi + P.wxah ≤ P.A0 (j + 1) ∧ P.cx j + P.Lxa.hi + P.wxah ≤ P.ZA0 (j + 1)
  H_DEP_YA : ∀ j, P.cy j + P.Lya.hi + P.wyah ≤ P.A1 (j + 1) ∧ P.cy j + P.Lya.hi + P.wyah ≤ P.ZA1 (j + 1)

section mux
variable {P : MuxRun} {R : Nat}

theorem E_rx0 (h : Enum (fun k => !P.sv k) P.κ0) (j : Nat) : rx P.E P.κ0 j = P.τ0 j := by
  unfold rx MuxRun.E
  have h1 : (2 * P.κ0 (j / 2) + j % 2) / 2 = P.κ0 (j / 2) := by omega
  have h2 : (2 * P.κ0 (j / 2) + j % 2) % 2 = j % 2 := by omega
  have h3 : P.sv (P.κ0 (j / 2)) = false := by have := h.hit (j / 2); simpa using this
  rw [h1, h2, h3, idx_κ h, show 2 * (j / 2) + j % 2 = j by omega]; rfl

theorem E_rx1 (h : Enum P.sv P.κ1) (j : Nat) : rx P.E P.κ1 j = P.τ1 j := by
  unfold rx MuxRun.E
  have h1 : (2 * P.κ1 (j / 2) + j % 2) / 2 = P.κ1 (j / 2) := by omega
  have h2 : (2 * P.κ1 (j / 2) + j % 2) % 2 = j % 2 := by omega
  rw [h1, h2, h.hit (j / 2), idx_κ h, show 2 * (j / 2) + j % 2 = j by omega]; rfl

/-- **The joins' edges form one monotone sequence.** Derived from the
joins' env latency and H_CTL_SEQ. -/
theorem mux_E_mono (hE0 : Enum (fun k => !P.sv k) P.κ0) (hE1 : Enum P.sv P.κ1) (TM : MuxTiming P R) :
    ∀ j, P.E j ≤ P.E (j + 1) := by
  intro j
  rcases Nat.mod_two_eq_zero_or_one j with hj | hj
  · obtain ⟨k, rfl⟩ : ∃ k, j = 2 * k := ⟨j / 2, by omega⟩
    unfold MuxRun.E
    rw [show 2 * k / 2 = k by omega, show (2 * k + 1) / 2 = k by omega,
      show 2 * k % 2 = 0 by omega, show (2 * k + 1) % 2 = 1 by omega]
    simp only [Nat.add_zero]
    split
    · apply fst_mono
      have := TM.H_DEP_J1 (2 * idx P.κ1 k); unfold MuxRun.c1 at *; omega
    · apply fst_mono
      have := TM.H_DEP_J0 (2 * idx P.κ0 k); unfold MuxRun.c0 at *; omega
  · obtain ⟨k, rfl⟩ : ∃ k, j = 2 * k + 1 := ⟨j / 2, by omega⟩
    have hs := TM.H_CTL_SEQ k
    have e2 : P.E (2 * k + 1 + 1) = if P.sv (k + 1) then P.τ1 (2 * idx P.κ1 (k + 1))
        else P.τ0 (2 * idx P.κ0 (k + 1)) := by
      unfold MuxRun.E; rw [show (2 * k + 1 + 1) / 2 = k + 1 by omega, show (2 * k + 1 + 1) % 2 = 0 by omega]; rfl
    rw [e2]
    cases hsv : P.sv (k + 1)
    · rw [hsv] at hs; simp only [Bool.false_eq_true, ite_false] at hs ⊢
      have hk := κ_idx hE0 (k := k + 1) (by simp [hsv])
      have a1 := P.Lj0.fst_ge (P.c0 (2 * idx P.κ0 (k + 1)))
      have a2 : P.D0 (2 * idx P.κ0 (k + 1)) = P.C0 (2 * (k + 1)) := by
        unfold MuxRun.D0; rw [rx_e, hk]
      unfold MuxRun.τ0 MuxRun.c0 at *
      rw [show 2 * (k + 1) = 2 * k + 2 by omega] at a2
      omega
    · rw [hsv] at hs; simp only [ite_true] at hs ⊢
      have hk := κ_idx hE1 (k := k + 1) hsv
      have a1 := P.Lj1.fst_ge (P.c1 (2 * idx P.κ1 (k + 1)))
      have a2 : P.D1 (2 * idx P.κ1 (k + 1)) = P.C1 (2 * (k + 1)) := by
        unfold MuxRun.D1; rw [rx_e, hk]
      unfold MuxRun.τ1 MuxRun.c1 at *
      rw [show 2 * (k + 1) = 2 * k + 2 by omega] at a2
      omega

/-- **`mux_ok`: the mux meets its handshake spec for every token.**
(1) Each join fires exactly for the control tokens selecting its input, once
per token (control-indexed `j0`, `j1`); (2) the server sees exactly one
transaction per control token (`z_req`); (3) x_ack pulses exactly in the
control tokens selecting x, i.e. exactly once per x token (x-indexed form),
never during a y transaction (and symmetrically for y); (4) order: the join
for x's `m`-th token fires only after both x's request and the control token
reached it, and an acknowledge rises only after the server's. -/
theorem mux_ok {rst x y ctl za xj yj cj0 cj1 sx0 sx1 j0 q0 j1 q1 e0 e1 ei zr j0x j1y zx zy xa qa
      ya qb xak yak : Trace}
    (G : MuxGates P rst x y ctl za xj yj cj0 cj1 sx0 sx1 j0 q0 j1 q1 e0 e1 ei zr j0x j1y zx zy xa qa
      ya qb xak yak)
    (V : MuxEnv P rst x y ctl za sx0 sx1 R) (TM : MuxTiming P R) :
    Tok P.Lj0.hi j0 P.E (fun k => !P.sv k) ∧ Tok P.Lj1.hi j1 P.E P.sv ∧
    Tok P.Tz zr P.Z (fun _ => true) ∧
    Tok P.Tx xak P.XA (fun k => !P.sv k) ∧ Tok P.Tx xak (rx P.XA P.κ0) (fun _ => true) ∧
    Tok P.Ty yak P.YA P.sv ∧ Tok P.Ty yak (rx P.YA P.κ1) (fun _ => true) ∧
    (∀ m, P.Xp (2 * m) ≤ P.E (2 * P.κ0 m) ∧ P.C0 (2 * P.κ0 m) ≤ P.E (2 * P.κ0 m)) ∧
    (∀ m, P.Yp (2 * m) ≤ P.E (2 * P.κ1 m) ∧ P.C1 (2 * P.κ1 m) ≤ P.E (2 * P.κ1 m)) ∧
    (∀ j, P.ζ j ≤ P.XA j ∧ P.ζ j ≤ P.YA j) := by
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12⟩ := TM.H_RST_LONG
  obtain ⟨u1, u2, u3, u4, u5, u6, u7, u8⟩ := TM.H_RST_EARLY
  have Em := mux_E_mono V.H_ENUM0 V.H_ENUM1 TM
  -- join 0, x-indexed
  have hxj : Tok R xj P.Xp (fun _ => true) := ((V.H_X.fifo P.Wx G.H_WX).mono (by omega))
  have hdec0 : Tok R (fun t => cj0 t && !sx0 t) P.D0 (fun _ => true) :=
    (((V.H_CTL.fifo P.Wc0 G.H_WC0).gate (fun a b => a && !b) (fun _ => rfl) (s := sx0) (sv := P.sv)
      (fun k t _ h1 h2 => V.H_S_PIN0 k t h1 h2)).reindex V.H_ENUM0).mono (by omega)
  have C0 : CEl xj (fun t => cj0 t && !sx0 t) rst j0 q0
      (fun t => j0B (xj t) (cj0 t) (sx0 t) (q0 t) (rst t)) P.Lj0 P.wj0l P.wj0h :=
    ⟨fun t => j0_spec _ _ _ _ _, G.H_UJ0, G.H_UJ0_FB, G.H_UJ0_POS⟩
  have n0 := cel_node C0 (cel_run C0 hxj hdec0 V.H_RST_HI V.H_RST_LO (Nat.le_refl R) r5 u1 u2 TM.H_DEP_J0)
  have j0E : Tok P.Lj0.hi j0 P.E (fun k => !P.sv k) :=
    ((n0.congr (fun j => (E_rx0 V.H_ENUM0 j).symm)).lift V.H_ENUM0 Em)
  -- join 1, y-indexed
  have hyj : Tok R yj P.Yp (fun _ => true) := ((V.H_Y.fifo P.Wy G.H_WY).mono (by omega))
  have hdec1 : Tok R (fun t => cj1 t && sx1 t) P.D1 (fun _ => true) :=
    (((V.H_CTL.fifo P.Wc1 G.H_WC1).gate (fun a b => a && b) (fun _ => rfl) (s := sx1) (sv := P.sv)
      (fun k t _ h1 h2 => V.H_S_PIN1 k t h1 h2)).reindex V.H_ENUM1).mono (by omega)
  have C1 : CEl yj (fun t => cj1 t && sx1 t) rst j1 q1
      (fun t => j1B (yj t) (cj1 t) (sx1 t) (q1 t) (rst t)) P.Lj1 P.wj1l P.wj1h :=
    ⟨fun t => j1_spec _ _ _ _ _, G.H_UJ1, G.H_UJ1_FB, G.H_UJ1_POS⟩
  have n1 := cel_node C1 (cel_run C1 hyj hdec1 V.H_RST_HI V.H_RST_LO (Nat.le_refl R) r6 u3 u4 TM.H_DEP_J1)
  have j1E : Tok P.Lj1.hi j1 P.E P.sv :=
    ((n1.congr (fun j => (E_rx1 V.H_ENUM1 j).symm)).lift V.H_ENUM1 Em)
  -- uor and the delay line
  have p0 : Tok (P.Lj0.hi + P.W0o.hi + (P.Lj1.hi + P.W1o.hi)) e0 P.O0 (fun k => !P.sv k) :=
    (j0E.fifo P.W0o G.H_W0O).mono (by omega)
  have p1 : Tok (P.Lj0.hi + P.W0o.hi + (P.Lj1.hi + P.W1o.hi)) e1 P.O1 (fun k => !(!P.sv k)) :=
    ((j1E.fifo P.W1o G.H_W1O).mono (by omega)).gcongr (fun k => by simp)
  have o := or_tok p0 p1 (fun j => (TM.H_OR_SKEW j).1) (fun j => (TM.H_OR_SKEW j).2)
  have zt := (o.fifo P.Lor (y := ei) (fun t ht => by rw [G.H_UOR t ht, or2_spec])).fifo P.Dz G.H_DZ
  -- the acknowledge C-elements
  have ax : Tok R j0x P.A0 (fun k => !P.sv k) := (j0E.fifo P.W0x G.H_W0X).mono (by omega)
  have zx' : Tok R zx P.ZA0 (fun _ => true) := (V.H_ZA.fifo P.Wzx G.H_WZX).mono (by omega)
  have CX : CEl j0x zx rst xa qa (fun t => c2B (j0x t) (zx t) (qa t) (rst t)) P.Lxa P.wxal P.wxah :=
    ⟨fun t => c2_spec _ _ _ _, G.H_UXA, G.H_UXA_FB, G.H_UXA_POS⟩
  have nx := cel_node CX (cel_run CX ax zx' V.H_RST_HI V.H_RST_LO (Nat.le_refl R) r11 u5 u6 TM.H_DEP_XA)
  have xk : Tok P.Tx xak P.XA (fun k => !P.sv k) :=
    ((nx.fifo P.Wxa G.H_WXA).gcongr (fun k => by simp))
  have ay : Tok R j1y P.A1 P.sv := (j1E.fifo P.W1y G.H_W1Y).mono (by omega)
  have zy' : Tok R zy P.ZA1 (fun _ => true) := (V.H_ZA.fifo P.Wzy G.H_WZY).mono (by omega)
  have CY : CEl j1y zy rst ya qb (fun t => c2B (j1y t) (zy t) (qb t) (rst t)) P.Lya P.wyal P.wyah :=
    ⟨fun t => c2_spec _ _ _ _, G.H_UYA, G.H_UYA_FB, G.H_UYA_POS⟩
  have ny := cel_node CY (cel_run CY ay zy' V.H_RST_HI V.H_RST_LO (Nat.le_refl R) r12 u7 u8 TM.H_DEP_YA)
  have yk : Tok P.Ty yak P.YA P.sv :=
    ((ny.fifo P.Wya G.H_WYA).gcongr (fun k => by simp))
  refine ⟨j0E, j1E, zt, xk, xk.reindex V.H_ENUM0, yk, yk.reindex V.H_ENUM1, fun m => ?_,
    fun m => ?_, fun j => ?_⟩
  · have e := E_rx0 V.H_ENUM0 (2 * m); rw [rx_e] at e; rw [e]
    have := P.Lj0.fst_ge (P.c0 (2 * m))
    have hd : P.D0 (2 * m) = P.C0 (2 * P.κ0 m) := rx_e _ _ m
    unfold MuxRun.τ0 MuxRun.c0 at *; omega
  · have e := E_rx1 V.H_ENUM1 (2 * m); rw [rx_e] at e; rw [e]
    have := P.Lj1.fst_ge (P.c1 (2 * m))
    have hd : P.D1 (2 * m) = P.C1 (2 * P.κ1 m) := rx_e _ _ m
    unfold MuxRun.τ1 MuxRun.c1 at *; omega
  · unfold MuxRun.XA MuxRun.YA MuxRun.cx MuxRun.cy MuxRun.ZA0 MuxRun.ZA1
    have := P.Wzx.fst_ge (P.ζ j); have := P.Wzy.fst_ge (P.ζ j)
    have := P.Lxa.fst_ge (max (P.A0 j) (P.Wzx.fst (P.ζ j)))
    have := P.Wxa.fst_ge (P.Lxa.fst (max (P.A0 j) (P.Wzx.fst (P.ζ j))))
    have := P.Lya.fst_ge (max (P.A1 j) (P.Wzy.fst (P.ζ j)))
    have := P.Wya.fst_ge (P.Lya.fst (max (P.A1 j) (P.Wzy.fst (P.ζ j))))
    omega

end mux

/-! ## 4. `bd_merge`

`cells/rtl/bd_merge.v`:

    uor: LUT2 E (x_req, y_req) -> either;  udly: bd_delay (either -> z_req)
    uxa: bd_c2 (x_req, z_ack) -> x_ack;     uya: bd_c2 (y_req, z_ack) -> y_ack
    usel: LUT2 E (x_req, x_ack) -> sel      (data select; not covered here)

Merged token `k` belongs to client x when `sv k = false`, y otherwise. The
cell's obligation (header: "the second input cannot assert until the first
transaction has fully completed", **H_MERGE_SEQ**) is, in timed form, that
the two clients' requests are ONE sequence of non-overlapping four-phase
transactions on common edges `ρ` (`H_X`, `H_Y`), plus the event-time
inequalities of `MergeTiming` (which carry the "fully completed" part: the
next request may reach a C-element only after the previous z_ack fall has
crossed it and its loop). -/

structure MergeRun where
  /-- wires `x_req → uor.I0`, `y_req → uor.I1` -/
  Wxo : Ret
  Wyo : Ret
  Lor : Ret
  Dz : Ret
  /-- wires `x_req → uxa.I0`, `y_req → uya.I0` -/
  Wxc : Ret
  Wyc : Ret
  Wzx : Ret
  Wzy : Ret
  Lxa : Ret
  Lya : Ret
  wxal : Nat
  wxah : Nat
  wyal : Nat
  wyah : Nat
  Wxa : Ret
  Wya : Ret
  /-- the merged request edges (owner `sv k`) and the server's acknowledge edges -/
  ρ : Nat → Nat
  ζ : Nat → Nat
  sv : Nat → Bool

namespace MergeRun
variable (P : MergeRun)
def XO (j : Nat) : Nat := P.Wxo.fst (P.ρ j)
def YO (j : Nat) : Nat := P.Wyo.fst (P.ρ j)
def Z (j : Nat) : Nat := P.Dz.fst (P.Lor.fst (orEdges (fun k => !P.sv k) P.XO P.YO j))
def AX (j : Nat) : Nat := P.Wxc.fst (P.ρ j)
def AY (j : Nat) : Nat := P.Wyc.fst (P.ρ j)
def ZA0 (j : Nat) : Nat := P.Wzx.fst (P.ζ j)
def ZA1 (j : Nat) : Nat := P.Wzy.fst (P.ζ j)
def cx (j : Nat) : Nat := max (P.AX j) (P.ZA0 j)
def cy (j : Nat) : Nat := max (P.AY j) (P.ZA1 j)
def XA (j : Nat) : Nat := P.Wxa.fst (P.Lxa.fst (P.cx j))
def YA (j : Nat) : Nat := P.Wya.fst (P.Lya.fst (P.cy j))
def Tz : Nat := P.Wxo.hi + P.Wyo.hi + P.Lor.hi + P.Dz.hi
def Tx : Nat := P.Lxa.hi + P.Wxa.hi
def Ty : Nat := P.Lya.hi + P.Wya.hi
end MergeRun

structure MergeGates (P : MergeRun) (rst x y za xo yo ei zr xc yc zx zy xa qa ya qb xak yak : Trace) :
    Prop where
  H_WXO : ∀ t, P.Wxo.hi ≤ t → xo t = x (P.Wxo.σ t)
  H_WYO : ∀ t, P.Wyo.hi ≤ t → yo t = y (P.Wyo.σ t)
  /-- **H_LUT_FIFO** for `uor` (`4'hE`). -/
  H_UOR : ∀ t, P.Lor.hi ≤ t → ei t = or2B (xo (P.Lor.σ t)) (yo (P.Lor.σ t))
  /-- **H_LINE_FIFO** for `bd_delay`. -/
  H_DZ : ∀ t, P.Dz.hi ≤ t → zr t = ei (P.Dz.σ t)
  H_WXC : ∀ t, P.Wxc.hi ≤ t → xc t = x (P.Wxc.σ t)
  H_WYC : ∀ t, P.Wyc.hi ≤ t → yc t = y (P.Wyc.σ t)
  H_WZX : ∀ t, P.Wzx.hi ≤ t → zx t = za (P.Wzx.σ t)
  H_WZY : ∀ t, P.Wzy.hi ≤ t → zy t = za (P.Wzy.σ t)
  /-- **H_LUT_FIFO** for `uxa`/`uya`, `bd_c2` REAL INIT. -/
  H_UXA : ∀ t, P.Lxa.hi ≤ t →
    xa t = c2B (xc (P.Lxa.σ t)) (zx (P.Lxa.σ t)) (qa (P.Lxa.σ t)) (rst (P.Lxa.σ t))
  H_UXA_FB : CElemTiming.WinDelay P.wxal P.wxah xa qa
  H_UXA_POS : 1 ≤ P.Lxa.lo + P.wxal
  H_UYA : ∀ t, P.Lya.hi ≤ t →
    ya t = c2B (yc (P.Lya.σ t)) (zy (P.Lya.σ t)) (qb (P.Lya.σ t)) (rst (P.Lya.σ t))
  H_UYA_FB : CElemTiming.WinDelay P.wyal P.wyah ya qb
  H_UYA_POS : 1 ≤ P.Lya.lo + P.wyal
  H_WXA : ∀ t, P.Wxa.hi ≤ t → xak t = xa (P.Wxa.σ t)
  H_WYA : ∀ t, P.Wya.hi ≤ t → yak t = ya (P.Wya.σ t)

structure MergeEnv (P : MergeRun) (rst x y za : Trace) (R : Nat) : Prop where
  H_RST_HI : ∀ t, t < R → rst t = true
  H_RST_LO : ∀ t, R ≤ t → rst t = false
  /-- **H_MERGE_SEQ** (shape): x's and y's requests are the two halves of one
  interleaved sequence of four-phase transactions. JSON: `bd_merge.seq`. -/
  H_X : Tok 0 x P.ρ (fun k => !P.sv k)
  H_Y : Tok 0 y P.ρ P.sv
  H_ZA : Tok 0 za P.ζ (fun _ => true)

structure MergeTiming (P : MergeRun) (R : Nat) : Prop where
  H_RST_LONG : P.Wxc.hi ≤ R ∧ P.Wyc.hi ≤ R ∧ P.Wzx.hi ≤ R ∧ P.Wzy.hi ≤ R ∧
    P.Lxa.hi + P.wxah ≤ R ∧ P.Lya.hi + P.wyah ≤ R
  H_RST_EARLY : R ≤ P.AX 0 ∧ R ≤ P.ZA0 0 ∧ R ≤ P.AY 0 ∧ R ≤ P.ZA1 0
  /-- **H_OR_SKEW** at uor's pins. JSON: none (reported missing). -/
  H_OR_SKEW : ∀ j, P.XO j ≤ P.YO (j + 1) ∧ P.YO j ≤ P.XO (j + 1)
  /-- **H_DEP_XA / H_DEP_YA**: the acknowledge C-elements' env latency. The
  instance `cx (2k+1) + Lxa.hi + wxah ≤ AX (2k+2)` (next request, of either
  client, reaches uxa only after z_ack's fall crossed uxa's loop) is the
  timed content of H_MERGE_SEQ's "fully completed" and of the
  `z_ack -> {uxa, uya}` isochronic fork; against `ZA0 (j+1)` it is
  `bd_merge.uxa_feedback` / `bd_c2.env_latency`. -/
  H_DEP_XA : ∀ j, P.cx j + P.Lxa.hi + P.wxah ≤ P.AX (j + 1) ∧ P.cx j + P.Lxa.hi + P.wxah ≤ P.ZA0 (j + 1)
  H_DEP_YA : ∀ j, P.cy j + P.Lya.hi + P.wyah ≤ P.AY (j + 1) ∧ P.cy j + P.Lya.hi + P.wyah ≤ P.ZA1 (j + 1)

/-- **`merge_ok`: the merge meets its handshake spec for every token.** The
server sees exactly one transaction per merged token (`z_req`), and each
server transaction acknowledges exactly the client that requested it
(`x_ack` pulses exactly in x's tokens, `y_ack` in y's), each acknowledge
rising only after the server's. -/
theorem merge_ok {P : MergeRun} {R : Nat} {rst x y za xo yo ei zr xc yc zx zy xa qa ya qb xak yak : Trace}
    (G : MergeGates P rst x y za xo yo ei zr xc yc zx zy xa qa ya qb xak yak)
    (V : MergeEnv P rst x y za R) (TM : MergeTiming P R) :
    Tok P.Tz zr P.Z (fun _ => true) ∧
    Tok P.Tx xak P.XA (fun k => !P.sv k) ∧ Tok P.Ty yak P.YA P.sv ∧
    (∀ j, P.ρ j ≤ P.Z j ∧ P.ζ j ≤ P.XA j ∧ P.ζ j ≤ P.YA j) := by
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := TM.H_RST_LONG
  obtain ⟨u1, u2, u3, u4⟩ := TM.H_RST_EARLY
  have p0 : Tok (P.Wxo.hi + P.Wyo.hi) xo P.XO (fun k => !P.sv k) :=
    (V.H_X.fifo P.Wxo G.H_WXO).mono (by omega)
  have p1 : Tok (P.Wxo.hi + P.Wyo.hi) yo P.YO (fun k => !(!P.sv k)) :=
    ((V.H_Y.fifo P.Wyo G.H_WYO).mono (by omega)).gcongr (fun k => by simp)
  have o := or_tok p0 p1 (fun j => (TM.H_OR_SKEW j).1) (fun j => (TM.H_OR_SKEW j).2)
  have zt := (o.fifo P.Lor (y := ei) (fun t ht => by rw [G.H_UOR t ht, or2_spec])).fifo P.Dz G.H_DZ
  have ax : Tok R xc P.AX (fun k => !P.sv k) := (V.H_X.fifo P.Wxc G.H_WXC).mono (by omega)
  have zx' : Tok R zx P.ZA0 (fun _ => true) := (V.H_ZA.fifo P.Wzx G.H_WZX).mono (by omega)
  have CX : CEl xc zx rst xa qa (fun t => c2B (xc t) (zx t) (qa t) (rst t)) P.Lxa P.wxal P.wxah :=
    ⟨fun t => c2_spec _ _ _ _, G.H_UXA, G.H_UXA_FB, G.H_UXA_POS⟩
  have nx := cel_node CX (cel_run CX ax zx' V.H_RST_HI V.H_RST_LO (Nat.le_refl R) r5 u1 u2 TM.H_DEP_XA)
  have ay : Tok R yc P.AY P.sv := (V.H_Y.fifo P.Wyc G.H_WYC).mono (by omega)
  have zy' : Tok R zy P.ZA1 (fun _ => true) := (V.H_ZA.fifo P.Wzy G.H_WZY).mono (by omega)
  have CY : CEl yc zy rst ya qb (fun t => c2B (yc t) (zy t) (qb t) (rst t)) P.Lya P.wyal P.wyah :=
    ⟨fun t => c2_spec _ _ _ _, G.H_UYA, G.H_UYA_FB, G.H_UYA_POS⟩
  have ny := cel_node CY (cel_run CY ay zy' V.H_RST_HI V.H_RST_LO (Nat.le_refl R) r6 u3 u4 TM.H_DEP_YA)
  refine ⟨zt, (nx.fifo P.Wxa G.H_WXA).gcongr (fun k => by simp),
    (ny.fifo P.Wya G.H_WYA).gcongr (fun k => by simp), fun j => ⟨?_, ?_, ?_⟩⟩
  · unfold MergeRun.Z orEdges MergeRun.XO MergeRun.YO
    have := P.Wxo.fst_ge (P.ρ j); have := P.Wyo.fst_ge (P.ρ j)
    split
    · have := P.Lor.fst_ge (P.Wxo.fst (P.ρ j)); have := P.Dz.fst_ge (P.Lor.fst (P.Wxo.fst (P.ρ j)))
      omega
    · have := P.Lor.fst_ge (P.Wyo.fst (P.ρ j)); have := P.Dz.fst_ge (P.Lor.fst (P.Wyo.fst (P.ρ j)))
      omega
  · unfold MergeRun.XA MergeRun.cx MergeRun.ZA0
    have := P.Wzx.fst_ge (P.ζ j)
    have := P.Lxa.fst_ge (max (P.AX j) (P.Wzx.fst (P.ζ j)))
    have := P.Wxa.fst_ge (P.Lxa.fst (max (P.AX j) (P.Wzx.fst (P.ζ j))))
    omega
  · unfold MergeRun.YA MergeRun.cy MergeRun.ZA1
    have := P.Wzy.fst_ge (P.ζ j)
    have := P.Lya.fst_ge (max (P.AY j) (P.Wzy.fst (P.ζ j)))
    have := P.Wya.fst_ge (P.Lya.fst (max (P.AY j) (P.Wzy.fst (P.ζ j))))
    omega

/-! ## 5. `bd_mux`: the event-form obligations from port-level causality

`MuxTiming`'s fields are inequalities between derived event times. Here the
four partners are given a port-level causal model (`MuxCausal`: each reacts
to the edge it sees, at least `E*` later), and every field of `MuxTiming`
except reset sequencing is DERIVED from per-arc static inequalities
(`MuxStatic`), of the shape the routed-netlist checker evaluates. `lj`, `wc`,
`wo` are lower bounds on the two joins' arcs, the two ctl_req wires and the
two join→uor wires (the slower path of a pair need not be named). -/

/-- **Port-level causality of the mux's four partners.** -/
structure MuxCausal (P : MuxRun) (Wzc : Ret) (Ex Ey Ec Es : Nat) : Prop where
  /-- x drops (raises) its request only `Ex` after seeing x_ack rise (fall). -/
  H_XC_FALL : ∀ m, P.XA (2 * P.κ0 m) + Ex ≤ P.ξ (2 * m + 1)
  H_XC_RISE : ∀ m, P.XA (2 * P.κ0 m + 1) + Ex ≤ P.ξ (2 * m + 2)
  H_YC_FALL : ∀ m, P.YA (2 * P.κ1 m) + Ey ≤ P.η (2 * m + 1)
  H_YC_RISE : ∀ m, P.YA (2 * P.κ1 m + 1) + Ey ≤ P.η (2 * m + 2)
  /-- The control sender moves ctl_req `Ec` after seeing ctl_ack (= z_ack,
  through its wire `Wzc`) move. -/
  H_CTL_C : ∀ j, Wzc.fst (P.ζ j) + Ec ≤ P.γ (j + 1)
  /-- The server moves z_ack `Es` after z_req's edge reached it. -/
  H_SRV : ∀ j, P.Z j + Es ≤ P.ζ j
  /-- Edges are after time 0 (avoids the truncated-subtraction corner). -/
  H_POS : ∀ j, 1 ≤ P.γ j

/-- **Static per-arc obligations.** `Kz` = min delay from a join node edge to
the server's z_ack edge; `Kc` = min delay from a z_ack edge to the next join
node edge through the control sender. -/
structure MuxStatic (P : MuxRun) (Wzc : Ret) (Ex Ey Ec Es lj wc wo : Nat) : Prop where
  H_LJ : lj ≤ P.Lj0.lo ∧ lj ≤ P.Lj1.lo
  H_WC : wc ≤ P.Wc0.lo ∧ wc ≤ P.Wc1.lo
  H_WO : wo ≤ P.W0o.lo ∧ wo ≤ P.W1o.lo
  /-- **S_J_REQ** (join env latency through the client; `bd_c2.env_latency` form). -/
  S_J0_X : P.Lj0.hi + P.wj0h ≤ P.Lj0.lo + P.W0x.lo + P.Lxa.lo + P.Wxa.lo + Ex + P.Wx.lo
  S_J1_Y : P.Lj1.hi + P.wj1h ≤ P.Lj1.lo + P.W1y.lo + P.Lya.lo + P.Wya.lo + Ey + P.Wy.lo
  /-- **S_J_CTL** (join env latency through the server and the control sender). -/
  S_J0_C : P.Lj0.hi + P.wj0h ≤ P.Lj0.lo + (wo + P.Lor.lo + P.Dz.lo + Es) + Wzc.lo + Ec + P.Wc0.lo
  S_J1_C : P.Lj1.hi + P.wj1h ≤ P.Lj1.lo + (wo + P.Lor.lo + P.Dz.lo + Es) + Wzc.lo + Ec + P.Wc1.lo
  /-- **S_OR_SKEW**: uor's pin skew below one full control round trip. -/
  S_OR : P.W0o.hi ≤ (wo + P.Lor.lo + P.Dz.lo + Es) + (Wzc.lo + Ec + wc + lj) + P.W1o.lo ∧
    P.W1o.hi ≤ (wo + P.Lor.lo + P.Dz.lo + Es) + (Wzc.lo + Ec + wc + lj) + P.W0o.lo
  /-- **S_ZA_FORK** (`z_ack -> {uxa, uya, ctl sender}`): z_ack's edge reaches
  the acknowledge C-element and its loop settles before the next join edge
  (launched by the same z_ack edge through the control sender) reaches it. -/
  S_XA_FORK : P.Wzx.hi + (P.Lxa.hi + P.wxah) ≤ (Wzc.lo + Ec + wc + lj) + P.W0x.lo
  S_YA_FORK : P.Wzy.hi + (P.Lya.hi + P.wyah) ≤ (Wzc.lo + Ec + wc + lj) + P.W1y.lo
  /-- **S_RTZ** = H_MUX_RTZ (`bd_mux.uxa_rtz_env`, `uya_rtz_env`): z_ack's
  pulse at uxa (either polarity) outlasts uxa's LUT + feedback loop plus the
  z_ack wire's spread. -/
  S_XA_RTZ : P.Wzx.hi + (P.Lxa.hi + P.wxah) ≤ P.Wzx.lo + (Wzc.lo + Ec + wc + lj) + (wo + P.Lor.lo + P.Dz.lo + Es)
  S_YA_RTZ : P.Wzy.hi + (P.Lya.hi + P.wyah) ≤ P.Wzy.lo + (Wzc.lo + Ec + wc + lj) + (wo + P.Lor.lo + P.Dz.lo + Es)
  /-- **S_J_ACK**: j's edge at uxa outlasts its loop until the next j edge
  (one round trip) and until the next z_ack edge. -/
  S_XA_J : P.W0x.hi + (P.Lxa.hi + P.wxah) ≤ (wo + P.Lor.lo + P.Dz.lo + Es) + (Wzc.lo + Ec + wc + lj) + P.W0x.lo ∧
    P.W0x.hi + (P.Lxa.hi + P.wxah) ≤ 2 * (wo + P.Lor.lo + P.Dz.lo + Es) + (Wzc.lo + Ec + wc + lj) + P.Wzx.lo
  S_YA_J : P.W1y.hi + (P.Lya.hi + P.wyah) ≤ (wo + P.Lor.lo + P.Dz.lo + Es) + (Wzc.lo + Ec + wc + lj) + P.W1y.lo ∧
    P.W1y.hi + (P.Lya.hi + P.wyah) ≤ 2 * (wo + P.Lor.lo + P.Dz.lo + Es) + (Wzc.lo + Ec + wc + lj) + P.Wzy.lo

section muxstatic
variable {P : MuxRun} {Wzc : Ret} {Ex Ey Ec Es lj wc wo : Nat}

theorem fl (r : Ret) {c : Nat} (hc : 1 ≤ c) : c + r.lo ≤ r.fst c := r.fst_lo hc

/-- The selected join's node edge follows its ctl_req edge by the join arc. -/
theorem C_le_E (hE0 : Enum (fun k => !P.sv k) P.κ0) (hE1 : Enum P.sv P.κ1) (hpos : ∀ j, 1 ≤ P.γ j)
    (j : Nat) : (P.sv (j / 2) = true → P.C1 j + P.Lj1.lo ≤ P.E j ∧ 1 ≤ P.C1 j) ∧
      (P.sv (j / 2) = false → P.C0 j + P.Lj0.lo ≤ P.E j ∧ 1 ≤ P.C0 j) := by
  have hj : 2 * (j / 2) + j % 2 = j := by omega
  constructor
  · intro hs
    have hk := κ_idx hE1 (k := j / 2) hs
    have hD : P.D1 (2 * idx P.κ1 (j / 2) + j % 2) = P.C1 j := by
      unfold MuxRun.D1 rx
      rw [show (2 * idx P.κ1 (j / 2) + j % 2) / 2 = idx P.κ1 (j / 2) by omega,
        show (2 * idx P.κ1 (j / 2) + j % 2) % 2 = j % 2 by omega, hk, hj]
    have c1 : 1 ≤ P.C1 j := by have := P.Wc1.fst_ge (P.γ j); have := hpos j; unfold MuxRun.C1; omega
    refine ⟨?_, c1⟩
    unfold MuxRun.E; rw [hs]; simp only [ite_true]
    unfold MuxRun.τ1
    have := fl P.Lj1 (c := P.c1 (2 * idx P.κ1 (j / 2) + j % 2)) (by unfold MuxRun.c1; omega)
    unfold MuxRun.c1 at *; omega
  · intro hs
    have hk := κ_idx hE0 (k := j / 2) (by simp [hs])
    have hD : P.D0 (2 * idx P.κ0 (j / 2) + j % 2) = P.C0 j := by
      unfold MuxRun.D0 rx
      rw [show (2 * idx P.κ0 (j / 2) + j % 2) / 2 = idx P.κ0 (j / 2) by omega,
        show (2 * idx P.κ0 (j / 2) + j % 2) % 2 = j % 2 by omega, hk, hj]
    have c1 : 1 ≤ P.C0 j := by have := P.Wc0.fst_ge (P.γ j); have := hpos j; unfold MuxRun.C0; omega
    refine ⟨?_, c1⟩
    unfold MuxRun.E; rw [hs]; simp only [Bool.false_eq_true, ite_false]
    unfold MuxRun.τ0
    have := fl P.Lj0 (c := P.c0 (2 * idx P.κ0 (j / 2) + j % 2)) (by unfold MuxRun.c0; omega)
    unfold MuxRun.c0 at *; omega

theorem γ_le_E (hE0 : Enum (fun k => !P.sv k) P.κ0) (hE1 : Enum P.sv P.κ1) (hpos : ∀ j, 1 ≤ P.γ j)
    (S : MuxStatic P Wzc Ex Ey Ec Es lj wc wo) (j : Nat) : P.γ j + wc + lj ≤ P.E j ∧ 1 ≤ P.E j := by
  have h := C_le_E hE0 hE1 hpos j
  have := S.H_LJ; have := S.H_WC; have := hpos j
  cases hs : P.sv (j / 2)
  · have := (h.2 hs).1
    have := fl P.Wc0 (hpos j); unfold MuxRun.C0 at *; omega
  · have := (h.1 hs).1
    have := fl P.Wc1 (hpos j); unfold MuxRun.C1 at *; omega

theorem E_le_ζ (hE0 : Enum (fun k => !P.sv k) P.κ0) (hE1 : Enum P.sv P.κ1)
    (Cs : MuxCausal P Wzc Ex Ey Ec Es) (S : MuxStatic P Wzc Ex Ey Ec Es lj wc wo) (j : Nat) :
    P.E j + (wo + P.Lor.lo + P.Dz.lo + Es) ≤ P.ζ j := by
  have hE := (γ_le_E hE0 hE1 Cs.H_POS S j).2
  have hs := Cs.H_SRV j
  have := S.H_WO
  unfold MuxRun.Z orEdges at hs
  unfold MuxRun.O0 MuxRun.O1 at hs
  split at hs
  · have a := fl P.W0o hE
    have b := fl P.Lor (c := P.W0o.fst (P.E j)) (by omega)
    have c := fl P.Dz (c := P.Lor.fst (P.W0o.fst (P.E j))) (by omega)
    omega
  · have a := fl P.W1o hE
    have b := fl P.Lor (c := P.W1o.fst (P.E j)) (by omega)
    have c := fl P.Dz (c := P.Lor.fst (P.W1o.fst (P.E j))) (by omega)
    omega

theorem ζ_le_E (hE0 : Enum (fun k => !P.sv k) P.κ0) (hE1 : Enum P.sv P.κ1)
    (Cs : MuxCausal P Wzc Ex Ey Ec Es) (S : MuxStatic P Wzc Ex Ey Ec Es lj wc wo) (j : Nat) :
    P.ζ j + (Wzc.lo + Ec + wc + lj) ≤ P.E (j + 1) := by
  have h1 := Cs.H_CTL_C j
  have hz : 1 ≤ P.ζ j := by
    have := E_le_ζ hE0 hE1 Cs S j; have := (γ_le_E hE0 hE1 Cs.H_POS S j).2; omega
  have h2 := fl Wzc hz
  have h3 := (γ_le_E hE0 hE1 Cs.H_POS S (j + 1)).1
  omega

theorem γ_mono (hE0 : Enum (fun k => !P.sv k) P.κ0) (hE1 : Enum P.sv P.κ1)
    (Cs : MuxCausal P Wzc Ex Ey Ec Es) (S : MuxStatic P Wzc Ex Ey Ec Es lj wc wo) :
    ∀ a b, a ≤ b → P.γ a ≤ P.γ b := by
  have step : ∀ j, P.γ j ≤ P.γ (j + 1) := by
    intro j
    have := (γ_le_E hE0 hE1 Cs.H_POS S j).1
    have := E_le_ζ hE0 hE1 Cs S j
    have := Cs.H_CTL_C j
    have := Wzc.fst_ge (P.ζ j)
    omega
  intro a b hab
  induction b with
  | zero => have : a = 0 := by omega
            subst this; omega
  | succ b ih =>
    by_cases h' : a ≤ b
    · have := ih h'; have := step b; omega
    · have : a = b + 1 := by omega
      subst this; omega

/-- **The event-form obligations follow from port-level causality and the
static per-arc inequalities.** Reset sequencing (`H_RST_LONG`,
`H_RST_EARLY`) stays as given. -/
theorem mux_timing_of_static {R : Nat} (hE0 : Enum (fun k => !P.sv k) P.κ0) (hE1 : Enum P.sv P.κ1)
    (Cs : MuxCausal P Wzc Ex Ey Ec Es) (S : MuxStatic P Wzc Ex Ey Ec Es lj wc wo)
    (hRL : P.Wx.hi ≤ R ∧ P.Wy.hi ≤ R ∧ P.Wc0.hi ≤ R ∧ P.Wc1.hi ≤ R ∧
      P.Lj0.hi + P.wj0h ≤ R ∧ P.Lj1.hi + P.wj1h ≤ R ∧ P.Lj0.hi + P.W0x.hi ≤ R ∧
      P.Lj1.hi + P.W1y.hi ≤ R ∧ P.Wzx.hi ≤ R ∧ P.Wzy.hi ≤ R ∧ P.Lxa.hi + P.wxah ≤ R ∧
      P.Lya.hi + P.wyah ≤ R)
    (hRE : R ≤ P.Xp 0 ∧ R ≤ P.D0 0 ∧ R ≤ P.Yp 0 ∧ R ≤ P.D1 0 ∧ R ≤ P.A0 0 ∧
      R ≤ P.ZA0 0 ∧ R ≤ P.A1 0 ∧ R ≤ P.ZA1 0) :
    MuxTiming P R := by
  have EZ := E_le_ζ hE0 hE1 Cs S
  have ZE := ζ_le_E hE0 hE1 Cs S
  have GE := γ_le_E hE0 hE1 Cs.H_POS S
  have GM := γ_mono hE0 hE1 Cs S
  have hLJ := S.H_LJ; have hWC := S.H_WC; have hWO := S.H_WO
  -- the joins' node edges in terms of E
  have e0 : ∀ j, P.τ0 j = P.E (2 * P.κ0 (j / 2) + j % 2) := fun j => by
    have := E_rx0 hE0 j; unfold rx at this; exact this.symm
  have e1 : ∀ j, P.τ1 j = P.E (2 * P.κ1 (j / 2) + j % 2) := fun j => by
    have := E_rx1 hE1 j; unfold rx at this; exact this.symm
  -- an acknowledge at its client follows the join edge
  have XAge : ∀ i, P.E i + P.W0x.lo + P.Lxa.lo + P.Wxa.lo ≤ P.XA i := by
    intro i
    have hE := (GE i).2
    have a := fl P.W0x hE
    have hcA : P.A0 i ≤ P.cx i := by unfold MuxRun.cx; omega
    have hA : P.A0 i = P.W0x.fst (P.E i) := rfl
    have b := fl P.Lxa (c := P.cx i) (by omega)
    have c := fl P.Wxa (c := P.Lxa.fst (P.cx i)) (by omega)
    show _ ≤ P.Wxa.fst (P.Lxa.fst (P.cx i)); omega
  have YAge : ∀ i, P.E i + P.W1y.lo + P.Lya.lo + P.Wya.lo ≤ P.YA i := by
    intro i
    have hE := (GE i).2
    have a := fl P.W1y hE
    have hcA : P.A1 i ≤ P.cy i := by unfold MuxRun.cy; omega
    have hA : P.A1 i = P.W1y.fst (P.E i) := rfl
    have b := fl P.Lya (c := P.cy i) (by omega)
    have c := fl P.Wya (c := P.Lya.fst (P.cy i)) (by omega)
    show _ ≤ P.Wya.fst (P.Lya.fst (P.cy i)); omega
  -- the join's phase start and its node edge
  have t0 : ∀ j, P.c0 j + P.Lj0.lo ≤ P.τ0 j ∧ 1 ≤ P.c0 j := by
    intro j
    have hd : P.D0 j = P.C0 (2 * P.κ0 (j / 2) + j % 2) := rfl
    have := P.Wc0.fst_ge (P.γ (2 * P.κ0 (j / 2) + j % 2)); have := Cs.H_POS (2 * P.κ0 (j / 2) + j % 2)
    have c1 : 1 ≤ P.c0 j := by unfold MuxRun.c0 MuxRun.C0 at *; omega
    exact ⟨fl P.Lj0 c1, c1⟩
  have t1 : ∀ j, P.c1 j + P.Lj1.lo ≤ P.τ1 j ∧ 1 ≤ P.c1 j := by
    intro j
    have hd : P.D1 j = P.C1 (2 * P.κ1 (j / 2) + j % 2) := rfl
    have := P.Wc1.fst_ge (P.γ (2 * P.κ1 (j / 2) + j % 2)); have := Cs.H_POS (2 * P.κ1 (j / 2) + j % 2)
    have c1 : 1 ≤ P.c1 j := by unfold MuxRun.c1 MuxRun.C1 at *; omega
    exact ⟨fl P.Lj1 c1, c1⟩
  refine ⟨hRL, hRE, fun j => ⟨?_, ?_⟩, fun j => ⟨?_, ?_⟩, fun k => ?_, fun j => ⟨?_, ?_⟩,
    fun j => ⟨?_, ?_⟩, fun j => ⟨?_, ?_⟩⟩
  · -- uj0, through x
    have hXA : P.XA (2 * P.κ0 (j / 2) + j % 2) + Ex ≤ P.ξ (j + 1) := by
      rcases Nat.mod_two_eq_zero_or_one j with hj | hj
      · obtain ⟨m, rfl⟩ : ∃ m, j = 2 * m := ⟨j / 2, by omega⟩
        have := Cs.H_XC_FALL m
        rw [show 2 * m / 2 = m by omega, show 2 * m % 2 = 0 by omega, Nat.add_zero]; exact this
      · obtain ⟨m, rfl⟩ : ∃ m, j = 2 * m + 1 := ⟨j / 2, by omega⟩
        have := Cs.H_XC_RISE m
        rw [show (2 * m + 1) / 2 = m by omega, show (2 * m + 1) % 2 = 1 by omega]; exact this
    have := XAge (2 * P.κ0 (j / 2) + j % 2)
    have hpos : 1 ≤ P.ξ (j + 1) := by have := (GE (2 * P.κ0 (j / 2) + j % 2)).2; omega
    have := fl P.Wx hpos
    have : P.Xp (j + 1) = P.Wx.fst (P.ξ (j + 1)) := rfl
    have := (t0 j).1; have := e0 j; have := S.S_J0_X
    omega
  · -- uj0, through the server and the control sender
    have hk : P.D0 (j + 1) = P.C0 (2 * P.κ0 ((j + 1) / 2) + (j + 1) % 2) := rfl
    have hge : 2 * P.κ0 (j / 2) + j % 2 + 1 ≤ 2 * P.κ0 ((j + 1) / 2) + (j + 1) % 2 := by
      rcases Nat.mod_two_eq_zero_or_one j with hj | hj
      · rw [show (j + 1) / 2 = j / 2 by omega]; omega
      · have := hE0.mono (j / 2); rw [show (j + 1) / 2 = j / 2 + 1 by omega]; omega
    have g := GM _ _ hge
    have hC := fl P.Wc0 (Cs.H_POS (2 * P.κ0 ((j + 1) / 2) + (j + 1) % 2))
    have hz := EZ (2 * P.κ0 (j / 2) + j % 2)
    have hc := Cs.H_CTL_C (2 * P.κ0 (j / 2) + j % 2)
    have hzz : 1 ≤ P.ζ (2 * P.κ0 (j / 2) + j % 2) := by
      have := (GE (2 * P.κ0 (j / 2) + j % 2)).2; omega
    have hw := fl Wzc hzz
    have := (t0 j).1; have := e0 j; have := S.S_J0_C
    unfold MuxRun.C0 at hk hC; omega
  · -- uj1, through y
    have hYA : P.YA (2 * P.κ1 (j / 2) + j % 2) + Ey ≤ P.η (j + 1) := by
      rcases Nat.mod_two_eq_zero_or_one j with hj | hj
      · obtain ⟨m, rfl⟩ : ∃ m, j = 2 * m := ⟨j / 2, by omega⟩
        have := Cs.H_YC_FALL m
        rw [show 2 * m / 2 = m by omega, show 2 * m % 2 = 0 by omega, Nat.add_zero]; exact this
      · obtain ⟨m, rfl⟩ : ∃ m, j = 2 * m + 1 := ⟨j / 2, by omega⟩
        have := Cs.H_YC_RISE m
        rw [show (2 * m + 1) / 2 = m by omega, show (2 * m + 1) % 2 = 1 by omega]; exact this
    have := YAge (2 * P.κ1 (j / 2) + j % 2)
    have hpos : 1 ≤ P.η (j + 1) := by have := (GE (2 * P.κ1 (j / 2) + j % 2)).2; omega
    have := fl P.Wy hpos
    have : P.Yp (j + 1) = P.Wy.fst (P.η (j + 1)) := rfl
    have := (t1 j).1; have := e1 j; have := S.S_J1_Y
    omega
  · -- uj1, through the server and the control sender
    have hk : P.D1 (j + 1) = P.C1 (2 * P.κ1 ((j + 1) / 2) + (j + 1) % 2) := rfl
    have hge : 2 * P.κ1 (j / 2) + j % 2 + 1 ≤ 2 * P.κ1 ((j + 1) / 2) + (j + 1) % 2 := by
      rcases Nat.mod_two_eq_zero_or_one j with hj | hj
      · rw [show (j + 1) / 2 = j / 2 by omega]; omega
      · have := hE1.mono (j / 2); rw [show (j + 1) / 2 = j / 2 + 1 by omega]; omega
    have g := GM _ _ hge
    have hC := fl P.Wc1 (Cs.H_POS (2 * P.κ1 ((j + 1) / 2) + (j + 1) % 2))
    have hz := EZ (2 * P.κ1 (j / 2) + j % 2)
    have hc := Cs.H_CTL_C (2 * P.κ1 (j / 2) + j % 2)
    have hzz : 1 ≤ P.ζ (2 * P.κ1 (j / 2) + j % 2) := by
      have := (GE (2 * P.κ1 (j / 2) + j % 2)).2; omega
    have hw := fl Wzc hzz
    have := (t1 j).1; have := e1 j; have := S.S_J1_C
    unfold MuxRun.C1 at hk hC; omega
  · -- H_CTL_SEQ
    have := ZE (2 * k + 1); have := EZ (2 * k + 1)
    have hc : Wzc.fst (P.ζ (2 * k + 1)) + Ec ≤ P.γ (2 * k + 2) := Cs.H_CTL_C (2 * k + 1)
    have := Wzc.fst_ge (P.ζ (2 * k + 1))
    have := P.Wc0.fst_ge (P.γ (2 * k + 2)); have := P.Wc1.fst_ge (P.γ (2 * k + 2))
    unfold MuxRun.C0 MuxRun.C1
    split <;> omega
  · -- H_OR_SKEW
    have := P.W0o.fst_le (P.E j); have := fl P.W1o (GE (j + 1)).2
    have := ZE j; have := EZ j; have := S.S_OR
    unfold MuxRun.O0 MuxRun.O1; omega
  · have := P.W1o.fst_le (P.E j); have := fl P.W0o (GE (j + 1)).2
    have := ZE j; have := EZ j; have := S.S_OR
    unfold MuxRun.O0 MuxRun.O1; omega
  · -- H_DEP_XA against the next j0 edge
    have := P.W0x.fst_le (P.E j); have := P.Wzx.fst_le (P.ζ j)
    have := fl P.W0x (GE (j + 1)).2
    have := ZE j; have := EZ j; have := S.S_XA_FORK; have := S.S_XA_J
    unfold MuxRun.cx MuxRun.A0 MuxRun.ZA0; omega
  · -- H_DEP_XA against the next z_ack edge (H_MUX_RTZ)
    have := P.W0x.fst_le (P.E j); have := P.Wzx.fst_le (P.ζ j)
    have hz1 : 1 ≤ P.ζ (j + 1) := by have := EZ (j + 1); have := (GE (j + 1)).2; omega
    have := fl P.Wzx hz1
    have := ZE j; have := EZ j; have := EZ (j + 1); have := S.S_XA_RTZ; have := S.S_XA_J
    unfold MuxRun.cx MuxRun.A0 MuxRun.ZA0; omega
  · have := P.W1y.fst_le (P.E j); have := P.Wzy.fst_le (P.ζ j)
    have := fl P.W1y (GE (j + 1)).2
    have := ZE j; have := EZ j; have := S.S_YA_FORK; have := S.S_YA_J
    unfold MuxRun.cy MuxRun.A1 MuxRun.ZA1; omega
  · have := P.W1y.fst_le (P.E j); have := P.Wzy.fst_le (P.ζ j)
    have hz1 : 1 ≤ P.ζ (j + 1) := by have := EZ (j + 1); have := (GE (j + 1)).2; omega
    have := fl P.Wzy hz1
    have := ZE j; have := EZ j; have := EZ (j + 1); have := S.S_YA_RTZ; have := S.S_YA_J
    unfold MuxRun.cy MuxRun.A1 MuxRun.ZA1; omega

/-- **`mux_ok_static`**: `mux_ok` with every timing obligation except reset
sequencing given as a per-arc static inequality, under port-level causal
partners. -/
theorem mux_ok_static {R : Nat} {rst x y ctl za xj yj cj0 cj1 sx0 sx1 j0 q0 j1 q1 e0 e1 ei zr j0x j1y
      zx zy xa qa ya qb xak yak : Trace}
    (G : MuxGates P rst x y ctl za xj yj cj0 cj1 sx0 sx1 j0 q0 j1 q1 e0 e1 ei zr j0x j1y zx zy xa qa
      ya qb xak yak)
    (V : MuxEnv P rst x y ctl za sx0 sx1 R) (Cs : MuxCausal P Wzc Ex Ey Ec Es)
    (S : MuxStatic P Wzc Ex Ey Ec Es lj wc wo)
    (hRL : P.Wx.hi ≤ R ∧ P.Wy.hi ≤ R ∧ P.Wc0.hi ≤ R ∧ P.Wc1.hi ≤ R ∧
      P.Lj0.hi + P.wj0h ≤ R ∧ P.Lj1.hi + P.wj1h ≤ R ∧ P.Lj0.hi + P.W0x.hi ≤ R ∧
      P.Lj1.hi + P.W1y.hi ≤ R ∧ P.Wzx.hi ≤ R ∧ P.Wzy.hi ≤ R ∧ P.Lxa.hi + P.wxah ≤ R ∧
      P.Lya.hi + P.wyah ≤ R)
    (hRE : R ≤ P.Xp 0 ∧ R ≤ P.D0 0 ∧ R ≤ P.Yp 0 ∧ R ≤ P.D1 0 ∧ R ≤ P.A0 0 ∧
      R ≤ P.ZA0 0 ∧ R ≤ P.A1 0 ∧ R ≤ P.ZA1 0) :
    Tok P.Tz zr P.Z (fun _ => true) ∧
    Tok P.Tx xak P.XA (fun k => !P.sv k) ∧ Tok P.Tx xak (rx P.XA P.κ0) (fun _ => true) ∧
    Tok P.Ty yak P.YA P.sv ∧ Tok P.Ty yak (rx P.YA P.κ1) (fun _ => true) := by
  have h := mux_ok G V (mux_timing_of_static V.H_ENUM0 V.H_ENUM1 Cs S hRL hRE)
  exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

end muxstatic

/-! ## 6. `bd_merge`: the event-form obligations from port-level causality -/

/-- **Port-level causality of the merge's partners.** `Own j` is the
acknowledge of token `j/2`'s owner at its pin. The owner drops its request
`Eo` after seeing its acknowledge rise; the NEXT requester (either client)
raises its request only `Eo` after the previous owner's acknowledge fell
(H_MERGE_SEQ, causal form); the server answers `Es` after z_req's edge. -/
structure MergeCausal (P : MergeRun) (Eo Es : Nat) : Prop where
  H_OWN : ∀ j, (if P.sv (j / 2) then P.YA j else P.XA j) + Eo ≤ P.ρ (j + 1)
  H_SRV : ∀ j, P.Z j + Es ≤ P.ζ j
  H_POS : ∀ j, 1 ≤ P.ρ j

/-- **Static per-arc obligations of the merge.** `Kz` = min request edge →
z_ack edge; `Ka` = min z_ack edge → next request edge (through an
acknowledge C-element and a client). -/
structure MergeStatic (P : MergeRun) (Eo Es wo wz la wa : Nat) : Prop where
  H_WO : wo ≤ P.Wxo.lo ∧ wo ≤ P.Wyo.lo
  H_WZ : wz ≤ P.Wzx.lo ∧ wz ≤ P.Wzy.lo
  H_LA : la ≤ P.Lxa.lo ∧ la ≤ P.Lya.lo
  H_WA : wa ≤ P.Wxa.lo ∧ wa ≤ P.Wya.lo
  /-- **S_OR_SKEW**. -/
  S_OR : P.Wxo.hi ≤ (wo + P.Lor.lo + P.Dz.lo + Es) + (wz + la + wa + Eo) + P.Wyo.lo ∧
    P.Wyo.hi ≤ (wo + P.Lor.lo + P.Dz.lo + Es) + (wz + la + wa + Eo) + P.Wxo.lo
  /-- **S_SEQ_FORK** (H_MERGE_SEQ's "fully completed", `z_ack -> {uxa, uya}`):
  z_ack's edge settles each acknowledge C-element's loop before the next
  request, launched through the other C-element and a client, reaches it. -/
  S_XA_FORK : P.Wzx.hi + (P.Lxa.hi + P.wxah) ≤ (wz + la + wa + Eo) + P.Wxc.lo
  S_YA_FORK : P.Wzy.hi + (P.Lya.hi + P.wyah) ≤ (wz + la + wa + Eo) + P.Wyc.lo
  /-- **S_ZA_PULSE** (`bd_merge.uxa_feedback`): z_ack's pulse at uxa outlasts
  the loop. -/
  S_XA_ZA : P.Wzx.hi + (P.Lxa.hi + P.wxah) ≤ P.Wzx.lo + (wz + la + wa + Eo) + (wo + P.Lor.lo + P.Dz.lo + Es)
  S_YA_ZA : P.Wzy.hi + (P.Lya.hi + P.wyah) ≤ P.Wzy.lo + (wz + la + wa + Eo) + (wo + P.Lor.lo + P.Dz.lo + Es)
  /-- **S_REQ_ACK**: a request edge at the C-element outlasts its loop. -/
  S_XA_R : P.Wxc.hi + (P.Lxa.hi + P.wxah) ≤ (wo + P.Lor.lo + P.Dz.lo + Es) + (wz + la + wa + Eo) + P.Wxc.lo ∧
    P.Wxc.hi + (P.Lxa.hi + P.wxah) ≤ 2 * (wo + P.Lor.lo + P.Dz.lo + Es) + (wz + la + wa + Eo) + P.Wzx.lo
  S_YA_R : P.Wyc.hi + (P.Lya.hi + P.wyah) ≤ (wo + P.Lor.lo + P.Dz.lo + Es) + (wz + la + wa + Eo) + P.Wyc.lo ∧
    P.Wyc.hi + (P.Lya.hi + P.wyah) ≤ 2 * (wo + P.Lor.lo + P.Dz.lo + Es) + (wz + la + wa + Eo) + P.Wzy.lo

theorem merge_timing_of_static {P : MergeRun} {R Eo Es wo wz la wa : Nat}
    (Cs : MergeCausal P Eo Es) (S : MergeStatic P Eo Es wo wz la wa)
    (hRL : P.Wxc.hi ≤ R ∧ P.Wyc.hi ≤ R ∧ P.Wzx.hi ≤ R ∧ P.Wzy.hi ≤ R ∧
      P.Lxa.hi + P.wxah ≤ R ∧ P.Lya.hi + P.wyah ≤ R)
    (hRE : R ≤ P.AX 0 ∧ R ≤ P.ZA0 0 ∧ R ≤ P.AY 0 ∧ R ≤ P.ZA1 0) : MergeTiming P R := by
  have hWO := S.H_WO; have hWZ := S.H_WZ; have hLA := S.H_LA; have hWA := S.H_WA
  -- request edge to z_ack edge
  have RZ : ∀ j, P.ρ j + (wo + P.Lor.lo + P.Dz.lo + Es) ≤ P.ζ j := by
    intro j
    have hs := Cs.H_SRV j; have hp := Cs.H_POS j
    unfold MergeRun.Z orEdges MergeRun.XO MergeRun.YO at hs
    split at hs
    · have a := fl P.Wxo hp
      have b := fl P.Lor (c := P.Wxo.fst (P.ρ j)) (by omega)
      have c := fl P.Dz (c := P.Lor.fst (P.Wxo.fst (P.ρ j))) (by omega)
      omega
    · have a := fl P.Wyo hp
      have b := fl P.Lor (c := P.Wyo.fst (P.ρ j)) (by omega)
      have c := fl P.Dz (c := P.Lor.fst (P.Wyo.fst (P.ρ j))) (by omega)
      omega
  -- z_ack edge to the next request edge
  have ZR : ∀ j, P.ζ j + (wz + la + wa + Eo) ≤ P.ρ (j + 1) := by
    intro j
    have ho := Cs.H_OWN j
    have hz : 1 ≤ P.ζ j := by have := RZ j; have := Cs.H_POS j; omega
    split at ho
    · have a := fl P.Wzy hz
      have hc : P.ZA1 j ≤ P.cy j := by unfold MergeRun.cy; omega
      have hZ : P.ZA1 j = P.Wzy.fst (P.ζ j) := rfl
      have b := fl P.Lya (c := P.cy j) (by omega)
      have c := fl P.Wya (c := P.Lya.fst (P.cy j)) (by omega)
      have hA : P.YA j = P.Wya.fst (P.Lya.fst (P.cy j)) := rfl
      omega
    · have a := fl P.Wzx hz
      have hc : P.ZA0 j ≤ P.cx j := by unfold MergeRun.cx; omega
      have hZ : P.ZA0 j = P.Wzx.fst (P.ζ j) := rfl
      have b := fl P.Lxa (c := P.cx j) (by omega)
      have c := fl P.Wxa (c := P.Lxa.fst (P.cx j)) (by omega)
      have hA : P.XA j = P.Wxa.fst (P.Lxa.fst (P.cx j)) := rfl
      omega
  refine ⟨hRL, hRE, fun j => ⟨?_, ?_⟩, fun j => ⟨?_, ?_⟩, fun j => ⟨?_, ?_⟩⟩
  · have := P.Wxo.fst_le (P.ρ j); have := fl P.Wyo (Cs.H_POS (j + 1))
    have := RZ j; have := ZR j; have := S.S_OR
    unfold MergeRun.XO MergeRun.YO; omega
  · have := P.Wyo.fst_le (P.ρ j); have := fl P.Wxo (Cs.H_POS (j + 1))
    have := RZ j; have := ZR j; have := S.S_OR
    unfold MergeRun.XO MergeRun.YO; omega
  · have := P.Wxc.fst_le (P.ρ j); have := P.Wzx.fst_le (P.ζ j)
    have := fl P.Wxc (Cs.H_POS (j + 1))
    have := RZ j; have := ZR j; have := S.S_XA_FORK; have := S.S_XA_R
    unfold MergeRun.cx MergeRun.AX MergeRun.ZA0; omega
  · have := P.Wxc.fst_le (P.ρ j); have := P.Wzx.fst_le (P.ζ j)
    have hz1 : 1 ≤ P.ζ (j + 1) := by have := RZ (j + 1); have := Cs.H_POS (j + 1); omega
    have := fl P.Wzx hz1
    have := RZ j; have := ZR j; have := RZ (j + 1); have := S.S_XA_ZA; have := S.S_XA_R
    unfold MergeRun.cx MergeRun.AX MergeRun.ZA0; omega
  · have := P.Wyc.fst_le (P.ρ j); have := P.Wzy.fst_le (P.ζ j)
    have := fl P.Wyc (Cs.H_POS (j + 1))
    have := RZ j; have := ZR j; have := S.S_YA_FORK; have := S.S_YA_R
    unfold MergeRun.cy MergeRun.AY MergeRun.ZA1; omega
  · have := P.Wyc.fst_le (P.ρ j); have := P.Wzy.fst_le (P.ζ j)
    have hz1 : 1 ≤ P.ζ (j + 1) := by have := RZ (j + 1); have := Cs.H_POS (j + 1); omega
    have := fl P.Wzy hz1
    have := RZ j; have := ZR j; have := RZ (j + 1); have := S.S_YA_ZA; have := S.S_YA_R
    unfold MergeRun.cy MergeRun.AY MergeRun.ZA1; omega

end Formal.Cells.OpsTimed
