import Formal.Net.OpsGen

/-!
# Probe C-10k: H_FB_FIRST (B's C2) from the RT_FB race (tcheck rule R / Rc)

C-8n's `OpsGen.FbFirst qp o` (H_FB_FIRST: at every output change the feedback
pin already shows the output) is what turns the physical feedback LUT
(`LutFb`) into the Ops SI gate (`lutFb_si`). C-8n derives it from `Gap hi o`
(output changes spaced by the feedback route's settle bound `hi`).

tcheck's rule R / Rc (C-10f, C-10h) checks a different-looking thing on the
routed graph: RT_FB, "the feedback wire reaches its pin before ANY response
to the node's output edge reaches another pin of the node". Are they the same
obligation? **No, but RT_FB implies H_FB_FIRST**, and this file proves the
trace half of that implication:

* `RespAfter hi p o` (H_RESP_AFTER, the trace reading of RT_FB): every change
  of the non-feedback pins `p` comes when the output has been stable for at
  least `hi` ticks (the response to the node's last edge arrives no earlier
  than `hi` after it, and nothing else moves those pins).
* `fbFirst_of_resp`: `LutFb F p qp o` (any LUT function `F`, generated or
  not) + the feedback route is a `BoundedDelay lo hi o qp` + `qp 0 = o 0`
  (reset) + `RespAfter hi p o` ⇒ `FbFirst qp o`.

How the route check discharges `RespAfter` (argued, not mechanised here):
Rc PASS says, at every corner model, `fb_hi ≤ resp_lo`, where `resp_lo` is the
certified earliest arrival, at any non-feedback pin, of any causal chain
launched by the node's output edge (`cverdict_sound`). `RespAfter` then
follows under **H_RESP_ONLY**: every non-feedback pin change of the node is
caused by its own previous output edge (the four-phase DI protocol: a
C-element input changes only after the output has agreed with it, so the
output is stable from that edge until the change). That is a protocol fact of
the closed handshake network, not a timing fact; it fails for a free-running
environment input.

The differences, stated:
* `Gap` is a property of the output alone (consecutive edges spaced by `hi`);
  `RespAfter` constrains only the inputs. Neither implies the other in
  general. `Gap` also needs a quiescent reset; `fbFirst_of_resp` does not
  (its reset hypothesis is only `qp 0 = o 0`).
* An output change caused by a feedback-pin change alone (the LUT reacting to
  its own stale copy) is ruled out by induction (`FbFirst` at the previous
  edge), not by any timing hypothesis: RT_FB need not mention it.
* B's C3 (per-pin form) is the same inequality with the site-pin delays of the
  feedback and response pins included. tcheck's prjxray variants already price
  every LUT-pin arc to the physical site pin (C-10f), so Rc's prjxray columns
  are C3's inequality; only its `sdf` column is C2 without the per-pin term.

`fbFirst_witness` is the non-vacuity check: a 2-input C-element LUT (majority
with its feedback), a feedback route of delay 1, both inputs rising together,
satisfying every hypothesis with the output actually changing.
-/

namespace Formal.Timing.FbFirstRt
open Formal.Net Formal.Net.Ops.Gen

/-- H_RESP_AFTER (RT_FB, trace form): a change of the non-feedback pins happens
only when the output has been stable for the last `hi` ticks (and not before
`hi`). -/
def RespAfter {α : Type} (hi : Nat) (p : Nat → α) (o : Trace) : Prop :=
  ∀ u, p (u + 1) ≠ p u → hi ≤ u + 1 ∧ stableOn o (u + 1 - hi) (u + 1)

/-- Either `o` never changed before `t`, or there is a last change `s < t`. -/
theorem last_change (o : Trace) : ∀ t, (∀ u, u < t → o (u + 1) = o u) ∨
    ∃ s, s < t ∧ o (s + 1) ≠ o s ∧ ∀ u, s < u → u < t → o (u + 1) = o u := by
  intro t
  induction t with
  | zero => exact Or.inl (fun u h => absurd h (Nat.not_lt_zero u))
  | succ t ih =>
    by_cases h : o (t + 1) = o t
    · rcases ih with ih | ⟨s, hs, hc, hst⟩
      · left; intro u hu
        rcases Nat.lt_succ_iff_lt_or_eq.mp hu with hu | hu
        · exact ih u hu
        · subst hu; exact h
      · right; refine ⟨s, by omega, hc, fun u h1 h2 => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h2 | h2
        · exact hst u h1 h2
        · subst h2; exact h
    · right; exact ⟨t, by omega, h, fun u h1 h2 => by omega⟩

/-- No change in `(a, b)` keeps the value of `o (a + 1)` up to `b`. -/
theorem const_of_steps {o : Trace} {a b : Nat} (h : ∀ u, a < u → u < b → o (u + 1) = o u) :
    ∀ x, a + 1 ≤ x → x ≤ b → o x = o (a + 1) := by
  intro x h1 h2
  induction x with
  | zero => omega
  | succ x ih =>
    by_cases hx : a + 1 ≤ x
    · rw [h x (by omega) (by omega)]; exact ih hx (by omega)
    · have : x = a := by omega
      subst this; rfl

/-- A value that differs at `s` and `t` (`s ≤ t`) changes at some step in between. -/
theorem step_of_ne {α : Type} {p : Nat → α} {s : Nat} : ∀ t, s ≤ t → p t ≠ p s →
    ∃ u, s ≤ u ∧ u < t ∧ p (u + 1) ≠ p u := by
  intro t
  induction t with
  | zero => intro h hne; have : s = 0 := by omega
            subst this; exact absurd rfl hne
  | succ t ih =>
    intro h hne
    by_cases hp : p (t + 1) = p t
    · have hs : s ≤ t := by
        rcases Nat.lt_or_ge t s with h' | h'
        · have : s = t + 1 := by omega
          subst this; exact absurd rfl hne
        · exact h'
      obtain ⟨u, h1, h2, h3⟩ := ih hs (by rw [← hp]; exact hne)
      exact ⟨u, h1, by omega, h3⟩
    · exact ⟨t, by
        rcases Nat.lt_or_ge t s with h' | h'
        · have : s = t + 1 := by omega
          subst this; exact absurd rfl hne
        · exact h', by omega, hp⟩

/-- Before the output's first change, the feedback pin keeps its reset value. -/
theorem qp_const {lo hi : Nat} {o qp : Trace} (hB : BoundedDelay lo hi o qp) (h0 : qp 0 = o 0)
    {t : Nat} (hc : ∀ u, u < t → o (u + 1) = o u) : ∀ x, x ≤ t → qp x = o 0 := by
  have ho : ∀ x, x ≤ t → o x = o 0 := by
    intro x hx
    induction x with
    | zero => rfl
    | succ x ih => rw [hc x (by omega)]; exact ih (by omega)
  intro x hx
  induction x with
  | zero => exact h0
  | succ x ih =>
    by_cases hq : qp x = qp (x + 1)
    · rw [← hq]; exact ih (by omega)
    · obtain ⟨d, _, _, hd, he⟩ := hB.cause x hq
      rw [he]; exact ho _ (by omega)

/-- **RT_FB (trace form) ⇒ H_FB_FIRST.** For any LUT function `F` read through a
feedback route that is a bounded delay with settle bound `hi`. -/
theorem fbFirst_of_resp {α : Type} {F : α → Bool → Bool} {p : Nat → α} {qp o : Trace}
    {lo hi : Nat} (hL : LutFb F p qp o) (hB : BoundedDelay lo hi o qp) (h0 : qp 0 = o 0)
    (hR : RespAfter hi p o) : FbFirst qp o := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t IH =>
  intro hch
  rcases last_change o t with hc | ⟨s, hs, hcs, hst⟩
  · rw [qp_const hB h0 hc t (Nat.le_refl t)]
    have : ∀ x, x ≤ t → o x = o 0 := by
      intro x hx
      induction x with
      | zero => rfl
      | succ x ih => rw [hc x (by omega)]; exact ih (by omega)
    exact (this t (Nat.le_refl t)).symm
  · have hqs : qp s = o s := IH s hs hcs
    have hot : o t = o (s + 1) := const_of_steps hst t (by omega) (Nat.le_refl t)
    apply Classical.byContradiction
    intro hne
    have hqt : qp t = qp s := by
      have h1 : qp t ≠ o (s + 1) := by rw [← hot]; exact hne
      have h2 : qp s ≠ o (s + 1) := by rw [hqs]; exact fun h => hcs h.symm
      revert h1 h2; cases qp t <;> cases qp s <;> cases o (s + 1) <;> simp
    have hFs : o (s + 1) = F (p s) (qp s) := hL s hcs
    have hFt : o (t + 1) = F (p t) (qp t) := hL t hch
    have hpne : p t ≠ p s := by
      intro hp
      apply hch
      rw [hFt, hp, hqt, ← hFs, hot]
    obtain ⟨u, hu1, hu2, hu3⟩ := step_of_ne t (by omega) hpne
    obtain ⟨hhi, hstab⟩ := hR u hu3
    have hgap : s + 1 ≤ u + 1 - hi := by
      apply Classical.byContradiction
      intro hlt
      have e1 := hstab s (by omega) (by omega)
      have e2 := hstab (s + 1) (by omega) (by omega)
      exact hcs (by rw [e1, e2])
    have hset : stableOn o (t - hi) t := by
      intro x h1 h2
      rw [const_of_steps hst x (by omega) h2, const_of_steps hst (t - hi) (by omega) (by omega)]
    exact hne (hB.settle t (by omega) hset)

/-- The Ops SI form, for any feedback LUT, from RT_FB's trace form. -/
theorem si_of_resp {α : Type} {F : α → Bool → Bool} {p : Nat → α} {qp o : Trace}
    {lo hi : Nat} (hL : LutFb F p qp o) (hB : BoundedDelay lo hi o qp) (h0 : qp 0 = o 0)
    (hR : RespAfter hi p o) : ∀ t, o (t + 1) ≠ o t → o (t + 1) = F (p t) (o t) :=
  lutFb_si hL (fbFirst_of_resp hL hB h0 hR)

/-! ## Non-vacuity: a C-element whose inputs rise together at 5 -/

/-- Majority of the two inputs and the feedback (bd_c2's function). -/
def maj (ab : Bool × Bool) (q : Bool) : Bool := (ab.1 && ab.2) || (q && (ab.1 || ab.2))

def wp (t : Nat) : Bool × Bool := (decide (5 ≤ t), decide (5 ≤ t))
def wo (t : Nat) : Bool := decide (6 ≤ t)
def wq (t : Nat) : Bool := decide (7 ≤ t)

theorem fbFirst_witness :
    LutFb maj wp wq wo ∧ BoundedDelay 1 1 wo wq ∧ wq 0 = wo 0 ∧ RespAfter 1 wp wo ∧
    FbFirst wq wo ∧ wo 6 ≠ wo 5 := by
  have hL : LutFb maj wp wq wo := by
    intro t h
    simp only [wo, wp, wq, maj, ne_eq] at *
    by_cases h5 : 5 ≤ t <;> by_cases h6 : 6 ≤ t <;> simp_all <;> omega
  have hB : BoundedDelay 1 1 wo wq := by
    refine ⟨fun t h => ⟨1, by omega, by omega, by omega, ?_⟩, fun t h1 h2 => ?_⟩
    · simp only [changes, wq, wo, ne_eq] at *
      by_cases h7 : 7 ≤ t + 1 <;> by_cases h6 : 6 ≤ t <;> simp_all <;> omega
    · have := h2 (t - 1) (by omega) (by omega)
      have h3 := h2 t (by omega) (by omega)
      simp only [wq, wo] at *
      by_cases h7 : 7 ≤ t <;> by_cases h6 : 6 ≤ t - 1 <;> simp_all <;> omega
  have hR : RespAfter 1 wp wo := by
    intro u h
    have hu : u = 4 := by
      simp only [wp, ne_eq, Prod.mk.injEq] at h
      by_cases h5 : 5 ≤ u + 1 <;> by_cases h4 : 5 ≤ u <;> simp_all <;> omega
    subst hu
    refine ⟨by omega, fun x h1 h2 => ?_⟩
    simp only [wo]
    have : ¬ 6 ≤ x := by omega
    simp [this]
  exact ⟨hL, hB, rfl, hR, fbFirst_of_resp hL hB rfl hR, by decide⟩

/-! ## H_CEL_NEXT: a C-element's next edge needs every input to change

tcheck rule X (C-10k) lower-bounds the NEXT edge of the node `D` that drives a
return-to-zero pulse by the first change, after `D`'s launch edge, of ONE
chosen handshake input of `D` (the one whose first change is latest). That
is sound when `D` is a C-element obeying H_FB_FIRST: between two consecutive
output edges, every input has changed. -/

/-- Between consecutive edges `s < t` of a C-element (`maj` read through its
feedback pin, H_FB_FIRST), both inputs differ at `t` from their values at `s`;
hence each changed at some step in `[s, t)` (`step_of_ne`). -/
theorem cel_next_needs_all {a b : Nat → Bool} {qp o : Trace}
    (hL : LutFb maj (fun t => (a t, b t)) qp o) (hF : FbFirst qp o) {s t : Nat}
    (hs : o (s + 1) ≠ o s) (hst : s < t) (hc : o (t + 1) ≠ o t)
    (hmid : ∀ u, s < u → u < t → o (u + 1) = o u) :
    (∃ u, s ≤ u ∧ u < t ∧ a (u + 1) ≠ a u) ∧ (∃ u, s ≤ u ∧ u < t ∧ b (u + 1) ≠ b u) := by
  have hot : o t = o (s + 1) := const_of_steps hmid t (by omega) (Nat.le_refl t)
  have e1 : o (s + 1) = maj (a s, b s) (o s) := by rw [hL s hs, hF s hs]
  have e2 : o (t + 1) = maj (a t, b t) (o (s + 1)) := by rw [hL t hc, hF t hc, hot]
  have n2 : o (t + 1) ≠ o (s + 1) := by rw [← hot]; exact hc
  have key : a t ≠ a s ∧ b t ≠ b s := by
    revert e1 e2 hs n2
    generalize o s = x0; generalize o (s + 1) = x1; generalize o (t + 1) = x2
    generalize a s = as_; generalize b s = bs; generalize a t = at_; generalize b t = bt
    cases x0 <;> cases x1 <;> cases x2 <;> cases as_ <;> cases bs <;> cases at_ <;> cases bt <;>
      simp [maj]
  exact ⟨step_of_ne t (by omega) key.1, step_of_ne t (by omega) key.2⟩

end Formal.Timing.FbFirstRt
