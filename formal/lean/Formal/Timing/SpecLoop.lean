import Formal.Timing.SpecChain

/-!
# Settle windows and storage loops on the collapsed relation (shard C)

**Problem, plainly.** After `SpecChain`/`CViewPS`, every logic gate of THE target is a
`CGateOK` gate: pin `i` reads a source node through a composite delay that is a sum of
admissible arc delays. A storage node (C-element, latch, arbiter state) is such a gate whose
feedback pin's source is its own output, the loop delay being the sum over the routed loop.
What does the relation alone guarantee about (a) a gate whose inputs are stable, and (b) a
storage node whose other inputs CONFIRM its value?

**Proved** (sane parameters, corner `c ∈ [0,1]`, arcs ordered):
* `sumAdm_bounds`: a composite delay lies in `[Σ dmin, Σ dmax]` of its arcs.
* `cgate_stable`: inputs stable on `[S i, U i]` ⇒ output = INIT at those values on
  `[max(S, S i + Σdmax i), min(U i + Σdmin i)]` (the collapsed analogue of `gate_stable`).
* `cgate_hold`: feedback pin `j` reads the gate's own output, with loop delay at least 1 ps
  (`1 ≤ Σ dmin`); the other pins hold values `v` on their windows; INIT at `(v, q)` is `q`
  (the pins confirm `q`); the output is `q` on `[T0 - Σdmax_j, T0)`. Then the output stays `q`
  on all of `[T0, E]`, for any `E` within every confirming pin's window. Proof by strong
  induction on time: each feedback read falls in the primed segment or an earlier instant.

**Not shown.** How the primed segment arises (a forcing phase: `cgate_stable` with values
that force `q` whatever the feedback is, held for at least the loop's `Σ dmax`; B's
`fb_switch` side condition); what happens when the confirming pins change (a new episode).
-/

namespace Formal.Timing.SpecLoop
open Formal.Target Formal.Timing.SpecSettle Formal.Timing.SpecChain

def sumMax (p : DelayPar) (es : List Arc) : Nat := (es.map (dmax p)).sum
def sumMin (p : DelayPar) (es : List Arc) : Nat := (es.map (dmin p)).sum

/-- Every arc ordered (`fmin ≤ smin`, `fmax ≤ smax`). -/
def ArcsOrd (es : List Arc) : Prop := ∀ e ∈ es, e.fmin ≤ e.smin ∧ e.fmax ≤ e.smax

theorem sumAdm_bounds {p : DelayPar} {c : ℚ} (hp : Sane p) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    ∀ (es : List Arc) (D : Nat), ArcsOrd es → SumAdm p c es D → sumMin p es ≤ D ∧ D ≤ sumMax p es
  | [], D, _, h => by simp [SumAdm] at h; simp [sumMin, sumMax, h]
  | e :: es, D, ho, ⟨d, hd, hle, hr⟩ => by
    have he := ho e List.mem_cons_self
    have h1 := adm_le_dmax hp hc0 hc1 he.2 hd
    have h2 := dmin_le_adm hp hc0 hc1 he.1 hd
    obtain ⟨r1, r2⟩ := sumAdm_bounds hp hc0 hc1 es (D - d) (fun e' h' => ho e' (List.mem_cons_of_mem _ h')) hr
    simp only [sumMin, sumMax, List.map_cons, List.sum_cons] at r1 r2 ⊢
    omega

/-- **Settle window of a collapsed gate.** -/
theorem cgate_stable {p : DelayPar} {c : ℚ} {g : Gate} {src : Nat → Nat} {arcs : Nat → List Arc} {S : Nat}
    {x : Beh} (hp : Sane p) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hord : ∀ i, i < g.k → ArcsOrd (arcs i))
    (hg : CGateOK p c g src arcs S x) (Si Ui : Nat → Nat) (v : Nat → Bool)
    (hin : ∀ i, i < g.k → ∀ t, Si i ≤ t → t ≤ Ui i → x (src i) t = v i) :
    ∀ t, S ≤ t → (∀ i, i < g.k → Si i + sumMax p (arcs i) ≤ t ∧ t ≤ Ui i + sumMin p (arcs i)) →
      x g.out t = g.init.testBit (addr g.k v) := by
  obtain ⟨F, -, hF⟩ := hg
  intro t ht hw
  obtain ⟨hr, ho⟩ := hF t ht
  rw [ho]; congr 1
  apply SpecSettle.addr_congr
  intro i hi
  obtain ⟨h1, h2⟩ := hr i hi
  obtain ⟨b1, b2⟩ := sumAdm_bounds hp hc0 hc1 _ _ (hord i hi) h2
  obtain ⟨w1, w2⟩ := hw i hi
  exact hin i hi (F i t) (by omega) (by omega)

/-- **A storage node holds a confirmed value through its routed loop.** -/
theorem cgate_hold {p : DelayPar} {c : ℚ} {g : Gate} {src : Nat → Nat} {arcs : Nat → List Arc} {S : Nat}
    {x : Beh} (hp : Sane p) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hord : ∀ i, i < g.k → ArcsOrd (arcs i))
    (hg : CGateOK p c g src arcs S x) {j : Nat} (hj : j < g.k) (hfb : src j = g.out)
    (hlo : 1 ≤ sumMin p (arcs j))
    (Si Ui : Nat → Nat) (v : Nat → Bool) (q : Bool)
    (hin : ∀ i, i < g.k → i ≠ j → ∀ t, Si i ≤ t → t ≤ Ui i → x (src i) t = v i)
    (hconf : g.init.testBit (addr g.k fun i => if i = j then q else v i) = q)
    (T0 E : Nat) (hS : S ≤ T0)
    (hw : ∀ i, i < g.k → i ≠ j → Si i + sumMax p (arcs i) ≤ T0 ∧ E ≤ Ui i + sumMin p (arcs i))
    (hprime : ∀ t, T0 - sumMax p (arcs j) ≤ t → t < T0 → x g.out t = q) :
    ∀ t, T0 ≤ t → t ≤ E → x g.out t = q := by
  obtain ⟨F, -, hF⟩ := hg
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro h1 h2
    obtain ⟨hr, ho⟩ := hF t (by omega)
    rw [ho, ← hconf]; congr 1
    apply SpecSettle.addr_congr
    intro i hi
    obtain ⟨r1, r2⟩ := hr i hi
    obtain ⟨b1, b2⟩ := sumAdm_bounds hp hc0 hc1 _ _ (hord i hi) r2
    by_cases e : i = j
    · subst e
      simp only [ite_true]
      rw [hfb]
      by_cases hlt : F i t < T0
      · exact hprime _ (by omega) hlt
      · exact ih (F i t) (by omega) (by omega) (by omega)
    · simp only [e, ite_false]
      obtain ⟨w1, w2⟩ := hw i hi e
      exact hin i hi e (F i t) (by omega) (by omega)


/-- **Forced**: the other pins hold `v` on their windows and INIT gives `q` at `v` whatever the
feedback pin reads. Then the output is `q` on the window, without any assumption on the loop. -/
theorem cgate_force {p : DelayPar} {c : ℚ} {g : Gate} {src : Nat → Nat} {arcs : Nat → List Arc} {S : Nat}
    {x : Beh} (hp : Sane p) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hord : ∀ i, i < g.k → ArcsOrd (arcs i))
    (hg : CGateOK p c g src arcs S x) {j : Nat} (Si Ui : Nat → Nat) (v : Nat → Bool) (q : Bool)
    (hin : ∀ i, i < g.k → i ≠ j → ∀ t, Si i ≤ t → t ≤ Ui i → x (src i) t = v i)
    (hforce : ∀ b : Bool, g.init.testBit (addr g.k fun i => if i = j then b else v i) = q) :
    ∀ t, S ≤ t → (∀ i, i < g.k → i ≠ j → Si i + sumMax p (arcs i) ≤ t ∧ t ≤ Ui i + sumMin p (arcs i)) →
      x g.out t = q := by
  obtain ⟨F, -, hF⟩ := hg
  intro t ht hw
  obtain ⟨hr, ho⟩ := hF t ht
  rw [ho, ← hforce (x (src j) (F j t))]; congr 1
  apply SpecSettle.addr_congr
  intro i hi
  by_cases e : i = j
  · subst e; simp
  · simp only [e, ite_false]
    obtain ⟨r1, r2⟩ := hr i hi
    obtain ⟨b1, b2⟩ := sumAdm_bounds hp hc0 hc1 _ _ (hord i hi) r2
    obtain ⟨w1, w2⟩ := hw i hi e
    exact hin i hi e (F i t) (by omega) (by omega)

/-- **A clean switch**: forced to `q` on `[T1, T0)` with `T0 - T1 ≥ Σdmax` of the loop (the
forcing lasts at least the loop's longest delay), then confirmed on `[T0, E]`: the output is `q`
on all of `[T1, E]`. The side condition is the per-storage-node timing obligation. -/
theorem cgate_switch {p : DelayPar} {c : ℚ} {g : Gate} {src : Nat → Nat} {arcs : Nat → List Arc} {S : Nat}
    {x : Beh} (hp : Sane p) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hord : ∀ i, i < g.k → ArcsOrd (arcs i))
    (hg : CGateOK p c g src arcs S x) {j : Nat} (hj : j < g.k) (hfb : src j = g.out)
    (hlo : 1 ≤ sumMin p (arcs j)) (q : Bool) (T1 T0 E : Nat) (hS : S ≤ T1)
    (hlen : T1 + sumMax p (arcs j) ≤ T0)
    (Sf Uf : Nat → Nat) (vf : Nat → Bool)
    (hinf : ∀ i, i < g.k → i ≠ j → ∀ t, Sf i ≤ t → t ≤ Uf i → x (src i) t = vf i)
    (hforce : ∀ b : Bool, g.init.testBit (addr g.k fun i => if i = j then b else vf i) = q)
    (hwf : ∀ i, i < g.k → i ≠ j → Sf i + sumMax p (arcs i) ≤ T1 ∧ T0 ≤ Uf i + sumMin p (arcs i))
    (Sc Uc : Nat → Nat) (vc : Nat → Bool)
    (hinc : ∀ i, i < g.k → i ≠ j → ∀ t, Sc i ≤ t → t ≤ Uc i → x (src i) t = vc i)
    (hconf : g.init.testBit (addr g.k fun i => if i = j then q else vc i) = q)
    (hwc : ∀ i, i < g.k → i ≠ j → Sc i + sumMax p (arcs i) ≤ T0 ∧ E ≤ Uc i + sumMin p (arcs i)) :
    ∀ t, T1 ≤ t → t ≤ E → x g.out t = q := by
  have hf : ∀ t, T1 ≤ t → t < T0 → x g.out t = q := fun t a b =>
    cgate_force hp hc0 hc1 hord hg Sf Uf vf q hinf hforce t (by omega)
      (fun i hi e => ⟨by have := (hwf i hi e).1; omega, by have := (hwf i hi e).2; omega⟩)
  have hh := cgate_hold hp hc0 hc1 hord hg hj hfb hlo Sc Uc vc q hinc hconf T0 E (by omega) hwc
    (fun t a b => hf t (by omega) b)
  intro t a b
  by_cases h : t < T0
  · exact hf t a h
  · exact hh t (by omega) b


/-- A signal that differs at `a ≤ b` toggles at some step in `(a, b]`. -/
theorem toggle_between (s : Sig) : ∀ (a b : Nat), a ≤ b → s a ≠ s b → ∃ u, a < u ∧ u ≤ b ∧ s (u - 1) ≠ s u := by
  intro a b hab hne
  induction b with
  | zero =>
    have : a = 0 := by omega
    subst this; exact absurd rfl hne
  | succ b ih =>
    by_cases hab' : a ≤ b
    · by_cases h : s b = s (b + 1)
      · obtain ⟨u, h1, h2, h3⟩ := ih hab' (by rw [h]; exact hne)
        exact ⟨u, h1, by omega, h3⟩
      · exact ⟨b + 1, by omega, le_refl _, by simpa using h⟩
    · have : a = b + 1 := by omega
      subst this; exact absurd rfl hne

/-- **No spontaneous change (causality).** If a collapsed gate's output differs at `t1 ≤ t2`
(both from its start on), some pin's source toggles at a time in
`(t1 - Σdmax, t2 - Σdmin]` of that pin's composite arcs. -/
theorem cgate_cause {p : DelayPar} {c : ℚ} {g : Gate} {src : Nat → Nat} {arcs : Nat → List Arc} {S : Nat}
    {x : Beh} (hp : Sane p) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hord : ∀ i, i < g.k → ArcsOrd (arcs i))
    (hg : CGateOK p c g src arcs S x) {t1 t2 : Nat} (hS : S ≤ t1) (h12 : t1 ≤ t2)
    (hne : x g.out t1 ≠ x g.out t2) :
    ∃ i, i < g.k ∧ ∃ u, t1 - sumMax p (arcs i) < u ∧ u ≤ t2 - sumMin p (arcs i) ∧
      x (src i) (u - 1) ≠ x (src i) u := by
  obtain ⟨F, hm, hF⟩ := hg
  obtain ⟨r1, o1⟩ := hF t1 hS
  obtain ⟨r2, o2⟩ := hF t2 (by omega)
  by_contra hno
  apply hne
  rw [o1, o2]; congr 1
  apply SpecSettle.addr_congr
  intro i hi
  obtain ⟨a1, b1⟩ := r1 i hi
  obtain ⟨a2, b2⟩ := r2 i hi
  obtain ⟨l1, u1⟩ := sumAdm_bounds hp hc0 hc1 _ _ (hord i hi) b1
  obtain ⟨l2, u2⟩ := sumAdm_bounds hp hc0 hc1 _ _ (hord i hi) b2
  have hmono : F i t1 ≤ F i t2 := hm i hi h12
  by_contra hd
  obtain ⟨u, h1, h2, h3⟩ := toggle_between (x (src i)) _ _ hmono hd
  exact hno ⟨i, hi, u, by omega, by omega, h3⟩


/-- `s` is constant on `[a, b]`. -/
def Quiet (s : Sig) (a b : Nat) : Prop := ∀ t, a ≤ t → t ≤ b → s t = s a

/-- **Settling of ranked combinational logic (fundamental mode).** Nodes `w` with `comb w` are
collapsed gates `gate w` (output `w`) whose every pin source is either a `root` or a comb node of
smaller rank `ρ`; every pin's composite delay is at most `M` (`sumMax ≤ M`) and every gate's
start is at most `A`. If every root is quiet on `[A, B]`, every comb node `w` is quiet on
`[A + (ρ w + 1) * M, B]`. With THE target's ranks (`CViewPS.comb_ranked`, depth ≤ 96) and the
storage and environment nodes as roots: once they stop moving, the whole circuit is quiet
`97 · M` later. -/
theorem settle_ranked {p : DelayPar} {c : ℚ} {x : Beh} (hp : Sane p) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (comb root : Nat → Prop) (ρ : Nat → Nat) (gate : Nat → Gate) (src : Nat → Nat → Nat)
    (arcs : Nat → Nat → List Arc) (S : Nat → Nat) (M A B : Nat)
    (hg : ∀ w, comb w → (gate w).out = w ∧ CGateOK p c (gate w) (src w) (arcs w) (S w) x)
    (hord : ∀ w, comb w → ∀ i, i < (gate w).k → ArcsOrd (arcs w i))
    (hsrc : ∀ w, comb w → ∀ i, i < (gate w).k → root (src w i) ∨ (comb (src w i) ∧ ρ (src w i) < ρ w))
    (hM : ∀ w, comb w → ∀ i, i < (gate w).k → sumMax p (arcs w i) ≤ M)
    (hS : ∀ w, comb w → S w ≤ A)
    (hroot : ∀ r, root r → Quiet (x r) A B) :
    ∀ w, comb w → Quiet (x w) (A + (ρ w + 1) * M) B := by
  intro w
  induction hr : ρ w using Nat.strong_induction_on generalizing w with
  | _ n ih =>
    intro hw t h1 h2
    obtain ⟨hout, hcg⟩ := hg w hw
    by_contra hne
    have hne' : x (gate w).out (A + (n + 1) * M) ≠ x (gate w).out t := by
      rw [hout]; exact fun e => hne e.symm
    obtain ⟨i, hi, u, u1, u2, u3⟩ := cgate_cause hp hc0 hc1 (hord w hw) hcg
      (by have := hS w hw; nlinarith) h1 hne'
    have hm := hM w hw i hi
    rcases hsrc w hw i hi with hrt | ⟨hc, hlt⟩
    · have q := hroot _ hrt
      have e1 := q (u - 1) (by rw [Nat.add_mul] at u1; omega) (by omega)
      have e2 := q u (by rw [Nat.add_mul] at u1; omega) (by omega)
      exact u3 (e1.trans e2.symm)
    · have q := ih (ρ (src w i)) (hr ▸ hlt) (src w i) rfl hc
      have hb : A + (ρ (src w i) + 1) * M ≤ A + n * M := by
        have : ρ (src w i) + 1 ≤ n := by omega
        have := Nat.mul_le_mul_right M this; omega
      have e1 := q (u - 1) (by rw [Nat.add_mul] at u1; omega) (by omega)
      have e2 := q u (by rw [Nat.add_mul] at u1; omega) (by omega)
      exact u3 (e1.trans e2.symm)


/-- **Quiet is forever.** Logic nodes `w` (`node w`) are collapsed gates (output `w`) whose pin
sources are logic nodes or roots; every composite delay is in `[1, M]` ps (`1 ≤ Σdmin`,
`Σdmax ≤ M`) and every start is at most `T - M`. If the roots are quiet from `T - M` on for ever
and every logic node is quiet on `[T - M, T]`, then every logic node is quiet for ever: a quiet
circuit with a quiet environment never starts moving by itself (no oscillation, no late glitch). -/
theorem quiet_forever {p : DelayPar} {c : ℚ} {x : Beh} (hp : Sane p) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (node root : Nat → Prop) (gate : Nat → Gate) (src : Nat → Nat → Nat)
    (arcs : Nat → Nat → List Arc) (S : Nat → Nat) (M T : Nat) (hMT : M ≤ T)
    (hg : ∀ w, node w → (gate w).out = w ∧ CGateOK p c (gate w) (src w) (arcs w) (S w) x)
    (hord : ∀ w, node w → ∀ i, i < (gate w).k → ArcsOrd (arcs w i))
    (hsrc : ∀ w, node w → ∀ i, i < (gate w).k → root (src w i) ∨ node (src w i))
    (hM : ∀ w, node w → ∀ i, i < (gate w).k →
      (1 ≤ sumMin p (arcs w i) ∨ root (src w i) ∨ (gate (src w i)).k = 0) ∧ sumMax p (arcs w i) ≤ M)
    (hS : ∀ w, node w → S w ≤ T - M)
    (hroot : ∀ r, root r → ∀ t, T - M ≤ t → x r t = x r (T - M))
    (hq : ∀ w, node w → ∀ t, T - M ≤ t → t ≤ T → x w t = x w (T - M)) :
    ∀ w, node w → ∀ t, T - M ≤ t → x w t = x w (T - M) := by
  -- no logic node toggles at any time after T - M
  have key : ∀ t, ∀ w, node w → T - M < t → x w (t - 1) = x w t := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro w hw ht
      by_cases htT : t ≤ T
      · rw [hq w hw (t - 1) (by omega) (by omega), hq w hw t (by omega) htT]
      by_contra hne
      obtain ⟨hout, hcg⟩ := hg w hw
      have hne' : x (gate w).out (t - 1) ≠ x (gate w).out t := by rw [hout]; exact hne
      obtain ⟨i, hi, u, u1, u2, u3⟩ := cgate_cause hp hc0 hc1 (hord w hw) hcg
        (by have := hS w hw; omega) (by omega) hne'
      obtain ⟨m1, m2⟩ := hM w hw i hi
      rcases hsrc w hw i hi with hr | hn
      · exact u3 ((hroot _ hr (u - 1) (by omega)).trans (hroot _ hr u (by omega)).symm)
      · by_cases hu : T - M < u
        · by_cases hut : u < t
          · exact u3 (ih u hut _ hn hu)
          · -- a zero-delay pin: its source is a root or a constant (k = 0) gate
            rcases m1 with m1 | m1 | m1
            · omega
            · exact u3 ((hroot _ m1 (u - 1) (by omega)).trans (hroot _ m1 u (by omega)).symm)
            · obtain ⟨ho', hcg'⟩ := hg _ hn
              have : x (gate (src w i)).out (u - 1) ≠ x (gate (src w i)).out u := by rw [ho']; exact u3
              obtain ⟨i', hi', -⟩ := cgate_cause hp hc0 hc1 (hord _ hn) hcg'
                (by have := hS _ hn; omega) (by omega) this
              omega
        · exact u3 ((hq _ hn (u - 1) (by omega) (by omega)).trans (hq _ hn u (by omega) (by omega)).symm)
  intro w hw t ht
  induction t with
  | zero => have : T - M = 0 := by omega
            rw [this]
  | succ t ih =>
    by_cases h : T - M ≤ t
    · rw [← ih h, ← key (t + 1) w hw (by omega)]; rfl
    · have : T - M = t + 1 := by omega
      rw [this]

end Formal.Timing.SpecLoop
