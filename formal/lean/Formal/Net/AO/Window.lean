import Formal.Net.AO.Timed

/-!
# Window certificates for the AND-OR timed check (shard C, all-pairs route; notes/C-allpairs.md)

**Problem, plainly.** For every operand pair, the run of THE target is a sequence of loop iterations whose control
order depends on the data only through the branch taken; its certificate is the concatenation of a few *window*
certificates, one per branch kind. The local check of the long certificate (`LCheckXA`, with AND-OR causes,
per-reader bounds and data guards) quantifies over count vectors of a node's dependency set. This file proves that,
at every count vector inside a window's *box* (each dependency node has passed the window's start offset `o` and has
not passed its end), the long certificate's local check follows from the window certificate's local check, when:
* the window's causes, shifted by `o`, are the long certificate's causes, up to extra causes that lie before the
  window's start (they are counted inside the box, so they never change which alternative is complete): `AltCorr`;
* the long certificate's guards for each data pin are the window's guards shifted by `o` (claim indices by `co`),
  preceded by guards that ended before the window and followed by guards that start after it (`hgd`), and the
  shifted claims carry the window's values;
* the window's bounds, where nonzero, shifted, are no stronger than the long certificate's (`hL`);
* the window's initial state is the long run's state after `o` events on the dependency set (`hs0`), and the move
  rule at `v` reads only the dependency set and data nodes (`hT`).

**Proved:** `altIn_corr`, `enabled_window`, `dv_window`, `lcheckXA_window` (the conclusion of the long local check,
at every count vector in the box, from the window's local check).

**Not shown here:** that every count vector the long check quantifies over lies in some window's box (coverage; an
instance property), the timing checks (`TOA`, `SepOK`, `UpOKA`, `GuardTime`) for windows, any instance.
-/

namespace Formal.Net.AO
open Formal.Net.OccNet (st)
open Formal.Net.OccNet.Timed Formal.Net.OccNet.TimedX

variable {α : Type} [DecidableEq α]

/-- The state after `n` flips is the window state (from the state after `o` flips) after `n - o` flips. -/
theorem st_shiftA (s0 : α → Bool) (o n : α → Nat) (u : α) (h : o u ≤ n u) :
    st s0 n u = st (st s0 o) (fun w => n w - o w) u := by
  unfold st
  obtain ⟨b, hb'⟩ : ∃ b, n u = o u + b := ⟨n u - o u, by omega⟩
  have e2 : n u - o u = b := by omega
  simp only [hb', e2]
  generalize o u = a
  cases s0 u <;> rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;> simp [Nat.add_mod, ha, hb]

/-- A long alternative `a` corresponds to a window alternative `a'`: every window cause, shifted, is in `a`, and
every cause of `a` is a shifted window cause or lies before the window (on a dependency node). -/
def AltCorr (Dv : List α) (o : α → Nat) (a a' : List (α × Nat)) : Prop :=
  (∀ q ∈ a', (q.1, q.2 + o q.1) ∈ a) ∧
  (∀ p ∈ a, (∃ q ∈ a', p = (q.1, q.2 + o q.1)) ∨ (p.1 ∈ Dv ∧ p.2 < o p.1))

theorem altIn_corr {Dv : List α} {o n : α → Nat} {a a' : List (α × Nat)} (hc : AltCorr Dv o a a')
    (hbox : ∀ u ∈ Dv, o u ≤ n u) (hD : ∀ q ∈ a', q.1 ∈ Dv) :
    AltIn n a ↔ AltIn (fun w => n w - o w) a' := by
  constructor
  · intro h q hq
    have h1 := h _ (hc.1 q hq)
    have h2 := hbox q.1 (hD q hq)
    simp only at h1 ⊢; omega
  · intro h p hp
    rcases hc.2 p hp with ⟨q, hq, rfl⟩ | ⟨hpD, hpo⟩
    · have h1 := h q hq
      have h2 := hbox q.1 (hD q hq)
      simp only at h1 ⊢; omega
    · have := hbox p.1 hpD; omega

/-- Two lists related elementwise (core Lean has no `List.Forall₂`). -/
inductive Pw {β γ : Type} (R : β → γ → Prop) : List β → List γ → Prop
  | nil : Pw R [] []
  | cons {b : β} {c : γ} {l : List β} {l' : List γ} : R b c → Pw R l l' → Pw R (b :: l) (c :: l')

theorem forall₂_mem_left {β γ : Type} {R : β → γ → Prop} :
    ∀ {l : List β} {l' : List γ}, Pw R l l' → ∀ b ∈ l, ∃ c ∈ l', R b c
  | _, _, .nil => by simp
  | _, _, .cons (b := b) (c := c) hbc hrest => by
    intro b' hb'
    rcases List.mem_cons.1 hb' with rfl | h
    · exact ⟨c, by simp, hbc⟩
    · obtain ⟨c', hc', hr⟩ := forall₂_mem_left hrest b' h
      exact ⟨c', by simp [hc'], hr⟩

theorem forall₂_mem_right {β γ : Type} {R : β → γ → Prop} :
    ∀ {l : List β} {l' : List γ}, Pw R l l' → ∀ c ∈ l', ∃ b ∈ l, R b c
  | _, _, .nil => by simp
  | _, _, .cons (b := b) (c := c) hbc hrest => by
    intro c' hc'
    rcases List.mem_cons.1 hc' with rfl | h
    · exact ⟨b, by simp, hbc⟩
    · obtain ⟨b', hb', hr⟩ := forall₂_mem_right hrest c' h
      exact ⟨b', by simp [hb'], hr⟩

/-- Causes of `v`'s window events, shifted, correspond to the long certificate's. -/
def CausesCorr (C C' : Cert α) (Dv : List α) (o : α → Nat) (v : α) : Prop :=
  ∀ k, k < C'.len v → k + o v < C.len v ∧ Pw (AltCorr Dv o) (C.causes v (k + o v)) (C'.causes v k)

theorem alts_corr {C C' : Cert α} {Dv : List α} {o n : α → Nat} {v : α} (hcs : CausesCorr C C' Dv o v)
    (hbox : ∀ u ∈ Dv, o u ≤ n u) (hcD : ∀ k, k < C'.len v → ∀ alt ∈ C'.causes v k, ∀ q ∈ alt, q.1 ∈ Dv)
    (k : Nat) (hk : k < C'.len v) :
    (∃ alt ∈ C.causes v (k + o v), AltIn n alt) ↔ (∃ alt ∈ C'.causes v k, AltIn (fun w => n w - o w) alt) := by
  have hF := (hcs k hk).2
  constructor
  · rintro ⟨a, ha, hin⟩
    obtain ⟨a', ha', hr⟩ := forall₂_mem_left hF a ha
    exact ⟨a', ha', (altIn_corr hr hbox (hcD k hk a' ha')).1 hin⟩
  · rintro ⟨a', ha', hin⟩
    obtain ⟨a, ha, hr⟩ := forall₂_mem_right hF a' ha'
    exact ⟨a, ha, (altIn_corr hr hbox (hcD k hk a' ha')).2 hin⟩

/-- **Enabledness inside the box** is the window's. -/
theorem enabled_window {C C' : Cert α} {Dv : List α} {o n : α → Nat} {v : α} (hcs : CausesCorr C C' Dv o v)
    (hbox : ∀ u ∈ Dv, o u ≤ n u) (hv : v ∈ Dv) (hlen : n v < C.len v ↔ n v - o v < C'.len v)
    (hcD : ∀ k, k < C'.len v → ∀ alt ∈ C'.causes v k, ∀ q ∈ alt, q.1 ∈ Dv) :
    Enabled C n v ↔ Enabled C' (fun w => n w - o w) v := by
  have hov := hbox v hv
  have e : n v = (n v - o v) + o v := by omega
  constructor
  · rintro ⟨h1, h2⟩
    have hk := hlen.1 h1
    refine ⟨hk, ?_⟩
    rw [e] at h2
    exact (alts_corr hcs hbox hcD _ hk).1 h2
  · rintro ⟨h1, h2⟩
    refine ⟨hlen.2 h1, ?_⟩
    rw [e]
    exact (alts_corr hcs hbox hcD _ h1).2 h2

/-! ## Guards -/

/-- A window guard shifted by the offsets `o` (events) and `co` (claim indices). -/
def shiftG (o : α → Nat) (co : Nat) (g : Guard α) : Guard α :=
  { ci := g.ci + co, st := g.st.map (fun w => (w.1, w.2 + o w.1)), en := g.en.map (fun w => (w.1, w.2 + o w.1)) }

theorem guardOn_shift {Dv : List α} {o n : α → Nat} (co : Nat) (g : Guard α) (hbox : ∀ u ∈ Dv, o u ≤ n u)
    (hgD : (∀ w, g.st = some w → w.1 ∈ Dv) ∧ (∀ w, g.en = some w → w.1 ∈ Dv)) :
    guardOn n (shiftG o co g) = guardOn (fun w => n w - o w) g := by
  unfold guardOn shiftG
  cases hs : g.st with
  | none =>
    cases he : g.en with
    | none => rfl
    | some w =>
      have := hbox w.1 (hgD.2 w he)
      simp only [Option.map]
      simp only [Bool.true_and]
      apply Bool.eq_iff_iff.2; simp only [decide_eq_true_eq]; omega
  | some w =>
    have h1 := hbox w.1 (hgD.1 w hs)
    cases he : g.en with
    | none =>
      simp only [Option.map, Bool.and_true]
      apply Bool.eq_iff_iff.2; simp only [decide_eq_true_eq]; omega
    | some w' =>
      have h2 := hbox w'.1 (hgD.2 w' he)
      simp only [Option.map]
      apply Bool.eq_iff_iff.2; simp only [Bool.and_eq_true, decide_eq_true_eq]; omega

theorem find?_pre {β : Type} {p : β → Bool} :
    ∀ (pre l : List β), (∀ g ∈ pre, p g = false) → (pre ++ l).find? p = l.find? p
  | [], l, _ => rfl
  | a :: pre, l, h => by
    simp only [List.cons_append, List.find?_cons, h a (by simp)]
    exact find?_pre pre l (fun g hg => h g (by simp [hg]))

theorem find?_post {β : Type} {p : β → Bool} :
    ∀ (l post : List β), (∀ g ∈ post, p g = false) → (l ++ post).find? p = l.find? p
  | [], post, h => by
    simp only [List.nil_append, List.find?_nil]
    induction post with
    | nil => rfl
    | cons a t ih =>
      simp only [List.find?_cons, h a (by simp)]
      exact ih (fun g hg => h g (by simp [hg]))
  | a :: l, post, h => by
    simp only [List.cons_append, List.find?_cons]
    split
    · rfl
    · exact find?_post l post h

theorem find?_map' {β γ : Type} (f : β → γ) (p : γ → Bool) :
    ∀ (l : List β), (l.map f).find? p = (l.find? (fun b => p (f b))).map f
  | [] => rfl
  | a :: l => by
    simp only [List.map_cons, List.find?_cons]
    split <;> simp_all [find?_map' f p l]

/-- How the long certificate's guards of one data pin sit around the window's. -/
def GuardsCorr (C' : Cert α) (Dv : List α) (o : α → Nat) (co : Nat) (cl cl' : List (Claim α))
    (gs gs' : List (Guard α)) : Prop :=
  ∃ pre post, gs = pre ++ gs'.map (shiftG o co) ++ post ∧
    (∀ g ∈ pre, ∃ w, g.en = some w ∧ w.1 ∈ Dv ∧ w.2 < o w.1) ∧
    (∀ g ∈ post, ∃ w, g.st = some w ∧ w.1 ∈ Dv ∧ o w.1 + C'.len w.1 ≤ w.2) ∧
    (∀ g ∈ gs', (∀ w, g.st = some w → w.1 ∈ Dv) ∧ (∀ w, g.en = some w → w.1 ∈ Dv)) ∧
    (∀ g ∈ gs', (cl[g.ci + co]?).map Claim.val = (cl'[g.ci]?).map Claim.val)

/-- **The data value a guard gives inside the box** is the window's. -/
theorem dv_window {C' : Cert α} {Dv : List α} {o n : α → Nat} {co : Nat} {cl cl' : List (Claim α)}
    {gs gs' : List (Guard α)} (hg : GuardsCorr C' Dv o co cl cl' gs gs')
    (hbox : ∀ u ∈ Dv, o u ≤ n u ∧ n u ≤ o u + C'.len u) :
    dv cl gs n = dv cl' gs' (fun w => n w - o w) := by
  obtain ⟨pre, post, rfl, hpre, hpost, hgD, hcl⟩ := hg
  have hbox1 : ∀ u ∈ Dv, o u ≤ n u := fun u hu => (hbox u hu).1
  unfold dv
  rw [find?_post _ post (fun g hg => by
        obtain ⟨w, hw, hwD, hwo⟩ := hpost g hg
        have := (hbox w.1 hwD).2
        unfold guardOn; rw [hw]; simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; left; omega),
      find?_pre pre _ (fun g hg => by
        obtain ⟨w, hw, hwD, hwo⟩ := hpre g hg
        have := (hbox w.1 hwD).1
        unfold guardOn; rw [hw]; simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; right; omega),
      find?_map']
  have hcongr : gs'.find? (fun b => guardOn n (shiftG o co b)) = gs'.find? (guardOn (fun w => n w - o w)) := by
    have : ∀ l : List (Guard α), (∀ g ∈ l, g ∈ gs') →
        l.find? (fun b => guardOn n (shiftG o co b)) = l.find? (guardOn (fun w => n w - o w)) := by
      intro l hl
      induction l with
      | nil => rfl
      | cons a t ih =>
        simp only [List.find?_cons]
        rw [guardOn_shift co a hbox1 (hgD a (hl a (by simp)))]
        split
        · rfl
        · exact ih (fun g hg => hl g (by simp [hg]))
    exact this gs' (fun g hg => hg)
  rw [hcongr]
  cases hf : gs'.find? (guardOn (fun w => n w - o w)) with
  | none => rfl
  | some g =>
    have hgm : g ∈ gs' := List.mem_of_find?_eq_some hf
    simp only [Option.map, shiftG]
    exact hcl g hgm

/-! ## The local check -/

/-- **The long local check inside a window's box, from the window's local check.** -/
theorem lcheckXA_window {N : TNet α} {dat : α → Bool} {envEn : α → (α → Bool) → Bool} {s0 s0' : α → Bool}
    {C C' : Cert α} {L L' : α → Nat → α → Nat} {D : α → List α} {cl cl' : List (Claim α)}
    {gd gd' : α → α → List (Guard α)} {v : α} (o : α → Nat) (co : Nat)
    (hc : LCheckXA N dat envEn s0' C' L' D cl' gd' v)
    (hv : v ∈ D v)
    (hT : ∀ s s' : α → Bool, (∀ u ∈ D v, s u = s' u) → (∀ u, dat u = true → s u = s' u) →
      tEn N envEn v s = tEn N envEn v s')
    (hs0 : ∀ u ∈ D v, s0' u = st s0 o u)
    (hcs : ∀ k, k < C'.len v → k + o v < C.len v ∧
      Pw (AltCorr (D v) o) (C.causes v (k + o v)) (C'.causes v k))
    (hcD : ∀ k, k < C'.len v → ∀ alt ∈ C'.causes v k, ∀ q ∈ alt, q.1 ∈ D v)
    (hgd : ∀ z, dat z = true → z ∈ N.pins v → GuardsCorr C' (D v) o co cl cl' (gd v z) (gd' v z))
    (hL : ∀ a ∈ D v, ∀ b ∈ D v, ∀ k, k < C'.len a → L' a k b = 0 ∨ L' a k b + o b ≤ L a (k + o a) b)
    (n : α → Nat) (hbox : ∀ u ∈ D v, o u ≤ n u ∧ n u ≤ o u + C'.len u)
    (hlen : n v < C.len v ↔ n v - o v < C'.len v)
    (hn1 : ∀ a ∈ D v, ∀ b ∈ D v, ∀ k, k < n a → L a k b ≤ n b)
    (hown : ∀ k, k < n v → ∃ alt ∈ C.causes v k, AltIn n alt)
    (bb : α → Bool) (hbb : ∀ z, dat z = true → z ∈ N.pins v → ∀ val, dv cl (gd v z) n = some val → bb z = val) :
    tEn N envEn v (mix dat (st s0 n) bb) = true ↔ Enabled C n v := by
  let n' : α → Nat := fun w => n w - o w
  have hbox1 : ∀ u ∈ D v, o u ≤ n u := fun u hu => (hbox u hu).1
  have hov := hbox1 v hv
  have h := hc n' (fun u hu => by have := hbox u hu; simp only [n']; omega)
    (fun a ha b hb k hk => by
      have ha' := hbox a ha
      have hb' := hbox b hb
      simp only [n'] at hk ⊢
      rcases hL a ha b hb k (by omega) with h0 | h1
      · rw [h0]; exact Nat.zero_le _
      · have := hn1 a ha b hb (k + o a) (by omega)
        omega)
    (fun k hk => by
      have hk' : k < C'.len v := by have := hbox v hv; simp only [n'] at hk; omega
      have := hown (k + o v) (by simp only [n'] at hk; omega)
      exact (alts_corr hcs hbox1 hcD k hk').1 this)
    bb (fun z hz hzp val hval => hbb z hz hzp val (by rw [dv_window (hgd z hz hzp) hbox]; exact hval))
  have hst : tEn N envEn v (mix dat (st s0 n) bb) = tEn N envEn v (mix dat (st s0' n') bb) := by
    apply hT
    · intro u hu
      unfold mix
      split
      · rfl
      · have e := st_shiftA s0 o n u (hbox1 u hu)
        rw [e]
        show st (st s0 o) n' u = st s0' n' u
        simp only [st, hs0 u hu]
    · intro u hu; unfold mix; simp [hu]
  rw [hst, h]
  exact (enabled_window hcs hbox1 hv hlen hcD).symm

end Formal.Net.AO
