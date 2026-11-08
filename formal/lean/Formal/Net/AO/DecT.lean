import Formal.Net.AO.Timed

/-!
# Boolean checkers for the AND-OR timing obligations (shard C)

`TimedOccDec` for `AO`: separation and upper-bound tables with lookups; `sepOKA_of_B` (form ii: in EVERY alternative
some cause carries the separation), `upOKA_of_B` (some alternative has all its upper bounds), `toA_of_B` (reader-
specific bounds, distinct sources, reader rows discharged by a cause in every alternative), `rtA_of_B`.
-/

namespace Formal.Net.AO
open Formal.Net.OccNet.Timed Formal.Net.OccNet.TimedX Formal.Net.OccNet.TimedR

variable {α : Type} [DecidableEq α]

/-- Separation table entries `(b, m, a, k, d)` and their lookup. -/
def sepL (sl : List (α × Nat × α × Nat × Nat)) (b : α) (m : Nat) (a : α) (k : Nat) : Option Nat :=
  (sl.find? fun e => e.1 == b && e.2.1 == m && e.2.2.1 == a && e.2.2.2.1 == k).map fun e => e.2.2.2.2

/-- Upper-bound table entries `(e0, e, d)` and their lookup. -/
def upL (ul : List ((α × Nat) × (α × Nat) × Nat)) (e0 e : α × Nat) : Option Nat :=
  (ul.find? fun q => q.1 == e0 && q.2.1 == e).map fun q => q.2.2

theorem find_map_some {β γ : Type} {l : List β} {f : β → Bool} {g : β → γ} {c : γ} (h : (l.find? f).map g = some c) :
    ∃ q, q ∈ l ∧ f q = true ∧ g q = c := by
  cases hf : l.find? f with
  | none => rw [hf] at h; cases h
  | some q =>
    rw [hf] at h; simp at h
    exact ⟨q, List.mem_of_find?_eq_some hf, List.find?_some hf, h⟩

theorem sepL_some {sl : List (α × Nat × α × Nat × Nat)} {b : α} {m : Nat} {a : α} {k d : Nat}
    (h : sepL sl b m a k = some d) : (b, m, a, k, d) ∈ sl ∨ ∃ e ∈ sl, e.1 = b ∧ e.2.1 = m ∧ e.2.2.1 = a ∧ e.2.2.2.1 = k ∧
      e.2.2.2.2 = d := by
  obtain ⟨q, hq, hf, hg⟩ := find_map_some h
  simp only [Bool.and_eq_true, beq_iff_eq] at hf
  exact Or.inr ⟨q, hq, hf.1.1.1, hf.1.1.2, hf.1.2, hf.2, hg⟩

section
variable (N : TNet α) (CP : Cert α) (sl : List (α × Nat × α × Nat × Nat)) (ul : List ((α × Nat) × (α × Nat) × Nat))

/-- The four forms for one key, with `d` the table's value. -/
def sepFormB (b : α) (m : Nat) (a : α) (k d : Nat) : Bool :=
  (b == a && m == k && d == 0) ||
  (CP.causes a k).all (fun alt => alt.any (fun p => match sepL sl b m p.1 p.2 with
    | some d' => decide (d ≤ d' + lo' N a p.1) | none => false)) ||
  (decide (0 < k) && match sepL sl b m a (k - 1) with
    | some d' => decide (d ≤ d' + lo' N a a) | none => false) ||
  (decide (1 ≤ d) && sl.any fun e => e.2.2.1 == a && e.2.2.2.1 == k &&
    match sepL sl e.1 e.2.1 a k, upL ul (e.1, e.2.1) (b, m) with
    | some dl, some du => decide (d + du ≤ dl) && decide (CP.tm e.1 e.2.1 < CP.tm b m)
    | _, _ => false)

/-- Every entry's key passes, with the looked-up value. -/
def sepB : Bool :=
  sl.all fun e => !(decide (e.2.2.2.1 < CP.len e.2.2.1)) ||
    match sepL sl e.1 e.2.1 e.2.2.1 e.2.2.2.1 with
    | some d => sepFormB N CP sl ul e.1 e.2.1 e.2.2.1 e.2.2.2.1 d
    | none => false

theorem sepOKR_of_B (h : sepB N CP sl ul = true) : SepOKA N CP (sepL sl) (upL ul) := by
  intro b m a k d hk hd
  obtain ⟨q, hq, hf, hg⟩ := find_map_some hd
  simp only [Bool.and_eq_true, beq_iff_eq] at hf
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hf
  unfold sepB at h
  have he := List.all_eq_true.1 h q hq
  rw [h1, h2, h3, h4] at he
  simp only [hk, decide_true, Bool.not_true, Bool.false_or] at he
  rw [hd] at he
  simp only [sepFormB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.any_eq_true, List.all_eq_true] at he
  rcases he with ((⟨⟨hb, hm⟩, hd0⟩ | hpall) | ⟨hk0, hpr⟩) | ⟨hd1, e, hel, hek⟩
  · exact Or.inl ⟨hb, hm, hd0⟩
  · right; left
    intro alt halt
    obtain ⟨p, hp, hpd⟩ := hpall alt halt
    cases hs : sepL sl b m p.1 p.2 with
    | none => rw [hs] at hpd; cases hpd
    | some d' => rw [hs] at hpd; exact ⟨p, hp, d', hs, by simpa using hpd⟩
  · right; right; left
    cases hs : sepL sl b m a (k - 1) with
    | none => rw [hs] at hpr; cases hpr
    | some d' => rw [hs] at hpr; exact ⟨hk0, d', rfl, by simpa using hpr⟩
  · right; right; right
    refine ⟨hd1, (e.1, e.2.1), ?_⟩
    obtain ⟨⟨ha, hkk⟩, hm⟩ := hek
    cases hs : sepL sl e.1 e.2.1 a k with
    | none => rw [hs] at hm; cases hm
    | some dl =>
      cases hu : upL ul (e.1, e.2.1) (b, m) with
      | none => rw [hs, hu] at hm; cases hm
      | some du =>
        rw [hs, hu] at hm
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
        exact ⟨dl, du, rfl, rfl, hm.1, hm.2⟩

end

section
variable (N : TNet α) (dat : α → Bool) (CP CF : Cert α) (sl : List (α × Nat × α × Nat × Nat))
  (ul : List ((α × Nat) × (α × Nat) × Nat))

def upFormB (e0 e : α × Nat) (d : Nat) : Bool :=
  (e == e0) ||
  (N.gate e.1 && !(dat e.1) && decide (e.2 < CP.len e.1) &&
    (CP.causes e.1 e.2).any (fun alt => alt.all (fun p => match upL ul e0 p with
      | some dp => decide (dp + hi' N e.1 p.1 ≤ d) | none => false)) &&
    (e.2 == 0 || (match upL ul e0 (e.1, e.2 - 1) with
      | some dp => decide (dp + hi' N e.1 e.1 ≤ d) | none => false) ||
      (match sepL sl e.1 (e.2 - 1) e0.1 e0.2 with
      | some _ => decide (hi' N e.1 e.1 ≤ d) | none => false)))

def upB : Bool := ul.all fun q => match upL ul q.1 q.2.1 with
  | some d => upFormB N dat CP sl ul q.1 q.2.1 d
  | none => false

theorem upOK_of_B (h : upB N dat CP sl ul = true) : UpOKA N dat CP (sepL sl) (upL ul) := by
  intro e0 e d hd
  obtain ⟨q, hq, hf, hg⟩ := find_map_some hd
  simp only [Bool.and_eq_true, beq_iff_eq] at hf
  obtain ⟨h1, h2⟩ := hf
  have he := List.all_eq_true.1 h q hq
  rw [h1, h2, hd] at he
  simp only [upFormB, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    List.all_eq_true, List.any_eq_true] at he
  rcases he with he | ⟨⟨⟨⟨hg1, hd1⟩, hl⟩, hc⟩, hp⟩
  · exact Or.inl he
  · right
    obtain ⟨alt, halt, hc'⟩ := hc
    refine ⟨hg1, hd1, hl, ⟨alt, halt, fun p hp' => ?_⟩, fun hk => ?_⟩
    · have := hc' p hp'
      cases hu : upL ul e0 p with
      | none => rw [hu] at this; cases this
      | some dp => rw [hu] at this; exact ⟨dp, rfl, by simpa using this⟩
    · rcases hp with (hp | hp) | hp
      · omega
      · left
        cases hu : upL ul e0 (e.1, e.2 - 1) with
        | none => rw [hu] at hp; cases hp
        | some dp => rw [hu] at hp; exact ⟨dp, rfl, by simpa using hp⟩
      · right
        cases hu : sepL sl e.1 (e.2 - 1) e0.1 e0.2 with
        | none => rw [hu] at hp; cases hp
        | some ds => rw [hu] at hp; exact ⟨ds, rfl, by simpa using hp⟩


end

section
variable (N : TNet α) (CF CP : Cert α) (sl : List (α × Nat × α × Nat × Nat))

/-- Reader rows: for some earlier event of the reader, every alternative has a cause on `b` high enough. -/
def readerRowB (L : α → α → Nat → α → Nat) (v b : α) (k : Nat) : Bool :=
  (List.range (k + 1)).any fun k' => (CP.causes v k').all fun alt =>
    alt.any fun p => p.1 == b && decide (L v v k b ≤ p.2 + 1)

def toAB (L : α → α → Nat → α → Nat) (D : α → List α) (V : List α) : Bool :=
  V.all fun v => (D v).all fun a => (D v).all fun b => (a == b) || (List.range (CF.len a)).all fun k =>
    (L v a k b == 0) || !(decide (lo' N v a < hi' N v b)) ||
      (match sepL sl b (L v a k b - 1) a k with
        | some d => decide (hi' N v b ≤ lo' N v a + d)
        | none => false) ||
      (a == v && readerRowB CP L v b k)

theorem toA_of_B (L : α → α → Nat → α → Nat) (D : α → List α) (V : List α) (hV : ∀ v, v ∉ V → D v = [])
    (h : toAB N CF CP sl L D V = true) : TOA N CF CP L D (sepL sl) := by
  intro v a b k ha hb hab hk hL hlt
  have hvV : v ∈ V := by
    by_cases hv : v ∈ V
    · exact hv
    · rw [hV v hv] at ha; simp at ha
  unfold toAB at h
  have := List.all_eq_true.1 h v hvV
  have := List.all_eq_true.1 this a ha
  have := List.all_eq_true.1 this b hb
  simp only [Bool.or_eq_true, beq_iff_eq] at this
  rcases this with h0 | h0
  · exact absurd h0 hab
  have := List.all_eq_true.1 h0 k (List.mem_range.2 hk)
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_false_iff_not, Bool.and_eq_true] at this
  rcases this with ((h1 | h1) | h1) | ⟨hav, hr⟩
  · omega
  · exact absurd hlt h1
  · left
    cases hs : sepL sl b (L v a k b - 1) a k with
    | none => rw [hs] at h1; cases h1
    | some d => rw [hs] at h1; exact ⟨d, rfl, by simpa using h1⟩
  · right
    refine ⟨hav, ?_⟩
    subst hav
    unfold readerRowB at hr
    simp only [List.any_eq_true, List.mem_range, List.all_eq_true, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at hr
    obtain ⟨k', hk', hall⟩ := hr
    exact ⟨k', by omega, fun alt halt => hall alt halt⟩

def rtAB (U : List α) : Bool :=
  U.all fun u => (List.range (CF.len u)).all fun k => (CP.causes u k).all fun altP =>
    (CF.causes u k).any fun altF => altF.all fun p =>
      altP.contains p || match sepL sl p.1 p.2 u k with
        | some d => decide (1 ≤ d)
        | none => false

theorem rtA_of_B (U : List α) (hcov : ∀ u, 0 < CF.len u → u ∈ U) (h : rtAB CF CP sl U = true) :
    ∀ u k, k < CF.len u → ∀ altP ∈ CP.causes u k, ∃ altF ∈ CF.causes u k, ∀ p ∈ altF,
      p ∈ altP ∨ ∃ d, sepL sl p.1 p.2 u k = some d ∧ 1 ≤ d := by
  intro u k hk altP haltP
  unfold rtAB at h
  have := List.all_eq_true.1 h u (hcov u (by omega))
  have := List.all_eq_true.1 this k (List.mem_range.2 hk)
  have := List.all_eq_true.1 this altP haltP
  obtain ⟨altF, haltF, hall⟩ := List.any_eq_true.1 this
  refine ⟨altF, haltF, fun p hp => ?_⟩
  have := List.all_eq_true.1 hall p hp
  simp only [Bool.or_eq_true, List.contains_iff_mem] at this
  rcases this with h1 | h1
  · exact Or.inl h1
  · right
    cases hs : sepL sl p.1 p.2 u k with
    | none => rw [hs] at h1; cases h1
    | some d => rw [hs] at h1; exact ⟨d, rfl, by simpa using h1⟩

end

end Formal.Net.AO
