import Formal.Net.OccNet

/-!
# AND-OR occurrence-net certificates (shard C, S4; replaces the AND-only `Net/OccNet` for instances)

**Problem, plainly.** On THE target about 1,400 control gates fire on the FIRST of two concurrent inputs (an OR, or
an AND-OR mux tree; JOURNAL-C 2026-11-08): their event has several alternative cause sets, any one of which enables
it, and the other input's later change is absorbed. `Net/OccNet` lists causes that must ALL happen, so it cannot
certify such a run. Here each event has a list of **alternatives**, each a list of causes (a disjunction of
conjunctions); an ideal must contain, for each of its events, all causes of at least one alternative. Bounds `L`
are per reader node (`L v a k b`), because one reader's timing may need a weaker bound than another's.

**Proved (generic):** `ideal_bump`, `enabled_of_not_full` (an ideal that is not full has an enabled event: no
deadlock), `lsound_of_step` (bounds justified one step back, through EVERY alternative, are sound in every ideal).
Time stamps must decrease along every cause of every alternative (the AND-OR graph is acyclic).

**Not shown here:** the timed theorems (`AO/Timed`).
-/

namespace Formal.Net.AO

variable {α : Type} [DecidableEq α]

structure Cert (α : Type) where
  len : α → Nat
  causes : α → Nat → List (List (α × Nat))
  tm : α → Nat → Nat

open Formal.Net.OccNet (st)

/-- All causes of the alternative have happened. -/
def AltIn (c : α → Nat) (alt : List (α × Nat)) : Prop := ∀ p ∈ alt, p.2 < c p.1

def Ideal (C : Cert α) (c : α → Nat) : Prop :=
  ∀ u, c u ≤ C.len u ∧ ∀ k, k < c u → ∃ alt ∈ C.causes u k, AltIn c alt

def Enabled (C : Cert α) (c : α → Nat) (v : α) : Prop :=
  c v < C.len v ∧ ∃ alt ∈ C.causes v (c v), AltIn c alt

def bump (c : α → Nat) (v : α) : α → Nat := fun u => if u = v then c u + 1 else c u

theorem altIn_mono {c c' : α → Nat} (hle : ∀ w, c w ≤ c' w) {alt : List (α × Nat)} (h : AltIn c alt) :
    AltIn c' alt := fun p hp => Nat.lt_of_lt_of_le (h p hp) (hle p.1)

theorem ideal_bump {C : Cert α} {c : α → Nat} {v : α} (hc : Ideal C c) (he : Enabled C c v) :
    Ideal C (bump c v) := by
  have hle : ∀ w, c w ≤ bump c v w := by intro w; unfold bump; split <;> omega
  intro u
  by_cases h : u = v
  · subst h
    refine ⟨by unfold bump; simp; exact he.1, fun k hk => ?_⟩
    unfold bump at hk; simp at hk
    rcases Nat.lt_or_ge k (c u) with hk' | hk'
    · obtain ⟨alt, ha, hin⟩ := (hc u).2 k hk'
      exact ⟨alt, ha, altIn_mono hle hin⟩
    · have : k = c u := by omega
      subst this
      obtain ⟨alt, ha, hin⟩ := he.2
      exact ⟨alt, ha, altIn_mono hle hin⟩
  · refine ⟨by unfold bump; simp [h]; exact (hc u).1, fun k hk => ?_⟩
    unfold bump at hk; simp [h] at hk
    obtain ⟨alt, ha, hin⟩ := (hc u).2 k hk
    exact ⟨alt, ha, altIn_mono hle hin⟩

/-- Time stamps: increasing along each node's events and along every cause of every alternative; causes name
existing events. -/
def TmOK (C : Cert α) : Prop :=
  (∀ u k, k + 1 < C.len u → C.tm u k < C.tm u (k + 1)) ∧
  (∀ u k, k < C.len u → ∀ alt ∈ C.causes u k, ∀ p ∈ alt, p.2 < C.len p.1 ∧ C.tm p.1 p.2 < C.tm u k)

theorem tm_mono {C : Cert α} (hT : TmOK C) (u : α) : ∀ a b, a ≤ b → b < C.len u → C.tm u a ≤ C.tm u b := by
  intro a b hab hb
  induction b with
  | zero => have : a = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ b ih =>
    rcases Nat.lt_or_ge a (b + 1) with h | h
    · exact Nat.le_trans (ih (by omega) (by omega)) (Nat.le_of_lt (hT.1 u b hb))
    · have : a = b + 1 := by omega
      subst this; exact Nat.le_refl _

theorem tm_prev {C : Cert α} (hT : TmOK C) (w : α) (j : Nat) (hj : 0 < j) (hl : j < C.len w) :
    C.tm w (j - 1) < C.tm w j := by
  have := hT.1 w (j - 1) (by omega)
  rwa [show j - 1 + 1 = j by omega] at this

/-- **No deadlock.** In an ideal that is not full, some node's next event is enabled. -/
theorem enabled_of_not_full {C : Cert α} (hT : TmOK C) {c : α → Nat} (hc : Ideal C c) (hne : ∀ u k, C.causes u k ≠ []) :
    ∀ N u, c u < C.len u → C.tm u (c u) ≤ N → ∃ v, Enabled C c v := by
  intro N
  refine Nat.strongRecOn N ?_
  intro N ih u hu hN
  -- take any alternative of `(u, c u)`; if one of its causes is missing, recurse on it
  obtain ⟨alt, halt⟩ := List.exists_mem_of_ne_nil _ (hne u (c u))
  by_cases hall : AltIn c alt
  · exact ⟨u, hu, alt, halt, hall⟩
  · simp only [AltIn, Classical.not_forall] at hall
    obtain ⟨p, hp, hlt⟩ := hall
    have hlt' : c p.1 ≤ p.2 := Nat.le_of_not_lt (by simpa using hlt)
    obtain ⟨hpl, hpt⟩ := hT.2 u (c u) hu alt halt p hp
    have hw : c p.1 < C.len p.1 := Nat.lt_of_le_of_lt hlt' hpl
    have hm := tm_mono hT p.1 (c p.1) p.2 hlt' hpl
    exact ih (C.tm p.1 (c p.1)) (by omega) p.1 hw (Nat.le_refl _)

/-! ## Bounds per reader -/

/-- `L a k w`: at least `L a k w` events of `w` are at or below `(a, k)` in every ideal containing it. -/
def LSound (C : Cert α) (L : α → Nat → α → Nat) : Prop :=
  ∀ c, Ideal C c → ∀ u k w, k < c u → L u k w ≤ c w

/-- The bound one alternative justifies. -/
def altBound (L : α → Nat → α → Nat) (alt : List (α × Nat)) (w : α) : Nat :=
  alt.foldr (fun p m => max m (max (L p.1 p.2 w) (if p.1 = w then p.2 + 1 else 0))) 0

/-- One step: through the node itself, its previous event, and EVERY alternative. -/
def LStep (C : Cert α) (L : α → Nat → α → Nat) : Prop :=
  ∀ u k w, k < C.len u →
    (L u k w ≤ (if u = w then k + 1 else 0) ∨ (0 < k ∧ L u k w ≤ L u (k - 1) w) ∨
      ∀ alt ∈ C.causes u k, L u k w ≤ altBound L alt w)

theorem altBound_le {L : α → Nat → α → Nat} {w : α} {B : Nat} :
    ∀ (alt : List (α × Nat)), (∀ p ∈ alt, L p.1 p.2 w ≤ B ∧ (p.1 = w → p.2 + 1 ≤ B)) → altBound L alt w ≤ B
  | [], _ => by simp [altBound]
  | a :: t, h => by
    simp only [altBound, List.foldr] at *
    have ha := h a (by simp)
    have := altBound_le t (fun p hp => h p (by simp [hp]))
    simp only [altBound] at this
    refine Nat.max_le.2 ⟨this, Nat.max_le.2 ⟨ha.1, ?_⟩⟩
    split
    · exact ha.2 (by assumption)
    · exact Nat.zero_le _

theorem lsound_of_step {C : Cert α} {L : α → Nat → α → Nat} (hT : TmOK C) (hL : LStep C L) : LSound C L := by
  intro c hc
  suffices H : ∀ N u k w, k < c u → C.tm u k ≤ N → L u k w ≤ c w by
    intro u k w hk; exact H _ u k w hk (Nat.le_refl _)
  intro N
  refine Nat.strongRecOn N ?_
  intro N ih u k w hk hN
  have hkl : k < C.len u := Nat.lt_of_lt_of_le hk (hc u).1
  rcases hL u k w hkl with h | ⟨hk0, h⟩ | h
  · refine Nat.le_trans h ?_
    split
    · rename_i h'; subst h'; exact hk
    · exact Nat.zero_le _
  · exact Nat.le_trans h (ih (C.tm u (k - 1)) (by have := tm_prev hT u k hk0 hkl; omega) u (k - 1) w (by omega)
      (Nat.le_refl _))
  · obtain ⟨alt, halt, hin⟩ := (hc u).2 k hk
    refine Nat.le_trans (h alt halt) (altBound_le alt (fun p hp => ⟨?_, fun he => ?_⟩))
    · obtain ⟨_, hpt⟩ := hT.2 u k hkl alt halt p hp
      exact ih (C.tm p.1 p.2) (by omega) p.1 p.2 w (hin p hp) (Nat.le_refl _)
    · subst he; exact hin p hp

/-- **The local check at `v`** with reader-specific bounds `L v`. -/
def LCheck (en : α → (α → Bool) → Bool) (s0 : α → Bool) (C : Cert α) (L : α → Nat → α → Nat)
    (D : α → List α) (v : α) : Prop :=
  ∀ n : α → Nat, (∀ u ∈ D v, n u ≤ C.len u) → (∀ u ∈ D v, ∀ w ∈ D v, ∀ k, k < n u → L u k w ≤ n w) →
    (en v (st s0 n) = true ↔ Enabled C n v)

/-- Sum over a list of nodes. -/
def sumOver (U : List α) (f : α → Nat) : Nat := U.foldr (fun u acc => f u + acc) 0

theorem sumOver_zero (U : List α) : sumOver U (fun _ => 0) = 0 := by
  induction U with
  | nil => rfl
  | cons a U ih => simp only [sumOver, List.foldr] at *; omega

theorem sumOver_le {U : List α} {f g : α → Nat} (h : ∀ u ∈ U, f u ≤ g u) : sumOver U f ≤ sumOver U g := by
  induction U with
  | nil => simp [sumOver]
  | cons a U ih =>
    simp only [sumOver, List.foldr] at *
    have := h a (by simp)
    have := ih (fun u hu => h u (by simp [hu]))
    omega

theorem sumOver_lt {U : List α} {f g : α → Nat} (hle : ∀ u ∈ U, f u ≤ g u) (v : α) (hv : v ∈ U)
    (hlt : f v < g v) : sumOver U f < sumOver U g := by
  induction U with
  | nil => simp at hv
  | cons a U ih =>
    simp only [sumOver, List.foldr] at *
    have h1 := sumOver_le (U := U) (f := f) (g := g) (fun u hu => hle u (by simp [hu]))
    simp only [sumOver] at h1
    by_cases hva : v = a
    · subst hva; omega
    · have := ih (fun u hu => hle u (by simp [hu])) (by simpa [hva] using hv)
      have := hle a (by simp)
      omega

end Formal.Net.AO
