import Formal.Net.AO.Window

/-!
# Window certificates: the separation and upper-bound tables (shard C, all-pairs route)

**Problem, plainly.** `Window.lcheckXA_window` lifts the local check from a window certificate to a long one. The
timed theorem also needs the long certificate's separation table (`SepOKA`) and upper-bound table (`UpOKA`) to be
justified. When the long tables, on a window's events, are the window's tables shifted by the offsets `o`, and time
stamps are shifted by a constant, each long entry's justification is the window entry's, shifted.

**Proved:** `sepClause_window` (every clause of `SepOKA` for a shifted window entry), `upClause_window` (the same
for `UpOKA`, given a justification for each long cause that lies before the window, and for the previous event of
a node's first window event).

Also `toRow_window` (a skew row of `TOA`) and `guardTime_window` (a shifted guard and claim).

**Not shown here:** that the long tables consist only of shifted window entries (an instance property), coverage,
the claim checks (`GateProof`, `ChainOK`).
-/

namespace Formal.Net.AO
open Formal.Net.OccNet.Timed Formal.Net.OccNet.TimedX Formal.Net.OccNet.TimedR

variable {α : Type} [DecidableEq α]

/-- One clause set of `SepOKA` for the entry `Sep b m a k = some d`. -/
def SepClause (N : TNet α) (CP : Cert α) (Sep : α → Nat → α → Nat → Option Nat)
    (Up : α × Nat → α × Nat → Option Nat) (b : α) (m : Nat) (a : α) (k d : Nat) : Prop :=
  (b = a ∧ m = k ∧ d = 0) ∨
  (∀ alt ∈ CP.causes a k, ∃ p ∈ alt, ∃ d', Sep b m p.1 p.2 = some d' ∧ d ≤ d' + lo' N a p.1) ∨
  (0 < k ∧ ∃ d', Sep b m a (k - 1) = some d' ∧ d ≤ d' + lo' N a a) ∨
  (1 ≤ d ∧ ∃ e0 : α × Nat, ∃ dl du, Sep e0.1 e0.2 a k = some dl ∧ Up e0 (b, m) = some du ∧ d + du ≤ dl ∧
    CP.tm e0.1 e0.2 < CP.tm b m)

theorem sepOKA_iff (N : TNet α) (CP : Cert α) (Sep : α → Nat → α → Nat → Option Nat)
    (Up : α × Nat → α × Nat → Option Nat) :
    SepOKA N CP Sep Up ↔ ∀ b m a k d, k < CP.len a → Sep b m a k = some d → SepClause N CP Sep Up b m a k d :=
  Iff.rfl

section
variable {N : TNet α} {C C' : Cert α} {Sep Sep' : α → Nat → α → Nat → Option Nat}
  {Up Up' : α × Nat → α × Nat → Option Nat} {o : α → Nat} {B : Nat}

/-- **A shifted window entry of the separation table is justified.** -/
theorem sepClause_window
    (hT' : TmOK C')
    (hSep : ∀ b m a k, m < C'.len b → k < C'.len a → Sep b (m + o b) a (k + o a) = Sep' b m a k)
    (hUp : ∀ e0 e : α × Nat, e0.2 < C'.len e0.1 → e.2 < C'.len e.1 →
      Up (e0.1, e0.2 + o e0.1) (e.1, e.2 + o e.1) = Up' e0 e)
    (hTm : ∀ u k, k < C'.len u → C.tm u (k + o u) = B + C'.tm u k)
    (hSepDom : ∀ b m a k d, Sep' b m a k = some d → m < C'.len b ∧ k < C'.len a)
    (Dv : List α) (a : α) (hcs : ∀ k, k < C'.len a → k + o a < C.len a ∧
      Pw (AltCorr Dv o) (C.causes a (k + o a)) (C'.causes a k))
    (b : α) (m k d : Nat) (hk : k < C'.len a) (hm : m < C'.len b) (hW : SepClause N C' Sep' Up' b m a k d) :
    SepClause N C Sep Up b (m + o b) a (k + o a) d := by
  rcases hW with ⟨rfl, rfl, rfl⟩ | h2 | ⟨hk0, d', hd', hle⟩ | ⟨hd1, e0, dl, du, hdl, hdu, hle, htm⟩
  · exact Or.inl ⟨rfl, rfl, rfl⟩
  · right; left
    intro alt halt
    obtain ⟨alt', halt', hcor⟩ := forall₂_mem_left (hcs k hk).2 alt halt
    obtain ⟨p, hp, d', hd', hle⟩ := h2 alt' halt'
    have hpl : p.2 < C'.len p.1 := (hT'.2 a k hk alt' halt' p hp).1
    refine ⟨(p.1, p.2 + o p.1), hcor.1 p hp, d', ?_, hle⟩
    rw [hSep b m p.1 p.2 hm hpl]; exact hd'
  · right; right; left
    refine ⟨by omega, d', ?_, hle⟩
    have := hSep b m a (k - 1) hm (by omega)
    rw [show k + o a - 1 = k - 1 + o a by omega, this]; exact hd'
  · right; right; right
    obtain ⟨he1, -⟩ := hSepDom _ _ _ _ _ hdl
    refine ⟨hd1, (e0.1, e0.2 + o e0.1), dl, du, ?_, ?_, hle, ?_⟩
    · rw [hSep e0.1 e0.2 a k he1 hk]; exact hdl
    · have := hUp e0 (b, m) he1 hm
      simp only at this; rw [this]; exact hdu
    · rw [hTm _ _ he1, hTm _ _ hm]; omega

end

/-- A cause `p` of an upper-bound step towards `e`, justified relative to `e0` (the three forms of `UpOKA`). -/
def UpCause (N : TNet α) (Sep : α → Nat → α → Nat → Option Nat) (Up : α × Nat → α × Nat → Option Nat)
    (e0 : α × Nat) (v : α) (p : α × Nat) (d : Nat) : Prop :=
  (∃ dp, Up e0 p = some dp ∧ dp + hi' N v p.1 ≤ d) ∨
  (∃ ds, Sep p.1 p.2 e0.1 e0.2 = some ds ∧ hi' N v p.1 ≤ d) ∨
  (∃ a dA dS, Up a p = some dA ∧ Sep a.1 a.2 e0.1 e0.2 = some dS ∧ dA + hi' N v p.1 ≤ d + dS)

/-- One clause set of `UpOKA` for the entry `Up e0 e = some d`. -/
def UpClause (N : TNet α) (dat : α → Bool) (CP : Cert α) (Sep : α → Nat → α → Nat → Option Nat)
    (Up : α × Nat → α × Nat → Option Nat) (e0 e : α × Nat) (d : Nat) : Prop :=
  e = e0 ∨
  (N.gate e.1 = true ∧ dat e.1 = false ∧ e.2 < CP.len e.1 ∧
    (∃ alt ∈ CP.causes e.1 e.2, ∀ p ∈ alt, UpCause N Sep Up e0 e.1 p d) ∧
    (0 < e.2 → UpCause N Sep Up e0 e.1 (e.1, e.2 - 1) d))

theorem upOKA_iff (N : TNet α) (dat : α → Bool) (CP : Cert α) (Sep : α → Nat → α → Nat → Option Nat)
    (Up : α × Nat → α × Nat → Option Nat) :
    UpOKA N dat CP Sep Up ↔ ∀ e0 e d, Up e0 e = some d → UpClause N dat CP Sep Up e0 e d :=
  Iff.rfl

section
variable {N : TNet α} {dat : α → Bool} {C C' : Cert α} {Sep Sep' : α → Nat → α → Nat → Option Nat}
  {Up Up' : α × Nat → α × Nat → Option Nat} {o : α → Nat}

/-- Shift an event by the offsets. -/
def shE (o : α → Nat) (e : α × Nat) : α × Nat := (e.1, e.2 + o e.1)

theorem upCause_window
    (hSep : ∀ b m a k, m < C'.len b → k < C'.len a → Sep b (m + o b) a (k + o a) = Sep' b m a k)
    (hUp : ∀ e0 e : α × Nat, e0.2 < C'.len e0.1 → e.2 < C'.len e.1 → Up (shE o e0) (shE o e) = Up' e0 e)
    (hSepDom : ∀ b m a k d, Sep' b m a k = some d → m < C'.len b ∧ k < C'.len a)
    (hUpDom : ∀ e0 e d, Up' e0 e = some d → e0.2 < C'.len e0.1 ∧ e.2 < C'.len e.1)
    (e0 : α × Nat) (he0 : e0.2 < C'.len e0.1) (v : α) (p : α × Nat) (hp : p.2 < C'.len p.1) (d : Nat)
    (h : UpCause N Sep' Up' e0 v p d) : UpCause N Sep Up (shE o e0) v (shE o p) d := by
  rcases h with ⟨dp, hdp, hle⟩ | ⟨ds, hds, hle⟩ | ⟨a, dA, dS, hdA, hdS, hle⟩
  · exact Or.inl ⟨dp, by rw [hUp e0 p he0 hp]; exact hdp, hle⟩
  · exact Or.inr (Or.inl ⟨ds, by simp only [shE]; rw [hSep p.1 p.2 e0.1 e0.2 hp he0]; exact hds, hle⟩)
  · have ha := (hUpDom a p dA hdA).1
    refine Or.inr (Or.inr ⟨shE o a, dA, dS, ?_, ?_, hle⟩)
    · rw [hUp a p ha hp]; exact hdA
    · simp only [shE]; rw [hSep a.1 a.2 e0.1 e0.2 ha he0]; exact hdS

/-- **A shifted window entry of the upper-bound table is justified**, when every cause of the long alternative that
is not a shifted window cause (it lies before the window) has its own justification (`hExtra`). -/
theorem upClause_window (hT' : TmOK C')
    (hSep : ∀ b m a k, m < C'.len b → k < C'.len a → Sep b (m + o b) a (k + o a) = Sep' b m a k)
    (hUp : ∀ e0 e : α × Nat, e0.2 < C'.len e0.1 → e.2 < C'.len e.1 → Up (shE o e0) (shE o e) = Up' e0 e)
    (hSepDom : ∀ b m a k d, Sep' b m a k = some d → m < C'.len b ∧ k < C'.len a)
    (hUpDom : ∀ e0 e d, Up' e0 e = some d → e0.2 < C'.len e0.1 ∧ e.2 < C'.len e.1)
    (Dv : List α) (e0 e : α × Nat) (d : Nat)
    (hcs : ∀ k, k < C'.len e.1 → k + o e.1 < C.len e.1 ∧
      Pw (AltCorr Dv o) (C.causes e.1 (k + o e.1)) (C'.causes e.1 k))
    (hExtra : ∀ p, p.2 < o p.1 → UpCause N Sep Up (shE o e0) e.1 p d)
    (hprevW : 0 < e.2 + o e.1 → e.2 = 0 → UpCause N Sep Up (shE o e0) e.1 (e.1, e.2 + o e.1 - 1) d)
    (hd : Up' e0 e = some d) (hW : UpClause N dat C' Sep' Up' e0 e d) :
    UpClause N dat C Sep Up (shE o e0) (shE o e) d := by
  obtain ⟨he0, he⟩ := hUpDom e0 e d hd
  rcases hW with rfl | ⟨hg, hdat, hlen, ⟨alt', halt', hall⟩, hprev⟩
  · exact Or.inl rfl
  · right
    refine ⟨hg, hdat, (hcs e.2 he).1, ?_, ?_⟩
    · obtain ⟨alt, halt, hcor⟩ := forall₂_mem_right (hcs e.2 he).2 alt' halt'
      refine ⟨alt, halt, fun p hp => ?_⟩
      rcases hcor.2 p hp with ⟨q, hq, rfl⟩ | ⟨_, hpo⟩
      · have hql : q.2 < C'.len q.1 := (hT'.2 e.1 e.2 hlen alt' halt' q hq).1
        exact upCause_window hSep hUp hSepDom hUpDom e0 he0 e.1 q hql d (hall q hq)
      · exact hExtra p hpo
    · intro hpos
      by_cases h0 : e.2 = 0
      · exact hprevW hpos h0
      · have := upCause_window (N := N) hSep hUp hSepDom hUpDom e0 he0 e.1 (e.1, e.2 - 1) (by simp only; omega) d
          (hprev (by omega))
        simp only [shE] at this ⊢
        rw [show e.2 + o e.1 - 1 = e.2 - 1 + o e.1 by omega]; exact this

end

/-! ## Skew rows and guard timing -/

/-- One row of `TOA`, for reader `v`, sources `a ≠ b`, event `k` of `a`. -/
def TORow (N : TNet α) (CP : Cert α) (L : α → α → Nat → α → Nat) (Sep : α → Nat → α → Nat → Option Nat)
    (v a b : α) (k : Nat) : Prop :=
  (∃ d, Sep b (L v a k b - 1) a k = some d ∧ hi' N v b ≤ lo' N v a + d) ∨
  (a = v ∧ ∃ k', k' ≤ k ∧ ∀ alt ∈ CP.causes v k', ∃ p ∈ alt, p.1 = b ∧ L v v k b ≤ p.2 + 1)

section
variable {N : TNet α} {C C' : Cert α} {Sep Sep' : α → Nat → α → Nat → Option Nat}
  {L L' : α → α → Nat → α → Nat} {o : α → Nat}

/-- **A window skew row gives the shifted long row**, when the reader's bound on `b` is the window's shifted. -/
theorem toRow_window
    (hSep : ∀ b m a k, m < C'.len b → k < C'.len a → Sep b (m + o b) a (k + o a) = Sep' b m a k)
    (Dv : List α) (v a b : α) (k : Nat) (hk : k < C'.len a)
    (hcs : ∀ k, k < C'.len v → k + o v < C.len v ∧
      Pw (AltCorr Dv o) (C.causes v (k + o v)) (C'.causes v k))
    (hL0 : 0 < L' v a k b) (hLb : L' v a k b - 1 < C'.len b)
    (hLa : L v a (k + o a) b = L' v a k b + o b)
    (hW : TORow N C' L' Sep' v a b k) : TORow N C L Sep v a b (k + o a) := by
  rcases hW with ⟨d, hd, hle⟩ | ⟨rfl, k', hk', hall⟩
  · left
    refine ⟨d, ?_, hle⟩
    rw [hLa, show L' v a k b + o b - 1 = (L' v a k b - 1) + o b by omega, hSep b _ a k hLb hk]
    exact hd
  · right
    refine ⟨rfl, k' + o a, by omega, fun alt halt => ?_⟩
    obtain ⟨alt', halt', hcor⟩ := forall₂_mem_left (hcs k' (by omega)).2 alt halt
    obtain ⟨p, hp, hpb, hle⟩ := hall alt' halt'
    refine ⟨(p.1, p.2 + o p.1), hcor.1 p hp, hpb, ?_⟩
    simp only
    have ho : o p.1 = o b := by rw [hpb]
    rw [hLa]; omega

/-- A claim shifted by the offsets. -/
def shC (o : α → Nat) (c : Claim α) : Claim α :=
  { c with A := c.A.map (shE o), B := c.B.map (shE o) }

/-- **Guard timing of a shifted guard and claim** follows from the window's. -/
theorem guardTime_window
    (hSep : ∀ b m a k, m < C'.len b → k < C'.len a → Sep b (m + o b) a (k + o a) = Sep' b m a k)
    (hSepDom : ∀ b m a k d, Sep' b m a k = some d → m < C'.len b ∧ k < C'.len a)
    (v z : α) (c : Claim α) (g : Guard α) (co : Nat)
    (hW : GuardTime N Sep' v z c g) : GuardTime N Sep v z (shC o c) (shiftG o co g) := by
  obtain ⟨hA, hB⟩ := hW
  refine ⟨?_, ?_⟩
  · cases hc : c.A with
    | none => simp [shC, hc]
    | some e =>
      rw [hc] at hA
      obtain ⟨w, hw, d, hd, hle⟩ := hA
      obtain ⟨h1, h2⟩ := hSepDom _ _ _ _ _ hd
      simp only [shC, hc, Option.map, shiftG, hw, shE]
      refine ⟨(w.1, w.2 + o w.1), rfl, d, ?_, hle⟩
      rw [hSep e.1 e.2 w.1 w.2 h1 h2]; exact hd
  · cases hc : c.B with
    | none => simp [shC, hc]
    | some e =>
      rw [hc] at hB
      obtain ⟨w, hw, d, hd, hle⟩ := hB
      obtain ⟨h1, h2⟩ := hSepDom _ _ _ _ _ hd
      simp only [shC, hc, Option.map, shiftG, hw, shE]
      refine ⟨(w.1, w.2 + o w.1), rfl, d, ?_, ?_⟩
      · rw [hSep w.1 w.2 e.1 e.2 h1 h2]; exact hd
      · exact hle

end

end Formal.Net.AO
