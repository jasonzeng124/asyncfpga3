import Formal.Net.TimedOcc

/-!
# Timed occurrence nets with a data layer: control events plus stable-window claims (shard C, S4)

**Problem, plainly.** `TimedOcc` needs every change of every node to be an event of the certificate. A
bundled-data datapath does not work that way: when a register's latches open together, the arithmetic behind
them glitches (bits arrive at different times), so its nodes change a data-dependent number of times. What
the design relies on instead is *bundling*: a control gate looks at a data node only while that node is
stable (`bd_steer`: `req & s` ignores `s` while `req` is low).

**The model.** Nodes are split by `dat`: *exact* nodes (control and environment handshakes), whose every change
is a certificate event as in `TimedOcc`, and *data* nodes, about which the certificate only makes **claims**: node
`z` has value `val` at every time `t` with `τ(A) + a ≤ t < τ(B) + b`, where `A`, `B` are exact events (or absent:
from the start, for ever) and `τ` is an event's time. Claims on free data nodes (the operand buses) are
assumptions (they are what H_ENV says); claims on data gates are proved.

**Checks (all local):**
* `CovOK`/`ValOK`: for a data-gate claim, each pin is covered by an exact input's value between two of its events,
  by a claim of its source, or left unknown (`X`); the gate's function gives `val` for every value of the unknown
  pins (Kleene: a definite output), and the covering windows contain every read time, which reduces to two
  separation inequalities per pin (`Sep` lower bounds only).
* guards: an exact gate may use a data input's value only in count vectors where a start witness has been read
  and an end witness has not; then the claim's window contains the read time (two separation inequalities).
  `LCheckX`: the local check where unguarded data inputs take every value.
* everything of `TimedOcc` for the exact nodes.

**Proved:** `timedX_follows`: at every time the exact nodes' count vector is an ideal, every exact change is a
certified event, and every claim holds.

**Not shown here:** liveness for this layer, any instance.
-/

namespace Formal.Net.OccNet.TimedX
open Formal.Net.OccNet Formal.Net.OccNet.Timed

variable {α : Type} [DecidableEq α]

/-- The behaviour hypotheses with a data layer: only exact nodes need be quiet before `t0`. -/
structure TBehX (N : TNet α) (dat : α → Bool) (envEn : α → (α → Bool) → Bool) (x : α → Nat → Bool)
    (r : α → α → Nat → Nat) (t0 H : Nat) : Prop where
  quiet : ∀ u s, dat u = false → t0 ≤ s + H → s ≤ t0 → x u s = x u t0
  rd : ∀ v w t, N.gate v = true → w ∈ N.pins v → t0 < t →
    N.lo v w ≤ t - r v w t ∧ t - r v w t ≤ N.hi v w ∧ r v w t ≤ t ∧ t0 ≤ r v w t + H
  lo1 : ∀ v w, N.gate v = true → w ∈ N.pins v → 1 ≤ N.lo v w
  mono : ∀ v w t t', N.gate v = true → w ∈ N.pins v → t0 < t → t ≤ t' → r v w t ≤ r v w t'
  geq : ∀ v t, N.gate v = true → t0 < t → x v t = N.F v ((N.pins v).map fun w => x w (r v w t))
  env : ∀ u t, N.gate u = false → dat u = false → t0 < t → x u t ≠ x u (t - 1) →
    envEn u (fun w => x w (t - 1)) = true

/-- Exact counts (0 at data nodes). -/
def cntE (dat : α → Bool) (x : α → Nat → Bool) (t0 : Nat) (u : α) (t : Nat) : Nat :=
  if dat u then 0 else cnt x t0 u t

/-- Event `e` happened by (integer) time `s`. -/
def hbI (x : α → Nat → Bool) (t0 : Nat) (e : α × Nat) (s : Int) : Prop := 0 ≤ s ∧ e.2 < cnt x t0 e.1 s.toNat

structure Claim (α : Type) where
  z : α
  val : Bool
  A : Option (α × Nat)
  a : Int
  B : Option (α × Nat)
  b : Nat

/-- The claim holds at `t`: inside its window, the node has its value. -/
def Holds (x : α → Nat → Bool) (t0 H : Nat) (c : Claim α) (t : Nat) : Prop :=
  t0 ≤ t + H →
  (match c.A with | none => True | some e => hbI x t0 e ((t : Int) - c.a)) →
  (match c.B with | none => True | some e => ¬ hbI x t0 e ((t : Int) - c.b)) →
  x c.z t = c.val

/-- How a data gate's claim covers one of its pins. -/
inductive Cov where
  | ex (k : Nat)   -- an exact source, between its events `k-1` and `k`
  | cl (i : Nat)   -- a claim of the source (index into the claim list)
  | X              -- unknown
  deriving DecidableEq

/-- The window and value a coverage stands for. -/
def covWin (s0 : α → Bool) (cl : List (Claim α)) (u : α) : Cov → Option (Claim α)
  | .ex k => some ⟨u, xor (s0 u) (k % 2 == 1), (if k = 0 then none else some (u, k - 1)), 0, some (u, k), 0⟩
  | .cl i => cl[i]?
  | .X => none

/-- Separation obligations for one covered pin (`hiZ`, `loZ`: the pin's delay bounds). -/
def CovTime (Sep : α → Nat → α → Nat → Option Nat) (c w : Claim α) (hiZ loZ : Nat) : Prop :=
  (match w.A with
    | none => True
    | some e' => ∃ e, c.A = some e ∧ ∃ d, Sep e'.1 e'.2 e.1 e.2 = some d ∧ (hiZ : Int) + w.a ≤ c.a + d) ∧
  (match w.B with
    | none => True
    | some e' => ∃ e, c.B = some e ∧ ∃ d, Sep e.1 e.2 e'.1 e'.2 = some d ∧ c.b ≤ loZ + w.b + d)

/-- A guard of an exact gate's data input: a claim index, a start witness (read) and an end witness (not read). -/
structure Guard (α : Type) where
  ci : Nat
  st : Option (α × Nat)
  en : Option (α × Nat)

def guardOn (n : α → Nat) (g : Guard α) : Bool :=
  (match g.st with | none => true | some (u, j) => decide (j < n u)) &&
  (match g.en with | none => true | some (u, i) => decide (n u ≤ i))

/-- The value an exact gate may use for data input `z` in count vector `n`. -/
def dv (cl : List (Claim α)) (gs : List (Guard α)) (n : α → Nat) : Option Bool :=
  match gs.find? (guardOn n) with
  | none => none
  | some g => (cl[g.ci]?).map Claim.val

/-- Separation obligations of a guard at gate `v` for data input `z`. -/
def GuardTime (N : TNet α) (Sep : α → Nat → α → Nat → Option Nat) (v z : α) (c : Claim α) (g : Guard α) : Prop :=
  (match c.A with
    | none => True
    | some e => ∃ w, g.st = some w ∧ ∃ d, Sep e.1 e.2 w.1 w.2 = some d ∧ (hi' N v z : Int) + c.a ≤ lo' N v w.1 + d) ∧
  (match c.B with
    | none => True
    | some e => ∃ w, g.en = some w ∧ ∃ d, Sep w.1 w.2 e.1 e.2 = some d ∧ hi' N v w.1 ≤ lo' N v z + c.b + d)

/-- Data values replace the exact state at data nodes. -/
def mix (dat : α → Bool) (s bb : α → Bool) : α → Bool := fun w => if dat w then bb w else s w

/-- **The local check with data inputs** at an exact node `v`. -/
def LCheckX (N : TNet α) (dat : α → Bool) (envEn : α → (α → Bool) → Bool) (s0 : α → Bool) (C : Cert α)
    (L : α → Nat → α → Nat) (D : α → List α) (cl : List (Claim α)) (gd : α → α → List (Guard α)) (v : α) : Prop :=
  ∀ n : α → Nat, (∀ u ∈ D v, n u ≤ C.len u) → (∀ u ∈ D v, ∀ w ∈ D v, ∀ k, k < n u → L u k w ≤ n w) →
    ∀ bb : α → Bool, (∀ z, dat z = true → z ∈ N.pins v → ∀ val, dv cl (gd v z) n = some val → bb z = val) →
      (tEn N envEn v (mix dat (st s0 n) bb) = true ↔ Enabled C n v)

/-- **The value check of a data-gate claim**: every value of the unknown pins gives the claimed value. -/
def ValOK (N : TNet α) (s0 : α → Bool) (cl : List (Claim α)) (c : Claim α) (cov : α → Cov) : Prop :=
  ∀ bb : α → Bool, (∀ u ∈ N.pins c.z, ∀ w, covWin s0 cl u (cov u) = some w → bb u = w.val) →
    N.F c.z ((N.pins c.z).map bb) = c.val

/-! ## Lemmas carried over from `TimedOcc` -/

section lem
variable {N : TNet α} {dat : α → Bool} {envEn : α → (α → Bool) → Bool} {x : α → Nat → Bool}
  {r : α → α → Nat → Nat} {t0 H : Nat} {C : Cert α} {L : α → Nat → α → Nat} {D : α → List α}
  {Sep : α → Nat → α → Nat → Option Nat}

theorem rho_boundsX (hb : TBehX N dat envEn x r t0 H) (v w : α) (s : Nat) (hs : t0 < s) :
    ρ N r v w s ≤ s - lo' N v w ∧ s - hi' N v w ≤ ρ N r v w s ∧ ρ N r v w s ≤ s - 1 ∧ t0 ≤ ρ N r v w s + H := by
  unfold ρ lo' hi'
  by_cases h : reads N v w = true
  · simp only [h, if_true]
    simp only [reads, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, h2, h3, h4⟩ := hb.rd v w s h.1 h.2 hs
    have := hb.lo1 v w h.1 h.2
    omega
  · simp only [h, if_false, Bool.false_eq_true]; omega

theorem rho_monoX (hb : TBehX N dat envEn x r t0 H) (v w : α) (s s' : Nat) (hs : t0 < s) (hss : s ≤ s') :
    ρ N r v w s ≤ ρ N r v w s' := by
  unfold ρ
  by_cases h : reads N v w = true
  · simp only [h, if_true]
    simp only [reads, Bool.and_eq_true, decide_eq_true_eq] at h
    exact hb.mono v w s s' h.1 h.2 hs hss
  · simp only [h, if_false, Bool.false_eq_true]; omega

/-- Separations are sound while every exact change so far was a certified event (`Sep` speaks only of exact
events). -/
theorem sep_soundX (hb : TBehX N dat envEn x r t0 H) (hT : TmOK C) (hS : SepOK N C Sep)
    (hSE : ∀ b m a k d, Sep b m a k = some d → dat a = false) (t : Nat)
    (hB : ∀ v s, dat v = false → t0 < s → s ≤ t → x v s ≠ x v (s - 1) → ChangeOK N C x t0 r v s) :
    ∀ M a k τ, C.tm a k ≤ M → τ ≤ t → k < cnt x t0 a τ → ∀ b m d, Sep b m a k = some d →
      m < cnt x t0 b (τ - d) := by
  intro M
  refine Nat.strongRecOn M ?_
  intro M ih a k τ hM hτ hk b m d hd
  obtain ⟨s, hs0, hsτ, hs1, hs2, hch⟩ := event_time a k τ hk
  obtain ⟨hfb, hen⟩ := hB a s (hSE b m a k d hd) hs0 (by omega) hch
  have hna : nT N x t0 r a s a = k := by
    unfold nT ρ
    by_cases h : reads N a a = true
    · simp only [h, if_true]; rw [hfb h, hs1]
    · simp only [h, if_false, Bool.false_eq_true]; exact hs1
  have hkl : k < C.len a := hna ▸ hen.1
  rcases hS b m a k d hkl hd with ⟨hb', hm, hd0⟩ | ⟨p, hp, d', hd', hle⟩ | ⟨hk0, d', hd', hle⟩
  · subst hb' hm hd0; simpa using hk
  · have hpc : p.2 < nT N x t0 r a s p.1 := hen.2 p (hna ▸ hp)
    obtain ⟨_, htm⟩ := hT.2 a k hkl p hp
    obtain ⟨r1, _, r3, _⟩ := rho_boundsX hb a p.1 s hs0
    have := ih (C.tm p.1 p.2) (by omega) p.1 p.2 (ρ N r a p.1 s) (Nat.le_refl _) (by omega) hpc b m d' hd'
    exact Nat.lt_of_lt_of_le this (cnt_mono b _ _ (by omega))
  · have hprev : k - 1 < cnt x t0 a (ρ N r a a s) := by
      have : cnt x t0 a (ρ N r a a s) = k := hna
      omega
    have htm : C.tm a (k - 1) < C.tm a k := by
      have := hT.1 a (k - 1) (by omega)
      rwa [show k - 1 + 1 = k by omega] at this
    obtain ⟨r1, _, r3, _⟩ := rho_boundsX hb a a s hs0
    have := ih (C.tm a (k - 1)) (by omega) a (k - 1) (ρ N r a a s) (Nat.le_refl _) (by omega) hprev b m d' hd'
    exact Nat.lt_of_lt_of_le this (cnt_mono b _ _ (by omega))

/-- Integer form: if `(a, k)` happened by `σ ≤ t` and `Sep b m a k = some d`, then `(b, m)` happened by `σ - d`. -/
theorem sep_hbI (hb : TBehX N dat envEn x r t0 H) (hT : TmOK C) (hS : SepOK N C Sep)
    (hSE : ∀ b m a k d, Sep b m a k = some d → dat a = false) (t : Nat)
    (hB : ∀ v s, dat v = false → t0 < s → s ≤ t → x v s ≠ x v (s - 1) → ChangeOK N C x t0 r v s)
    (a b : α) (k m d : Nat) (hd : Sep b m a k = some d) (σ : Int) (hσ : σ ≤ t) (h : hbI x t0 (a, k) σ) :
    hbI x t0 (b, m) (σ - d) := by
  obtain ⟨h0, h1⟩ := h
  have := sep_soundX hb hT hS hSE t hB _ a k σ.toNat (Nat.le_refl _) (by omega) h1 b m d hd
  refine ⟨?_, ?_⟩
  · rcases Nat.lt_or_ge σ.toNat d with hlt | hge
    · exfalso; rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)] at this; simp [cnt] at this
    · omega
  · have e : (σ - d).toNat = σ.toNat - d := by omega
    rw [e]; exact this

theorem hbI_mono {x : α → Nat → Bool} {t0 : Nat} {e : α × Nat} {s s' : Int} (h : hbI x t0 e s) (hs : s ≤ s') :
    hbI x t0 e s' :=
  ⟨by have := h.1; omega, Nat.lt_of_lt_of_le h.2 (cnt_mono e.1 _ _ (by have := h.1; omega))⟩

/-- The read tuple respects the bounds on `D v` (exact nodes only). -/
theorem read_consistentX (hb : TBehX N dat envEn x r t0 H) (hT : TmOK C) (hLs : LSound C L) (hS : SepOK N C Sep)
    (hSE : ∀ b m a k d, Sep b m a k = some d → dat a = false)
    (hTO : TO N C L D Sep) (hDE : ∀ v u, u ∈ D v → dat u = false) (t : Nat) (ht : t0 ≤ t)
    (hI : ∀ τ, τ ≤ t → Ideal C (fun u => cntE dat x t0 u τ))
    (hB : ∀ v s, dat v = false → t0 < s → s ≤ t → x v s ≠ x v (s - 1) → ChangeOK N C x t0 r v s) (v : α) :
    ∀ a ∈ D v, ∀ b ∈ D v, ∀ k, k < nT N x t0 r v (t + 1) a → L a k b ≤ nT N x t0 r v (t + 1) b := by
  intro a ha b hbD k hk
  have hae := hDE v a ha
  have hbe := hDE v b hbD
  obtain ⟨ra1, ra2, ra3, _⟩ := rho_boundsX hb v a (t + 1) (by omega)
  obtain ⟨rb1, rb2, rb3, _⟩ := rho_boundsX hb v b (t + 1) (by omega)
  let τa := ρ N r v a (t + 1)
  have hIa := hI τa (by omega)
  have hk' : k < cntE dat x t0 a τa := by simp only [cntE, hae]; exact hk
  have hL1 : L a k b ≤ cntE dat x t0 b τa := hLs _ hIa a k b hk'
  simp only [cntE, hbe] at hL1
  unfold nT
  by_cases hle : τa ≤ ρ N r v b (t + 1)
  · exact Nat.le_trans hL1 (cnt_mono b _ _ hle)
  · by_cases hL0 : L a k b = 0
    · rw [hL0]; exact Nat.zero_le _
    · have hkl : k < C.len a := by
        have := (hIa a).1; simp only [cntE, hae] at this; exact Nat.lt_of_lt_of_le hk this
      obtain ⟨d, hd, hdle⟩ := hTO v a b k ha hbD hkl (by omega) (by omega)
      have := sep_soundX hb hT hS hSE t hB _ a k τa (Nat.le_refl _) (by omega) hk b (L a k b - 1) d hd
      have h2 := cnt_mono (x := x) (t0 := t0) b (τa - d) (ρ N r v b (t + 1)) (by omega)
      omega

end lem

/-! ## Reading data through guards and coverings -/

section reads
variable {N : TNet α} {dat : α → Bool} {envEn : α → (α → Bool) → Bool} {x : α → Nat → Bool}
  {r : α → α → Nat → Nat} {t0 H : Nat} {C : Cert α} {L : α → Nat → α → Nat} {D : α → List α}
  {Sep : α → Nat → α → Nat → Option Nat} {cl : List (Claim α)} {gd : α → α → List (Guard α)}

theorem find_some {l : List (Guard α)} {f : Guard α → Bool} {g : Guard α} (h : l.find? f = some g) :
    g ∈ l ∧ f g = true := ⟨List.mem_of_find?_eq_some h, List.find?_some h⟩

theorem cnt_pos {x : α → Nat → Bool} {t0 : Nat} {u : α} {k s : Nat} (h : k < cnt x t0 u s) : t0 < s := by
  rcases Nat.lt_or_ge t0 s with h1 | h1
  · exact h1
  · rw [cnt_le_t0 u s h1] at h; exact absurd h (Nat.not_lt_zero _)

/-- **A guarded data read is the claimed value.** -/
theorem guard_read (hb : TBehX N dat envEn x r t0 H) (hT : TmOK C) (hS : SepOK N C Sep)
    (hSE : ∀ b m a k d, Sep b m a k = some d → dat a = false) (t : Nat) (ht : t0 ≤ t)
    (hB : ∀ v s, dat v = false → t0 < s → s ≤ t → x v s ≠ x v (s - 1) → ChangeOK N C x t0 r v s)
    (hC : ∀ c ∈ cl, ∀ s, s ≤ t → Holds x t0 H c s)
    (v z : α) (hg : N.gate v = true) (hz : z ∈ N.pins v)
    (hGd : ∀ g ∈ gd v z, ∃ c, cl[g.ci]? = some c ∧ c.z = z ∧ GuardTime N Sep v z c g)
    (val : Bool) (hdv : dv cl (gd v z) (nT N x t0 r v (t + 1)) = some val) :
    x z (r v z (t + 1)) = val := by
  unfold dv at hdv
  split at hdv
  · cases hdv
  · rename_i g hf
    obtain ⟨hgm, hon⟩ := find_some hf
    obtain ⟨c, hc, hcz, hgt⟩ := hGd g hgm
    rw [hc] at hdv; simp only [Option.map_some, Option.some.injEq] at hdv
    have hcm : c ∈ cl := List.mem_of_getElem? hc
    subst hcz hdv
    have hrz : reads N v c.z = true := by simp [reads, hg, hz]
    have hρz : ρ N r v c.z (t + 1) = r v c.z (t + 1) := by simp [ρ, hrz]
    obtain ⟨z1, z2, z3, z4⟩ := rho_boundsX hb v c.z (t + 1) (by omega)
    rw [hρz] at z1 z2 z3 z4
    have hHolds := hC c hcm (r v c.z (t + 1)) (by omega)
    apply hHolds z4
    · -- start
      obtain ⟨hgA, _⟩ := hgt
      cases hA : c.A with
      | none => trivial
      | some e =>
        rw [hA] at hgA
        obtain ⟨w, hw, d, hd, hle⟩ := hgA
        simp only [guardOn, hw, Bool.and_eq_true, decide_eq_true_eq] at hon
        have hw1 := hon.1
        obtain ⟨w1, w2, w3, _⟩ := rho_boundsX hb v w.1 (t + 1) (by omega)
        have hw1' : w.2 < cnt x t0 w.1 (ρ N r v w.1 (t + 1)) := by simpa [nT] using hw1
        have := cnt_pos hw1'
        have hhb : hbI x t0 (w.1, w.2) (ρ N r v w.1 (t + 1) : Int) := ⟨by omega, by simpa using hw1'⟩
        have := sep_hbI hb hT hS hSE t hB w.1 e.1 w.2 e.2 d hd _ (by omega) hhb
        refine hbI_mono this ?_
        have : (hi' N v c.z : Int) = N.hi v c.z := by simp [hi', hrz]
        omega
    · -- end
      obtain ⟨_, hgB⟩ := hgt
      cases hB' : c.B with
      | none => trivial
      | some e =>
        rw [hB'] at hgB
        obtain ⟨w, hw, d, hd, hle⟩ := hgB
        simp only [guardOn, hw, Bool.and_eq_true, decide_eq_true_eq] at hon
        have hw2 := hon.2
        intro hE
        obtain ⟨w1, w2, w3, _⟩ := rho_boundsX hb v w.1 (t + 1) (by omega)
        have hlz : (lo' N v c.z : Int) = N.lo v c.z := by simp [lo', hrz]
        have := sep_hbI hb hT hS hSE t hB e.1 w.1 e.2 w.2 d hd _ (by omega) hE
        have h2 := hbI_mono this (s' := (ρ N r v w.1 (t + 1) : Int)) (by omega)
        have h3 := h2.2
        simp only [Int.toNat_natCast] at h3
        simp only [nT] at hw2
        omega

/-- **Window transfer**: if a claim's window contains `s` and a covering window's separations hold for a pin read
at `ρ ∈ [s - hi, s - lo]`, then the covering window contains `ρ`. -/
theorem win_transfer (hb : TBehX N dat envEn x r t0 H) (hT : TmOK C) (hS : SepOK N C Sep)
    (hSE : ∀ b m a k d, Sep b m a k = some d → dat a = false) (s : Nat)
    (hB : ∀ v s', dat v = false → t0 < s' → s' ≤ s → x v s' ≠ x v (s' - 1) → ChangeOK N C x t0 r v s')
    (c w : Claim α) (hi lo ρ' : Nat) (ha : 0 ≤ c.a) (hρ1 : s ≤ ρ' + hi) (hρ2 : ρ' + lo ≤ s)
    (hct : CovTime Sep c w hi lo)
    (hA : match c.A with | none => True | some e => hbI x t0 e ((s : Int) - c.a))
    (hBn : match c.B with | none => True | some e => ¬ hbI x t0 e ((s : Int) - c.b)) :
    (match w.A with | none => True | some e => hbI x t0 e ((ρ' : Int) - w.a)) ∧
    (match w.B with | none => True | some e => ¬ hbI x t0 e ((ρ' : Int) - w.b)) := by
  obtain ⟨hcA, hcB⟩ := hct
  refine ⟨?_, ?_⟩
  · cases hwA : w.A with
    | none => trivial
    | some e' =>
      rw [hwA] at hcA
      obtain ⟨e, he, d, hd, hle⟩ := hcA
      rw [he] at hA
      have := sep_hbI hb hT hS hSE s hB e.1 e'.1 e.2 e'.2 d hd _ (by omega) hA
      exact hbI_mono this (by omega)
  · cases hwB : w.B with
    | none => trivial
    | some e' =>
      rw [hwB] at hcB
      obtain ⟨e, he, d, hd, hle⟩ := hcB
      rw [he] at hBn
      intro hE
      have hpos := hE.1
      have := sep_hbI hb hT hS hSE s hB e'.1 e.1 e'.2 e.2 d hd _ (by omega) hE
      exact hBn (hbI_mono this (by omega))

/-- **One step for a data-gate claim.** -/
theorem claim_step (hb : TBehX N dat envEn x r t0 H) (hT : TmOK C) (hS : SepOK N C Sep)
    (hSE : ∀ b m a k d, Sep b m a k = some d → dat a = false) (t : Nat) (ht : t0 ≤ t)
    (hB : ∀ v s', dat v = false → t0 < s' → s' ≤ t + 1 → x v s' ≠ x v (s' - 1) → ChangeOK N C x t0 r v s')
    (hC : ∀ c ∈ cl, ∀ s, s ≤ t → Holds x t0 H c s)
    (c : Claim α) (hgz : N.gate c.z = true) (ha : 0 ≤ c.a) (cov : α → Cov)
    (hval : ValOK N (fun w => x w t0) cl c cov)
    (hcov : ∀ u ∈ N.pins c.z, ∀ w, covWin (fun w => x w t0) cl u (cov u) = some w →
      CovTime Sep c w (N.hi c.z u) (N.lo c.z u))
    (hkind : ∀ u ∈ N.pins c.z, (∀ k, cov u = .ex k → dat u = false) ∧
      (∀ i w, cov u = .cl i → cl[i]? = some w → w.z = u)) :
    Holds x t0 H c (t + 1) := by
  intro _ hA hBn
  rw [hb.geq c.z (t + 1) hgz (by omega)]
  apply hval
  intro u hu w hw
  obtain ⟨r1, r2, r3, r4⟩ := hb.rd c.z u (t + 1) hgz hu (by omega)
  have hlo := hb.lo1 c.z u hgz hu
  obtain ⟨wA, wB⟩ := win_transfer hb hT hS hSE (t + 1) hB c w (N.hi c.z u) (N.lo c.z u) (r c.z u (t + 1))
    ha (by omega) (by omega) (hcov u hu w hw) hA hBn
  obtain ⟨hk1, hk2⟩ := hkind u hu
  cases hc : cov u with
  | X => rw [hc] at hw; simp [covWin] at hw
  | cl i =>
    rw [hc] at hw
    simp only [covWin] at hw
    have hwz := hk2 i w hc hw
    have hwm : w ∈ cl := List.mem_of_getElem? hw
    have := hC w hwm (r c.z u (t + 1)) (by omega) (by omega) wA wB
    rw [hwz] at this; exact this
  | ex k =>
    rw [hc] at hw
    simp only [covWin, Option.some.injEq] at hw
    subst hw
    have hdu := hk1 k hc
    simp only at wA wB
    have hcnt : cnt x t0 u (r c.z u (t + 1)) = k := by
      have hle : cnt x t0 u (r c.z u (t + 1)) ≤ k := by
        rcases Nat.lt_or_ge k (cnt x t0 u (r c.z u (t + 1))) with h | h
        · exact absurd ⟨by omega, by simpa using h⟩ wB
        · exact h
      by_cases hk0 : k = 0
      · omega
      · simp only [hk0, if_false] at wA
        have := wA.2; simp at this; omega
    rw [x_eq_st u H (fun s' h1 h2 => hb.quiet u s' hdu h1 h2) _ r4]
    simp only [st, hcnt]

theorem pins_readX (hb : TBehX N dat envEn x r t0 H) (v : α) (hv : N.gate v = true) (s : Nat) (hs : t0 < s) :
    (N.pins v).map (fun w => x w (r v w s)) =
      (N.pins v).map (mix dat (st (fun w => x w t0) (nT N x t0 r v s)) (fun w => x w (r v w s))) := by
  apply List.map_congr_left
  intro w hw
  unfold mix
  cases hdw : dat w with
  | true => rfl
  | false =>
    simp only [Bool.false_eq_true, if_false]
    have hrd : reads N v w = true := by simp [reads, hv, hw]
    obtain ⟨_, _, _, h4⟩ := hb.rd v w s hv hw hs
    rw [x_eq_st w H (fun s' h1 h2 => hb.quiet w s' hdw h1 h2) _ h4]
    simp only [st, nT, ρ, hrd, if_true]

theorem st_nT_selfX (hb : TBehX N dat envEn x r t0 H) (v : α) (hve : dat v = false) (hnr : reads N v v = false)
    (t : Nat) (ht : t0 ≤ t) : st (fun w => x w t0) (nT N x t0 r v (t + 1)) v = x v t := by
  rw [x_eq_st v H (fun s' h1 h2 => hb.quiet v s' hve h1 h2) t (by omega)]
  simp [st, nT, ρ, hnr]

theorem change_okX (hb : TBehX N dat envEn x r t0 H) (hT : TmOK C) (hLs : LSound C L) (hS : SepOK N C Sep)
    (hSE : ∀ b m a k d, Sep b m a k = some d → dat a = false)
    (hTO : TO N C L D Sep) (hDE : ∀ v u, u ∈ D v → dat u = false)
    (hloc : ∀ v, dat v = false → LCheckX N dat envEn (fun w => x w t0) C L D cl gd v)
    (hgdF : ∀ v z, N.gate v = false → gd v z = [])
    (hGd : ∀ v z, N.gate v = true → z ∈ N.pins v → ∀ g ∈ gd v z, ∃ c, cl[g.ci]? = some c ∧ c.z = z ∧
      GuardTime N Sep v z c g)
    (t : Nat) (ht : t0 ≤ t) (hI : ∀ τ, τ ≤ t → Ideal C (fun u => cntE dat x t0 u τ))
    (hB : ∀ v s, dat v = false → t0 < s → s ≤ t → x v s ≠ x v (s - 1) → ChangeOK N C x t0 r v s)
    (hC : ∀ c ∈ cl, ∀ s, s ≤ t → Holds x t0 H c s)
    (v : α) (hve : dat v = false) (hch : x v (t + 1) ≠ x v t) : ChangeOK N C x t0 r v (t + 1) := by
  have hcons := read_consistentX hb hT hLs hS hSE hTO hDE t ht hI hB v
  have hlen : ∀ u ∈ D v, nT N x t0 r v (t + 1) u ≤ C.len u := by
    intro u hu
    obtain ⟨_, _, h3, _⟩ := rho_boundsX hb v u (t + 1) (by omega)
    have := (hI (ρ N r v u (t + 1)) (by omega) u).1
    simp only [cntE, hDE v u hu, Bool.false_eq_true, if_false] at this
    exact this
  have hq : ∀ u, dat u = false → ∀ s, t0 ≤ s + H → x u s = st (fun w => x w t0) (fun w => cnt x t0 w s) u :=
    fun u hu => x_eq_st (x := x) (t0 := t0) u H (fun s' h1 h2 => hb.quiet u s' hu h1 h2)
  have hsub : t + 1 - 1 = t := by omega
  show (reads N v v = true → cnt x t0 v (r v v (t + 1)) = cnt x t0 v (t + 1 - 1)) ∧
    Enabled C (nT N x t0 r v (t + 1)) v
  rw [hsub]
  cases hg : N.gate v with
  | false =>
    -- a free node
    have he := hb.env v (t + 1) hg hve (by omega) (by simpa [hsub] using hch)
    have hrd : reads N v v = false := by simp [reads, hg]
    refine ⟨fun h => absurd h (by simp [hrd]), ?_⟩
    have hL := hloc v hve (nT N x t0 r v (t + 1)) hlen hcons (fun w => x w t)
      (fun z _ _ val hdv => by rw [hgdF v z hg] at hdv; simp [dv] at hdv)
    apply hL.1
    unfold tEn; rw [hg]; simp only [Bool.false_eq_true, if_false]
    rw [hsub] at he
    have : (fun w => x w t) = mix dat (st (fun w => x w t0) (nT N x t0 r v (t + 1))) (fun w => x w t) := by
      funext w
      unfold mix
      cases hdw : dat w with
      | true => rfl
      | false =>
        have hrw : reads N v w = false := by simp [reads, hg]
        simp only [Bool.false_eq_true, if_false]
        rw [hq w hdw t (by omega)]; simp [st, nT, ρ, hrw]
    rw [← this]; exact he
  | true =>
    have hbb : ∀ z, dat z = true → z ∈ N.pins v → ∀ val,
        dv cl (gd v z) (nT N x t0 r v (t + 1)) = some val → x z (r v z (t + 1)) = val :=
      fun z _ hz val hdv => guard_read hb hT hS hSE t ht hB hC v z hg hz (hGd v z hg hz) val hdv
    have hL := hloc v hve (nT N x t0 r v (t + 1)) hlen hcons (fun w => x w (r v w (t + 1))) hbb
    have hgeq := hb.geq v (t + 1) hg (by omega)
    rw [pins_readX hb v hg (t + 1) (by omega)] at hgeq
    have hmixv : ∀ n : α → Nat, ∀ bb : α → Bool, mix dat (st (fun w => x w t0) n) bb v = st (fun w => x w t0) n v := by
      intro n bb; simp [mix, hve]
    by_cases hfb : reads N v v = true
    · -- a gate with a feedback pin
      let nv := nT N x t0 r v (t + 1) v
      have hnv : nv = cnt x t0 v (r v v (t + 1)) := by simp [nv, nT, ρ, hfb]
      obtain ⟨rv1, _, rv3, rv4⟩ := rho_boundsX hb v v (t + 1) (by omega)
      have hrle : r v v (t + 1) ≤ t := by
        have : ρ N r v v (t + 1) = r v v (t + 1) := by simp [ρ, hfb]
        omega
      have hnvle : nv ≤ cnt x t0 v t := by rw [hnv]; exact cnt_mono v _ _ hrle
      rcases Nat.lt_or_ge nv (cnt x t0 v t) with hlt | hge
      · -- stale feedback: no change can happen (contradiction)
        exfalso
        obtain ⟨s1, h1a, h1b, h1c, h1d, h1e⟩ := event_time (x := x) (t0 := t0) v nv t hlt
        obtain ⟨fb1, en1⟩ := hB v s1 hve h1a h1b h1e
        have hr_s1 : r v v (t + 1) < s1 := by
          rcases Nat.lt_or_ge (r v v (t + 1)) s1 with h | h
          · exact h
          · have := cnt_mono (x := x) (t0 := t0) v s1 (r v v (t + 1)) h
            rw [← hnv] at this; omega
        have hn1v : nT N x t0 r v s1 v = nv := by
          simp only [nT, ρ, hfb, if_true]; rw [fb1 hfb, h1c]
        have hEn : Enabled C (nT N x t0 r v (t + 1)) v := by
          refine enabled_mono en1 (by rw [hn1v]) (fun w => ?_)
          exact cnt_mono w _ _ (rho_monoX hb v w s1 (t + 1) h1a (by omega))
        have hen := hL.2 hEn
        unfold tEn at hen; rw [hg] at hen; simp only [if_true] at hen
        rw [hmixv, ← hgeq] at hen
        -- the state of `v` in the tuple is its value before event `nv`
        have hstv : st (fun w => x w t0) (nT N x t0 r v (t + 1)) v = x v (s1 - 1) := by
          rw [hq v hve (s1 - 1) (by omega)]; simp only [st, nT, ρ, hfb, if_true]; rw [← hnv, h1c]
        rw [hstv] at hen
        -- at most one event of `v` after the stale read
        have hcnt : cnt x t0 v t = nv + 1 := by
          rcases Nat.lt_or_ge (nv + 1) (cnt x t0 v t) with h2 | h2
          · exfalso
            obtain ⟨s2, h2a, h2b, h2c, _, h2e⟩ := event_time (x := x) (t0 := t0) v (nv + 1) t h2
            obtain ⟨fb2, _⟩ := hB v s2 hve h2a h2b h2e
            have := fb2 hfb
            have hs12 : s1 < s2 := by
              rcases Nat.lt_or_ge s1 s2 with h | h
              · exact h
              · have := cnt_mono (x := x) (t0 := t0) v s2 s1 h; omega
            have hm := hb.mono v v s2 (t + 1) hg (by simp [reads] at hfb; exact hfb.2) h2a (by omega)
            have := cnt_mono (x := x) (t0 := t0) v _ _ hm
            rw [← hnv] at this; omega
          · have := cnt_mono (x := x) (t0 := t0) v s1 t h1b
            omega
        have hxt : x v t = x v s1 := by
          rw [hq v hve t (by omega), hq v hve s1 (by omega)]; simp only [st]; rw [hcnt, h1d]
        apply hch
        rw [hxt]; exact bool3 hen h1e
      · -- current feedback
        have hnveq : nv = cnt x t0 v t := Nat.le_antisymm hnvle hge
        refine ⟨fun _ => by rw [← hnv, hnveq], ?_⟩
        apply hL.1
        unfold tEn; rw [hg]; simp only [if_true]
        rw [hmixv, ← hgeq]
        have : st (fun w => x w t0) (nT N x t0 r v (t + 1)) v = x v t := by
          rw [hq v hve t (by omega)]; simp only [st]; rw [show nT N x t0 r v (t + 1) v = nv from rfl, hnveq]
        rw [this]; simpa using hch
    · -- a gate without a feedback pin
      have hfb' : reads N v v = false := by simpa using hfb
      refine ⟨fun h => absurd h hfb, ?_⟩
      apply hL.1
      unfold tEn; rw [hg]; simp only [if_true]
      rw [hmixv, ← hgeq, st_nT_selfX hb v hve hfb' t ht]
      simpa using hch

theorem enabled_mono' {C : Cert α} {n n' : α → Nat} {v : α} (h : Enabled C n v) (hv : n v = n' v)
    (hle : ∀ p ∈ C.causes v (n v), n p.1 ≤ n' p.1) : Enabled C n' v :=
  ⟨hv ▸ h.1, fun p hp => Nat.lt_of_lt_of_le (h.2 p (hv ▸ hp)) (hle p (hv ▸ hp))⟩

/-- **Every bounded-delay behaviour follows the certificate, data layer included.** For every `t`: the exact
nodes' count vector is an ideal at every time up to `t`, every exact change is a certified event, and every claim
holds at every time up to `t`. Hypotheses on the data layer: each data-gate claim starts at or after its start
event (`0 ≤ a`) and has a covering with `ValOK`/`CovTime`; claims on free data nodes (the environment's buses) and
every claim before `t0` are given. -/
theorem timedX_follows (hb : TBehX N dat envEn x r t0 H) (hT : TmOK C) (hLs : LSound C L) (hS : SepOK N C Sep)
    (hSE : ∀ b m a k d, Sep b m a k = some d → dat a = false)
    (hTO : TO N C L D Sep) (hDE : ∀ v u, u ∈ D v → dat u = false)
    (hloc : ∀ v, dat v = false → LCheckX N dat envEn (fun w => x w t0) C L D cl gd v)
    (hgdF : ∀ v z, N.gate v = false → gd v z = [])
    (hGd : ∀ v z, N.gate v = true → z ∈ N.pins v → ∀ g ∈ gd v z, ∃ c, cl[g.ci]? = some c ∧ c.z = z ∧
      GuardTime N Sep v z c g)
    (hGC : ∀ c ∈ cl, N.gate c.z = true → 0 ≤ c.a ∧ ∃ cov : α → Cov, ValOK N (fun w => x w t0) cl c cov ∧
      (∀ u ∈ N.pins c.z, ∀ w, covWin (fun w => x w t0) cl u (cov u) = some w →
        CovTime Sep c w (N.hi c.z u) (N.lo c.z u)) ∧
      (∀ u ∈ N.pins c.z, (∀ k, cov u = .ex k → dat u = false) ∧ (∀ i w, cov u = .cl i → cl[i]? = some w → w.z = u)))
    (hEnvC : ∀ c ∈ cl, N.gate c.z = false → ∀ s, Holds x t0 H c s)
    (hInit : ∀ c ∈ cl, ∀ s, s ≤ t0 → Holds x t0 H c s)
    (hDataLen : ∀ u, dat u = true → C.len u = 0) :
    ∀ t, (∀ τ, τ ≤ t → Ideal C (fun u => cntE dat x t0 u τ)) ∧
      (∀ v s, dat v = false → t0 < s → s ≤ t → x v s ≠ x v (s - 1) → ChangeOK N C x t0 r v s) ∧
      (∀ c ∈ cl, ∀ s, s ≤ t → Holds x t0 H c s) := by
  have h0 : Ideal C (fun _ => 0) := fun u => ⟨Nat.zero_le _, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  have hz : ∀ τ, τ ≤ t0 → (fun u => cntE dat x t0 u τ) = fun _ => 0 := by
    intro τ hτ; funext u; unfold cntE; split
    · rfl
    · exact cnt_le_t0 u τ hτ
  intro t
  induction t with
  | zero =>
    refine ⟨fun τ hτ => ?_, fun v s _ h1 h2 => by omega, fun c hc s hs => hInit c hc s (by omega)⟩
    rw [hz τ (by omega)]; exact h0
  | succ t ih =>
    obtain ⟨hI, hB, hC⟩ := ih
    by_cases ht : t0 ≤ t
    · have hC1 : ∀ v, dat v = false → x v (t + 1) ≠ x v t → ChangeOK N C x t0 r v (t + 1) :=
        fun v hve hch => change_okX hb hT hLs hS hSE hTO hDE hloc hgdF hGd t ht hI hB hC v hve hch
      have hB' : ∀ v s, dat v = false → t0 < s → s ≤ t + 1 → x v s ≠ x v (s - 1) → ChangeOK N C x t0 r v s := by
        intro v s hve h1 h2 h3
        rcases Nat.lt_or_ge s (t + 1) with h | h
        · exact hB v s hve h1 (by omega) h3
        · have : s = t + 1 := by omega
          subst this; exact hC1 v hve (by simpa using h3)
      refine ⟨fun τ hτ => ?_, hB', fun c hc s hs => ?_⟩
      · rcases Nat.lt_or_ge τ (t + 1) with h | h
        · exact hI τ (by omega)
        · have : τ = t + 1 := by omega
          subst this
          apply ideal_step C (hI t (Nat.le_refl _))
          · intro u
            unfold cntE
            cases hdu : dat u with
            | true => left; rfl
            | false =>
              simp only [Bool.false_eq_true, if_false]
              rw [cnt_succ u t ht]
              by_cases hx : x u (t + 1) = x u t
              · left; simp [hx]
              · right
                refine ⟨by simp [hx], ?_⟩
                obtain ⟨hfb, hen⟩ := hC1 u hdu hx
                have e : nT N x t0 r u (t + 1) u = cnt x t0 u t := by
                  unfold nT ρ
                  by_cases h : reads N u u = true
                  · simp only [h, if_true]; rw [hfb h]; rfl
                  · simp only [h, if_false, Bool.false_eq_true]; rfl
                have hE : Enabled C (fun w => cntE dat x t0 w t) u := by
                  refine enabled_mono' hen (by simp [cntE, hdu, e]) (fun p hp => ?_)
                  have hlt : nT N x t0 r u (t + 1) u < C.len u := hen.1
                  obtain ⟨hpl, _⟩ := hT.2 u _ hlt p hp
                  have hpe : dat p.1 = false := by
                    cases hd : dat p.1 with
                    | false => rfl
                    | true => have := hDataLen p.1 hd; omega
                  obtain ⟨_, _, h3, _⟩ := rho_boundsX hb u p.1 (t + 1) (by omega)
                  simp only [nT, cntE, hpe, Bool.false_eq_true, if_false]
                  exact cnt_mono p.1 _ _ (by omega)
                exact hE
          · intro u; unfold cntE; split
            · exact Nat.le_refl _
            · exact cnt_mono u _ _ (by omega)
      · rcases Nat.lt_or_ge s (t + 1) with h | h
        · exact hC c hc s (by omega)
        · have : s = t + 1 := by omega
          subst this
          cases hgz : N.gate c.z with
          | false => exact hEnvC c hc hgz _
          | true =>
            obtain ⟨ha, cov, hval, hcov, hkind⟩ := hGC c hc hgz
            exact claim_step hb hT hS hSE t ht hB' hC c hgz ha cov hval hcov hkind
    · refine ⟨fun τ hτ => ?_, fun v s hve h1 h2 h3 => ?_, fun c hc s hs => hInit c hc s (by omega)⟩
      · rw [hz τ (by omega)]; exact h0
      · rcases Nat.lt_or_ge s (t + 1) with h | h
        · exact hB v s hve h1 (by omega) h3
        · omega

/-! ## Liveness with the data layer -/

/-- **An enabled exact gate event happens within `K`.** -/
theorem gate_firesX (hb : TBehX N dat envEn x r t0 H) (hT : TmOK C) (hLs : LSound C L) (hS : SepOK N C Sep)
    (hSE : ∀ b m a k d, Sep b m a k = some d → dat a = false)
    (hTO : TO N C L D Sep) (hDE : ∀ v u, u ∈ D v → dat u = false)
    (hloc : ∀ v, dat v = false → LCheckX N dat envEn (fun w => x w t0) C L D cl gd v)
    (hgdF : ∀ v z, N.gate v = false → gd v z = [])
    (hGd : ∀ v z, N.gate v = true → z ∈ N.pins v → ∀ g ∈ gd v z, ∃ c, cl[g.ci]? = some c ∧ c.z = z ∧
      GuardTime N Sep v z c g)
    (hGC : ∀ c ∈ cl, N.gate c.z = true → 0 ≤ c.a ∧ ∃ cov : α → Cov, ValOK N (fun w => x w t0) cl c cov ∧
      (∀ u ∈ N.pins c.z, ∀ w, covWin (fun w => x w t0) cl u (cov u) = some w →
        CovTime Sep c w (N.hi c.z u) (N.lo c.z u)) ∧
      (∀ u ∈ N.pins c.z, (∀ k, cov u = .ex k → dat u = false) ∧ (∀ i w, cov u = .cl i → cl[i]? = some w → w.z = u)))
    (hEnvC : ∀ c ∈ cl, N.gate c.z = false → ∀ s, Holds x t0 H c s)
    (hInit : ∀ c ∈ cl, ∀ s, s ≤ t0 → Holds x t0 H c s)
    (hDataLen : ∀ u, dat u = true → C.len u = 0)
    (v : α) (hve : dat v = false) (hg : N.gate v = true) (K : Nat) (hK : ∀ w ∈ N.pins v, N.hi v w < K) (hK1 : 1 ≤ K)
    (t : Nat) (ht : t0 ≤ t) (hen : Enabled C (fun u => cntE dat x t0 u t) v) :
    cnt x t0 v t < cnt x t0 v (t + K) := by
  rcases Nat.lt_or_ge (cnt x t0 v t) (cnt x t0 v (t + K - 1)) with hlt | hge
  · exact Nat.lt_of_lt_of_le hlt (cnt_mono v _ _ (by omega))
  · have hconst : ∀ τ, t ≤ τ → τ ≤ t + K - 1 → cnt x t0 v τ = cnt x t0 v t := by
      intro τ h1 h2
      have := cnt_mono (x := x) (t0 := t0) v t τ h1
      have := cnt_mono (x := x) (t0 := t0) v τ (t + K - 1) h2
      omega
    let t' := t + K - 1
    obtain ⟨hI, hB, hC⟩ := timedX_follows hb hT hLs hS hSE hTO hDE hloc hgdF hGd hGC hEnvC hInit hDataLen t'
    have hcons := read_consistentX hb hT hLs hS hSE hTO hDE t' (by omega) hI hB v
    have hlen : ∀ u ∈ D v, nT N x t0 r v (t' + 1) u ≤ C.len u := by
      intro u hu
      obtain ⟨_, _, h3, _⟩ := rho_boundsX hb v u (t' + 1) (by omega)
      have := (hI (ρ N r v u (t' + 1)) (by omega) u).1
      simp only [cntE, hDE v u hu, Bool.false_eq_true, if_false] at this
      exact this
    have hbb : ∀ z, dat z = true → z ∈ N.pins v → ∀ val,
        dv cl (gd v z) (nT N x t0 r v (t' + 1)) = some val → x z (r v z (t' + 1)) = val :=
      fun z _ hz val hdv => guard_read hb hT hS hSE t' (by omega) hB hC v z hg hz (hGd v z hg hz) val hdv
    have hL := hloc v hve (nT N x t0 r v (t' + 1)) hlen hcons (fun w => x w (r v w (t' + 1))) hbb
    have hρ : ∀ w, t ≤ ρ N r v w (t' + 1) := by
      intro w
      unfold ρ
      by_cases h : reads N v w = true
      · simp only [h, if_true]
        simp only [reads, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨_, h2, h3, _⟩ := hb.rd v w (t' + 1) h.1 h.2 (by omega)
        have := hK w h.2
        omega
      · simp only [h, if_false, Bool.false_eq_true]; omega
    have hnv : nT N x t0 r v (t' + 1) v = cnt x t0 v t := by
      have h1 := hρ v
      obtain ⟨_, _, h3, _⟩ := rho_boundsX hb v v (t' + 1) (by omega)
      exact hconst _ h1 (by omega)
    have hEn : Enabled C (nT N x t0 r v (t' + 1)) v := by
      refine enabled_mono' hen (by simp [cntE, hve, hnv]) (fun p hp => ?_)
      have hlt : (fun u => cntE dat x t0 u t) v < C.len v := hen.1
      obtain ⟨hpl, _⟩ := hT.2 v _ hlt p hp
      have hpe : dat p.1 = false := by
        cases hd : dat p.1 with
        | false => rfl
        | true => have := hDataLen p.1 hd; omega
      simp only [nT, cntE, hpe, Bool.false_eq_true, if_false]
      exact cnt_mono p.1 _ _ (hρ p.1)
    have he := hL.2 hEn
    unfold tEn at he; rw [hg] at he; simp only [if_true] at he
    have hgeq := hb.geq v (t' + 1) hg (by omega)
    rw [pins_readX hb v hg (t' + 1) (by omega)] at hgeq
    have hmixv : mix dat (st (fun w => x w t0) (nT N x t0 r v (t' + 1))) (fun w => x w (r v w (t' + 1))) v =
        st (fun w => x w t0) (nT N x t0 r v (t' + 1)) v := by simp [mix, hve]
    rw [hmixv, ← hgeq] at he
    have hst : st (fun w => x w t0) (nT N x t0 r v (t' + 1)) v = x v t' := by
      rw [x_eq_st v H (fun s' h1 h2 => hb.quiet v s' hve h1 h2) t' (by omega)]
      simp only [st]; rw [hnv, hconst t' (by omega) (Nat.le_refl _)]
    rw [hst] at he
    have hc := cnt_succ (x := x) (t0 := t0) v t' (by omega)
    have hx : (x v (t' + 1) != x v t') = true := he
    rw [hx] at hc
    have e : t' + 1 = t + K := by omega
    rw [← e, hc, hconst t' (by omega) (Nat.le_refl _)]
    simp

/-- **Liveness with the data layer.** If every enabled environment move eventually happens, every event of the
certificate happens: from some `T` on every exact node has had exactly its `len` changes and never changes again. -/
theorem timedX_live (hb : TBehX N dat envEn x r t0 H) (hT : TmOK C) (hLs : LSound C L) (hS : SepOK N C Sep)
    (hSE : ∀ b m a k d, Sep b m a k = some d → dat a = false)
    (hTO : TO N C L D Sep) (hDE : ∀ v u, u ∈ D v → dat u = false)
    (hloc : ∀ v, dat v = false → LCheckX N dat envEn (fun w => x w t0) C L D cl gd v)
    (hgdF : ∀ v z, N.gate v = false → gd v z = [])
    (hGd : ∀ v z, N.gate v = true → z ∈ N.pins v → ∀ g ∈ gd v z, ∃ c, cl[g.ci]? = some c ∧ c.z = z ∧
      GuardTime N Sep v z c g)
    (hGC : ∀ c ∈ cl, N.gate c.z = true → 0 ≤ c.a ∧ ∃ cov : α → Cov, ValOK N (fun w => x w t0) cl c cov ∧
      (∀ u ∈ N.pins c.z, ∀ w, covWin (fun w => x w t0) cl u (cov u) = some w →
        CovTime Sep c w (N.hi c.z u) (N.lo c.z u)) ∧
      (∀ u ∈ N.pins c.z, (∀ k, cov u = .ex k → dat u = false) ∧ (∀ i w, cov u = .cl i → cl[i]? = some w → w.z = u)))
    (hEnvC : ∀ c ∈ cl, N.gate c.z = false → ∀ s, Holds x t0 H c s)
    (hInit : ∀ c ∈ cl, ∀ s, s ≤ t0 → Holds x t0 H c s)
    (hDataLen : ∀ u, dat u = true → C.len u = 0)
    (U : List α) (hcov : ∀ u, 0 < C.len u → u ∈ U)
    (K : α → Nat) (hK : ∀ v, N.gate v = true → 1 ≤ K v ∧ ∀ w ∈ N.pins v, N.hi v w < K v)
    (henv : ∀ u t, N.gate u = false → dat u = false → t0 ≤ t → Enabled C (fun w => cntE dat x t0 w t) u →
      ∃ t', t < t' ∧ cnt x t0 u t < cnt x t0 u t') :
    ∃ T, t0 ≤ T ∧ (∀ u, cntE dat x t0 u T = C.len u) ∧ ∀ u s, dat u = false → T ≤ s → x u s = x u T := by
  have hfol := timedX_follows hb hT hLs hS hSE hTO hDE hloc hgdF hGd hGC hEnvC hInit hDataLen
  have hI : ∀ t, Ideal C (fun u => cntE dat x t0 u t) := fun t => (hfol t).1 t (Nat.le_refl _)
  have prog : ∀ t, t0 ≤ t → (∃ u, cntE dat x t0 u t < C.len u) →
      ∃ t', t < t' ∧ ∃ v, v ∈ U ∧ cntE dat x t0 v t < cntE dat x t0 v t' := by
    intro t ht ⟨u, hu⟩
    obtain ⟨v, hv⟩ := enabled_of_not_full hT (hI t) _ u hu (Nat.le_refl _)
    have hvl : 0 < C.len v := by have := hv.1; omega
    have hvU : v ∈ U := hcov v hvl
    have hve : dat v = false := by
      cases hd : dat v with
      | false => rfl
      | true => have := hDataLen v hd; omega
    cases hg : N.gate v with
    | true =>
      obtain ⟨hK1, hK2⟩ := hK v hg
      have := gate_firesX hb hT hLs hS hSE hTO hDE hloc hgdF hGd hGC hEnvC hInit hDataLen v hve hg (K v) hK2 hK1 t ht hv
      exact ⟨t + K v, by omega, v, hvU, by simp only [cntE, hve, Bool.false_eq_true, if_false]; exact this⟩
    | false =>
      obtain ⟨t', h1, h2⟩ := henv v t hg hve ht hv
      exact ⟨t', h1, v, hvU, by simp only [cntE, hve, Bool.false_eq_true, if_false]; exact h2⟩
  have hmonoE : ∀ u a b, a ≤ b → cntE dat x t0 u a ≤ cntE dat x t0 u b := by
    intro u a b hab; unfold cntE; split
    · exact Nat.le_refl _
    · exact cnt_mono u _ _ hab
  let M : Nat → Nat := fun t => sumOver U fun u => C.len u - cntE dat x t0 u t
  have hMdec : ∀ t t', t ≤ t' → ∀ v ∈ U, cntE dat x t0 v t < cntE dat x t0 v t' → M t' < M t := by
    intro t t' htt v hv hlt
    have hle : ∀ u ∈ U, C.len u - cntE dat x t0 u t' ≤ C.len u - cntE dat x t0 u t := fun u _ => by
      have := hmonoE u t t' htt; omega
    have hlt' : C.len v - cntE dat x t0 v t' < C.len v - cntE dat x t0 v t := by
      have := (hI t' v).1; simp only at this; omega
    exact sumOver_lt hle v hv hlt'
  have full : ∀ n t, t0 ≤ t → M t ≤ n → ∃ T, t ≤ T ∧ ∀ u, cntE dat x t0 u T = C.len u := by
    intro n
    induction n with
    | zero =>
      intro t ht hM
      refine ⟨t, Nat.le_refl _, fun u => ?_⟩
      rcases Nat.lt_or_ge (cntE dat x t0 u t) (C.len u) with hlt | hge
      · exfalso
        have hpos := hcov u (by omega)
        have := sumOver_lt (U := U) (f := fun _ => 0) (g := fun u => C.len u - cntE dat x t0 u t)
          (fun _ _ => Nat.zero_le _) u hpos (by omega)
        rw [sumOver_zero] at this
        simp only [M] at hM; omega
      · have := (hI t u).1; simp only at this; omega
    | succ n ih =>
      intro t ht hM
      by_cases hall : ∀ u, cntE dat x t0 u t = C.len u
      · exact ⟨t, Nat.le_refl _, hall⟩
      · simp only [Classical.not_forall] at hall
        obtain ⟨u, hu⟩ := hall
        obtain ⟨t', h1, v, hv, h2⟩ := prog t ht ⟨u, Nat.lt_of_le_of_ne (by have := (hI t u).1; simpa using this) hu⟩
        have := hMdec t t' (by omega) v hv h2
        obtain ⟨T, hT1, hT2⟩ := ih t' (by omega) (by omega)
        exact ⟨T, by omega, hT2⟩
  obtain ⟨T, hT1, hT2⟩ := full (M t0) t0 (Nat.le_refl _) (Nat.le_refl _)
  refine ⟨T, hT1, hT2, fun u s hue hs => ?_⟩
  have hc : ∀ s, T ≤ s → cnt x t0 u s = cnt x t0 u T := by
    intro s hs
    have h1 := hmonoE u T s hs
    have h2 := (hI s u).1
    simp only at h2
    have h3 := hT2 u
    simp only [cntE, hue, Bool.false_eq_true, if_false] at h1 h2 h3 ⊢
    omega
  rw [x_eq_st u H (fun s' h1 h2 => hb.quiet u s' hue h1 h2) s (by omega),
    x_eq_st u H (fun s' h1 h2 => hb.quiet u s' hue h1 h2) T (by omega)]
  simp only [st]; rw [hc s hs]

end reads

end Formal.Net.OccNet.TimedX
