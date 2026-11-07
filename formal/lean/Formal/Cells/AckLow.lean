import Formal.Cells.GrantExcl

/-!
# Formal.Cells.AckLow — the losing client's grant and acknowledge stay low (THE Spec semantics)

Shard B, THE goal, H_ARB(T). The arbiter's safety contract at gate level ("one acknowledge per transaction",
`ArbT.one_ack` / `ArbTSpec.spec_one_ack`, here for the collapsed relation with routed pins):
* `grant_low`: a grant gate that can be 1 only when its q pin reads `b` (tied pins at their values) is 0 on
  `[a + hi j, e + lo j]` (from its collapse start) whenever q's source shows `!b` on `[a, e]`.
* `ack_low`: an ack gate (C-element of the grant and the server's A0) whose INIT is 0 whenever its grant pin and its
  feedback pin both read 0 (tied pins at their values) stays 0 on `[s, e]` if it was 0 on `[s - hi fb, s - 1]` and
  its grant's source is 0 on `[s - hi g, e - lo g]`, whatever A0 does.
Together with H_ARB(T) (q constant once the state LUT's inputs have been for T), the losing client cannot be
acknowledged while the state stays settled. Not covered: the settling window, and that the server waits for it
(the server-path obligation).
-/

namespace Formal.Cells.AckLow

open Formal.Target Formal.Timing.SpecChain Formal.Cells.SpecFbChain

theorem grant_low {p : DelayPar} {c : ℚ} {g : Gate} {src : Nat → Nat} {arcs : Nat → List Arc} {S : Nat} {x : Beh}
    (hg : CGateOK p c g src arcs S x) {lo hi : Nat → Nat} (hb : CBands p c g.k arcs lo hi)
    {j qn : Nat} (hj : j < g.k) (hs : src j = qn) (b : Bool) (held ov : Nat → Bool)
    (hf : ∀ v : Nat → Bool, (∀ i, i < g.k → held i = true → v i = ov i) →
      g.init.testBit (addr g.k v) = true → v j = b)
    (hh : ∀ i, i < g.k → held i = true → ∀ t, x (src i) t = ov i)
    {a e : Nat} (hq : ∀ t, a ≤ t → t ≤ e → x qn t = !b) :
    ∀ t, S ≤ t → a + hi j ≤ t → t ≤ e + lo j → x g.out t = false := by
  obtain ⟨F, -, hF⟩ := hg
  intro t hS h1 h2
  obtain ⟨r, y⟩ := hF t hS
  have d := hb j hj _ (r j hj).2
  have e1 := (r j hj).1
  cases ho : x g.out t
  · rfl
  · have := hf _ (fun i hi hh' => hh i hi hh' _) (by rw [← y]; exact ho)
    rw [hs, hq _ (by omega) (by omega)] at this
    cases b <;> simp at this

theorem ack_low {p : DelayPar} {c : ℚ} {g : Gate} {src : Nat → Nat} {arcs : Nat → List Arc} {S : Nat} {x : Beh}
    (hg : CGateOK p c g src arcs S x) {lo hi : Nat → Nat} (hb : CBands p c g.k arcs lo hi)
    {gp fb : Nat} (hgp : gp < g.k) (hfbk : fb < g.k) (hfb : src fb = g.out) (hlo : 1 ≤ lo fb)
    (held ov : Nat → Bool)
    (hf : ∀ v : Nat → Bool, (∀ i, i < g.k → held i = true → v i = ov i) → v gp = false → v fb = false →
      g.init.testBit (addr g.k v) = false)
    (hh : ∀ i, i < g.k → held i = true → ∀ t, x (src i) t = ov i)
    {s e : Nat} (hS : S ≤ s) (hpre : ∀ t, s ≤ t + hi fb → t < s → x g.out t = false)
    (hgl : ∀ t, s ≤ t + hi gp → t + lo gp ≤ e → x (src gp) t = false) :
    ∀ t, s ≤ t → t ≤ e → x g.out t = false := by
  obtain ⟨F, -, hF⟩ := hg
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  intro hst hte
  obtain ⟨r, y⟩ := hF t (by omega)
  have dg := hb gp hgp _ (r gp hgp).2
  have df := hb fb hfbk _ (r fb hfbk).2
  have eg := (r gp hgp).1
  have ef := (r fb hfbk).1
  have hfr : x (src fb) (F fb t) = false := by
    rw [hfb]
    by_cases hc : s ≤ F fb t
    · exact ih _ (by omega) hc (by omega)
    · exact hpre _ (by omega) (by omega)
  rw [y]
  exact hf _ (fun i hi hh' => hh i hi hh' _) (hgl _ (by omega) (by omega)) hfr

end Formal.Cells.AckLow
