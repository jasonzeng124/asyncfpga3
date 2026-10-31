import Formal.Net.CapstoneRefineNet
import Formal.Net.OpsBusy2

/-!
# Probe C-8x3: a tcheck certificate gives `Held` step by step (receiver rule only up to `t`)

C-8x's `held_of_bcert` needs the receiver rule at ALL times. Its proof only looks backwards:
`Held` at step `t` uses `RecvStep` at the steps `≤ t` (`busy_cover` walks back to the offer,
`idle_until` walks forward from the launch to the offer). Bounded copies:

* `idle_untilT`, `busy_coverT`, `heldStep_of_txwin`;
* **`heldStep_of_bcert`**: `BCert P`, reset, `RecvStep P s` for `s ≤ t` ⇒ `HeldStep P t`.
-/

namespace Formal.Net.CapstoneRefine
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Timing Formal.Net.OpsBusy2

theorem idle_untilT {P : Chan} {sig : Nat → Nat → Trace} {data : List Nat} {R : Nat → Nat → Prop}
    (X : TxWin P sig data R) {T : Nat} (hrecv : ∀ s, s < T → RecvStep P s) {k r : Nat}
    (ho : OffAt P k r) (hrT : r ≤ T) :
    ∀ n, X.τ k + n ≤ r → P.req (X.τ k + n) = false ∧ P.ack (X.τ k + n) = false := by
  intro n
  induction n with
  | zero => intro _; exact X.idle k ⟨r, ho⟩
  | succ n ih =>
    intro hn
    obtain ⟨hr, ha⟩ := ih (by omega)
    have hreq : P.req (X.τ k + n + 1) = false := by
      cases hq : P.req (X.τ k + n + 1) with
      | false => rfl
      | true =>
        exfalso
        have hrise : riseB P.req (X.τ k + n) = true := by simp [riseB, hr, hq]
        have := cnt_mono (riseB P.req) (show X.τ k + n + 1 ≤ r by omega)
        rw [cnt_succ_of hrise, ho.2] at this
        have := cnt_mono (riseB P.req) (show X.τ k ≤ X.τ k + n by omega)
        rw [X.count k ⟨r, ho⟩] at this; omega
    refine ⟨hreq, ?_⟩
    cases hq : P.ack (X.τ k + n + 1) with
    | false => rfl
    | true =>
      exfalso
      have := hrecv (X.τ k + n) (by omega) (by rw [hq, ha]; decide)
      rw [ha, hr] at this; exact this rfl

theorem busy_coverT {P : Chan} (hinit : Init P) {T : Nat} (hrecv : ∀ s, s < T → RecvStep P s) :
    ∀ t, t ≤ T → inTx P t = true →
      ∃ k r, OffAt P k r ∧ r < t ∧ ∀ s, r < s → s ≤ t → inTx P s = true := by
  intro t
  induction t with
  | zero => intro _ h; simp [inTx, hinit.1, hinit.2] at h
  | succ t ih =>
    intro hT h
    by_cases hb : inTx P t = true
    · obtain ⟨k, r, ho, hr, hs⟩ := ih (by omega) hb
      refine ⟨k, r, ho, by omega, fun s h1 h2 => ?_⟩
      rcases Nat.lt_or_eq_of_le h2 with h2 | h2
      · exact hs s h1 (by omega)
      · rw [h2]; exact h
    · have hr0 : P.req t = false := by simp [inTx] at hb; exact hb.1
      have ha0 : P.ack t = false := by simp [inTx] at hb; exact hb.2
      have ha1 : P.ack (t + 1) = false := by
        cases hq : P.ack (t + 1) with
        | false => rfl
        | true =>
          exfalso
          have := hrecv t (by omega) (by rw [hq, ha0]; decide)
          rw [ha0, hr0] at this; exact this rfl
      have hr1 : P.req (t + 1) = true := by simpa [inTx, ha1] using h
      refine ⟨cnt (riseB P.req) t, t, ⟨by simp [riseB, hr0, hr1], rfl⟩, by omega, fun s h1 h2 => ?_⟩
      rw [show s = t + 1 by omega]; exact h

theorem heldStep_of_txwin {net : Netlist} (hwf : net.WF) {P : Chan} {sig : Nat → Nat → Trace}
    {data : List Nat} {R : Nat → Nat → Prop} (runs : ∀ k, Run net (sig k))
    (X : TxWin P sig data R)
    (hsep : ∀ k v, R k v → ∀ d ∈ data, ∀ s, changes (sig k d) s → s ≤ v)
    (hinit : Init P) {t : Nat} (hrecv : ∀ s, s ≤ t → RecvStep P s) : HeldStep P t := by
  intro h0 h1
  have hrecv' : ∀ s, s < t + 1 → RecvStep P s := fun s hs => hrecv s (by omega)
  obtain ⟨k, r, ho, hr, hs⟩ := busy_coverT hinit hrecv' (t + 1) (Nat.le_refl _) h1
  rcases Nat.lt_or_eq_of_le (show r ≤ t by omega) with hlt | heq
  · rw [sampled_eq_zd hwf runs X hsep ho (by omega) hs,
      sampled_eq_zd hwf runs X hsep ho hlt (fun s a b => hs s a (by omega))]
  · exfalso
    subst heq
    obtain ⟨h1', _⟩ := off_in_win X ho
    obtain ⟨hr0, ha0⟩ := idle_untilT X hrecv' ho (by omega) (r - X.τ k) (by omega)
    rw [show X.τ k + (r - X.τ k) = r by omega] at hr0 ha0
    simp [inTx, hr0, ha0] at h0

/-- **A certificate gives `Held` at step `t` from the receiver rule up to `t`.** -/
theorem heldStep_of_bcert {P : Chan} (B : BCert P) (hinit : Init P) {t : Nat}
    (hrecv : ∀ s, s ≤ t → RecvStep P s) : HeldStep P t := by
  cases B with
  | dag net req data setup sig hwf hc runs X =>
    exact heldStep_of_txwin hwf runs X (sep_dag hwf hc runs) hinit hrecv
  | cert dag late pot data targets setup sigD sigL hwf hpot hnz hwin rD rL X =>
    exact heldStep_of_txwin hwf rD X (sep_cert hwf hpot hnz hwin rD rL) hinit hrecv
  | exempt h => exact h t

end Formal.Net.CapstoneRefine
