import Formal.Net.CapstoneLiveNdWalk

/-!
# Probe C-8z2 (6): gcd_hw liveness with `start`'s release bounded

8z's `gcd_hw_live_final` exempts `start`'s `bd_src` LUT from every delay bound once it has
offered (H_BOUNDED_DELAY' skips it, H_START_ENV only covers the time before the first offer).
That exemption is too wide: the LUT may then keep its request high for ever after the
acknowledge, the start token is never released, and the return-to-zero wave that out0's close
needs never starts. `CapstoneLiveWitCex` exhibits such a run: it meets the six other
hypotheses and out0 never closes, so 8z's open obligation H_NO_DEADLOCK' is FALSE on it (it
is not a consequence of the other hypotheses: it smuggles in an environment assumption).

Repair, here:
* **H_START_REL `H`** (`StartRel`, environment): while `start`'s request and acknowledge are
  both high on a whole window `[t, t + H]`, the request falls somewhere in it (the release half
  of the LUT's bounded delay; the second offer stays forbidden by H_START_ONCE).
* **H_NO_DEADLOCK''**: before out0's first close, the state is not quiescent, where quiescent
  now also requires that `start`'s LUT is not excited to release (`¬ (req ∧ ack)`). It is
  implied by 8z's H_NO_DEADLOCK' (weaker obligation), and is still OPEN in general.

`gcd_hw_live_final2`: same conclusion as `gcd_hw_live_final`, under H_CELLS, H_BUNDLE,
H_START_ONCE, H_BOUNDED_DELAY' `H`, H_START_ENV `H`, **H_START_REL `H`**,
H_ARB_UNCONTESTED_BOUNDED `H` and **H_NO_DEADLOCK''**. The proof is 8z's (ranking over the
projected state, `firing_bound` with 8z's offer certificate), with the stronger quiescence.
-/

namespace Formal.Net.CapNet.Live.Nd2
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapNet.Live Formal.Net.CapNet.Live.Nd
open Formal.Net.CapSafe (Good TS texec)

/-- H_START_REL `H`: `start`'s LUT releases its request within `H` of the acknowledge. -/
def StartRel (H : Nat) (c : Chan) : Prop :=
  ∀ t, Win H t (fun u => c.req u = true ∧ c.ack u = true) → Ev H t (fun u => c.req u = false)

/-- Quiescent, with `start`'s release excitation included. -/
def QuietR (x : GS × Bool) : Prop := QuietS x ∧ ¬ (x.1.rq start = true ∧ x.1.ak start = true)

/-- H_NO_DEADLOCK'' for a run. -/
def NoDeadlock2 (ch : Fin NC → Chan) (itr : Itr) : Prop :=
  ∀ t, cnt (fallB (ch out0).ack) t = 0 →
    ¬ (Quiet2 (gsAt ch itr t) ∧
       (cnt (riseB (ch start).req) t = 0 → (ch start).ack t = false → (ch start).req t = true) ∧
       ¬ ((ch start).req t = true ∧ (ch start).ack t = true))

/-- 8z's H_NO_DEADLOCK' implies H_NO_DEADLOCK''. -/
theorem nd2_of_nd' {ch : Fin NC → Chan} {itr : Itr}
    (h : ∀ t, cnt (fallB (ch out0).ack) t = 0 →
      ¬ (Quiet2 (gsAt ch itr t) ∧
         (cnt (riseB (ch start).req) t = 0 → (ch start).ack t = false → (ch start).req t = true))) :
    NoDeadlock2 ch itr :=
  fun t ht hq => h t ht ⟨hq.1, hq.2.1⟩

theorem frozen_quietR (H : Nat) (ch : Fin NC → Chan) (itr : Itr)
    (hB : ∀ p, p ≠ prodOf start → ∀ g ∈ gatesK p (opAt p), BndG H (gsAt ch itr) g)
    (hA : ∀ p x u z w, opAt p = .amerge x u z w → ArbSettle H (ch x) (ch u) (ch z) (itr p 0) (itr p 1))
    (hS : StartEnv H (ch start)) (hR : StartRel H (ch start))
    {t : Nat} (hfz : ∀ u, t ≤ u → u ≤ t + H → St ch itr u = St ch itr t) :
    QuietR (St ch itr t) := by
  refine ⟨frozen_quietS H ch itr hB hA hS hfz, ?_⟩
  intro hra
  have hrq : ∀ u, t ≤ u → u ≤ t + H → (ch start).req u = (ch start).req t := fun u h1 h2 => by
    have := congrArg (fun x : GS × Bool => x.1.rq start) (hfz u h1 h2)
    simpa [St, pj, gsAt] using this
  have hak : ∀ u, t ≤ u → u ≤ t + H → (ch start).ack u = (ch start).ack t := fun u h1 h2 => by
    have := congrArg (fun x : GS × Bool => x.1.ak start) (hfz u h1 h2)
    simpa [St, pj, gsAt] using this
  have h0 : (ch start).req t = true ∧ (ch start).ack t = true := by
    simpa [St, pj, gsAt] using hra
  obtain ⟨u, h1, h2, hu⟩ := hR t (fun u h1 h2 => ⟨by rw [hrq u h1 h2]; exact h0.1,
    by rw [hak u h1 h2]; exact h0.2⟩)
  rw [hrq u h1 h2, h0.1] at hu; cases hu

/-- **gcd_hw circuit liveness, with `start`'s release bounded.** -/
theorem gcd_hw_live_final2 (a b H : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31)
    (ch : Fin NC → Chan) (itr : Itr)
    (H_CELLS : ∀ p : Fin NO, CellI ch (srcV a b) itr p (opAt p))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, cnt (riseB (ch start).req) t ≤ 1)
    (H_BOUNDED_DELAY' : ∀ p, p ≠ prodOf start → ∀ g ∈ gatesK p (opAt p), BndG H (gsAt ch itr) g)
    (H_START_ENV : StartEnv H (ch start))
    (H_START_REL : StartRel H (ch start))
    (H_ARB_UNCONTESTED_BOUNDED : ∀ p x u z w, opAt p = .amerge x u z w →
      ArbUnc H (ch x) (ch u) (ch z) (itr p 0) (itr p 1))
    (H_NO_DEADLOCK'' : NoDeadlock2 ch itr) :
    ∃ y, Good a b y ∧ ∃ e, e < (1168 * (8 * Lrun y + 23) + 1) * (H + 1) ∧ TokAt (ch out0) 0 e ∧
      (ch out0).dat e = Nat.gcd a b := by
  obtain ⟨y, ls, hy, hex⟩ := good_run ha hb
  have hW := walk_ok hy hex
  have hE := walk_ends hy hex
  have hC : ∀ p : Fin NO, Cell ch (srcV a b) (opAt p) := fun p => cellI_cell _ (H_CELLS p)
  have hA : ∀ p x u z w, opAt p = .amerge x u z w →
      ArbSettle H (ch x) (ch u) (ch z) (itr p 0) (itr p 1) := by
    intro p x u z w hp
    have M' := H_CELLS p
    rw [hp] at M'
    exact gcd_hw_arb_settle a b H ch hC H_BUNDLE H_START_ONCE y hy hW p x u z w hp _ _ M'
      (H_ARB_UNCONTESTED_BOUNDED p x u z w hp)
  have hO := gcd_hw_offers_bounded a b (Lrun y) ch hC H_BUNDLE H_START_ONCE y hy hW hE
  have hm : 1168 * (2 * (4 * Lrun y + 11) + 1) = 1168 * (8 * Lrun y + 23) := by omega
  obtain ⟨t, ht, hP⟩ := rank_live (St ch itr) QuietR (fun t => cnt (fallB (ch out0).ack) t ≠ 0)
    (chS ch itr) H (1168 * (8 * Lrun y + 23)) (fun _ h => chS_false h)
    (fun _ hfz => frozen_quietR H ch itr H_BOUNDED_DELAY' hA H_START_ENV H_START_REL hfz)
    (fun t hp hq => by
      apply H_NO_DEADLOCK'' t (by omega)
      refine ⟨?_, ?_, ?_⟩
      · intro p hp' g hg v he
        have hI := gate_pj p g hg (gsAt ch itr t)
        rw [← hI.1]; exact hq.1.1 p hp' g hg v ((hI.2 v).mpr he)
      · intro h0 hak
        have := hq.1.2 (by simp [St, h0]) (by simp [St, pj, gsAt, hak])
        simpa [St, pj, gsAt] using this
      · intro hra
        exact hq.2 (by simpa [St, pj, gsAt] using hra))
    (fun T hT => by
      rw [← hm]
      exact firing_bound a b (4 * Lrun y + 11) ch itr H_CELLS H_BUNDLE (fun c T _ => hO c T) T
        (by have := hT T (Nat.le_refl _); omega))
  obtain ⟨e, he, hf, hc0⟩ := first_ev (fallB (ch out0).ack) t (by omega)
  have hsafe := (gcd_hw_circuit_safe'' a b ch hC H_BUNDLE H_START_ONCE ⟨y, hy, hW⟩).1
  exact ⟨y, hy, e, by omega, ⟨hf, hc0⟩, hsafe 0 e ⟨hf, hc0⟩⟩

end Formal.Net.CapNet.Live.Nd2
