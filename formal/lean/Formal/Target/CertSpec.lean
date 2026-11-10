import Formal.Net.AO.Timed
import Formal.Net.AO.EnvHS
import Formal.Net.AO.EnvData
import Formal.Target.Spec

/-!
# Formal.Target.CertSpec — from an occurrence certificate to Spec's four-phase clauses (shard A, 2026-11-10)

**Problem, plainly.** Shard C's timed certificate theorems (`AO.timedA_follows`, `timedA_live`) conclude, for every
admissible behaviour, facts about *event counts*: at every time the counts of all nodes form an ideal of the
certificate's order, and every change of a node is enabled at the counts its gate read. THE statement's conclusion
(`Spec.Correct`, and `Assembly.StepCore` per episode) is about *values*: an acknowledge moves only while it differs
from its request (`AckMoves`), a circuit-driven request moves only while it equals its acknowledge (`ReqMoves`).
Do the count facts give the value facts?

**Proved** (generic in the certificate, nodes `Nat`, Spec's behaviours):
* `ackMoves_of_cert`: if the certificate makes acknowledge event `k` need request event `k` and request event
  `k + 1` need acknowledge event `k`, both nodes start low at `t0`, the counts are an ideal at every time, and every
  change of the acknowledge is enabled at counts no later than the previous instant, then `AckMoves` holds from `t0`.
* `reqMoves_of_cert`: the same order, for a request the circuit drives (e.g. `out0.req` against the environment's
  `out0.ack`): `ReqMoves` from `t0`.
* `enabled_of_changeOKA`: C's per-change conclusion `ChangeOKA` at a gate, with the read bounds of `TBehX`
  (`rd`, `lo1`), gives the "enabled at earlier counts" premise above.

**Not shown.** The other `StepCore` fields (one out0 handshake, the data, the end state) and the instance for THE
target (its certificate's cause lists for the boundary events).
-/

namespace Formal.Target.CertSpec
open Formal.Target Formal.Net.AO Formal.Net.OccNet.Timed

theorem parity_ne (c : Nat) : (c % 2 == 1) ≠ ((c + 1) % 2 == 1) := by
  rcases Nat.mod_two_eq_zero_or_one c with h | h
  · have : (c + 1) % 2 = 1 := by omega
    simp [h, this]
  · have : (c + 1) % 2 = 0 := by omega
    simp [h, this]

/-- **Acknowledge side.** -/
theorem ackMoves_of_cert (C : Cert Nat) (x : Beh) (t0 r a : Nat) (h0r : x r t0 = false) (h0a : x a t0 = false)
    (hI : ∀ s, Ideal C (fun u => cnt x t0 u s))
    (hAk : ∀ k, k < C.len a → ∀ alt ∈ C.causes a k, (r, k) ∈ alt)
    (hRq : ∀ k, k + 1 < C.len r → ∀ alt ∈ C.causes r (k + 1), (a, k) ∈ alt)
    (hen : ∀ s, t0 < s → x a s ≠ x a (s - 1) → ∃ n : Nat → Nat, (∀ w, n w ≤ cnt x t0 w (s - 1)) ∧
      n a = cnt x t0 a (s - 1) ∧ Enabled C n a) :
    AckMoves (x r) (x a) t0 := by
  intro t ht hne
  obtain ⟨n, hle, hna, hlen, alt, halt, hin⟩ := hen (t + 1) (by omega) (by simpa using hne)
  simp only [Nat.add_sub_cancel] at hle hna
  have hra := hin _ (hAk _ hlen alt halt)
  have h1 := hle r
  have hc := Formal.Net.AO.EnvHS.hs_counts C _ (hI t) r a hAk hRq
  have heq : cnt x t0 r t = cnt x t0 a t + 1 := by simp only at hc hra; omega
  rw [Formal.Net.AO.EnvData.x_par x t0 a h0a t ht, Formal.Net.AO.EnvData.x_par x t0 r h0r t ht, heq]
  exact parity_ne _

/-- **Request side** (a request the circuit drives, against the environment's acknowledge). -/
theorem reqMoves_of_cert (C : Cert Nat) (x : Beh) (t0 r a : Nat) (h0r : x r t0 = false) (h0a : x a t0 = false)
    (hI : ∀ s, Ideal C (fun u => cnt x t0 u s))
    (hAk : ∀ k, k < C.len a → ∀ alt ∈ C.causes a k, (r, k) ∈ alt)
    (hRq : ∀ k, k + 1 < C.len r → ∀ alt ∈ C.causes r (k + 1), (a, k) ∈ alt)
    (hen : ∀ s, t0 < s → x r s ≠ x r (s - 1) → ∃ n : Nat → Nat, (∀ w, n w ≤ cnt x t0 w (s - 1)) ∧
      n r = cnt x t0 r (s - 1) ∧ Enabled C n r) :
    ReqMoves (x r) (x a) t0 := by
  intro t ht hne
  obtain ⟨n, hle, hnr, hlen, alt, halt, hin⟩ := hen (t + 1) (by omega) (by simpa using hne)
  simp only [Nat.add_sub_cancel] at hle hnr
  have hc := Formal.Net.AO.EnvHS.hs_counts C _ (hI t) r a hAk hRq
  have heq : cnt x t0 r t = cnt x t0 a t := by
    rcases Nat.eq_zero_or_pos (n r) with h0 | hpos
    · omega
    · obtain ⟨k, hk⟩ : ∃ k, n r = k + 1 := ⟨n r - 1, by omega⟩
      rw [hk] at hlen halt
      have hak := hin _ (hRq k hlen alt halt)
      have := hle a
      simp only at hak
      omega
  rw [Formal.Net.AO.EnvData.x_par x t0 a h0a t ht, Formal.Net.AO.EnvData.x_par x t0 r h0r t ht, heq]

/-- **From C's per-change conclusion**: a gate's change at `s` is enabled at its read counts, which are no later than
`s - 1` (every pin delay at least 1 ps, `TBehX.lo1`), and its own count is the current one. -/
theorem enabled_of_changeOKA {N : TNet Nat} {CP : Cert Nat} {x : Beh} {t0 : Nat} {r : Nat → Nat → Nat → Nat}
    {v s : Nat}
    (hrd : ∀ w, w ∈ N.pins v → N.lo v w ≤ s - r v w s ∧ r v w s ≤ s)
    (hlo1 : ∀ w, w ∈ N.pins v → 1 ≤ N.lo v w)
    (hch : ChangeOKA N CP x t0 r v s) :
    ∃ n : Nat → Nat, (∀ w, n w ≤ cnt x t0 w (s - 1)) ∧ n v = cnt x t0 v (s - 1) ∧ Enabled CP n v := by
  obtain ⟨hself, hen⟩ := hch
  refine ⟨nT N x t0 r v s, fun w => ?_, ?_, hen⟩
  · unfold nT ρ
    split
    · rename_i hrw
      simp only [reads, Bool.and_eq_true, decide_eq_true_eq] at hrw
      obtain ⟨h1, h2⟩ := hrd w hrw.2
      have := hlo1 w hrw.2
      exact cnt_mono w _ _ (by omega)
    · exact le_refl _
  · unfold nT ρ
    split
    · rename_i hrv; exact hself hrv
    · rfl

/-! ## Transitive forms: the order facts may hold through other events -/

/-- **Acknowledge side, transitive form.** `hInter`: the two counts interleave at every time; `hAkT`: in every ideal
containing a cause alternative of acknowledge event `k`, request event `k` has happened. -/
theorem ackMoves_of_certT (C : Cert Nat) (x : Beh) (t0 r a : Nat) (h0r : x r t0 = false) (h0a : x a t0 = false)
    (hI : ∀ s, Ideal C (fun u => cnt x t0 u s))
    (hInter : ∀ s, cnt x t0 a s ≤ cnt x t0 r s ∧ cnt x t0 r s ≤ cnt x t0 a s + 1)
    (hAkT : ∀ k, ∀ alt ∈ C.causes a k, ∀ c : Nat → Nat, Ideal C c → AltIn c alt → k < c r)
    (hen : ∀ s, t0 < s → x a s ≠ x a (s - 1) → ∃ n : Nat → Nat, (∀ w, n w ≤ cnt x t0 w (s - 1)) ∧
      n a = cnt x t0 a (s - 1) ∧ Enabled C n a) :
    AckMoves (x r) (x a) t0 := by
  intro t ht hne
  obtain ⟨n, hle, hna, -, alt, halt, hin⟩ := hen (t + 1) (by omega) (by simpa using hne)
  simp only [Nat.add_sub_cancel] at hle hna
  have hra := hAkT _ alt halt _ (hI t) (altIn_mono hle hin)
  have hc := hInter t
  have heq : cnt x t0 r t = cnt x t0 a t + 1 := by omega
  rw [Formal.Net.AO.EnvData.x_par x t0 a h0a t ht, Formal.Net.AO.EnvData.x_par x t0 r h0r t ht, heq]
  exact parity_ne _

/-- **Request side, transitive form.** `hRqT`: in every ideal containing a cause alternative of request event
`k + 1`, acknowledge event `k` has happened. -/
theorem reqMoves_of_certT (C : Cert Nat) (x : Beh) (t0 r a : Nat) (h0r : x r t0 = false) (h0a : x a t0 = false)
    (hI : ∀ s, Ideal C (fun u => cnt x t0 u s))
    (hInter : ∀ s, cnt x t0 a s ≤ cnt x t0 r s ∧ cnt x t0 r s ≤ cnt x t0 a s + 1)
    (hRqT : ∀ k, ∀ alt ∈ C.causes r (k + 1), ∀ c : Nat → Nat, Ideal C c → AltIn c alt → k < c a)
    (hen : ∀ s, t0 < s → x r s ≠ x r (s - 1) → ∃ n : Nat → Nat, (∀ w, n w ≤ cnt x t0 w (s - 1)) ∧
      n r = cnt x t0 r (s - 1) ∧ Enabled C n r) :
    ReqMoves (x r) (x a) t0 := by
  intro t ht hne
  obtain ⟨n, hle, hnr, -, alt, halt, hin⟩ := hen (t + 1) (by omega) (by simpa using hne)
  simp only [Nat.add_sub_cancel] at hle hnr
  have hc := hInter t
  have heq : cnt x t0 r t = cnt x t0 a t := by
    rcases Nat.eq_zero_or_pos (n r) with h0 | hpos
    · omega
    · obtain ⟨k, hk⟩ : ∃ k, n r = k + 1 := ⟨n r - 1, by omega⟩
      rw [hk] at halt
      have hak := hRqT k alt halt _ (hI t) (altIn_mono hle hin)
      omega
  rw [Formal.Net.AO.EnvData.x_par x t0 a h0a t ht, Formal.Net.AO.EnvData.x_par x t0 r h0r t ht, heq]

end Formal.Target.CertSpec
