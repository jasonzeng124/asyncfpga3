import Formal.Net.AO.Occ
import Formal.Net.TimedOcc

/-!
# Environment moves of a four-phase handshake, by counts (shard C, S4: the env half of the bridge)

**Problem, plainly.** `AO.timedA_follows` asks (`hEnvE`) that every change of an environment node be an enabled event
of the certificate at the counts just before it. `Spec.EnvIn` only says how a request moves in STATE terms
(`ReqMoves`: it changes only while it equals its acknowledge). Does the state rule give the count rule? It does, once
the counts are an ideal of an order in which acknowledge `k` needs request `k` and request `k+1` needs acknowledge `k`:
then the two counts differ by at most one, so equal values mean equal counts, so the request's next event finds the
acknowledge event it needs.

**Proved:**
* `hs_counts`: in such an ideal, `c ak ≤ c rq ≤ c ak + 1`;
* `hs_balanced`: if the request changes at `s` (both started low, `ReqMoves` from `t0`), the counts at `s - 1` are
  equal;
* `req_enabled`: hence the request's change is enabled in any certificate whose request event `n` has an
  alternative `(ak, n-1) :: E` (or `E` for `n = 0`) with `E` already in the ideal.

**Not shown here:** the `E` part for THE target (the `SeqEnv` conditions on `out0`), the request count bound from
`Offered`, the output side (`AckMoves`, `Δo`), data setup `su`.
-/

namespace Formal.Net.AO.EnvHS
open Formal.Net.OccNet (st)
open Formal.Net.AO Formal.Net.OccNet.Timed

variable {α : Type}

/-- **Counts within one.** -/
theorem hs_counts (C : Cert α) (c : α → Nat) (hI : Ideal C c) (rq ak : α)
    (hAk : ∀ k, k < C.len ak → ∀ alt ∈ C.causes ak k, (rq, k) ∈ alt)
    (hRq : ∀ k, k + 1 < C.len rq → ∀ alt ∈ C.causes rq (k + 1), (ak, k) ∈ alt) :
    c ak ≤ c rq ∧ c rq ≤ c ak + 1 := by
  constructor
  · rcases Nat.eq_zero_or_pos (c ak) with h | h
    · omega
    · obtain ⟨hle, hall⟩ := hI ak
      obtain ⟨alt, ha, hin⟩ := hall (c ak - 1) (by omega)
      have := hin _ (hAk _ (by omega) alt ha)
      simp only at this; omega
  · rcases Nat.lt_or_ge (c rq) 2 with h | h
    · omega
    · obtain ⟨hle, hall⟩ := hI rq
      obtain ⟨alt, ha, hin⟩ := hall (c rq - 1) (by omega)
      have h' : c rq - 1 = (c rq - 2) + 1 := by omega
      rw [h'] at ha
      have := hin _ (hRq _ (by omega) alt ha)
      simp only at this; omega

theorem par_eq {a b : Nat} (h1 : a ≤ b) (h2 : b ≤ a + 1) (hp : (a % 2 == 1) = (b % 2 == 1)) : a = b := by
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;> rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
    simp [ha, hb] at hp <;> omega

/-- **Equal values mean equal counts.** -/
theorem hs_balanced [DecidableEq α] (C : Cert α) (x : α → Nat → Bool) (t0 H : Nat) (rq ak : α)
    (hq : ∀ u, ∀ s, t0 ≤ s + H → s ≤ t0 → x u s = x u t0)
    (h0r : x rq t0 = false) (h0a : x ak t0 = false)
    (hmv : ∀ t, t0 ≤ t → x rq (t + 1) ≠ x rq t → x rq t = x ak t)
    (c : α → Nat) (hI : Ideal C c)
    (hAk : ∀ k, k < C.len ak → ∀ alt ∈ C.causes ak k, (rq, k) ∈ alt)
    (hRq : ∀ k, k + 1 < C.len rq → ∀ alt ∈ C.causes rq (k + 1), (ak, k) ∈ alt)
    (s : Nat) (hs : t0 < s) (hc1 : c rq = cnt x t0 rq (s - 1)) (hc2 : c ak = cnt x t0 ak (s - 1))
    (hch : x rq s ≠ x rq (s - 1)) :
    cnt x t0 ak (s - 1) = cnt x t0 rq (s - 1) := by
  have hss : s - 1 + 1 = s := by omega
  have he := hmv (s - 1) (by omega) (by rw [hss]; exact hch)
  rw [x_eq_st rq H (hq rq) (s - 1) (by omega), x_eq_st ak H (hq ak) (s - 1) (by omega)] at he
  simp only [st, h0r, h0a, Bool.false_xor] at he
  obtain ⟨h1, h2⟩ := hs_counts C c hI rq ak hAk hRq
  rw [hc1, hc2] at h1 h2
  exact par_eq h1 h2 he.symm

/-- **The request's change is enabled.** -/
theorem req_enabled [DecidableEq α] (CP C : Cert α) (x : α → Nat → Bool) (t0 H : Nat) (rq ak : α)
    (hq : ∀ u, ∀ s, t0 ≤ s + H → s ≤ t0 → x u s = x u t0)
    (h0r : x rq t0 = false) (h0a : x ak t0 = false)
    (hmv : ∀ t, t0 ≤ t → x rq (t + 1) ≠ x rq t → x rq t = x ak t)
    (c : α → Nat) (hI : Ideal C c)
    (hAk : ∀ k, k < C.len ak → ∀ alt ∈ C.causes ak k, (rq, k) ∈ alt)
    (hRq : ∀ k, k + 1 < C.len rq → ∀ alt ∈ C.causes rq (k + 1), (ak, k) ∈ alt)
    (s : Nat) (hs : t0 < s) (hch : x rq s ≠ x rq (s - 1))
    (hc : ∀ u, c u = cnt x t0 u (s - 1))
    (hlen : cnt x t0 rq (s - 1) < CP.len rq)
    (E : List (α × Nat))
    (halt : (if cnt x t0 rq (s - 1) = 0 then E else (ak, cnt x t0 rq (s - 1) - 1) :: E) ∈
      CP.causes rq (cnt x t0 rq (s - 1)))
    (hE : AltIn (fun w => cnt x t0 w (s - 1)) E) :
    Enabled CP (fun w => cnt x t0 w (s - 1)) rq := by
  have hb := hs_balanced C x t0 H rq ak hq h0r h0a hmv c hI hAk hRq s hs (hc rq) (hc ak) hch
  refine ⟨hlen, _, halt, ?_⟩
  split
  · exact hE
  · rename_i hn
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · simp only; omega
    · exact hE p hp

end Formal.Net.AO.EnvHS
