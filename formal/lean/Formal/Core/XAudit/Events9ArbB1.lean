import Formal.Core.XAudit.Events9ArbNetEdge

/-!
# Formal.Core.XAudit.Events9ArbB1 — what a failing B1 row does and does not mean

Shard A, lead, 2026-10-31. Notes: `formal/notes/A-e9arbnet.md` (2026-10-31 section).

On the rebuilt gcd_hw routes the B1 row `hi Dr + 2 ≤ lo DrQ + lo Dq` of `ArbRowsOK` fails on 2-6
of 9 arbiters at slow/fast (xarbnet). B1 is what `b1_of` needs to show that the real grant
`y t = s (wr t) && e (wq t)` (an AND of its request read and its state-literal read) behaves as
the corrected core's grant, a C-element: with the request read high and the state literal lost,
the output must already have been low.

**Problem statement.** Without the B1 row, using only (i) the flip property of ustate O6 (a flip
of the literal away from the branch at `τ` happens only with ustate reading the request LOW at
`fQ τ`; proved from the real INIT in `flipAway1`/`flipAway2` under QClean) and (ii) no re-request
during the switch (`NoReReq` of `ArbEdge`), does the real grant still keep the four-phase order
"the grant falls only after its request has fallen"?

**Proved** (`grant_fall_after_req_fall`): at every fall of the grant (`y (t-1) = true`,
`y t = false`) at a time `t > lo Dr + lo Q + lo Dq`, there is a time `u` with `wr (t-1) < u` (after the grant's last high read of the
request), `s u = false` (the request is low), and `u + min lo Dr (lo Q + lo Dq) ≤ t`. So the
request has fallen, after the read that kept the grant high, at least `min(lo Dr, lo Q + lo Dq)`
before the grant falls, whether the fall came through the request pin or through the q pin.
The B1 row is not used. So a failing B1 row does not by itself break req↓ → grant↓; what it
breaks is the match with the C-element grant of the corrected core (`and_cel`'s hold clause).

NOT covered: exclusion, the rise side, what downstream readers of the grant need, and the
hypotheses themselves (QClean, NoReReq).
-/

namespace Formal.Core.XAudit.Events9ArbNet

open Formal.Core
open Formal.Core.TraceDiscrete (Sig Warp Mono)

theorem grant_fall_after_req_fall {s e y : Sig} {wr wq fQ : Nat → Nat}
    {loDr hiDr loDq hiDq loQ hiQ : Nat}
    (hy : ∀ t, y t = (s (wr t) && e (wq t)))
    (hwr : Warp loDr hiDr wr) (hwq : Warp loDq hiDq wq) (hfQ : Warp loQ hiQ fQ)
    (hflip : ∀ τ, 1 ≤ τ → e (τ - 1) = true → e τ = false → s (fQ τ) = false)
    (hnore : ∀ τ, 1 ≤ τ → e (τ - 1) = true → e τ = false →
      ∀ v, fQ τ ≤ v → v + loDr < τ + hiDq + 2 → s v = false) :
    ∀ t, loDr + loQ + loDq + 1 ≤ t → y (t - 1) = true → y t = false →
      ∃ u, wr (t - 1) < u ∧ s u = false ∧ u + min loDr (loQ + loDq) ≤ t := by
  intro t ht h1 h0
  rw [hy] at h1 h0
  have hs1 : s (wr (t - 1)) = true := by cases h : s (wr (t - 1)) <;> simp_all
  have he1 : e (wq (t - 1)) = true := by cases h : e (wq (t - 1)) <;> simp_all
  have a1 := hwr.le_late t
  cases hst : s (wr t)
  · -- the fall came through the request pin
    refine ⟨wr t, ?_, hst, by omega⟩
    have hm := hwr.mono (t - 1) t (by omega)
    rcases Nat.lt_or_eq_of_le hm with h | h
    · exact h
    · rw [h, hst] at hs1; exact absurd hs1 (by decide)
  · -- the fall came through the state literal
    have he0 : e (wq t) = false := by rw [hst] at h0; simpa using h0
    obtain ⟨τ, h2, h3, h4, h5⟩ := first_fall e he1 he0 (hwq.mono (t - 1) t (by omega))
    have hτ : 1 ≤ τ := by omega
    have hfl := hflip τ hτ h4 h5
    have b1 := hfQ.le_late τ
    have b2 := hwq.le_late t
    have b3 := hwq.early_le (t - 1)
    have b4 := hwr.le_late (t - 1)
    refine ⟨fQ τ, ?_, hfl, by omega⟩
    -- if ustate's low read came at or before the grant's high read, that is a re-request
    rcases Nat.lt_or_ge (wr (t - 1)) (fQ τ) with h | h
    · exact h
    · exfalso
      have := hnore τ hτ h4 h5 (wr (t - 1)) h (by omega)
      rw [hs1] at this; exact absurd this (by decide)

end Formal.Core.XAudit.Events9ArbNet
