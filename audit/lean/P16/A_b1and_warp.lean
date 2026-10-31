import Formal.Core.XAudit.Events9ArbB1
/-! Auditor P16 (shard A, 3f9444c3): b1_and's only warp-dependent signal hypothesis, `hnore`, follows
for EVERY warp `fQ` in its band from a warp-free window condition on the request (no re-request on
`[τ - hiQ, τ + hiDq + 2 - loDr)` after a flip away at τ). So, unlike ArbOrd (P15a), b1_and has no
hypothesis that is a pure inequality on the chosen warps. Also: #check of the statement as built. -/
open Formal.Core Formal.Core.TraceDiscrete Formal.Core.XAudit.Events9ArbNet

theorem hnore_of_window {s e : Sig} {fQ : Nat → Nat} {loQ hiQ loDr hiDq : Nat}
    (hfQ : Warp loQ hiQ fQ)
    (hw : ∀ τ, 1 ≤ τ → e (τ - 1) = true → e τ = false →
      ∀ v, τ - hiQ ≤ v → v + loDr < τ + hiDq + 2 → s v = false) :
    ∀ τ, 1 ≤ τ → e (τ - 1) = true → e τ = false →
      ∀ v, fQ τ ≤ v → v + loDr < τ + hiDq + 2 → s v = false := by
  intro τ h1 h2 h3 v hv hv2
  have := hfQ.early_le τ
  exact hw τ h1 h2 h3 v (by omega) hv2

#check @b1_and
#print axioms b1_and
#print axioms hnore_of_window
