import Formal.Net.AO.UnrollRest

/-!
# Glue: the local-check hypothesis of `timedA_follows_unroll` from window checks (shard C, 2026-11-10)

**Problem.** `UnrollRest.timedA_follows_unroll` / `timedA_live_unroll` keep the local check `hloc` as a hypothesis,
stated on the long certificate `LC BIG (wP ks)` with claims `uclT`. `UnrollAsm.lcheckXA_unroll` proves the local
check of an unrolled certificate (with claims `ucl`) from the r-window checks. Do they fit?

**Proved** (`hloc_unroll`): yes: the long local check at a reader `v`, in exactly the form `hloc` takes, follows
from `lcheckXA_unroll`'s hypotheses for the word `wk (wP ks)` (`LC` is `unroll` of the same windows, definitionally;
`lcheckXA_uclT` swaps `ucl` for `uclT`).

**Not shown:** that the window checks pass for any instance.
-/

namespace Formal.Net.AO
open Formal.Net.OccNet (st)
open Formal.Net.OccNet.Timed Formal.Net.OccNet.TimedX

variable {α : Type} [DecidableEq α]

theorem hloc_unroll {N : TNet α} {dat : α → Bool} {envEn : α → (α → Bool) → Bool} {s0 : α → Bool}
    {D : α → List α} {v : α} (hv : v ∈ D v)
    (hT : ∀ s s' : α → Bool, (∀ u ∈ D v, s u = s' u) → (∀ u, dat u = true → s u = s' u) →
      tEn N envEn v s = tEn N envEn v s')
    (BIG : Nat) (ks : List (WKindF α)) (tm' : α → Nat → Nat) (r : Nat) (hr : 2 ≤ r)
    (hcD : ∀ w ∈ wk (wP ks), ∀ k, ∀ alt ∈ w.causes v k, ∀ q ∈ alt, q.1 ∈ D v)
    (hen : ∀ z, dat z = true → z ∈ N.pins v →
      ∀ k ∈ wk (wP ks), ∀ g ∈ k.gd v z, ∃ w, g.en = some w ∧ w.1 ∈ D v ∧ w.2 < k.len w.1)
    (hst : ∀ z, dat z = true → z ∈ N.pins v → ∀ k ∈ wk (wP ks), ∀ g ∈ k.gd v z, ∃ w, g.st = some w ∧ w.1 ∈ D v)
    (hci : ∀ z, dat z = true → z ∈ N.pins v → ∀ k ∈ wk (wP ks), ∀ g ∈ k.gd v z, g.ci < k.cl.length)
    (hP : PairChain (D v) (wk (wP ks)))
    (hWv : ∀ j, j ≤ (wk (wP ks)).length → off (wcs (wk (wP ks))) (j + 2) v < tot (wcs (wk (wP ks))) v →
      off (wcs (wk (wP ks))) (j + 2) v < off (wcs (wk (wP ks))) (j + r) v)
    (hW : ∀ j, j ≤ (wk (wP ks)).length →
      LCheckXA N dat envEn (st s0 (off (wcs (wk (wP ks))) j)) (win (wcs (wk (wP ks))) j r tm')
        (uL (((wk (wP ks)).drop j).take r) (fun _ => 0)) D
        (ucl (((wk (wP ks)).drop j).take r)) (fun v z => ugd v z (((wk (wP ks)).drop j).take r) (fun _ => 0) 0) v) :
    v ∈ D v ∧ LCheckXA N dat envEn s0 (LC BIG (wP ks)) (uL (wk (wP ks)) (fun _ => 0)) D
        (uclT (wk (wP ks)) (fun _ => 0)) (fun v z => ugd v z (wk (wP ks)) (fun _ => 0) 0) v := by
  refine ⟨hv, ?_⟩
  have h := lcheckXA_unroll hv hT (wk (wP ks)) (utm BIG (wP ks)) tm' r hr hcD hen hst hci hP hWv hW
  exact (lcheckXA_uclT (wk (wP ks)) (fun _ => 0)).mpr h

end Formal.Net.AO
