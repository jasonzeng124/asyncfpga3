import Formal.Net.AO.UnrollRest
import Formal.Net.AO.TimedUp

/-!
# Every word, with upper-bound claim joins and external claims (shard C, 2026-11-10)

**Problem.** `UnrollRest.timedA_follows_unroll` (safety for the certificate of every word of kinds) uses
`timedA_follows`: claims joined only by separations, and every gate claim proved inside the certificate. The c = 0
data layer needs upper-bound joins (`TimedOccUp.ChainUOK`), and the datapath condition claims cannot be proved per
kind (piece 3, notes/C-allpairs.md).

**Proved** (`timedA_follows_unrollUX`): the same theorem on `AO/TimedUp.timedA_followsUX`: claims satisfying `ext`
are hypotheses (`hExt`, environment-claim shape), the others are proved by GateProof or a `ChainUOK` chain with the
long tables `LSep`, `LUp`.

Also `timedA_live_unrollUX` (liveness, same change).

**Not shown:** discharging `hExt` (the sub-word form of `ChainUOK` is in `UnrollClaimU`).
-/

namespace Formal.Net.AO
open Formal.Net.OccNet (st)
open Formal.Net.OccNet.Timed Formal.Net.OccNet.TimedX Formal.Net.OccNet.TimedR Formal.Net.OccNet.TimedU

variable {α : Type} [DecidableEq α]

section main
variable {N : TNet α} {dat : α → Bool} {envEn : α → (α → Bool) → Bool} {x : α → Nat → Bool}
  {r : α → α → Nat → Nat} {t0 H : Nat} {D : α → List α}

/-- **Safety for the certificate of every word**, with upper-bound joins and external claims. -/
theorem timedA_follows_unrollUX (ext : Claim α → Prop) [DecidablePred ext] (BIG r' : Nat) (hr : 2 ≤ r') (ks : List (WKindF α)) (Dc : α → List α)
    (hKP : ∀ w ∈ ks, KindTm BIG w.toWKindT) (hKF : ∀ w ∈ ks, KindTm BIG w.full)
    (hcD : ∀ w ∈ wP ks, ∀ u k, ∀ alt ∈ w.causes u k, ∀ q ∈ alt, q.1 ∈ Dc u) (hBC : BackChain (wP ks))
    (hS : ∀ i, i < (wP ks).length → SepWin N BIG (((wP ks).drop (i - 1)).take r') (i - (i - 1)))
    (hU : ∀ i, i < (wP ks).length → UpWin N dat BIG (((wP ks).drop (i - 1)).take r') (i - (i - 1)))
    (hT : ∀ i, i < (wP ks).length → TOWin N BIG D (((wP ks).drop (i - 1)).take r') (i - (i - 1)))
    (hG : ∀ i, i < (wP ks).length → GdWin N (((wP ks).drop (i - 1)).take r') (i - (i - 1)))
    (hL : ∀ i (hi : i < (wF ks).length), KindLStep (if i = 0 then none else (wF ks)[i - 1]?) (wF ks)[i])
    (hRTk : ∀ w ∈ ks, KindRT w)
    (hSEk : ∀ w ∈ ks, ∀ b m a k d, w.sep b m a k = some d → dat a = false)
    (hDLk : ∀ w ∈ ks, ∀ u, dat u = true → w.len u = 0)
    (hb : TBehX N dat envEn x r t0 H) (hDE : ∀ v u, u ∈ D v → dat u = false)
    (hloc : ∀ v, N.gate v = true → dat v = false → v ∈ D v ∧
      LCheckXA N dat envEn (fun w => x w t0) (LC BIG (wP ks)) (uL (wk (wP ks)) (fun _ => 0)) D
        (uclT (wk (wP ks)) (fun _ => 0)) (fun v z => ugd v z (wk (wP ks)) (fun _ => 0) 0) v)
    (hEnvE : ∀ v s, N.gate v = false → dat v = false → t0 < s → x v s ≠ x v (s - 1) →
      Ideal (CFu BIG ks) (fun u => cntE dat x t0 u (s - 1)) → Enabled (CPu BIG ks) (fun w => cnt x t0 w (s - 1)) v)
    (hgdF : ∀ v z, N.gate v = false → ugd v z (wk (wP ks)) (fun _ => 0) 0 = [])
    (hGC : ∀ c ∈ uclT (wk (wP ks)) (fun _ => 0), ¬ ext c → N.gate c.z = true →
      GateProof N dat (LSep (wP ks)) (fun w => x w t0) (uclT (wk (wP ks)) (fun _ => 0)) c ∨
      ∃ cs : List (Claim α), (∀ c' ∈ cs, c' ∈ uclT (wk (wP ks)) (fun _ => 0) ∧
        GateProof N dat (LSep (wP ks)) (fun w => x w t0) (uclT (wk (wP ks)) (fun _ => 0)) c') ∧
        ChainUOK (LSep (wP ks)) (LUp (wP ks)) c cs)
    (hExt : ∀ c ∈ uclT (wk (wP ks)) (fun _ => 0), ext c → ∀ s,
      (∀ τ, τ ≤ s → Ideal (CFu BIG ks) (fun u => cntE dat x t0 u τ)) → Holds x t0 H c s)
    (hEnvC : ∀ c ∈ uclT (wk (wP ks)) (fun _ => 0), N.gate c.z = false → ∀ s,
      (∀ τ, τ ≤ s → Ideal (CFu BIG ks) (fun u => cntE dat x t0 u τ)) → Holds x t0 H c s)
    (hInit : ∀ c ∈ uclT (wk (wP ks)) (fun _ => 0), ∀ s, s ≤ t0 → Holds x t0 H c s) :
    ∀ t, (∀ τ, τ ≤ t → Ideal (CFu BIG ks) (fun u => cntE dat x t0 u τ)) ∧
      (∀ v s, dat v = false → t0 < s → s ≤ t → x v s ≠ x v (s - 1) → ChangeOKA N (CPu BIG ks) x t0 r v s) ∧
      (∀ c ∈ uclT (wk (wP ks)) (fun _ => 0), ∀ s, s ≤ t → Holds x t0 H c s) ∧ SepSound x t0 (LSep (wP ks)) t := by
  obtain ⟨hTP, hSep, hUp, hTO, hGd⟩ := timing_unroll_pad N dat D BIG r' hr ks
    (fun w hw => by obtain ⟨w0, hw0, rfl⟩ := List.mem_map.mp hw; exact hKP w0 hw0) Dc hcD hBC hS hU hT hG
  exact timedA_followsUX ext hb hTP (lsound_PF BIG ks hKF hL) (se_unroll ks dat hSEk) hTO hDE
    (fun v hg hd => lcheckXA_padC (hloc v hg hd).1 (hloc v hg hd).2) hEnvE (lenEq_unroll BIG ks) hgdF hGd hUp hSep
    (tmOK_PF BIG ks hKP hKF).2 (rt_unroll BIG ks hRTk) hGC hExt hEnvC hInit (dataLen_unroll BIG ks dat hDLk)

/-- **Liveness for the certificate of every word**, with upper-bound joins and external claims. -/
theorem timedA_live_unrollUX (ext : Claim α → Prop) [DecidablePred ext] (BIG r' : Nat) (hr : 2 ≤ r') (ks : List (WKindF α)) (Dc : α → List α)
    (hKP : ∀ w ∈ ks, KindTm BIG w.toWKindT) (hKF : ∀ w ∈ ks, KindTm BIG w.full)
    (hcD : ∀ w ∈ wP ks, ∀ u k, ∀ alt ∈ w.causes u k, ∀ q ∈ alt, q.1 ∈ Dc u) (hBC : BackChain (wP ks))
    (hS : ∀ i, i < (wP ks).length → SepWin N BIG (((wP ks).drop (i - 1)).take r') (i - (i - 1)))
    (hU : ∀ i, i < (wP ks).length → UpWin N dat BIG (((wP ks).drop (i - 1)).take r') (i - (i - 1)))
    (hT : ∀ i, i < (wP ks).length → TOWin N BIG D (((wP ks).drop (i - 1)).take r') (i - (i - 1)))
    (hG : ∀ i, i < (wP ks).length → GdWin N (((wP ks).drop (i - 1)).take r') (i - (i - 1)))
    (hL : ∀ i (hi : i < (wF ks).length), KindLStep (if i = 0 then none else (wF ks)[i - 1]?) (wF ks)[i])
    (hRTk : ∀ w ∈ ks, KindRT w)
    (hSEk : ∀ w ∈ ks, ∀ b m a k d, w.sep b m a k = some d → dat a = false)
    (hDLk : ∀ w ∈ ks, ∀ u, dat u = true → w.len u = 0)
    (hSubk : ∀ w ∈ ks, KindSub w) (hNek : ∀ w ∈ ks, KindNe w)
    (U : List α) (hCovk : ∀ w ∈ ks, ∀ u, 0 < w.len u → u ∈ U)
    (hb : TBehX N dat envEn x r t0 H) (hDE : ∀ v u, u ∈ D v → dat u = false)
    (hloc : ∀ v, N.gate v = true → dat v = false → v ∈ D v ∧
      LCheckXA N dat envEn (fun w => x w t0) (LC BIG (wP ks)) (uL (wk (wP ks)) (fun _ => 0)) D
        (uclT (wk (wP ks)) (fun _ => 0)) (fun v z => ugd v z (wk (wP ks)) (fun _ => 0) 0) v)
    (hEnvE : ∀ v s, N.gate v = false → dat v = false → t0 < s → x v s ≠ x v (s - 1) →
      Ideal (CFu BIG ks) (fun u => cntE dat x t0 u (s - 1)) → Enabled (CPu BIG ks) (fun w => cnt x t0 w (s - 1)) v)
    (hgdF : ∀ v z, N.gate v = false → ugd v z (wk (wP ks)) (fun _ => 0) 0 = [])
    (hGC : ∀ c ∈ uclT (wk (wP ks)) (fun _ => 0), ¬ ext c → N.gate c.z = true →
      GateProof N dat (LSep (wP ks)) (fun w => x w t0) (uclT (wk (wP ks)) (fun _ => 0)) c ∨
      ∃ cs : List (Claim α), (∀ c' ∈ cs, c' ∈ uclT (wk (wP ks)) (fun _ => 0) ∧
        GateProof N dat (LSep (wP ks)) (fun w => x w t0) (uclT (wk (wP ks)) (fun _ => 0)) c') ∧
        ChainUOK (LSep (wP ks)) (LUp (wP ks)) c cs)
    (hExt : ∀ c ∈ uclT (wk (wP ks)) (fun _ => 0), ext c → ∀ s,
      (∀ τ, τ ≤ s → Ideal (CFu BIG ks) (fun u => cntE dat x t0 u τ)) → Holds x t0 H c s)
    (hEnvC : ∀ c ∈ uclT (wk (wP ks)) (fun _ => 0), N.gate c.z = false → ∀ s,
      (∀ τ, τ ≤ s → Ideal (CFu BIG ks) (fun u => cntE dat x t0 u τ)) → Holds x t0 H c s)
    (hInit : ∀ c ∈ uclT (wk (wP ks)) (fun _ => 0), ∀ s, s ≤ t0 → Holds x t0 H c s)
    (K : α → Nat) (hK : ∀ v, N.gate v = true → 1 ≤ K v ∧ ∀ w ∈ N.pins v, N.hi v w < K v)
    (henv : ∀ u t, N.gate u = false → dat u = false → t0 ≤ t → Enabled (CFu BIG ks) (fun w => cntE dat x t0 w t) u →
      ∃ t', t < t' ∧ cnt x t0 u t < cnt x t0 u t') :
    ∃ T, t0 ≤ T ∧ (∀ u, cntE dat x t0 u T = (CFu BIG ks).len u) ∧ ∀ u s, dat u = false → T ≤ s → x u s = x u T := by
  obtain ⟨hTP, hSep, hUp, hTO, hGd⟩ := timing_unroll_pad N dat D BIG r' hr ks
    (fun w hw => by obtain ⟨w0, hw0, rfl⟩ := List.mem_map.mp hw; exact hKP w0 hw0) Dc hcD hBC hS hU hT hG
  exact timedA_liveUX ext hb hTP (lsound_PF BIG ks hKF hL) (se_unroll ks dat hSEk) hTO hDE
    (fun v hg hd => lcheckXA_padC (hloc v hg hd).1 (hloc v hg hd).2) hEnvE (lenEq_unroll BIG ks) hgdF hGd hUp hSep
    (tmOK_PF BIG ks hKP hKF).2 (rt_unroll BIG ks hRTk) hGC hExt hEnvC hInit (dataLen_unroll BIG ks dat hDLk)
    (sub_unroll BIG ks hSubk) U (cov_unroll BIG ks U hCovk) K hK (ne_unroll BIG ks hNek) henv

end main

end Formal.Net.AO
