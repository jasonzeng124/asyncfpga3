import Formal.Cells.ConstraintsMux

/-!
# NecessityMuxRtz: `bd_mux.uxa_rtz_env` / `uya_rtz_env` are tight to 1 ps

Probe Bsx (shard B). The rows were "sufficient; env bound tightness argued,
not proved". The sufficient theorems are `MuxRtzTimed.mux_rtz_env_safe`
(uxa) and `ConstraintsMux.mux_rtz_env_safe_uya` (uya): a trace-level chain
z_ack (server) -> control sender -> ctl_req -> uj1 (uj0) -> uor -> request
line -> server -> z_ack -> uxa (uya), every stage a named hypothesis
(window wires `WinDelay`, min-latency stages `Causal`, the join as an `FLoop`
of its REAL INIT, uxa/uya as `CElemTiming.Loop` of the REAL bd_c2 INIT), and

    H_RTZ_ENV : te + (dlmax + dwmax) ≤ Tzf + Lmin + wux,
    Lmin = wzc + dc + wcr + dl1 + wjo + dlo + dz + ds.

## Result

`RtzEnvClaim slack` is `mux_rtz_env_safe` with H_RTZ_ENV weakened by `slack`
ticks (every other hypothesis verbatim). Then

* `claim0 : RtzEnvClaim 0` (= the existing theorem), and
* `claim1_false : ¬ RtzEnvClaim 1`: ONE tick of slack breaks it. The
  counter-run (`cex_*`, all numbers in ticks = ps) satisfies every other
  hypothesis: every stage is a 1-tick transport except the z_ack -> uxa wire
  (window [1, 4]: z_ack's FALL is seen through 4, its next RISE through 1,
  the same routed wire, H_W_ZX); uj1 has y_req waiting and s = 1 (the next
  token selects y); uxa is the real bd_c2 with dl = 2, dw = 4 (loop 6), x's
  join low. z_ack falls at the server at 21, is low at uxa's pin on
  [25, 30) (5 ticks < loop 6), and x_ack, which must stay low on [27, 102],
  is 1 again at 32 (a runt train, `MuxRtzTimed.rtz_counter`).
  `te + (dlmax + dwmax) = 31 = Tzf + Lmin + wux + 1`.
* the same for uya (`RtzEnvClaimY`, `claimY0`, `claimY1_false`) with the real
  uj0 INIT (x_req waiting, s = 0).

So the rows are **sufficient + necessary at the boundary** in this model:
no uniform weakening by even 1 ps is sound. (This is a counter-run at one
parameter point per form; it does not show that every violating parameter
point fails, nor that each term is individually needed.) With a Kleene X window on uxa's release pin
(CElemStrict) equality itself fails, which is the rows' existing +1.

* `claim1_false_1C`, `claimY1_false_1C`: the same with EVERY stage a single
  fixed delay (one corner, the z_ack wire included): still broken by one tick
  of slack. So the bound is tight in 1C as well as in the box.

NOT covered: the rest of the mux (mux_ok's other hypotheses) is not
re-checked on this run; the claim is about the cited theorem's hypothesis
set. Lumped LUT arcs, as in MuxRtzTimed.
-/

namespace Formal.Cells.NecessityMuxRtz
open Formal.Cells
open Formal.Cells.CElemTiming
open Formal.Cells.MuxRtzTimed
open Formal.Cells.ConstraintsMux (INIT_uj0 mux_rtz_env_safe_uya)

/-- `mux_rtz_env_safe` with H_RTZ_ENV weakened by `slack`. -/
def RtzEnvClaim (slack : Nat) : Prop :=
  ∀ (zs zc cr crj y s rst j1 j1q j1o j0o ei zr zx j0x rstx xa xq : Trace)
    (wzc Wzc dc tc0 tc1 wcr Wcr dl1 Dl1 dw1 Dw1 tj wjo Wjo dlo Dlo t0o Tend
     dz te0 te1 ds tz0 Tzf tch wux Wux dlmin dlmax dwmin dwmax te t2 : Nat),
    WinDelay wzc Wzc zs zc →
    Causal zc cr true false tc0 tc1 dc →
    WinDelay wcr Wcr cr crj →
    FLoop (fun t q => lutB INIT_uj1 [y t, crj t, s t, q, rst t, false]) j1 j1q dl1 Dl1 dw1 Dw1 →
    (∀ t, tj ≤ t → t < tj + (Dw1 + Dl1) → j1 t = false) →
    WinDelay wjo Wjo j1 j1o →
    WinDelay dlo Dlo (fun t => lutB 0xE [j0o t, j1o t]) ei →
    (∀ t, t0o ≤ t → t < Tend → j0o t = false) →
    Causal ei zr false false te0 te1 dz →
    Causal zr zs false false tz0 Tzf ds →
    (∀ t, tch ≤ t → t < Tzf → zs t = true) →
    WinDelay wux Wux zs zx →
    tch + Wzc ≤ tc0 → tc1 + Wcr ≤ tj + Dw1 →
    t0o ≤ tj + Wjo → tj + Wjo + Dlo ≤ te0 → te1 ≤ tz0 →
    Tzf + wzc + dc + wcr + dl1 + wjo ≤ Tend →
    Loop INIT_c2 j0x zx rstx xa xq dlmin dlmax dwmin dwmax →
    (∀ u, te ≤ u → u ≤ t2 → rstx u = false) →
    (∀ u, te ≤ u → u ≤ t2 → j0x u = false) →
    Tzf + Wux ≤ te →
    Tzf + (wzc + dc + wcr + dl1 + wjo + dlo + dz + ds) + wux ≤ t2 →
    te + (dlmax + dwmax) ≤ Tzf + (wzc + dc + wcr + dl1 + wjo + dlo + dz + ds) + wux + slack →
    ∀ t, te + dlmax ≤ t → t ≤ t2 + dlmin → xa t = false

theorem claim0 : RtzEnvClaim 0 := by
  intro zs zc cr crj y s rst j1 j1q j1o j0o ei zr zx j0x rstx xa xq wzc Wzc dc tc0 tc1 wcr Wcr
    dl1 Dl1 dw1 Dw1 tj wjo Wjo dlo Dlo t0o Tend dz te0 te1 ds tz0 Tzf tch wux Wux dlmin dlmax
    dwmin dwmax te t2 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 b1 b2 b3 b4 b5 b6 L n1 n2 n3 n4 h
  exact mux_rtz_env_safe a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 b1 b2 b3 b4 b5 b6 L n1 n2 n3 n4
    (by omega)

/-! ## The counter-run (ticks) -/

def zsN : Trace := fun t => decide (t < 21 ∨ 29 ≤ t)
def zcN : Trace := fun t => zsN (t - 1)
def crN : Trace := fun t => decide (23 ≤ t)
def crjN : Trace := fun t => crN (t - 1)
def tN : Trace := fun _ => true
def fN : Trace := fun _ => false
def j1N : Trace := fun t => decide (25 ≤ t)
def j1qN : Trace := fun t => j1N (t - 1)
def j1oN : Trace := fun t => j1N (t - 1)
def j0oN : Trace := fun t => decide (t < 10)
def eiN : Trace := fun t => lutB 0xE [j0oN (t - 1), j1oN (t - 1)]
def zrN : Trace := fun t => eiN (t - 1)

theorem tr1 (x : Trace) : WinDelay 1 1 x (fun t => x (t - 1)) :=
  transport_winDelay (Nat.le_refl _) (Nat.le_refl _) (fun t => by simp)

theorem cex_zx : WinDelay 1 4 zsN (zaC 5 25) := by
  intro t ht
  by_cases h : t < 25
  · refine ⟨t - 4, by omega, by omega, ?_⟩
    simp only [zaC, bR, zsN]
    have : ¬ (25 ≤ t ∧ t < 25 + 5) := by omega
    simp [this]; omega
  · refine ⟨t - 1, by omega, by omega, ?_⟩
    simp only [zaC, bR, zsN]
    by_cases h2 : t < 30
    · have : (25 ≤ t ∧ t < 25 + 5) := by omega
      simp [this]; omega
    · have : ¬ (25 ≤ t ∧ t < 25 + 5) := by omega
      simp [this]; omega

theorem cex_ctl : Causal zcN crN true false 1 0 1 := by
  intro T hT t _ ht
  by_cases hT22 : T ≤ 22
  · simp [crN]; omega
  · have := hT 22 (by omega) (by omega)
    exact absurd this (by decide)

theorem cex_dly : Causal eiN zrN false false 12 13 1 := by
  intro T hT t h1 h2
  exact hT (t - 1) (by omega) (by omega)

theorem cex_srv : Causal zrN zsN false false 13 21 1 := by
  intro T hT t h1 h2
  by_cases hT28 : T ≤ 28
  · simp [zsN]; omega
  · have := hT 28 (by omega) (by omega)
    exact absurd this (by decide)

theorem cex_uj1 :
    FLoop (fun t q => lutB INIT_uj1 [tN t, crjN t, tN t, q, fN t, false]) j1N j1qN 1 1 1 1 where
  H_LUT := transport_winDelay (Nat.le_refl _) (Nat.le_refl _) (fun t => by
    show j1N (t + 1) = lutB INIT_uj1 [true, crjN t, true, j1qN t, false, false]
    rw [uj1_eq]
    simp only [j1N, crjN, crN, j1qN]
    by_cases h : 24 ≤ t
    · have e1 : 23 ≤ t - 1 := by omega
      simp [e1]; omega
    · have e1 : ¬ 23 ≤ t - 1 := by omega
      have e2 : ¬ 25 ≤ t - 1 := by omega
      simp [e1, e2]; omega)
  H_FB := tr1 j1N
  H_LOOP_POS := by decide

theorem cex_uor : WinDelay 1 1 (fun t => lutB 0xE [j0oN t, j1oN t]) eiN := tr1 _

/-- **Every hypothesis except H_RTZ_ENV holds, H_RTZ_ENV fails by exactly one
tick, and the conclusion fails at 32.** -/
theorem claim1_false : ¬ RtzEnvClaim 1 := by
  intro h
  have hc := h zsN zcN crN crjN tN tN fN j1N j1qN j1oN j0oN eiN zrN (zaC 5 25) j0C rstR
    (xaC 2 4 5 25) (qpC 2 4 5 25)
    1 1 1 1 0 1 1 1 1 1 1 10 1 1 1 1 10 1000 1 12 13 1 13 21 0 1 4 2 2 4 4 25 100
    (tr1 zsN) cex_ctl (tr1 crN) cex_uj1
    (fun t h1 h2 => by simp [j1N]; omega) (tr1 j1N) cex_uor
    (fun t h1 h2 => by simp [j0oN]; omega) cex_dly cex_srv
    (fun t h1 h2 => by simp [zsN]; omega) cex_zx
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (rtz_counter_loop 2 4 5 25 (by decide) (by decide))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (by decide) (by decide) (by decide)
    32 (by decide) (by decide)
  have := ((rtz_counter 2 4 5 25 (by decide) (by decide)).2.1 0).2
  rw [show 25 + 2 + (2 + 4) * 0 + 5 = 32 by decide] at this
  rw [hc] at this
  exact absurd this (by decide)

/-- The counter-run's numbers: H_RTZ_ENV is violated by exactly 1 tick. -/
theorem cex_margin : 25 + (2 + 4) = 21 + (1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) + 1 + 1 := by decide

/-! ## uya (mirror, real uj0 INIT: x_req waiting, s = 0) -/

def RtzEnvClaimY (slack : Nat) : Prop :=
  ∀ (zs zc cr crj x s rst j0 j0q j0o j1o ei zr zy j1y rsty ya yq : Trace)
    (wzc Wzc dc tc0 tc1 wcr Wcr dl0 Dl0 dw0 Dw0 tj wjo Wjo dlo Dlo t1o Tend
     dz te0 te1 ds tz0 Tzf tch wuy Wuy dlmin dlmax dwmin dwmax te t2 : Nat),
    WinDelay wzc Wzc zs zc →
    Causal zc cr true false tc0 tc1 dc →
    WinDelay wcr Wcr cr crj →
    FLoop (fun t q => lutB INIT_uj0 [x t, crj t, s t, q, rst t, false]) j0 j0q dl0 Dl0 dw0 Dw0 →
    (∀ t, tj ≤ t → t < tj + (Dw0 + Dl0) → j0 t = false) →
    WinDelay wjo Wjo j0 j0o →
    WinDelay dlo Dlo (fun t => lutB 0xE [j0o t, j1o t]) ei →
    (∀ t, t1o ≤ t → t < Tend → j1o t = false) →
    Causal ei zr false false te0 te1 dz →
    Causal zr zs false false tz0 Tzf ds →
    (∀ t, tch ≤ t → t < Tzf → zs t = true) →
    WinDelay wuy Wuy zs zy →
    tch + Wzc ≤ tc0 → tc1 + Wcr ≤ tj + Dw0 →
    t1o ≤ tj + Wjo → tj + Wjo + Dlo ≤ te0 → te1 ≤ tz0 →
    Tzf + wzc + dc + wcr + dl0 + wjo ≤ Tend →
    Loop INIT_c2 j1y zy rsty ya yq dlmin dlmax dwmin dwmax →
    (∀ u, te ≤ u → u ≤ t2 → rsty u = false) →
    (∀ u, te ≤ u → u ≤ t2 → j1y u = false) →
    Tzf + Wuy ≤ te →
    Tzf + (wzc + dc + wcr + dl0 + wjo + dlo + dz + ds) + wuy ≤ t2 →
    te + (dlmax + dwmax) ≤ Tzf + (wzc + dc + wcr + dl0 + wjo + dlo + dz + ds) + wuy + slack →
    ∀ t, te + dlmax ≤ t → t ≤ t2 + dlmin → ya t = false

theorem claimY0 : RtzEnvClaimY 0 := by
  intro zs zc cr crj x s rst j0 j0q j0o j1o ei zr zy j1y rsty ya yq wzc Wzc dc tc0 tc1 wcr Wcr
    dl0 Dl0 dw0 Dw0 tj wjo Wjo dlo Dlo t1o Tend dz te0 te1 ds tz0 Tzf tch wuy Wuy dlmin dlmax
    dwmin dwmax te t2 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 b1 b2 b3 b4 b5 b6 L n1 n2 n3 n4 h
  exact mux_rtz_env_safe_uya a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 b1 b2 b3 b4 b5 b6 L n1 n2 n3 n4
    (by omega)

/-- uj0 with x_req = 1, s = 0, rst = 0 is `ctl_req || q`. -/
theorem uj0_sel : ∀ c q : Bool, lutB INIT_uj0 [true, c, false, q, false, false] = (c || q) := by
  decide

theorem cex_uj0 :
    FLoop (fun t q => lutB INIT_uj0 [tN t, crjN t, fN t, q, fN t, false]) j1N j1qN 1 1 1 1 where
  H_LUT := transport_winDelay (Nat.le_refl _) (Nat.le_refl _) (fun t => by
    show j1N (t + 1) = lutB INIT_uj0 [true, crjN t, false, j1qN t, false, false]
    rw [uj0_sel]
    simp only [j1N, crjN, crN, j1qN]
    by_cases h : 24 ≤ t
    · have e1 : 23 ≤ t - 1 := by omega
      simp [e1]; omega
    · have e1 : ¬ 23 ≤ t - 1 := by omega
      have e2 : ¬ 25 ≤ t - 1 := by omega
      simp [e1, e2]; omega)
  H_FB := tr1 j1N
  H_LOOP_POS := by decide

/-- uor with the joins swapped (j0 now carries the new token, j1 the old). -/
def eiY : Trace := fun t => lutB 0xE [j1oN (t - 1), j0oN (t - 1)]
def zrY : Trace := fun t => eiY (t - 1)

theorem cexY_dly : Causal eiY zrY false false 12 13 1 := by
  intro T hT t h1 h2
  exact hT (t - 1) (by omega) (by omega)

theorem cexY_srv : Causal zrY zsN false false 13 21 1 := by
  intro T hT t h1 h2
  by_cases hT28 : T ≤ 28
  · simp [zsN]; omega
  · have := hT 28 (by omega) (by omega)
    exact absurd this (by decide)

theorem claimY1_false : ¬ RtzEnvClaimY 1 := by
  intro h
  have hc := h zsN zcN crN crjN tN fN fN j1N j1qN j1oN j0oN eiY zrY (zaC 5 25) j0C rstR
    (xaC 2 4 5 25) (qpC 2 4 5 25)
    1 1 1 1 0 1 1 1 1 1 1 10 1 1 1 1 10 1000 1 12 13 1 13 21 0 1 4 2 2 4 4 25 100
    (tr1 zsN) cex_ctl (tr1 crN) cex_uj0
    (fun t h1 h2 => by simp [j1N]; omega) (tr1 j1N) (tr1 _)
    (fun t h1 h2 => by simp [j0oN]; omega) cexY_dly cexY_srv
    (fun t h1 h2 => by simp [zsN]; omega) cex_zx
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (rtz_counter_loop 2 4 5 25 (by decide) (by decide))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (by decide) (by decide) (by decide)
    32 (by decide) (by decide)
  have := ((rtz_counter 2 4 5 25 (by decide) (by decide)).2.1 0).2
  rw [show 25 + 2 + (2 + 4) * 0 + 5 = 32 by decide] at this
  rw [hc] at this
  exact absurd this (by decide)


/-! ## One-corner (1C) counter-runs: every wire a single fixed delay

The runs above see z_ack's fall at uxa through 4 and its rise through 1 (a
box-mode wire). Here EVERY stage, the z_ack -> uxa / uya wire included, is a
1-tick transport (one corner); uxa / uya have dl = 2, dw = 7 (loop 9). z_ack
is low at the pin on [22, 30) (8 ticks), `te + (dlmax + dwmax) = 31 =
Tzf + Lmin + wux + 1`, and x_ack (y_ack) is 1 again at 32. -/

theorem cex_zx1 : WinDelay 1 1 zsN (zaC 8 22) := by
  intro t ht
  refine ⟨t - 1, by omega, by omega, ?_⟩
  simp only [zaC, bR, zsN]
  by_cases h2 : 22 ≤ t ∧ t < 22 + 8
  · simp [h2]; omega
  · simp [h2]; omega

theorem claim1_false_1C : ¬ RtzEnvClaim 1 := by
  intro h
  have hc := h zsN zcN crN crjN tN tN fN j1N j1qN j1oN j0oN eiN zrN (zaC 8 22) j0C rstR
    (xaC 2 7 8 22) (qpC 2 7 8 22)
    1 1 1 1 0 1 1 1 1 1 1 10 1 1 1 1 10 1000 1 12 13 1 13 21 0 1 1 2 2 7 7 22 100
    (tr1 zsN) cex_ctl (tr1 crN) cex_uj1
    (fun t h1 h2 => by simp [j1N]; omega) (tr1 j1N) cex_uor
    (fun t h1 h2 => by simp [j0oN]; omega) cex_dly cex_srv
    (fun t h1 h2 => by simp [zsN]; omega) cex_zx1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (rtz_counter_loop 2 7 8 22 (by decide) (by decide))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (by decide) (by decide) (by decide)
    32 (by decide) (by decide)
  have := ((rtz_counter 2 7 8 22 (by decide) (by decide)).2.1 0).2
  rw [show 22 + 2 + (2 + 7) * 0 + 8 = 32 by decide] at this
  rw [hc] at this
  exact absurd this (by decide)

theorem claimY1_false_1C : ¬ RtzEnvClaimY 1 := by
  intro h
  have hc := h zsN zcN crN crjN tN fN fN j1N j1qN j1oN j0oN eiY zrY (zaC 8 22) j0C rstR
    (xaC 2 7 8 22) (qpC 2 7 8 22)
    1 1 1 1 0 1 1 1 1 1 1 10 1 1 1 1 10 1000 1 12 13 1 13 21 0 1 1 2 2 7 7 22 100
    (tr1 zsN) cex_ctl (tr1 crN) cex_uj0
    (fun t h1 h2 => by simp [j1N]; omega) (tr1 j1N) (tr1 _)
    (fun t h1 h2 => by simp [j0oN]; omega) cexY_dly cexY_srv
    (fun t h1 h2 => by simp [zsN]; omega) cex_zx1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (rtz_counter_loop 2 7 8 22 (by decide) (by decide))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (by decide) (by decide) (by decide)
    32 (by decide) (by decide)
  have := ((rtz_counter 2 7 8 22 (by decide) (by decide)).2.1 0).2
  rw [show 22 + 2 + (2 + 7) * 0 + 8 = 32 by decide] at this
  rw [hc] at this
  exact absurd this (by decide)

end Formal.Cells.NecessityMuxRtz
