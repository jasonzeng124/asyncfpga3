-- MUTANT M09_SelfAuditB9 of Formal/Cells/SelfAuditB9.lean: pin_of_pinless without the pinless hypothesis hnil (must FAIL)
import Formal.Cells.FiniteNetMixed
import Formal.Cells.EdgeTimesRing

/-!
# SelfAuditB9 (probe Bsa6, shard B): checks found while auditing shard B's work since self-audit 5

Note: `formal/notes/B-self-audit6.md`. Core Lean only (no Mathlib).

## Assumed / proved / NOT covered

**Assumed:** nothing beyond the imported files.

**Proved:**
1. `fcellOK_of_gph`, `seg_of_clean`: a cell whose node is a clean step signal meets its
   truncated contract `FCellOK`, whatever its pins do. So every assumed contract of
   `FiniteNetMixed` / `AssumeGuaranteeMuxNNet` (`H_REST`), and the chain-end contracts
   `SRC_SEG` / `SNK_SEG` of `FiniteNet.FChain` (same shape), hold on a run as soon as their
   conclusion does.
2. `fcellOK_nil_iff`: for a cell with NO pins, `FCellOK` is equivalent to "its node is a
   clean step signal" (`GPh`). Such a cell is allowed by `GD` / `FGcdNetOK` / `FGcdNetOK3`:
   `H_REST` asks `FCellOK` of every untied cell, and no field fixes `D.pins` of an untied
   cell or the driver (`GPin.drv`) of a tied cell's pin.
3. `pin_of_pinless`, `flink_env1_local`: a link cell (`FLinkSpec`) whose request and
   acknowledge pins are driven by pinless cells gets Bfin's `FEnv1` and `Timing1` from the
   two drivers' `FCellOK` alone (with `FNetW`), no other cell of the network entering. So in
   `gcd_hw_safe_fin_net` / `_net3` the link environment "derived from the network" can be,
   for every link, the assumed contract of a private pinless driver: the gate models of the
   forks, joins, steers, muxes, muxn and trees need not lie on any link's input path.
4. `htok_iff_D`, `pring_D_pos`: `RingPhys.PRing`'s field `H_TOK` is equivalent to
   `0 < Ring.D N b`; so the `0 < D` half of `EdgeTimesRing.ring_run_iff`'s forward direction is
   a field of the hypothesis (no dynamics used); only `D < N` (and `3 ≤ N`) is derived.

**NOT covered:** a whole `FGcdNetOK` / `FGcdNetOK3` instance with pinless drivers is not built
here (the uncommitted probe Bfin3, `FiniteNetWit2`, builds one for `FGcdNetOK` on `chW`).
-/

namespace Formal.Cells.SelfAuditB9
open Formal.Cells
open Formal.Cells.FiniteNet
open Formal.Cells.WinFifoCausal (Timing1 τs)
open Formal.Cells.PipeTimed (Vph)
open Formal.Cells.FiniteRuns (FEnv1)
open Formal.Cells.LutFbBridge2Env (ash)
open Formal.Cells.AssumeGuaranteeEnds (GPin gE)
open Formal.Cells.AssumeGuaranteeEndsNet (GD)

variable {ι : Type}

/-- **A contract holds when its conclusion does.** -/
theorem fcellOK_of_gph {D : GD ι} {L : ι → Nat → Prop} {c : ι}
    (h : GPh (D.O c) (D.τ c) (L c)) : FCellOK D L c :=
  fun T _ => h (T + D.lo c)

/-- **The chain-end contracts of `FiniteNet.FChain` hold when their conclusion does**
(`SRC_SEG` / `SNK_SEG` have this shape: any premise `A T`, conclusion the end node clean up to
`T + lo`). -/
theorem seg_of_clean {x : Nat → Bool} {c : Nat → Nat} {L : Nat → Prop} (h : GPh x c L)
    (A : Nat → Prop) (k : Nat) : ∀ T, A T → GPhT x c L (T + k) :=
  fun T _ => h (T + k)

/-- **A pinless cell's contract is the bare assertion that its node is clean.** -/
theorem fcellOK_nil_iff {D : GD ι} {L : ι → Nat → Prop} {c : ι} (hnil : D.pins c = []) :
    FCellOK D L c ↔ GPh (D.O c) (D.τ c) (L c) := by
  constructor
  · intro h T
    exact gphT_mono (h T (by rw [hnil]; intro p hp; simp at hp)) (by omega)
  · exact fcellOK_of_gph

/-- **A pin driven by a pinless cell is clean from that cell's contract alone.** -/
theorem pin_of_pinless {D : GD ι} {L : ι → Nat → Prop} (NW : FNetW D L) {c : ι} {p : GPin ι}
    (hp : p ∈ D.pins c) (hok : FCellOK D L p.drv) :
    GPh p.P (gE D.τ p) (L p.drv) := fun T =>
  gphT_mono (twire (NW.H_WIRE c p hp) ((fcellOK_nil_iff hnil).1 hok T) (NW.H_FLOOR c p hp))
    (by omega)

/-- **A link's `FEnv1`, local form.** `flink_spec_env1`'s conclusion for a link cell whose two
pins are driven by pinless cells, from `FNetW`, the link's own spec and the two drivers'
contracts: no other cell of the network is used. -/
theorem flink_env1_local (D : GD ι) (L : ι → Nat → Prop) (NW : FNetW D L) (n : ι → Nat)
    (hn : ∀ c j, L c j ↔ j < n c) {c : ι} {rp ap : GPin ι} {Es Ea : Nat}
    (S : FLinkSpec D L c rp ap Es Ea) (hr : D.pins rp.drv = []) (ha : D.pins ap.drv = [])
    (okr : FCellOK D L rp.drv) (oka : FCellOK D L ap.drv) :
    FEnv1 rp.P ap.P D.rst (D.O c) (D.lo c) (D.hi c) D.R (gE D.τ rp) (ash D.R (gE D.τ ap))
      (n rp.drv) (n ap.drv) Es Ea ∧ Timing1 (D.lo c) (D.hi c) (D.fh c) D.R Es Ea := by
  have pr := pin_of_pinless NW (c := c) (p := rp) (by rw [S.H_PINS]; simp) hr okr
  have pa := pin_of_pinless NW (c := c) (p := ap) (by rw [S.H_PINS]; simp) ha oka
  have hL : ∀ c, L c = fun j => j < n c := fun c => funext fun j => propext (hn c j)
  rw [hL] at pr pa
  have pr' := gph_fin_iff.1 pr
  have pa' := gph_fin_iff.1 pa
  have hlnk : ∀ j, j < n rp.drv → (∀ i, j = i + 1 → i < n ap.drv) → L c j := fun j h1 h2 =>
    (S.H_CNT j).2 ⟨(hn _ j).2 h1, fun i hi => (hn _ i).2 (h2 i hi)⟩
  refine ⟨{ H_RST := NW.H_RST
            H_REQ_LOW0 := fun t _ h => pr'.pre t h
            H_REQ := pr'.ph
            H_ACK0 := rfl
            H_ACK := fun j t hj h1 h2 => ?_
            H_RST_EARLY := S.H_RST_EARLY 0
            H_SND := fun j h1 h2 => ?_
            H_RCV := fun j h1 h2 => ?_ }, S.H_T⟩
  · cases j with
    | zero =>
      rw [pa'.pre t (by by_cases h : n ap.drv = 0; exact Or.inl h; exact Or.inr (h2 (by omega)))]
      rfl
    | succ k => rw [pa'.ph k t (by omega) h1 h2, PipeTimed.Vph_succ, Bool.not_not]
  · rw [← S.H_TIMES j]
    exact S.H_SND j (hlnk j (by omega) (fun i hi => by omega)) ((hn _ (j + 1)).2 h1)
  · rw [← S.H_TIMES j]
    exact S.H_RCV j (hlnk j h2 (fun i hi => by omega)) ((hn _ j).2 h1)

/-! ## Rings: `H_TOK` is `0 < D` -/

open Formal.Net

/-- `RingPhys.PRing.H_TOK` (some wavefront in the reset pattern) is `0 < Ring.D N b`. -/
theorem htok_iff_D (N : Nat) (b : Nat → Bool) :
    (∃ i, i < N ∧ Ring.tok N b i = true) ↔ 0 < Ring.D N b :=
  ⟨fun ⟨_, hi, h⟩ => Ring.cnt_ge_of_true hi h, fun h => Ring.cnt_pos h⟩

/-- The `0 < D` half of `ring_run_iff`'s forward direction, from the field `H_TOK` alone. -/
theorem pring_D_pos {D : RingPhys.RingData} (C : RingPhys.PRing D) : 0 < Ring.D D.N D.b :=
  (htok_iff_D D.N D.b).1 C.H_TOK

end Formal.Cells.SelfAuditB9
