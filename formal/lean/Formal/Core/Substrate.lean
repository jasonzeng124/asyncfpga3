import Formal.Core.Substrate.Chan
import Formal.Core.Substrate.CornerNat
import Formal.Core.Substrate.Real

/-!
# Formal.Core.Substrate — THE substrate shards B and C state theorems in

One discrete-time model, one delay relation, one delay model, one bridge to
real time. Built on (importing, never copying) the proved Core files. Guide,
name map and hypothesis list: `formal/notes/A-substrate.md`.

## The ℝ bridge, stated once

Real time is the physics. Let a continuous circuit (`Discretize.CCircuit`:
gate functions through FIFO transport channels with real bands
`[lo n, hi n]`) have a behaviour `v`, and let every gate's excitation have no
two transitions within one quantum `q` (**H_SEP**). Then, for any natural
`L n ≤ lo n / q` and `H n ≥ hi n / q`, the grid samples of `v` are a behaviour
of the substrate net `C.toDNet L H` (`circuit_sample_win`), so

> **every theorem proved for all `DNet.Beh` behaviours holds of the samples of
> every such continuous behaviour** (`transfer_win`, `transfer_win_invariant`),

and a grid invariant of a jointly separated at-rest tuple holds at every real
time (`invariant_real_time`). Without H_SEP the transfer is false
(`Discretize.tie_counterexample`, `Discretize.mutex_between`): a sub-quantum
runt is the one thing the binary grid cannot see; the K3 view
(`Discretize.chan_sample_hull`, `XSim`) is where it shows up as `X`.

## Layers (file: main names)

1. `Substrate/Chan.lean` (core Lean): `Sig`, `KSig`, `Covers`; **`Win`**
   (the relation), `WinR` (at rest), `Start`; `DNet`, `DNet.Beh` / `BehR` /
   `BehT` / `BehFixed`, `DNet.refines`; inclusions `transport_winR`,
   `winR_win`, `winR_iff`, `delay_win`, `shift_win`, `saf_winR`; strictness
   `winR_not_transport`, `win_not_winR`, `inertial_not_win`; algebra
   `win_mono`, `win_comp`, `win_map`; timing `win_stable`, `win_after`,
   `winR_after`, `win_bundle`; K3 `win_covered`, `winR_covered`, `winR_exact`.
2. `Substrate/CornerNat.lean` (ℕ ps, decidable): `Kappa`, `CArc`, `Corner`,
   `nom`, `Scat`, `CornerModel`, `RealizesAt`, `Realizes`, `RealizesOn`;
   bands `bandLo`/`bandHi` (outward), `indLo`/`indHi`; `scat_band`,
   `band_sub_ind`, `scat_path`; `EndpointOK`, `bundle_endpoints`,
   `bundle_paths`, `bundle_realizes`, `bundle_band`,
   `independent_implies_endpoint`.
3. `Substrate/Real.lean`: `chan_sample_win(R)`, `circuit_sample_win(R)`,
   `transfer_win`, `invariant_real_time`; `scat_real`, `endpoint_real`,
   **`endpoints_sound_real`**, `corner_chan_sample_ind`, `corner_chan_sample_band`.
4. `Substrate/Legacy.lean` (NOT imported here; it depends on the shards'
   `Prelim`): `win_iff_winDelay`, `loop_iff`, `winR_boundedDelay`,
   `boundedDelay_not_winR`, `runOfWinR`.

Values and LUTs are not re-defined: `Formal.Core.K3` (`Kleene.lean`) and
`Formal.Core.Lut` (`Lut.lean`) are canonical; `Formal.Core.Bridge` maps
shard B's `Prelim` values onto them.

## End-to-end examples (this file)

* `win_bundle_corner`: discrete bundled data with BOTH wires in the corner
  model at one shared corner: a decidable endpoint check (margin `ts + 2`)
  makes the data settled whenever the request is seen.
* `bundle_real_of_check`: the same check, in real time, at any real corner
  (`Corner.bundle_corner` with its two endpoint hypotheses discharged by the
  ℕ check).
* `tight_band_bundle`, `floor_ceil_exist`: at any REAL corner, whole-ps
  bands tight to one ps (they exist) satisfy `ts + H_D ≤ L_R` under the same
  check, so the discrete route (`chan_sample_win` + `win_bundle`) is not
  limited to the ℕ model's rational corners.
-/

namespace Formal.Core.Substrate

theorem path_single {A : Type} (M : CornerModel A) (e : A) : M.path [e] = M.arc e := by
  cases h : M.arc e
  simp [CornerModel.path, pathArc, CArc.add, CArc.zero, h]

/-- **Bundled data, discrete, in the corner model.** Data wire `eD` and
request wire `eR` are `Win` channels with their corner bands at ONE corner
`c` (the request wire at rest). If the decidable endpoint check
`EndpointOK κ D R (ts + 2)` passes (`ts` = data settling time after the
request launch, `+2` = one ps of outward rounding per wire), the data is `v`
at the receiver whenever the request has arrived, up to `t1 + bandLo D`. -/
theorem win_bundle_corner {A : Type} (M : CornerModel A) (c : Corner) (eD eR : A)
    {ts t0 t1 s : Nat} {b v : Bool} {src data reqIn reqOut : Sig}
    (hcheck : EndpointOK M.κ (M.arc eD) (M.arc eR) (ts + 2))
    (hD : Win (bandLo M.κ c (M.arc eD)) (bandHi M.κ c (M.arc eD)) src data)
    (hR : WinR (bandLo M.κ c (M.arc eR)) (bandHi M.κ c (M.arc eR)) reqIn reqOut)
    (hsrc : ∀ u, t0 + ts ≤ u → u ≤ t1 → src u = v) (ht0 : 0 < t0)
    (hb : ∀ u, u < t0 → reqIn u = b) (hs : reqOut s ≠ b)
    (hs1 : s ≤ t1 + bandLo M.κ c (M.arc eD)) : data s = v := by
  have h := bundle_band M c [eD] [eR] (m := ts)
    (by rw [path_single, path_single]; simpa using hcheck)
  simp only [sumOver, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.add_zero] at h
  exact win_bundle hsrc hD hR ht0 hb (by omega) hs hs1

/-- **Bundled data, real time, any real corner.** The ℕ endpoint check
discharges both endpoint hypotheses of `Corner.bundle_corner`. -/
theorem bundle_real_of_check {k : Kappa} {D R : CArc} {ts : Nat} (h : EndpointOK k D R ts)
    {t0 t1 s : ℝ} {b v : Bool} {src data reqIn reqOut : DelayPure.Sig}
    (hcorner : ∃ c, 0 ≤ c ∧ c ≤ 1 ∧
      DelayPure.Chan ((1 - k.toReal) * D.toArc.at' c) ((1 + k.toReal) * D.toArc.at' c) src data ∧
      DelayPure.Chan ((1 - k.toReal) * R.toArc.at' c) ((1 + k.toReal) * R.toArc.at' c) reqIn reqOut)
    (hsrc : DelayPure.StableOn src (t0 + ts) t1 v) (hb : DelayPure.StableBefore reqIn t0 b)
    (hs : reqOut s ≠ b) (hs1 : s ≤ t1 + (1 - k.toReal) * D.F) : data s = v := by
  obtain ⟨e0, e1⟩ := endpoint_real h
  exact Formal.Core.Corner.bundle_corner (D := D.toArc) (R := R.toArc) k.toReal_le_one hcorner
    hsrc hb (by simp only [CArc.toArc]; linarith) (by simp only [CArc.toArc]; linarith) hs
    (by simpa [CArc.toArc] using hs1)

/-- **Any real corner, discrete bands.** At a REAL corner `c` (not
necessarily one of the ℕ model's rational corners), take any whole-ps bands
that are tight to one ps: `H_D < (1+κ)·D(c) + 1` and `(1-κ)·R(c) < L_R + 1`
(floor and ceiling satisfy this, `floor_ceil_exist`). The endpoint check
with margin `ts + 2` gives `ts + H_D ≤ L_R`, the hypothesis of `win_bundle`.
So the discrete route covers every real corner, not only rational ones. -/
theorem tight_band_bundle {k : Kappa} {D R : CArc} {ts : Nat} (h : EndpointOK k D R (ts + 2))
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) {HD LR : Nat}
    (hH : (HD : ℝ) < (1 + k.toReal) * D.toArc.at' c + 1)
    (hL : (1 - k.toReal) * R.toArc.at' c < (LR : ℝ) + 1) : ts + HD ≤ LR := by
  obtain ⟨e0, e1⟩ := endpoint_real h
  have := Formal.Core.Corner.bundle_ratio_affine (κ := k.toReal) (m := ((ts + 2 : Nat) : ℝ))
    (Fd := D.F) (Sd := D.S) (Fr := R.F) (Sr := R.S) hc0 hc1 e0 e1
  have key : ((ts + HD : Nat) : ℝ) < (LR : ℝ) + 1 := by
    unfold Formal.Core.Corner.Arc.at' CArc.toArc at hH hL
    simp only at hH hL
    push_cast at this ⊢
    linarith
  have : ts + HD < LR + 1 := by exact_mod_cast key
  omega

/-- Whole-ps bands tight to one ps exist for every nonnegative real band
(floor of the lower end, ceiling of the upper end). -/
theorem floor_ceil_exist {lo hi : ℝ} (hlo : 0 ≤ lo) (hhi : 0 ≤ hi) :
    ∃ L H : Nat, (L : ℝ) ≤ lo ∧ lo < (L : ℝ) + 1 ∧ hi ≤ (H : ℝ) ∧ (H : ℝ) < hi + 1 :=
  ⟨Nat.floor lo, Nat.ceil hi, Nat.floor_le hlo, Nat.lt_floor_add_one lo, Nat.le_ceil hi,
    Nat.ceil_lt_add_one hhi⟩

end Formal.Core.Substrate
