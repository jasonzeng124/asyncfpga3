import Formal.Core.Trace.Discrete
import Formal.Core.Delay.SAF
import Formal.Core.Delay.GLSFid

/-!
# What a passing board-fidelity GLS run (`GLS_MODEL=fid`) does and does not imply

The fid channel is formalised in `Formal.Core.Delay.GLSFid`: every combinational fid
primitive is a *per-pin pure-delay gate* (`perPin`): pin `j` of cell `k` is read
`D k j` steps ago (routed wire + the pin's SDF arc, `perPin_icbuf`, `fidO6_default`), then
a zero-time function. A fid run on an acyclic netlist without state nodes (no
`FID_RESOLVE` resolver active) is therefore a `FidRun` at one per-pin assignment `D`.

The silicon envelope is `BandRun lo hi`: every pin of every cell is SOME monotone time warp
with delays in `[lo k j, hi k j]` (the `Trace.Discrete` `Transport` channel, chosen per pin
and allowed to vary from edge to edge, e.g. rise slower than fall, which prjxray-db cannot
distinguish). This is the sound digital envelope used by Delay/Pure and Delay/Corner. It is
not an involution or analog model. Inertial silicon is treated separately (`inertial`).

Discrete time, 1 step = 1 ps. Lean core only (no Mathlib).

Results:
* (a) `fid_in_band`, `fid_unique`: a fid run at a point of the band is one band behaviour,
  and the only fid run at that point.
* (b) sufficient conditions under which runs cover the band:
  - `band_settle_sta`, `band_agree_sta` (any logic): from the static-timing horizon on,
    every band behaviour (so every fid run at any point of the band) has the same, settled
    value. One run gives the final values, nothing before the horizon.
  - `bracket` (monotone acyclic logic, rising inputs): the two consistent-corner runs (all
    arcs at FAST_MIN = `lo`, all at SLOW_MAX = `hi`) bracket every band behaviour,
    edge-varying ones included; `cover_rise`, `cover_quiet`, `cover_bundle`.
* (c) counterexamples, each an explicit netlist and stimulus:
  - `xor_*`: an XOR of one edge through two pins with identical bands. EVERY run whose
    per-arc delay is a function of the arc's corner data (min, max, typ, `band` lerp, any
    `GLS_DELAY_SCALE`) passes; a point of the band (mixed corners) glitches, under a
    transport output and under an inertial output with `δ < hi - lo`; with `δ ≥ hi - lo`
    the inertial output hides it (there the fid run is the pessimistic one).
  - `and_*`: the same with a monotone AND and one falling input: `bracket`'s
    rising-inputs hypothesis cannot be dropped.
  - `buf_*`: a buffer on a `w`-ps pulse. EVERY fid run, at every point of the band, passes
    the pulse; a band behaviour whose pin is `w` slower on the rise than on the fall loses
    it (`w + lo ≤ hi`). With an inertial output `δ ≥ w` every point loses it, while every
    fid run shows it.
-/

namespace Formal.Core.GLSPass2

open Formal.Core.TraceDiscrete
open Formal.Core.GLSFid (perPin)

/-! ## Netlists, fid runs and band behaviours -/

/-- A netlist. Signals `0 .. m-1` are primary inputs; every signal `k ≥ m` is a cell with
`ar k` pins, pin `j` reading signal `src k j`, and zero-time function `F k`. -/
structure PNet where
  m : Nat
  ar : Nat → Nat
  src : Nat → Nat → Nat
  F : Nat → (Nat → Bool) → Bool

/-- Acyclic, with signals numbered in topological order. -/
def Topo (N : PNet) : Prop := ∀ k j, N.m ≤ k → j < N.ar k → N.src k j < k

/-- A cell reads only its first `ar k` pins. -/
def Local (N : PNet) : Prop :=
  ∀ k (a b : Nat → Bool), (∀ j, j < N.ar k → a j = b j) → N.F k a = N.F k b

/-- A fid run at the per-pin assignment `D` (wire + arc for pin `j` of cell `k`), inputs `x`. -/
def FidRun (N : PNet) (D : Nat → Nat → Nat) (x : Nat → Sig) (s : Nat → Sig) : Prop :=
  (∀ i, i < N.m → s i = x i) ∧
    ∀ k, N.m ≤ k → s k = perPin (N.F k) (D k) (fun j => s (N.src k j))

/-- A band behaviour: every pin is some `Transport (lo k j) (hi k j)` read of its source. -/
def BandRun (N : PNet) (lo hi : Nat → Nat → Nat) (x : Nat → Sig) (s : Nat → Sig) : Prop :=
  (∀ i, i < N.m → s i = x i) ∧
    ∀ k, N.m ≤ k → ∃ φ : Nat → Nat → Nat, (∀ j, j < N.ar k → Warp (lo k j) (hi k j) (φ j)) ∧
      ∀ t, s k t = N.F k (fun j => s (N.src k j) (φ j t))

/-- The assignment is a point of the band. -/
def InBand (N : PNet) (lo hi D : Nat → Nat → Nat) : Prop :=
  ∀ k j, N.m ≤ k → j < N.ar k → lo k j ≤ D k j ∧ D k j ≤ hi k j

/-! ## (a) A fid run is one point of the band -/

theorem fid_in_band {N : PNet} {lo hi D : Nat → Nat → Nat} {x s : Nat → Sig}
    (hb : InBand N lo hi D) (h : FidRun N D x s) : BandRun N lo hi x s := by
  refine ⟨h.1, fun k hk => ⟨fun j t => t - D k j, fun j hj => ?_, fun t => ?_⟩⟩
  · have := hb k j hk hj
    exact ⟨fun a b hab => by dsimp only; omega, fun t => by dsimp only; omega,
      fun t => by dsimp only; omega⟩
  · rw [h.2 k hk]; rfl

/-- Strong induction over signal numbers (core has no `Nat.strong_induction_on` lemma we
want to depend on by name). -/
theorem strong {P : Nat → Prop} (h : ∀ k, (∀ i, i < k → P i) → P k) : ∀ k, P k := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih => exact h k ih

/-- On an acyclic netlist the fid run at an assignment is unique. -/
theorem fid_unique {N : PNet} (ht : Topo N) (hl : Local N) {D : Nat → Nat → Nat}
    {x s s' : Nat → Sig} (h : FidRun N D x s) (h' : FidRun N D x s') : ∀ k, s k = s' k := by
  refine strong fun k ih => ?_
  by_cases hk : k < N.m
  · rw [h.1 k hk, h'.1 k hk]
  · have hk' : N.m ≤ k := by omega
    rw [h.2 k hk', h'.2 k hk']
    funext t
    exact hl k _ _ fun j hj => by
      show s (N.src k j) (t - D k j) = s' (N.src k j) (t - D k j)
      rw [ih _ (ht k j hk' hj)]

/-! ## (b1) Any logic: the static-timing horizon -/

/-- `S` is a static-timing horizon for the band: inputs are constant from `S i`, and every
cell's horizon is at least each source's horizon plus that pin's maximum delay. -/
def STA (N : PNet) (hi : Nat → Nat → Nat) (x : Nat → Sig) (S : Nat → Nat) : Prop :=
  (∀ i, i < N.m → ∀ t, S i ≤ t → x i t = x i (S i)) ∧
    ∀ k j, N.m ≤ k → j < N.ar k → S (N.src k j) + hi k j ≤ S k

/-- Every band behaviour is settled from the horizon on. -/
theorem band_settle_sta {N : PNet} (ht : Topo N) (hl : Local N) {lo hi : Nat → Nat → Nat}
    {x s : Nat → Sig} {S : Nat → Nat} (hS : STA N hi x S) (hs : BandRun N lo hi x s) :
    ∀ k t, S k ≤ t → s k t = s k (S k) := by
  refine strong fun k ih => ?_
  intro t ht'
  by_cases hk : k < N.m
  · rw [hs.1 k hk]; exact hS.1 k hk t ht'
  · have hk' : N.m ≤ k := by omega
    obtain ⟨φ, hφ, he⟩ := hs.2 k hk'
    rw [he t, he (S k)]
    refine hl k _ _ fun j hj => ?_
    have h1 := hS.2 k j hk' hj
    have w1 := (hφ j hj).early_le t
    have w2 := (hφ j hj).early_le (S k)
    rw [ih _ (ht k j hk' hj) (φ j t) (by omega), ih _ (ht k j hk' hj) (φ j (S k)) (by omega)]

/-- Any two band behaviours (for example two fid runs at two points of the band, or a fid
run and the silicon) agree from the horizon on. -/
theorem band_agree_sta {N : PNet} (ht : Topo N) (hl : Local N) {lo hi : Nat → Nat → Nat}
    {x s s' : Nat → Sig} {S : Nat → Nat} (hS : STA N hi x S) (hs : BandRun N lo hi x s)
    (hs' : BandRun N lo hi x s') : ∀ k t, S k ≤ t → s k t = s' k t := by
  refine strong fun k ih => ?_
  intro t ht'
  by_cases hk : k < N.m
  · rw [hs.1 k hk, hs'.1 k hk]
  · have hk' : N.m ≤ k := by omega
    obtain ⟨φ, hφ, he⟩ := hs.2 k hk'
    obtain ⟨φ', hφ', he'⟩ := hs'.2 k hk'
    rw [he t, he' t]
    refine hl k _ _ fun j hj => ?_
    have h1 := hS.2 k j hk' hj
    have w1 := (hφ j hj).early_le t
    have w2 := (hφ' j hj).early_le t
    have hsrc := ht k j hk' hj
    rw [band_settle_sta ht hl hS hs _ _ (show S (N.src k j) ≤ φ j t by omega),
      band_settle_sta ht hl hS hs' _ _ (show S (N.src k j) ≤ φ' j t by omega)]
    exact ih _ hsrc _ (Nat.le_refl _)

/-- **One fid run covers the band's final values**: if the fid run at any point of the
band shows `v` on signal `k` at some time after the horizon, every band behaviour shows `v`
on `k` from the horizon on. Nothing is said before the horizon. -/
theorem fid_final_covers {N : PNet} (ht : Topo N) (hl : Local N) {lo hi D : Nat → Nat → Nat}
    {x g s : Nat → Sig} {S : Nat → Nat} (hS : STA N hi x S) (hD : InBand N lo hi D)
    (hg : FidRun N D x g) (hs : BandRun N lo hi x s) (k T : Nat) (hT : S k ≤ T) :
    ∀ t, S k ≤ t → s k t = g k T := by
  intro t htt
  rw [band_agree_sta ht hl hS hs (fid_in_band hD hg) k t htt,
    band_settle_sta ht hl hS (fid_in_band hD hg) k t htt,
    band_settle_sta ht hl hS (fid_in_band hD hg) k T hT]

/-! ## (b2) Monotone logic, rising inputs: two corner runs bracket the band -/

/-- Boolean order, as an implication. -/
def BLe (a b : Bool) : Prop := a = true → b = true

/-- A signal that only rises. -/
def Rising (s : Sig) : Prop := ∀ a b, a ≤ b → BLe (s a) (s b)

/-- Every cell function is monotone (positive-unate) in its pins. -/
def MonoNet (N : PNet) : Prop :=
  ∀ k (a b : Nat → Bool), N.m ≤ k → (∀ j, j < N.ar k → BLe (a j) (b j)) → BLe (N.F k a) (N.F k b)

/-- **Bracketing.** Monotone acyclic netlist, rising inputs. Let `sL` be the fid run with
every arc at its minimum (`GLS_SDF_FIELD=min`, the FAST_MIN corner) and `sH` the fid run
with every arc at its maximum (`max`, SLOW_MAX). Then every band behaviour `s` (and so
every fid run at any point of the band, every scatter seed, every mixed-corner point, and
every edge-varying behaviour) satisfies `sH ≤ s ≤ sL` at every signal and time. -/
theorem bracket {N : PNet} (ht : Topo N) (hm : MonoNet N) {lo hi : Nat → Nat → Nat}
    {x sL sH s : Nat → Sig} (hx : ∀ i, i < N.m → Rising (x i))
    (hL : FidRun N lo x sL) (hH : FidRun N hi x sH) (hs : BandRun N lo hi x s) :
    ∀ k, Rising (sL k) ∧ Rising (sH k) ∧ Rising (s k) ∧
      (∀ t, BLe (sH k t) (s k t)) ∧ (∀ t, BLe (s k t) (sL k t)) := by
  refine strong fun k ih => ?_
  by_cases hk : k < N.m
  · rw [hL.1 k hk, hH.1 k hk, hs.1 k hk]
    exact ⟨hx k hk, hx k hk, hx k hk, fun _ h => h, fun _ h => h⟩
  · have hk' : N.m ≤ k := by omega
    obtain ⟨φ, hφ, he⟩ := hs.2 k hk'
    have eL := hL.2 k hk'
    have eH := hH.2 k hk'
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro a b hab; rw [eL]
      exact hm k _ _ hk' fun j hj => (ih _ (ht k j hk' hj)).1 _ _ (by omega)
    · intro a b hab; rw [eH]
      exact hm k _ _ hk' fun j hj => (ih _ (ht k j hk' hj)).2.1 _ _ (by omega)
    · intro a b hab; rw [he a, he b]
      exact hm k _ _ hk' fun j hj =>
        (ih _ (ht k j hk' hj)).2.2.1 _ _ ((hφ j hj).mono _ _ hab)
    · intro t; rw [eH, he t]
      refine hm k _ _ hk' fun j hj => ?_
      have I := ih _ (ht k j hk' hj)
      intro h1
      exact I.2.2.2.1 _ (I.2.1 _ _ ((hφ j hj).early_le t) h1)
    · intro t; rw [eL, he t]
      refine hm k _ _ hk' fun j hj => ?_
      have I := ih _ (ht k j hk' hj)
      intro h1
      exact I.1 _ _ ((hφ j hj).le_late t) (I.2.2.2.2 _ h1)

/-- The slow-corner run covers rises: if `sH` has `k` high at `T`, every band behaviour has
`k` high from `T` on. -/
theorem cover_rise {N : PNet} (ht : Topo N) (hm : MonoNet N) {lo hi : Nat → Nat → Nat}
    {x sL sH s : Nat → Sig} (hx : ∀ i, i < N.m → Rising (x i))
    (hL : FidRun N lo x sL) (hH : FidRun N hi x sH) (hs : BandRun N lo hi x s)
    (k T : Nat) (hT : sH k T = true) : ∀ t, T ≤ t → s k t = true := by
  intro t htt
  have B := bracket ht hm hx hL hH hs k
  exact B.2.2.1 _ _ htt (B.2.2.2.1 T hT)

/-- The fast-corner run covers quiet times: if `sL` has `k` low at `T`, every band behaviour
has `k` low at every `t ≤ T`. -/
theorem cover_quiet {N : PNet} (ht : Topo N) (hm : MonoNet N) {lo hi : Nat → Nat → Nat}
    {x sL sH s : Nat → Sig} (hx : ∀ i, i < N.m → Rising (x i))
    (hL : FidRun N lo x sL) (hH : FidRun N hi x sH) (hs : BandRun N lo hi x s)
    (k T : Nat) (hT : sL k T = false) : ∀ t, t ≤ T → s k t = false := by
  intro t htt
  have B := bracket ht hm hx hL hH hs k
  cases h : s k t
  · rfl
  · have := B.1 _ _ htt (B.2.2.2.2 t h); rw [hT] at this; exact absurd this (by decide)

/-- **Bundled data from two corner runs.** If in the slow run the data `kd` is high by `T`
and in the fast run the request `kr` is low before `T`, then in every band behaviour the
request is never high while the data is low. -/
theorem cover_bundle {N : PNet} (ht : Topo N) (hm : MonoNet N) {lo hi : Nat → Nat → Nat}
    {x sL sH s : Nat → Sig} (hx : ∀ i, i < N.m → Rising (x i))
    (hL : FidRun N lo x sL) (hH : FidRun N hi x sH) (hs : BandRun N lo hi x s)
    (kd kr T : Nat) (hd : sH kd T = true) (hr : ∀ t, t < T → sL kr t = false) :
    ∀ t, s kr t = true → s kd t = true := by
  intro t h
  by_cases htt : T ≤ t
  · exact cover_rise ht hm hx hL hH hs kd T hd t htt
  · have := cover_quiet ht hm hx hL hH hs kr t (hr t (by omega)) t (Nat.le_refl _)
    rw [h] at this; exact absurd this (by decide)

/-! ## (c) Counterexamples -/

/-- A step at `p`. -/
def step (p : Nat) : Sig := fun t => decide (p ≤ t)

/-- One input (signal 0); signal 1 is a 2-pin cell `F a = a 0 op a 1`, both pins reading
signal 0; every other signal is a constant-false 0-pin cell. -/
def twoPin (op : Bool → Bool → Bool) : PNet where
  m := 1
  ar := fun k => if k = 1 then 2 else 0
  src := fun _ _ => 0
  F := fun k a => if k = 1 then op (a 0) (a 1) else false

/-- The explicit fid run of `twoPin op` at `D` with input `x`. -/
def twoPinRun (op : Bool → Bool → Bool) (D : Nat → Nat → Nat) (x : Sig) : Nat → Sig :=
  fun k t => if k = 0 then x t else if k = 1 then op (x (t - D 1 0)) (x (t - D 1 1)) else false

theorem twoPinRun_is (op : Bool → Bool → Bool) (D : Nat → Nat → Nat) (x : Sig) :
    FidRun (twoPin op) D (fun _ => x) (twoPinRun op D x) := by
  refine ⟨fun i hi => ?_, fun k hk => ?_⟩
  · have : i = 0 := by simp [twoPin] at hi; omega
    subst this; funext t; simp [twoPinRun]
  · funext t
    simp only [twoPin] at hk
    by_cases h1 : k = 1
    · subst h1; simp [twoPinRun, perPin, twoPin]
    · have h0 : k ≠ 0 := by omega
      simp [twoPinRun, perPin, twoPin, h0, h1]

theorem twoPin_topo (op : Bool → Bool → Bool) : Topo (twoPin op) := by
  intro k j hk hj
  simp only [twoPin] at hk hj ⊢
  split at hj <;> omega

theorem twoPin_local (op : Bool → Bool → Bool) : Local (twoPin op) := by
  intro k a b h
  simp only [twoPin] at h ⊢
  by_cases h1 : k = 1
  · subst h1; simp only [ite_true] at h ⊢
    rw [h 0 (by decide), h 1 (by decide)]
  · simp [h1]

/-- Any fid run of `twoPin op` is the explicit one. -/
theorem twoPin_run_eq {op : Bool → Bool → Bool} {D : Nat → Nat → Nat} {x : Sig}
    {s : Nat → Sig} (h : FidRun (twoPin op) D (fun _ => x) s) (k : Nat) :
    s k = twoPinRun op D x k :=
  fid_unique (twoPin_topo op) (twoPin_local op) h (twoPinRun_is op D x) k

/-- Corner data of each arc (for example prjxray's `(FAST_MIN, SLOW_MIN, SLOW_MAX)`
triple, as `xray_delay.py` writes it). A *consistent-corner* run takes each arc's delay as
one fixed function `g` of that arc's own corner data: `GLS_SDF_FIELD=min|typ|max|band`
(any `GLS_SDF_BAND`), with any `GLS_DELAY_SCALE`. -/
abbrev Corners := Nat → Nat → Nat × Nat × Nat

/-- **XOR, every consistent-corner run passes.** If the two pins of the XOR have the same
corner data (two sinks of one source with identical routes and arcs), every
consistent-corner fid run keeps the XOR low at all times. -/
theorem xor_consistent_pass (c : Corners) (hc : c 1 0 = c 1 1) (g : Nat × Nat × Nat → Nat)
    (p : Nat) {s : Nat → Sig}
    (h : FidRun (twoPin (· != ·)) (fun k j => g (c k j)) (fun _ => step p) s) :
    ∀ t, s 1 t = false := by
  intro t
  rw [twoPin_run_eq h]
  simp [twoPinRun, hc]

/-- **XOR, a point of the band fails.** With pin 0 at `lo` and pin 1 at `hi` (a mixed-corner
point, inside the band whenever both pins have band `[lo, hi]`), the fid run, and transport
silicon at that point, shows a pulse of width `hi - lo` on the XOR. -/
theorem xor_band_fail (lo hi p : Nat) (hp : 1 ≤ p) (hlh : lo < hi) :
    ∀ t, twoPinRun (· != ·) (fun _ j => if j = 0 then lo else hi) (step p) 1 t =
      pulse false (p + lo) (hi - lo) t := by
  intro t
  rw [Formal.Core.DelaySAF.pulse_false_eq]
  simp only [twoPinRun, step, ite_true,
    show ((1 : Nat) = 0) = False from by decide, ite_false]
  by_cases h1 : p ≤ t - lo <;> by_cases h2 : p ≤ t - hi <;>
    simp only [h1, h2, decide_true, decide_false, bne_self_eq_false, Bool.true_bne,
      Bool.false_bne, Bool.not_false] <;>
    (first | (symm; simp only [decide_eq_true_eq]; omega)
           | (symm; simp only [decide_eq_false_iff_not]; omega))

/-- The failing point is a point of the band `[lo, hi]` on both pins. -/
theorem xor_point_in_band (lo hi : Nat) (hlh : lo ≤ hi) :
    InBand (twoPin (· != ·)) (fun _ _ => lo) (fun _ _ => hi)
      (fun _ j => if j = 0 then lo else hi) := by
  intro k j _ _; dsimp only; by_cases hj : j = 0 <;> simp [hj] <;> omega

/-- Inertial silicon at the failing point, `δ < hi - lo`: the glitch survives. -/
theorem xor_inertial_fail (lo hi p δ : Nat) (hp : 1 ≤ p) (hlh : lo < hi) (hδ : δ < hi - lo) :
    inertial δ (twoPinRun (· != ·) (fun _ j => if j = 0 then lo else hi) (step p) 1)
      (p + lo + δ) = true := by
  have e : twoPinRun (· != ·) (fun _ j => if j = 0 then lo else hi) (step p) 1 =
      pulse false (p + lo) (hi - lo) := funext (xor_band_fail lo hi p hp hlh)
  rw [e, inertial_passes (by omega) hδ, Formal.Core.DelaySAF.pulse_false_eq]
  simp; omega

/-- Inertial silicon with `δ ≥ hi - lo` hides the glitch even at the mixed point: here the
fid run (transport, which shows it) is the pessimistic side. -/
theorem xor_inertial_hidden (lo hi p δ : Nat) (hp : 1 ≤ p) (hlh : lo < hi)
    (hδ : hi - lo ≤ δ) (t : Nat) :
    inertial δ (twoPinRun (· != ·) (fun _ j => if j = 0 then lo else hi) (step p) 1) t =
      false := by
  have e : twoPinRun (· != ·) (fun _ j => if j = 0 then lo else hi) (step p) 1 =
      pulse false (p + lo) (hi - lo) := funext (xor_band_fail lo hi p hp hlh)
  rw [e]; exact inertial_filters (by omega) hδ t

/-- prjxray O6 numbers: FAST_MIN 45 ps, SLOW_MAX 124 ps (one arc, two corners). Every
consistent-corner run passes; the mixed point (45, 124) shows a 79 ps glitch, which an
inertial output with `δ < 79` passes. -/
theorem xor_o6 : twoPinRun (· != ·) (fun _ j => if j = 0 then 45 else 124) (step 1000) 1 1045 = true ∧
    twoPinRun (· != ·) (fun _ j => if j = 0 then 45 else 124) (step 1000) 1 1124 = false := by
  refine ⟨?_, ?_⟩ <;> rw [xor_band_fail 45 124 1000 (by decide) (by decide)] <;>
    simp [pulse]

/-- **AND with one falling input.** The rising-inputs hypothesis of `bracket` is needed:
a monotone AND of `a` (rising at `p`) and `b` (falling at `p`), both from one source edge,
passes every consistent-corner run and glitches at a mixed point. -/
def andNet : PNet where
  m := 1
  ar := fun k => if k = 1 then 2 else 0
  src := fun _ _ => 0
  F := fun k a => if k = 1 then (a 0 && !a 1) else false

/-- `andNet` is `twoPin` with `op a b = a && !b`: the second pin reads the source inverted
(equivalently a falling input). The cell function in pins (a, b) is the monotone AND when
`b` is taken as the falling signal `!x`. -/
theorem andNet_eq : andNet = twoPin (fun a b => a && !b) := rfl

theorem and_consistent_pass (c : Corners) (hc : c 1 0 = c 1 1) (g : Nat × Nat × Nat → Nat)
    (p : Nat) {s : Nat → Sig}
    (h : FidRun andNet (fun k j => g (c k j)) (fun _ => step p) s) : ∀ t, s 1 t = false := by
  intro t
  rw [andNet_eq] at h
  rw [twoPin_run_eq h]
  simp [twoPinRun, hc]

theorem and_band_fail (lo hi p : Nat) (hp : 1 ≤ p) (hlh : lo < hi) :
    twoPinRun (fun a b => a && !b) (fun _ j => if j = 0 then lo else hi) (step p) 1 (p + lo) =
      true := by
  simp [twoPinRun, step]; omega

/-- A buffer: one input, signal 1 reads it on one pin. -/
def bufNet : PNet where
  m := 1
  ar := fun k => if k = 1 then 1 else 0
  src := fun _ _ => 0
  F := fun k a => if k = 1 then a 0 else false

/-- **Buffer, every point passes the pulse.** At every assignment, the fid run shows the
`w`-ps input pulse (`w ≥ 1`) on the buffer output, at `p + D 1 0`. -/
theorem buf_every_point_passes (D : Nat → Nat → Nat) (p w : Nat) (hw : 1 ≤ w) {s : Nat → Sig}
    (h : FidRun bufNet D (fun _ => pulse false p w) s) : s 1 (p + D 1 0) = true := by
  rw [h.2 1 (by decide)]
  simp only [perPin, bufNet, ite_true]
  rw [h.1 0 (by decide)]
  show pulse false p w (p + D 1 0 - D 1 0) = true
  rw [Formal.Core.DelaySAF.pulse_false_eq]
  simp; omega

/-- The fid run of `bufNet` exists (so `buf_every_point_passes` is not vacuous). -/
theorem buf_run_exists (D : Nat → Nat → Nat) (x : Sig) :
    FidRun bufNet D (fun _ => x) (fun k t => if k = 0 then x t else if k = 1 then x (t - D 1 0)
      else false) := by
  refine ⟨fun i hi => ?_, fun k hk => ?_⟩
  · have : i = 0 := by simp [bufNet] at hi; omega
    subst this; rfl
  · have hk0 : k ≠ 0 := by simp [bufNet] at hk; omega
    funext t
    by_cases h1 : k = 1
    · subst h1; simp [perPin, bufNet]
    · simp [perPin, bufNet, hk0, h1]

/-- **Buffer, the band loses the pulse.** If the pin's band is at least `w` wide
(`w + lo ≤ hi`), some band behaviour (rise delayed by `hi`, fall by `lo`) never raises the
buffer output. -/
theorem buf_band_loses (lo hi p w : Nat) (hp : 1 ≤ p) (hw : w + lo ≤ hi) :
    ∃ s, BandRun bufNet (fun _ _ => lo) (fun _ _ => hi) (fun _ => pulse false p w) s ∧
      ∀ t, s 1 t = false := by
  obtain ⟨f, hf, he⟩ := pulse_lost (lo := lo) (hi := hi) (p := p) (w := w) false hp hw
  refine ⟨fun k => if k = 0 then pulse false p w else fun _ => false, ⟨fun i hi' => ?_,
    fun k hk => ⟨fun _ => f, fun j _ => hf, fun t => ?_⟩⟩, fun t => ?_⟩
  · have : i = 0 := by simp [bufNet] at hi'; omega
    subst this; rfl
  · have hk0 : k ≠ 0 := by simp [bufNet] at hk; omega
    simp only [hk0, ite_false, bufNet]
    by_cases h1 : k = 1
    · simp only [h1, ite_true]
      show false = pulse false p w (f t)
      rw [← he t]
    · simp [h1]
  · simp

/-- Inertial silicon with `δ ≥ w` loses the pulse at every point, while every fid run shows
it (`buf_every_point_passes`): for a property that needs the pulse (a two-phase enable),
a fid pass is optimistic against inertial silicon. -/
theorem buf_inertial_loses (D p w δ : Nat) (hp : 1 ≤ p) (hw : w ≤ δ) (t : Nat) :
    inertial δ (delay D (pulse false p w)) t = false := by
  have e : delay D (pulse false p w) = pulse false (p + D) w := by
    funext u; rw [Formal.Core.DelaySAF.pulse_false_eq]
    simp only [delay]
    rw [Formal.Core.DelaySAF.pulse_false_eq]
    exact decide_eq_decide.mpr (by constructor <;> intro h <;> omega)
  rw [e]; exact inertial_filters (by omega) hw t

end Formal.Core.GLSPass2
