import Formal.Cells.RingPhysStage

/-!
# Probe Bring (shard B), part 2: a physical ring of `bd_c2n` / `bd_c2n_set` stages

A ring of `N` link controllers wired as `tb_ring.v` and C's `Formal.Net.Ring` (stage `i`
reads its request from node `prv i` and its acknowledge from node `nxt i`); stage `i` is
`bd_c2n_set` if `b i = true` (comes up holding) and `bd_c2n` otherwise. Every gate is B's
bounded-delay model (`StageB`: Win LUT + H_NO_REVERT + feedback wire, real INITs; `WireB`:
window wires). The circle is closed by `AssumeGuarantee.ag_time`, as for chains, with the
event time the END of each node segment; there is no stage index to induct on, the time
does it.

## Assumed / proved / NOT covered

**Assumed** (`PRing`, `PRingT`): per stage `StageB`, H_PWR (node at its reset value before
the LUT's first sure read), H_LUT_POS; per wire `WireB`; H_RST; H_TIMES (the edge times are
read off the node traces: `τs` of the stage's own pins' phase starts, the pin edges `ε` of
the drivers' edges; definitions written as equations, the theorems hold for every
solution); H_TOK (some stage differs from its upstream at reset: `D > 0`). Timing
(`PRingT`): H_RST_LONG, H_LAT with the DERIVED slacks `Es i = vl (prv i) + lo (prv i) + wl i`,
`Ea i = wl (nxt i) + lo (nxt i) + vl i` (exactly `link_link_env`'s / the chain's),
H_WIRE_R, H_RT (each wire's spread below the round trip of its channel). NO environment
hypothesis on any stage, no source, no sink.

**Proved:**
* `ring_nodes` (the circle closed): every node, normalised by its reset value, is a clean
  step signal with edges `τ i`: the physical node is `b i` until its first edge and then
  alternates, for EVERY edge index (infinitely many edges); `ring_toggles`: it toggles at
  each `τ i j`, and the `τ i j` are strictly increasing (`ring_inc`);
* `ring_cond` (**the hypotheses force C's token/bubble condition**): `3 ≤ N` and
  `0 < D < N`, where `D = Ring.D N b` is C's wavefront count of the reset pattern (twice the
  number of loop tokens). Proof: otherwise `ring_frozen_D` (no C-excited stage, every trace
  frozen) contradicts `ring_nodes`. So timing adds NO condition to C's: under the link
  rows (H_LAT, H_RT, H_WIRE_R, H_RST_LONG) the live rings are exactly C's;
* `ring_tick` / `ring_reach` (**refinement onto C's `Ring`**): every node that changes at
  tick `t+1` is C-excited (`Ring.excited`) in the sampled state at `t`, and every sampled
  state is reachable (`Ring.Reach`) from `b` in C's interleaving semantics (simultaneous
  toggles are fired in index order, by C's `persistent`); hence C's `D_reach`: the
  physical ring conserves `D` (`ring_tokens`);
* `ring_reset_live`: for C's reset `resetState K` (`0 < K < N`: `K` `_set` stages), the
  hypotheses imply `N ≥ 3` (C's ring rule, physical), every node circulates forever.

**NOT covered:** existence of a solution of H_TIMES in general (only the witnesses of
`RingPhysWit`, `N = 3`); the converse "`0 < D < N` implies a run exists" is therefore
shown only on the witness; data latches; X power-up; the LinkExact box model (this file
uses B's `Stage`/`Win` model, where the cross-token re-arm race is covered by H_LAT and
the derived departures, see the note). Core Lean only.
-/

namespace Formal.Cells.RingPhys
open Formal.Cells Formal.Net
open Formal.Cells.WinFifo (Win win_le)
open Formal.Cells.WinFifoCausal (nt nt_lo Stage cph τs cW vW)
open Formal.Cells.PipeTimed (Vph)
open Formal.Cells.LutFbBridge (Phases)
open Formal.Cells.LutFbBridge2Env (Wire ε ε_lo ash)
open Formal.Cells.AssumeGuarantee (ag_time)
open Formal.Cells.AssumeGuaranteeLinks (SegK phases_of_segK segK_of_phases wire_segK)
open Formal.Net.Ring (prv nxt excited b2n)

/-! ## 1. The data and the gate relations -/

/-- The data of a ring (traces, delays, edge times). Wire `(wl i, wh i)` drives stage `i`'s
request pin from node `prv i`; wire `(vl i, vh i)` drives its acknowledge pin from node
`nxt i`. -/
structure RingData where
  N : Nat
  R : Nat
  b : Nat → Bool
  O : Nat → Nat → Bool
  req : Nat → Nat → Bool
  ack : Nat → Nat → Bool
  qp : Nat → Nat → Bool
  rst : Nat → Bool
  lo : Nat → Nat
  hi : Nat → Nat
  fl : Nat → Nat
  fh : Nat → Nat
  wl : Nat → Nat
  wh : Nat → Nat
  vl : Nat → Nat
  vh : Nat → Nat
  τ : Nat → Nat → Nat

namespace RingData
variable (D : RingData)

/-- C's wavefront at stage `i` in the reset pattern. -/
def tk (i : Nat) : Bool := Ring.tok D.N D.b i
/-- Node `i` normalised by its reset value (starts at 0). -/
def On (i : Nat) : Nat → Bool := xr (D.b i) (D.O i)
/-- Request pin of stage `i`, normalised by its DRIVER's reset value. -/
def P (i : Nat) : Nat → Bool := xr (D.b (prv D.N i)) (D.req i)
/-- Acknowledge pin of stage `i`, normalised by its driver's reset value. -/
def Q (i : Nat) : Nat → Bool := xr (D.b (nxt D.N i)) (D.ack i)
def εF (i : Nat) : Nat → Nat := ε (D.P i) (D.wl i) (D.wh i) (D.τ (prv D.N i))
def εB (i : Nat) : Nat → Nat := ε (D.Q i) (D.vl i) (D.vh i) (D.τ (nxt D.N i))
/-- Stage `i`'s request phase starts: with a wavefront at `i` the first phase is already
present at reset release (the upstream holds the token). -/
def ρR (i : Nat) : Nat → Nat := cond (D.tk i) (ash D.R (D.εF i)) (D.εF i)
/-- Stage `i`'s acknowledge phase starts: with a wavefront at `nxt i` the first phase waits
for the downstream's first edge. -/
def αR (i : Nat) : Nat → Nat := cond (D.tk (nxt D.N i)) (D.εB i) (ash D.R (D.εB i))
def Es (i : Nat) : Nat := D.vl (prv D.N i) + D.lo (prv D.N i) + D.wl i
def Ea (i : Nat) : Nat := D.wl (nxt D.N i) + D.lo (nxt D.N i) + D.vl i
/-- Minimum round trip of the channel into stage `i` (from node `prv i`). -/
def RTF (i : Nat) : Nat := D.wl i + D.lo i + D.vl (prv D.N i) + D.lo (prv D.N i)
/-- Minimum round trip of the channel out of stage `i` (to node `nxt i`). -/
def RTB (i : Nat) : Nat := D.vl i + D.lo i + D.wl (nxt D.N i) + D.lo (nxt D.N i)

end RingData

/-- **The gate relations of the ring.** No environment hypothesis on any stage. -/
structure PRing (D : RingData) : Prop where
  H_RST : ∀ t, D.rst t = decide (t < D.R)
  /-- each stage: B's bounded-delay controller, real INIT of its polarity. -/
  H_STAGE : ∀ i, i < D.N → StageB (D.b i) (D.req i) (D.ack i) D.rst (D.O i) (D.qp i)
    (D.lo i) (D.hi i) (D.fl i) (D.fh i)
  H_PWR : ∀ i, i < D.N → ∀ t, t < D.hi i → D.O i t = D.b i
  H_LUT_POS : ∀ i, i < D.N → 1 ≤ D.lo i
  H_WF : ∀ i, i < D.N → WireB (D.b (prv D.N i)) (D.wl i) (D.wh i) (D.O (prv D.N i)) (D.req i)
  H_WB : ∀ i, i < D.N → WireB (D.b (nxt D.N i)) (D.vl i) (D.vh i) (D.O (nxt D.N i)) (D.ack i)
  /-- **H_TIMES**: each edge time is the node's own edge after its pins' phase starts. -/
  H_TIMES : ∀ i, i < D.N → ∀ j, D.τ i j = τs (D.On i) (D.lo i) (D.hi i) (D.ρR i) (D.αR i) j
  /-- **H_TOK**: at least one wavefront in the reset pattern. -/
  H_TOK : ∃ i, i < D.N ∧ D.tk i = true

/-- **Timing of the ring** (the chain's `ChainT`, per stage and per channel). -/
structure PRingT (D : RingData) : Prop where
  H_RST_LONG : ∀ i, i < D.N → D.hi i + D.fh i ≤ D.R
  H_LAT : ∀ i, i < D.N → D.hi i + D.fh i ≤ D.lo i + min (D.Es i) (D.Ea i)
  H_WIRE_R : ∀ i, i < D.N → D.wh i ≤ D.R ∧ D.vh i ≤ D.R
  H_RT : ∀ i, i < D.N → D.wh i ≤ D.RTF i ∧ D.vh i ≤ D.RTB i

/-! ## 2. Unconditional time inequalities -/

theorem ρR_t0 {D : RingData} (i : Nat) (h : D.tk i = true) : D.ρR i 0 = D.R := by
  unfold RingData.ρR; rw [h]; rfl

theorem αR_f0 {D : RingData} (i : Nat) (h : D.tk (nxt D.N i) = false) : D.αR i 0 = D.R := by
  unfold RingData.αR; rw [h]; rfl

section times
variable {D : RingData} (C : PRing D)
include C

theorem r_lh (i : Nat) (hi : i < D.N) : D.lo i ≤ D.hi i :=
  win_le (stageB_norm (C.H_STAGE i hi)).H_LUT_WIN

theorem t_ρ (i : Nat) (hi : i < D.N) (j : Nat) : D.ρR i j + D.lo i ≤ D.τ i j := by
  rw [C.H_TIMES i hi j]
  have := nt_lo (D.On i) (cph (D.ρR i) (D.αR i) j) (Vph j) (r_lh C i hi) (hi := D.hi i)
  have : D.ρR i j ≤ cph (D.ρR i) (D.αR i) j := Nat.le_max_left _ _
  unfold τs; omega

theorem t_α (i : Nat) (hi : i < D.N) (j : Nat) : D.αR i j + D.lo i ≤ D.τ i j := by
  rw [C.H_TIMES i hi j]
  have := nt_lo (D.On i) (cph (D.ρR i) (D.αR i) j) (Vph j) (r_lh C i hi) (hi := D.hi i)
  have : D.αR i j ≤ cph (D.ρR i) (D.αR i) j := Nat.le_max_right _ _
  unfold τs; omega

theorem t_F_f (i : Nat) (hi : i < D.N) (h : D.tk i = false) (j : Nat) :
    D.τ (prv D.N i) j + D.wl i ≤ D.ρR i j := by
  have e : D.ρR i j = D.εF i j := by unfold RingData.ρR; rw [h]; rfl
  rw [e]; exact ε_lo (wireB_norm (C.H_WF i hi)) _ j

theorem t_F_t (i : Nat) (hi : i < D.N) (h : D.tk i = true) (j : Nat) :
    D.τ (prv D.N i) j + D.wl i ≤ D.ρR i (j + 1) := by
  have e : D.ρR i (j + 1) = D.εF i j := by unfold RingData.ρR; rw [h]; rfl
  rw [e]; exact ε_lo (wireB_norm (C.H_WF i hi)) _ j

theorem t_B_t (i : Nat) (hi : i < D.N) (h : D.tk (nxt D.N i) = true) (j : Nat) :
    D.τ (nxt D.N i) j + D.vl i ≤ D.αR i j := by
  have e : D.αR i j = D.εB i j := by unfold RingData.αR; rw [h]; rfl
  rw [e]; exact ε_lo (wireB_norm (C.H_WB i hi)) _ j

theorem t_B_f (i : Nat) (hi : i < D.N) (h : D.tk (nxt D.N i) = false) (j : Nat) :
    D.τ (nxt D.N i) j + D.vl i ≤ D.αR i (j + 1) := by
  have e : D.αR i (j + 1) = D.εB i j := by unfold RingData.αR; rw [h]; rfl
  rw [e]; exact ε_lo (wireB_norm (C.H_WB i hi)) _ j

/-- Stage `i`'s request departs at least `Es` after its own edge (unconditional). -/
theorem r_snd (i : Nat) (hi : i < D.N) (j : Nat) : D.τ i j + D.Es i ≤ D.ρR i (j + 1) := by
  have hx := Ring.prv_lt hi
  have e1 : nxt D.N (prv D.N i) = i := Ring.nxt_prv hi
  unfold RingData.Es
  cases h : D.tk i
  · have a := t_F_f C i hi h (j + 1)
    have b := t_α C (prv D.N i) hx (j + 1)
    have c := t_B_f C (prv D.N i) hx (by rw [e1]; exact h) j
    rw [e1] at c; omega
  · have a := t_F_t C i hi h j
    have b := t_α C (prv D.N i) hx j
    have c := t_B_t C (prv D.N i) hx (by rw [e1]; exact h) j
    rw [e1] at c; omega

/-- Stage `i`'s acknowledge departs at least `Ea` after its own edge (unconditional). -/
theorem r_rcv (i : Nat) (hi : i < D.N) (j : Nat) : D.τ i j + D.Ea i ≤ D.αR i (j + 1) := by
  have hy := Ring.nxt_lt hi
  have e1 : prv D.N (nxt D.N i) = i := Ring.prv_nxt hi
  unfold RingData.Ea
  cases h : D.tk (nxt D.N i)
  · have a := t_B_f C i hi h j
    have b := t_ρ C (nxt D.N i) hy j
    have c := t_F_f C (nxt D.N i) hy h j
    rw [e1] at c; omega
  · have a := t_B_t C i hi h (j + 1)
    have b := t_ρ C (nxt D.N i) hy (j + 1)
    have c := t_F_t C (nxt D.N i) hy h j
    rw [e1] at c; omega

theorem r_inc (i : Nat) (hi : i < D.N) (j : Nat) : D.τ i j < D.τ i (j + 1) := by
  have := r_snd C i hi j; have := t_ρ C i hi (j + 1); have := C.H_LUT_POS i hi; omega

theorem r_mono (i : Nat) (hi : i < D.N) {j j' : Nat} (h : j ≤ j') : D.τ i j ≤ D.τ i j' := by
  induction j' with
  | zero => have : j = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ j' ih =>
    rcases Nat.lt_or_ge j (j' + 1) with h' | h'
    · have := ih (by omega); have := r_inc C i hi j'; omega
    · have : j = j' + 1 := by omega
      subst this; exact Nat.le_refl _

/-- Spacing of node `prv i`, measured by the round trip of channel `i`. -/
theorem r_spF (i : Nat) (hi : i < D.N) (j : Nat) :
    D.τ (prv D.N i) j + D.RTF i ≤ D.τ (prv D.N i) (j + 1) := by
  have hx := Ring.prv_lt hi
  have e1 : nxt D.N (prv D.N i) = i := Ring.nxt_prv hi
  have a := r_rcv C (prv D.N i) hx j
  have b := t_α C (prv D.N i) hx (j + 1)
  unfold RingData.Ea at a; rw [e1] at a
  unfold RingData.RTF; omega

/-- Spacing of node `nxt i`, measured by the round trip of channel `nxt i`. -/
theorem r_spB (i : Nat) (hi : i < D.N) (j : Nat) :
    D.τ (nxt D.N i) j + D.RTB i ≤ D.τ (nxt D.N i) (j + 1) := by
  have hy := Ring.nxt_lt hi
  have e1 : prv D.N (nxt D.N i) = i := Ring.prv_nxt hi
  have a := r_snd C (nxt D.N i) hy j
  have b := t_ρ C (nxt D.N i) hy (j + 1)
  unfold RingData.Es at a; rw [e1] at a
  unfold RingData.RTB; omega

/-- **Every first edge comes after reset release** (from H_TOK, by induction on the
distance to the nearest upstream wavefront). -/
theorem r_ge0 (i : Nat) (hi : i < D.N) : D.R < D.τ i 0 := by
  obtain ⟨i0, h0, ht⟩ := C.H_TOK
  have key : ∀ d, D.R < D.τ ((i0 + d) % D.N) 0 := by
    intro d
    induction d with
    | zero =>
      rw [Nat.add_zero, Nat.mod_eq_of_lt h0]
      have := t_ρ C i0 h0 0; rw [ρR_t0 i0 ht] at this
      have := C.H_LUT_POS i0 h0; omega
    | succ d ih =>
      have hm : (i0 + d) % D.N < D.N := Nat.mod_lt _ (by omega)
      rw [← Nat.add_assoc, Ring.mod_succ_nxt]
      have hn := Ring.nxt_lt hm
      have hl := C.H_LUT_POS _ hn
      cases h : D.tk (nxt D.N ((i0 + d) % D.N))
      · have a := t_F_f C _ hn h 0
        rw [Ring.prv_nxt hm] at a
        have := t_ρ C _ hn 0; omega
      · have := t_ρ C _ hn 0; rw [ρR_t0 _ h] at this; omega
  have e : (i0 + (i + D.N - i0)) % D.N = i := by
    have : i0 + (i + D.N - i0) = i + D.N := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
  have := key (i + D.N - i0); rw [e] at this; exact this

theorem r_geR (i : Nat) (hi : i < D.N) (j : Nat) : D.R < D.τ i j := by
  have := r_ge0 C i hi; have := r_mono C i hi (Nat.zero_le j); omega

theorem r_early (i : Nat) (hi : i < D.N) : D.R ≤ D.ρR i 0 ∧ D.R ≤ D.αR i 0 := by
  constructor
  · cases h : D.tk i
    · have := t_F_f C i hi h 0; have := r_ge0 C _ (Ring.prv_lt hi); omega
    · rw [ρR_t0 i h]; exact Nat.le_refl _
  · cases h : D.tk (nxt D.N i)
    · rw [αR_f0 i h]; exact Nat.le_refl _
    · have := t_B_t C i hi h 0; have := r_ge0 C _ (Ring.nxt_lt hi); omega

end times

/-! ## 3. Pin bookkeeping -/

theorem rq_eq (D : RingData) (i t : Nat) :
    xr (D.b i) (D.req i) t = cond (D.tk i) (!D.P i t) (D.P i t) := by
  unfold RingData.P RingData.tk Ring.tok xr
  cases D.b (prv D.N i) <;> cases D.b i <;> cases D.req i t <;> rfl

theorem ak_eq (D : RingData) (i t : Nat) (hi : i < D.N) :
    xr (D.b i) (D.ack i) t = cond (D.tk (nxt D.N i)) (!D.Q i t) (D.Q i t) := by
  unfold RingData.Q RingData.tk Ring.tok xr
  rw [Ring.prv_nxt hi]
  cases D.b (nxt D.N i) <;> cases D.b i <;> cases D.ack i t <;> rfl

theorem seg0 {P : Nat → Bool} {e : Nat → Nat} (h : SegK P e 0) : ∀ t, t < e 0 → P t = false :=
  fun t ht => h t (Nat.zero_le _) ht

theorem segS {P : Nat → Bool} {e : Nat → Nat} {j : Nat} (h : SegK P e (j + 1)) :
    ∀ t, e j ≤ t → t < e (j + 1) → P t = Vph j := fun t h1 h2 => h t h1 h2

theorem Vph0 : Vph 0 = true := rfl

/-! ## 4. The circle, closed -/

/-- Guarantee of event `(i, k)`: segment `k` of node `i` (normalised). -/
def Gev (D : RingData) (e : Nat × Nat) : Prop :=
  e.1 < D.N → SegK (D.On e.1) (D.τ e.1) e.2

/-- Assumption of event `(i, k)`: the request pin's segments `m` with `m + [tok i] ≤ k`,
the acknowledge pin's segments `m` with `m + 1 ≤ k + [tok (nxt i)]`. -/
def Aev (D : RingData) (e : Nat × Nat) : Prop :=
  e.1 < D.N →
    (∀ m, m + b2n (D.tk e.1) ≤ e.2 → SegK (D.P e.1) (D.εF e.1) m) ∧
    (∀ m, m + 1 ≤ e.2 + b2n (D.tk (nxt D.N e.1)) → SegK (D.Q e.1) (D.εB e.1) m)

section closed
variable {D : RingData} (C : PRing D) (T : PRingT D)
include C T

/-- **H_CELL**: every stage meets its contract (`link_segK'` on the normalised stage). -/
theorem ring_cell (e : Nat × Nat) (hA : Aev D e) : Gev D e := by
  obtain ⟨i, k⟩ := e
  intro hi
  obtain ⟨aF, aB⟩ := hA hi
  simp only at aF aB hi ⊢
  have hτ : D.τ i = τs (D.On i) (D.lo i) (D.hi i) (D.ρR i) (D.αR i) := funext (C.H_TIMES i hi)
  rw [hτ]
  have hE := r_early C i hi
  refine link_segK' (E := min (D.Es i) (D.Ea i)) (stageB_norm (C.H_STAGE i hi)) C.H_RST
    (T.H_RST_LONG i hi) (T.H_LAT i hi) (C.H_LUT_POS i hi) ?_ hE (fun j => ?_) (fun j => ?_) k
    ?_ ?_
  · intro t ht; show cond (D.b i) (!D.O i t) (D.O i t) = false
    rw [C.H_PWR i hi t ht]; cases D.b i <;> rfl
  · show τs (D.On i) (D.lo i) (D.hi i) (D.ρR i) (D.αR i) j + _ ≤ _
    rw [← C.H_TIMES i hi j]; have := r_snd C i hi j; omega
  · show τs (D.On i) (D.lo i) (D.hi i) (D.ρR i) (D.αR i) j + _ ≤ _
    rw [← C.H_TIMES i hi j]; have := r_rcv C i hi j; omega
  · intro hk t h1 h2
    subst hk
    rw [rq_eq, ak_eq D i t hi]
    unfold cph at h2
    cases hF : D.tk i <;> cases hB : D.tk (nxt D.N i)
    · left
      have := aF 0 (by rw [hF]; decide)
      have e1 : D.ρR i 0 = D.εF i 0 := by unfold RingData.ρR; rw [hF]; rfl
      have e2 : D.αR i 0 = D.R := αR_f0 i hB
      rw [seg0 this t (by omega)]; rfl
    · by_cases ht : t < D.εF i 0
      · left
        have := aF 0 (by rw [hF]; decide)
        rw [seg0 this t ht]; rfl
      · right
        have e1 : D.ρR i 0 = D.εF i 0 := by unfold RingData.ρR; rw [hF]; rfl
        have e2 : D.αR i 0 = D.εB i 0 := by unfold RingData.αR; rw [hB]; rfl
        have := aB 0 (by rw [hB]; decide)
        rw [seg0 this t (by omega)]; rfl
    · have e1 := ρR_t0 i hF; have e2 := αR_f0 i hB; omega
    · right
      have e1 := ρR_t0 i hF
      have e2 : D.αR i 0 = D.εB i 0 := by unfold RingData.αR; rw [hB]; rfl
      have := aB 0 (by rw [hB]; decide)
      rw [seg0 this t (by omega)]; rfl
  · intro j hk
    subst hk
    refine ⟨fun t h1 h2 => ?_, fun t h1 h2 => ?_⟩
    · rw [rq_eq]
      cases hF : D.tk i
      · have e : ∀ m, D.ρR i m = D.εF i m := fun m => by unfold RingData.ρR; rw [hF]; rfl
        rw [e] at h1; rw [e] at h2
        have := aF (j + 1) (by rw [hF]; simp [b2n])
        exact segS this t h1 h2
      · have := aF j (by rw [hF]; simp [b2n])
        show (!D.P i t) = Vph j
        cases j with
        | zero =>
          rw [ρR_t0 i hF] at h1
          have e : D.ρR i 1 = D.εF i 0 := by unfold RingData.ρR; rw [hF]; rfl
          rw [e] at h2
          rw [seg0 this t h2]; rfl
        | succ j' =>
          have e : ∀ m, D.ρR i (m + 1) = D.εF i m := fun m => by unfold RingData.ρR; rw [hF]; rfl
          rw [e] at h1; rw [e] at h2
          rw [segS this t h1 h2, PipeTimed.Vph_succ]
    · rw [ak_eq D i t hi]
      cases hB : D.tk (nxt D.N i)
      · have := aB j (by rw [hB]; simp [b2n])
        show D.Q i t = !Vph j
        cases j with
        | zero =>
          rw [αR_f0 i hB] at h1
          have e : D.αR i 1 = D.εB i 0 := by unfold RingData.αR; rw [hB]; rfl
          rw [e] at h2
          rw [seg0 this t h2]; rfl
        | succ j' =>
          have e : ∀ m, D.αR i (m + 1) = D.εB i m := fun m => by unfold RingData.αR; rw [hB]; rfl
          rw [e] at h1; rw [e] at h2
          rw [segS this t h1 h2, PipeTimed.Vph_succ, Bool.not_not]
      · have e : ∀ m, D.αR i m = D.εB i m := fun m => by unfold RingData.αR; rw [hB]; rfl
        rw [e] at h1; rw [e] at h2
        have := aB (j + 1) (by rw [hB]; simp [b2n])
        show (!D.Q i t) = !Vph j
        rw [segS this t h1 h2]

/-- **H_ENV** with the causality side condition: each pin segment an event reads is a
wire copy (`wire_segK`) of a node segment that ENDS strictly earlier. -/
theorem ring_env (e : Nat × Nat) (ih : ∀ e', D.τ e'.1 e'.2 < D.τ e.1 e.2 → Gev D e') :
    Aev D e := by
  obtain ⟨i, k⟩ := e
  intro hi
  simp only at ih hi ⊢
  have hx := Ring.prv_lt hi
  have hy := Ring.nxt_lt hi
  have hl := C.H_LUT_POS i hi
  refine ⟨fun m hm => ?_, fun m hm => ?_⟩
  · have WF := C.H_WF i hi
    have hlt : D.τ (prv D.N i) m < D.τ i k := by
      have := WF.H_POS
      cases hF : D.tk i
      · rw [hF] at hm; simp [b2n] at hm
        have := t_F_f C i hi hF m; have := t_ρ C i hi m; have := r_mono C i hi hm; omega
      · rw [hF] at hm; simp [b2n] at hm
        have := t_F_t C i hi hF m; have := t_ρ C i hi (m + 1)
        have := r_mono C i hi (show m + 1 ≤ k by omega); omega
    have hG := ih (prv D.N i, m) hlt hx
    exact wire_segK (wireB_norm WF) m hG (fun j _ => by
      have := (T.H_WIRE_R i hi).1; have := r_geR C _ hx j; have := r_spF C i hi j
      have := (T.H_RT i hi).1; have := WF.H_POS
      exact ⟨by omega, by omega⟩)
  · have WB := C.H_WB i hi
    have hlt : D.τ (nxt D.N i) m < D.τ i k := by
      have := WB.H_POS
      cases hB : D.tk (nxt D.N i)
      · rw [hB] at hm; simp [b2n] at hm
        have := t_B_f C i hi hB m; have := t_α C i hi (m + 1)
        have := r_mono C i hi (show m + 1 ≤ k by omega); omega
      · rw [hB] at hm; simp [b2n] at hm
        have := t_B_t C i hi hB m; have := t_α C i hi m; have := r_mono C i hi hm; omega
    have hG := ih (nxt D.N i, m) hlt hy
    exact wire_segK (wireB_norm WB) m hG (fun j _ => by
      have := (T.H_WIRE_R i hi).2; have := r_geR C _ hy j; have := r_spB C i hi j
      have := (T.H_RT i hi).2; have := WB.H_POS
      exact ⟨by omega, by omega⟩)

/-- **The circle closed, on a ring.** Every node, normalised by its reset value, is a clean
step signal with the edges read off its own trace, for every edge index. -/
theorem ring_nodes (i : Nat) (hi : i < D.N) : Phases (D.On i) (D.τ i) :=
  phases_of_segK fun k =>
    ag_time (fun e : Nat × Nat => D.τ e.1 e.2) (Gev D) (Aev D) (ring_cell C T)
      (ring_env C T) (i, k) hi

/-- The physical node: its reset value on segment 0, then alternating. -/
theorem ring_node_val (i : Nat) (hi : i < D.N) :
    (∀ t, t < D.τ i 0 → D.O i t = D.b i) ∧
    (∀ j t, D.τ i j ≤ t → t < D.τ i (j + 1) → D.O i t = (D.b i != Vph j)) := by
  have ph := ring_nodes C T i hi
  have inv : ∀ t, D.O i t = (D.b i != D.On i t) := fun t => by
    unfold RingData.On xr; cases D.b i <;> cases D.O i t <;> rfl
  refine ⟨fun t ht => ?_, fun j t h1 h2 => ?_⟩
  · rw [inv, ph.pre t ht]; cases D.b i <;> rfl
  · rw [inv, ph.ph j t h1 h2]

/-- **The ring circulates forever**: every node toggles at every `τ i j`, and these
instants increase strictly (so every node toggles infinitely often). -/
theorem ring_toggles (i : Nat) (hi : i < D.N) (j : Nat) :
    D.τ i j < D.τ i (j + 1) ∧ D.O i (D.τ i j) ≠ D.O i (D.τ i j - 1) := by
  have hinc := r_inc C i hi
  refine ⟨hinc j, ?_⟩
  have v := ring_node_val C T i hi
  have a := v.2 j (D.τ i j) (Nat.le_refl _) (hinc j)
  have hR := r_ge0 C i hi
  cases j with
  | zero =>
    have b := v.1 (D.τ i 0 - 1) (by omega)
    rw [a, b, Vph0]; cases D.b i <;> decide
  | succ j' =>
    have hj' := hinc j'
    have b := v.2 j' (D.τ i (j' + 1) - 1) (by omega) (by omega)
    rw [a, b, PipeTimed.Vph_succ]; cases D.b i <;> cases Vph j' <;> decide

theorem ring_inf (i : Nat) (hi : i < D.N) (T0 : Nat) :
    ∃ t, T0 ≤ t ∧ D.O i (t + 1) ≠ D.O i t := by
  have hj : T0 + 1 ≤ D.τ i (T0 + 1) := by
    have : ∀ j, j ≤ D.τ i j := by
      intro j; induction j with
      | zero => exact Nat.zero_le _
      | succ j ih => have := r_inc C i hi j; omega
    exact this _
  refine ⟨D.τ i (T0 + 1) - 1, by omega, ?_⟩
  have := (ring_toggles C T i hi (T0 + 1)).2
  rw [show D.τ i (T0 + 1) - 1 + 1 = D.τ i (T0 + 1) by omega]; exact this

/-! ## 5. The hypotheses force C's token/bubble condition -/

/-- **Necessity, physical**: a ring satisfying the gate relations and the timing rows has
`3 ≤ N` and `0 < D < N` (C's `live_iff`). Timing adds no condition, and removes none. -/
theorem ring_cond : 3 ≤ D.N ∧ 0 < Ring.D D.N D.b ∧ Ring.D D.N D.b < D.N := by
  apply Classical.byContradiction
  intro hn
  have h : D.N ≤ 2 ∨ ¬ (0 < Ring.D D.N D.b ∧ Ring.D D.N D.b < D.N) := by
    by_cases h2 : D.N ≤ 2
    · exact Or.inl h2
    · exact Or.inr fun ⟨a, b⟩ => hn ⟨by omega, a, b⟩
  have fr := ring_frozen_D D.b C.H_RST C.H_STAGE C.H_PWR
    (fun i hi => by have := T.H_RST_LONG i hi; omega) C.H_LUT_POS C.H_WF C.H_WB h
  obtain ⟨i0, hi0, _⟩ := C.H_TOK
  have := (ring_toggles C T i0 hi0 0).2
  rw [fr _ i0 hi0, fr _ i0 hi0] at this
  exact this rfl

end closed

/-! ## 6. Refinement onto C's ring -/

/-- The sampled state at tick `t` (C's `Ring.State`). -/
def st (D : RingData) (t : Nat) : Ring.State := fun i => if i < D.N then D.O i t else D.b i

/-- Segment membership. -/
def InSeg (c : Nat → Nat) (m t : Nat) : Prop :=
  (m = 0 → t < c 0) ∧ (∀ m', m = m' + 1 → c m' ≤ t ∧ t < c m)

theorem seg_val {x : Nat → Bool} {c : Nat → Nat} (h : Phases x c) {m t : Nat} (hs : InSeg c m t) :
    x t = vW m := by
  cases m with
  | zero => exact h.pre t (hs.1 rfl)
  | succ m' => obtain ⟨a, b⟩ := hs.2 m' rfl; exact h.ph m' t a b

theorem vW_succ (m : Nat) : vW (m + 1) = !vW m := by
  cases m with
  | zero => rfl
  | succ m' => show Vph (m' + 1) = !Vph m'; exact PipeTimed.Vph_succ m'

/-- A clean step signal changes only at its edges. -/
theorem change_at {x : Nat → Bool} {c : Nat → Nat} (h : Phases x c) (hc : ∀ j, c j < c (j + 1))
    {t : Nat} (hx : x (t + 1) ≠ x t) : ∃ j, c j = t + 1 := by
  have loc : ∀ t, t < c 0 ∨ ∃ j, c j ≤ t ∧ t < c (j + 1) := by
    intro t
    induction t with
    | zero =>
      by_cases h0 : 0 < c 0
      · exact Or.inl h0
      · exact Or.inr ⟨0, by omega, by have := hc 0; omega⟩
    | succ t ih =>
      rcases ih with h0 | ⟨j, h1, h2⟩
      · by_cases h' : t + 1 < c 0
        · exact Or.inl h'
        · exact Or.inr ⟨0, by omega, by have := hc 0; omega⟩
      · by_cases h' : t + 1 < c (j + 1)
        · exact Or.inr ⟨j, by omega, h'⟩
        · exact Or.inr ⟨j + 1, by omega, by have := hc (j + 1); omega⟩
  rcases loc t with h0 | ⟨j, h1, h2⟩
  · by_cases h' : t + 1 < c 0
    · exact absurd ((h.pre _ h').trans (h.pre _ h0).symm) hx
    · exact ⟨0, by omega⟩
  · by_cases h' : t + 1 < c (j + 1)
    · exact absurd ((h.ph j _ (by omega) h').trans (h.ph j _ h1 h2).symm) hx
    · exact ⟨j + 1, by omega⟩

section tick
variable {D : RingData} (C : PRing D) (T : PRingT D)
include C T

/-- **Each physical toggle is a C firing**: a node that changes at tick `t+1` is
C-excited (`Ring.excited`) in the sampled state at `t`. -/
theorem ring_tick (t i : Nat) (hi : i < D.N) (hc : D.O i (t + 1) ≠ D.O i t) :
    excited D.N (st D t) i := by
  have hx := Ring.prv_lt hi
  have hy := Ring.nxt_lt hi
  have e1 : nxt D.N (prv D.N i) = i := Ring.nxt_prv hi
  have e2 : prv D.N (nxt D.N i) = i := Ring.prv_nxt hi
  have hinc := r_inc C
  have phi := ring_nodes C T i hi
  have hOn : D.On i (t + 1) ≠ D.On i t := by
    unfold RingData.On xr; cases D.b i <;> simp_all
  obtain ⟨j, hj⟩ := change_at phi (hinc i hi) hOn
  have hl := C.H_LUT_POS i hi
  -- the stage's own value just before its edge `j`
  have vi : D.On i t = vW j := seg_val phi (by
    refine ⟨fun h => by subst h; omega, fun m' h => by subst h; have := hinc i hi m'; omega⟩)
  -- the upstream node
  have vx : D.On (prv D.N i) t = cond (D.tk i) (vW j) (!vW j) := by
    have ph := ring_nodes C T _ hx
    cases hF : D.tk i
    · rw [seg_val ph (m := j + 1) ⟨fun h => by omega, fun m' h => by
        have hm : m' = j := by omega
        subst hm
        have := t_F_f C i hi hF m'; have := t_ρ C i hi m'
        have := t_B_f C (prv D.N i) hx (by rw [e1]; exact hF) m'
        rw [e1] at this; have := t_α C _ hx (m' + 1); have := C.H_LUT_POS _ hx
        exact ⟨by omega, by omega⟩⟩, vW_succ]; rfl
    · cases j with
      | zero =>
        rw [seg_val ph (m := 0) ⟨fun _ => by
          have := t_B_t C (prv D.N i) hx (by rw [e1]; exact hF) 0
          rw [e1] at this; have := t_α C _ hx 0; omega, fun m' h => by omega⟩]; rfl
      | succ j' =>
        rw [seg_val ph (m := j' + 1) ⟨fun h => by omega, fun m' h => by
          have hm : m' = j' := by omega
          subst hm
          have := t_F_t C i hi hF m'; have := t_ρ C i hi (m' + 1)
          have := t_B_t C (prv D.N i) hx (by rw [e1]; exact hF) (m' + 1)
          rw [e1] at this; have := t_α C _ hx (m' + 1)
          exact ⟨by omega, by omega⟩⟩]; rfl
  -- the downstream node
  have vy : D.On (nxt D.N i) t = cond (D.tk (nxt D.N i)) (!vW j) (vW j) := by
    have ph := ring_nodes C T _ hy
    have hly := C.H_LUT_POS _ hy
    cases hB : D.tk (nxt D.N i)
    · cases j with
      | zero =>
        rw [seg_val ph (m := 0) ⟨fun _ => by
          have := t_F_f C (nxt D.N i) hy hB 0
          rw [e2] at this; have := t_ρ C _ hy 0; omega, fun m' h => by omega⟩]; rfl
      | succ j' =>
        rw [seg_val ph (m := j' + 1) ⟨fun h => by omega, fun m' h => by
          have hm : m' = j' := by omega
          subst hm
          have := t_B_f C i hi hB m'; have := t_α C i hi (m' + 1)
          have := t_F_f C (nxt D.N i) hy hB (m' + 1)
          rw [e2] at this; have := t_ρ C _ hy (m' + 1)
          exact ⟨by omega, by omega⟩⟩]; rfl
    · rw [seg_val ph (m := j + 1) ⟨fun h => by omega, fun m' h => by
        have hm : m' = j := by omega
        subst hm
        have := t_B_t C i hi hB m'; have := t_α C i hi m'
        have := t_F_t C (nxt D.N i) hy hB m'
        rw [e2] at this; have := t_ρ C _ hy (m' + 1)
        exact ⟨by omega, by omega⟩⟩, vW_succ]; rfl
  rw [Ring.excited_iff]
  refine ⟨hi, ?_, ?_⟩
  · simp only [st, hx, hi, ↓reduceIte]
    have ex : D.O (prv D.N i) t = (D.b (prv D.N i) != D.On (prv D.N i) t) := by
      unfold RingData.On xr; cases D.b (prv D.N i) <;> cases D.O (prv D.N i) t <;> rfl
    have ei : D.O i t = (D.b i != D.On i t) := by
      unfold RingData.On xr; cases D.b i <;> cases D.O i t <;> rfl
    rw [ex, ei, vx, vi]
    unfold RingData.tk Ring.tok
    cases D.b (prv D.N i) <;> cases D.b i <;> cases vW j <;> decide
  · simp only [st, hy, hi, ↓reduceIte]
    have ey : D.O (nxt D.N i) t = (D.b (nxt D.N i) != D.On (nxt D.N i) t) := by
      unfold RingData.On xr; cases D.b (nxt D.N i) <;> cases D.O (nxt D.N i) t <;> rfl
    have ei : D.O i t = (D.b i != D.On i t) := by
      unfold RingData.On xr; cases D.b i <;> cases D.O i t <;> rfl
    rw [ey, ei, vy, vi]
    unfold RingData.tk Ring.tok
    rw [e2]
    cases D.b (nxt D.N i) <;> cases D.b i <;> cases vW j <;> decide

end tick

/-- Firing a set of simultaneously excited stages, one after another in index order, is a
C run (C's `persistent`). -/
theorem fire_set {n : Nat} (hn : 3 ≤ n) {s0 s : Ring.State} (hr : Ring.Reach n s0 s)
    (ch : Nat → Bool) (hex : ∀ i, i < n → ch i = true → excited n s i) :
    Ring.Reach n s0 (fun i => if i < n ∧ ch i = true then !s i else s i) := by
  let sm : Nat → Ring.State := fun m i => if i < m ∧ i < n ∧ ch i = true then !s i else s i
  have key : ∀ m, Ring.Reach n s0 (sm m) ∧
      ∀ i, m ≤ i → i < n → ch i = true → excited n (sm m) i := by
    intro m
    induction m with
    | zero =>
      have e : sm 0 = s := funext fun i => by simp [sm]
      rw [e]; exact ⟨hr, fun i _ h1 h2 => hex i h1 h2⟩
    | succ m ih =>
      obtain ⟨r, x⟩ := ih
      by_cases hm : m < n ∧ ch m = true
      · have e : sm (m + 1) = Ring.fire (sm m) m := funext fun j => by
          simp only [sm, Ring.fire]
          by_cases hj : j = m
          · subst hj; simp [hm.1, hm.2]
          · have : (j < m + 1) ↔ (j < m) := by omega
            simp [hj, this]
        rw [e]
        refine ⟨Ring.Reach.step m r (x m (Nat.le_refl _) hm.1 hm.2), fun i h1 h2 h3 => ?_⟩
        exact Ring.persistent hn (x i (by omega) h2 h3) (x m (Nat.le_refl _) hm.1 hm.2)
          (by omega)
      · have e : sm (m + 1) = sm m := funext fun j => by
          simp only [sm]
          by_cases hj : j = m
          · subst hj
            have : ¬ (j < j + 1 ∧ j < n ∧ ch j = true) := fun ⟨_, a, b⟩ => hm ⟨a, b⟩
            simp only [this, ite_false]; simp
          · have : (j < m + 1) ↔ (j < m) := by omega
            simp [this]
        rw [e]; exact ⟨r, fun i h1 h2 h3 => x i (by omega) h2 h3⟩
  have e : sm n = (fun i => if i < n ∧ ch i = true then !s i else s i) := funext fun i => by
    simp only [sm]
    by_cases h : i < n <;> simp [h]
  rw [← e]; exact (key n).1

section refine
variable {D : RingData} (C : PRing D) (T : PRingT D)
include C T

/-- **Refinement onto C's `Ring`**: every sampled state of the physical ring is reachable
in C's interleaving semantics from the reset pattern `b` (each tick's toggles are C firings
of pairwise non-interfering excited stages). -/
theorem ring_reach (t : Nat) : Ring.Reach D.N D.b (st D t) := by
  have hn := (ring_cond C T).1
  induction t with
  | zero =>
    have e : st D 0 = D.b := funext fun i => by
      unfold st
      by_cases h : i < D.N
      · simp only [h, ↓reduceIte]; exact C.H_PWR i h 0 (by have := C.H_LUT_POS i h; have := r_lh C i h; omega)
      · simp only [h, ↓reduceIte]
    rw [e]; exact .refl
  | succ t ih =>
    have e : st D (t + 1) = fun i =>
        if i < D.N ∧ (D.O i (t + 1) != D.O i t) = true then !st D t i else st D t i := by
      funext i
      unfold st
      by_cases h : i < D.N
      · simp only [h, ↓reduceIte, true_and]
        cases h1 : D.O i (t + 1) <;> cases h2 : D.O i t <;> rfl
      · simp [h]
    rw [e]
    exact fire_set hn ih _ (fun i hi hc => ring_tick C T t i hi (by
      intro h; rw [h] at hc; simp at hc))

/-- C's `D_reach` on the physical ring: the wavefront count (twice the loop-token count) is
conserved at every tick. -/
theorem ring_tokens (t : Nat) : Ring.D D.N (st D t) = Ring.D D.N D.b :=
  Ring.D_reach (ring_cond C T).1 (ring_reach C T t)

/-- Every sampled state has a C-excited stage (C's `live_iff` along the refinement). -/
theorem ring_live_C (t : Nat) : ∃ i, excited D.N (st D t) i := by
  obtain ⟨h3, h0, h1⟩ := ring_cond C T
  exact Ring.live_of_D h3 (by rw [ring_tokens C T t]; exact h0) (by rw [ring_tokens C T t]; exact h1)

/-- **C's ring rule, physical** (`K` `_set` stages, `0 < K < N`, C's `resetState K`): the
hypotheses imply `N ≥ 3`, and then every node circulates forever (toggles at every
`τ i j`, strictly increasing), the ring carries one loop token (`D = 2`) at every tick. -/
theorem ring_reset_live (K : Nat) (hK0 : 0 < K) (hKn : K < D.N) (hb : D.b = Ring.resetState K) :
    3 ≤ D.N ∧ (∀ i, i < D.N → ∀ j, D.τ i j < D.τ i (j + 1) ∧ D.O i (D.τ i j) ≠ D.O i (D.τ i j - 1)) ∧
    (∀ t, Ring.D D.N (st D t) = 2) := by
  refine ⟨(ring_cond C T).1, fun i hi j => ring_toggles C T i hi j, fun t => ?_⟩
  rw [ring_tokens C T t, hb, Ring.D_reset hK0 hKn]

/-- **`t` loop tokens need `2t+1` stages, physically**: if the reset pattern carries
`D = 2t` wavefronts, the hypotheses imply `2t + 1 ≤ N`. -/
theorem ring_k_tokens (t : Nat) (ht : Ring.D D.N D.b = 2 * t) : 1 ≤ t ∧ 2 * t + 1 ≤ D.N := by
  have := ring_cond C T; omega

end refine

end Formal.Cells.RingPhys
