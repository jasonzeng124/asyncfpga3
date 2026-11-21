import Formal.Cells.LutFbBridge

/-!
# Probe Bfb2 (shard B): the `LutFb`/`LutSI` bridge for the remaining cells of C's bindings

Probe Bfb (`LutFbBridge`) derived C's `LutFb`/`FbFirst` premises (`OpsGen`) for `bd_c2n`
and every 2-input `bd_c2` C-element, from B's physical model: the LUT output is a `Win lo hi`
copy of the real-INIT excitation with the intrinsic H_NO_REVERT (`NoRevertI`), the feedback
wire is a `WinDelay wl wh`, in a four-phase environment. This file covers the cells it left
open: a C-element with ANY number of pins (`CelLaw`/`CelG`/`EnvG`, the generic theorem
`celG_lutFb`), whose instances are `bd_join` N=3 (`bd_c3`, a 5-pin LUT) and `bd_mux`'s
`uj0`/`uj1` (5-pin LUTs reading the select), plus C's `LutSI` premises of `bd_steer` and
`bd_src` (LUTs without feedback). The composition with the neighbouring cells is in
`LutFbBridge2Env`.

## Assumed / proved / NOT covered

**Assumed** (named; the channel ones are Bfb's, unchanged):
* H_LUT_WIN, H_NO_REVERT, H_FB, H_LUT_POS (`CelG`): the LUT output is a `Win lo hi` copy of
  the excitation `G (pins) (feedback pin) (rst)`, `NoRevertI`, feedback `WinDelay wl wh`,
  `1 ≤ lo`. `G` is the generated LUT (yosys INIT and pin map, `genF`), with its REAL `rst`
  pin; `CelLaw G` (reset forces 0; all pins `v` gives `v`; feedback `v` and SOME pin `v`
  holds `v`) is PROVED for every instance by `decide +kernel`, not assumed.
* the four-phase environment `EnvG`: reset high on `[0, R)`; pin `i` is 0 from `R` until
  `ρ i 0` and `Vph j` on `[ρ i j, ρ i (j+1))`; `c j` is the LAST arrival of phase `j`
  (`H_ARR`, `H_LAST`); every pin's next edge comes at least `E` after the node's edge
  (`H_SND`). Timing: H_RST_LONG `hi + wh ≤ R`, H_LAT `hi + wh ≤ lo + E`; H_PWR (output 0
  for `t < hi`).
* for `uj0`/`uj1` the effective second pin is the GATED request `ctl_req ∧ ¬s` (resp.
  `∧ s`); its four-phase shape is part of `EnvG` there (it is ctl_req's protocol plus
  H_SEL_STABLE, the select constant while `ctl_req` is high; `gated_phases` derives it from
  those two for a token enumeration).
* for `steer` and `src`: the excitation's phases (`Phases`, B's H_EX_CLEAN) and spacing are
  named hypotheses (a feedback-free LUT's excitation is an environment fact); for `src`,
  H_PWR_SRC: during the power-up window `t < hi` the source's output may only rise.

**Proved:**
* `celG_lutFb`: for any pin set and any `G` with `CelLaw G`, `CelG` + `EnvG` + H_RST_LONG +
  H_LAT + H_PWR give C's `LutFb (fun p q => G p q false) p qp O` and `FbFirst qp O`.
* `join3_lutFb` (`bd_join` N=3, cell `u.genblk1.genblk1.g3.u.u`, i.e. `bd_c3`): C's exact
  premises of `OpsGen.join3_cel`; `join3_cel_phys` composes it with `join3_cel`.
* `muxJ0_lutFb`, `muxJ1_lutFb` (`bd_mux` W=2 `uj0`, `uj1`, 5-pin, real `rst` pin): C's exact
  premises `h0, f0` / `h1, f1` of `OpsGen.mux_bound`.
* `lutSI_of_phases` (generic, no feedback), `steer_lutSI` (both branch LUTs O5/O6 of
  `bd_steer`'s `u`), `steer_ack_lutSI` (`uack`), `src_lutSI` (`bd_src` `u`, LUT1 `¬ack`):
  C's `LutSI` premises of `steer_bound` and `src_bound`.
* `gated_phases`: the gated request `r ∧ (s == b)` has phases, derived from `r`'s phases,
  the select constant while `r` is high, and an enumeration of the tokens steered to `b`.
* Non-vacuity with nonzero delays (LUT band `[1, 2]`, wire 1): `join3_witness` (the real
  `bd_c3` loop; pins disagree on `[4, 5)`, `[8, 9)` so the cell holds through feedback),
  `muxJ0_witness` (the real `uj0` loop).
* `steer_witness` (LUT delay 1, branch request toggles) and `src_witness` (LUT band `[1, 2]`,
  the source rises at 1, inside the power-up window, so H_PWR_SRC is used).
* Counter-run `sel_glitch_breaks_uj0`: the real `uj0` LUT with a fixed transport delay 2,
  feedback 1 (every channel hypothesis, H_LUT_POS, H_PWR), `x_req = ctl_req = 1` and a
  ONE-tick select glitch: C's `LutFb muxJ0F` fails. So H_SEL_STABLE (or C's H_SEL_PIN) is
  needed for `uj0`, not only the request protocols.

**NOT covered:** C-trees (fork/join N ≥ 4, two LUT levels: the inner node's environment is
the composition of `LutFbBridge2Env`, not done for trees); runs in which a cell handshakes
only finitely often (`EnvG`, `Phases`, Bfb's `EnvC`/`Env1` all describe an infinite
alternating run; a mux branch or steer branch that is never selected again is not covered);
the uack OR-gate's excitation phases (the mutual exclusion of the two branch acks) are
assumed, not derived. Core Lean only.
-/

namespace Formal.Cells.LutFbBridge2
open Formal.Cells
open Formal.Net.Ops.Gen (LutFb FbFirst LutSI cel2 cel3 genF join3_cel join3_gate mux_gate
  muxJ0F muxJ1F steerF steer_gate src_gate)
open Formal.Gen Formal.Gen.Cells
open Formal.Cells.WinFifo (Win win_le)
open Formal.Cells.WinFifoCausal (NoRevertI nt nt_lo nt_eq)
open Formal.Cells.PipeTimed (Vph)
open Formal.Cells.LutFbBridge (Phases lutFb_of_phases fbFirst_of_phases)

/-! ## 1. A C-element with any number of pins -/

/-- **The C-element laws** of a LUT function `G pins feedback rst` (proved per instance). -/
structure CelLaw {ι : Type} (G : (ι → Bool) → Bool → Bool → Bool) : Prop where
  rst : ∀ p q, G p q true = false
  all : ∀ p q v, (∀ i, p i = v) → G p q false = v
  hold : ∀ p v, (∃ i, p i = v) → G p v false = v

/-- **The gate relations of one C-element LUT** (B's model, as `WinFifoCausal.Stage`). -/
structure CelG {ι : Type} (G : (ι → Bool) → Bool → Bool → Bool) (p : Nat → ι → Bool)
    (rst O qp : Nat → Bool) (lo hi wl wh : Nat) : Prop where
  /-- **H_LUT_WIN** -/
  H_LUT_WIN : Win lo hi (fun t => G (p t) (qp t) (rst t)) O
  /-- **H_NO_REVERT** (intrinsic) -/
  H_NO_REVERT : NoRevertI lo hi (fun t => G (p t) (qp t) (rst t)) O
  /-- **H_FB**: the feedback wire `O → qp`. -/
  H_FB : CElemTiming.WinDelay wl wh O qp
  /-- **H_LUT_POS** -/
  H_LUT_POS : 1 ≤ lo

/-- **The four-phase environment of an `ι`-pin C-element.** `c j` is the last pin arrival
of phase `j`; departures are measured from the node's own edge `nt O lo hi (c j) (Vph j)`. -/
structure EnvG {ι : Type} (p : Nat → ι → Bool) (rst O : Nat → Bool) (lo hi R : Nat)
    (ρ : ι → Nat → Nat) (c : Nat → Nat) (E : Nat) : Prop where
  H_NE : Nonempty ι
  H_RST : ∀ t, rst t = decide (t < R)
  H_P0 : ∀ i t, R ≤ t → t < ρ i 0 → p t i = false
  H_P : ∀ i j t, ρ i j ≤ t → t < ρ i (j + 1) → p t i = Vph j
  /-- **H_ARR**: every pin has arrived by `c j`. -/
  H_ARR : ∀ i j, ρ i j ≤ c j
  /-- **H_LAST**: before `c j` some pin has not arrived. -/
  H_LAST : ∀ j s, s < c j → ∃ i, s < ρ i j
  H_RST_EARLY : R ≤ c 0
  /-- **H_SND**: each pin's next edge comes `E` after the node's edge. -/
  H_SND : ∀ i j, nt O lo hi (c j) (Vph j) + E ≤ ρ i (j + 1)

section gen
variable {ι : Type} {G : (ι → Bool) → Bool → Bool → Bool} {p : Nat → ι → Bool}
  {rst O qp : Nat → Bool} {lo hi wl wh R E : Nat} {ρ : ι → Nat → Nat} {c : Nat → Nat}

theorem g_gap (C : CelG G p rst O qp lo hi wl wh) (Ev : EnvG p rst O lo hi R ρ c E) (j : Nat) :
    c j + lo + E ≤ c (j + 1) := by
  obtain ⟨i0⟩ := Ev.H_NE
  have := Ev.H_SND i0 j; have := Ev.H_ARR i0 (j + 1)
  have := nt_lo O (c j) (Vph j) (win_le C.H_LUT_WIN) (hi := hi)
  omega

theorem g_ge (C : CelG G p rst O qp lo hi wl wh) (Ev : EnvG p rst O lo hi R ρ c E) :
    ∀ j, R ≤ c j := by
  intro j
  induction j with
  | zero => exact Ev.H_RST_EARLY
  | succ j ih => have := g_gap C Ev j; omega

/-- **H_EX_CLEAN, phase `j`** (generic C-element). -/
theorem g_phase (L : CelLaw G) (C : CelG G p rst O qp lo hi wl wh)
    (Ev : EnvG p rst O lo hi R ρ c E) (hRL : hi + wh ≤ R) (hLAT : hi + wh ≤ lo + E) (j : Nat) :
    ∀ s, c j ≤ s → s < c (j + 1) → G (p s) (qp s) (rst s) = Vph j := by
  have hR := g_ge C Ev j
  have hl := nt_lo O (c j) (Vph j) (win_le C.H_LUT_WIN) (hi := hi)
  have hlo := C.H_LUT_POS
  intro s
  induction s using Nat.strongRecOn with
  | _ s ih =>
    intro h1 h2
    have hr : rst s = false := by rw [Ev.H_RST]; simp; omega
    rw [hr]
    by_cases hd : ∀ i, s < ρ i (j + 1)
    · exact L.all _ _ _ (fun i => Ev.H_P i j s (Nat.le_trans (Ev.H_ARR i j) h1) (hd i))
    · rw [Classical.not_forall] at hd
      obtain ⟨i0, hi0⟩ := hd
      have hsnd := Ev.H_SND i0 j
      obtain ⟨u, hu1, hu2, e⟩ := C.H_FB s (by omega)
      obtain ⟨s', q1, q2, q3⟩ := C.H_LUT_WIN u (by omega)
      have hq : qp s = Vph j := by
        rw [e, q3]; exact ih s' (by omega) (by omega) (by omega)
      rw [hq]
      obtain ⟨i1, hi1⟩ := Ev.H_LAST (j + 1) s h2
      exact L.hold _ _ ⟨i1, Ev.H_P i1 j s (Nat.le_trans (Ev.H_ARR i1 j) h1) hi1⟩

/-- **Before the first phase** (generic C-element). -/
theorem g_pre (L : CelLaw G) (C : CelG G p rst O qp lo hi wl wh)
    (Ev : EnvG p rst O lo hi R ρ c E) (hRL : hi + wh ≤ R) :
    ∀ s, s < c 0 → G (p s) (qp s) (rst s) = false := by
  have hlo := C.H_LUT_POS
  intro s
  induction s using Nat.strongRecOn with
  | _ s ih =>
    intro h
    by_cases hs : s < R
    · rw [Ev.H_RST s]; simp only [hs, decide_true]; exact L.rst _ _
    · have hr : rst s = false := by rw [Ev.H_RST]; simp; omega
      obtain ⟨u, hu1, hu2, e⟩ := C.H_FB s (by omega)
      obtain ⟨s', q1, q2, q3⟩ := C.H_LUT_WIN u (by omega)
      have hq : qp s = false := by rw [e, q3]; exact ih s' (by omega) (by omega)
      rw [hr, hq]
      obtain ⟨i1, hi1⟩ := Ev.H_LAST 0 s h
      exact L.hold _ _ ⟨i1, Ev.H_P0 i1 s (by omega) hi1⟩

/-- **Bridge, generic C-element.** -/
theorem celG_lutFb (L : CelLaw G) (C : CelG G p rst O qp lo hi wl wh)
    (Ev : EnvG p rst O lo hi R ρ c E) (H_RST_LONG : hi + wh ≤ R) (H_LAT : hi + wh ≤ lo + E)
    (H_PWR : ∀ t, t < hi → O t = false) :
    LutFb (fun pv q => G pv q false) p qp O ∧ FbFirst qp O := by
  have hx : Phases (fun t => G (p t) (qp t) (rst t)) c :=
    ⟨g_pre L C Ev H_RST_LONG, g_phase L C Ev H_RST_LONG H_LAT⟩
  have hR := g_ge C Ev 0
  have hgap := g_gap C Ev
  have hlo := C.H_LUT_POS
  have hsp : ∀ j, c j + hi ≤ c (j + 1) := fun j => by have := hgap j; omega
  have hspw : ∀ j, c j + hi + wh < c (j + 1) + lo := fun j => by have := hgap j; omega
  refine ⟨lutFb_of_phases C.H_LUT_WIN C.H_NO_REVERT hx hlo (by omega) hsp H_PWR
      (fun t ht => ?_),
    fbFirst_of_phases C.H_LUT_WIN C.H_NO_REVERT hx hlo (by omega) hsp H_PWR C.H_FB
      (by omega) hspw⟩
  have hr : rst t = false := by
    have := Ev.H_RST t; rw [this]; simp; omega
  show G (p t) (qp t) (rst t) = G (p t) (qp t) false
  rw [hr]

end gen

/-! ## 2. `bd_join` N = 3 (`bd_c3`, 5-pin LUT) -/

def j3Cell := "u.genblk1.genblk1.g3.u.u"

/-- The generated `bd_c3` LUT with its REAL reset pin: `¬rst ∧ C(r0, r1, r2; q)`. -/
theorem join3_gen : ∀ r0 r1 r2 q r : Bool,
    genF bd_join_N3 j3Cell .O ["req_in[0]", "req_in[1]", "req_in[2]", "req", "rst"]
      [r0, r1, r2, q, r] = (!r && cel3 r0 r1 r2 q) := by decide +kernel

/-- The `bd_c3` LUT as a function of a 3-pin vector. -/
def G3 (pv : Fin 3 → Bool) (q r : Bool) : Bool :=
  genF bd_join_N3 j3Cell .O ["req_in[0]", "req_in[1]", "req_in[2]", "req", "rst"]
    [pv 0, pv 1, pv 2, q, r]

theorem fin3_cases (P : Fin 3 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) : ∀ i, P i := by
  intro i
  match i with
  | ⟨0, _⟩ => exact h0
  | ⟨1, _⟩ => exact h1
  | ⟨2, _⟩ => exact h2

theorem law3 : CelLaw G3 where
  rst pv q := by unfold G3; rw [join3_gen]; rfl
  all pv q v h := by
    unfold G3; rw [join3_gen, h 0, h 1, h 2]; cases v <;> rfl
  hold pv v h := by
    unfold G3; rw [join3_gen]
    obtain ⟨i, hi⟩ := h
    have : pv 0 = v ∨ pv 1 = v ∨ pv 2 = v := by
      match i, hi with
      | ⟨0, _⟩, hi => exact Or.inl hi
      | ⟨1, _⟩, hi => exact Or.inr (Or.inl hi)
      | ⟨2, _⟩, hi => exact Or.inr (Or.inr hi)
    rcases this with h | h | h <;> rw [h] <;> cases v <;> cases pv 0 <;> cases pv 1 <;>
      cases pv 2 <;> simp_all [cel3]

/-- The three request pins as a pin vector. -/
def pv3 (a b d : Nat → Bool) (t : Nat) : Fin 3 → Bool := fun i =>
  if i.val = 0 then a t else if i.val = 1 then b t else d t

/-- **Bridge, `bd_join` N = 3.** B's physical model of the real `bd_c3` cell (5-pin LUT,
real reset pin) in a four-phase environment gives C's exact premises of
`OpsGen.join3_cel`. -/
theorem join3_lutFb {a b d rst O qp : Nat → Bool} {lo hi wl wh R E : Nat}
    {ρ : Fin 3 → Nat → Nat} {c : Nat → Nat}
    (C : CelG G3 (pv3 a b d) rst O qp lo hi wl wh) (Ev : EnvG (pv3 a b d) rst O lo hi R ρ c E)
    (H_RST_LONG : hi + wh ≤ R) (H_LAT : hi + wh ≤ lo + E) (H_PWR : ∀ t, t < hi → O t = false) :
    LutFb (fun (p : Bool × Bool × Bool) q => genF bd_join_N3 j3Cell .O
      ["req_in[0]", "req_in[1]", "req_in[2]", "req", "rst"] [p.1, p.2.1, p.2.2, q, false])
      (fun t => (a t, b t, d t)) qp O ∧ FbFirst qp O := by
  have h := celG_lutFb law3 C Ev H_RST_LONG H_LAT H_PWR
  exact ⟨fun t ht => h.1 t ht, h.2⟩

/-- **Composed with C's `join3_cel`**: the `Join.cel` field of a 3-way join. -/
theorem join3_cel_phys {i0 i1 i2 o : Formal.Net.Handshake.Chan} {rst qp : Nat → Bool}
    {lo hi wl wh R E : Nat} {ρ : Fin 3 → Nat → Nat} {c : Nat → Nat}
    (C : CelG G3 (pv3 i0.req i1.req i2.req) rst o.req qp lo hi wl wh)
    (Ev : EnvG (pv3 i0.req i1.req i2.req) rst o.req lo hi R ρ c E)
    (H_RST_LONG : hi + wh ≤ R) (H_LAT : hi + wh ≤ lo + E)
    (H_PWR : ∀ t, t < hi → o.req t = false) :
    ∀ t, o.req (t + 1) ≠ o.req t → ∀ i ∈ [i0, i1, i2], i.req t = o.req (t + 1) :=
  have h := join3_lutFb C Ev H_RST_LONG H_LAT H_PWR
  join3_cel h.1 h.2

/-! ## 3. `bd_mux` W = 2: `uj0`, `uj1` (5-pin LUTs reading the select) -/

/-- The generated `uj0` with its real reset pin: `¬rst ∧ C(x_req, ctl_req ∧ ¬s; q)`. -/
theorem uj0_gen : ∀ x cr s q r : Bool,
    genF bd_mux_W2 "uj0" .O ["x_req", "ctl_req", "s", "j0", "rst"] [x, cr, s, q, r] =
      (!r && cel2 x (cr && !s) q) := by decide +kernel

theorem uj1_gen : ∀ y cr s q r : Bool,
    genF bd_mux_W2 "uj1" .O ["y_req", "ctl_req", "s", "j1", "rst"] [y, cr, s, q, r] =
      (!r && cel2 y (cr && s) q) := by decide +kernel

/-- A 2-input C-element `¬rst ∧ C(a, b; q)` on a 2-pin vector. -/
def G2 (pv : Fin 2 → Bool) (q r : Bool) : Bool := !r && cel2 (pv 0) (pv 1) q

theorem law2 : CelLaw G2 where
  rst pv q := rfl
  all pv q v h := by unfold G2; rw [h 0, h 1]; cases v <;> rfl
  hold pv v h := by
    unfold G2
    obtain ⟨i, hi⟩ := h
    have : pv 0 = v ∨ pv 1 = v := by
      match i, hi with
      | ⟨0, _⟩, hi => exact Or.inl hi
      | ⟨1, _⟩, hi => exact Or.inr hi
    rcases this with h | h <;> rw [h] <;> cases v <;> cases pv 0 <;> cases pv 1 <;>
      simp_all [cel2]

def pv2 (a b : Nat → Bool) (t : Nat) : Fin 2 → Bool := fun i => if i.val = 0 then a t else b t

/-- The gated request of `uj0` (`b = false`) / `uj1` (`b = true`): `ctl_req ∧ (s == b)`. -/
def gate (b : Bool) (cr s : Nat → Bool) (t : Nat) : Bool := cr t && (s t == b)

theorem gate_false (cr s : Nat → Bool) (t : Nat) : gate false cr s t = (cr t && !s t) := by
  unfold gate; cases s t <;> rfl
theorem gate_true (cr s : Nat → Bool) (t : Nat) : gate true cr s t = (cr t && s t) := by
  unfold gate; cases s t <;> rfl

/-- **The real 5-pin `uj0` excitation is `G2` of `(x_req, ctl_req ∧ ¬s)`.** -/
theorem uj0_exc (x cr s qp rst : Nat → Bool) :
    (fun t => genF bd_mux_W2 "uj0" .O ["x_req", "ctl_req", "s", "j0", "rst"]
      [x t, cr t, s t, qp t, rst t]) =
    (fun t => G2 (pv2 x (gate false cr s) t) (qp t) (rst t)) := by
  funext t; rw [uj0_gen]; unfold G2 pv2; simp only [gate_false]; rfl

theorem uj1_exc (y cr s qp rst : Nat → Bool) :
    (fun t => genF bd_mux_W2 "uj1" .O ["y_req", "ctl_req", "s", "j1", "rst"]
      [y t, cr t, s t, qp t, rst t]) =
    (fun t => G2 (pv2 y (gate true cr s) t) (qp t) (rst t)) := by
  funext t; rw [uj1_gen]; unfold G2 pv2; simp only [gate_true]; rfl

/-- **The physical gate relations of `uj0`/`uj1`** on the real 5-pin LUT (`nm` the cell,
`pins` its pin names). -/
structure MuxJ (nm : String) (pins : List String) (x cr s rst O qp : Nat → Bool)
    (lo hi wl wh : Nat) : Prop where
  H_LUT_WIN : Win lo hi (fun t => genF bd_mux_W2 nm .O pins [x t, cr t, s t, qp t, rst t]) O
  H_NO_REVERT : NoRevertI lo hi (fun t => genF bd_mux_W2 nm .O pins [x t, cr t, s t, qp t, rst t]) O
  H_FB : CElemTiming.WinDelay wl wh O qp
  H_LUT_POS : 1 ≤ lo

/-- **Bridge, `bd_mux` `uj0`.** The real 5-pin LUT (real `rst` pin), in a four-phase
environment of its two effective pins `x_req` and the gated request `ctl_req ∧ ¬s`, gives
C's exact premises `h0`, `f0` of `OpsGen.mux_bound` (with `s` the select pin trace; C's
H_SEL_PIN reads `s = sel (c.dat)`). -/
theorem muxJ0_lutFb {x cr s rst O qp : Nat → Bool} {lo hi wl wh R E : Nat}
    {ρ : Fin 2 → Nat → Nat} {c : Nat → Nat}
    (M : MuxJ "uj0" ["x_req", "ctl_req", "s", "j0", "rst"] x cr s rst O qp lo hi wl wh)
    (Ev : EnvG (pv2 x (gate false cr s)) rst O lo hi R ρ c E)
    (H_RST_LONG : hi + wh ≤ R) (H_LAT : hi + wh ≤ lo + E) (H_PWR : ∀ t, t < hi → O t = false) :
    LutFb muxJ0F (fun t => (x t, cr t, s t)) qp O ∧ FbFirst qp O := by
  have C : CelG G2 (pv2 x (gate false cr s)) rst O qp lo hi wl wh := by
    have h1 := M.H_LUT_WIN; have h2 := M.H_NO_REVERT
    rw [uj0_exc] at h1 h2
    exact ⟨h1, h2, M.H_FB, M.H_LUT_POS⟩
  have h := celG_lutFb law2 C Ev H_RST_LONG H_LAT H_PWR
  refine ⟨fun t ht => ?_, h.2⟩
  rw [h.1 t ht]
  show G2 _ (qp t) false = genF bd_mux_W2 "uj0" .O _ [x t, cr t, s t, qp t, false]
  rw [uj0_gen]; unfold G2 pv2; simp only [gate_false]; rfl

/-- **Bridge, `bd_mux` `uj1`.** -/
theorem muxJ1_lutFb {y cr s rst O qp : Nat → Bool} {lo hi wl wh R E : Nat}
    {ρ : Fin 2 → Nat → Nat} {c : Nat → Nat}
    (M : MuxJ "uj1" ["y_req", "ctl_req", "s", "j1", "rst"] y cr s rst O qp lo hi wl wh)
    (Ev : EnvG (pv2 y (gate true cr s)) rst O lo hi R ρ c E)
    (H_RST_LONG : hi + wh ≤ R) (H_LAT : hi + wh ≤ lo + E) (H_PWR : ∀ t, t < hi → O t = false) :
    LutFb muxJ1F (fun t => (y t, cr t, s t)) qp O ∧ FbFirst qp O := by
  have C : CelG G2 (pv2 y (gate true cr s)) rst O qp lo hi wl wh := by
    have h1 := M.H_LUT_WIN; have h2 := M.H_NO_REVERT
    rw [uj1_exc] at h1 h2
    exact ⟨h1, h2, M.H_FB, M.H_LUT_POS⟩
  have h := celG_lutFb law2 C Ev H_RST_LONG H_LAT H_PWR
  refine ⟨fun t ht => ?_, h.2⟩
  rw [h.1 t ht]
  show G2 _ (qp t) false = genF bd_mux_W2 "uj1" .O _ [y t, cr t, s t, qp t, false]
  rw [uj1_gen]; unfold G2 pv2; simp only [gate_true]; rfl

/-! ## 4. LUTs without feedback: `LutSI` (steer, src) -/

/-- **C's `LutSI` from the physical LUT** (any function `F`, no feedback): `Win` +
H_NO_REVERT, H_LUT_POS, H_PWR, an excitation clean in phases at least `hi` long. -/
theorem lutSI_of_phases {α : Type} {F : α → Bool} {p : Nat → α} {x O : Nat → Bool}
    {lo hi : Nat} {c : Nat → Nat}
    (hW : Win lo hi x O) (hN : NoRevertI lo hi x O) (hx : Phases x c)
    (hlo : 1 ≤ lo) (hR : hi ≤ c 0) (hsp : ∀ j, c j + hi ≤ c (j + 1))
    (hP : ∀ t, t < hi → O t = false) (hF : ∀ t, c 0 ≤ t → x t = F (p t)) : LutSI F p O :=
  fun t ht => lutFb_of_phases (F := fun a (_ : Bool) => F a) (p := p) (qp := fun _ => false)
    hW hN hx hlo hR hsp hP hF t ht

/-- **Bridge, `bd_steer` branch `b`** (`u`'s O5 for `b = false`, O6 for `b = true`): C's
`LutSI` premise `hL b` of `OpsGen.steer_bound`, with `s` the select pin trace (C's
H_SEL_PIN reads `s = sel (j.dat)`). The excitation's phases (`H_EX_CLEAN`) and spacing are
named hypotheses; `gated_phases` derives the phases from the request protocol and
H_SEL_STABLE. -/
theorem steer_lutSI (b : Bool) {req s O : Nat → Bool} {lo hi : Nat} {c : Nat → Nat}
    (H_LUT_WIN : Win lo hi (fun t => steerF b (req t, s t)) O)
    (H_NO_REVERT : NoRevertI lo hi (fun t => steerF b (req t, s t)) O)
    (H_LUT_POS : 1 ≤ lo) (H_PWR : ∀ t, t < hi → O t = false)
    (H_EX_CLEAN : Phases (fun t => steerF b (req t, s t)) c)
    (H_EX_LONG : hi ≤ c 0 ∧ ∀ j, c j + hi ≤ c (j + 1)) :
    LutSI (steerF b) (fun t => (req t, s t)) O :=
  lutSI_of_phases H_LUT_WIN H_NO_REVERT H_EX_CLEAN H_LUT_POS H_EX_LONG.1 H_EX_LONG.2 H_PWR
    (fun _ _ => rfl)

/-- The branch LUT is the gated request. -/
theorem steerF_gate (b : Bool) (r s : Bool) : steerF b (r, s) = (r && (s == b)) := by
  cases b
  · exact (steer_gate r s false false).1
  · exact (steer_gate r s false false).2.1

/-- **Bridge, `bd_steer` `uack`**: C's `LutSI` premise `hA` of `OpsGen.steer_bound`. The
OR's excitation phases (the two branch acks never overlap) are a named hypothesis. -/
theorem steer_ack_lutSI {a0 a1 O : Nat → Bool} {lo hi : Nat} {c : Nat → Nat}
    (H_LUT_WIN : Win lo hi (fun t => genF bd_steer "uack" .O ["ack0", "ack1"] [a0 t, a1 t]) O)
    (H_NO_REVERT : NoRevertI lo hi
      (fun t => genF bd_steer "uack" .O ["ack0", "ack1"] [a0 t, a1 t]) O)
    (H_LUT_POS : 1 ≤ lo) (H_PWR : ∀ t, t < hi → O t = false)
    (H_EX_CLEAN : Phases (fun t => genF bd_steer "uack" .O ["ack0", "ack1"] [a0 t, a1 t]) c)
    (H_EX_LONG : hi ≤ c 0 ∧ ∀ j, c j + hi ≤ c (j + 1)) :
    LutSI (fun p : Bool × Bool => genF bd_steer "uack" .O ["ack0", "ack1"] [p.1, p.2])
      (fun t => (a0 t, a1 t)) O :=
  lutSI_of_phases H_LUT_WIN H_NO_REVERT H_EX_CLEAN H_LUT_POS H_EX_LONG.1 H_EX_LONG.2 H_PWR
    (fun _ _ => rfl)

theorem ite_ff {c : Prop} [Decidable c] {a b : Bool} (h : ¬ c) : (if c then a else b) = b := by
  simp [h]
theorem ite_tt {c : Prop} [Decidable c] {a b : Bool} (h : c) : (if c then a else b) = a := by
  simp [h]

/-- **Bridge, `bd_src`** (`u` = LUT1 `¬ack`, no reset pin). The source's excitation is 1
from power-up, so Bfb's H_PWR (output 0 until `hi`) cannot hold; it is replaced by
H_PWR_SRC: during the power-up window `t < hi`, where `Win` says nothing, the output may
only rise. The consumer's acknowledge is a four-phase signal (`Phases ack α`, 0 until
`α 0 ≥ hi`) with phases at least `hi` long. Then C's `LutSI` premise of
`OpsGen.src_bound` holds. -/
theorem src_lutSI {ack O : Nat → Bool} {lo hi : Nat} {α : Nat → Nat}
    (H_LUT_WIN : Win lo hi (fun t => genF bd_src_W2 "u" .O ["ack"] [ack t]) O)
    (H_NO_REVERT : NoRevertI lo hi (fun t => genF bd_src_W2 "u" .O ["ack"] [ack t]) O)
    (H_LUT_POS : 1 ≤ lo)
    (H_ACK : Phases ack α) (H_ACK_LONG : hi ≤ α 0 ∧ ∀ j, α j + hi ≤ α (j + 1))
    (H_PWR_SRC : ∀ t, t + 1 < hi → O (t + 1) ≠ O t → O (t + 1) = true) :
    LutSI (fun a => genF bd_src_W2 "u" .O ["ack"] [a]) ack O := by
  have ex : (fun t => genF bd_src_W2 "u" .O ["ack"] [ack t]) = fun t => !ack t :=
    funext fun t => src_gate (ack t)
  rw [ex] at H_LUT_WIN H_NO_REVERT
  -- the complemented node, forced to 0 on the power-up window
  let O2 : Nat → Bool := fun t => if t < hi then false else !O t
  have hW2 : Win lo hi ack O2 := by
    intro t ht
    obtain ⟨s, s1, s2, s3⟩ := H_LUT_WIN t ht
    refine ⟨s, s1, s2, ?_⟩
    show (if t < hi then false else !O t) = ack s
    rw [ite_ff (by omega), s3, Bool.not_not]
  have hN2 : NoRevertI lo hi ack O2 := by
    intro a b v t1 t2 hab h0 h1 h12 h2 hv
    have hv' : O t1 = !v := by
      have : O2 t1 = !O t1 := ite_ff (by omega)
      rw [this] at hv; rw [← hv, Bool.not_not]
    have := H_NO_REVERT a b (!v) t1 t2 (fun s x y => by show (!ack s) = !v; rw [hab s x y]) h0 h1 h12 h2 hv'
    show (if t2 < hi then false else !O t2) = v
    rw [ite_ff (by omega), this, Bool.not_not]
  have hP2 : ∀ t, t < hi → O2 t = false := fun t h => ite_tt (by omega)
  have hL := lutSI_of_phases (F := fun a => a) (p := ack) hW2 hN2 H_ACK H_LUT_POS
    H_ACK_LONG.1 H_ACK_LONG.2 hP2 (fun _ _ => rfl)
  intro t ht
  show O (t + 1) = genF bd_src_W2 "u" .O ["ack"] [ack t]
  rw [src_gate]
  by_cases h : t < hi
  · have ha : ack t = false := H_ACK.pre t (by omega)
    rw [ha]
    by_cases h' : t + 1 < hi
    · exact H_PWR_SRC t h' ht
    · obtain ⟨s, s1, s2, s3⟩ := H_LUT_WIN (t + 1) (by omega)
      rw [s3]; show (!ack s) = !false; rw [H_ACK.pre s (by omega)]
  · have e1 : O2 (t + 1) = !O (t + 1) := ite_ff (by omega)
    have e0 : O2 t = !O t := ite_ff (by omega)
    have hne : O2 (t + 1) ≠ O2 t := by
      rw [e1, e0]; intro hc; apply ht
      cases h1 : O (t + 1) <;> cases h2 : O t <;> simp_all
    have h3 : (!O (t + 1)) = ack t := by rw [← e1]; exact hL t hne
    rw [← h3, Bool.not_not]

/-! ### The gated request's phases from the request protocol and H_SEL_STABLE -/

/-- Phase starts of the gated request: tokens `κ m` of the request, high and low edges. -/
def gc (κ γ : Nat → Nat) (j : Nat) : Nat := γ (2 * κ (j / 2) + j % 2)

theorem gc_even (κ γ : Nat → Nat) (m : Nat) : gc κ γ (2 * m) = γ (2 * κ m) := by
  unfold gc; rw [show 2 * m / 2 = m by omega, show 2 * m % 2 = 0 by omega]; rfl
theorem gc_odd (κ γ : Nat → Nat) (m : Nat) : gc κ γ (2 * m + 1) = γ (2 * κ m + 1) := by
  unfold gc; rw [show (2 * m + 1) / 2 = m by omega, show (2 * m + 1) % 2 = 1 by omega]

theorem mono_of_succ {κ : Nat → Nat} (h : ∀ m, κ m < κ (m + 1)) : ∀ i j, i ≤ j → κ i ≤ κ j :=
  LutFbBridge.c_mono (hi := 1) (fun j => h j)

/-- **The gated request `r ∧ (s == b)` is a clean four-phase signal**, derived from: `r`'s
phases (`Phases r γ`, token `k` = phases `2k`, `2k+1`), **H_SEL_STABLE** (`s` is constant
`σ k` while `r` is high in token `k`), and an enumeration `κ` (strictly increasing) of
exactly the tokens with `σ k = b`. Its phase starts are `gc κ γ`. -/
theorem gated_phases {r s : Nat → Bool} {γ : Nat → Nat} {σ : Nat → Bool} {κ : Nat → Nat}
    {b : Bool} (hr : Phases r γ) (hγ : ∀ k, γ k < γ (k + 1))
    (H_SEL_STABLE : ∀ k t, γ (2 * k) ≤ t → t < γ (2 * k + 1) → s t = σ k)
    (hκ : ∀ m, κ m < κ (m + 1)) (hκb : ∀ m, σ (κ m) = b)
    (hκall : ∀ k, σ k = b → ∃ m, κ m = k) :
    Phases (fun t => r t && (s t == b)) (gc κ γ) := by
  have km := mono_of_succ hκ
  have gm := mono_of_succ hγ
  have xoff : ∀ n t, γ n ≤ t → t < γ (n + 1) → (∀ k, n = 2 * k → σ k ≠ b) →
      (r t && (s t == b)) = false := by
    intro n t h1 h2 hn
    by_cases hp : n % 2 = 1
    · have : r t = false := by
        rw [hr.ph n t h1 h2, show n = 2 * (n / 2) + 1 by omega]; exact PipeTimed.Vph_odd _
      rw [this]; rfl
    · have hn2 : n = 2 * (n / 2) := by omega
      have hs : s t = σ (n / 2) :=
        H_SEL_STABLE (n / 2) t (by rw [← hn2]; exact h1) (by rw [← hn2]; exact h2)
      have hne := hn (n / 2) hn2
      rw [hs, beq_eq_false_iff_ne.mpr hne, Bool.and_false]
  refine ⟨fun t ht => ?_, fun j t h1 h2 => ?_⟩
  · have ht' : t < γ (2 * κ 0) := by
      have := gc_even κ γ 0; rw [Nat.mul_zero] at this; rw [← this]; exact ht
    by_cases h0 : t < γ 0
    · show (r t && (s t == b)) = false
      rw [hr.pre t h0]; rfl
    · rcases LutFbBridge.seg_of_mono γ hγ t with h | ⟨n, n1, n2⟩
      · exact absurd h h0
      · have hn : n < 2 * κ 0 := by
          apply Classical.byContradiction; intro hc
          have := gm (2 * κ 0) n (by omega); omega
        refine xoff n t n1 n2 (fun k hk hk2 => ?_)
        obtain ⟨m, hm⟩ := hκall k hk2
        have := km 0 m (Nat.zero_le _); omega
  · obtain ⟨m, rfl | rfl⟩ : ∃ m, j = 2 * m ∨ j = 2 * m + 1 := ⟨j / 2, by omega⟩
    · rw [gc_even] at h1; rw [gc_odd] at h2
      have hr1 : r t = true := by
        rw [hr.ph (2 * κ m) t h1 h2]; exact PipeTimed.Vph_even _
      have hs : s t = b := by rw [H_SEL_STABLE (κ m) t h1 h2, hκb]
      show (r t && (s t == b)) = Vph (2 * m)
      rw [hr1, hs, PipeTimed.Vph_even]; cases b <;> rfl
    · rw [gc_odd] at h1
      rw [show 2 * m + 1 + 1 = 2 * (m + 1) by omega, gc_even] at h2
      rcases LutFbBridge.seg_of_mono γ hγ t with h | ⟨n, n1, n2⟩
      · have := gm 0 (2 * κ m + 1) (Nat.zero_le _); omega
      · have hn1 : 2 * κ m + 1 ≤ n := by
          apply Classical.byContradiction; intro hc
          have := gm (n + 1) (2 * κ m + 1) (by omega); omega
        have hn2 : n < 2 * κ (m + 1) := by
          apply Classical.byContradiction; intro hc
          have := gm (2 * κ (m + 1)) n (by omega); omega
        show (r t && (s t == b)) = Vph (2 * m + 1)
        rw [PipeTimed.Vph_odd]
        refine xoff n t n1 n2 (fun k hk hk2 => ?_)
        obtain ⟨m', hm'⟩ := hκall k hk2
        rcases Nat.lt_or_ge m m' with h | h
        · have := km (m + 1) m' h; omega
        · have := km m' m h; omega

/-! ## 5. Non-vacuity, with nonzero delays -/

open Formal.Cells.PipeTimed.Wit (sq sq_pre sq_phase sq_shift rstW)

theorem cel3_aba (a b q r : Bool) :
    (!r && cel3 a b a q) = CElemTiming.exc CElemTiming.INIT_c2 a b q r := by
  rw [CElemTiming.c2_eq]; cases a <;> cases b <;> cases q <;> cases r <;> rfl

theorem cel2_c2 (a b q r : Bool) :
    (!r && cel2 a b q) = CElemTiming.exc CElemTiming.INIT_c2 a b q r := by
  rw [CElemTiming.c2_eq]; cases a <;> cases b <;> cases q <;> cases r <;> rfl

def ρ3 (i : Fin 3) (j : Nat) : Nat := if i.val = 1 then 5 + 4 * j else 4 + 4 * j
def ρ2 (i : Fin 2) (j : Nat) : Nat := if i.val = 0 then 4 + 4 * j else 5 + 4 * j
def cw (j : Nat) : Nat := 5 + 4 * j

theorem nt6 (j : Nat) : nt (sq 6) 1 2 (cw j) (Vph j) = 6 + 4 * j := by
  unfold cw; rw [nt_eq (sq 6) (by decide) (sq_phase 6 j _ (by omega) (by omega))]; omega

theorem ex3_w (s : Nat) : G3 (pv3 (sq 4) (sq 5) (sq 4) s) (sq 7 s) (rstW s) = sq 5 s := by
  unfold G3; rw [join3_gen]
  show (!rstW s && cel3 (sq 4 s) (sq 5 s) (sq 4 s) (sq 7 s)) = sq 5 s
  rw [cel3_aba]; exact LutFbBridge.keyC s

theorem cel3_w : CelG G3 (pv3 (sq 4) (sq 5) (sq 4)) rstW (sq 6) (sq 7) 1 2 1 1 := by
  have hx : ∀ t, 1 ≤ t → sq 6 t = G3 (pv3 (sq 4) (sq 5) (sq 4) (t - 1)) (sq 7 (t - 1)) (rstW (t - 1)) := by
    intro t ht
    rw [ex3_w]
    have := sq_shift 5 1 (t - 1); rw [Nat.sub_add_cancel ht] at this; exact this
  exact { H_LUT_WIN := fun t ht => ⟨t - 1, by omega, by omega, hx t (by omega)⟩
          H_NO_REVERT := WinFifoCausal.noRevertI_shift hx
          H_FB := CElemTiming.transport_winDelay (Nat.le_refl 1) (Nat.le_refl 1)
            (fun t => by have := sq_shift 6 1 t; exact this)
          H_LUT_POS := by decide }

theorem env3_w : EnvG (pv3 (sq 4) (sq 5) (sq 4)) rstW (sq 6) 1 2 4 ρ3 cw 2 where
  H_NE := ⟨0⟩
  H_RST _ := rfl
  H_P0 := fin3_cases _ (fun t h1 h2 => by simp [ρ3] at h2; omega)
    (fun t _ h2 => sq_pre 5 t (by simpa [ρ3] using h2))
    (fun t h1 h2 => by simp [ρ3] at h2; omega)
  H_P := fin3_cases _
    (fun j t h1 h2 => by simp [ρ3] at h1 h2; exact sq_phase 4 j t h1 (by omega))
    (fun j t h1 h2 => by simp [ρ3] at h1 h2; exact sq_phase 5 j t h1 (by omega))
    (fun j t h1 h2 => by simp [ρ3] at h1 h2; exact sq_phase 4 j t h1 (by omega))
  H_ARR := fin3_cases _ (fun j => by simp [ρ3, cw]) (fun j => by simp [ρ3, cw])
    (fun j => by simp [ρ3, cw])
  H_LAST j s h := ⟨1, by simp [ρ3]; simp [cw] at h; omega⟩
  H_RST_EARLY := by decide
  H_SND := fin3_cases _ (fun j => by rw [nt6]; simp [ρ3]; omega)
    (fun j => by rw [nt6]; simp [ρ3]; omega) (fun j => by rw [nt6]; simp [ρ3]; omega)

/-- **`bd_c3` witness**: the real 5-pin `bd_c3` loop (LUT band `[1, 2]`, wire 1, reset until
4), pins `sq 4`, `sq 5`, `sq 4` (they disagree on `[4, 5)`, `[8, 9)`: the cell holds through
its feedback): every hypothesis of `join3_lutFb` holds, the node toggles, and C's
`join3_cel` premises hold. -/
theorem join3_witness :
    CelG G3 (pv3 (sq 4) (sq 5) (sq 4)) rstW (sq 6) (sq 7) 1 2 1 1 ∧
    EnvG (pv3 (sq 4) (sq 5) (sq 4)) rstW (sq 6) 1 2 4 ρ3 cw 2 ∧ 2 + 1 ≤ 4 ∧ 2 + 1 ≤ 1 + 2 ∧
    (∀ t, t < 2 → sq 6 t = false) ∧ sq 4 4 ≠ sq 5 4 ∧ sq 6 (5 + 1) ≠ sq 6 5 ∧
    LutFb (fun (p : Bool × Bool × Bool) q => genF bd_join_N3 j3Cell .O
      ["req_in[0]", "req_in[1]", "req_in[2]", "req", "rst"] [p.1, p.2.1, p.2.2, q, false])
      (fun t => (sq 4 t, sq 5 t, sq 4 t)) (sq 7) (sq 6) ∧ FbFirst (sq 7) (sq 6) := by
  have hP : ∀ t, t < 2 → sq 6 t = false := fun t h => sq_pre 6 t (by omega)
  have r := join3_lutFb cel3_w env3_w (by decide) (by decide) hP
  exact ⟨cel3_w, env3_w, by decide, by decide, hP, by decide, by decide, r.1, r.2⟩

def s0 : Nat → Bool := fun _ => false

theorem exJ0_w (s : Nat) : genF bd_mux_W2 "uj0" .O ["x_req", "ctl_req", "s", "j0", "rst"]
    [sq 4 s, sq 5 s, s0 s, sq 7 s, rstW s] = sq 5 s := by
  rw [uj0_gen]; show (!rstW s && cel2 (sq 4 s) (sq 5 s && !false) (sq 7 s)) = sq 5 s
  rw [Bool.not_false, Bool.and_true, cel2_c2]; exact LutFbBridge.keyC s

theorem muxj_w : MuxJ "uj0" ["x_req", "ctl_req", "s", "j0", "rst"] (sq 4) (sq 5) s0 rstW
    (sq 6) (sq 7) 1 2 1 1 := by
  have hx : ∀ t, 1 ≤ t → sq 6 t = genF bd_mux_W2 "uj0" .O ["x_req", "ctl_req", "s", "j0", "rst"]
      [sq 4 (t - 1), sq 5 (t - 1), s0 (t - 1), sq 7 (t - 1), rstW (t - 1)] := by
    intro t ht
    rw [exJ0_w]
    have := sq_shift 5 1 (t - 1); rw [Nat.sub_add_cancel ht] at this; exact this
  exact { H_LUT_WIN := fun t ht => ⟨t - 1, by omega, by omega, hx t (by omega)⟩
          H_NO_REVERT := WinFifoCausal.noRevertI_shift hx
          H_FB := CElemTiming.transport_winDelay (Nat.le_refl 1) (Nat.le_refl 1)
            (fun t => by have := sq_shift 6 1 t; exact this)
          H_LUT_POS := by decide }

theorem gate_w (t : Nat) : gate false (sq 5) s0 t = sq 5 t := by
  unfold gate s0; cases sq 5 t <;> rfl

theorem fin2_cases (P : Fin 2 → Prop) (h0 : P 0) (h1 : P 1) : ∀ i, P i := by
  intro i
  match i with
  | ⟨0, _⟩ => exact h0
  | ⟨1, _⟩ => exact h1

theorem envj_w : EnvG (pv2 (sq 4) (gate false (sq 5) s0)) rstW (sq 6) 1 2 4 ρ2 cw 2 where
  H_NE := ⟨0⟩
  H_RST _ := rfl
  H_P0 := fin2_cases _ (fun t h1 h2 => by simp [ρ2] at h2; omega)
    (fun t _ h2 => by simp only [pv2]; simp; rw [gate_w]; exact sq_pre 5 t (by simpa [ρ2] using h2))
  H_P := fin2_cases _
    (fun j t h1 h2 => by simp [ρ2] at h1 h2; simp [pv2]; exact sq_phase 4 j t h1 (by omega))
    (fun j t h1 h2 => by
      simp [ρ2] at h1 h2; simp only [pv2]; simp; rw [gate_w]; exact sq_phase 5 j t h1 (by omega))
  H_ARR := fin2_cases _ (fun j => by simp [ρ2, cw]) (fun j => by simp [ρ2, cw])
  H_LAST j s h := ⟨1, by simp [ρ2]; simp [cw] at h; omega⟩
  H_RST_EARLY := by decide
  H_SND := fin2_cases _ (fun j => by rw [nt6]; simp [ρ2]; omega)
    (fun j => by rw [nt6]; simp [ρ2]; omega)

/-- **`uj0` witness**: the real 5-pin `uj0` loop (band `[1, 2]`, wire 1), `x_req = sq 4`,
`ctl_req = sq 5`, select 0: every hypothesis of `muxJ0_lutFb` holds, the node toggles, C's
`h0`/`f0` hold. -/
theorem muxJ0_witness :
    MuxJ "uj0" ["x_req", "ctl_req", "s", "j0", "rst"] (sq 4) (sq 5) s0 rstW (sq 6) (sq 7) 1 2 1 1 ∧
    EnvG (pv2 (sq 4) (gate false (sq 5) s0)) rstW (sq 6) 1 2 4 ρ2 cw 2 ∧
    (∀ t, t < 2 → sq 6 t = false) ∧ sq 6 (5 + 1) ≠ sq 6 5 ∧
    LutFb muxJ0F (fun t => (sq 4 t, sq 5 t, s0 t)) (sq 7) (sq 6) ∧ FbFirst (sq 7) (sq 6) := by
  have hP : ∀ t, t < 2 → sq 6 t = false := fun t h => sq_pre 6 t (by omega)
  have r := muxJ0_lutFb muxj_w envj_w (by decide) (by decide) hP
  exact ⟨muxj_w, envj_w, hP, by decide, r.1, r.2⟩

/-- **Steer witness** (branch 0, LUT delay 1): request `sq 4`, select 0; every hypothesis
of `steer_lutSI` holds and the branch request toggles. -/
theorem steer_witness :
    Win 1 1 (fun t => steerF false (sq 4 t, s0 t)) (sq 5) ∧
    NoRevertI 1 1 (fun t => steerF false (sq 4 t, s0 t)) (sq 5) ∧
    Phases (fun t => steerF false (sq 4 t, s0 t)) (fun j => 4 + 4 * j) ∧
    sq 5 (4 + 1) ≠ sq 5 4 ∧ LutSI (steerF false) (fun t => (sq 4 t, s0 t)) (sq 5) := by
  have ex : ∀ t, steerF false (sq 4 t, s0 t) = sq 4 t := fun t => by
    rw [steerF_gate]; unfold s0; cases sq 4 t <;> rfl
  have hx : ∀ t, 1 ≤ t → sq 5 t = steerF false (sq 4 (t - 1), s0 (t - 1)) := fun t ht => by
    rw [ex]; have := sq_shift 4 1 (t - 1); rw [Nat.sub_add_cancel ht] at this; exact this
  have hW : Win 1 1 (fun t => steerF false (sq 4 t, s0 t)) (sq 5) :=
    fun t ht => ⟨t - 1, by omega, by omega, hx t ht⟩
  have hN := WinFifoCausal.noRevertI_shift (hi := 1) (x := fun t => steerF false (sq 4 t, s0 t)) hx
  have hP : Phases (fun t => steerF false (sq 4 t, s0 t)) (fun j => 4 + 4 * j) :=
    ⟨fun t h => by show steerF false _ = false; rw [ex]; exact sq_pre 4 t h,
     fun j t h1 h2 => by show steerF false _ = _; rw [ex]; exact sq_phase 4 j t h1 (by omega)⟩
  exact ⟨hW, hN, hP, by decide, steer_lutSI false hW hN (Nat.le_refl 1)
    (fun t h => sq_pre 5 t (by omega)) hP ⟨by decide, fun j => by omega⟩⟩

/-- The source output of the witness: 0 at power-up, then `¬ack` one tick late. -/
def srcO (t : Nat) : Bool := decide (1 ≤ t) && !sq 7 t

/-- **Src witness** (LUT band `[1, 2]`): the consumer's acknowledge is `sq 6`; the source
rises at 1, INSIDE the power-up window `t < 2` where `Win` says nothing (so H_PWR_SRC is
used, not vacuous); every hypothesis of `src_lutSI` holds. -/
theorem src_witness :
    Win 1 2 (fun t => genF bd_src_W2 "u" .O ["ack"] [sq 6 t]) srcO ∧
    NoRevertI 1 2 (fun t => genF bd_src_W2 "u" .O ["ack"] [sq 6 t]) srcO ∧
    Phases (sq 6) (fun j => 6 + 4 * j) ∧
    (∀ t, t + 1 < 2 → srcO (t + 1) ≠ srcO t → srcO (t + 1) = true) ∧ srcO 1 ≠ srcO 0 ∧
    LutSI (fun a => genF bd_src_W2 "u" .O ["ack"] [a]) (sq 6) srcO := by
  have hx : ∀ t, 1 ≤ t → srcO t = genF bd_src_W2 "u" .O ["ack"] [sq 6 (t - 1)] := fun t ht => by
    rw [src_gate]
    have := sq_shift 6 1 (t - 1); rw [Nat.sub_add_cancel ht] at this
    show (decide (1 ≤ t) && !sq 7 t) = !sq 6 (t - 1)
    rw [decide_eq_true ht]; exact congrArg (fun b => true && !b) this
  have hW : Win 1 2 (fun t => genF bd_src_W2 "u" .O ["ack"] [sq 6 t]) srcO :=
    fun t ht => ⟨t - 1, by omega, by omega, hx t (by omega)⟩
  have hN := WinFifoCausal.noRevertI_shift (hi := 2)
    (x := fun t => genF bd_src_W2 "u" .O ["ack"] [sq 6 t]) hx
  have hP : Phases (sq 6) (fun j => 6 + 4 * j) :=
    ⟨fun t h => sq_pre 6 t h, fun j t h1 h2 => sq_phase 6 j t h1 (by omega)⟩
  have hS : ∀ t, t + 1 < 2 → srcO (t + 1) ≠ srcO t → srcO (t + 1) = true := fun t h _ => by
    have : t = 0 := by omega
    subst this; decide
  exact ⟨hW, hN, hP, hS, by decide,
    src_lutSI hW hN (Nat.le_refl 1) hP ⟨by decide, fun j => by omega⟩ hS⟩

/-! ## 6. Counter-run: a select glitch breaks `uj0` -/

/-- The select: 1 except a one-tick glitch to 0 at 5. -/
def sG (t : Nat) : Bool := decide (t ≠ 5)

theorem exG (t : Nat) : genF bd_mux_W2 "uj0" .O ["x_req", "ctl_req", "s", "j0", "rst"]
    [true, true, sG t, LutFbBridge.qB t, false] =
    PipeTimed.ex LutFbBridge.reqB (fun _ => false) LutFbBridge.qB (fun _ => false) t := by
  rw [uj0_gen, LutFbBridge.exB]
  unfold sG LutFbBridge.reqB
  by_cases h : t = 5
  · subst h; cases LutFbBridge.qB 5 <;> rfl
  · simp [h, cel2]

/-- **H_SEL_STABLE is needed for `uj0`.** The real 5-pin `uj0` LUT with a FIXED transport
delay 2 (`Win 2 2`, `NoRevertI`) and a 1-tick feedback wire (every channel hypothesis of
`MuxJ`), H_PWR, `x_req = ctl_req = 1` constant, and a select that glitches to 0 for ONE
tick at 5: the gated request is a 1-tick runt, the node rises at 7 while the pins at 6
already say "hold 0": C's `LutFb muxJ0F` fails. -/
theorem sel_glitch_breaks_uj0 :
    MuxJ "uj0" ["x_req", "ctl_req", "s", "j0", "rst"] (fun _ => true) (fun _ => true) sG
      (fun _ => false) LutFbBridge.OB LutFbBridge.qB 2 2 1 1 ∧
    (∀ t, t < 2 → LutFbBridge.OB t = false) ∧ (∀ t, t ≠ 5 → sG t = true) ∧
    ¬ LutFb muxJ0F (fun t => (true, true, sG t)) LutFbBridge.qB LutFbBridge.OB := by
  obtain ⟨S, _, hP, _⟩ := LutFbBridge.env_needed_lutFb
  have hx : ∀ t, 2 ≤ t → LutFbBridge.OB t = genF bd_mux_W2 "uj0" .O
      ["x_req", "ctl_req", "s", "j0", "rst"] [true, true, sG (t - 2), LutFbBridge.qB (t - 2), false] :=
    fun t ht => by rw [exG]; exact LutFbBridge.OB_shift t ht
  refine ⟨{ H_LUT_WIN := fun t ht => ⟨t - 2, by omega, by omega, hx t ht⟩
            H_NO_REVERT := WinFifoCausal.noRevertI_shift hx
            H_FB := S.H_FB
            H_LUT_POS := by decide }, hP, fun t h => by unfold sG; simp [h], fun h => ?_⟩
  have := h 6 (by decide)
  exact absurd this (by decide +kernel)

end Formal.Cells.LutFbBridge2
