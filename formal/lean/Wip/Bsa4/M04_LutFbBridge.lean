-- Bsa4 mutant M04 of Formal/Cells/LutFbBridge.lean: one change, 'theorem c2w_env : EnvC (sq 4) (sq 5) rstW (sq 6) 1 2 4 ρc βc 2 2 where' -> 'theorem c2w_env : EnvC (sq 4) (sq 5) rstW (sq 6) 1 2 4 ρc βc 3 2 where'. Expected: FAIL.
import Formal.Net.OpsGen
import Formal.Cells.WinFifoCausal

/-!
# Probe Bfb (shard B): C's `LutFb` / `FbFirst` premises from B's physical cell model

C's operator bindings (`Formal/Net/OpsGen.lean`, C-8n, open item O4 / B's bridge Br1)
take, for every LUT-with-feedback node `o`, the premises

* `LutFb F p qp o` : `o` changes only to `F (p t) (qp t)`, the generated LUT's function of
  the pins and of the FEEDBACK PIN one tick earlier;
* `FbFirst qp o`   : at every change of `o`, the feedback pin already shows `o`.

No B file derived them from the physical model. This file does, for the real INITs, from
B's channel model of a feedback LUT (`WinFifo.Win` LUT channel = shard A's substrate
window channel, intrinsic H_NO_REVERT `WinFifoCausal.NoRevertI`, `CElemTiming.WinDelay`
feedback wire), C's definitions imported verbatim (not restated).

## Assumed / proved / NOT covered

**Assumed** (named; the physical ones are B's existing hypotheses):
* H_LUT_WIN, H_NO_REVERT, H_FB: the LUT output is a `Win lo hi` copy of the real-INIT
  excitation, with `NoRevertI lo hi`; the feedback wire is `WinDelay wl wh`
  (`WinFifoCausal.Stage` for the link controller, `CelC` below for `bd_c2`).
* H_LUT_POS: `1 ≤ lo` (the LUT's minimum delay is at least one tick). Needed because
  `LutFb` has the one-tick delay built in.
* H_PWR: the output's power-up value is the reset value 0 before the window channel is
  defined (`t < hi`). `Win` says nothing there, while `LutFb` speaks about every `t`.
* the four-phase environment with reset (`WinFifoCausal.Env1` for the link controller,
  `EnvC` below for a C-element: clean phases from reset release, departures measured
  from the node's own edges) and B's timing obligations `WinFifoCausal.Timing1`
  (H_RST_LONG `hi + wh ≤ R`, H_LAT `hi + wh ≤ lo + min Es Ea`, B's C2/H_ENV_LATENCY).
* For the generic theorem only: H_EX_CLEAN in phase form (`Phases`) and the phase
  spacing; the cell theorems DERIVE these.

**Proved:**
* `lutFb_of_phases`, `fbFirst_of_phases` (any LUT function `F`): a `Win` LUT with
  H_NO_REVERT whose excitation is clean in phases spaced by `hi` (and `hi + wh` against
  `lo`) yields C's `LutFb` and, with a `WinDelay` feedback wire, C's `FbFirst`.
* `link_lutFb` (bd_link controller = `bd_c2n`, INIT `0x00B200B200B200B2`): B's
  `Stage` + `Env1` + `Timing1` + H_LUT_POS + H_PWR give C's exact
  `LutFb linkF (fun t => (req t, ack t)) qp O` and `FbFirst qp O`; `link_cel_si` composes
  it with C's `link_bound` (the `Link.H_CEL_SI` field).
* `c2_lutFb` (`bd_c2`, INIT `0x00E800E800E800E8`, the C-element of `bd_fork`, `bd_join`
  N=2, bdc_muxn's `bd_c2`, `bd_arbiter`'s `ua1`/`ua2`, `bd_mux`'s `uxa`/`uya`): the same
  for any LUT function equal to `cel2`; instances `fork2_lutFb` (+ `fork2_cel_phys`, C's
  `Fork.cel` field), `join2_lutFb`, `muxn_c2_lutFb`, `arb_ack_lutFb`, `mux_ack_lutFb`.
* Non-vacuity with nonzero delays: `link_witness` (B's `Wx.witness1` run: LUT band
  `[1, 3]`, two ticks wide, where `Win` is not FIFO; wire 1; the node really toggles) and
  `c2_witness` (LUT band `[1, 2]`, wire 1, inputs offset by one tick, so the C-element
  really holds while its inputs disagree).
* Counter-runs: `no_revert_needed_lutFb` (B's one-glitch run: every hypothesis but
  H_NO_REVERT holds, and BOTH `LutFb` and `FbFirst` fail) and `env_needed_lutFb` (a fixed
  transport-delay loop, LUT delay 2, wire 1, meets every CHANNEL hypothesis (`Stage`,
  H_LUT_POS, H_PWR) with a one-tick input runt; `LutFb` fails: it is not a property of the
  cell's channels alone; an environment timing hypothesis is needed).

**NOT covered:** `bd_mux`'s `uj0`/`uj1` (5-pin LUTs with the select; the generic theorem
applies but their excitation phases are not derived), `bd_join` N=3 (`bd_c3`), C-trees,
and the `LutSI` premises (steer, src); bd_latch and bd_arbiter's `ustate` carry no
`LutFb`/`LutSI` premise in C's bindings (the latch is the `H_LATCH_*` data fields, `ustate`
is lumped into `AMerge.zr`, H_DELAY_LUMPED). The environment hypotheses (`Env1`/`EnvC`) are
not derived from the neighbouring cells here (that is the network-level induction of
`WinFifoCausal.pipe_fifo` for the pipe, not done for gcd_hw's network), and no binding
is instantiated on `CapstoneNet`.

Core Lean only (no Mathlib in the closure).
-/

namespace Formal.Cells.LutFbBridge
open Formal.Cells
open Formal.Net.Ops.Gen (LutFb FbFirst linkF c2F cel2 genF forkCell link_bound fork2_cel
  fork2_gate join2_gate c2_gate arb_gate mux_gate arbA1F arbA2F muxXaF muxYaF)
open Formal.Gen Formal.Gen.Cells
open Formal.Cells.WinFifo (Win win_le)
open Formal.Cells.WinFifoCausal (NoRevertI nt nt_lo nt_eq node_win Stage Env1 Timing1 cph)
open Formal.Cells.PipeTimed (ex Vph)

/-! ## 1. Generic: a `Win` LUT with H_NO_REVERT on a phase-clean excitation -/

/-- **H_EX_CLEAN, phase form**: the excitation `x` is 0 before `c 0` and `Vph j` on
`[c j, c (j+1))`. -/
structure Phases (x : Nat → Bool) (c : Nat → Nat) : Prop where
  pre : ∀ s, s < c 0 → x s = false
  ph : ∀ j s, c j ≤ s → s < c (j + 1) → x s = Vph j

theorem c_mono {c : Nat → Nat} {hi : Nat} (hsp : ∀ j, c j + hi ≤ c (j + 1)) :
    ∀ i j, i ≤ j → c i ≤ c j := by
  intro i j h
  induction j with
  | zero => have : i = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ j ih =>
    rcases Nat.lt_or_ge j i with h' | h'
    · have : i = j + 1 := by omega
      subst this; exact Nat.le_refl _
    · have := hsp j; have := ih h'; omega

/-- Segments of a strictly increasing sequence cover `ℕ` from `τ 0` on. -/
theorem seg_of_mono (τ : Nat → Nat) (hm : ∀ j, τ j < τ (j + 1)) :
    ∀ n, n < τ 0 ∨ ∃ j, τ j ≤ n ∧ n < τ (j + 1) := by
  have hge : ∀ j, j ≤ τ j := by
    intro j; induction j with
    | zero => exact Nat.zero_le _
    | succ j ih => have := hm j; omega
  have P : ∀ k n, n < τ k → n < τ 0 ∨ ∃ j, τ j ≤ n ∧ n < τ (j + 1) := by
    intro k
    induction k with
    | zero => intro n h; exact Or.inl h
    | succ k ih =>
      intro n h
      by_cases h' : n < τ k
      · exact ih n h'
      · exact Or.inr ⟨k, by omega, h⟩
  intro n; exact P (n + 1) n (by have := hge (n + 1); omega)

/-- The node's `j`-th edge: first instant `≥ c j + lo` showing `Vph j`. -/
def τ (O : Nat → Bool) (lo hi : Nat) (c : Nat → Nat) (j : Nat) : Nat := nt O lo hi (c j) (Vph j)

section generic
variable {x O qp : Nat → Bool} {lo hi wl wh : Nat} {c : Nat → Nat}

/-- **The node is a clean step signal** with one edge `τ j ∈ [c j + lo, c j + hi]` per
phase. -/
theorem node_steps (hW : Win lo hi x O) (hN : NoRevertI lo hi x O) (hx : Phases x c)
    (hlo : 1 ≤ lo) (hR : hi ≤ c 0) (hsp : ∀ j, c j + hi ≤ c (j + 1))
    (hP : ∀ t, t < hi → O t = false) :
    (∀ j, c j + lo ≤ τ O lo hi c j ∧ τ O lo hi c j ≤ c j + hi) ∧
    (∀ t, t < τ O lo hi c 0 → O t = false) ∧
    (∀ j t, τ O lo hi c j ≤ t → t < τ O lo hi c (j + 1) → O t = Vph j) := by
  have cm := c_mono hsp
  have nw : ∀ j, c j + lo ≤ nt O lo hi (c j) (Vph j) ∧ nt O lo hi (c j) (Vph j) ≤ c j + hi ∧
      (∀ t, nt O lo hi (c j) (Vph j) ≤ t → t < c (j + 1) + lo → O t = Vph j) ∧
      (∀ t, c j + lo ≤ t → t < nt O lo hi (c j) (Vph j) → O t = !Vph j) := fun j =>
    node_win hW hN (hx.ph j) (by have := cm 0 j (Nat.zero_le _); omega) (by have := hsp j; omega)
  refine ⟨fun j => ⟨(nw j).1, (nw j).2.1⟩, fun t ht => ?_, fun j t h1 h2 => ?_⟩
  · by_cases h0 : t < hi
    · exact hP t h0
    · by_cases h1 : t < c 0 + lo
      · obtain ⟨s, s1, s2, s3⟩ := hW t (by omega)
        rw [s3]; exact hx.pre s (by omega)
      · have := (nw 0).2.2.2 t (by omega) ht
        rw [this, PipeTimed.Vph_even 0]; rfl
  · by_cases ht : t < c (j + 1) + lo
    · exact (nw j).2.2.1 t h1 ht
    · have := (nw (j + 1)).2.2.2 t (by omega) h2
      rw [this, PipeTimed.Vph_succ, Bool.not_not]

/-- Every output change is a node edge. -/
theorem change_at (hW : Win lo hi x O) (hN : NoRevertI lo hi x O) (hx : Phases x c)
    (hlo : 1 ≤ lo) (hR : hi ≤ c 0) (hsp : ∀ j, c j + hi ≤ c (j + 1))
    (hP : ∀ t, t < hi → O t = false) :
    ∀ t, O (t + 1) ≠ O t → ∃ j, t + 1 = τ O lo hi c j := by
  obtain ⟨hb, hpre, hseg⟩ := node_steps hW hN hx hlo hR hsp hP
  have hm : ∀ j, τ O lo hi c j < τ O lo hi c (j + 1) := fun j => by
    have := (hb j).2; have := (hb (j + 1)).1; have := hsp j; omega
  intro t h
  rcases seg_of_mono _ hm (t + 1) with h0 | ⟨j, h1, h2⟩
  · exact absurd ((hpre (t + 1) h0).trans (hpre t (by omega)).symm) h
  · refine ⟨j, ?_⟩
    apply Classical.byContradiction; intro hne
    exact h ((hseg j (t + 1) h1 h2).trans (hseg j t (by omega) (by omega)).symm)

/-- **C's `LutFb` from the physical LUT** (any LUT function `F`): `Win` + H_NO_REVERT,
H_LUT_POS, H_PWR, a phase-clean excitation with phases at least `hi` long, which after
the first phase start is `F` of the pins and the feedback pin. -/
theorem lutFb_of_phases {α : Type} {F : α → Bool → Bool} {p : Nat → α}
    (hW : Win lo hi x O) (hN : NoRevertI lo hi x O) (hx : Phases x c)
    (hlo : 1 ≤ lo) (hR : hi ≤ c 0) (hsp : ∀ j, c j + hi ≤ c (j + 1))
    (hP : ∀ t, t < hi → O t = false)
    (hF : ∀ t, c 0 ≤ t → x t = F (p t) (qp t)) : LutFb F p qp O := by
  intro t h
  obtain ⟨j, hj⟩ := change_at hW hN hx hlo hR hsp hP t h
  obtain ⟨hb, _, hseg⟩ := node_steps hW hN hx hlo hR hsp hP
  have cm := c_mono hsp
  have b1 := (hb j).1; have b2 := (hb j).2; have b3 := (hb (j + 1)).1; have s1 := hsp j
  have c0 := cm 0 j (Nat.zero_le _)
  have e1 : O (t + 1) = Vph j := hseg j (t + 1) (by omega) (by omega)
  have e2 : x t = Vph j := hx.ph j t (by omega) (by omega)
  rw [e1, ← e2, hF t (by omega)]

/-- **C's `FbFirst` from the physical feedback wire**: additionally a `WinDelay wl wh`
feedback wire, and the phases spaced so that the previous node edge is more than `wh`
before the next one (`c j + hi + wh < c (j+1) + lo`, `hi + wh ≤ c 0`). -/
theorem fbFirst_of_phases (hW : Win lo hi x O) (hN : NoRevertI lo hi x O) (hx : Phases x c)
    (hlo : 1 ≤ lo) (hR : hi ≤ c 0) (hsp : ∀ j, c j + hi ≤ c (j + 1))
    (hP : ∀ t, t < hi → O t = false)
    (hFB : CElemTiming.WinDelay wl wh O qp) (hRw : hi + wh ≤ c 0)
    (hspw : ∀ j, c j + hi + wh < c (j + 1) + lo) : FbFirst qp O := by
  intro t h
  obtain ⟨j, hj⟩ := change_at hW hN hx hlo hR hsp hP t h
  obtain ⟨hb, hpre, hseg⟩ := node_steps hW hN hx hlo hR hsp hP
  have cm := c_mono hsp
  have c0 := cm 0 j (Nat.zero_le _)
  have b1 := (hb j).1
  obtain ⟨u, u1, u2, e⟩ := hFB t (by omega)
  rw [e]
  cases j with
  | zero => rw [hpre u (by omega), hpre t (by omega)]
  | succ k =>
    have := (hb k).2; have := hspw k
    rw [hseg k u (by omega) (by omega), hseg k t (by omega) (by omega)]

end generic

/-! ## 2. The link controller (`bd_c2n`) from B's `Stage` / `Env1` / `Timing1` -/

/-- C's generated `bd_link` controller LUT (`ctl.u.u`, run mode) is B's `bd_c2n`
excitation (real INIT `0x00B200B200B200B2` through `Prelim.lutB`), `rst = 0`. -/
theorem linkF_c2n : ∀ r a q : Bool,
    linkF (r, a) q = CElemTiming.exc CElemTiming.INIT_c2n r a q false := by
  decide +kernel

/-- **Bridge, link controller.** B's physical single-stage model of the `bd_link`
controller (Win LUT + H_NO_REVERT + Win feedback wire, four-phase environment with reset,
H_RST_LONG, H_LAT), plus H_LUT_POS and H_PWR, gives C's exact premises of `link_bound`. -/
theorem link_lutFb {req ack rst O qp : Nat → Bool} {lo hi wl wh R Es Ea : Nat}
    {ρ α : Nat → Nat}
    (S : Stage req ack rst O qp lo hi wl wh) (E : Env1 req ack rst O lo hi R ρ α Es Ea)
    (T : Timing1 lo hi wh R Es Ea) (H_LUT_POS : 1 ≤ lo) (H_PWR : ∀ t, t < hi → O t = false) :
    LutFb linkF (fun t => (req t, ack t)) qp O ∧ FbFirst qp O := by
  have hx : Phases (ex req ack qp rst) (cph ρ α) :=
    ⟨WinFifoCausal.s_pre S E T, WinFifoCausal.s_phase S E T⟩
  have hR := WinFifoCausal.cph_ge S E T 0
  have hgap := WinFifoCausal.s_gap S E T
  have hlat := T.H_LAT; have hrl := T.H_RST_LONG
  have hsp : ∀ j, cph ρ α j + hi ≤ cph ρ α (j + 1) := fun j => by have := hgap j; omega
  have hspw : ∀ j, cph ρ α j + hi + wh < cph ρ α (j + 1) + lo := fun j => by
    have := hgap j; omega
  refine ⟨lutFb_of_phases S.H_LUT_WIN S.H_NO_REVERT hx H_LUT_POS (by omega) hsp H_PWR
      (fun t ht => ?_),
    fbFirst_of_phases S.H_LUT_WIN S.H_NO_REVERT hx H_LUT_POS (by omega) hsp H_PWR S.H_FB
      (by omega) hspw⟩
  show CElemTiming.exc _ (req t) (ack t) (qp t) (rst t) = linkF (req t, ack t) (qp t)
  rw [WinFifoCausal.s_rst_lo S E T t (by omega), linkF_c2n]

/-- **Composed with C's `link_bound`**: the `Link.H_CEL_SI` field from the physical
model. -/
theorem link_cel_si {i o : Formal.Net.Handshake.Chan} {rst c qp : Nat → Bool}
    {lo hi wl wh R Es Ea : Nat} {ρ α : Nat → Nat}
    (S : Stage i.req o.ack rst c qp lo hi wl wh) (E : Env1 i.req o.ack rst c lo hi R ρ α Es Ea)
    (T : Timing1 lo hi wh R Es Ea) (H_LUT_POS : 1 ≤ lo) (H_PWR : ∀ t, t < hi → c t = false) :
    ∀ t, c (t + 1) ≠ c t →
      c (t + 1) = Formal.Cells.LinkHandshake.ctlB (i.req t) (o.ack t) (c t) false :=
  have h := link_lutFb S E T H_LUT_POS H_PWR
  link_bound h.1 h.2

/-! ## 3. The C-element `bd_c2` -/

/-- `bd_c2`'s real INIT is `bd_c2n`'s with the `b` pin inverted. -/
theorem c2_eq_c2n_inv (a b q r : Bool) :
    CElemTiming.exc CElemTiming.INIT_c2 a b q r = CElemTiming.exc CElemTiming.INIT_c2n a (!b) q r := by
  rw [CElemTiming.c2_eq, CElemTiming.c2n_eq]
  cases a <;> cases b <;> cases q <;> cases r <;> rfl

theorem cel2_c2n (a b q : Bool) : cel2 a b q = CElemTiming.exc CElemTiming.INIT_c2n a (!b) q false := by
  rw [CElemTiming.c2n_eq]; cases a <;> cases b <;> cases q <;> rfl

/-- The real `bd_c2` excitation (`I0 = a`, `I1 = b`, `I2 = qp`, `I3 = rst`). -/
def exC (a b qp rst : Nat → Bool) (t : Nat) : Bool :=
  CElemTiming.exc CElemTiming.INIT_c2 (a t) (b t) (qp t) (rst t)

theorem exC_eq (a b qp rst : Nat → Bool) : exC a b qp rst = ex a (fun t => !b t) qp rst :=
  funext fun _ => c2_eq_c2n_inv _ _ _ _

/-- **The gate relations of one `bd_c2` cell** (B's model; fields as `WinFifoCausal.Stage`
with the real `bd_c2` INIT). -/
structure CelC (a b rst O qp : Nat → Bool) (lo hi wl wh : Nat) : Prop where
  /-- **H_LUT_WIN**: the LUT output is a `Win lo hi` copy of the real excitation. -/
  H_LUT_WIN : Win lo hi (exC a b qp rst) O
  /-- **H_NO_REVERT** (intrinsic). -/
  H_NO_REVERT : NoRevertI lo hi (exC a b qp rst) O
  /-- **H_FB**: the feedback wire `O → I2`. -/
  H_FB : CElemTiming.WinDelay wl wh O qp
  /-- **H_LUT_POS**: the LUT's minimum delay is at least one tick. -/
  H_LUT_POS : 1 ≤ lo

/-- **The four-phase environment of a C-element**: reset high on `[0, R)`; both inputs
0 from `R` until their first rise; input `a` is `Vph j` on `[ρ j, ρ (j+1))`, input `b`
on `[β j, β (j+1))` (each input moves once per phase); each input's next edge comes
`Es` / `Ea` after the node's own edge (the node edge is read off `O`). -/
structure EnvC (a b rst O : Nat → Bool) (lo hi R : Nat) (ρ β : Nat → Nat) (Es Ea : Nat) : Prop where
  H_RST : ∀ t, rst t = decide (t < R)
  H_A0 : ∀ t, R ≤ t → t < ρ 0 → a t = false
  H_B0 : ∀ t, R ≤ t → t < β 0 → b t = false
  H_A : ∀ j t, ρ j ≤ t → t < ρ (j + 1) → a t = Vph j
  H_B : ∀ j t, β j ≤ t → t < β (j + 1) → b t = Vph j
  H_RST_EARLY : R ≤ ρ 0 ∧ R ≤ β 0
  /-- **H_SND_A**: input `a`'s next edge comes `Es` after the node's edge. -/
  H_SND : ∀ j, nt O lo hi (cph ρ β j) (Vph j) + Es ≤ ρ (j + 1)
  /-- **H_SND_B**: input `b`'s next edge comes `Ea` after the node's edge. -/
  H_RCV : ∀ j, nt O lo hi (cph ρ β j) (Vph j) + Ea ≤ β (j + 1)

section celc
variable {a b rst O qp : Nat → Bool} {lo hi wl wh R Es Ea : Nat} {ρ β : Nat → Nat}

theorem cc_ge (C : CelC a b rst O qp lo hi wl wh) (E : EnvC a b rst O lo hi R ρ β Es Ea) :
    ∀ j, R ≤ cph ρ β j := by
  have hlh := win_le C.H_LUT_WIN
  intro j
  induction j with
  | zero => have := E.H_RST_EARLY; unfold cph; omega
  | succ j ih =>
    have h1 := E.H_SND j; have h2 := nt_lo O (cph ρ β j) (Vph j) hlh (hi := hi)
    have h3 : ρ (j + 1) ≤ cph ρ β (j + 1) := Nat.le_max_left _ _
    omega

theorem cc_gap (C : CelC a b rst O qp lo hi wl wh) (E : EnvC a b rst O lo hi R ρ β Es Ea)
    (j : Nat) : cph ρ β j + lo + min Es Ea ≤ cph ρ β (j + 1) := by
  have hlh := win_le C.H_LUT_WIN
  have := E.H_SND j; have := E.H_RCV j
  have := nt_lo O (cph ρ β j) (Vph j) hlh (hi := hi)
  unfold cph at *; omega

theorem cc_pre (C : CelC a b rst O qp lo hi wl wh) (E : EnvC a b rst O lo hi R ρ β Es Ea)
    (T : Timing1 lo hi wh R Es Ea) : ∀ s, s < cph ρ β 0 → exC a b qp rst s = false := by
  have hW := C.H_LUT_WIN; have hlo := C.H_LUT_POS; have hRL := T.H_RST_LONG
  intro s
  induction s using Nat.strongRecOn with
  | _ s ih =>
    intro h
    unfold exC; rw [CElemTiming.c2_eq]
    by_cases hs : s < R
    · rw [E.H_RST s]; simp [hs]
    · obtain ⟨u, hu1, hu2, e⟩ := C.H_FB s (by omega)
      obtain ⟨s', q1, q2, q3⟩ := hW u (by omega)
      have hq : qp s = false := by rw [e, q3]; exact ih _ (by omega) (by omega)
      rw [hq]
      have hab : a s = false ∨ b s = false := by
        unfold cph at h
        rcases Nat.lt_or_ge s (ρ 0) with h' | h'
        · exact Or.inl (E.H_A0 s (by omega) h')
        · exact Or.inr (E.H_B0 s (by omega) (by omega))
      rcases hab with h' | h' <;> rw [h'] <;> cases rst s <;> cases a s <;> cases b s <;> rfl

theorem cc_phase (C : CelC a b rst O qp lo hi wl wh) (E : EnvC a b rst O lo hi R ρ β Es Ea)
    (T : Timing1 lo hi wh R Es Ea) (j : Nat) :
    ∀ s, cph ρ β j ≤ s → s < cph ρ β (j + 1) → ex a (fun t => !b t) qp rst s = Vph j := by
  have hW : Win lo hi (ex a (fun t => !b t) qp rst) O := by rw [← exC_eq]; exact C.H_LUT_WIN
  have hR := cc_ge C E j
  have hlh := win_le C.H_LUT_WIN
  have hl := nt_lo O (cph ρ β j) (Vph j) hlh (hi := hi)
  have d1 := E.H_SND j; have d2 := E.H_RCV j
  have hb := T.H_RST_LONG
  have hrst : ∀ t, max (ρ j) (β j) ≤ t → rst t = false := fun t ht => by
    rw [E.H_RST t]; unfold cph at hR; simp; omega
  exact WinFifoCausal.exc_phase_w hW C.H_FB (by have := C.H_LUT_POS; omega) (Vph j) (ρ j)
    (ρ (j + 1)) (β j) (β (j + 1)) (min Es Ea) (E.H_A j)
    (fun t h1 h2 => by show (!b t) = !Vph j; rw [E.H_B j t h1 h2])
    hrst (by unfold cph at *; omega) (by unfold cph at *; omega) T.H_LAT
    (by unfold cph at hR; omega)

/-- **Bridge, C-element.** For any LUT function `F` equal to the C-element `cel2` (the
generated `bd_c2`-type LUTs below), B's physical model of the real `bd_c2` cell in a
four-phase environment with H_RST_LONG, H_LAT and H_PWR gives C's `LutFb` and
`FbFirst`. -/
theorem c2_lutFb {F : Bool × Bool → Bool → Bool} (hFe : ∀ x y q, F (x, y) q = cel2 x y q)
    (C : CelC a b rst O qp lo hi wl wh) (E : EnvC a b rst O lo hi R ρ β Es Ea)
    (T : Timing1 lo hi wh R Es Ea) (H_PWR : ∀ t, t < hi → O t = false) :
    LutFb F (fun t => (a t, b t)) qp O ∧ FbFirst qp O := by
  have hW : Win lo hi (ex a (fun t => !b t) qp rst) O := by rw [← exC_eq]; exact C.H_LUT_WIN
  have hN : NoRevertI lo hi (ex a (fun t => !b t) qp rst) O := by
    rw [← exC_eq]; exact C.H_NO_REVERT
  have hx : Phases (ex a (fun t => !b t) qp rst) (cph ρ β) :=
    ⟨fun s h => by rw [← exC_eq]; exact cc_pre C E T s h, cc_phase C E T⟩
  have hR := cc_ge C E 0
  have hgap := cc_gap C E
  have hlat := T.H_LAT; have hrl := T.H_RST_LONG; have hlo := C.H_LUT_POS
  have hsp : ∀ j, cph ρ β j + hi ≤ cph ρ β (j + 1) := fun j => by have := hgap j; omega
  have hspw : ∀ j, cph ρ β j + hi + wh < cph ρ β (j + 1) + lo := fun j => by
    have := hgap j; omega
  refine ⟨lutFb_of_phases hW hN hx hlo (by omega) hsp H_PWR (fun t ht => ?_),
    fbFirst_of_phases hW hN hx hlo (by omega) hsp H_PWR C.H_FB (by omega) hspw⟩
  have hr : rst t = false := by rw [E.H_RST t]; simp; omega
  show CElemTiming.exc _ (a t) (!b t) (qp t) (rst t) = F (a t, b t) (qp t)
  rw [hr, hFe, cel2_c2n]

end celc

/-! ### Instances: every `bd_c2`-type LUT in C's bindings -/

theorem fork2F_cel : ∀ x y q : Bool,
    genF bd_fork_N2 forkCell .O ["ack_in[0]", "ack_in[1]", "ack", "rst"] [x, y, q, false] =
      cel2 x y q := fork2_gate
theorem join2F_cel : ∀ x y q : Bool,
    genF bd_join_N2 forkCell .O ["req_in[0]", "req_in[1]", "req", "rst"] [x, y, q, false] =
      cel2 x y q := join2_gate

section inst
variable {a b rst O qp : Nat → Bool} {lo hi wl wh R Es Ea : Nat} {ρ β : Nat → Nat}

/-- `bd_fork` N=2's acknowledge C-element (`OpsGen.fork2_cel`'s premises). -/
theorem fork2_lutFb (C : CelC a b rst O qp lo hi wl wh) (E : EnvC a b rst O lo hi R ρ β Es Ea)
    (T : Timing1 lo hi wh R Es Ea) (H_PWR : ∀ t, t < hi → O t = false) :
    LutFb (fun p q => genF bd_fork_N2 forkCell .O ["ack_in[0]", "ack_in[1]", "ack", "rst"]
      [p.1, p.2, q, false]) (fun t => (a t, b t)) qp O ∧ FbFirst qp O :=
  c2_lutFb (fun x y q => fork2F_cel x y q) C E T H_PWR

/-- `bd_join` N=2's request C-element (`OpsGen.join2_cel`'s premises). -/
theorem join2_lutFb (C : CelC a b rst O qp lo hi wl wh) (E : EnvC a b rst O lo hi R ρ β Es Ea)
    (T : Timing1 lo hi wh R Es Ea) (H_PWR : ∀ t, t < hi → O t = false) :
    LutFb (fun p q => genF bd_join_N2 forkCell .O ["req_in[0]", "req_in[1]", "req", "rst"]
      [p.1, p.2, q, false]) (fun t => (a t, b t)) qp O ∧ FbFirst qp O :=
  c2_lutFb (fun x y q => join2F_cel x y q) C E T H_PWR

/-- bdc_muxn's per-input `bd_c2` (`OpsGen.muxn_bound`'s premises, one node). -/
theorem muxn_c2_lutFb (C : CelC a b rst O qp lo hi wl wh) (E : EnvC a b rst O lo hi R ρ β Es Ea)
    (T : Timing1 lo hi wh R Es Ea) (H_PWR : ∀ t, t < hi → O t = false) :
    LutFb c2F (fun t => (a t, b t)) qp O ∧ FbFirst qp O :=
  c2_lutFb (fun x y q => c2_gate x y q) C E T H_PWR

/-- `bd_arbiter`'s acknowledge C-elements `ua1`, `ua2` (`OpsGen.amerge_ack_bound`). -/
theorem arb_ack_lutFb (C : CelC a b rst O qp lo hi wl wh) (E : EnvC a b rst O lo hi R ρ β Es Ea)
    (T : Timing1 lo hi wh R Es Ea) (H_PWR : ∀ t, t < hi → O t = false) :
    (LutFb arbA1F (fun t => (a t, b t)) qp O ∧ FbFirst qp O) ∧
    (LutFb arbA2F (fun t => (a t, b t)) qp O ∧ FbFirst qp O) :=
  ⟨c2_lutFb (fun x y q => (arb_gate x y q).1) C E T H_PWR,
   c2_lutFb (fun x y q => (arb_gate x y q).2) C E T H_PWR⟩

/-- `bd_mux`'s acknowledge C-elements `uxa`, `uya` (`OpsGen.mux_bound`'s `h2`, `h3`). -/
theorem mux_ack_lutFb (C : CelC a b rst O qp lo hi wl wh) (E : EnvC a b rst O lo hi R ρ β Es Ea)
    (T : Timing1 lo hi wh R Es Ea) (H_PWR : ∀ t, t < hi → O t = false) :
    (LutFb muxXaF (fun t => (a t, b t)) qp O ∧ FbFirst qp O) ∧
    (LutFb muxYaF (fun t => (a t, b t)) qp O ∧ FbFirst qp O) :=
  ⟨c2_lutFb (fun x y q => (mux_gate x false false false q y).2.2.1) C E T H_PWR,
   c2_lutFb (fun x y q => (mux_gate false x false false q y).2.2.2) C E T H_PWR⟩

/-- **Composed with C's `fork2_cel`**: the `Fork.cel` field of a 2-way fork from the
physical model of its `bd_c2`. -/
theorem fork2_cel_phys {f o0 o1 : Formal.Net.Handshake.Chan}
    (C : CelC o0.ack o1.ack rst f.ack qp lo hi wl wh)
    (E : EnvC o0.ack o1.ack rst f.ack lo hi R ρ β Es Ea)
    (T : Timing1 lo hi wh R Es Ea) (H_PWR : ∀ t, t < hi → f.ack t = false) :
    ∀ t, f.ack (t + 1) ≠ f.ack t → ∀ o ∈ [o0, o1], o.ack t = f.ack (t + 1) :=
  have h := fork2_lutFb C E T H_PWR
  fork2_cel h.1 h.2

end inst

/-! ## 4. Non-vacuity, with nonzero delays -/

open Formal.Cells.PipeTimed.Wit (sq sq_pre sq_phase sq_shift rstW)

/-- **Link witness**: B's `Wx.witness1` run (LUT band `[1, 3]`, two ticks wide; wire 1;
junk pins before reset release at 4) meets every hypothesis of `link_lutFb`, the node
really changes, and so (by the theorem) C's premises hold on it. -/
theorem link_witness :
    Stage WinFifoCausal.Wx.reqJ WinFifoCausal.Wx.ackJ rstW (sq 5) (sq 6) 1 3 1 1 ∧
    Env1 WinFifoCausal.Wx.reqJ WinFifoCausal.Wx.ackJ rstW (sq 5) 1 3 4
      WinFifoCausal.Wx.ρ1 WinFifoCausal.Wx.ρ1 3 3 ∧
    Timing1 1 3 1 4 3 3 ∧ 1 ≤ 1 ∧ (∀ t, t < 3 → sq 5 t = false) ∧
    1 + 2 ≤ 3 ∧ sq 5 (4 + 1) ≠ sq 5 4 ∧
    LutFb linkF (fun t => (WinFifoCausal.Wx.reqJ t, WinFifoCausal.Wx.ackJ t)) (sq 6) (sq 5) ∧
    FbFirst (sq 6) (sq 5) := by
  have S := WinFifoCausal.Wx.stage1_w
  have E := WinFifoCausal.Wx.env1_w
  have T := WinFifoCausal.Wx.timing1_w
  have hP : ∀ t, t < 3 → sq 5 t = false := fun t h => sq_pre 5 t (by omega)
  have r := link_lutFb S E T (by decide) hP
  exact ⟨S, E, T, by decide, hP, by decide, by decide, r.1, r.2⟩

/-- The `bd_c2` excitation of inputs `sq 4`, `sq 5` (b one tick late) with feedback
`sq 7` is `sq 5`. -/
theorem keyC (s : Nat) : exC (sq 4) (sq 5) (sq 7) rstW s = sq 5 s := by
  unfold exC rstW; rw [CElemTiming.c2_eq]
  by_cases h0 : s < 5
  · rw [sq_pre 5 s h0, sq_pre 7 s (by omega)]
    cases decide (s < 4) <;> cases sq 4 s <;> rfl
  · have hr : decide (s < 4) = false := by simp; omega
    rw [hr]
    have hm : (s - 5) % 8 < 8 := Nat.mod_lt _ (by omega)
    by_cases hA : (s - 5) % 8 < 4
    · have e2 : sq 5 s = true := by unfold sq; simp; omega
      by_cases h3 : (s - 5) % 8 = 3
      · have e1 : sq 4 s = false := by unfold sq; simp; omega
        have e3 : sq 7 s = true := by unfold sq; simp; omega
        rw [e1, e2, e3]; rfl
      · have e1 : sq 4 s = true := by unfold sq; simp; omega
        rw [e1, e2]; cases sq 7 s <;> rfl
    · have e2 : sq 5 s = false := by unfold sq; simp; omega
      by_cases h7 : (s - 5) % 8 = 7
      · have e1 : sq 4 s = true := by unfold sq; simp; omega
        have e3 : sq 7 s = false := by unfold sq; simp; omega
        rw [e1, e2, e3]; rfl
      · have e1 : sq 4 s = false := by unfold sq; simp; omega
        rw [e1, e2]; cases sq 7 s <;> rfl

theorem c2w_cel : CelC (sq 4) (sq 5) rstW (sq 6) (sq 7) 1 2 1 1 := by
  have hx : ∀ t, 1 ≤ t → sq 6 t = exC (sq 4) (sq 5) (sq 7) rstW (t - 1) := by
    intro t ht
    rw [keyC]
    have := sq_shift 5 1 (t - 1); rw [Nat.sub_add_cancel ht] at this; exact this
  exact { H_LUT_WIN := fun t ht => ⟨t - 1, by omega, by omega, hx t (by omega)⟩
          H_NO_REVERT := WinFifoCausal.noRevertI_shift hx
          H_FB := CElemTiming.transport_winDelay (Nat.le_refl 1) (Nat.le_refl 1)
            (fun t => by have := sq_shift 6 1 t; exact this)
          H_LUT_POS := by decide }

def ρc (j : Nat) : Nat := 4 + 4 * j
def βc (j : Nat) : Nat := 5 + 4 * j

theorem c2w_nt (j : Nat) : nt (sq 6) 1 2 (cph ρc βc j) (Vph j) = 6 + 4 * j := by
  have hc : cph ρc βc j = 5 + 4 * j := by unfold cph ρc βc; omega
  rw [hc, nt_eq (sq 6) (by decide) (sq_phase 6 j _ (by omega) (by omega))]; omega

theorem c2w_env : EnvC (sq 4) (sq 5) rstW (sq 6) 1 2 4 ρc βc 3 2 where
  H_RST _ := rfl
  H_A0 t h1 h2 := by simp only [ρc] at h2; omega
  H_B0 t h1 h2 := sq_pre 5 t (by simp only [βc] at h2; omega)
  H_A j t h1 h2 := sq_phase 4 j t h1 (by simp only [ρc] at h2; omega)
  H_B j t h1 h2 := sq_phase 5 j t h1 (by simp only [βc] at h2; omega)
  H_RST_EARLY := by simp only [ρc, βc]; omega
  H_SND j := by rw [c2w_nt]; simp only [ρc]; omega
  H_RCV j := by rw [c2w_nt]; simp only [βc]; omega

/-- **C-element witness**: the real `bd_c2` loop, LUT band `[1, 2]`, wire 1, inputs
`a = sq 4`, `b = sq 5` (so on `[4, 5)` and `[8, 9)` the inputs disagree and the cell
holds through its feedback), reset until 4: every hypothesis of `c2_lutFb` holds, the
node changes, and C's premises for the fork C-element hold. -/
theorem c2_witness :
    CelC (sq 4) (sq 5) rstW (sq 6) (sq 7) 1 2 1 1 ∧
    EnvC (sq 4) (sq 5) rstW (sq 6) 1 2 4 ρc βc 2 2 ∧ Timing1 1 2 1 4 2 2 ∧
    (∀ t, t < 2 → sq 6 t = false) ∧ sq 4 4 ≠ sq 5 4 ∧ sq 6 (5 + 1) ≠ sq 6 5 ∧
    LutFb (fun p q => genF bd_fork_N2 forkCell .O ["ack_in[0]", "ack_in[1]", "ack", "rst"]
      [p.1, p.2, q, false]) (fun t => (sq 4 t, sq 5 t)) (sq 7) (sq 6) ∧
    FbFirst (sq 7) (sq 6) := by
  have T : Timing1 1 2 1 4 2 2 := ⟨by decide, by decide, by decide⟩
  have hP : ∀ t, t < 2 → sq 6 t = false := fun t h => sq_pre 6 t (by omega)
  have r := fork2_lutFb c2w_cel c2w_env T hP
  exact ⟨c2w_cel, c2w_env, T, hP, by decide, by decide, r.1, r.2⟩

/-! ## 5. Counter-runs -/

/-- **H_NO_REVERT cannot be dropped.** B's one-glitch run (`Wx.no_revert_needed`: the
node drops for one tick at 6 inside its first uncertainty zone): `Win` LUT, `WinDelay`
wire, `Env1`, `Timing1`, H_LUT_POS and H_PWR all hold, and BOTH of C's premises fail. -/
theorem no_revert_needed_lutFb :
    Win 1 3 (ex (sq 4) (sq 8) WinFifoCausal.Wx.qg rstW) WinFifoCausal.Wx.Og ∧
    CElemTiming.WinDelay 1 1 WinFifoCausal.Wx.Og WinFifoCausal.Wx.qg ∧
    Env1 (sq 4) (sq 8) rstW WinFifoCausal.Wx.Og 1 3 4 WinFifoCausal.Wx.ρ1 WinFifoCausal.Wx.ρ1 3 3 ∧
    Timing1 1 3 1 4 3 3 ∧ 1 ≤ 1 ∧ (∀ t, t < 3 → WinFifoCausal.Wx.Og t = false) ∧
    ¬ NoRevertI 1 3 (ex (sq 4) (sq 8) WinFifoCausal.Wx.qg rstW) WinFifoCausal.Wx.Og ∧
    ¬ LutFb linkF (fun t => (sq 4 t, sq 8 t)) WinFifoCausal.Wx.qg WinFifoCausal.Wx.Og ∧
    ¬ FbFirst WinFifoCausal.Wx.qg WinFifoCausal.Wx.Og := by
  obtain ⟨hW, hF, _, hE, hT, hN, _⟩ := WinFifoCausal.Wx.no_revert_needed
  refine ⟨hW, hF, hE, hT, by decide, fun t h => ?_, hN, fun h => ?_, fun h => ?_⟩
  · rw [WinFifoCausal.Wx.Og_eq t (by omega)]; exact sq_pre 5 t (by omega)
  · have := h 5 (by decide)
    exact absurd this (by decide +kernel)
  · have := h 6 (by decide)
    exact absurd this (by decide)

/-- The environment-free counter-run: a pulse of one tick on `req`, `ack = 0`, no reset. -/
def reqB (t : Nat) : Bool := decide (t = 5)
def OB (t : Nat) : Bool := decide (7 ≤ t ∧ t % 3 = 1)
def qB (t : Nat) : Bool := decide (8 ≤ t ∧ t % 3 = 2)

theorem exB (s : Nat) : ex reqB (fun _ => false) qB (fun _ => false) s = (reqB s || qB s) := by
  unfold ex; rw [CElemTiming.c2n_eq]; cases reqB s <;> cases qB s <;> rfl

theorem OB_shift (t : Nat) (ht : 2 ≤ t) : OB t = ex reqB (fun _ => false) qB (fun _ => false) (t - 2) := by
  rw [exB]; unfold OB reqB qB
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · intro h; omega
  · intro h; omega

/-- **An environment hypothesis is needed.** The real `bd_c2n` link-controller loop with
a FIXED transport LUT delay 2 (so `Win 2 2` and `NoRevertI`, by `noRevertI_shift`) and a
1-tick feedback wire meets every channel hypothesis (`Stage`), H_LUT_POS and H_PWR; the
request is a 1-tick runt (shorter than the LUT delay: the environment withdraws the
request before the node answers, which `Env1`'s H_SND forbids). The node rises at 7
while the pins at 6 already say 0: C's `LutFb` fails (the runt then circulates in the
loop, as in `CElemTiming.runt_oscillates`). -/
theorem env_needed_lutFb :
    Stage reqB (fun _ => false) (fun _ => false) OB qB 2 2 1 1 ∧ 1 ≤ 2 ∧
    (∀ t, t < 2 → OB t = false) ∧
    ¬ LutFb linkF (fun t => (reqB t, false)) qB OB := by
  have hx : ∀ t, 2 ≤ t → OB t = ex reqB (fun _ => false) qB (fun _ => false) (t - 2) := OB_shift
  refine ⟨{ H_LUT_WIN := fun t ht => ⟨t - 2, by omega, by omega, hx t ht⟩
            H_NO_REVERT := WinFifoCausal.noRevertI_shift hx
            H_FB := CElemTiming.transport_winDelay (Nat.le_refl 1) (Nat.le_refl 1) (fun t => by
              unfold OB qB
              apply Bool.eq_iff_iff.mpr
              simp only [decide_eq_true_eq]
              constructor
              · intro h; omega
              · intro h; omega)
            H_LOOP_POS := by decide }, by decide, fun t h => ?_, fun h => ?_⟩
  · unfold OB; simp; omega
  · have := h 6 (by decide)
    exact absurd this (by decide +kernel)

end Formal.Cells.LutFbBridge
