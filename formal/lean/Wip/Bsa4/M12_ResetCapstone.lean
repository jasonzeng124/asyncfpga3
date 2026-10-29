-- Bsa4 mutant M12 of Formal/Cells/ResetCapstone.lean: one change, 'fun c => if c.val = 3 then 3257 else 65⟩' -> 'fun c => if c.val = 3 then 65 else 65⟩'. Expected: FAIL.
import Formal.Cells.ResetCapstoneGlue
import Formal.Cells.ResetCapstoneWit
import Formal.Net.CapstoneWalk
import Formal.Net.CapstoneWitness3

/-!
# Probe Brz (shard B): B's gcd_hw reset theorems connected to C's circuit capstone

C's `gcd_hw_circuit_safe3` takes `H_CELLS : ∀ o, Cell ch (srcV a b) (opAt o)`, whose `init*`
fields say: at time 0 every one of the 465 channels is idle and every internal node is 0
(`ResetCapstoneGlue.cap_idle0`). B's `gcd_reset_binary` (Rst2) says what the elaborated RTL
control network `gNet` actually shows during reset. This file connects the two.

## Results

* `rtl_env_high`, `rtl_not_idle` (**the mismatch, negative**): in every bounded GMW run of
  `gNet` with rst held, the rig token `urig.uenv1` (node 3275) and the p_end acknowledge
  `urig.upsnk.g[1]` (node 3257) are 1 at every step of `[23(D+W+1), E]` (and, by
  `gcd_reset_release`, until a frontier link moves). So under the identification "start's
  request is the net driven by node 3275" (it is: `ucond_br10_j` reads it, pin 0, as the
  start-fork branch), C's initial state does not hold at ANY shift `T0` in that window:
  `¬ ∀ o, Cell (shiftF ch T0) _ (opAt o)`. C's literal H_RESET is false for the RTL.
* `atS_of_rtl` (**B's state → C's state**): under a channel map `μ` (each channel's request
  and acknowledge read from one control node of `gNet`; `MapOK`: the nodes are control nodes
  and lie in B's `onesL` exactly for the 7 hot requests and channel 3's acknowledge), every
  RTL run is in `AtS` (C's channels: requests 1 exactly on 0..6, acknowledges 0 except
  channel 3's, which is 1 in the RTL) at the explicit time `T0 = 23(D+W+1)`. `rtl_cold_node`: every other control node (the link
  C-elements, the mux joins, the arbiter grants: the internal nodes of C's models) is 0 there.
* `gcd_hw_safe_from_reset` (**C-side, from the reset state**): from `AtS r T0`, C's gate
  models after `T0` (`CellA`, H_CELLS_AFTER), bundling after `T0` (H_BUNDLE_AFTER) and no
  new start request after `T0` (H_START_AFTER), every token `out0` latches at or after `T0`
  carries `Nat.gcd a b`, for `a, b < 2^31`. Proof: the glued family `gl r T0` (3 virtual
  C-legal ticks from C's idle state into `AtS`, then `r`) meets C's three hypotheses, and
  `gcd_hw_circuit_safe3` applies.
* `gcd_hw_safe_after_reset` (**headline**): the two composed: B's reset hypotheses
  (bounded GMW run, H_RST_HELD on `(0, E]`, H_HOLD_LONG' `23(D+W+1) ≤ E`), the channel map
  (H_MAP), and C's dynamics/bundling/start hypotheses from `T0 = 23(D+W+1)` on give gcd on
  every `out0` latch from `T0` on.
* `reset_capstone_nonvac`: all hypotheses of the headline hold jointly (D = 40, W = 1,
  E = 967, a = 12, b = 18), with B's non-degenerate witness run `wRun` and a frozen C family.
* `gcd_hw_safe_from_reset_nonvac`: the C-side theorem's hypotheses hold for C's 8t run `chW`
  seen from `T0 = 2`, and out0 latches 6 = gcd 12 18 there (a result is delivered).
* `hot_wiring`: the `gNet` pins that identify channels 0..6 and 3's acknowledge.

## What is NOT covered (open)

* The channel map itself is a hypothesis (H_MAP, `MapOK`): no table maps C's 465 channel
  names (GcdHw SSA values + link segment) to `gNet` node ids. B's census proves the only
  candidates for a 1 are `onesL` (rst, 9 arbiter priority states, 4 `bd_src`, 2 upsnk, uenv1),
  so `MapOK` amounts to: no C wire is an arbiter q or a collapsed `bd_src` request
  (C-8i's H_SOURCE_ETERNAL removed those channels), channels 0..6 are uenv1's wires, and
  channel 3's acknowledge is upsnk's output.
* H_CELLS_AFTER (C's SI gate models on the RTL from `T0` on) is assumed, not derived from
  B's GMW run: that is C's O4 refinement (H_CEL_SI needs excitation persistence). On
  `[T0, E]` every mapped wire is constant (B), so the step fields hold vacuously there.
* H_START_AFTER is C's H_START_ONCE caveat: the rig re-offers start after every result.
* The 9 source frontier links (`ulink_n36/68/94/155_*`) fill after release; in C's network
  those channels do not exist (H_SOURCE_ETERNAL). Their effect on the joins they feed is not
  modelled here.
* `gcd_hw_live_final` (liveness): its gate models `CellI` carry the same `init*` content;
  the glue was not redone for `CellI`/`BndG`/`StartEnv`.
* The joint witness's C family is frozen (nothing moves after `T0`), so the headline's
  conclusion is vacuous on it; the C side alone is witnessed with a result
  (`gcd_hw_safe_from_reset_nonvac`), but no single witness runs B's `gNet` and C's network
  together (they are different models, joined only by H_MAP at `T0`).
-/

namespace Formal.Cells.ResetCapstone
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Cells Formal.Cells.TernarySound Formal.Cells.ResetContract Formal.Cells.ResetGcd

/-! ## (2a) The mismatch: the RTL reset state is not C's idle state -/

theorem ctl3275 : gCtl 3275 = true := by decide +kernel
theorem ctl3257 : gCtl 3257 = true := by decide +kernel
theorem gR3275 : gR 3275 = true := by decide +kernel
theorem gR3257 : gR 3257 = true := by decide +kernel

/-- **The rig token is up during reset.** -/
theorem rtl_env_high {v : Nat → Nat → Bool} (Rn : Run gNet v) {D W : Nat}
    (hB : Bounded gNet v Rn D W) (E : Nat)
    (H_RST_HELD : ∀ k, 0 < k → k ≤ E → TernaryPhases.InputsIn gNet v gA k) :
    ∀ k, (maxRank + 2) * (D + W + 1) ≤ k → k ≤ E → v k 3275 = true ∧ v k 3257 = true := by
  intro k h1 h2
  rw [gcd_reset_binary Rn hB E H_RST_HELD 3275 ctl3275 k h1 h2,
    gcd_reset_binary Rn hB E H_RST_HELD 3257 ctl3257 k h1 h2, gR3275, gR3257]
  exact ⟨rfl, rfl⟩

/-- The same after release, until a frontier link controller moves. -/
theorem rtl_env_high_release {v : Nat → Nat → Bool} (Rn : Run gNet v) {D W : Nat}
    (hB : Bounded gNet v Rn D W) (E T : Nat)
    (H_RST_HELD : ∀ k, 0 < k → k ≤ E → TernaryPhases.InputsIn gNet v gA k)
    (H_HOLD_LONG : (maxRank + 2) * (D + W + 1) + W ≤ E)
    (H_FRONT_HOLD : ∀ k n, n ∈ frontierL → E ≤ k → k ≤ T → v k n = gR n) :
    ∀ k, (maxRank + 2) * (D + W + 1) ≤ k → k ≤ T → v k 3275 = true ∧ v k 3257 = true := by
  intro k h1 h2
  rw [gcd_reset_release Rn hB E T H_RST_HELD H_HOLD_LONG H_FRONT_HOLD k 3275 h1 h2 ctl3275
    (by decide), gcd_reset_release Rn hB E T H_RST_HELD H_HOLD_LONG H_FRONT_HOLD k 3257 h1 h2
    ctl3257 (by decide), gR3275, gR3257]
  exact ⟨rfl, rfl⟩

/-- The family `ch` seen from `T0` on. -/
def shiftF (ch : Fin NC → Chan) (T0 : Nat) (c : Fin NC) : Chan :=
  ⟨fun t => (ch c).req (t + T0), fun t => (ch c).ack (t + T0), fun t => (ch c).dat (t + T0)⟩

/-- **C's initial state never holds for the RTL in the reset window**: if start's request is
read from `urig.uenv1` (node 3275), no shift `T0` in `[23(D+W+1), E]` makes the RTL channels
satisfy C's H_CELLS (already `Src.iz` fails). -/
theorem rtl_not_idle {v : Nat → Nat → Bool} (Rn : Run gNet v) {D W : Nat}
    (hB : Bounded gNet v Rn D W) (E : Nat)
    (H_RST_HELD : ∀ k, 0 < k → k ≤ E → TernaryPhases.InputsIn gNet v gA k)
    (ch : Fin NC → Chan) (sv : Nat → Nat) (T0 : Nat)
    (h1 : (maxRank + 2) * (D + W + 1) ≤ T0) (h2 : T0 ≤ E)
    (H_MAP_START : (ch start).req T0 = v T0 3275) :
    ¬ ∀ o : Fin NO, Cell (shiftF ch T0) sv (opAt o) := by
  intro H
  have h0 := (cap_idle0 _ sv H start).1
  have : (ch start).req (0 + T0) = false := h0
  rw [Nat.zero_add, H_MAP_START, (rtl_env_high Rn hB E H_RST_HELD T0 h1 h2).1] at this
  exact absurd this (by decide)

/-- **Wiring evidence for the hot channels** (from `gNet`; the channel identification itself
is not mechanised): the three joins of `cond_br9/10/11` read `urig.uenv1` (node 3275) at pin 0
as their data request (C channels 1 = b, 4 = start-fork `0#1`, 5 = a-fork `1#0`); the link
controller `ulink_n1__1` reads it as its request (C channel 6 = `1#1`); the p_end sink
acknowledge `urig.upsnk` is a 2-buffer from it (C channel 3 = `0#0`); the start fork's ack
C-element `ufork0` reads that acknowledge (C channel 2's acknowledge). -/
theorem hot_wiring :
    gNode 99 = .gate I_c2 [p 3275, p 97, p 99, p 0, k0, k0] ∧
    gNode 103 = .gate I_c2 [p 3275, p 97, p 103, p 0, k0, k0] ∧
    gNode 107 = .gate I_c2 [p 3275, p 97, p 107, p 0, k0, k0] ∧
    gNode 1696 = .gate I_c2n [p 3275, p 98, p 1696, p 0, k0, k0] ∧
    gNode 3256 = .gate I_buf [p 3275] ∧ gNode 3257 = .gate I_buf [p 3256] ∧
    gNode 65 = .gate I_c2 [p 3257, p 106, p 65, p 0, k0, k0] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## (2b) From B's per-node reset values to `AtS` -/

/-- Which `gNet` node drives each C channel's request and acknowledge wire. -/
structure ChanMap where
  μR : Fin NC → Nat
  μA : Fin NC → Nat

/-- H_MAP (the decidable part): control nodes, and in B's `onesL` exactly where `AtS` puts a 1. -/
def MapOK (μ : ChanMap) : Prop :=
  ∀ c, gCtl (μ.μR c) = true ∧ μ.μR c ≠ 0 ∧ gCtl (μ.μA c) = true ∧ μ.μA c ≠ 0 ∧
    (μ.μR c ∈ onesL ↔ hot c = true) ∧ (μ.μA c ∈ onesL ↔ c.val = 3)

theorem gR_iff (n : Nat) (hc : gCtl n = true) (b : Bool) (h : n ∈ onesL ↔ b = true) : gR n = b := by
  have := gcd_reset_ones n hc
  cases hb : b <;> cases hg : gR n <;> simp_all

/-- **B's reset state, in C's channel terms**: at `T0 ∈ [23(D+W+1), E]` the RTL channels are
in `AtS`. -/
theorem atS_of_rtl {v : Nat → Nat → Bool} (Rn : Run gNet v) {D W : Nat}
    (hB : Bounded gNet v Rn D W) (E : Nat)
    (H_RST_HELD : ∀ k, 0 < k → k ≤ E → TernaryPhases.InputsIn gNet v gA k)
    (T0 : Nat) (h1 : (maxRank + 2) * (D + W + 1) ≤ T0) (h2 : T0 ≤ E)
    (r : Fin NC → Chan) (μ : ChanMap) (hμ : MapOK μ)
    (H_MAP_T0 : ∀ c, (r c).req T0 = v T0 (μ.μR c) ∧ (r c).ack T0 = v T0 (μ.μA c)) :
    AtS r T0 where
  req c := by
    obtain ⟨hc, _, _, _, hr, _⟩ := hμ c
    rw [(H_MAP_T0 c).1, gcd_reset_binary Rn hB E H_RST_HELD _ hc T0 h1 h2]
    exact gR_iff _ hc _ hr
  ack c h3 := by
    obtain ⟨_, _, hc, _, _, ha⟩ := hμ c
    rw [(H_MAP_T0 c).2, gcd_reset_binary Rn hB E H_RST_HELD _ hc T0 h1 h2]
    exact gR_iff _ hc _ (by simpa [h3] using ha)

/-- Every control node outside `onesL` (in particular every `bd_c2n` link C-element, every
`bd_mux` join and every arbiter grant: the internal nodes of C's models) is 0 at `T0`. -/
theorem rtl_cold_node {v : Nat → Nat → Bool} (Rn : Run gNet v) {D W : Nat}
    (hB : Bounded gNet v Rn D W) (E : Nat)
    (H_RST_HELD : ∀ k, 0 < k → k ≤ E → TernaryPhases.InputsIn gNet v gA k)
    (T0 : Nat) (h1 : (maxRank + 2) * (D + W + 1) ≤ T0) (h2 : T0 ≤ E)
    (n : Nat) (hc : gCtl n = true) (hn : n ∉ onesL) : v T0 n = false := by
  rw [gcd_reset_binary Rn hB E H_RST_HELD n hc T0 h1 h2]
  exact gR_iff n hc false (by simpa using hn)

/-! ## (2c) The capstone from the reset state -/

/-- H_BUNDLE from `T0` on. -/
def HeldA (c : Chan) (T0 : Nat) : Prop :=
  ∀ t, T0 ≤ t → inTx c t = true → inTx c (t + 1) = true → c.dat (t + 1) = c.dat t

section cap
variable {r : Fin NC → Chan} {T0 : Nat}

theorem glue_held (c : Fin NC) (h : HeldA (r c) T0) : Held (gl r T0 c) := by
  intro t h1 h2
  by_cases ht : t < 3
  · rw [gl_dat_pre c (by omega), gl_dat_pre c (by omega)]
  · obtain ⟨s, rfl⟩ := shift_of ht
    have i1 : inTx (gl r T0 c) (s + 3) = inTx (r c) (s + T0) := by
      unfold inTx; rw [gl_req_s, gl_ack_s]
    have i2 : inTx (gl r T0 c) (s + 3 + 1) = inTx (r c) (s + T0 + 1) := by
      unfold inTx; rw [show s + 3 + 1 = (s + 1) + 3 by omega, gl_req_s, gl_ack_s, s1]
    rw [i1] at h1; rw [i2] at h2
    rw [show s + 3 + 1 = (s + 1) + 3 by omega, gl_dat_s, gl_dat_s, s1]
    exact h (s + T0) (by omega) h1 h2

theorem cnt_le_one (f : Nat → Bool) (h : ∀ u, f u = true → u = 0) : ∀ t, cnt f t ≤ 1 := by
  have key : ∀ t, cnt f (t + 1) = if f 0 = true then 1 else 0 := by
    intro t
    induction t with
    | zero => simp [cnt]
    | succ t ih =>
      show cnt f (t + 1) + (if f (t + 1) = true then 1 else 0) = _
      have : f (t + 1) = false := by
        cases hf : f (t + 1)
        · rfl
        · exact absurd (h _ hf) (by omega)
      rw [ih, this]; simp
  intro t
  cases t with
  | zero => simp [cnt]
  | succ t => rw [key t]; split <;> omega

theorem glue_start (H : ∀ t, T0 ≤ t → riseB (r start).req t = false) :
    ∀ t, cnt (riseB (gl r T0 start).req) t ≤ 1 := by
  apply cnt_le_one
  intro u hu
  by_cases hu3 : u < 3
  · have : u = 0 ∨ u = 1 ∨ u = 2 := by omega
    rcases this with rfl | rfl | rfl
    · rfl
    · exfalso; revert hu; unfold riseB
      rw [gl_req_lt start (by decide), gl_req_lt start (by decide)]; decide
    · exfalso; revert hu; unfold riseB
      rw [gl_req_lt start (by decide), show preR start 2 = true by decide]
      intro h; simp at h
  · exfalso
    obtain ⟨s, rfl⟩ := shift_of hu3
    have := H (s + T0) (by omega)
    revert hu; unfold riseB at this ⊢
    rw [show s + 3 + 1 = (s + 1) + 3 by omega, gl_req_s, gl_req_s, s1, this]; decide

end cap

/-- **gcd_hw circuit safety from B's reset state**: started in `AtS` at `T0` and following
C's gate models (H_CELLS_AFTER), bundling (H_BUNDLE_AFTER) and no new start offer
(H_START_AFTER) from `T0` on, the network latches only `Nat.gcd a b` on `out0` at or after
`T0`. -/
theorem gcd_hw_safe_from_reset (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31)
    (r : Fin NC → Chan) (T0 : Nat) (hS : AtS r T0)
    (H_CELLS_AFTER : ∀ o : Fin NO, CellA r T0 (srcV a b) (opAt o))
    (H_BUNDLE_AFTER : ∀ c, HeldA (r c) T0)
    (H_START_AFTER : ∀ t, T0 ≤ t → riseB (r start).req t = false) :
    ∀ e, T0 ≤ e → fallB (r out0).ack e = true → (r out0).dat e = Nat.gcd a b := by
  have H := (gcd_hw_circuit_safe3 a b ha hb (gl r T0) (glue_cells _ hS H_CELLS_AFTER)
    (fun c => glue_held c (H_BUNDLE_AFTER c)) (glue_start H_START_AFTER)).1
  intro e he hf
  obtain ⟨s, rfl⟩ : ∃ s, e = s + T0 := ⟨e - T0, by omega⟩
  have hf' : fallB (gl r T0 out0).ack (s + 3) = true := by
    unfold fallB at hf ⊢
    rw [show s + 3 + 1 = (s + 1) + 3 by omega, gl_ack_s, gl_ack_s, s1]; exact hf
  have := H _ (s + 3) ⟨hf', rfl⟩
  rwa [gl_dat_s] at this

/-- The explicit reset-exit time. -/
def T0of (D W : Nat) : Nat := (maxRank + 2) * (D + W + 1)

theorem T0of_eq (D W : Nat) : T0of D W = 23 * (D + W + 1) := rfl

/-- **Headline: gcd_hw from reset.** Every bounded GMW run `v` of B's `gNet` with rst held on
`(0, E]` (H_RST_HELD), `E ≥ T0 = 23(D+W+1)` (H_HOLD_LONG'), every channel family `r` whose
wires at `T0` are read from `gNet` nodes by a map meeting `MapOK` (H_MAP), and which from
`T0` on follows C's gate models, bundling and a single start offer: every `out0` latch at or
after `T0` carries `Nat.gcd a b`. -/
theorem gcd_hw_safe_after_reset (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31)
    {v : Nat → Nat → Bool} (Rn : Run gNet v) {D W : Nat} (hB : Bounded gNet v Rn D W) (E : Nat)
    (H_RST_HELD : ∀ k, 0 < k → k ≤ E → TernaryPhases.InputsIn gNet v gA k)
    (H_HOLD_LONG' : T0of D W ≤ E)
    (r : Fin NC → Chan) (μ : ChanMap) (H_MAP : MapOK μ)
    (H_MAP_T0 : ∀ c, (r c).req (T0of D W) = v (T0of D W) (μ.μR c) ∧
      (r c).ack (T0of D W) = v (T0of D W) (μ.μA c))
    (H_CELLS_AFTER : ∀ o : Fin NO, CellA r (T0of D W) (srcV a b) (opAt o))
    (H_BUNDLE_AFTER : ∀ c, HeldA (r c) (T0of D W))
    (H_START_AFTER : ∀ t, T0of D W ≤ t → riseB (r start).req t = false) :
    ∀ e, T0of D W ≤ e → fallB (r out0).ack e = true → (r out0).dat e = Nat.gcd a b :=
  gcd_hw_safe_from_reset a b ha hb r _
    (atS_of_rtl Rn hB E H_RST_HELD _ (Nat.le_refl _) H_HOLD_LONG' r μ H_MAP H_MAP_T0)
    H_CELLS_AFTER H_BUNDLE_AFTER H_START_AFTER

/-! ## Non-vacuity -/

/-- A frozen C family in the reset state: `AtS` forever, data from a C run's time-0 data. -/
def frzC (ch : Fin NC → Chan) (c : Fin NC) : Chan :=
  ⟨fun _ => hot c, fun _ => decide (c.val = 3), fun _ => (ch c).dat 0⟩

theorem frozen_cellA (ch : Fin NC → Chan) (sv : Nat → Nat) (T0 : Nat) (k : K NC)
    (hs : Side k = true) (h : Cell ch sv k) : CellA (frzC ch) T0 sv k := by
  cases k with
  | forkG i os =>
    exact ⟨fun e => h.ne (by simp [e]), fun _ _ _ _ hm => absurd rfl hm,
      fun _ _ hm => absurd rfl hm, fun o ho _ _ => h.dat (ch o) (List.mem_map_of_mem ho) 0⟩
  | forkH i os l hh d hs' =>
    exact ⟨fun e => h.ne (by simp [e]), fun _ _ _ _ hm => absurd rfl hm,
      fun _ _ hm => absurd rfl hm, fun o ho _ _ => h.dat (ch o) (List.mem_map_of_mem ho) 0⟩
  | join ins o e js jw =>
    refine ⟨fun e' => h.ne (by simp [e']), fun _ _ hm => absurd rfl hm,
      fun _ _ _ _ hm => absurd rfl hm, fun _ _ => ?_⟩
    show (ch o).dat 0 = _
    rw [h.dat 0, List.map_map]; rfl
  | bjoin ins o ec ed =>
    refine ⟨fun e' => h.ne (by simp [e']), fun _ _ hm => absurd rfl hm,
      fun _ _ _ _ hm => absurd rfl hm, fun _ _ => ?_⟩
    show (ch o).dat 0 = _
    rw [h.dat 0, List.map_map]; rfl
  | steerC j t f =>
    exact ⟨fun _ _ _ hm => absurd rfl hm, fun _ _ hm => absurd rfl hm,
      fun b _ _ => by cases b <;> exact h.dat _ 0⟩
  | steerD j t f fd sw =>
    exact ⟨fun _ _ _ hm => absurd rfl hm, fun _ _ hm => absurd rfl hm,
      fun b _ _ => by cases b <;> exact h.dat _ 0⟩
  | mux c x y z mw =>
    obtain ⟨_, _, M⟩ := h
    exact ⟨fun _ => false, fun _ => false, fun _ _ hm => absurd rfl hm, fun _ _ hm => absurd rfl hm,
      fun _ _ hm => absurd rfl hm, fun _ _ hm => absurd rfl hm, fun _ _ hm => absurd rfl hm,
      fun _ _ hm => absurd rfl hm, fun _ _ => M.dat 0, rfl, rfl⟩
  | muxn c x0 x1 x2 z nw =>
    obtain ⟨_, M⟩ := h
    exact ⟨fun _ _ => false, fun _ _ _ _ hm => absurd rfl hm, fun _ _ hm => absurd rfl hm,
      fun _ _ _ _ hm => absurd rfl hm, fun _ _ hm => absurd rfl hm, fun _ _ hs' => M.dat 0 hs',
      fun _ _ => rfl⟩
  | amerge x y z w =>
    obtain ⟨g1, g2, M⟩ := h
    simp only [Side, Bool.and_eq_true] at hs
    refine ⟨fun _ => false, fun _ => false, fun _ _ hm => absurd rfl hm,
      fun _ _ hm => absurd rfl hm, fun _ _ => rfl, fun _ _ hm => absurd rfl hm, ?_,
      fun _ _ hm => absurd rfl hm, fun _ _ hm => absurd rfl hm, ?_, rfl, rfl⟩
    · intro _ _ h0 h1; exact absurd (h0.symm.trans h1) (by decide)
    · intro _ _
      have e := M.dat 0
      rw [M.i2, M.iy] at e
      show (ch z).dat 0 = 2 * (if (false || decide (y.val = 3)) then (ch y).dat 0 else (ch x).dat 0)
        + Ops.Mux.b2n (false || decide (y.val = 3))
      rw [show decide (y.val = 3) = false by simpa using ne3_ne hs.2]
      exact e
  | link i o =>
    exact ⟨fun _ => false, ⟨fun _ _ hm => absurd rfl hm, fun _ _ hm => absurd rfl hm,
      fun _ _ hm => absurd rfl hm, fun _ _ hc => absurd hc (by decide), fun _ _ _ => rfl, rfl⟩⟩
  | src z which d => exact ⟨fun _ _ hm => absurd rfl hm, fun _ _ => h.dat 0⟩
  | sink i => exact ⟨fun _ _ hm => absurd rfl hm⟩

/-- The witness map: hot requests from `urig.uenv1`, channel 3's acknowledge from
`urig.upsnk.g[1]`, every other wire from a cold control node (`ufork0`, node 65). -/
def μW : ChanMap := ⟨fun c => if hot c then 3275 else 65, fun c => if c.val = 3 then 65 else 65⟩

theorem μW_ok_b : (List.finRange NC).all (fun c =>
    gCtl (μW.μR c) && (μW.μR c != 0) && gCtl (μW.μA c) && (μW.μA c != 0) &&
    (onesL.contains (μW.μR c) == hot c) && (onesL.contains (μW.μA c) == decide (c.val = 3)) &&
    (gR (μW.μR c) == hot c) && (gR (μW.μA c) == decide (c.val = 3))) = true := by decide +kernel

theorem μW_facts (c : Fin NC) :
    gCtl (μW.μR c) = true ∧ μW.μR c ≠ 0 ∧ gCtl (μW.μA c) = true ∧ μW.μA c ≠ 0 ∧
    (onesL.contains (μW.μR c) = hot c) ∧ (onesL.contains (μW.μA c) = decide (c.val = 3)) ∧
    gR (μW.μR c) = hot c ∧ gR (μW.μA c) = decide (c.val = 3) := by
  have := List.all_eq_true.1 μW_ok_b c (List.mem_finRange c)
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at this
  obtain ⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩ := this
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩

theorem μW_ok : MapOK μW := by
  intro c
  obtain ⟨a1, a2, a3, a4, a5, a6, _, _⟩ := μW_facts c
  refine ⟨a1, a2, a3, a4, ?_, ?_⟩
  · rw [← List.contains_iff_mem, a5]
  · rw [← List.contains_iff_mem, a6]; simp

/-- **Joint non-vacuity of `gcd_hw_safe_after_reset`** (a = 12, b = 18): B's non-degenerate
GMW run of `gNet` (`D = 40`, `W = 1`, rst held on `(0, 967]`, `T0 = 966`), the map `μW`, and
the frozen family `frzC chW` (C's 8t run's time-0 data) meet every hypothesis. -/
theorem reset_capstone_nonvac :
    ∃ (v : Nat → Nat → Bool) (Rn : Run gNet v) (D W E : Nat) (r : Fin NC → Chan) (μ : ChanMap),
      0 < D ∧ 0 < W ∧ Bounded gNet v Rn D W ∧
      (∀ k, 0 < k → k ≤ E → TernaryPhases.InputsIn gNet v gA k) ∧ T0of D W ≤ E ∧
      MapOK μ ∧
      (∀ c, (r c).req (T0of D W) = v (T0of D W) (μ.μR c) ∧
        (r c).ack (T0of D W) = v (T0of D W) (μ.μA c)) ∧
      (∀ o : Fin NO, CellA r (T0of D W) (srcV 12 18) (opAt o)) ∧
      (∀ c, HeldA (r c) (T0of D W)) ∧
      (∀ t, T0of D W ≤ t → riseB (r start).req t = false) := by
  refine ⟨ResetCapstoneWit.wv, ResetCapstoneWit.wRun, 40, 1, 967, frzC Wit.chW, μW,
    by decide, by decide, ResetCapstoneWit.wBounded, ResetCapstoneWit.w_rst_clean, by decide,
    μW_ok, ?_, ?_, ?_, ?_⟩
  · intro c
    obtain ⟨_, a2, _, a4, _, _, a7, a8⟩ := μW_facts c
    have e : ∀ n, n ≠ 0 → ResetCapstoneWit.wv (T0of 40 1) n = gR n := by
      intro n hn
      rw [ResetCapstoneWit.wv_lt (by decide), ResetCapstoneWit.frz_gate hn]
    exact ⟨by rw [e _ a2, a7]; rfl, by rw [e _ a4, a8]; rfl⟩
  · intro o
    exact frozen_cellA _ _ _ _ (side_all o) (Wit.w_cells o)
  · intro c t _ _ _; rfl
  · intro t _; unfold riseB; cases hot start <;> rfl

/-! ## Non-vacuity of the C-side theorem with a delivered result -/

/-- Operators with an internal node in C's model. -/
def hasInt : K NC → Bool
  | .mux .. => true
  | .muxn .. => true
  | .amerge .. => true
  | .link .. => true
  | _ => false

theorem stay0 (x : Trace) (h0 : x 0 = false)
    (hs : ∀ t, t < 2 → x (t + 1) ≠ x t → x (t + 1) = false) : x 2 = false := by
  have h1 : x 1 = false := by
    by_cases hm : x (0 + 1) = x 0
    · rw [← h0]; exact hm
    · exact hs 0 (by decide) hm
  by_cases hm : x (1 + 1) = x 1
  · rw [← h1]; exact hm
  · exact hs 1 (by decide) hm

theorem ctlB_off (b c : Bool) (h : c = false) :
    Formal.Cells.LinkHandshake.ctlB false b c false = false := by
  subst h; cases b <;> decide

/-- A C run from time 0, seen from time 2: if the inputs of the operators with an internal
node have not requested at times 0 and 1, the internal nodes are still 0 at time 2, and C's
gate model restricted to `t ≥ 2` is `CellA _ 2`. -/
theorem cell_restrict2 (ch : Fin NC → Chan) (sv : Nat → Nat) (k : K NC) (h : Cell ch sv k)
    (hin : hasInt k = true → ∀ c ∈ k.insC, (ch c).req 0 = false ∧ (ch c).req 1 = false) :
    CellA ch 2 sv k := by
  cases k with
  | forkG i os => exact ⟨by simpa using h.ne, fun o ho t _ => h.wire (ch o) (List.mem_map_of_mem ho) t,
      fun t _ hm o ho => h.cel t hm (ch o) (List.mem_map_of_mem ho),
      fun o ho t _ => h.dat (ch o) (List.mem_map_of_mem ho) t⟩
  | forkH i os l hh d hs' => exact ⟨by simpa using h.ne,
      fun o ho t _ => h.wire (ch o) (List.mem_map_of_mem ho) t,
      fun t _ hm o ho => h.cel t hm (ch o) (List.mem_map_of_mem ho),
      fun o ho t _ => h.dat (ch o) (List.mem_map_of_mem ho) t⟩
  | join ins o e js jw =>
    refine ⟨by simpa using h.ne, fun t _ hm i hi => h.cel t hm (ch i) (List.mem_map_of_mem hi),
      fun i hi t _ => h.wire (ch i) (List.mem_map_of_mem hi) t, fun t _ => ?_⟩
    rw [h.dat t, List.map_map]; rfl
  | bjoin ins o ec ed =>
    refine ⟨by simpa using h.ne, fun t _ hm i hi => h.cel t hm (ch i) (List.mem_map_of_mem hi),
      fun i hi t _ => h.wire (ch i) (List.mem_map_of_mem hi) t, fun t _ => ?_⟩
    rw [h.dat t, List.map_map]; rfl
  | steerC j t f => exact ⟨fun b u _ => h.lut b u, fun u _ => h.orr u, fun b u _ => h.dat b u⟩
  | steerD j t f fd sw => exact ⟨fun b u _ => h.lut b u, fun u _ => h.orr u, fun b u _ => h.dat b u⟩
  | mux c x y z mw =>
    obtain ⟨j0, j1, M⟩ := h
    have hx := hin rfl x (by simp [K.insC])
    have hy := hin rfl y (by simp [K.insC])
    refine ⟨j0, j1, fun t _ => M.cj0 t, fun t _ => M.cj1 t, fun t _ => M.zr t, fun t _ => M.xa t,
      fun t _ => M.ya t, fun t _ => M.ca t, fun t _ => M.dat t, ?_, ?_⟩
    · apply stay0 j0 M.i0; intro t ht hm
      have e := (M.cj0 t hm).1
      cases hj : j0 (t + 1)
      · rfl
      · rw [hj] at e; have : t = 0 ∨ t = 1 := by omega
        rcases this with rfl | rfl
        · rw [hx.1] at e; exact absurd e (by decide)
        · rw [hx.2] at e; exact absurd e (by decide)
    · apply stay0 j1 M.i1; intro t ht hm
      have e := (M.cj1 t hm).1
      cases hj : j1 (t + 1)
      · rfl
      · rw [hj] at e; have : t = 0 ∨ t = 1 := by omega
        rcases this with rfl | rfl
        · rw [hy.1] at e; exact absurd e (by decide)
        · rw [hy.2] at e; exact absurd e (by decide)
  | muxn c x0 x1 x2 z nw =>
    obtain ⟨j, M⟩ := h
    refine ⟨j, fun k hk t _ => M.cj k hk t, fun t _ => M.zr t, fun k hk t _ => M.xa k hk t,
      fun t _ => M.ca t, fun t _ => M.dat t, ?_⟩
    intro k hk
    have hxk : (ch (cx3 x0 x1 x2 k)).req 0 = false ∧ (ch (cx3 x0 x1 x2 k)).req 1 = false := by
      apply hin rfl
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;> simp [K.insC, cx3]
    apply stay0 (j k) (M.ij k hk); intro t ht hm
    have e := (M.cj k hk t hm).1
    cases hj : j k (t + 1)
    · rfl
    · rw [hj] at e; have : t = 0 ∨ t = 1 := by omega
      rcases this with rfl | rfl
      · rw [hxk.1] at e; exact absurd e (by decide)
      · rw [hxk.2] at e; exact absurd e (by decide)
  | amerge x y z w =>
    obtain ⟨g1, g2, M⟩ := h
    have hx := hin rfl x (by simp [K.insC])
    have hy := hin rfl y (by simp [K.insC])
    refine ⟨g1, g2, fun t _ => M.H_ARB1 t, fun t _ => M.H_ARB2 t, fun t _ => M.H_ARB_EXCL t,
      fun t _ => M.zr t, fun t _ => M.H_AMERGE_RTZ t, fun t _ => M.xa t, fun t _ => M.ya t,
      fun t _ => M.dat t, ?_, ?_⟩
    · apply stay0 g1 M.i1; intro t ht hm
      have e := (M.H_ARB1 t hm).1
      cases hj : g1 (t + 1)
      · rfl
      · rw [hj] at e; have : t = 0 ∨ t = 1 := by omega
        rcases this with rfl | rfl
        · rw [hx.1] at e; exact absurd e (by decide)
        · rw [hx.2] at e; exact absurd e (by decide)
    · apply stay0 g2 M.i2; intro t ht hm
      have e := (M.H_ARB2 t hm).1
      cases hj : g2 (t + 1)
      · rfl
      · rw [hj] at e; have : t = 0 ∨ t = 1 := by omega
        rcases this with rfl | rfl
        · rw [hy.1] at e; exact absurd e (by decide)
        · rw [hy.2] at e; exact absurd e (by decide)
  | link i o =>
    obtain ⟨c, L⟩ := h
    have hi := hin rfl i (by simp [K.insC])
    refine ⟨c, fun t _ => L.H_CEL_SI t, fun t _ => L.H_ACK_DI t, fun t _ => L.H_REQ_DI t,
      fun t _ => L.H_LATCH_OPEN t, fun t _ => L.H_LATCH_HOLD t, ?_⟩
    apply stay0 c L.ic; intro t ht hm
    have e := L.H_CEL_SI t hm
    have : t = 0 ∨ t = 1 := by omega
    have hc0 : c t = false := by
      rcases this with rfl | rfl
      · exact L.ic
      · cases h1 : c 1
        · rfl
        · exfalso; have e0 := L.H_CEL_SI 0
          by_cases hm0 : c (0 + 1) = c 0
          · rw [L.ic] at hm0; rw [hm0] at h1; exact absurd h1 (by decide)
          · rw [e0 hm0, hi.1, L.ic, ctlB_off _ _ rfl] at h1; exact absurd h1 (by decide)
    rcases this with rfl | rfl
    · rw [e, hi.1, ctlB_off _ _ hc0]
    · rw [e, hi.2, ctlB_off _ _ hc0]
  | src z which d => exact ⟨fun t _ => h.H_LUT_SI t, fun t _ => h.dat t⟩
  | sink i => exact ⟨fun t _ => h.wire t⟩

theorem chW_atS_b : (List.finRange NC).all (fun c => ((Wit.chW c).req 2 == hot c) &&
    (decide (c.val = 3) || !(Wit.chW c).ack 2)) = true := by decide +kernel

theorem chW_atS : AtS Wit.chW 2 where
  req c := by
    have := List.all_eq_true.1 chW_atS_b c (List.mem_finRange c)
    simp only [Bool.and_eq_true, beq_iff_eq] at this; exact this.1
  ack c h3 := by
    have := List.all_eq_true.1 chW_atS_b c (List.mem_finRange c)
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, h3, false_or,
      Bool.not_eq_true'] at this
    exact this.2

theorem chW_early_b : ops.all (fun k => !hasInt k ||
    k.insC.all (fun c => !(Wit.chW c).req 0 && !(Wit.chW c).req 1)) = true := by decide +kernel

theorem chW_cellA (o : Fin NO) : CellA Wit.chW 2 (srcV 12 18) (opAt o) := by
  apply cell_restrict2 _ _ _ (Wit.w_cells o)
  intro hi c hc
  have := List.all_eq_true.1 chW_early_b (opAt o) (getD_mem (o := o))
  rw [hi] at this
  simp only [Bool.not_true, Bool.false_or] at this
  have := List.all_eq_true.1 this c hc
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
  exact this

theorem chW_start_after : ∀ t, 2 ≤ t → riseB (Wit.chW start).req t = false := by
  intro t ht
  cases hr : riseB (Wit.chW start).req t
  · rfl
  · exfalso
    have h0 : riseB (Wit.chW start).req 0 = true := by decide +kernel
    have c1 : cnt (riseB (Wit.chW start).req) 1 = 1 := by simp [cnt, h0]
    have c2 := cnt_mono (riseB (Wit.chW start).req) (show 1 ≤ t by omega)
    have c3 := cnt_succ_of hr
    have := Wit.w_start_once (t + 1)
    omega

/-- **Non-vacuity of `gcd_hw_safe_from_reset`, with a result**: C's 8t run `chW` (a = 12,
b = 18), seen from `T0 = 2`, is in `AtS` (with channel 3's acknowledge still 0), meets
H_CELLS_AFTER, H_BUNDLE_AFTER and H_START_AFTER, and latches 6 = gcd 12 18 on out0 at 473. -/
theorem gcd_hw_safe_from_reset_nonvac :
    ∃ (r : Fin NC → Chan) (T0 : Nat), AtS r T0 ∧
      (∀ o : Fin NO, CellA r T0 (srcV 12 18) (opAt o)) ∧ (∀ c, HeldA (r c) T0) ∧
      (∀ t, T0 ≤ t → riseB (r start).req t = false) ∧
      ∃ e, T0 ≤ e ∧ fallB (r out0).ack e = true ∧ (r out0).dat e = 6 :=
  ⟨Wit.chW, 2, chW_atS, chW_cellA, fun c t _ => Wit.w_held c t, chW_start_after,
    Wit.out0Close, by decide, Wit.w_out0.1.1, Wit.w_out0.2⟩

end Formal.Cells.ResetCapstone
