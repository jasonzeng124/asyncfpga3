import Formal.Net.CapstoneNetChk

/-!
# Probe Brz (shard B): what C's gcd_hw capstone assumes at time 0, and the glue from B's reset state

C's capstone (`gcd_hw_circuit_safe3`, `gcd_hw_live_final`) quantifies over channel families
`ch : Fin NC → Chan` with `H_CELLS : ∀ o, Cell ch (srcV a b) (opAt o)`. The initial-state
assumption is not a separate hypothesis: it is the `init*` fields of every operator's gate
model, at time 0.

## (1) The exact initial-state content of H_CELLS (`cell_req0`, `cell_ack0`, `cap_idle0`)

Per operator kind (C's structures, read-only):
* `Fork.Fork`: `initA : a.ack 0 = false`, `initO : ∀ o ∈ os, o.req 0 = false`;
* `Join.Join`: `initO : o.req 0 = false`, `initI : ∀ i ∈ is, i.ack 0 = false`;
* `Steer.Steer`: `initJ : j.ack 0 = false`, `initO : ∀ b, (out b).req 0 = false`;
* `Mux.Mux`: `i0 : j0 0 = false`, `i1 : j1 0 = false`, `iz`, `ix`, `iy`, `ic` (wires 0);
* `MuxN.MuxN`: `ij : ∀ k < 3, j k 0 = false`, `iz`, `ix`, `ic`;
* `CM.AMerge`: `i1 : g1 0 = false`, `i2 : g2 0 = false`, `iz`, `ix`, `iy`;
* `Link.Link`: `ic : c 0 = false` (the C-element), `ii : i.ack 0 = false`, `io : o.req 0 = false`;
* `Capstone.Src`: `iz : z.req 0 = false` (a, b and start are NOT offered at time 0);
* `Gcd.Sink`: `init : c.ack 0 = false`.
`cap_idle0`: since every channel has a producer and a consumer (C's `prod_mem`, `cons_mem`),
H_CELLS implies `Init (ch c)` (req = ack = 0 at time 0) for EVERY one of the 465 channels, and
every internal node (link C-element, mux joins, arbiter grants) is 0. Data is unconstrained.
That is C's H_RESET row ("every channel starts at req = ack = 0 and every C-element node at 0").
There are no initial tokens in C's network (bdc places none in gcd_hw's links).

## (3) The glue (`gl`, `glue_cell`, `glue_cells`)

B's reset theorems show the RTL is NOT in that state at any time of the reset or quiet window
(see `ResetCapstone.rtl_not_idle`): the rig token `urig.uenv1` is 1 during reset, so the
requests of a, b, start and of their fork branches (channels 0..6, all wires from node 3275)
are 1, and the p_end sink (channel 3) has already acknowledged (`urig.upsnk`, node 3257).
That state `AtS` is reachable from C's idle state in three C-legal steps (sources rise,
fork branches rise, the sink acknowledges). `gl r T0` is that 3-tick virtual prefix followed
by the real family `r` from `T0` on. `glue_cells`: if `r` is in `AtS` at `T0` and satisfies
the gate models from `T0` on (`CellA`, C's gate models with the `init*` fields dropped and
every step field restricted to `t ≥ T0`), then `gl r T0` satisfies C's H_CELLS exactly.

Assumed: `AtS r T0`; `CellA` for every operator (= C's H_CELLS dynamics after `T0`, with the
internal nodes 0 at `T0`). Proved: H_CELLS for the glued family. NOT covered: whether the RTL
satisfies `CellA` (that is C's H_CELLS problem, the O4 refinement), anything before `T0`.
-/

namespace Formal.Cells.ResetCapstone
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd

/-! ## (1) The init content of H_CELLS -/

section init
variable {n : Nat}

theorem cell_req0 (ch : Fin n → Chan) (sv : Nat → Nat) (k : K n) (h : Cell ch sv k) :
    ∀ c ∈ k.outsC, (ch c).req 0 = false := by
  intro c hc
  cases k with
  | forkG i os => exact h.initO _ (List.mem_map_of_mem hc)
  | forkH i os l hh d hs => exact h.initO _ (List.mem_map_of_mem hc)
  | join ins o e js jw =>
    simp only [K.outsC, List.mem_singleton] at hc; subst hc; exact h.initO
  | bjoin ins o ec ed =>
    simp only [K.outsC, List.mem_singleton] at hc; subst hc; exact h.initO
  | steerC j t f =>
    simp only [K.outsC, List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl
    · exact h.initO true
    · exact h.initO false
  | steerD j t f fd sw =>
    simp only [K.outsC, List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl
    · exact h.initO true
    · exact h.initO false
  | mux c' x y z mw =>
    simp only [K.outsC, List.mem_singleton] at hc; subst hc
    obtain ⟨_, _, M⟩ := h; exact M.iz
  | muxn c' x0 x1 x2 z nw =>
    simp only [K.outsC, List.mem_singleton] at hc; subst hc
    obtain ⟨_, M⟩ := h; exact M.iz
  | amerge x y z w =>
    simp only [K.outsC, List.mem_singleton] at hc; subst hc
    obtain ⟨_, _, M⟩ := h; exact M.iz
  | link i o =>
    simp only [K.outsC, List.mem_singleton] at hc; subst hc
    obtain ⟨_, L⟩ := h; exact L.io
  | src z which d =>
    simp only [K.outsC, List.mem_singleton] at hc; subst hc; exact h.iz
  | sink i => simp [K.outsC] at hc

theorem cell_ack0 (ch : Fin n → Chan) (sv : Nat → Nat) (k : K n) (h : Cell ch sv k) :
    ∀ c ∈ k.insC, (ch c).ack 0 = false := by
  intro c hc
  cases k with
  | forkG i os =>
    simp only [K.insC, List.mem_singleton] at hc; subst hc; exact h.initA
  | forkH i os l hh d hs =>
    simp only [K.insC, List.mem_singleton] at hc; subst hc; exact h.initA
  | join ins o e js jw => exact h.initI _ (List.mem_map_of_mem hc)
  | bjoin ins o ec ed => exact h.initI _ (List.mem_map_of_mem hc)
  | steerC j t f =>
    simp only [K.insC, List.mem_singleton] at hc; subst hc; exact h.initJ
  | steerD j t f fd sw =>
    simp only [K.insC, List.mem_singleton] at hc; subst hc; exact h.initJ
  | mux c' x y z mw =>
    obtain ⟨_, _, M⟩ := h
    simp only [K.insC, List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact M.ic
    · exact M.ix
    · exact M.iy
  | muxn c' x0 x1 x2 z nw =>
    obtain ⟨_, M⟩ := h
    simp only [K.insC, List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact M.ic
    · exact M.ix 0 (by decide)
    · exact M.ix 1 (by decide)
    · exact M.ix 2 (by decide)
  | amerge x y z w =>
    obtain ⟨_, _, M⟩ := h
    simp only [K.insC, List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl
    · exact M.ix
    · exact M.iy
  | link i o =>
    simp only [K.insC, List.mem_singleton] at hc; subst hc
    obtain ⟨_, L⟩ := h; exact L.ii
  | src z which d => simp [K.insC] at hc
  | sink i =>
    simp only [K.insC, List.mem_singleton] at hc; subst hc; exact h.init

end init

/-- **C's initial-state assumption, exactly** (the channel part): H_CELLS forces every one
of the 465 channels of gcd_hw's network to be idle (`req = ack = 0`) at time 0. -/
theorem cap_idle0 (ch : Fin NC → Chan) (sv : Nat → Nat)
    (H_CELLS : ∀ o : Fin NO, Cell ch sv (opAt o)) : ∀ c, Init (ch c) := fun c =>
  ⟨cell_req0 ch sv _ (H_CELLS (prodOf c)) c (prod_mem c),
   cell_ack0 ch sv _ (H_CELLS (consOf c)) c (cons_mem c)⟩

/-! ## (3) The reset state in C's terms, and the virtual prefix -/

/-- The channels whose request is 1 in the RTL reset state: a, b, start (0, 1, 2) and the
fork branches 3..6 (`0#0` = p_end, `0#1`, `1#0`, `1#1`): all wires of `urig.uenv1`. -/
def hot (c : Fin NC) : Bool := decide (c.val < 7)

/-- The virtual prefix: the sources rise at tick 1, the fork branches at tick 2. -/
def preR (c : Fin NC) (t : Nat) : Bool :=
  decide (c.val < 3 ∧ 1 ≤ t) || decide (c.val < 7 ∧ 2 ≤ t)

/-- **The RTL reset state, in C's channel terms** (`AtS r T0`): requests 1 exactly on
channels 0..6, acknowledge 1 exactly on channel 3 (the p_end sink has consumed). -/
structure AtS (r : Fin NC → Chan) (T0 : Nat) : Prop where
  req : ∀ c, (r c).req T0 = hot c
  ack : ∀ c, (r c).ack T0 = decide (c.val = 3)

/-- The glued channel: 3 virtual ticks, then `r` from `T0`. Data in the prefix is `r`'s at
`T0`. -/
def gl (r : Fin NC → Chan) (T0 : Nat) (c : Fin NC) : Chan where
  req t := if t < 3 then preR c t else (r c).req (t - 3 + T0)
  ack t := if t < 3 then false else (r c).ack (t - 3 + T0)
  dat t := if t < 3 then (r c).dat T0 else (r c).dat (t - 3 + T0)

/-- A glued internal node: 0 in the prefix. -/
def glT (x : Trace) (T0 : Nat) : Trace := fun t => if t < 3 then false else x (t - 3 + T0)

section glue
variable {r : Fin NC → Chan} {T0 : Nat}

theorem gl_req_s (c : Fin NC) (s : Nat) : (gl r T0 c).req (s + 3) = (r c).req (s + T0) := by
  simp only [gl, show ¬ (s + 3 < 3) by omega, ↓reduceIte, Nat.add_sub_cancel]
theorem gl_ack_s (c : Fin NC) (s : Nat) : (gl r T0 c).ack (s + 3) = (r c).ack (s + T0) := by
  simp only [gl, show ¬ (s + 3 < 3) by omega, ↓reduceIte, Nat.add_sub_cancel]
theorem gl_dat_s (c : Fin NC) (s : Nat) : (gl r T0 c).dat (s + 3) = (r c).dat (s + T0) := by
  simp only [gl, show ¬ (s + 3 < 3) by omega, ↓reduceIte, Nat.add_sub_cancel]
theorem glT_s (x : Trace) (s : Nat) : glT x T0 (s + 3) = x (s + T0) := by
  simp only [glT, show ¬ (s + 3 < 3) by omega, ↓reduceIte, Nat.add_sub_cancel]
theorem gl_req_lt (c : Fin NC) {t : Nat} (h : t < 3) : (gl r T0 c).req t = preR c t := by
  simp [gl, h]
theorem gl_ack_lt (c : Fin NC) {t : Nat} (h : t < 3) : (gl r T0 c).ack t = false := by
  simp [gl, h]
theorem gl_dat_lt (c : Fin NC) {t : Nat} (h : t < 3) : (gl r T0 c).dat t = (r c).dat T0 := by
  simp [gl, h]
theorem glT_lt (x : Trace) {t : Nat} (h : t < 3) : glT x T0 t = false := by simp [glT, h]

theorem s1 (s T0 : Nat) : s + 1 + T0 = s + T0 + 1 := by omega

/-- Time split: prefix, junction, real. -/
theorem tsplit (t : Nat) : t < 2 ∨ t = 2 ∨ ∃ s, t = s + 3 :=
  if h : t < 2 then .inl h else if h2 : t = 2 then .inr (.inl h2) else .inr (.inr ⟨t - 3, by omega⟩)

/-- In the prefix and at the junction only hot requests and ack 3 move. -/
theorem req_step_pre (hS : AtS r T0) (c : Fin NC) {t : Nat} (ht : t < 3)
    (hm : (gl r T0 c).req (t + 1) ≠ (gl r T0 c).req t) :
    hot c = true ∧ (gl r T0 c).req (t + 1) = true ∧ (t = 0 ∧ c.val < 3 ∨ t = 1 ∧ 3 ≤ c.val) := by
  have hc := c.isLt
  rcases tsplit t with h | rfl | ⟨s, rfl⟩
  · rw [gl_req_lt c (by omega), gl_req_lt c ht] at *
    simp only [preR, hot] at *
    have : t = 0 ∨ t = 1 := by omega
    rcases this with rfl | rfl <;> by_cases h3 : c.val < 3 <;> by_cases h7 : c.val < 7 <;>
      simp_all <;> omega
  · exfalso; apply hm
    rw [show (2 : Nat) + 1 = 0 + 3 from rfl, gl_req_s, Nat.zero_add, hS.req, gl_req_lt c ht]
    simp only [preR, hot]; by_cases h3 : c.val < 3 <;> by_cases h7 : c.val < 7 <;> simp_all <;> omega
  · omega

theorem ack_step_pre (hS : AtS r T0) (c : Fin NC) {t : Nat} (ht : t < 3)
    (hm : (gl r T0 c).ack (t + 1) ≠ (gl r T0 c).ack t) : c.val = 3 ∧ t = 2 := by
  rcases tsplit t with h | rfl | ⟨s, rfl⟩
  · rw [gl_ack_lt c (by omega), gl_ack_lt c ht] at hm; exact absurd rfl hm
  · refine ⟨?_, rfl⟩
    rw [show (2 : Nat) + 1 = 0 + 3 from rfl, gl_ack_s, Nat.zero_add, hS.ack, gl_ack_lt c ht] at hm
    by_cases h : c.val = 3
    · exact h
    · simp [h] at hm
  · omega

theorem glT_step_pre {x : Trace} (hx : x T0 = false) {t : Nat} (ht : t < 3) :
    glT x T0 (t + 1) = glT x T0 t := by
  rcases tsplit t with h | rfl | ⟨s, rfl⟩
  · rw [glT_lt x (by omega), glT_lt x ht]
  · rw [show (2 : Nat) + 1 = 0 + 3 from rfl, glT_s, Nat.zero_add, hx, glT_lt x ht]
  · omega

theorem gl_dat_pre (c : Fin NC) {t : Nat} (ht : t ≤ 3) : (gl r T0 c).dat t = (r c).dat T0 := by
  by_cases h : t < 3
  · exact gl_dat_lt c h
  · rw [show t = 0 + 3 by omega, gl_dat_s, Nat.zero_add]

theorem gl_req_pre (hS : AtS r T0) (c : Fin NC) (hc : hot c = false) {t : Nat} (ht : t ≤ 3) :
    (gl r T0 c).req t = false := by
  by_cases h : t < 3
  · rw [gl_req_lt c h]; simp only [preR]; simp only [hot, decide_eq_false_iff_not] at hc
    simp; omega
  · rw [show t = 0 + 3 by omega, gl_req_s, Nat.zero_add, hS.req, hc]

theorem gl_ack_pre (hS : AtS r T0) (c : Fin NC) (hc : c.val ≠ 3) {t : Nat} (ht : t ≤ 3) :
    (gl r T0 c).ack t = false := by
  by_cases h : t < 3
  · exact gl_ack_lt c h
  · rw [show t = 0 + 3 by omega, gl_ack_s, Nat.zero_add, hS.ack]; simp [hc]

end glue

end Formal.Cells.ResetCapstone
