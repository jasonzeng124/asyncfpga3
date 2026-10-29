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

/-! ## C's gate models from `T0` on (`CellA`): the `init*` fields dropped, steps `t ≥ T0` -/

section after
variable (r : Fin NC → Chan) (T0 : Nat)

structure ForkA (a : Fin NC) (os : List (Fin NC)) : Prop where
  ne : os ≠ []
  wire : ∀ o ∈ os, ∀ t, T0 ≤ t → (r o).req (t + 1) ≠ (r o).req t → (r o).req (t + 1) = (r a).req t
  cel : ∀ t, T0 ≤ t → (r a).ack (t + 1) ≠ (r a).ack t → ∀ o ∈ os, (r o).ack t = (r a).ack (t + 1)
  dat : ∀ o ∈ os, ∀ t, T0 ≤ t → (r o).dat t = (r a).dat t

structure JoinA (g : List Nat → Nat) (is : List (Fin NC)) (o : Fin NC) : Prop where
  ne : is ≠ []
  cel : ∀ t, T0 ≤ t → (r o).req (t + 1) ≠ (r o).req t → ∀ i ∈ is, (r i).req t = (r o).req (t + 1)
  wire : ∀ i ∈ is, ∀ t, T0 ≤ t → (r i).ack (t + 1) ≠ (r i).ack t → (r i).ack (t + 1) = (r o).ack t
  dat : ∀ t, T0 ≤ t → (r o).dat t = g (is.map (fun i => (r i).dat t))

structure SteerA (sel : Nat → Bool) (f : Nat → Nat) (j tt ff : Fin NC) : Prop where
  lut : ∀ b t, T0 ≤ t → (r (bif b then tt else ff)).req (t + 1) ≠ (r (bif b then tt else ff)).req t →
    (r (bif b then tt else ff)).req (t + 1) = ((r j).req t && (sel ((r j).dat t) == b))
  orr : ∀ t, T0 ≤ t → (r j).ack (t + 1) ≠ (r j).ack t →
    (r j).ack (t + 1) = ((r tt).ack t || (r ff).ack t)
  dat : ∀ b t, T0 ≤ t → (r (bif b then tt else ff)).dat t = f ((r j).dat t)

structure MuxA (sel : Nat → Bool) (x y c z : Fin NC) (j0 j1 : Trace) : Prop where
  cj0 : ∀ t, T0 ≤ t → j0 (t + 1) ≠ j0 t →
    (r x).req t = j0 (t + 1) ∧ ((r c).req t && !sel ((r c).dat t)) = j0 (t + 1)
  cj1 : ∀ t, T0 ≤ t → j1 (t + 1) ≠ j1 t →
    (r y).req t = j1 (t + 1) ∧ ((r c).req t && sel ((r c).dat t)) = j1 (t + 1)
  zr : ∀ t, T0 ≤ t → (r z).req (t + 1) ≠ (r z).req t → (r z).req (t + 1) = (j0 t || j1 t)
  xa : ∀ t, T0 ≤ t → (r x).ack (t + 1) ≠ (r x).ack t → j0 t = (r x).ack (t + 1) ∧ (r z).ack t = (r x).ack (t + 1)
  ya : ∀ t, T0 ≤ t → (r y).ack (t + 1) ≠ (r y).ack t → j1 t = (r y).ack (t + 1) ∧ (r z).ack t = (r y).ack (t + 1)
  ca : ∀ t, T0 ≤ t → (r c).ack (t + 1) ≠ (r c).ack t → (r c).ack (t + 1) = (r z).ack t
  dat : ∀ t, T0 ≤ t → (r z).dat t = if sel ((r c).dat t) then (r y).dat t else (r x).dat t
  i0 : j0 T0 = false
  i1 : j1 T0 = false

structure MuxNA (sel : Nat → Nat) (xs : Nat → Fin NC) (c z : Fin NC) (j : Nat → Trace) : Prop where
  cj : ∀ k, k < 3 → ∀ t, T0 ≤ t → j k (t + 1) ≠ j k t →
    (r (xs k)).req t = j k (t + 1) ∧ ((r c).req t && (sel ((r c).dat t) == k)) = j k (t + 1)
  zr : ∀ t, T0 ≤ t → (r z).req (t + 1) ≠ (r z).req t → (r z).req (t + 1) = (j 0 t || j 1 t || j 2 t)
  xa : ∀ k, k < 3 → ∀ t, T0 ≤ t → (r (xs k)).ack (t + 1) ≠ (r (xs k)).ack t →
    j k t = (r (xs k)).ack (t + 1) ∧ (r z).ack t = (r (xs k)).ack (t + 1)
  ca : ∀ t, T0 ≤ t → (r c).ack (t + 1) ≠ (r c).ack t → (r c).ack (t + 1) = (r z).ack t
  dat : ∀ t, T0 ≤ t → sel ((r c).dat t) < 3 → (r z).dat t = (r (xs (sel ((r c).dat t)))).dat t
  ij : ∀ k, k < 3 → j k T0 = false

structure AMergeA (x y z : Fin NC) (g1 g2 : Trace) : Prop where
  H_ARB1 : ∀ t, T0 ≤ t → g1 (t + 1) ≠ g1 t →
    g1 (t + 1) = (r x).req t ∧ (g1 (t + 1) = true → g2 t = false ∧ (r z).ack t = false)
  H_ARB2 : ∀ t, T0 ≤ t → g2 (t + 1) ≠ g2 t →
    g2 (t + 1) = (r y).req t ∧ (g2 (t + 1) = true → g1 t = false ∧ (r z).ack t = false)
  H_ARB_EXCL : ∀ t, T0 ≤ t → (g1 t && g2 t) = false
  zr : ∀ t, T0 ≤ t → (r z).req (t + 1) ≠ (r z).req t → (r z).req (t + 1) = (g1 t || g2 t)
  H_AMERGE_RTZ : ∀ t, T0 ≤ t → (r z).req t = false → (r z).req (t + 1) = true →
    (r x).ack t = false ∧ (r y).ack t = false
  xa : ∀ t, T0 ≤ t → (r x).ack (t + 1) ≠ (r x).ack t → g1 t = (r x).ack (t + 1) ∧ (r z).ack t = (r x).ack (t + 1)
  ya : ∀ t, T0 ≤ t → (r y).ack (t + 1) ≠ (r y).ack t → g2 t = (r y).ack (t + 1) ∧ (r z).ack t = (r y).ack (t + 1)
  dat : ∀ t, T0 ≤ t → (r z).dat t =
    2 * (if (g2 t || (r y).ack t) then (r y).dat t else (r x).dat t) + Ops.Mux.b2n (g2 t || (r y).ack t)
  i1 : g1 T0 = false
  i2 : g2 T0 = false

structure LinkA (i o : Fin NC) (c : Trace) : Prop where
  H_CEL_SI : ∀ t, T0 ≤ t → c (t + 1) ≠ c t →
    c (t + 1) = Formal.Cells.LinkHandshake.ctlB ((r i).req t) ((r o).ack t) (c t) false
  H_ACK_DI : ∀ t, T0 ≤ t → (r i).ack (t + 1) ≠ (r i).ack t → (r i).ack (t + 1) = c t
  H_REQ_DI : ∀ t, T0 ≤ t → (r o).req (t + 1) ≠ (r o).req t → (r o).req (t + 1) = c t
  H_LATCH_OPEN : ∀ t, T0 ≤ t → c t = true → (r o).dat t = (r i).dat t
  H_LATCH_HOLD : ∀ t, T0 ≤ t → c (t + 1) = false → (r o).dat (t + 1) = (r o).dat t
  ic : c T0 = false

structure SrcA (z : Fin NC) (v : Nat) : Prop where
  H_LUT_SI : ∀ t, T0 ≤ t → (r z).req (t + 1) ≠ (r z).req t → (r z).req (t + 1) = !(r z).ack t
  dat : ∀ t, T0 ≤ t → (r z).dat t = v

structure SinkA (i : Fin NC) : Prop where
  wire : ∀ t, T0 ≤ t → (r i).ack (t + 1) ≠ (r i).ack t → (r i).ack (t + 1) = (r i).req t

/-- **H_CELLS_AFTER**: C's gate model of each operator, from `T0` on, with the operator's
internal nodes 0 at `T0` (and no condition at all before `T0`). -/
def CellA (sv : Nat → Nat) : K NC → Prop
  | .forkG i os => ForkA r T0 i os
  | .forkH i os _ _ _ _ => ForkA r T0 i (os.map Prod.fst)
  | .join ins o e js _ => JoinA r T0 (jg e js) ins o
  | .bjoin ins o ec ed => JoinA r T0 (bg ec ed) ins o
  | .steerC j t f => SteerA r T0 sel2 (fun _ => 0) j t f
  | .steerD j t f fd _ => SteerA r T0 sel2 (fun v => fd.eval [v / 2]) j t f
  | .mux c x y z _ => ∃ j0 j1, MuxA r T0 sel2 x y c z j0 j1
  | .muxn c x0 x1 x2 z _ => ∃ j, MuxNA r T0 selD (cx3 x0 x1 x2) c z j
  | .amerge x y z _ => ∃ g1 g2, AMergeA r T0 x y z g1 g2
  | .link i o => ∃ c, LinkA r T0 i o c
  | .src z which _ => SrcA r T0 z (sv which)
  | .sink i => SinkA r T0 i

end after

/-- Which channel each operator's prefix steps may move (decidable side conditions,
checked for every gcd_hw operator in `side_all`). -/
def ne3 (c : Fin NC) : Bool := c.val != 3

def Side : K NC → Bool
  | .forkG i os => ne3 i && os.all (fun o => !hot o || (decide (i.val < 3) && decide (3 ≤ o.val)))
  | .forkH i os _ _ _ _ => ne3 i &&
      (os.map Prod.fst).all (fun o => !hot o || (decide (i.val < 3) && decide (3 ≤ o.val)))
  | .join ins o _ _ _ => !hot o && ins.all ne3
  | .bjoin ins o _ _ => !hot o && ins.all ne3
  | .steerC j t f => ne3 j && !hot t && !hot f
  | .steerD j t f _ _ => ne3 j && !hot t && !hot f
  | .mux c x y z _ => !hot z && ne3 c && ne3 x && ne3 y
  | .muxn c x0 x1 x2 z _ => !hot z && ne3 c && ne3 x0 && ne3 x1 && ne3 x2
  | .amerge x y z _ => !hot z && ne3 x && ne3 y
  | .link i o => !hot o && ne3 i
  | .src z _ _ => !hot z || decide (z.val < 3)
  | .sink _ => true

/-! ## The glue, cell type by cell type -/

section gluek
variable {r : Fin NC → Chan} {T0 : Nat}

theorem shift_of {t : Nat} (ht : ¬ t < 3) : ∃ s, t = s + 3 := ⟨t - 3, by omega⟩

theorem preR0 (c : Fin NC) : preR c 0 = false := by simp [preR]

theorem ne3_ne {c : Fin NC} (h : ne3 c = true) : c.val ≠ 3 := by
  simpa [ne3] using h

theorem hot_f {c : Fin NC} (h : (!hot c) = true) : hot c = false := by simpa using h

/-- A non-hot request never moves in the prefix or at the junction. -/
theorem cold_req (hS : AtS r T0) {c : Fin NC} (hc : hot c = false) {t : Nat} (ht : t < 3)
    (hm : (gl r T0 c).req (t + 1) ≠ (gl r T0 c).req t) : False := by
  have := (req_step_pre hS c ht hm).1; rw [hc] at this; exact absurd this (by decide)

theorem cold_ack (hS : AtS r T0) {c : Fin NC} (hc : c.val ≠ 3) {t : Nat} (ht : t < 3)
    (hm : (gl r T0 c).ack (t + 1) ≠ (gl r T0 c).ack t) : False :=
  hc (ack_step_pre hS c ht hm).1

theorem cold_glT {x : Trace} (hx : x T0 = false) {t : Nat} (ht : t < 3)
    (hm : glT x T0 (t + 1) ≠ glT x T0 t) : False := hm (glT_step_pre hx ht)

theorem glue_fork (hS : AtS r T0) (a : Fin NC) (os : List (Fin NC))
    (ha : ne3 a = true)
    (hos : os.all (fun o => !hot o || (decide (a.val < 3) && decide (3 ≤ o.val))) = true)
    (A : ForkA r T0 a os) : Fork.Fork (gl r T0 a) (os.map (gl r T0)) where
  ne := by simpa using A.ne
  wire := by
    intro o' ho' t hm
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 ho'
    by_cases ht : t < 3
    · obtain ⟨hh, h1, hc⟩ := req_step_pre hS o ht hm
      have hx := List.all_eq_true.1 hos o ho
      simp only [hh, Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hx
      rcases hc with ⟨rfl, h⟩ | ⟨rfl, h⟩
      · omega
      · rw [h1, gl_req_lt a (by omega)]; simp [preR, hx.1]
    · obtain ⟨s, rfl⟩ := shift_of ht
      rw [show s + 3 + 1 = (s + 1) + 3 by omega] at hm ⊢
      simp only [gl_req_s, s1] at hm ⊢
      exact A.wire o ho (s + T0) (by omega) hm
  cel := by
    intro t hm o' ho'
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 ho'
    by_cases ht : t < 3
    · exact absurd (cold_ack hS (ne3_ne ha) ht hm) id
    · obtain ⟨s, rfl⟩ := shift_of ht
      rw [show s + 3 + 1 = (s + 1) + 3 by omega] at hm ⊢
      simp only [gl_ack_s, s1] at hm ⊢
      exact A.cel (s + T0) (by omega) hm o ho
  dat := by
    intro o' ho' t
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 ho'
    by_cases ht : t < 3
    · rw [gl_dat_lt o ht, gl_dat_lt a ht]; exact A.dat o ho T0 (Nat.le_refl _)
    · obtain ⟨s, rfl⟩ := shift_of ht
      simp only [gl_dat_s]; exact A.dat o ho (s + T0) (by omega)
  initA := gl_ack_lt a (by decide)
  initO := by
    intro o' ho'
    obtain ⟨o, _, rfl⟩ := List.mem_map.1 ho'
    rw [gl_req_lt o (by decide)]; exact preR0 o

theorem glue_join (hS : AtS r T0) (g : List Nat → Nat) (is : List (Fin NC)) (o : Fin NC)
    (ho : hot o = false) (his : is.all ne3 = true)
    (A : JoinA r T0 g is o) : Join.Join g (is.map (gl r T0)) (gl r T0 o) where
  ne := by simpa using A.ne
  cel := by
    intro t hm i' hi'
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hi'
    by_cases ht : t < 3
    · exact absurd (cold_req hS ho ht hm) id
    · obtain ⟨s, rfl⟩ := shift_of ht
      rw [show s + 3 + 1 = (s + 1) + 3 by omega] at hm ⊢
      simp only [gl_req_s, s1] at hm ⊢
      exact A.cel (s + T0) (by omega) hm i hi
  wire := by
    intro i' hi' t hm
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hi'
    by_cases ht : t < 3
    · exact absurd (cold_ack hS (ne3_ne (List.all_eq_true.1 his i hi)) ht hm) id
    · obtain ⟨s, rfl⟩ := shift_of ht
      rw [show s + 3 + 1 = (s + 1) + 3 by omega] at hm ⊢
      simp only [gl_ack_s, s1] at hm ⊢
      exact A.wire i hi (s + T0) (by omega) hm
  dat := by
    intro t
    by_cases ht : t < 3
    · rw [gl_dat_lt o ht, A.dat T0 (Nat.le_refl _), List.map_map]
      congr 1; apply List.map_congr_left; intro i _; simp [Function.comp, gl_dat_lt i ht]
    · obtain ⟨s, rfl⟩ := shift_of ht
      rw [gl_dat_s, A.dat (s + T0) (by omega), List.map_map]
      congr 1
  initO := by rw [gl_req_lt o (by decide)]; exact preR0 o
  initI := by
    intro i' hi'
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hi'
    exact gl_ack_lt i (by decide)

theorem glue_steer (hS : AtS r T0) (sel : Nat → Bool) (f : Nat → Nat) (j tt ff : Fin NC)
    (hj : ne3 j = true) (htt : hot tt = false) (hff : hot ff = false)
    (A : SteerA r T0 sel f j tt ff) :
    Steer.Steer sel f (gl r T0 j) (fun b => gl r T0 (bif b then tt else ff)) where
  lut := by
    intro b t hm
    by_cases ht : t < 3
    · have hc : hot (bif b then tt else ff) = false := by cases b <;> assumption
      exact absurd (cold_req hS hc ht hm) id
    · obtain ⟨s, rfl⟩ := shift_of ht
      rw [show s + 3 + 1 = (s + 1) + 3 by omega] at hm ⊢
      simp only [gl_req_s, gl_dat_s, s1] at hm ⊢
      exact A.lut b (s + T0) (by omega) hm
  orr := by
    intro t hm
    by_cases ht : t < 3
    · exact absurd (cold_ack hS (ne3_ne hj) ht hm) id
    · obtain ⟨s, rfl⟩ := shift_of ht
      rw [show s + 3 + 1 = (s + 1) + 3 by omega] at hm ⊢
      simp only [gl_ack_s, s1] at hm ⊢
      exact A.orr (s + T0) (by omega) hm
  dat := by
    intro b t
    by_cases ht : t < 3
    · rw [gl_dat_lt _ ht, gl_dat_lt j ht]; exact A.dat b T0 (Nat.le_refl _)
    · obtain ⟨s, rfl⟩ := shift_of ht
      simp only [gl_dat_s]; exact A.dat b (s + T0) (by omega)
  initJ := gl_ack_lt j (by decide)
  initO := by intro b; rw [gl_req_lt _ (by decide)]; exact preR0 _

theorem glue_mux (hS : AtS r T0) (sel : Nat → Bool) (x y c z : Fin NC) (j0 j1 : Trace)
    (hz : hot z = false) (hc : ne3 c = true) (hx : ne3 x = true) (hy : ne3 y = true)
    (A : MuxA r T0 sel x y c z j0 j1) :
    Mux.Mux sel (gl r T0 x) (gl r T0 y) (gl r T0 c) (gl r T0 z) (glT j0 T0) (glT j1 T0) where
  cj0 := by
    intro t hm
    by_cases ht : t < 3
    · exact absurd (cold_glT A.i0 ht hm) id
    · obtain ⟨s, rfl⟩ := shift_of ht
      rw [show s + 3 + 1 = (s + 1) + 3 by omega] at hm ⊢
      simp only [gl_req_s, gl_dat_s, glT_s, s1] at hm ⊢
      exact A.cj0 (s + T0) (by omega) hm
  cj1 := by
    intro t hm
    by_cases ht : t < 3
    · exact absurd (cold_glT A.i1 ht hm) id
    · obtain ⟨s, rfl⟩ := shift_of ht
      rw [show s + 3 + 1 = (s + 1) + 3 by omega] at hm ⊢
      simp only [gl_req_s, gl_dat_s, glT_s, s1] at hm ⊢
      exact A.cj1 (s + T0) (by omega) hm
  zr := by
    intro t hm
    by_cases ht : t < 3
    · exact absurd (cold_req hS hz ht hm) id
    · obtain ⟨s, rfl⟩ := shift_of ht
      rw [show s + 3 + 1 = (s + 1) + 3 by omega] at hm ⊢
      simp only [gl_req_s, glT_s, s1] at hm ⊢
      exact A.zr (s + T0) (by omega) hm
  xa := by
    intro t hm
    by_cases ht : t < 3
    · exact absurd (cold_ack hS (ne3_ne hx) ht hm) id
    · obtain ⟨s, rfl⟩ := shift_of ht
      rw [show s + 3 + 1 = (s + 1) + 3 by omega] at hm ⊢
      simp only [gl_ack_s, glT_s, s1] at hm ⊢
      exact A.xa (s + T0) (by omega) hm
  ya := by
    intro t hm
    by_cases ht : t < 3
    · exact absurd (cold_ack hS (ne3_ne hy) ht hm) id
    · obtain ⟨s, rfl⟩ := shift_of ht
      rw [show s + 3 + 1 = (s + 1) + 3 by omega] at hm ⊢
      simp only [gl_ack_s, glT_s, s1] at hm ⊢
      exact A.ya (s + T0) (by omega) hm
  ca := by
    intro t hm
    by_cases ht : t < 3
    · exact absurd (cold_ack hS (ne3_ne hc) ht hm) id
    · obtain ⟨s, rfl⟩ := shift_of ht
      rw [show s + 3 + 1 = (s + 1) + 3 by omega] at hm ⊢
      simp only [gl_ack_s, s1] at hm ⊢
      exact A.ca (s + T0) (by omega) hm
  dat := by
    intro t
    by_cases ht : t < 3
    · rw [gl_dat_lt z ht, gl_dat_lt c ht, gl_dat_lt x ht, gl_dat_lt y ht]
      exact A.dat T0 (Nat.le_refl _)
    · obtain ⟨s, rfl⟩ := shift_of ht
      simp only [gl_dat_s]; exact A.dat (s + T0) (by omega)
  i0 := glT_lt j0 (by decide)
  i1 := glT_lt j1 (by decide)
  iz := by rw [gl_req_lt z (by decide)]; exact preR0 z
  ix := gl_ack_lt x (by decide)
  iy := gl_ack_lt y (by decide)
  ic := gl_ack_lt c (by decide)

theorem glue_muxn (hS : AtS r T0) (sel : Nat → Nat) (x0 x1 x2 c z : Fin NC) (j : Nat → Trace)
    (hz : hot z = false) (hc : ne3 c = true) (h0 : ne3 x0 = true) (h1 : ne3 x1 = true)
    (h2 : ne3 x2 = true) (A : MuxNA r T0 sel (cx3 x0 x1 x2) c z j) :
    MuxN.MuxN sel (fun k => gl r T0 (cx3 x0 x1 x2 k)) (gl r T0 c) (gl r T0 z)
      (fun k => glT (j k) T0) where
  cj := by
    intro k hk t hm
    by_cases ht : t < 3
    · exact absurd (cold_glT (A.ij k hk) ht hm) id
    · obtain ⟨s, rfl⟩ := shift_of ht
      rw [show s + 3 + 1 = (s + 1) + 3 by omega] at hm ⊢
      simp only [gl_req_s, gl_dat_s, glT_s, s1] at hm ⊢
      exact A.cj k hk (s + T0) (by omega) hm
  zr := by
    intro t hm
    by_cases ht : t < 3
    · exact absurd (cold_req hS hz ht hm) id
    · obtain ⟨s, rfl⟩ := shift_of ht
      rw [show s + 3 + 1 = (s + 1) + 3 by omega] at hm ⊢
      simp only [gl_req_s, glT_s, s1] at hm ⊢
      exact A.zr (s + T0) (by omega) hm
  xa := by
    intro k hk t hm
    by_cases ht : t < 3
    · have hk' : ne3 (cx3 x0 x1 x2 k) = true := by
        rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;> assumption
      exact absurd (cold_ack hS (ne3_ne hk') ht hm) id
    · obtain ⟨s, rfl⟩ := shift_of ht
      rw [show s + 3 + 1 = (s + 1) + 3 by omega] at hm ⊢
      simp only [gl_ack_s, glT_s, s1] at hm ⊢
      exact A.xa k hk (s + T0) (by omega) hm
  ca := by
    intro t hm
    by_cases ht : t < 3
    · exact absurd (cold_ack hS (ne3_ne hc) ht hm) id
    · obtain ⟨s, rfl⟩ := shift_of ht
      rw [show s + 3 + 1 = (s + 1) + 3 by omega] at hm ⊢
      simp only [gl_ack_s, s1] at hm ⊢
      exact A.ca (s + T0) (by omega) hm
  dat := by
    intro t hsel
    by_cases ht : t < 3
    · rw [gl_dat_lt c ht] at hsel ⊢
      rw [gl_dat_lt z ht, gl_dat_lt _ ht]
      exact A.dat T0 (Nat.le_refl _) hsel
    · obtain ⟨s, rfl⟩ := shift_of ht
      simp only [gl_dat_s] at hsel ⊢; exact A.dat (s + T0) (by omega) hsel
  ij := fun k _ => glT_lt (j k) (by decide)
  iz := by rw [gl_req_lt z (by decide)]; exact preR0 z
  ix := fun k _ => gl_ack_lt _ (by decide)
  ic := gl_ack_lt c (by decide)

theorem glue_amerge (hS : AtS r T0) (x y z : Fin NC) (g1 g2 : Trace)
    (hz : hot z = false) (hx : ne3 x = true) (hy : ne3 y = true)
    (A : AMergeA r T0 x y z g1 g2) :
    CM.AMerge (gl r T0 x) (gl r T0 y) (gl r T0 z) (glT g1 T0) (glT g2 T0) where
  H_ARB1 := by
    intro t hm
    by_cases ht : t < 3
    · exact absurd (cold_glT A.i1 ht hm) id
    · obtain ⟨s, rfl⟩ := shift_of ht
      rw [show s + 3 + 1 = (s + 1) + 3 by omega] at hm ⊢
      simp only [gl_req_s, gl_ack_s, glT_s, s1] at hm ⊢
      exact A.H_ARB1 (s + T0) (by omega) hm
  H_ARB2 := by
    intro t hm
    by_cases ht : t < 3
    · exact absurd (cold_glT A.i2 ht hm) id
    · obtain ⟨s, rfl⟩ := shift_of ht
      rw [show s + 3 + 1 = (s + 1) + 3 by omega] at hm ⊢
      simp only [gl_req_s, gl_ack_s, glT_s, s1] at hm ⊢
      exact A.H_ARB2 (s + T0) (by omega) hm
  H_ARB_EXCL := by
    intro t
    by_cases ht : t < 3
    · rw [glT_lt g1 ht]; rfl
    · obtain ⟨s, rfl⟩ := shift_of ht
      simp only [glT_s]; exact A.H_ARB_EXCL (s + T0) (by omega)
  zr := by
    intro t hm
    by_cases ht : t < 3
    · exact absurd (cold_req hS hz ht hm) id
    · obtain ⟨s, rfl⟩ := shift_of ht
      rw [show s + 3 + 1 = (s + 1) + 3 by omega] at hm ⊢
      simp only [gl_req_s, glT_s, s1] at hm ⊢
      exact A.zr (s + T0) (by omega) hm
  H_AMERGE_RTZ := by
    intro t h0 h1
    by_cases ht : t < 3
    · rw [gl_req_pre hS z hz (by omega)] at h1; exact absurd h1 (by decide)
    · obtain ⟨s, rfl⟩ := shift_of ht
      rw [show s + 3 + 1 = (s + 1) + 3 by omega] at h1
      simp only [gl_req_s, gl_ack_s, s1] at h0 h1 ⊢
      exact A.H_AMERGE_RTZ (s + T0) (by omega) h0 h1
  xa := by
    intro t hm
    by_cases ht : t < 3
    · exact absurd (cold_ack hS (ne3_ne hx) ht hm) id
    · obtain ⟨s, rfl⟩ := shift_of ht
      rw [show s + 3 + 1 = (s + 1) + 3 by omega] at hm ⊢
      simp only [gl_ack_s, glT_s, s1] at hm ⊢
      exact A.xa (s + T0) (by omega) hm
  ya := by
    intro t hm
    by_cases ht : t < 3
    · exact absurd (cold_ack hS (ne3_ne hy) ht hm) id
    · obtain ⟨s, rfl⟩ := shift_of ht
      rw [show s + 3 + 1 = (s + 1) + 3 by omega] at hm ⊢
      simp only [gl_ack_s, glT_s, s1] at hm ⊢
      exact A.ya (s + T0) (by omega) hm
  dat := by
    intro t
    by_cases ht : t < 3
    · have e := A.dat T0 (Nat.le_refl _)
      rw [A.i2, hS.ack y, show decide (y.val = 3) = false by simpa using ne3_ne hy] at e
      rw [gl_dat_lt z ht, gl_dat_lt x ht, gl_dat_lt y ht, glT_lt g2 ht, gl_ack_lt y ht]
      exact e
    · obtain ⟨s, rfl⟩ := shift_of ht
      simp only [gl_dat_s, gl_ack_s, glT_s]; exact A.dat (s + T0) (by omega)
  i1 := glT_lt g1 (by decide)
  i2 := glT_lt g2 (by decide)
  iz := by rw [gl_req_lt z (by decide)]; exact preR0 z
  ix := gl_ack_lt x (by decide)
  iy := gl_ack_lt y (by decide)

theorem glue_link (hS : AtS r T0) (i o : Fin NC) (c : Trace)
    (ho : hot o = false) (hi : ne3 i = true) (A : LinkA r T0 i o c) :
    Link.Link (gl r T0 i) (gl r T0 o) (glT c T0) where
  H_CEL_SI := by
    intro t hm
    by_cases ht : t < 3
    · exact absurd (cold_glT A.ic ht hm) id
    · obtain ⟨s, rfl⟩ := shift_of ht
      rw [show s + 3 + 1 = (s + 1) + 3 by omega] at hm ⊢
      simp only [gl_req_s, gl_ack_s, glT_s, s1] at hm ⊢
      exact A.H_CEL_SI (s + T0) (by omega) hm
  H_ACK_DI := by
    intro t hm
    by_cases ht : t < 3
    · exact absurd (cold_ack hS (ne3_ne hi) ht hm) id
    · obtain ⟨s, rfl⟩ := shift_of ht
      rw [show s + 3 + 1 = (s + 1) + 3 by omega] at hm ⊢
      simp only [gl_ack_s, glT_s, s1] at hm ⊢
      exact A.H_ACK_DI (s + T0) (by omega) hm
  H_REQ_DI := by
    intro t hm
    by_cases ht : t < 3
    · exact absurd (cold_req hS ho ht hm) id
    · obtain ⟨s, rfl⟩ := shift_of ht
      rw [show s + 3 + 1 = (s + 1) + 3 by omega] at hm ⊢
      simp only [gl_req_s, glT_s, s1] at hm ⊢
      exact A.H_REQ_DI (s + T0) (by omega) hm
  H_LATCH_OPEN := by
    intro t hc
    by_cases ht : t < 3
    · rw [glT_lt c ht] at hc; exact absurd hc (by decide)
    · obtain ⟨s, rfl⟩ := shift_of ht
      simp only [gl_dat_s, glT_s] at hc ⊢; exact A.H_LATCH_OPEN (s + T0) (by omega) hc
  H_LATCH_HOLD := by
    intro t hc
    by_cases ht : t < 3
    · rw [gl_dat_pre o (by omega), gl_dat_pre o (by omega)]
    · obtain ⟨s, rfl⟩ := shift_of ht
      rw [show s + 3 + 1 = (s + 1) + 3 by omega] at hc ⊢
      simp only [gl_dat_s, glT_s, s1] at hc ⊢
      exact A.H_LATCH_HOLD (s + T0) (by omega) hc
  ic := glT_lt c (by decide)
  ii := gl_ack_lt i (by decide)
  io := by rw [gl_req_lt o (by decide)]; exact preR0 o

theorem glue_src (hS : AtS r T0) (z : Fin NC) (v : Nat) (hz : (!hot z || decide (z.val < 3)) = true)
    (A : SrcA r T0 z v) : Capstone.Src (gl r T0 z) v where
  H_LUT_SI := by
    intro t hm
    by_cases ht : t < 3
    · obtain ⟨hh, h1, hc⟩ := req_step_pre hS z ht hm
      simp only [hh, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hz
      rcases hc with ⟨rfl, _⟩ | ⟨rfl, h⟩
      · rw [h1, gl_ack_lt z (by decide)]; rfl
      · omega
    · obtain ⟨s, rfl⟩ := shift_of ht
      rw [show s + 3 + 1 = (s + 1) + 3 by omega] at hm ⊢
      simp only [gl_req_s, gl_ack_s, s1] at hm ⊢
      exact A.H_LUT_SI (s + T0) (by omega) hm
  dat := by
    intro t
    by_cases ht : t < 3
    · rw [gl_dat_lt z ht]; exact A.dat T0 (Nat.le_refl _)
    · obtain ⟨s, rfl⟩ := shift_of ht
      simp only [gl_dat_s]; exact A.dat (s + T0) (by omega)
  iz := by rw [gl_req_lt z (by decide)]; exact preR0 z

theorem glue_sink (hS : AtS r T0) (i : Fin NC) (A : SinkA r T0 i) : Ops.Gcd.Sink (gl r T0 i) where
  wire := by
    intro t hm
    by_cases ht : t < 3
    · obtain ⟨h3, rfl⟩ := ack_step_pre hS i ht hm
      rw [show (2 : Nat) + 1 = 0 + 3 from rfl, gl_ack_s, Nat.zero_add, hS.ack, gl_req_lt i (by decide)]
      simp [preR, h3]
    · obtain ⟨s, rfl⟩ := shift_of ht
      rw [show s + 3 + 1 = (s + 1) + 3 by omega] at hm ⊢
      simp only [gl_req_s, gl_ack_s, s1] at hm ⊢
      exact A.wire (s + T0) (by omega) hm
  init := gl_ack_lt i (by decide)

/-- **The glue for one operator**: C's gate model of the glued family follows from the gate
model after `T0` plus the reset state at `T0`, for every operator meeting `Side`. -/
theorem glue_cell (hS : AtS r T0) (sv : Nat → Nat) (k : K NC) (hs : Side k = true)
    (A : CellA r T0 sv k) : Cell (gl r T0) sv k := by
  cases k with
  | forkG i os =>
    simp only [Side, Bool.and_eq_true] at hs
    exact glue_fork hS i os hs.1 hs.2 A
  | forkH i os l hh d hs' =>
    simp only [Side, Bool.and_eq_true] at hs
    have := glue_fork hS i (os.map Prod.fst) hs.1 hs.2 A
    simpa [Cell, List.map_map] using this
  | join ins o e js jw =>
    simp only [Side, Bool.and_eq_true] at hs
    exact glue_join hS _ ins o (hot_f hs.1) hs.2 A
  | bjoin ins o ec ed =>
    simp only [Side, Bool.and_eq_true] at hs
    exact glue_join hS _ ins o (hot_f hs.1) hs.2 A
  | steerC j t f =>
    simp only [Side, Bool.and_eq_true] at hs
    exact glue_steer hS _ _ j t f hs.1.1 (hot_f hs.1.2) (hot_f hs.2) A
  | steerD j t f fd sw =>
    simp only [Side, Bool.and_eq_true] at hs
    exact glue_steer hS _ _ j t f hs.1.1 (hot_f hs.1.2) (hot_f hs.2) A
  | mux c x y z mw =>
    simp only [Side, Bool.and_eq_true] at hs
    obtain ⟨j0, j1, A⟩ := A
    exact ⟨_, _, glue_mux hS _ x y c z j0 j1 (hot_f hs.1.1.1) hs.1.1.2 hs.1.2 hs.2 A⟩
  | muxn c x0 x1 x2 z nw =>
    simp only [Side, Bool.and_eq_true] at hs
    obtain ⟨j, A⟩ := A
    exact ⟨_, glue_muxn hS _ x0 x1 x2 c z j (hot_f hs.1.1.1.1) hs.1.1.1.2 hs.1.1.2 hs.1.2 hs.2 A⟩
  | amerge x y z w =>
    simp only [Side, Bool.and_eq_true] at hs
    obtain ⟨g1, g2, A⟩ := A
    exact ⟨_, _, glue_amerge hS x y z g1 g2 (hot_f hs.1.1) hs.1.2 hs.2 A⟩
  | link i o =>
    simp only [Side, Bool.and_eq_true] at hs
    obtain ⟨c, A⟩ := A
    exact ⟨_, glue_link hS i o c (hot_f hs.1) hs.2 A⟩
  | src z which d => exact glue_src hS z _ hs A
  | sink i => exact glue_sink hS i A

end gluek

/-- Every gcd_hw operator meets `Side`. -/
theorem side_chk : ops.all Side = true := by decide +kernel

theorem side_all (o : Fin NO) : Side (opAt o) = true := List.all_eq_true.1 side_chk _ getD_mem

/-- **H_CELLS for the glued family**, from the reset state at `T0` and the gate models
after `T0`. -/
theorem glue_cells {r : Fin NC → Chan} {T0 : Nat} (sv : Nat → Nat) (hS : AtS r T0)
    (H_CELLS_AFTER : ∀ o : Fin NO, CellA r T0 sv (opAt o)) :
    ∀ o : Fin NO, Cell (gl r T0) sv (opAt o) :=
  fun o => glue_cell hS sv _ (side_all o) (H_CELLS_AFTER o)

end Formal.Cells.ResetCapstone
