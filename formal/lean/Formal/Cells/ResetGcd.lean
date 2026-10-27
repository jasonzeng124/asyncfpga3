import Formal.Cells.ResetGcdNet

/-!
# Probe Rst2 (shard B, gcd_hw capstone): the reset contract on the real control netlist

Notes: `formal/notes/B-reset-gcd.md`. Network: `ResetGcdNet.lean` (generated).

`ResetContract` proved the generic reset theorems (`ResetSpec` ⇒
`reset_ternary`, `reset_binary`) and checked them on a 35-node skeleton; the
whole-design facts (414 reset cells, frontier of 10 links, tokens) came from a
Python scan. Here the CONTROL netlist of gcd_hw itself (bdc_gcd + the gcd_rig
ring and samplers; 3322 nodes: rst, 64 data nets as free inputs, and every
control LUT output with its real INIT and pin map, delay lines element by
element) is a `TernarySound.Circ` (`gNet`), and every claim below is checked
by the kernel (`decide +kernel`, chunked).

Results:
* `gcd_spec`: `ResetSpec` holds for the whole network (every control node,
  rank ≤ 21), so
* `gcd_reset_ternary`: Kleene simulation from all-X with `rst = t` (every data
  net `x`) puts EVERY control node at its reset value after 21 + 2 steps;
* `gcd_reset_binary`: every bounded GMW run (gate bound `D`, wire bound `W`,
  per-pin read times, so rst fanout skew included), from ANY power-up state,
  with rst held at 1 on `(0, E]` and every data net doing anything, shows every
  control node at its reset value on `[(21 + 2)(D + W + 1), E]`;
* `gcd_reset_ones`: the control nodes whose reset value is 1 are exactly
  rst, the 9 arbiter state nodes (q), the 4 `bd_src` requests, the rig's
  `uenv1` token and the 2 elements of the rig's `upsnk` line (the p_end sink
  has consumed its copy of the token during reset); every other control node,
  in particular every link/pipe controller (`gcd_links_empty`), is 0;
* `gcd_frontier`, `gcd_frontier_fire`: at the simultaneous-release state
  (rst 0 at every pin, control nets at their reset values, data X) the nodes
  whose excitation differs from their value are exactly 10 `bd_c2n` link
  controllers, each with excitation 1, each fed by a token (env_c or a source);
* `gcd_post_definite`: every control node's post-release excitation is
  definite, although all 64 data nets are X;
* negative controls `neg_norst`, `neg_unguarded`: the per-node check fails
  when a link controller loses its rst pin or a steer's AND guard becomes OR.

Core Lean only. The import of the netlist (Verilog → `ResetGcdNet.lean`) is
done by an unverified Python generator; see the notes for what it trusts.
-/

namespace Formal.Cells.ResetGcd
open Formal.Cells Formal.Cells.TernarySound Formal.Cells.ResetContract

/-! ## The network -/

def gInfo (n : Nat) : NInfo := gTree.get n
def gNode (n : Nat) : Node := if n < gM then (gInfo n).node else .input
/-- gcd_hw's control netlist. -/
def gNet : Circ := ⟨gM, gNode⟩
/-- Control nodes: rst and every LUT output (data inputs are not control). -/
def gCtl (n : Nat) : Bool := decide (n < gM) && (gInfo n).ctl
def gRank (n : Nat) : Nat := (gInfo n).rank
def gR (n : Nat) : Bool := (gInfo n).rv
/-- During reset: `rst = t`, every data net `x`. -/
def gA (n : Nat) : K3 := if n = 0 then .t else .x
def maxRank : Nat := 21

/-- `H_LOCAL`/`H_IN` at node `n`, for a node function `nd` (the real one is
`gNode`; the negative controls pass a mutated one). -/
def localOK (nd : Nat → Node) (n : Nat) : Bool :=
  match nd n with
  | .input => !gCtl n || decide (gA n = K3.ofBool (gR n))
  | .gate init pins =>
    !gCtl n ||
      decide (lutK init (pins.map (srcK (Bst ⟨gM, nd⟩ gA gCtl gRank gR (gRank n))))
        = K3.ofBool (gR n))

/-- The simultaneous-release state: rst 0, control nets at their reset values,
data `x`. -/
def postB (i : Nat) : K3 := if i = 0 then .f else if gCtl i then K3.ofBool (gR i) else .x

/-- Excitation of node `n` at the release state. -/
def postExc (n : Nat) : K3 :=
  match gNode n with
  | .input => postB n
  | .gate init pins => lutK init (pins.map (srcK postB))

/-- The release-race state: rst `x` at every pin (falling, with any skew, or
glitching), every other control net at its reset value, data `x`. -/
def raceB (i : Nat) : K3 := if i = 0 then .x else if gCtl i then K3.ofBool (gR i) else .x

/-- Excitation of node `n` in the release-race state. -/
def raceExc (n : Nat) : K3 :=
  match gNode n with
  | .input => raceB n
  | .gate init pins => lutK init (pins.map (srcK raceB))

/-- The first-firing nodes (computed by the generator; checked below). -/
def frontierL : List Nat := [1696, 1931, 1938, 2182, 2189, 2196, 2432, 2439, 2596, 2603]
/-- Their request sources. -/
def frontierReq : List Nat := [3275, 1399, 1399, 308, 308, 308, 627, 627, 846, 846]
/-- The control nodes whose reset value is 1. -/
def onesL : List Nat := [0, 287, 308, 533, 606, 627, 825, 846, 1192, 1378, 1399, 1583, 1658, 1664, 3256, 3257, 3275]

def isC2n : Node → Bool
  | .gate init _ => init == I_c2n
  | .input => false

/-- Everything checked per node. -/
def nodeOK (n : Nat) : Bool :=
  localOK gNode n && (!gCtl n || decide (gRank n ≤ maxRank)) &&
    (!gCtl n || (decide (postExc n ≠ .x) &&
      (decide (n ≠ 0 ∧ postExc n ≠ K3.ofBool (gR n)) == frontierL.contains n) &&
      (gR n == onesL.contains n) &&
      (n == 0 || (decide (raceExc n ≠ K3.ofBool (gR n)) == frontierL.contains n))))

def chunkOK (lo k : Nat) : Bool := (List.range' lo k).all nodeOK

theorem chunk_mem {lo k : Nat} (h : chunkOK lo k = true) {n : Nat} (h1 : lo ≤ n)
    (h2 : n < lo + k) : nodeOK n = true :=
  List.all_eq_true.1 h n (List.mem_range'_1.2 ⟨h1, h2⟩)

/-! ## The kernel checks (chunked) -/

theorem ck0 : chunkOK 0 400 = true := by decide +kernel
theorem ck1 : chunkOK 400 400 = true := by decide +kernel
theorem ck2 : chunkOK 800 400 = true := by decide +kernel
theorem ck3 : chunkOK 1200 400 = true := by decide +kernel
theorem ck4 : chunkOK 1600 400 = true := by decide +kernel
theorem ck5 : chunkOK 2000 400 = true := by decide +kernel
theorem ck6 : chunkOK 2400 400 = true := by decide +kernel
theorem ck7 : chunkOK 2800 400 = true := by decide +kernel
theorem ck8 : chunkOK 3200 122 = true := by decide +kernel

theorem all_ok (n : Nat) (h : n < gM) : nodeOK n = true := by
  have hM : gM = 3322 := rfl
  by_cases h0 : n < 400
  · exact chunk_mem ck0 (by omega) (by omega)
  by_cases h1 : n < 800
  · exact chunk_mem ck1 (by omega) (by omega)
  by_cases h2 : n < 1200
  · exact chunk_mem ck2 (by omega) (by omega)
  by_cases h3 : n < 1600
  · exact chunk_mem ck3 (by omega) (by omega)
  by_cases h4 : n < 2000
  · exact chunk_mem ck4 (by omega) (by omega)
  by_cases h5 : n < 2400
  · exact chunk_mem ck5 (by omega) (by omega)
  by_cases h6 : n < 2800
  · exact chunk_mem ck6 (by omega) (by omega)
  by_cases h7 : n < 3200
  · exact chunk_mem ck7 (by omega) (by omega)
  exact chunk_mem ck8 (by omega) (by omega)

/-! ## Consequences -/

theorem gCtl_lt {n : Nat} (h : gCtl n = true) : n < gM := by
  simp only [gCtl, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1

theorem gNode_eq {n : Nat} (h : n < gM) : gNet.node n = (gInfo n).node := by
  show gNode n = _; simp only [gNode, h, ite_true]

theorem ok_of_ctl {n : Nat} (hc : gCtl n = true) : nodeOK n = true := all_ok n (gCtl_lt hc)

theorem local_of_ctl {n : Nat} (hc : gCtl n = true) : localOK gNode n = true := by
  have h := ok_of_ctl hc
  simp only [nodeOK, Bool.and_eq_true] at h
  exact h.1.1

theorem rank_of_ctl {n : Nat} (hc : gCtl n = true) : gRank n ≤ maxRank := by
  have h := ok_of_ctl hc
  simp only [nodeOK, Bool.and_eq_true, hc, Bool.not_true, Bool.false_or, decide_eq_true_eq] at h
  exact h.1.2

theorem post_of_ctl {n : Nat} (hc : gCtl n = true) :
    postExc n ≠ .x ∧ (decide (n ≠ 0 ∧ postExc n ≠ K3.ofBool (gR n)) == frontierL.contains n) = true ∧
      (gR n == onesL.contains n) = true ∧
      (n == 0 || (decide (raceExc n ≠ K3.ofBool (gR n)) == frontierL.contains n)) = true := by
  have h := ok_of_ctl hc
  simp only [nodeOK, Bool.and_eq_true, hc, Bool.not_true, Bool.false_or, decide_eq_true_eq] at h
  exact ⟨h.2.1.1.1, h.2.1.1.2, h.2.1.2, h.2.2⟩

/-- **gcd_hw's control network meets the reset specification** (every
control node; real INITs; every data net `x`). -/
theorem gcd_spec : ResetSpec gNet gA gCtl gRank gR where
  H_IN n hn hc := by
    have h := local_of_ctl hc
    have hn' : gNode n = .input := hn
    simp only [localOK, hn', hc, Bool.not_true, Bool.false_or, decide_eq_true_eq] at h
    exact h
  H_LOCAL n init pins hn hc := by
    have h := local_of_ctl hc
    have hn' : gNode n = .gate init pins := hn
    simp only [localOK, hn', hc, Bool.not_true, Bool.false_or, decide_eq_true_eq] at h
    exact h

/-- **Reset, Kleene, from all-X.** -/
theorem gcd_reset_ternary (n : Nat) (hc : gCtl n = true) :
    iter gNet gA (maxRank + 2) allX n = K3.ofBool (gR n) :=
  reset_ternary gcd_spec (maxRank + 1) n hc (by have := rank_of_ctl hc; omega)

/-- **Reset, binary, any power-up state, every bounded run.** `H_RST_HELD`:
the rst source is 1 on `(0, E]` (the data inputs are unconstrained: `gA` is
`x` on them). -/
theorem gcd_reset_binary {v : Nat → Nat → Bool} (Rn : Run gNet v) {D W : Nat}
    (hB : Bounded gNet v Rn D W) (E : Nat)
    (H_RST_HELD : ∀ k, 0 < k → k ≤ E → TernaryPhases.InputsIn gNet v gA k)
    (n : Nat) (hc : gCtl n = true) :
    ∀ k, (maxRank + 2) * (D + W + 1) ≤ k → k ≤ E → v k n = gR n :=
  reset_binary gcd_spec Rn hB E H_RST_HELD (maxRank + 1) n hc
    (by have := rank_of_ctl hc; omega)

/-- **Which control nodes are 1 under reset**: exactly these 17:
  - 0 `rst`
  - 287 `ucontrol_merge2.uarb1.ustate.O6`
  - 308 `usource3.u`
  - 533 `ucontrol_merge3.uarb1.ustate.O6`
  - 606 `ucontrol_merge4.uarb1.ustate.O6`
  - 627 `usource5.u`
  - 825 `ucontrol_merge6.uarb1.ustate.O6`
  - 846 `usource7.u`
  - 1192 `ucontrol_merge9.uarb1.ustate.O6`
  - 1378 `ucontrol_merge10.uarb1.ustate.O6`
  - 1399 `usource13.u`
  - 1583 `ucontrol_merge11.uarb1.ustate.O6`
  - 1658 `ucontrol_merge12.uarb1.ustate.O6`
  - 1664 `ucontrol_merge12.uarb2.ustate.O6`
  - 3256 `urig.upsnk.g[0].u`
  - 3257 `urig.upsnk.g[1].u`
  - 3275 `urig.uenv1.u` -/
theorem gcd_reset_ones (n : Nat) (hc : gCtl n = true) : gR n = true ↔ n ∈ onesL := by
  have h := (post_of_ctl hc).2.2.1
  rw [beq_iff_eq] at h
  rw [h, List.contains_iff_mem]

/-- Every node of `onesL` is a control node. -/
theorem onesL_ctl : onesL.all gCtl = true := by decide +kernel

/-- **Every link/pipe controller (every `bd_c2n`) is empty (0) under reset.** -/
theorem gcd_links_empty : onesL.all (fun n => !isC2n (gNode n)) = true := by decide +kernel

theorem gcd_links_empty' (n : Nat) (hc : gCtl n = true) (hl : isC2n (gNode n) = true) :
    gR n = false := by
  cases hr : gR n
  · rfl
  · have hm := (gcd_reset_ones n hc).1 hr
    have := List.all_eq_true.1 gcd_links_empty n hm
    rw [hl] at this; exact absurd this (by decide)

/-- **The frontier.** At the simultaneous-release state, the control nodes
(other than rst) whose excitation differs from their reset value are exactly
`frontierL`:
  - 1696 `ulink_n1__1.ctl.u` (request from node 3275, `urig.uenv1.u`)
  - 1931 `ulink_n155__0.ctl.u` (request from node 1399, `usource13.u`)
  - 1938 `ulink_n155__1.ctl.u` (request from node 1399, `usource13.u`)
  - 2182 `ulink_n36__0.ctl.u` (request from node 308, `usource3.u`)
  - 2189 `ulink_n36__1.ctl.u` (request from node 308, `usource3.u`)
  - 2196 `ulink_n36__2.ctl.u` (request from node 308, `usource3.u`)
  - 2432 `ulink_n68__0.ctl.u` (request from node 627, `usource5.u`)
  - 2439 `ulink_n68__1.ctl.u` (request from node 627, `usource5.u`)
  - 2596 `ulink_n94__0.ctl.u` (request from node 846, `usource7.u`)
  - 2603 `ulink_n94__1.ctl.u` (request from node 846, `usource7.u`) -/
theorem gcd_frontier (n : Nat) (hc : gCtl n = true) :
    (n ≠ 0 ∧ postExc n ≠ K3.ofBool (gR n)) ↔ n ∈ frontierL := by
  have h := (post_of_ctl hc).2.1
  rw [beq_iff_eq, ← List.contains_iff_mem] at *
  constructor
  · intro hh; rw [← h]; exact decide_eq_true hh
  · intro hh; rw [← h] at hh; exact of_decide_eq_true hh

def frontOK (n r : Nat) : Bool :=
  gCtl n && postExc n == .t && !gR n &&
    (match gNode n with
     | .gate init pins => init == I_c2n && pins == [p r, pins.getD 1 (.const false), p n, p 0, k0, k0]
     | .input => false) &&
    gR r && gCtl r

/-- **Each frontier node fires**: a `bd_c2n` link controller (own feedback on
I2, rst on I3), reset to 0 (empty), excitation 1 at release, whose request pin
I0 is a control node at 1 during reset (the token: `uenv1` or a `bd_src`). -/
theorem gcd_frontier_fire : (frontierL.zip frontierReq).all (fun q => frontOK q.1 q.2) = true ∧
    frontierL.length = 10 := by decide +kernel

/-- **All excitations definite at release** although every data net is `x`. -/
theorem gcd_post_definite (n : Nat) (hc : gCtl n = true) : postExc n ≠ .x :=
  (post_of_ctl hc).1

/-! ## Census (ties the import to the scan of `B-reset-contract.md`) -/

/-- Gates with INIT `i` that read rst (node 0) on some pin. -/
def censusOf (i : Nat) : Nat :=
  (List.range gM).countP fun n =>
    match gNode n with
    | .gate init pins => init == i && pins.contains (p 0)
    | .input => false

/-- Every reader of rst. -/
def rstReaders : Nat :=
  (List.range gM).countP fun n =>
    match gNode n with
    | .gate _ pins => pins.contains (p 0)
    | .input => false

/-- **414 reset-carrying state LUTs**: 153 `bd_c2` (joins, fork-ack trees,
mux/muxn3/arbiter acks), 185 `bd_c2n` (link/pipe controllers, `uenv0`),
1 `bd_c2n_set` (`uenv1`), 10 `bd_c3`, 14 `bd_c4`, 21 + 21 `bd_mux` joins,
9 arbiter state O6; plus the 9 arbiter O5 (R0) that also read rst: 423 rst
pins. -/
theorem gcd_census :
    [I_c2, I_c2n, I_c2n_set, I_c3, I_c4, I_uj0, I_uj1, I_arb, I_arb5].map censusOf =
      [153, 185, 1, 10, 14, 21, 21, 9, 9] ∧ rstReaders = 423 := by
  decide +kernel

/-! ## Release: nothing moves before a frontier link controller does -/

/-- Every control node other than rst is a gate. -/
theorem ctl_gate {n : Nat} (hc : gCtl n = true) (h0 : n ≠ 0) :
    ∃ init pins, gNode n = .gate init pins := by
  have h := local_of_ctl hc
  cases hn : gNode n with
  | gate init pins => exact ⟨init, pins, rfl⟩
  | input =>
    simp only [localOK, hn, hc, Bool.not_true, Bool.false_or, decide_eq_true_eq, gA, h0,
      ite_false] at h
    cases hr : gR n <;> rw [hr] at h <;> exact absurd h (by decide)

/-- In the release-race state, every control node outside the frontier is
excited to its own reset value. -/
theorem race_hold {n : Nat} (hc : gCtl n = true) (h0 : n ≠ 0) (hf : n ∉ frontierL) :
    raceExc n = K3.ofBool (gR n) := by
  have h := (post_of_ctl hc).2.2.2
  have h0' : (n == 0) = false := by simp [h0]
  rw [h0', Bool.false_or, beq_iff_eq] at h
  have hf' : frontierL.contains n = false := by
    cases hh : frontierL.contains n
    · rfl
    · exact absurd (List.contains_iff_mem.1 hh) hf
  rw [hf'] at h
  exact Classical.byContradiction fun hne => by simp [hne] at h

/-- **Release quiet (whole network, GMW, any rst skew).** Take a run whose
wires are at most `W` steps old. Suppose every control node except rst is at
its reset value on `[k0 - W, k0]` (`H_SETTLED`, given by `gcd_reset_binary`)
and, from `k0` to `T`, no frontier link controller has left its reset value
(`H_FRONT_HOLD`). Then no control node leaves its reset value on `[k0, T]`,
whatever rst and every data net do from `k0` on: rst may release with any
per-pin skew, or glitch. -/
theorem gcd_release_quiet {v : Nat → Nat → Bool} (Rn : Run gNet v) {W : Nat}
    (H_WIRE_BOUND : ∀ k j p, k ≤ Rn.rd k j p + W) (k0 T : Nat)
    (H_SETTLED : ∀ k n, k0 ≤ k + W → k ≤ k0 → gCtl n = true → n ≠ 0 → v k n = gR n)
    (H_FRONT_HOLD : ∀ k n, n ∈ frontierL → k0 ≤ k → k ≤ T → v k n = gR n) :
    ∀ k n, k0 ≤ k → k ≤ T → gCtl n = true → n ≠ 0 → v k n = gR n := by
  have key : ∀ k, k ≤ T → ∀ j, k0 ≤ j + W → j ≤ k →
      ∀ n, gCtl n = true → n ≠ 0 → v j n = gR n := by
    intro k
    induction k with
    | zero =>
      intro _ j hj hjk n hc h0
      exact H_SETTLED j n hj (by omega) hc h0
    | succ k ih =>
      intro hT j hj hjk n hc h0
      rcases Nat.lt_or_ge j (k + 1) with hlt | hge
      · exact ih (by omega) j hj (by omega) n hc h0
      have hj' : j = k + 1 := by omega
      subst hj'
      by_cases hk0 : k + 1 ≤ k0
      · exact H_SETTLED (k + 1) n hj hk0 hc h0
      by_cases hf : n ∈ frontierL
      · exact H_FRONT_HOLD (k + 1) n hf (by omega) hT
      obtain ⟨init, pins, hn⟩ := ctl_gate hc h0
      have hn' : gNet.node n = .gate init pins := hn
      rcases Rn.gate k n init pins hn' with h | h
      · rw [h]; exact ih (by omega) k (by omega) (Nat.le_refl k) n hc h0
      · rw [h]
        have hr := race_hold hc h0 hf
        simp only [raceExc, hn] at hr
        have hs := lutK_sound init (pins_forall2 raceB (fun p i => v (Rn.rd k n p) i) ?_ pins 0)
        · rw [hr] at hs; exact (admits_ofBool_iff _ _).1 hs
        intro q i
        have h1 := Rn.rd_le k n q
        have h2 := H_WIRE_BOUND k n q
        unfold raceB
        by_cases hi : i = 0
        · simp only [hi, ite_true]; rfl
        · simp only [hi, ite_false]
          cases hci : gCtl i
          · rfl
          · simp only [ite_true]
            rw [admits_ofBool_iff]
            exact ih (by omega) _ (by omega) h1 i hci hi
  intro k n h1 h2 hc h0
  exact key k h2 k (by omega) (Nat.le_refl k) n hc h0

/-- **Reset, then release, composed (GMW).** Every bounded run, from ANY
power-up state, with rst held at 1 on `(0, E]` where
`E ≥ (maxRank + 2)(D + W + 1) + W`, and with rst and data arbitrary after `E`:
as long as no frontier link controller has moved (`[E, T]`), every control
node is at its reset value on `[(maxRank + 2)(D + W + 1), T]`. -/
theorem gcd_reset_release {v : Nat → Nat → Bool} (Rn : Run gNet v) {D W : Nat}
    (hB : Bounded gNet v Rn D W) (E T : Nat)
    (H_RST_HELD : ∀ k, 0 < k → k ≤ E → TernaryPhases.InputsIn gNet v gA k)
    (H_HOLD_LONG : (maxRank + 2) * (D + W + 1) + W ≤ E)
    (H_FRONT_HOLD : ∀ k n, n ∈ frontierL → E ≤ k → k ≤ T → v k n = gR n) :
    ∀ k n, (maxRank + 2) * (D + W + 1) ≤ k → k ≤ T → gCtl n = true → n ≠ 0 →
      v k n = gR n := by
  intro k n h1 h2 hc h0
  by_cases hk : k ≤ E
  · exact gcd_reset_binary Rn hB E H_RST_HELD n hc k h1 hk
  · exact gcd_release_quiet Rn hB.wire E T
      (fun j m hj hjE hcm _ => gcd_reset_binary Rn hB E H_RST_HELD m hcm j (by omega) hjE)
      H_FRONT_HOLD k n (by omega) h2 hc h0

/-! ## Negative controls (the check can fail) -/

/-- Tie `ulink_n1__1`'s rst pin to 0: its power-up X is never cleared, the
node's check fails. -/
theorem neg_norst :
    localOK (fun n => if n = 1696 then .gate I_c2n [p 3275, p 98, p 1696, k0, k0, k0] else gNode n) 1696 = false := by
  decide +kernel

/-- Make `ucond_br9`'s req1 (`bd_steer` O6, AND of request and the X select)
an OR of the same pins: the X escapes into control, the check fails. -/
theorem neg_unguarded :
    localOK (fun n => if n = 101 then .gate I_or2 [p 99, p 1] else gNode n) 101 = false := by
  decide +kernel

end Formal.Cells.ResetGcd
