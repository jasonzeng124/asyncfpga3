import Formal.Cells.IpowCells
import Formal.Cells.CTreeExact
import Formal.Cells.ArbPin

/-!
# Probe Bbr (shard B): model bridges for IpowCells' contract fields

`IpowCells` (probe Bipw) derives C's H_CELLS for ipow from per-cell `Contract`s whose fields
H_CTREE_ATOMIC, H_SEL_PIN, H_DELAY_LUMPED and the arbiter grant fields were bare hypotheses,
with B's theorems for them cited, not used. This file proves those fields (as IpowCells states
them, imported) from B's theorems and their own hypotheses, where that is possible, and gives
counter-runs where it is not. Notes: `formal/notes/B-contract-bridge.md`.

## Assumed / proved / NOT covered

**Assumed** (B's model hypotheses, every one named):
* tree (`CTreeB`): `CTreeExact`'s model (H_PIN_READ per node, monotone read maps H_PIN_FIFO in
  the box, H_LEAF, H_ACK, feedback maps in the box), **H_CTREE_LOOP** (`Cond`), every read
  lower bound `>= 1` (H_LO_POS), and H_RUN: every finite prefix of the run is a prefix of one
  B-model run (so finitely-switching leaves are allowed).
* select pins (`SelPin`): `LibGapSteer.steer_tokens`' H_REQ_TOK, H_S_STABLE, H_SETUP_PIN,
  H_HOLD_PIN with the request read through C's one tick (`Rd.const 1`), plus H_SEL_DEC (during
  token `k` the bus decodes to the token's select `v k`); the steer outputs obey B's
  H_PIN_READ (level form, real INIT `outB`); the mux's `uj0`/`uj1` are `FbCel` on the PHYSICAL
  select pin.
* mux request path (`ReqPath`): `uor -> bd_delay -> z_req` is ONE read map (H_OR_SAME_PATH)
  of B's per-pin model, monotone (H_PIN_FIFO), minimum delay `>= 1`, and **H_PULSE_WIDTH**
  (the OR's input holds for the path's maximum delay after each change).

**Proved:**
* `ctreeB_cel`, `fbCel_of_ctreeB` (from `CTreeExact.tree_suff`, the sufficient half of
  `tree_box_exact`): a `bd_ctree` of any shape meets `Join.cel`, and `FbCel cgate` exactly as
  IpowCells' contract states it (H_CTREE_ATOMIC derived; `leaves5`/`sh5` for ipow's
  `uselect0`, `leaves6`/`sh6` for gcd_hw's 6-way fork). `root_phase`, `root_edge_leaves`.
* `fbCel_iff_si`: **IpowCells' `FbCel` is equivalent to the SI step** (its H_FB_ROUTE /
  H_RT_FB are existential and met by `qp = o`, `lo = hi = 0`): a finding about `FbCel`.
* `selPin_ok`, `steer_lut_of_pins`: H_SEL_PIN (`SteerC.H_LUT_SI`) from B's per-pin steer model;
  `uj0_of_pin`/`uj1_of_pin`: the mux's select-pin step from `FbCel` on the physical pin.
* `lumped_of_fifo`: H_DELAY_LUMPED (ungated path) from a FIFO read map + H_PULSE_WIDTH;
  `lumped_needs_fifo`: counter-run with a non-monotone map (LibGapDelay's H_PIN_READ allows
  it): a runt on `z` breaks the lumped node although H_PULSE_WIDTH holds.
* `arb_excl_not_derivable`: counter-run (B's `ArbPin.su_osc_instance`): H_ARB_EXCL does not
  follow from B's per-pin arbiter model; `arb_excl_of_window`: it does inside B's window
  (`ArbPin.su_box_iff`), for ONE arbitration of single-step requests.
* `contract_of_contractB`: `ContractB` (the B-model contract) implies IpowCells' `Contract`;
  `cell_of_contractB`, `ipow_safe_of_contracts'` (C-8y's safety with `ContractB`),
  `ipow_contractsB_satisfiable` (non-vacuity: one run meets all 83 `ContractB`s, H_BUNDLE,
  H_START_ONCE), `ctreeB_switching` (a switching tree meets `CTreeB`).

**NOT covered:** the arbiter grant fields H_ARB1 / H_ARB2 / H_ARB_EXCL / H_AMERGE_RTZ on
multi-token runs of the held `bd_arbiter` (B's arbiter theorems are single-scenario; they stay
hypotheses of `AMergeC`); the GATED H_DELAY_LUMPED (`bd_delay_gated` after a join's C-element
or the arbiter's `ustate.O5`: lumping two SI nodes needs an extra wait hypothesis, not in
LibGapDelay/GcdCells); the uor's two pins on different read maps; the select driver's own
timing (`S0`/`S1` are free parameters, as in LibGapSteer); routed numbers.
-/

namespace Formal.Cells.ContractBridge
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.Ops.Gen Formal.Gen Formal.Gen.Cells
open Formal.Cells.IpowCells (FbCel cgate cgate_eq celL celL_move)
open Formal.Cells.CTreeExact (Tr Path Wf InT Sol Good iv Tm Tf LeafOK HAck NS Cond PhaseTr V ofPh
  ofPh_phase iv_phase tree_suff arrive_bound anc_bound distL distL_nonneg maxmin_nonneg rho rho_ge
  ph_find lv sh5 wf_sh5 und_of_InT)
open Formal.Cells.NecessityMerge (Mono)
open Formal.Cells.LibGapSteer (Rd)

/-! ## 1. H_CTREE_ATOMIC from `CTreeExact.tree_box_exact` -/

/-- A phase trace changes exactly at its phase times. -/
theorem phase_change {x : Int → Bool} {T : Nat → Int} (hP : PhaseTr x T) {τ : Int}
    (h : x τ ≠ x (τ - 1)) : ∃ k, τ = T k ∧ x τ = V k := by
  by_cases h0 : τ < T 0
  · exact absurd ((hP.pre τ h0).trans (hP.pre (τ - 1) (by omega)).symm) h
  · obtain ⟨k, h1, h2⟩ := ph_find hP.inc τ (by omega)
    refine ⟨k, ?_, hP.ph k τ h1 h2⟩
    apply Classical.byContradiction; intro hne
    exact h ((hP.ph k τ h1 h2).trans (hP.ph k (τ - 1) (by omega) (by omega)).symm)

theorem distL_pos {lo : Path → Int} (hlo : ∀ q, 1 ≤ lo q) :
    ∀ (a : Nat) (p : Path), 1 ≤ distL lo (a :: p) := by
  intro a p
  have := distL_nonneg (lo := lo) (fun q => by have := hlo q; omega) p
  have := hlo (a :: p)
  simp only [distL]; omega

/-- Every leaf of a node sits at a nonempty path. -/
theorem leaf_path_ne {k : Nat} {cs : Fin k → Tr} {q : Path} (h : InT (.node k cs) [] q .leaf) :
    ∃ a p, q = a :: p := by
  cases h with
  | child j h' =>
    obtain ⟨r, hr⟩ := und_of_InT h'
    cases r with
    | nil => exact ⟨j.1, [], by simpa using hr⟩
    | cons a r => exact ⟨a, r ++ [j.1], by simpa using hr⟩

/-- **The root of a tree in B's model is a phase trace** (from `tree_suff`): under
`CTreeExact`'s hypotheses and H_CTREE_LOOP, every possible root output `O` is the ideal
trace, which switches exactly at `Tm .. k` to `V k`, and every phase-`k` root edge is at
least 1 ps (the read lower bound) after every leaf's phase-`k` switch. -/
theorem root_phase {k : Nat} {cs : Fin k → Tr} (hwf : Wf (.node k cs))
    {lo hi Qlo Qhi : Path → Int} {E : Int} (hlo1 : ∀ q, 1 ≤ lo q) (hQ1 : ∀ q, 1 ≤ Qlo q)
    (hE : 1 ≤ E) (hC : Cond lo Qhi E (.node k cs))
    {rd : Path → Rd} {σ : Path → Nat → Int} {fb : Path → Rd} (hm : ∀ q, Mono (rd q))
    (hbox : ∀ q, lo q ≤ (rd q).lo ∧ (rd q).hi ≤ hi q)
    (hleaf : ∀ q, InT (.node k cs) [] q .leaf → LeafOK σ q) (hack : HAck rd σ E (.node k cs))
    (hfb : ∀ q, Qlo q ≤ (fb q).lo ∧ (fb q).hi ≤ Qhi q)
    {O : Int → Bool} (hO : Sol rd σ fb (.node k cs) [] O) :
    O = iv rd σ (.node k cs) [] ∧ PhaseTr O (Tm rd σ (.node k cs) []) ∧
      ∀ q, InT (.node k cs) [] q .leaf → ∀ kk, σ q kk + 1 ≤ Tm rd σ (.node k cs) [] kk := by
  have hlo : ∀ q, 0 ≤ lo q := fun q => by have := hlo1 q; omega
  have hG := tree_suff (hi := hi) (Qlo := Qlo) hwf hlo hQ1 hE hC rd σ hm hbox hleaf hack fb hfb
  have hOe : O = iv rd σ (.node k cs) [] := hG.1 O hO
  have hrl : ∀ q x, x + lo q ≤ rho (rd q) x := fun q x => by
    have := rho_ge (rd q) (hm q) x; have := (hbox q).1; omega
  have hlo' : ∀ q, 0 ≤ (rd q).lo := fun q => by have := (hbox q).1; have := hlo q; omega
  have hNS : ∀ p0 s0, InT (.node k cs) [] p0 s0 → NS rd σ s0 p0 := by
    intro p0 s0 hin
    cases s0 with
    | leaf => trivial
    | node k' cs' =>
      simp only [NS]; intro kk j
      have := arrive_bound hrl hwf hack hin kk j
      have := distL_nonneg hlo p0; have := maxmin_nonneg hlo (cs' j) (j.1 :: p0)
      have := hlo (j.1 :: p0)
      omega
  have hPh := (iv_phase hm hlo' (.node k cs) [] hwf hleaf hNS).1
  refine ⟨hOe, hOe ▸ hPh, fun q hq kk => ?_⟩
  have hB : σ q kk + distL lo q ≤ Tm rd σ (.node k cs) [] kk + 0 :=
    anc_bound hrl (fun q => σ q kk) hq
  obtain ⟨a, p, rfl⟩ := leaf_path_ne hq
  have hd := distL_pos hlo1 a p
  omega

/-- **Root edge sees every leaf already at its new value** (B's tree model). Under
`CTreeExact`'s hypotheses (monotone read maps in the box, H_LEAF, H_ACK, feedback maps in
the box) and H_CTREE_LOOP (`Cond`), with every read lower bound at least 1 ps, every
possible root output `O` changes at `τ` only to the value every leaf has at `τ - 1`. -/
theorem root_edge_leaves {k : Nat} {cs : Fin k → Tr} (hwf : Wf (.node k cs))
    {lo hi Qlo Qhi : Path → Int} {E : Int} (hlo1 : ∀ q, 1 ≤ lo q) (hQ1 : ∀ q, 1 ≤ Qlo q)
    (hE : 1 ≤ E) (hC : Cond lo Qhi E (.node k cs))
    {rd : Path → Rd} {σ : Path → Nat → Int} {fb : Path → Rd} (hm : ∀ q, Mono (rd q))
    (hbox : ∀ q, lo q ≤ (rd q).lo ∧ (rd q).hi ≤ hi q)
    (hleaf : ∀ q, InT (.node k cs) [] q .leaf → LeafOK σ q) (hack : HAck rd σ E (.node k cs))
    (hfb : ∀ q, Qlo q ≤ (fb q).lo ∧ (fb q).hi ≤ Qhi q)
    {O : Int → Bool} (hO : Sol rd σ fb (.node k cs) [] O) :
    ∀ τ, O τ ≠ O (τ - 1) → ∀ q, InT (.node k cs) [] q .leaf → ofPh (σ q) (τ - 1) = O τ := by
  obtain ⟨_, hPh, hle⟩ := root_phase (hi := hi) hwf hlo1 hQ1 hE hC hm hbox hleaf hack hfb hO
  intro τ hτ q hq
  obtain ⟨kk, hk, hv⟩ := phase_change hPh hτ
  rw [hv]
  have hL := ofPh_phase (hleaf q hq).1
  have hA := hack q hq kk
  have hB := hle q hq kk
  exact hL.ph kk _ (by omega) (by omega)

/-- B's tree model, prefix form: up to `N`, the node's output `o` and its input vector `xs`
(in the order `leaves`) coincide with ONE run of `CTreeExact`'s model in the box. -/
def BRun (tr : Tr) (lo hi Qlo Qhi : Path → Int) (E : Int) (leaves : List Path)
    (xs : Nat → List Bool) (o : Trace) (N : Nat) : Prop :=
  ∃ (rd : Path → Rd) (σ : Path → Nat → Int) (fb : Path → Rd) (O : Int → Bool),
    (∀ q, Mono (rd q)) ∧ (∀ q, lo q ≤ (rd q).lo ∧ (rd q).hi ≤ hi q) ∧
    (∀ q, InT tr [] q .leaf → LeafOK σ q) ∧ HAck rd σ E tr ∧
    (∀ q, Qlo q ≤ (fb q).lo ∧ (fb q).hi ≤ Qhi q) ∧ Sol rd σ fb tr [] O ∧
    ∀ u : Nat, u ≤ N → o u = O u ∧ xs u = leaves.map (fun q => ofPh (σ q) u)

/-- **CTreeB**: the request node of a join is a REAL C-element tree of shape `tr`
(`bd_ctree`), in B's per-pin model (`CTreeExact`), with H_CTREE_LOOP (`Cond`), every read lower
bound `>= 1` ps, `Qlo >= 1`, `E >= 1`, its leaves listed in input order, and every finite
prefix of the run a prefix of a B-model run (`BRun`). -/
structure CTreeB (tr : Tr) (lo hi Qlo Qhi : Path → Int) (E : Int) (leaves : List Path)
    (xs : Nat → List Bool) (o : Trace) : Prop where
  wf : Wf tr
  node : ∃ k cs, tr = .node k cs
  H_LO_POS : ∀ q, 1 ≤ lo q
  H_QLO : ∀ q, 1 ≤ Qlo q
  H_E : 1 ≤ E
  H_CTREE_LOOP : Cond lo Qhi E tr
  H_LEAVES : ∀ q ∈ leaves, InT tr [] q .leaf
  H_RUN : ∀ N, BRun tr lo hi Qlo Qhi E leaves xs o N

/-- **H_CTREE_ATOMIC's use, derived**: a `CTreeB` node meets C's `Join.cel` step on its
inputs (every input already at the output's new value one tick before it changes). -/
theorem ctreeB_cel {tr : Tr} {lo hi Qlo Qhi : Path → Int} {E : Int} {leaves : List Path}
    {xs : Nat → List Bool} {o : Trace} (h : CTreeB tr lo hi Qlo Qhi E leaves xs o) :
    ∀ t, o (t + 1) ≠ o t → ∀ x ∈ xs t, x = o (t + 1) := by
  intro t ht x hx
  obtain ⟨k, cs, rfl⟩ := h.node
  obtain ⟨rd, σ, fb, O, hm, hbox, hleaf, hack, hfb, hO, hag⟩ := h.H_RUN (t + 1)
  obtain ⟨e1, _⟩ := hag (t + 1) (Nat.le_refl _)
  obtain ⟨e0, ex⟩ := hag t (Nat.le_succ t)
  rw [ex] at hx
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
  have key := root_edge_leaves h.wf h.H_LO_POS h.H_QLO h.H_E h.H_CTREE_LOOP hm hbox hleaf hack hfb hO
    ((t + 1 : Nat) : Int) (by
      rw [show ((t + 1 : Nat) : Int) - 1 = ((t : Nat) : Int) by omega, ← e1, ← e0]; exact ht)
    q (h.H_LEAVES q hq)
  rw [show ((t + 1 : Nat) : Int) - 1 = ((t : Nat) : Int) by omega] at key
  rw [key, e1]

/-- The leaves of `bd_ctree N=5` = `sh5 = C2(C4(a0..a3), a4)`, in input order. -/
def leaves5 : List Path := [[0, 0], [1, 0], [2, 0], [3, 0], [1]]

theorem leaves5_in : ∀ q ∈ leaves5, InT sh5 [] q .leaf := by
  intro q hq
  have inner : ∀ i : Fin 4, InT sh5 [] [i.1, 0] .leaf := fun i =>
    InT.child (k := 2) ⟨0, by decide⟩
      (show InT (lv 4) [0] [i.1, 0] .leaf from InT.child i (InT.refl _ _))
  simp only [leaves5, List.mem_cons, List.mem_nil_iff, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact inner ⟨0, by decide⟩
  · exact inner ⟨1, by decide⟩
  · exact inner ⟨2, by decide⟩
  · exact inner ⟨3, by decide⟩
  · exact InT.child (k := 2) ⟨1, by decide⟩ (show InT .leaf [1] [1] .leaf from InT.refl _ _)


/-! ### Non-vacuity of `CTreeB` (B's own run, switching) -/

theorem maxmin_sh5 : CTreeExact.MaxMin (fun _ => (1 : Int)) sh5 [] = 2 := by
  simp only [sh5, lv, CTreeExact.MaxMin, CTreeExact.fmx]; decide

/-- H_CTREE_LOOP holds for every tree when every loop bound is within `E + lo` (uniform). -/
theorem cond_const (tr : Tr) (l Qh E : Int) (hl : 0 ≤ l) (h : Qh ≤ E + l) :
    Cond (fun _ => l) (fun _ => Qh) E tr := by
  intro p0 k cs _ j
  have := distL_nonneg (lo := fun _ => l) (fun _ => hl) p0
  have := maxmin_nonneg (lo := fun _ => l) (fun _ => hl) (cs j) (j.1 :: p0)
  show Qh ≤ distL (fun _ => l) p0 + E + CTreeExact.MaxMin (fun _ => l) (cs j) (j.1 :: p0) + l
  omega

/-- The uniform box used by the witnesses: every read 1 ps, every loop 1 ps, `E = 1`. -/
theorem sh5_static : Wf sh5 ∧ Cond (fun _ => 1) (fun _ => 1) 1 sh5 :=
  ⟨wf_sh5, cond_const sh5 1 1 1 (by decide) (by decide)⟩

/-- Witness read maps: every read and loop a 1 ps transport. -/
def rd1 : Path → Rd := fun _ => Rd.const 1
/-- Witness leaf schedule: every leaf switches at `B + 10 k`. -/
def σw (B : Int) : Path → Nat → Int := fun _ k => B + 10 * (k : Int)

theorem σw_inc (B : Int) (q : Path) : ∀ k, σw B q k < σw B q (k + 1) := by
  intro k; simp only [σw]; omega

/-- The witness run meets every hypothesis of B's tree model (box 1 ps, `E = 1`). -/
theorem sh5_run (B : Int) (hB : 0 ≤ B) :
    let rd := rd1
    let σ := σw B
    (∀ q, Mono (rd q)) ∧ (∀ q, (1 : Int) ≤ (rd q).lo ∧ (rd q).hi ≤ 1) ∧
      (∀ q, InT sh5 [] q .leaf → LeafOK σ q) ∧ HAck rd σ 1 sh5 := by
  intro rd σ
  refine ⟨fun _ => NecessityMerge.const_mono 1, fun _ => ⟨Int.le_refl _, Int.le_refl _⟩,
    fun _ _ => ⟨fun k => by show B + 10 * ((k : Nat) : Int) < B + 10 * ((k + 1 : Nat) : Int); omega,
      by show (0 : Int) ≤ B + 10 * ((0 : Nat) : Int); omega⟩, ?_⟩
  intro q _ k
  have := CTreeExact.up_bound (lo := fun _ => 1) (rd := rd1)
    (fun q x => by rw [rd1, CTreeExact.rho_const]; exact Int.le_refl _)
    (fun _ => B + 10 * (k : Int)) (B + 10 * (k : Int)) sh5 [] wf_sh5 (fun _ _ => Int.le_refl _)
  rw [maxmin_sh5] at this
  show Tf rd1 (fun _ => B + 10 * (k : Int)) sh5 [] + 1 ≤ B + 10 * ((k + 1 : Nat) : Int)
  omega

/-- **`ctreeB_switching`**: B's own `bd_ctree N=5` run (leaves at `10 k`, every delay 1 ps)
meets `CTreeB`, and its root really switches. So `CTreeB` (hence `ctreeB_cel`) is not
vacuous on a switching tree. -/
theorem ctreeB_switching :
    ∃ (xs : Nat → List Bool) (o : Trace),
      CTreeB sh5 (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) 1 leaves5 xs o ∧
      ∃ t, o (t + 1) ≠ o t := by
  obtain ⟨hm, hbox, hleaf, hack⟩ := sh5_run 0 (Int.le_refl 0)
  have hfb : ∀ q : Path, (1 : Int) ≤ (rd1 q).lo ∧ (rd1 q).hi ≤ 1 :=
    fun _ => ⟨Int.le_refl _, Int.le_refl _⟩
  have hO := CTreeExact.sol_rv (rd := rd1) (σ := σw 0) (fb := rd1) (fun _ u => by
    show u - 1 ≤ u - 1; exact Int.le_refl _) sh5 []
  refine ⟨fun u => leaves5.map (fun q => ofPh (σw 0 q) u), fun u => CTreeExact.rv rd1 (σw 0) rd1 sh5 [] u,
    ⟨wf_sh5, ⟨2, _, rfl⟩, fun _ => Int.le_refl _, fun _ => Int.le_refl _, by decide,
      sh5_static.2, leaves5_in,
      fun N => ⟨rd1, σw 0, rd1, _, hm, hbox, hleaf, hack, hfb, hO, fun u _ => ⟨rfl, rfl⟩⟩⟩, ?_⟩
  obtain ⟨_, hPh, hle⟩ := root_phase (hi := fun _ => 1) wf_sh5 (fun _ => Int.le_refl _)
    (fun _ => Int.le_refl _) (by decide) sh5_static.2 hm hbox hleaf hack hfb hO
  have hPh : PhaseTr (CTreeExact.rv rd1 (σw 0) rd1 sh5 []) (Tm rd1 (σw 0) sh5 []) := hPh
  have h1 : σw 0 [1] 0 + 1 ≤ Tm rd1 (σw 0) sh5 [] 0 := hle [1] (leaves5_in [1] (by simp [leaves5])) 0
  have hσ : σw 0 [1] 0 = 0 := by simp [σw]
  have e1 := hPh.ph 0 (Tm rd1 (σw 0) sh5 [] 0) (Int.le_refl _) (hPh.inc 0)
  have e0 := hPh.pre (Tm rd1 (σw 0) sh5 [] 0 - 1) (by omega)
  refine ⟨(Tm rd1 (σw 0) sh5 [] 0 - 1).toNat, fun h => ?_⟩
  have c1 : (((Tm rd1 (σw 0) sh5 [] 0 - 1).toNat + 1 : Nat) : Int) = Tm rd1 (σw 0) sh5 [] 0 := by omega
  have c0 : (((Tm rd1 (σw 0) sh5 [] 0 - 1).toNat : Nat) : Int) = Tm rd1 (σw 0) sh5 [] 0 - 1 := by omega
  simp only [c1, c0] at h
  rw [e1, e0] at h
  exact absurd h (by decide)

/-! ### `FbCel` is exactly the SI step (its timing fields are existential) -/

/-- **`FbCel` is equivalent to the SI gate step.** Its H_FB_ROUTE / H_RT_FB fields are
existential in the feedback pin `qp` and the bounds `lo hi`, and are always met by the ideal
feedback `qp = o`, `lo = hi = 0` (`BoundedDelay 0 0 o o`, `RespAfter 0`). So `FbCel` adds no
timing content to `FbCel.si`; the timing has to be read off the CHOSEN `qp lo hi`. -/
theorem fbCel_iff_si {α : Type} (F : α → Bool → Bool) (p : Nat → α) (o : Trace) :
    FbCel F p o ↔ ∀ t, o (t + 1) ≠ o t → o (t + 1) = F (p t) (o t) := by
  refine ⟨fun h => h.si, fun h => ⟨o, 0, 0, h, ⟨fun t _ => ⟨0, Nat.le_refl _, Nat.le_refl _,
    Nat.zero_le _, by simp⟩, fun _ _ _ => rfl⟩, rfl, fun u _ => ⟨Nat.zero_le _, fun t h1 h2 => ?_⟩⟩⟩
  rw [show t = u + 1 - 0 by omega]

theorem celL_of_all (xs : List Bool) (q v : Bool) (hne : xs ≠ []) (h : ∀ x ∈ xs, x = v) :
    celL xs q = v := by
  unfold celL
  cases v
  · have h1 : xs.all id = false := by
      cases xs with
      | nil => exact absurd rfl hne
      | cons a l => have := h a (List.mem_cons_self ..); simp [this]
    have h2 : xs.all (fun x => !x) = true := List.all_eq_true.mpr (fun x hx => by simp [h x hx])
    simp [h1, h2]
  · have h1 : xs.all id = true := List.all_eq_true.mpr (fun x hx => by simp [h x hx])
    simp [h1]

/-- A node whose inputs are all at the new value whenever it changes meets `FbCel cgate`. -/
theorem fbCel_of_cel {xs : Nat → List Bool} {o : Trace} (hne : ∀ t, xs t ≠ [])
    (h : ∀ t, o (t + 1) ≠ o t → ∀ x ∈ xs t, x = o (t + 1)) : FbCel cgate xs o :=
  (fbCel_iff_si _ _ _).mpr fun t ht => by
    rw [cgate_eq _ _ (hne t), celL_of_all _ _ _ (hne t) (h t ht)]

/-- **H_CTREE_ATOMIC, exactly as IpowCells states it (`FbCel cgate`), from B's tree model**,
for a tree of ANY shape (`bd_ctree` N = 5: `sh5`; gcd_hw's N = 6 fork: `sh6`). -/
theorem fbCel_of_ctreeB {tr : Tr} {lo hi Qlo Qhi : Path → Int} {E : Int} {leaves : List Path}
    {xs : Nat → List Bool} {o : Trace} (h : CTreeB tr lo hi Qlo Qhi E leaves xs o)
    (hne : ∀ t, xs t ≠ []) : FbCel cgate xs o :=
  fbCel_of_cel hne (ctreeB_cel h)

/-- The leaves of `bd_ctree N=6` = `sh6 = C2(C4(a0..a3), C2(a4, a5))` (gcd_hw's 6-way fork). -/
def leaves6 : List Path := [[0, 0], [1, 0], [2, 0], [3, 0], [0, 1], [1, 1]]

theorem leaves6_in : ∀ q ∈ leaves6, InT CTreeExact.sh6 [] q .leaf := by
  intro q hq
  have inner : ∀ i : Fin 4, InT CTreeExact.sh6 [] [i.1, 0] .leaf := fun i =>
    InT.child (k := 2) ⟨0, by decide⟩
      (show InT (lv 4) [0] [i.1, 0] .leaf from InT.child i (InT.refl _ _))
  have inner2 : ∀ i : Fin 2, InT CTreeExact.sh6 [] [i.1, 1] .leaf := fun i =>
    InT.child (k := 2) ⟨1, by decide⟩
      (show InT (lv 2) [1] [i.1, 1] .leaf from InT.child i (InT.refl _ _))
  simp only [leaves6, List.mem_cons, List.mem_nil_iff, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact inner ⟨0, by decide⟩
  · exact inner ⟨1, by decide⟩
  · exact inner ⟨2, by decide⟩
  · exact inner ⟨3, by decide⟩
  · exact inner2 ⟨0, by decide⟩
  · exact inner2 ⟨1, by decide⟩

/-! ## 2. The join with its real request node (no H_CTREE_ATOMIC) -/

/-- The request node of a join: the generated flat C-element of arity `<= 4` (`FbCel` on
`bd_c2/c3/c4`), or the two-level `bd_ctree N=5` in B's tree model (`CTreeB`). For arity 5
only the tree branch can hold, so the contract no longer contains H_CTREE_ATOMIC. -/
def ReqNode (xs : Nat → List Bool) (o : Trace) : Prop :=
  ((∀ t, (xs t).length ≤ 4) ∧ FbCel cgate xs o) ∨
  ∃ (lo hi Qlo Qhi : Path → Int) (E : Int), CTreeB sh5 lo hi Qlo Qhi E leaves5 xs o

theorem reqNode_cel {xs : Nat → List Bool} {o : Trace} (h : ReqNode xs o)
    (hne : ∀ t, xs t ≠ []) : ∀ t, o (t + 1) ≠ o t → ∀ x ∈ xs t, x = o (t + 1) := by
  rcases h with ⟨_, hF⟩ | ⟨lo, hi, Qlo, Qhi, E, hT⟩
  · intro t ht x hx
    have e := hF.si t ht
    rw [cgate_eq _ _ (hne t)] at e
    rw [e] at ht ⊢
    exact celL_move _ _ ht x hx
  · exact ctreeB_cel hT

/-- `JoinC` with the request field `ReqNode` (IpowCells' `JoinC` has `FbCel cgate`). -/
structure JoinB (g : List Nat → Nat) (is : List Chan) (ex : List Trace) (o : Chan) : Prop where
  ne : is ≠ []
  req : ReqNode (fun t => is.map (fun i => i.req t) ++ ex.map (fun r => r t)) o.req
  H_WIRE_DI : ∀ i ∈ is, ∀ t, i.ack (t + 1) ≠ i.ack t → i.ack (t + 1) = o.ack t
  H_DATA_COMB : ∀ t, o.dat t = g (is.map (fun i => i.dat t))
  initO : o.req 0 = false
  initI : ∀ i ∈ is, i.ack 0 = false

theorem join_of_B {g : List Nat → Nat} {is : List Chan} {ex : List Trace} {o : Chan}
    (h : JoinB g is ex o) : Join.Join g is o := by
  refine ⟨h.ne, fun t ht i hi => ?_, h.H_WIRE_DI, h.H_DATA_COMB, h.initO, h.initI⟩
  have hne : ∀ t, is.map (fun i => i.req t) ++ ex.map (fun r => r t) ≠ [] := by
    intro t hn; apply h.ne; simpa using (List.append_eq_nil_iff.mp hn).1
  exact reqNode_cel h.req hne t ht (i.req t)
    (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨i, hi, rfl⟩)))

/-- A JoinC (flat, arity <= 4) is a JoinB. -/
theorem joinB_of_joinC {g : List Nat → Nat} {is : List Chan} {ex : List Trace} {o : Chan}
    (h : IpowCells.JoinC g is ex o) (hl : is.length + ex.length ≤ 4) : JoinB g is ex o :=
  ⟨h.ne, Or.inl ⟨fun t => by simpa using hl, h.req⟩, h.H_WIRE_DI, h.H_DATA_COMB, h.initO, h.initI⟩

/-! ## 3. H_SEL_PIN from `LibGapSteer.steer_tokens` -/

/-- A Nat trace as an Int signal, low before 0. -/
def toI (x : Trace) (u : Int) : Bool := if u < 0 then false else x u.toNat

theorem toI_nat (x : Trace) (t : Nat) : toI x (t : Int) = x t := by simp [toI]

theorem toI_tok {x : Trace} {R F : Nat → Int}
    (h : ∀ t : Nat, x t = true → ∃ k, R k ≤ t ∧ t < F k) :
    ∀ u : Int, toI x u = true → ∃ k, R k ≤ u ∧ u < F k := by
  intro u hu
  unfold toI at hu
  split at hu
  · exact absurd hu (by decide)
  · obtain ⟨k, h1, h2⟩ := h u.toNat hu
    exact ⟨k, by omega, by omega⟩

/-- **SelPin**: B's per-pin select model (LibGapSteer's H_REQ_TOK, H_S_STABLE, H_SETUP_PIN,
H_HOLD_PIN) for a LUT that reads the channel's request through C's one tick
(`Rd.const 1`) and the select `s` (at its driver) through `ps`; plus H_SEL_DEC: during
token `k` the bus decodes to that token's select value `v k` (H_BUNDLE + the decoder). -/
structure SelPin (sel : Nat → Bool) (c : Chan) (s : Int → Bool) (ps : Rd)
    (R F S0 S1 : Nat → Int) (v : Nat → Bool) : Prop where
  H_REQ_TOK : ∀ t : Nat, c.req t = true → ∃ k, R k ≤ t ∧ t < F k
  H_S_STABLE : ∀ k, LibGapSteer.Stable s (v k) (S0 k) (S1 k)
  H_SETUP_PIN : ∀ k, S0 k + ps.hi ≤ R k + 1
  H_HOLD_PIN : ∀ k, F k + 1 ≤ S1 k + ps.lo
  H_SEL_DEC : ∀ k (t : Nat), R k ≤ t → t < F k → sel (c.dat t) = v k

/-- **H_SEL_DEC from H_BUNDLE**: if the request is high on the whole window `[R k, F k)`, C's
`Held` keeps the bus constant there, so the select decodes to `v k := sel (dat (R k))`. -/
theorem sel_dec_of_held {sel : Nat → Bool} {c : Chan} {R F : Nat → Int} (hH : Held c)
    (hR0 : ∀ k, 0 ≤ R k) (hP : ∀ k (t : Nat), R k ≤ t → t < F k → c.req t = true) :
    ∀ k (t : Nat), R k ≤ t → t < F k → sel (c.dat t) = sel (c.dat (R k).toNat) := by
  intro k t h1 h2
  have key : ∀ d : Nat, ((R k).toNat + d : Nat) < F k → c.dat ((R k).toNat + d) = c.dat (R k).toNat := by
    intro d
    induction d with
    | zero => intro _; rfl
    | succ d ih =>
      intro hd
      have a := hP k ((R k).toNat + d) (by have := hR0 k; omega) (by omega)
      have b := hP k ((R k).toNat + (d + 1)) (by have := hR0 k; omega) hd
      rw [← ih (by omega), show (R k).toNat + (d + 1) = (R k).toNat + d + 1 by omega]
      exact hH _ (by simp [inTx, a]) (by simp [inTx, show (R k).toNat + d + 1 = (R k).toNat + (d + 1) by omega, b])
  have := key (t - (R k).toNat) (by have := hR0 k; omega)
  rw [show (R k).toNat + (t - (R k).toNat) = t by omega] at this
  rw [this]

theorem outB_true_eq : ∀ s w : Bool, LibGapSteer.outB true true s = (w == true) → s = w := by
  decide

/-- **The select pin shows the bus's select whenever the request pin is high** (B's
`steer_tokens`, at the request read map `Rd.const 1`). -/
theorem selPin_ok {sel : Nat → Bool} {c : Chan} {s : Int → Bool} {ps : Rd}
    {R F S0 S1 : Nat → Int} {v : Nat → Bool} (h : SelPin sel c s ps R F S0 S1 v) :
    ∀ t : Nat, c.req t = true → s (ps.σ ((t : Int) + 1)) = sel (c.dat t) := by
  intro t ht
  have hT := (LibGapSteer.steer_tokens true (Rd.const 1) ps (toI c.req) s R F S0 S1 v
    (toI_tok h.H_REQ_TOK) h.H_S_STABLE (fun k => by have := h.H_SETUP_PIN k; simp [Rd.const]; omega)
    (fun k => by have := h.H_HOLD_PIN k; simp [Rd.const]; omega) ((t : Int) + 1)).2
  have e : (Rd.const 1).σ ((t : Int) + 1) = (t : Int) := by simp [Rd.const]
  rw [e, toI_nat] at hT
  obtain ⟨k, h1, h2, h3⟩ := hT ht
  rw [ht] at h3
  rw [outB_true_eq _ _ h3, h.H_SEL_DEC k t h1 h2]

theorem steerF_outB : ∀ b r x : Bool, steerF b (r, x) = LibGapSteer.outB b r x := by
  decide +kernel

theorem outB_low : ∀ b x : Bool, LibGapSteer.outB b false x = false := by decide

/-- `bd_steer` in B's per-pin model: the two branch outputs are the real INIT of the request
(C's one tick) and the select pin read through its own map `ps b` (H_PIN_READ, level form),
`SelPin` for each branch; `uack`, data and reset as in `SteerC`. -/
structure SteerPins (sel : Nat → Bool) (f : Nat → Nat) (j : Chan) (out : Bool → Chan)
    (s : Int → Bool) (ps : Bool → Rd) (R F S0 S1 : Nat → Int) (v : Nat → Bool) : Prop where
  H_PIN_READ : ∀ b (t : Nat), (out b).req (t + 1) =
    LibGapSteer.outB b (j.req t) (s ((ps b).σ ((t : Int) + 1)))
  H_SEL : ∀ b, SelPin sel j s (ps b) R F S0 S1 v
  H_ACK_LUT : LutSI (fun p : Bool × Bool => genF bd_steer "uack" .O ["ack0", "ack1"] [p.1, p.2])
    (fun t => ((out false).ack t, (out true).ack t)) j.ack
  H_DATA_WIRE : ∀ b t, (out b).dat t = f (j.dat t)
  initJ : j.ack 0 = false
  initO : ∀ b, (out b).req 0 = false

def SteerB (sel : Nat → Bool) (f : Nat → Nat) (j : Chan) (out : Bool → Chan) : Prop :=
  ∃ (s : Int → Bool) (ps : Bool → Rd) (R F S0 S1 : Nat → Int) (v : Nat → Bool),
    SteerPins sel f j out s ps R F S0 S1 v

/-- **H_SEL_PIN, derived**: B's per-pin steer model gives `SteerC.H_LUT_SI` exactly as
IpowCells states it (in level form, so a fortiori in change form). -/
theorem steer_lut_of_pins {sel : Nat → Bool} {f : Nat → Nat} {j : Chan} {out : Bool → Chan}
    {s : Int → Bool} {ps : Bool → Rd} {R F S0 S1 : Nat → Int} {v : Nat → Bool}
    (h : SteerPins sel f j out s ps R F S0 S1 v) :
    ∀ b, LutSI (steerF b) (fun t => (j.req t, sel (j.dat t))) (out b).req := by
  intro b t _
  show (out b).req (t + 1) = steerF b (j.req t, sel (j.dat t))
  rw [h.H_PIN_READ b t, steerF_outB]
  cases hr : j.req t
  · rw [outB_low, outB_low]
  · rw [selPin_ok (h.H_SEL b) t hr]

theorem steer_of_B {sel : Nat → Bool} {f : Nat → Nat} {j : Chan} {out : Bool → Chan}
    (h : SteerB sel f j out) : Steer.Steer sel f j out := by
  obtain ⟨s, ps, R, F, S0, S1, v, P⟩ := h
  obtain ⟨hl, ho⟩ := steer_bound (steer_lut_of_pins P) P.H_ACK_LUT
  exact ⟨hl, ho, P.H_DATA_WIRE, P.initJ, P.initO⟩

/-! ## 4. H_DELAY_LUMPED (ungated request path) from B's FIFO read-map model -/

/-- **H_PULSE_WIDTH**: after every change, `w` stays put for `hw` ps. -/
def Width (hw : Int) (w : Int → Bool) : Prop :=
  ∀ c, w c ≠ w (c - 1) → ∀ u, c ≤ u → u < c + hw → w u = w c

/-- **ReqPath**: the request path from `w` (the `uor` input value, both pins on ONE read map:
H_OR_SAME_PATH) to `z`, as one read map `r` of B's per-pin model, with H_PIN_FIFO (`Mono`),
a positive minimum delay, and H_PULSE_WIDTH at the path's maximum delay. -/
def ReqPath (r : Rd) (w : Trace) (z : Trace) : Prop :=
  Mono r ∧ 1 ≤ r.lo ∧ (∀ t : Nat, z t = toI w (r.σ t)) ∧ Width r.hi (toI w)

/-- **H_DELAY_LUMPED, derived** (FIFO read map + pulse width): the path's output changes only
to the value its input had one tick earlier, i.e. the lumped path is C's SI node. -/
theorem lumped_of_fifo {r : Rd} {w z : Trace} (h : ReqPath r w z) :
    ∀ t, z (t + 1) ≠ z t → z (t + 1) = w t := by
  obtain ⟨hm, hlo, hz, hW⟩ := h
  intro t ht
  rw [hz, hz] at ht
  rw [hz, ← toI_nat w t]
  have hab : r.σ (t : Int) ≤ r.σ ((t + 1 : Nat) : Int) := hm _ _ (by omega)
  have hb := r.le ((t + 1 : Nat) : Int)
  have ha := r.ge (t : Int)
  apply Classical.byContradiction; intro hne
  obtain ⟨c1, c1a, c1b, c1c⟩ := NecessityMerge.exists_change (toI w) (by omega) hne
  obtain ⟨c2, c2a, c2b, c2c⟩ := NecessityMerge.exists_change (toI w) hab (fun e => ht e.symm)
  have e1 := hW c2 c2c c1 (by omega) (by omega)
  have e2 := hW c2 c2c (c1 - 1) (by omega) (by omega)
  exact c1c (e1.trans e2.symm)

/-- **Counter-run: H_PULSE_WIDTH and a non-monotone read map (LibGapDelay's H_PIN_READ
allows it) break the lumped node.** One clean input step at 10, read map in `[1, 3]` that
reads `t - 1` except `9` at 12: the output goes 1 at 11, back to 0 at 12 (a runt), while the
input at 11 is 1. -/
def nmMap : Rd :=
  ⟨fun t => if t = 12 then 9 else t - 1, 1, 3, fun t => by split <;> omega,
   fun t => by split <;> omega⟩

theorem lumped_needs_fifo :
    let w : Trace := fun t => decide (10 ≤ t)
    let z : Trace := fun t => toI w (nmMap.σ t)
    1 ≤ nmMap.lo ∧ (∀ t : Nat, z t = toI w (nmMap.σ t)) ∧ Width nmMap.hi (toI w) ∧
      ¬ Mono nmMap ∧ z 12 ≠ z 11 ∧ z 12 ≠ w 11 := by
  intro w z
  have hw : ∀ u : Int, toI w u = decide (10 ≤ u) := by
    intro u; simp only [toI, w]; split <;> simp <;> omega
  refine ⟨by decide, fun _ => rfl, ?_, fun hm => ?_, by decide, by decide⟩
  · intro c hc u h1 _
    rw [hw, hw] at hc; rw [hw, hw]
    have : c = 10 := by
      by_cases a : 10 ≤ c <;> by_cases b : 10 ≤ c - 1 <;> simp [a, b] at hc <;> omega
    subst this; simp; omega
  · have := hm 11 12 (by decide)
    simp [nmMap] at this

/-! ## 5. The mux with B's select pins and request path -/

theorem mux0_c_low (a s s' q : Bool) : muxJ0F (a, false, s) q = muxJ0F (a, false, s') q :=
  (mux_gate a false false s q false).1.trans
    ((by simp : cel2 a (false && !s) q = cel2 a (false && !s') q).trans
      (mux_gate a false false s' q false).1.symm)
theorem mux1_c_low (a s s' q : Bool) : muxJ1F (a, false, s) q = muxJ1F (a, false, s') q :=
  (mux_gate false a false s q false).2.1.trans
    ((by simp : cel2 a (false && s) q = cel2 a (false && s') q).trans
      (mux_gate false a false s' q false).2.1.symm)

/-- A feedback LUT reading the PHYSICAL select pin (`FbCel`) is, on the bus's select, the
step model `mux_bound` needs (LutFb + FbFirst), when `SelPin` holds. This is weaker than
IpowCells' `uj0 : FbCel .. sel (c.dat t)` (whose H_RT_FB would constrain the bus's select,
not the pin), and it is all `mux_of_contract` uses. -/
theorem uj0_of_pin {sel : Nat → Bool} {x c : Chan} {j0 : Trace} {s : Int → Bool} {ps : Rd}
    {R F S0 S1 : Nat → Int} {v : Nat → Bool}
    (hF : FbCel muxJ0F (fun t => (x.req t, c.req t, s (ps.σ ((t : Int) + 1)))) j0)
    (hS : SelPin sel c s ps R F S0 S1 v) :
    ∃ qp, LutFb muxJ0F (fun t => (x.req t, c.req t, sel (c.dat t))) qp j0 ∧ FbFirst qp j0 := by
  obtain ⟨qp, hL, hFF⟩ := hF.lutFb
  refine ⟨qp, fun t ht => ?_, hFF⟩
  rw [hL t ht]
  show muxJ0F (x.req t, c.req t, s (ps.σ ((t : Int) + 1))) (qp t) =
    muxJ0F (x.req t, c.req t, sel (c.dat t)) (qp t)
  by_cases hc : c.req t = true
  · rw [selPin_ok hS t hc]
  · rw [Bool.not_eq_true] at hc
    rw [hc]
    exact mux0_c_low _ _ _ _

theorem uj1_of_pin {sel : Nat → Bool} {y c : Chan} {j1 : Trace} {s : Int → Bool} {ps : Rd}
    {R F S0 S1 : Nat → Int} {v : Nat → Bool}
    (hF : FbCel muxJ1F (fun t => (y.req t, c.req t, s (ps.σ ((t : Int) + 1)))) j1)
    (hS : SelPin sel c s ps R F S0 S1 v) :
    ∃ qp, LutFb muxJ1F (fun t => (y.req t, c.req t, sel (c.dat t))) qp j1 ∧ FbFirst qp j1 := by
  obtain ⟨qp, hL, hFF⟩ := hF.lutFb
  refine ⟨qp, fun t ht => ?_, hFF⟩
  rw [hL t ht]
  show muxJ1F (y.req t, c.req t, s (ps.σ ((t : Int) + 1))) (qp t) =
    muxJ1F (y.req t, c.req t, sel (c.dat t)) (qp t)
  by_cases hc : c.req t = true
  · rw [selPin_ok hS t hc]
  · rw [Bool.not_eq_true] at hc
    rw [hc]
    exact mux1_c_low _ _ _ _

/-- `bd_mux` with the select read at its own pins (`uj0`/`uj1` on the physical `s` pin,
`SelPin`) and the request path `uor -> bd_delay -> z_req` as one FIFO read map (`ReqPath`). -/
structure MuxPins (sel : Nat → Bool) (x y c z : Chan) (j0 j1 : Trace) (s : Int → Bool)
    (ps0 ps1 r : Rd) (R F S0 S1 : Nat → Int) (v : Nat → Bool) : Prop where
  uj0 : FbCel muxJ0F (fun t => (x.req t, c.req t, s (ps0.σ ((t : Int) + 1)))) j0
  uj1 : FbCel muxJ1F (fun t => (y.req t, c.req t, s (ps1.σ ((t : Int) + 1)))) j1
  H_SEL0 : SelPin sel c s ps0 R F S0 S1 v
  H_SEL1 : SelPin sel c s ps1 R F S0 S1 v
  uxa : FbCel muxXaF (fun t => (j0 t, z.ack t)) x.ack
  uya : FbCel muxYaF (fun t => (j1 t, z.ack t)) y.ack
  H_REQ_PATH : ReqPath r (fun t => j0 t || j1 t) z.req
  H_WIRE_DI : ∀ t, c.ack (t + 1) ≠ c.ack t → c.ack (t + 1) = z.ack t
  H_DATA_COMB : ∀ t, z.dat t = if sel (c.dat t) then y.dat t else x.dat t
  i0 : j0 0 = false
  i1 : j1 0 = false
  iz : z.req 0 = false
  ix : x.ack 0 = false
  iy : y.ack 0 = false
  ic : c.ack 0 = false

def MuxB (sel : Nat → Bool) (x y c z : Chan) (j0 j1 : Trace) : Prop :=
  ∃ (s : Int → Bool) (ps0 ps1 r : Rd) (R F S0 S1 : Nat → Int) (v : Nat → Bool),
    MuxPins sel x y c z j0 j1 s ps0 ps1 r R F S0 S1 v

theorem mux_of_B {sel : Nat → Bool} {x y c z : Chan} {j0 j1 : Trace} (h : MuxB sel x y c z j0 j1) :
    Mux.Mux sel x y c z j0 j1 := by
  obtain ⟨s, ps0, ps1, r, R, F, S0, S1, v, P⟩ := h
  obtain ⟨q0, h0, f0⟩ := uj0_of_pin P.uj0 P.H_SEL0
  obtain ⟨q1, h1, f1⟩ := uj1_of_pin P.uj1 P.H_SEL1
  obtain ⟨q2, h2, f2⟩ := P.uxa.lutFb
  obtain ⟨q3, h3, f3⟩ := P.uya.lutFb
  obtain ⟨c0, c1, xa, ya⟩ := mux_bound h0 f0 h1 f1 h2 f2 h3 f3
  refine ⟨c0, c1, fun t ht => ?_, xa, ya, P.H_WIRE_DI, P.H_DATA_COMB, P.i0, P.i1, P.iz, P.ix, P.iy, P.ic⟩
  exact lumped_of_fifo P.H_REQ_PATH t ht

/-! ## 6. The arbiter grant fields: what B's per-pin arbiter model gives -/

/-- **Counter-run: H_ARB_EXCL is not derivable from B's per-pin arbiter model.** B's
`bd_arbcell` (real `ustate`/`ugrant` INITs, transport delays in `boxS`, requests at 100 and
105 ps, inside the race window) has a behaviour whose grants, sampled at ticks, are both
high at some tick (`ArbPin.su_osc_instance`). -/
theorem arb_excl_not_derivable :
    ∃ c : ArbPin.Cell ArbPin.boxS false (ArbPin.up 100) (ArbPin.up 105),
      ¬ ∀ n : Nat, (c.g1 n && c.g2 n) = false := by
  obtain ⟨c, _, hov, _⟩ := ArbPin.su_osc_instance
  obtain ⟨t, ht, h1, h2⟩ := hov 0
  refine ⟨c, fun h => ?_⟩
  have := h t.toNat
  rw [show ((t.toNat : Nat) : Int) = t by omega, h1, h2] at this
  exact absurd this (by decide)

/-- **H_ARB_EXCL inside B's window** (`ArbPin.su_box_iff`, sufficient half): for ONE
arbitration (both requests single rising steps, `q0 = 0`), QUIET or COMMIT-without-overlap
gives C's `H_ARB_EXCL` on the tick-sampled grants, for every per-pin behaviour in the box. -/
theorem arb_excl_of_window {B : ArbPin.Box} {e1 e2 : Int} (hB : B.Ok) (H_LOOP2 : 2 ≤ B.L)
    (H_QWIN : B.c5 < B.C6 ∧ B.c6 ≤ B.C5 + 1) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2)
    (H_WIN : e2 + B.A2 ≤ e1 + B.a1 ∨ (e1 + B.A1 + B.L ≤ e2 + B.a2 ∧ ¬ ArbPin.SuOvT B e1 e2))
    (c : ArbPin.Cell B false (ArbPin.up e1) (ArbPin.up e2)) :
    ∀ n : Nat, (c.g1 n && c.g2 n) = false := by
  intro n
  have hx := (ArbPin.su_box_iff hB H_LOOP2 H_QWIN he1 he2).mpr H_WIN c n
  cases h1 : c.g1 n <;> cases h2 : c.g2 n <;> simp_all


/-! ## 7. The ipow contracts with the bridged fields -/

section ipow
open Formal.Net.CapNet hiding R Hh Hh_pr Hh_cn NoEnd JOK FoldOK OpChk
open Formal.Cells.IpowCells (ForkC AMergeC LinkC fork_of_contract amerge_of_contract
  link_of_contract chQ fbCel_quiet mem_chQ DataOK dvW dataOK_all cnt_quiet extraIn grant_idle)
open Formal.Net.IpowCap (NC NO ops opAt start out0)

variable {n : Nat}

/-- **ContractB**: IpowCells' `Contract` with three bridged fields replaced by B-model
hypotheses: every join's request node is `ReqNode` (no H_CTREE_ATOMIC: an arity-5 join must be
B's `bd_ctree` tree), every steer is `SteerB` (H_SEL_PIN replaced by B's per-pin select
model), every mux is `MuxB` (H_SEL_PIN at `uj0`/`uj1` and the ungated H_DELAY_LUMPED replaced
by B's per-pin select model and a FIFO request path). Forks, amerges (arbiter fields H_ARB*,
H_AMERGE_RTZ and the gated H_DELAY_LUMPED), links, sources and sinks are unchanged. -/
def ContractB (ch : Fin n → Chan) (sv : Nat → Nat) (nx : Nat) : K n → Prop
  | .forkG i os => ForkC (ch i) (os.map ch)
  | .forkH i os _ _ _ _ => ForkC (ch i) ((os.map Prod.fst).map ch)
  | .join ins o e js _ => ∃ ex : List Trace, ex.length = nx ∧ JoinB (jg e js) (ins.map ch) ex (ch o)
  | .bjoin ins o ec ed => ∃ ex : List Trace, ex.length = nx ∧ JoinB (bg ec ed) (ins.map ch) ex (ch o)
  | .steerC j t f => SteerB sel2 (fun _ => 0) (ch j) (fun b => ch (bif b then t else f))
  | .steerD j t f fd _ =>
      SteerB sel2 (fun v => fd.eval [v / 2]) (ch j) (fun b => ch (bif b then t else f))
  | .mux c x y z _ => ∃ j0 j1, MuxB sel2 (ch x) (ch y) (ch c) (ch z) j0 j1
  | .muxn c x0 x1 x2 z _ =>
      ∃ j, MuxN.MuxN selD (fun k => ch (cx3 x0 x1 x2 k)) (ch c) (ch z) j
  | .amerge x y z _ => ∃ g1 g2, AMergeC (ch x) (ch y) (ch z) g1 g2
  | .link i o => ∃ c, LinkC (ch i) (ch o) c
  | .src z which _ => Capstone.Src (ch z) (sv which)
  | .sink i => Ops.Gcd.Sink (ch i)

/-- Every operator's `ContractB` gives C's gate model. -/
theorem cell_of_contractB (ch : Fin n → Chan) (sv : Nat → Nat) (nx : Nat) (k : K n)
    (h : ContractB ch sv nx k) : Cell ch sv k := by
  cases k with
  | forkG i os => exact fork_of_contract h
  | forkH i os l hh d hs => exact fork_of_contract h
  | join ins o e js jw => obtain ⟨ex, _, J⟩ := h; exact join_of_B J
  | bjoin ins o ec ed => obtain ⟨ex, _, J⟩ := h; exact join_of_B J
  | steerC j t f => exact steer_of_B h
  | steerD j t f fd sw => exact steer_of_B h
  | mux c x y z mw => obtain ⟨j0, j1, M⟩ := h; exact ⟨j0, j1, mux_of_B M⟩
  | muxn c x0 x1 x2 z nw => exact h
  | amerge x y z w => obtain ⟨g1, g2, A⟩ := h; exact ⟨g1, g2, amerge_of_contract A⟩
  | link i o => obtain ⟨c, L⟩ := h; exact ⟨c, link_of_contract L⟩
  | src z which d => exact h
  | sink i => exact h

/-- **`ipow_safe_of_contracts'`**: C-8y's `ipow_circuit_safe3` with H_CELLS discharged by
`ContractB`: H_CTREE_ATOMIC, H_SEL_PIN (steers and muxes) and the mux's H_DELAY_LUMPED are no
longer hypotheses; in their place are B's tree model with H_CTREE_LOOP (`CTreeB`), B's per-pin
select model with H_SETUP_PIN / H_HOLD_PIN (`SelPin`), and a FIFO request path with
H_PULSE_WIDTH (`ReqPath`). -/
theorem ipow_safe_of_contracts' (b e : Nat) (he : e < 2 ^ 32) (ch : Fin NC → Chan)
    (H_CONTRACTS : ∀ o : Fin NO, ContractB ch (srcV b e) (extraIn o) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, cnt (riseB (ch start).req) t ≤ 1) :
    (∀ k v, TokAt (ch out0) k v → (ch out0).dat v = IpowHw.ipowSpec b e) ∧
    (∀ t, closedVals (ch out0) t =
      List.replicate (cnt (fallB (ch out0).ack) t) (IpowHw.ipowSpec b e)) :=
  Formal.Net.IpowCap.ipow_circuit_safe3 b e he ch
    (fun o => cell_of_contractB ch (srcV b e) (extraIn o) (opAt o) (H_CONTRACTS o)) H_BUNDLE
    H_START_ONCE

/-! ### The bridged fields as IpowCells states them -/

theorem joinC_of_joinB {g : List Nat → Nat} {is : List Chan} {ex : List Trace} {o : Chan}
    (h : JoinB g is ex o) : IpowCells.JoinC g is ex o := by
  have hne : ∀ t, is.map (fun i => i.req t) ++ ex.map (fun r => r t) ≠ [] := by
    intro t hn; apply h.ne; simpa using (List.append_eq_nil_iff.mp hn).1
  refine ⟨h.ne, ?_, h.H_WIRE_DI, h.H_DATA_COMB, h.initO, h.initI⟩
  rcases h.req with ⟨_, hF⟩ | ⟨lo, hi, Qlo, Qhi, E, hT⟩
  · exact hF
  · exact fbCel_of_ctreeB hT hne

theorem steerC_of_steerB {sel : Nat → Bool} {f : Nat → Nat} {j : Chan} {out : Bool → Chan}
    (h : SteerB sel f j out) : IpowCells.SteerC sel f j out := by
  obtain ⟨s, ps, R, F, S0, S1, v, P⟩ := h
  exact ⟨steer_lut_of_pins P, P.H_ACK_LUT, P.H_DATA_WIRE, P.initJ, P.initO⟩

theorem fbCel_of_fbFirst {α : Type} {F : α → Bool → Bool} {p : Nat → α} {o : Trace}
    (h : ∃ qp, LutFb F p qp o ∧ FbFirst qp o) : FbCel F p o := by
  obtain ⟨qp, hL, hF⟩ := h
  exact (fbCel_iff_si _ _ _).mpr fun t ht => by rw [hL t ht, hF t ht]

theorem muxC_of_muxB {sel : Nat → Bool} {x y c z : Chan} {j0 j1 : Trace}
    (h : MuxB sel x y c z j0 j1) : IpowCells.MuxC sel x y c z j0 j1 := by
  obtain ⟨s, ps0, ps1, r, R, F, S0, S1, v, P⟩ := h
  refine ⟨fbCel_of_fbFirst (uj0_of_pin P.uj0 P.H_SEL0), fbCel_of_fbFirst (uj1_of_pin P.uj1 P.H_SEL1),
    P.uxa, P.uya, fun t ht => ?_, P.H_WIRE_DI, P.H_DATA_COMB, P.i0, P.i1, P.iz, P.ix, P.iy, P.ic⟩
  rw [lumped_of_fifo P.H_REQ_PATH t ht]
  exact (mux_zr_chain (j0 t) (j1 t)).symm

/-- **The bridged fields hold exactly as IpowCells states them**: `ContractB` implies
IpowCells' `Contract` (H_CTREE_ATOMIC = `FbCel cgate` at arity 5, H_SEL_PIN in `SteerC` and
`MuxC`, `MuxC.H_DELAY_LUMPED`), operator by operator. -/
theorem contract_of_contractB (ch : Fin n → Chan) (sv : Nat → Nat) (nx : Nat) (k : K n)
    (h : ContractB ch sv nx k) : IpowCells.Contract ch sv nx k := by
  cases k with
  | forkG i os => exact h
  | forkH i os l hh d hs => exact h
  | join ins o e js jw => obtain ⟨ex, hl, J⟩ := h; exact ⟨ex, hl, joinC_of_joinB J⟩
  | bjoin ins o ec ed => obtain ⟨ex, hl, J⟩ := h; exact ⟨ex, hl, joinC_of_joinB J⟩
  | steerC j t f => exact steerC_of_steerB h
  | steerD j t f fd sw => exact steerC_of_steerB h
  | mux c x y z mw => obtain ⟨j0, j1, M⟩ := h; exact ⟨j0, j1, muxC_of_muxB M⟩
  | muxn c x0 x1 x2 z nw => exact h
  | amerge x y z w => exact h
  | link i o => exact h
  | src z which d => exact h
  | sink i => exact h

/-! ## 8. Non-vacuity of `ipow_safe_of_contracts'` -/

/-- The all-quiet tree: for every horizon `N`, B's run with leaves switching from `N + 1` on
agrees with constant-low inputs and output up to `N`. -/
theorem ctreeB_quiet :
    CTreeB sh5 (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) 1 leaves5
      (fun _ => leaves5.map (fun _ => false)) (fun _ => false) := by
  refine ⟨wf_sh5, ⟨2, _, rfl⟩, fun _ => Int.le_refl _, fun _ => Int.le_refl _, by decide,
    sh5_static.2, leaves5_in, fun N => ?_⟩
  obtain ⟨hm, hbox, hleaf, hack⟩ := sh5_run ((N : Int) + 1) (by omega)
  have hfb : ∀ q : Path, (1 : Int) ≤ (rd1 q).lo ∧ (rd1 q).hi ≤ 1 :=
    fun _ => ⟨Int.le_refl _, Int.le_refl _⟩
  have hO := CTreeExact.sol_rv (rd := rd1) (σ := σw ((N : Int) + 1)) (fb := rd1) (fun _ u => by
    show u - 1 ≤ u - 1; exact Int.le_refl _) sh5 []
  refine ⟨rd1, σw ((N : Int) + 1), rd1, _, hm, hbox, hleaf, hack, hfb, hO, fun u hu => ⟨?_, ?_⟩⟩
  · obtain ⟨_, hPh, hle⟩ := root_phase (hi := fun _ => 1) wf_sh5 (fun _ => Int.le_refl _)
      (fun _ => Int.le_refl _) (by decide) sh5_static.2 hm hbox hleaf hack hfb hO
    have hPh : PhaseTr (CTreeExact.rv rd1 (σw ((N : Int) + 1)) rd1 sh5 [])
      (Tm rd1 (σw ((N : Int) + 1)) sh5 []) := hPh
    have h1 : σw ((N : Int) + 1) [1] 0 + 1 ≤ Tm rd1 (σw ((N : Int) + 1)) sh5 [] 0 :=
      hle [1] (leaves5_in [1] (by simp [leaves5])) 0
    have hσ : σw ((N : Int) + 1) [1] 0 = (N : Int) + 1 := by simp [σw]
    exact (hPh.pre _ (by omega)).symm
  · apply List.map_congr_left
    intro q _
    have hL := ofPh_phase (σw_inc ((N : Int) + 1) q)
    have hσ : σw ((N : Int) + 1) q 0 = (N : Int) + 1 := by simp [σw]
    exact (hL.pre _ (by omega)).symm


/-- At arity 5 the flat branch of `ReqNode` is impossible: the contract IS B's tree. -/
theorem reqNode_len5 {xs : Nat → List Bool} {o : Trace} (hl : ∀ t, (xs t).length = 5)
    (h : ReqNode xs o) :
    ∃ (lo hi Qlo Qhi : Path → Int) (E : Int), CTreeB sh5 lo hi Qlo Qhi E leaves5 xs o := by
  rcases h with ⟨h4, _⟩ | h
  · have := h4 0; rw [hl 0] at this; omega
  · exact h

/-- Real join arity (modelled inputs + unmodelled ones), 0 for other kinds. -/
def jar : K n → Nat → Nat
  | .join ins _ _ _ _, nx => ins.length + nx
  | .bjoin ins _ _ _, nx => ins.length + nx
  | _, _ => 0

theorem ipow_jar : ∀ o : Fin NO, jar (opAt o) (extraIn o) ≤ 5 := by decide +kernel

theorem reqNode_quiet (m : Nat) (hm : m ≤ 5) :
    ReqNode (fun _ => List.replicate m false) (fun _ => false) := by
  by_cases h4 : m ≤ 4
  · exact Or.inl ⟨fun _ => by simpa using h4, fbCel_quiet _ _ (fun _ => rfl)⟩
  · have : m = 5 := by omega
    subst this
    exact Or.inr ⟨_, _, _, _, _, ctreeB_quiet⟩

theorem xs_quiet (dv : Fin n → Nat) (ins : List (Fin n)) (nx : Nat) :
    (fun t => (ins.map (chQ dv)).map (fun i => i.req t) ++
      (List.replicate nx (fun _ : Nat => false)).map (fun r => r t)) =
    fun _ => List.replicate (ins.length + nx) false := by
  funext t
  simp [chQ, List.map_map, Function.comp_def, List.map_const', List.replicate_append_replicate]

theorem selPin_quiet (sel : Nat → Bool) (c : Chan) (hc : ∀ t, c.req t = false) :
    SelPin sel c (fun _ => false) (Rd.const 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 1)
      (fun _ => false) :=
  ⟨fun t h => absurd (h.symm.trans (hc t)) (by decide), fun _ _ _ _ => rfl,
    fun _ => by simp [Rd.const], fun _ => by simp [Rd.const],
    fun _ t h1 h2 => absurd (Int.lt_of_le_of_lt h1 h2) (by omega)⟩

theorem toI_false (u : Int) : toI (fun _ => false) u = false := by
  simp only [toI]; split <;> rfl

theorem reqPath_quiet : ReqPath (Rd.const 1) (fun _ => false || false) (fun _ => false) :=
  ⟨NecessityMerge.const_mono 1, Int.le_refl _, fun _ => (toI_false _).symm,
    fun c hc => absurd ((toI_false c).trans (toI_false (c - 1)).symm) hc⟩

/-- **The all-quiet run meets every `ContractB`** whose data equations it solves, for joins of
real arity at most 5 (the arity-5 join through B's tree, `ctreeB_quiet`). -/
theorem quietB_contract (sv : Nat → Nat) (dv : Fin n → Nat) (nx : Nat) (k : K n)
    (hd : DataOK sv dv k) (ha : jar k nx ≤ 5) : ContractB (chQ dv) sv nx k := by
  have Q := IpowCells.quiet_contract sv dv nx k hd
  cases k with
  | forkG i os => exact Q
  | forkH i os l hh d hs => exact Q
  | join ins o e js jw =>
    obtain ⟨_, _, J⟩ := Q
    refine ⟨List.replicate nx (fun _ => false), List.length_replicate .., J.ne, ?_, J.H_WIRE_DI,
      J.H_DATA_COMB, J.initO, J.initI⟩
    rw [xs_quiet]
    exact reqNode_quiet _ ha
  | bjoin ins o ec ed =>
    obtain ⟨_, _, J⟩ := Q
    refine ⟨List.replicate nx (fun _ => false), List.length_replicate .., J.ne, ?_, J.H_WIRE_DI,
      J.H_DATA_COMB, J.initO, J.initI⟩
    rw [xs_quiet]
    exact reqNode_quiet _ ha
  | steerC j t f =>
    exact ⟨_, fun _ => Rd.const 0, _, _, _, _, _,
      ⟨fun b u => (outB_low b _).symm, fun _ => selPin_quiet _ _ (fun _ => rfl), Q.H_ACK_LUT,
        Q.H_DATA_WIRE, Q.initJ, Q.initO⟩⟩
  | steerD j t f fd sw =>
    exact ⟨_, fun _ => Rd.const 0, _, _, _, _, _,
      ⟨fun b u => (outB_low b _).symm, fun _ => selPin_quiet _ _ (fun _ => rfl), Q.H_ACK_LUT,
        Q.H_DATA_WIRE, Q.initJ, Q.initO⟩⟩
  | mux c x y z mw =>
    exact ⟨fun _ => false, fun _ => false, fun _ => false, Rd.const 0, Rd.const 0, Rd.const 1, _, _,
      _, _, _, ⟨fbCel_quiet _ _ (fun _ => rfl), fbCel_quiet _ _ (fun _ => rfl),
        selPin_quiet _ _ (fun _ => rfl), selPin_quiet _ _ (fun _ => rfl),
        fbCel_quiet _ _ (fun _ => rfl), fbCel_quiet _ _ (fun _ => rfl), reqPath_quiet,
        fun _ h => absurd rfl h, fun _ => hd, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  | muxn c x0 x1 x2 z nw => exact Q
  | amerge x y z w => exact Q
  | link i o => exact Q
  | src z which d => exact Q
  | sink i => exact Q

/-- **Non-vacuity of `ipow_safe_of_contracts'`**: one run (b = 3, e = 7, the all-quiet run of
IpowCells with bus values `dvW`) meets every `ContractB` (op 20 through B's tree model,
every steer and mux through B's select-pin model and FIFO request path), H_BUNDLE and
H_START_ONCE at once. -/
theorem ipow_contractsB_satisfiable :
    ∃ (b e : Nat) (ch : Fin NC → Chan), e < 2 ^ 32 ∧
      (∀ o : Fin NO, ContractB ch (srcV b e) (extraIn o) (opAt o)) ∧ (∀ c, Held (ch c)) ∧
      (∀ t, cnt (riseB (ch start).req) t ≤ 1) :=
  ⟨3, 7, chQ dvW, by decide, fun o => quietB_contract _ _ _ _ (dataOK_all o) (ipow_jar o),
    fun _ _ _ _ => rfl, fun t => by
      rw [show (chQ dvW start).req = fun _ => false from rfl, cnt_quiet]; decide⟩

end ipow

end Formal.Cells.ContractBridge
