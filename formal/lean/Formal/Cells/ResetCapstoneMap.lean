import Formal.Cells.ResetCapstoneMapData

/-!
# Probe Bmap (shard B): H_MAP as a theorem, for the generated channel table

`ResetCapstone.gcd_hw_safe_after_reset` takes the channel map `μ` (C channel -> `gNet` node of
its request and acknowledge wire) and `MapOK μ` (H_MAP) as hypotheses; no table existed.
`ResetCapstoneMapData` is that table, GENERATED from the RTL by `formal/tools-B/gcdnet_gen.py`
(`map`): for each of C's 465 CapstoneNet channels (C's names, rebuilt by C's own generator
from bdc's parser), the nets bdc's `emit.py` gives it, resolved through the elaborated RTL to
their driving `gNet` node. The same tool regenerates `ResetGcdNet.lean` (`gNet`) byte for byte
from bdc's emitted Verilog, so node ids in the table are `gNet`'s.

## Results

* `names_ok`: the table's rows are C's channels, in C's order (`mapNames = chanNames`).
* `μT_ok` (**H_MAP, now a theorem**): `MapOK μT` for the table `μT`, by kernel `decide` over
  all 465 rows.
* `μT_wire : WireOK μT`, `μW_not_wire : MapOK μW ∧ ¬ WireOK μW` (**the strengthened
  predicate**): injective on wires except where the RTL makes two C wires one net, each
  exception tied to a C operator (fork requests, join acks, bd_snk ack = req, mux select ack
  = output ack, zero-delay link C-element, the rig's 3 source requests).
* `gcd_hw_safe_after_reset_map` (**headline**): `gcd_hw_safe_after_reset` with `μ := μT` and
  H_MAP discharged.
* `reset_capstone_map_nonvac`: every remaining hypothesis of the headline is jointly
  satisfiable (B's `wRun`, `D = 40`, `W = 1`, `E = 967`, the frozen C family); on that family
  nothing moves after `T0`, so the conclusion is vacuous there (as for `reset_capstone_nonvac`).
* `hot_rows`: the table's first 8 rows (a, b, start, the four fork branches of start and a,
  the link output of `1#1`) as numbers, for review against `ResetCapstone.hot_wiring`.

## Assumed / proved / NOT covered

* Assumed (headline): as `gcd_hw_safe_after_reset`, minus H_MAP: a GMW run of `gNet`, Bounded
  D W, rst held on `(0, E]`, `T0of D W ≤ E`, H_MAP_T0 for `μT` (C's wires at `T0` ARE the
  driving nodes' values: the identification itself), H_CELLS_AFTER, H_BUNDLE_AFTER,
  H_START_AFTER.
* Proved: `MapOK μT` (each mapped node is a control node, not rst, in `onesL` exactly for the
  7 hot requests and channel 3's acknowledge), and the headline.
* NOT covered: that the table is the right identification is the GENERATOR's claim (Python,
  read from bdc's net names), not a Lean theorem: Lean checks the table's shape against
  C's names, `MapOK` and `WireOK`, not that row `c`'s node is the RTL driver of C's wire `c`. MapOK is
  weak: `ResetCapstone.μW` (everything cold read from node 65) also meets it.
  H_MAP_T0, H_CELLS_AFTER (C's O4), H_START_AFTER, liveness: unchanged, open.
-/

namespace Formal.Cells.ResetCapstoneMap
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Cells Formal.Cells.TernarySound Formal.Cells.ResetContract Formal.Cells.ResetGcd
open Formal.Cells.ResetCapstone

/-- The table's rows are C's channels, in C's order. -/
theorem names_ok : mapNames = chanNames := by decide +kernel

theorem reqL_len : reqL.length = NC := by decide +kernel
theorem ackL_len : ackL.length = NC := by decide +kernel

/-- The generated channel map. -/
def μT : ChanMap := ⟨fun c => reqL.getD c.val 0, fun c => ackL.getD c.val 0⟩

theorem μT_ok_b : (List.finRange NC).all (fun c =>
    gCtl (μT.μR c) && (μT.μR c != 0) && gCtl (μT.μA c) && (μT.μA c != 0) &&
    (onesL.contains (μT.μR c) == hot c) && (onesL.contains (μT.μA c) == decide (c.val = 3)) &&
    (gR (μT.μR c) == hot c) && (gR (μT.μA c) == decide (c.val = 3))) = true := by decide +kernel

theorem μT_facts (c : Fin NC) :
    gCtl (μT.μR c) = true ∧ μT.μR c ≠ 0 ∧ gCtl (μT.μA c) = true ∧ μT.μA c ≠ 0 ∧
    (onesL.contains (μT.μR c) = hot c) ∧ (onesL.contains (μT.μA c) = decide (c.val = 3)) ∧
    gR (μT.μR c) = hot c ∧ gR (μT.μA c) = decide (c.val = 3) := by
  have := List.all_eq_true.1 μT_ok_b c (List.mem_finRange c)
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at this
  obtain ⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩ := this
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩

/-- **H_MAP is a theorem for the generated table.** -/
theorem μT_ok : MapOK μT := by
  intro c
  obtain ⟨a1, a2, a3, a4, a5, a6, _, _⟩ := μT_facts c
  refine ⟨a1, a2, a3, a4, ?_, ?_⟩
  · rw [← List.contains_iff_mem, a5]
  · rw [← List.contains_iff_mem, a6]; simp

/-- The first 8 rows: a, b, start, `0#0` (p_end), `0#1`, `1#0`, `1#1` before its link, and
`1#1` after it. Requests: `urig.uenv1` (3275) for the 7 hot ones, `ulink_n1__1.ctl` (1696);
acknowledges: `ufork1`, `ucond_br9.uack`, `ufork0`, `urig.upsnk.g[1]`, `ucond_br10.uack`,
`ucond_br11.uack`, `ulink_n1__1.uack.g[5]`, `ufork2`. -/
theorem hot_rows : reqL.take 8 = [3275, 3275, 3275, 3275, 3275, 3275, 3275, 1696] ∧
    ackL.take 8 = [66, 102, 65, 3257, 106, 110, 1702, 98] := by decide

/-! ## A wiring-faithful predicate (MapOK is too weak)

`MapOK` does not constrain wiring: `ResetCapstone.μW` reads every cold wire from node 65 and
meets it. `WireOK μ` says the map is INJECTIVE on wires, except exactly where the RTL makes
two C wires one electrical net of one driver, each exception tied to a C operator:
* a fork's output requests are its input request (`bd_fork`: `req_out = {N{req}}`);
* a join's (bjoin's) input acknowledges are its output acknowledge (`ack_out = {N{ack}}`);
* a kernel sink's acknowledge is its request (`bd_snk`: `ack = req`; not the rig's two
  environment sinks, channel 3 = p_end and `out0`);
* a mux's (muxn's) select acknowledge is its output acknowledge (`ctl_ack = z_ack`);
* a link whose input acknowledge and output request are the same node (both delays 0: the
  link C-element drives both);
* the three sources' requests are one node (the rig's 3-way fork, outside C's network) that
  drives no other wire.
`copyOK` checks every listed identity holds; `drivenL` (all other wires) must be duplicate-free. -/

/-- The channels whose request is a fork output (a copy of the fork's input request). -/
def forkOuts : K NC → List Nat
  | .forkG _ os => os.map Fin.val
  | .forkH _ os _ _ _ _ => os.map (·.1.val)
  | _ => []

def srcOuts : K NC → List Nat
  | .src z _ _ => [z.val]
  | _ => []

/-- The channels whose acknowledge is a copy of another wire (see above). -/
def copyAs (μ : ChanMap) : K NC → List Nat
  | .join ins _ _ _ _ => ins.map Fin.val
  | .bjoin ins _ _ _ => ins.map Fin.val
  | .sink i => if i == out0 || i.val == 3 then [] else [i.val]
  | .mux s _ _ _ _ => [s.val]
  | .muxn s _ _ _ _ _ => [s.val]
  | .link i o => if μ.μA i == μ.μR o then [i.val] else []
  | _ => []

/-- Every identity the exceptions claim holds. -/
def copyOK (μ : ChanMap) : Bool := ops.all fun k => match k with
  | .forkG i os => os.all fun o => μ.μR o == μ.μR i
  | .forkH i os _ _ _ _ => os.all fun p => μ.μR p.1 == μ.μR i
  | .join ins o _ _ _ => ins.all fun x => μ.μA x == μ.μA o
  | .bjoin ins o _ _ => ins.all fun x => μ.μA x == μ.μA o
  | .sink i => i == out0 || i.val == 3 || μ.μA i == μ.μR i
  | .mux s _ _ z _ => μ.μA s == μ.μA z
  | .muxn s _ _ _ z _ => μ.μA s == μ.μA z
  | _ => true

/-- The nodes of all other wires (computed from three channel lists, one pass over `ops` each). -/
def drivenOf (μ : ChanMap) (crs srcs cas : List Nat) : List Nat :=
  ((List.finRange NC).filter fun c => !crs.contains c.val && !srcs.contains c.val).map μ.μR ++
  ((List.finRange NC).filter fun c => !cas.contains c.val).map μ.μA

def drivenL (μ : ChanMap) : List Nat :=
  drivenOf μ (ops.flatMap forkOuts) (ops.flatMap srcOuts) (ops.flatMap (copyAs μ))

def srcL (μ : ChanMap) : List Nat := (ops.flatMap srcOuts).map fun c => μ.μR (Fin.ofNat NC c)

/-- **The strengthened map predicate.** -/
def WireOK (μ : ChanMap) : Prop :=
  MapOK μ ∧ copyOK μ = true ∧ (drivenL μ).Nodup ∧
    (∀ x ∈ srcL μ, ∀ y ∈ srcL μ, x = y) ∧ (∀ x ∈ srcL μ, x ∉ drivenL μ)

/-- Duplicate-freeness as a `Bool` (cheap in the kernel). -/
def nodupB : List Nat → Bool
  | [] => true
  | x :: xs => !xs.contains x && nodupB xs

theorem nodupB_sound : ∀ l : List Nat, nodupB l = true → l.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    simp only [nodupB, Bool.and_eq_true, Bool.not_eq_true'] at h
    refine List.nodup_cons.2 ⟨fun hm => ?_, nodupB_sound xs h.2⟩
    have := List.contains_iff_mem.2 hm
    rw [h.1] at this; exact absurd this (by decide)

theorem nodupB_complete : ∀ l : List Nat, l.Nodup → nodupB l = true
  | [], _ => rfl
  | x :: xs, h => by
    have h' := List.nodup_cons.1 h
    simp only [nodupB, Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨?_, nodupB_complete xs h'.2⟩
    cases hc : xs.contains x
    · rfl
    · exact absurd (List.contains_iff_mem.1 hc) h'.1

theorem copyOK_T : copyOK μT = true := by decide +kernel
theorem crs_eq : ops.flatMap forkOuts = crsL := by decide +kernel
theorem srcs_eq : ops.flatMap srcOuts = [0, 1, 2] := by decide +kernel
theorem cas_eq_T : ops.flatMap (copyAs μT) = casL := by decide +kernel
theorem drivenL_T : drivenL μT = drvL := by
  unfold drivenL; rw [crs_eq, srcs_eq, cas_eq_T]; decide +kernel
theorem drivenL_T_len : drvL.length = 657 := by decide +kernel
theorem drivenL_T_nodupB : nodupB drvL = true := by decide +kernel
theorem drivenL_T_nodup : (drivenL μT).Nodup := drivenL_T ▸ nodupB_sound _ drivenL_T_nodupB
theorem srcL_T : srcL μT = [3275, 3275, 3275] := by unfold srcL; rw [srcs_eq]; decide +kernel
theorem src_not_driven_T : (drivenL μT).contains 3275 = false := by
  rw [drivenL_T]; decide +kernel

/-- **The generated table meets the strengthened predicate.** -/
theorem μT_wire : WireOK μT := by
  refine ⟨μT_ok, copyOK_T, drivenL_T_nodup, ?_, ?_⟩
  · intro x hx y hy
    rw [srcL_T] at hx hy
    simp at hx hy
    rw [hx, hy]
  · intro x hx hm
    rw [srcL_T] at hx
    simp at hx
    subst hx
    have := src_not_driven_T
    rw [List.contains_iff_mem.2 hm] at this
    exact absurd this (by decide)

/-- **`WireOK` is strictly stronger than `MapOK`**: the witness map `μW` meets `MapOK` and fails
`WireOK` (node 65 is read for many distinct driven wires). -/
theorem μW_not_wire : MapOK μW ∧ ¬ WireOK μW := by
  refine ⟨μW_ok, fun h => ?_⟩
  -- many driven wires (e.g. the requests of channels 7 and 8, both cold) read node 65
  have h7 : nodupB (drivenL μW) = false := by
    unfold drivenL; rw [crs_eq, srcs_eq, show ops.flatMap (copyAs μW) = casW by decide +kernel]
    decide +kernel
  rw [nodupB_complete _ h.2.2.1] at h7
  exact absurd h7 (by decide)

/-- **Headline: gcd_hw from reset, with the generated channel map** (H_MAP discharged by
`μT_ok`). Every bounded GMW run `v` of `gNet` with rst held on `(0, E]`, `E ≥ T0 = 23(D+W+1)`,
and every C channel family `r` whose wires at `T0` are the values of the table's nodes
(H_MAP_T0) and which from `T0` on follows C's gate models, bundling and a single start offer:
every `out0` latch at or after `T0` carries `Nat.gcd a b`. -/
theorem gcd_hw_safe_after_reset_map (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31)
    {v : Nat → Nat → Bool} (Rn : Run gNet v) {D W : Nat} (hB : Bounded gNet v Rn D W) (E : Nat)
    (H_RST_HELD : ∀ k, 0 < k → k ≤ E → TernaryPhases.InputsIn gNet v gA k)
    (H_HOLD_LONG' : T0of D W ≤ E)
    (r : Fin NC → Chan)
    (H_MAP_T0 : ∀ c : Fin NC, (r c).req (T0of D W) = v (T0of D W) (reqL.getD c.val 0) ∧
      (r c).ack (T0of D W) = v (T0of D W) (ackL.getD c.val 0))
    (H_CELLS_AFTER : ∀ o : Fin NO, CellA r (T0of D W) (srcV a b) (opAt o))
    (H_BUNDLE_AFTER : ∀ c, HeldA (r c) (T0of D W))
    (H_START_AFTER : ∀ t, T0of D W ≤ t → riseB (r start).req t = false) :
    ∀ e, T0of D W ≤ e → fallB (r out0).ack e = true → (r out0).dat e = Nat.gcd a b :=
  gcd_hw_safe_after_reset a b ha hb Rn hB E H_RST_HELD H_HOLD_LONG' r μT μT_ok H_MAP_T0
    H_CELLS_AFTER H_BUNDLE_AFTER H_START_AFTER

/-- **Joint non-vacuity of `gcd_hw_safe_after_reset_map`** (a = 12, b = 18): B's GMW run `wRun`
of `gNet` (`D = 40`, `W = 1`, rst held on `(0, 967]`), the frozen C family `frzC chW` and the
generated table meet every hypothesis. -/
theorem reset_capstone_map_nonvac :
    ∃ (v : Nat → Nat → Bool) (Rn : Run gNet v) (D W E : Nat) (r : Fin NC → Chan),
      0 < D ∧ 0 < W ∧ Bounded gNet v Rn D W ∧
      (∀ k, 0 < k → k ≤ E → TernaryPhases.InputsIn gNet v gA k) ∧ T0of D W ≤ E ∧
      (∀ c : Fin NC, (r c).req (T0of D W) = v (T0of D W) (reqL.getD c.val 0) ∧
        (r c).ack (T0of D W) = v (T0of D W) (ackL.getD c.val 0)) ∧
      (∀ o : Fin NO, CellA r (T0of D W) (srcV 12 18) (opAt o)) ∧
      (∀ c, HeldA (r c) (T0of D W)) ∧
      (∀ t, T0of D W ≤ t → riseB (r start).req t = false) := by
  refine ⟨ResetCapstoneWit.wv, ResetCapstoneWit.wRun, 40, 1, 967, frzC Wit.chW,
    by decide, by decide, ResetCapstoneWit.wBounded, ResetCapstoneWit.w_rst_clean, by decide,
    ?_, ?_, ?_, ?_⟩
  · intro c
    obtain ⟨_, a2, _, a4, _, _, a7, a8⟩ := μT_facts c
    have e : ∀ n, n ≠ 0 → ResetCapstoneWit.wv (T0of 40 1) n = gR n := by
      intro n hn
      rw [ResetCapstoneWit.wv_lt (by decide), ResetCapstoneWit.frz_gate hn]
    exact ⟨by show _ = ResetCapstoneWit.wv _ (μT.μR c); rw [e _ a2, a7]; rfl,
      by show _ = ResetCapstoneWit.wv _ (μT.μA c); rw [e _ a4, a8]; rfl⟩
  · intro o
    exact frozen_cellA _ _ _ _ (side_all o) (Wit.w_cells o)
  · intro c t _ _ _; rfl
  · intro t _; unfold riseB; cases hot start <;> rfl

end Formal.Cells.ResetCapstoneMap
