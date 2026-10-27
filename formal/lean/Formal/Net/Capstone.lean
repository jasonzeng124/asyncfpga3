import Formal.Net.OpsLink
import Formal.Net.OpsMuxNOp
import Formal.Net.OpsCM
import Formal.Net.CapstoneRing

/-!
# Probe C-8l: the capstone glue (shard C's part), and exactly where it stops

What the pieces give (all proved, no hypotheses beyond the named gate-model fields):
* token level (C-8i/8k): `GcdHw.Gcd.gcd_hw_graph_computes_gcd` — for `a, b < 2^31` every
  complete run of the graph bdc emits ends with exactly `[Nat.gcd a b]` on `out0`;
* cells (8f/8j/8l): every cell kind gcd_hw instantiates is an Ops operator (`fork_op`,
  `join_op`, `steer_op`, `mux_op`, `Mux.sink_op`, `CM.amerge_op`, `Link.link_op`,
  `MuxN.muxn_op`; the 3-input control_merge is two `amerge_op`s, `amerge3_cascade`);
* network (8f): `Ops.net_refines`, `net_prefix` — any network of operators, every channel
  bundled, refines every TOTAL stream solution of its token equations;
* structure (8l): `GcdHw.Gcd.gcdhw_ring_ge3` — every cycle of bdc's gcd_hw graph carries at
  least 3 bd_link stages.

`latched_const` below is the end-to-end reduction: if the token equations of the circuit's
network have a solution whose `out` stream is constantly `g`, then every token the circuit
EVER latches on `out` is `g`, and at every time the latched list is `g` repeated.

NOT proved (formal/notes/C-8l-capstone.md, C-gcd_hw-hypotheses.md §5): the premise
`O_SOLUTION` for gcd_hw. It needs (O1) the circuit's control_merge winner streams to equal the
token run's labels (a simulation of the token LTS by the circuit), and (O2) a total periodic
stream solution built from the token run's per-channel histories; plus (O4) binding the Ops
gate models to the generated cells. So `gcd_hw_conditional` is conditional, and says so in
its hypothesis name.
-/

namespace Formal.Net.Capstone
open Formal.Net Formal.Net.Handshake Formal.Net.Ops

variable {C O : Type}

/-- End-to-end reduction for any network: a solution whose `out` stream is constantly `g`
forces every latched `out` token to be `g`, and the latched list at every time to be
`g, g, ..., g` (one per close so far). -/
theorem latched_const (N : Net C O) (ch : C → Chan) (E : O → (C → Nat → Nat) → Prop)
    (hop : ∀ o, OpProto ch (N.ins o) (N.outs o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (hdat : ∀ o, OpData ch (N.ins o) (N.outs o) (E o))
    (out : C) (g : Nat)
    (O_SOLUTION : ∃ ref : C → Nat → Nat, (∀ o, E o ref) ∧ ∀ k, ref out k = g) :
    (∀ k e, TokAt (ch out) k e → (ch out).dat e = g) ∧
    (∀ t, closedVals (ch out) t = List.replicate (cnt (fallB (ch out).ack) t) g) := by
  obtain ⟨ref, href, hout⟩ := O_SOLUTION
  refine ⟨fun k e h => ?_, fun t => ?_⟩
  · rw [net_refines_close N ch E hop H_BUNDLE hdat ref href out k e h, hout]
  · rw [net_prefix N ch E hop H_BUNDLE hdat ref href out t]
    apply List.ext_getElem
    · simp
    · intro i h1 h2; simp [hout]

/-- The capstone statement for gcd_hw, CONDITIONAL on the open premise `O_SOLUTION`
(see the module doc). For any handshake network whose operators meet their cell specs and
whose channels are bundled: every value latched on `out0` is `Nat.gcd a b`. -/
theorem gcd_hw_conditional (a b : Nat) (N : Net C O) (ch : C → Chan)
    (E : O → (C → Nat → Nat) → Prop)
    (H_CELLS : ∀ o, OpProto ch (N.ins o) (N.outs o) ∧ OpData ch (N.ins o) (N.outs o) (E o))
    (H_BUNDLE : ∀ c, Held (ch c)) (out0 : C)
    (O_SOLUTION : ∃ ref : C → Nat → Nat, (∀ o, E o ref) ∧ ∀ k, ref out0 k = Nat.gcd a b) :
    ∀ k e, TokAt (ch out0) k e → (ch out0).dat e = Nat.gcd a b :=
  (latched_const N ch E (fun o => (H_CELLS o).1) H_BUNDLE (fun o => (H_CELLS o).2) out0 _
    O_SOLUTION).1

/-- bdc's 3-input control_merge (`emit_amerge` n = 3) is a CASCADE of two `bd_arbiter`
stages: stage 1 arbitrates in0 against in1 into an internal channel `acc`
(`R0`/`A0` of `uarb1` = `r1`/`A1` of `uarb2`), stage 2 arbitrates `acc` against in2.
Each stage is the 2-input gate model `CM.AMerge`; `acc`'s bus is the stage-1 index
(`won1`, plus the selected data: zero bits in gcd_hw), which bdc's priority encoder reads
together with `won2` (`index = won2 ? 2 : won1`, a function of the two stage buses at the same
tick, H_DATA_COMB). So the cascade is two Ops operators and needs no new cell proof; its
only new obligation is H_BUNDLE of the internal `acc` bus (B's H_BUNDLED_IDX). -/
theorem amerge3_cascade (ch : C → Chan) (c0 c1 c2 cacc cz : C) (g11 g21 g12 g22 : Trace)
    (M1 : CM.AMerge (ch c0) (ch c1) (ch cacc) g11 g21)
    (M2 : CM.AMerge (ch cacc) (ch c2) (ch cz) g12 g22) :
    (OpProto ch [c0, c1] [cacc] ∧
      OpData ch [c0, c1] [cacc] (CM.amergeEq (CM.winner (ch cacc)) c0 c1 cacc)) ∧
    (OpProto ch [cacc, c2] [cz] ∧
      OpData ch [cacc, c2] [cz] (CM.amergeEq (CM.winner (ch cz)) cacc c2 cz)) :=
  ⟨CM.amerge_op ch c0 c1 cacc g11 g21 M1, CM.amerge_op ch cacc c2 cz g12 g22 M2⟩

/-- The ring graph's weights are the exported link stages: every edge of `ringG` weighs
exactly the `links` entry of its channel (`ringCh`), 0 for a wire. -/
theorem ring_weights_are_links :
    (GcdHw.Gcd.ringG.zip GcdHw.Gcd.ringCh).all (fun p =>
      p.1.w == ((GcdHw.Gcd.links.find? (fun q => q.1 == p.2)).map (·.2)).getD 0) = true ∧
    GcdHw.Gcd.ringG.length = GcdHw.Gcd.ringCh.length := by
  decide +kernel

/-- Negative control for `gcdhw_ring_ge3`: the checker is not trivially true. The explicit
cycle `aCycle` carries 7 stages, so "every cycle carries at least 8" is false. -/
theorem gcdhw_not_ge8 : ¬ RingCheck.AllCyclesGe GcdHw.Gcd.ringG 8 := by
  intro h
  have hw : RingCheck.Walk GcdHw.Gcd.ringG GcdHw.Gcd.aCycleStart GcdHw.Gcd.aCycleStart 7 := by
    have hf := GcdHw.Gcd.aCycle_follow
    unfold GcdHw.Gcd.aCycle at hf
    exact GcdHw.Gcd.follow_start _ _ _ _ _ _ hf
  have := h _ _ hw
  omega

end Formal.Net.Capstone
