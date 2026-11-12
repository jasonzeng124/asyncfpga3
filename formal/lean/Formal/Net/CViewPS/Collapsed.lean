import Formal.Net.CViewPS.All

/-!
# THE target's logic gates read their sources through the routing (shard C, S4 groundwork)

**Problem, plainly.** `DecodedPS.net` (THE target, gcd_ps_e6bb4aec) has 186,873 gates, of which
all but 19,878 of the circuit's are one-pin copy gates (pips, wires, site hops). Cell-level
reasoning needs each logic gate (LUT, MUXF, CARRY4 piece, constant) with its pins tied to the
logic output (or environment/undriven node) they really read, and the delay of that read.

**Proved** (`collapsed`): for every delay parameter with `0 ≤ κ ≤ 1`, `0 < g`, and every
behaviour of THE theorem's circuit (`Behaves p (circuit net boundary) x`), at the behaviour's one
corner `c`: every logic gate `e.1` in the generated view `logicView cs keepPS vss` satisfies
`CGateOK`: pin `i` reads node `src i` (the end of its copy chain) at a non-decreasing time whose
delay is a sum of one `Adm`-admissible delay per arc on the way (the pin's own arc, then each
copy gate's), output = INIT at those reads. `view_complete`: every gate of the circuit that is
not a copy gate is in the view. The chains are recovered by following the circuit's copy map
(`cmPS`), which the kernel checks against the gate list chunk by chunk (`facts`), and every pin's
claimed source and chain length are kernel-checked (`views_ok`).

**Not shown.** Anything about what the logic gates compute together (cells, handshakes): this
is the netlist side of S4 only. Before `cStart` (a few ns: the gate's and its chains' longest
delays) nothing is said (power-up). Two readers of one routed net are collapsed separately.
-/

namespace Formal.Net.CViewPS
open Formal.Target Formal.Target.DecodedPS Formal.Timing.SpecSettle Formal.Timing.SpecChain
  Formal.Timing.SpecChainM Formal.Timing.ChunkCM

theorem gates_flatten : gates = cs.flatten := by
  simp [gates, cs]

theorem circuit_eq : (circuit net boundary).gates = cs.flatten.filter keepPS := by
  rw [circuit_gates, gates_flatten]

/-- **The collapsed view of THE target's circuit.** -/
theorem collapsed {p : DelayPar} (hp : Sane p) {x : Beh} (hb : Behaves p (circuit net boundary) x) :
    ∃ c : ℚ, 0 ≤ c ∧ c ≤ 1 ∧ ∀ e ∈ logicView cs keepPS vss,
      CGateOK p c e.1 (fun i => ((toPCs cmPS (gaOf cs 2500) e.1 e.2).getD i ⟨0, []⟩).src)
        (pinArcs e.1 (toPCs cmPS (gaOf cs 2500) e.1 e.2))
        (cStart p e.1 (toPCs cmPS (gaOf cs 2500) e.1 e.2)) x :=
  collapse_chunks hp (circuit_wf net_wf) hb (by decide) (by decide) circuit_eq tl_len facts views_ok

/-- Every logic gate of the circuit is in the view. -/
theorem view_complete {g : Gate} (hg : g ∈ (circuit net boundary).gates) (hn : cpIn g = none) :
    ∃ pv, (g, pv) ∈ logicView cs keepPS vss := by
  rw [circuit_eq, List.mem_filter] at hg
  refine logicView_complete rfl (fun q hq => ?_) hg.1 hg.2 hn
  have := views_ok q hq
  simp only [chunkViewOK, Bool.and_eq_true, beq_iff_eq] at this
  exact this.1

end Formal.Net.CViewPS
