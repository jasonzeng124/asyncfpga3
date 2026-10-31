import Formal.Core.XAudit.Events5

/-!
# Wip/Events5 — what is still open after probe A-events5 (NOT claimed; `sorry` marks each)

Proved (`Formal/Core/XAudit/Events5Line.lean`, `Events5.lean`, check OK):
`Beh4.safe` (W-E4i, the integration), `Beh4.verdict` / `Beh4.verdictW` (the
verdict from certificates: `Back4` / `BackW` with R1, R3 and SUB walk steps,
`LineCert`, `ExclCert`), `wd_sound`, `exclOK_of_cert` (binary merges),
`lineOK_of_cert`, the delay-line lemmas `tree_contig`, `line_and`, `line_or`,
`hop_skew`, `prefix_skew`.

Still open, each with the obligation stated as precisely as I can:
-/

namespace Formal.Core.XAudit.Events5.Wip

open Formal.Core.XAudit.Events5

/-- **W-E4g: GuardOK from ENTRY/EXIT** (~1.5 days). `Beh4.GuardOK` is a named
hypothesis of `safe`. To discharge it, `gc j p s` (the guarded pin's count)
must be DEFINED from the model: for bd_mux's `x_ack = C(j0, z_ack)` it is the
count of `z_ack` restricted to the transactions of branch `b`, i.e. `filt` over
`z_ack`'s OWN transaction sequence, whose branch labels are those of the mux's
merge order — a second select sequence that must be related to the steer's
(`sel` of the group) by a FIFO argument through the merge (`merge_excl` gives
exclusivity, not order). With that definition, ENTRY (`hi(D→j) ≤ lo(D→S) +
loF S + lo(S → … → guard)`) and EXIT (`hi(D→j) − lo(D→j) + hiF j + hiQ j ≤ W D`)
must give the two conjuncts of GuardOK; both need a LOWER-bound walk judgement
(a count is at least another's, `M_D (G s) ≥ …`), which the min-plus recursion
does not provide: lower bounds need every pin of a stage (a cut), not one walk.
The H_ARB acknowledges (`A_b = C(g_b, A0)`) are the same shape with the virtual
core's `ctl` as the steer. -/
theorem guard_ok_shape : True := by
  sorry -- W-E4g

/-- **W-E4n: design_beh4** (~1.5 days). Every `Circuit.Sat` behaviour of the
parsed skeleton (`events4/skel.py` output, recognised by `Events4Main`) is a
`Beh4` for the `Net4`/`Bands4` the recogniser builds: stage/merge/line/steer/
guard roles from the INIT over physical pins (as `Events2Design.layout` +
`Recog2`), the copies' warps by `chain_warp` through the buffers/inverters, and
the field `hskew` from `Events5Line.hop_skew` (+ `prefix_skew` for a shared
prefix) at each gate of a line, with `Bands4.dw` the window `contig5` computes.
`mg0` (a merge is low at time 0) follows from the acyclicity of the OR gates.
H_ARB (the arbiter cores as virtual mux cores) enters here, as a hypothesis on
the arbiter LUTs' behaviour. Then an executable `Events5Main` would check
`Net4.OK`, `BackW` (derivations emitted by `ana5.py`), `LineCert`, `ExclCert`
by `decide` and print the verdict as the conclusion of `Beh4.verdictW`. -/
theorem design_beh4_shape : True := by
  sorry -- W-E4n

/-- **W-E4x: n-ary merges** (~0.5 day). `ExclCert` requires `ar x ≤ 2`; the
3-way mux merge (gcd: one) needs `fodd ≤ 1` from three U-bounds by distinct
branches of a `Fin 3` select (the 2-bit mux decode) and an n-ary `filt_add`. -/
theorem merge_excl_nary_shape : True := by
  sorry -- W-E4x

/-- **U through merges (U3)** (~0.5 day). `UArmD` certifies an arm's branch by a
token-free walk through STAGE pins ending at a filtered pin; `ana.py` also lets
a branch label pass through a reconverging merge (`compute_U` with `r3`). The
lemma: if a merge's arms are the two branches of `S` and `S` is U-bounded by
`(S', g', β')`, so is the merge (`reconv` + `filt` of a `filt`, which needs the
two select sequences to be nested). -/
theorem u_through_merge_shape : True := by
  sorry -- U3

/-- **The cascaded arbiter** (`control_merge12`, ~0.5 day): a 3-way virtual
core (one `σ` over three requests) so that the inner `R0` and the outer grant
are one merge of three branches (needs W-E4x). -/
theorem cascade_shape : True := by
  sorry -- cascade

end Formal.Core.XAudit.Events5.Wip
