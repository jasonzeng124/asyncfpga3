import Formal.Core.XAudit.Events6Beh

/-!
# Wip/Events6 — what is still open after probe A-events6 (NOT claimed; `sorry` marks each)

Proved in `Formal/Core/XAudit/Events6{Gate,Cert,Design,Beh}.lean` (check OK):
`gate_spec`, `chkT_sound`, `pairW_sound` (per-pin netlist semantics, trees, the
hop window with suffix cancellation and prefix width), `DW.sound`, `UA.sound`,
`WDX` / `wdx_sound` (walk derivations whose merge arms may be steered pins),
`Beh4F.verdictR` (the verdict with residual obligations), `ndReal`, `init0`,
**`design_beh4`** (W-E4n), **`design_verdict`** (what `xevents5` checks).

Open, each stated as precisely as I can:
-/

namespace Formal.Core.XAudit.Events6.Wip

open Formal.Core.XAudit.Events5

/-- **W-E4g, reduced (not proved).** `design_beh4` takes the guarded counts `gc`
as a free monotone argument, so GuardOK stays a hypothesis about the realisation.
The reduction I would prove next (≈ 0.5 day, a copy of `Beh4.safe`'s induction):

* choose `gc j p s := tg (c j) (Q j s) + (if (pin j p s ^^ neg j p) = q j s then 0 else 1)`
  where `tg c u` is the number of value changes of the wire `c` on `[0, u]`;
* GuardOK's second conjunct then holds BY CONSTRUCTION (a pin that differs from
  the feedback reads `ph v (tg + 1)`, else `ph v tg`; `q j s = ph v (tg (c j) (Q j s))`);
* its first conjunct holds inside `safe`'s induction once `tg (c j) u = M u j`
  for `u = Q j s < s` (a stage count moves by at most one per step, by `PinOK`);
* what remains is `gcmono`, i.e. PERSISTENCE: once a guarded pin shows the
  advanced value while its guard has advanced, it keeps showing it until the
  stage's own feedback has moved. This is a property of the pin's source `D`
  between two of the stage's samples: `D` must not fire in
  `[G s₁, G s₂]` with `s₂ - s₁ ≤ hiF j + hiQ j` — the EXIT inequality
  `hi(D→j) - lo(D→j) + hiF + hiQ < W D` gives it once the guarded pin's
  advance is not STALE, and ENTRY (`hi(D→j) < lo(D→S) + loF S + lo(S→…→guard)`)
  excludes staleness; ENTRY needs the lower-bound walk judgement (a count is at
  least another one), which the min-plus `M` recursion does not provide.
So GuardOK ⟸ persistence ⟸ ENTRY ∧ EXIT, with the second arrow the open part. -/
theorem guard_persist_shape : True := by
  sorry -- W-E4g

/-- **W-E4x: the 3-way merge** (gcd: `umux21`'s request OR; arms filtered by the
2-bit select patterns 00, 01, 10 of `ulink_n_index_97.stage[1]`). `Beh4` filters
with a Boolean per group, so a 2-bit pattern is its own group (`br = true`), and
exclusivity across the three groups needs the three `sel g` to be the
indicator functions of ONE value sequence `V` (`sel gᵢ k = (V k == patᵢ)`): a
hypothesis on the select parameter, then `fodd ≤ 1` by an n-ary `merge_excl`
(`filt` over `Fin 3`, `filt_add` generalised to a partition). -/
theorem merge_excl_ternary_shape : True := by
  sorry -- W-E4x

/-- **U3: branch labels through reconverging merges** (24 Back pins and 6 merges
per seed are residual for this alone). `ana.py`'s `compute_U` gives a merge the
U-label of its R3 source; `UArmX` certifies an arm only by a walk through STAGE
pins (or a steered arm). Needed lemma: if merge `x`'s arms are the two branches
of `S` and `S` is U-bounded by `(S', g', β')`, so is `x` — `reconv` plus a
`filt` of a `filt`, which needs the two select sequences nested. -/
theorem u_through_merge_shape : True := by
  sorry -- U3

/-- **The cascaded arbiter** (`control_merge12`): H_ARB's two-input virtual core
does not compose (the inner `R0` is read by the outer core's grant); a 3-way
virtual core (one `σ` over three requests). 3 Back pins and 1 merge residual. -/
theorem cascade_shape : True := by
  sorry -- cascade

end Formal.Core.XAudit.Events6.Wip
