# What the research branch should change (from claude/formal, shard A)

Short and concrete. Each item: what was found, the evidence (a command that
reproduces it, or a Lean theorem checked by `formal/check.sh`), and the change.
"Proved" means proved about the stated model. Whether the model matches
silicon is a separate, named hypothesis, and each item says which one.
Draft: rules A/E/F/H/I/J will be filled in from shard C's verified checker
(phase 2).

## 1. GLS: LUT specify paths propagate edges early (fix first)
- **Found:** `cells/gls/prims.v` `SLICE_LUTX` under iverilog 12 `-gspecify`
  is neither inertial nor transport. It is "sample at fire": a change at t
  schedules an update at t+d, the update copies the function value at fire
  time, and nothing is cancelled. An edge that follows an earlier change within d
  comes out early; one example has a 4 ps latency through a 124 ps arc.
- **Evidence:** `sh formal/tools-A/gls-compare/run_all.sh /tmp/gls-compare/prims.v /tmp/gls-compare`
  (copy prims.v from origin/claude/research first; about 3 min): 140/140 random traces
  fit SAF, against 48 for inertial and 4 for transport. Lean: `Formal/Core/Delay/SAF.lean`:
  - `saf_early`: early edges.
  - `saf_not_transport`: no lower delay bound ≥ 2 ps holds.
  - `xor_settle_late`, `chain_early`: GLS settle time is neither an upper nor a lower bound on reconvergent logic.
  - `saf_eq_delay_iff`: exact condition under which a GLS run equals the pure-delay run.
- **Change, either of:**
  1. Make LUT paths transport: drive O5/O6 through a `#d` transport assignment
     (as `-DGLS_TRANSPORT_IC` already does for ICBUF) and keep the specify block
     only for SDF annotation.
  2. Keep the specify paths and add a monitor that flags every fire whose copied
     value differs from the value its own scheduling change produced. This is
     `Faithful` in SAF.lean; a run with zero flags equals the transport run
     (`net_eq_delay_of_faithful`).
- **Then:** rerun the gcd GLS both ways and diff the bundled-data margins.
  Until that is done, a GLS margin on a cone whose LUTs glitch is not a bound.
- **Also:** the annotated (`gate.vvp`) and baked (`run_baked.vvp`) builds treat
  wire pulses differently, LUT-like in one and transport in the other.
  "Every event timestamp identical" held for the gcd run only.

## 2. GLS: inertial LUT paths cannot show runts
Even for isolated pulses, the GLS removes pulses narrower than the arc
(`Inertial.lean`: `inertialRD_pulse_short`, `noShort_of_inertialRD`). So a GLS
pass is not evidence of runt-freedom for any C-element, latch or arbiter
loop. The faithful model is the involution channel, which shrinks pulses
continuously (`Involution.lean`: `pulseWidth_small`). Change: transport LUT paths
(item 1), plus a pulse-width sweep through a LUT chain on the board to fit
δ↑/δ↓ (notes/A-delay-involution.md).

## 3. The LUT mux tree in prims.v is upside down (low priority)
`SLICE_LUTX` puts A6 at the leaves; the silicon has A6 at the root (UG474). This
does not change logic or X values (`LutTree.evalTree_swap`,
`Bridge.lt_evalTree_sil_eq_keval`), only timing. Per-pin delays live in the site-pin
arcs (A1 up to 0.516 ns slow max, A6 0.005 ns; notes/A-fidelity.md). Check that
the F1 delay calculator includes them.

## 4. prjxray SDF triples are (FAST)(SLOW), not rise/fall
`prjxray-db timings/*.sdf` is written by `utils/makesdf.py` with the two
triples as fast and slow corner. A standard SDF reader takes them as rise/fall.
prjxray has no rise/fall data, and setup/hold exist only at the slow corner.
Check every reader in the F1 calculator and gen.py (notes/A-fidelity.md).

## 5. Delay model for any margin: shared corner + local scatter κ
Independent per-arc bands [fast-min, slow-max] are 3–4× wide, so no bundling
inequality can be proved from them. The model to use is one corner shared by
the die, affine per arc between its fast and slow endpoints, plus local
scatter |ε| ≤ κ (`Formal/Core/Substrate/CornerNat.lean`,
`Delay/Corner.lean`). Checking a bundling inequality at the fast and slow
endpoints is then exact for every corner (`bundle_realizes`,
`endpoints_sound_real`). The guardbands map to κ:
- skew.py rule E is sound iff κ ≤ 19.9% (`ruleE_sound`, tight);
- tighten.py rule A is sound iff κ ≤ 9.1% (`ruleA_sound_rel`, tight).

**The κ that matters is unmeasured.** Per path, the 128-ring data gives
κ ≥ 0.311 (`python3 formal/tools-A/kappa/kappa.py repo`). The rules compare two
paths, so what they need is κ on a path difference.
- **Cheapest step:** commit the per-ring raw logs of the `ro_many` 128-ring run
  (`kappa.py rawlogs` parses them).
- **Real test:** a ring with a shared body that splits into two tails, rejoined
  at a scan-selected LUT mux (the body and its offset cancel). Use ≥ 64 pairs per
  length class, 4 seeds and two temperatures, then run `kappa.py pairs`
  (schema in `formal/tools-A/kappa/data/pairs_template.csv`).

## 6. bd_arb: two header claims to correct, one margin to check
- A same-sense tie (both requests rising from idle) is a static hazard on q,
  not "resolved deterministically" (`LutAudit.arb_tie_from_idle_hazard`; shard B
  7a, timed). Add same-sense near-ties to the MTBF experiment
  (cells/verify/MTBF.md).
- The losing grant can pulse without metastability
  (`LutAudit.arb_grant_near_tie_runt`). A2 = C(g2, A0) absorbs it, but bdc/emit.py's
  `won = g2 | ack` drives `index` directly. Check that nothing samples `index`
  inside that window.
- Shard B: rule J ignores per-pin site-pin delays (up to ~0.5 ns) and uses a
  flat 124 ps LUT arc; proposed rule J' in formal/notes/B-arb-a0fork.md.

## 7. Hypotheses each proof rests on, and their tests
See `formal/notes/A-substrate.md` (graded list) and FEASIBILITY.md's fidelity
table. The ones only the board can test:
- `H_mux_kleene`: a LUT mux with a mid-rail select and equal data passes the
  data. Test: a masked-pin toggle into a fabric edge counter.
- The involution δ↑/δ↓ per LUT pin and edge. Test: a pulse-width sweep with a TDC.
- κ on path differences: item 5.
