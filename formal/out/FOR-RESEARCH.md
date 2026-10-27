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

**The κ that matters is unmeasured.** (Correction: the ring ratios behind κ ≥ 0.311 are
measured/predicted against SDFs written *before*
`patches/nextpnr-xilinx-lut-perm-sink.patch` (shard C,
`notes/C-10c-prjxdelay.md`): those SDFs charged 0–150 ps for permuted LUT pins
where the routed hop is ~295 ps, on ~85% of chain hops. Against corrected
predictions, comparable rings agree to 1.1% (prjxray median) / 6.7% (current
SDF), population against population. So the 0.311 bound measures that SDF bug,
not silicon scatter, and does **not** refute the per-path hypotheses of
`ruleE_sound`/`ruleA_sound_rel`. κ (per path and on differences) is unmeasured
on the current toolchain; the per-ring data and bitstreams needed to redo it
are not in the tree.) Per path, the 128-ring data gives
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

## 6b. Add a rule: C-element own feedback faster than every neighbour loop
`FbBound` (shard C, Formal/Net, track 8 Muller timed): for every C-element,
feedback-wire hi < the lo-sum of each loop through a neighbour back to its
inputs (strict; equality is a function hazard). Independently flagged by
`xaudit` (formal/tools-A/xaudit/run_all.sh, `pipe3_slowfb`). Placement-
dependent and checked by no rule today. Change: add it to tighten.py as a
gate, with prjxray slow-max for the feedback and fast-min for the loops.

## 6c. The own-feedback race on real gcd_hw routes depends on corner mixing
On gcd_hw R5 (seeds d, 3, 4, 5), the C-element own-feedback obligation holds at
each single corner, but with per-element [fast_min, slow_max] bands there are
4–10 violating candidates per seed. One reproduces concretely: a 9 ps runt in
`ucontrol_merge4.uarb1.ua2` on seed d, circulating in its loop, answer still
correct (`formal/tools-A/xaudit/gcd/results/`). Whether silicon can mix like
this is exactly κ on a path difference (item 5). Until κ is measured, check
these feedback loops with the ring-measured scatter applied.

## 6c'. First items to test on gcd_hw R5 (fail at skew.py's own guardband)
Events5 (notes/A-events5.md, `formal/tools-A/xaudit/events5/run5.sh`): with one die
anywhere in [0.668, 1.0] × slow max (skew.py's 0.772/1.155 spread), four race
margins go negative: three arbiter re-arm entries on seed d (−52, −26, −9 ps) and
the rig's `uenv1` own-feedback (−19 ps, seed 5). Check them in the board-fidelity
GLS with per-element scatter. Also: rule F misses the in-flight term at the head of
`bd_delay_gated` (g[0] is a plain buffer; −365 ps seed d `ushli0`, −726 ps seed 3
`uselect1` on mixed dies); add the term to rule F (gating g[0] would touch frozen
cells/rtl).

## 6d. toolchain.sh does not check runtime libraries
A restored toolchain cache lacked libtcl8.6 and boost 1.83 at runtime. toolchain.sh
greps the binary and passed anyway. Add `ldd nextpnr-xilinx | grep 'not found'` (and
yosys) to it, and a check that can fail on a stripped install.

## 6e. Race checks need per-pin site-pin delays (nextpnr's SDF lacks them)
`xevents2pin` (`formal/tools-A/xaudit/pin/run.sh`, notes/A-events2pin.md): the
site-pin delay difference between a C-element's input pin and its feedback pin is
−468..+308 ps at the slow corner on gcd_hw R5, and goes the unsafe way on ~46% of
own-feedback pins; the placer's pin permutation puts feedback on A1 (slowest) ~20%
of the time. Any race/bundling check fed from nextpnr's SDF is wrong by that
amount. Feed checks from prjxray per physical pin (`xray_delay.py`, mapped through
`X_ORIG_PORT_A<k>`; `formal/tools-A/xaudit/pinbands.py` does this).

## 7. Hypotheses each proof rests on, and their tests
See `formal/notes/A-substrate.md` (graded list) and FEASIBILITY.md's fidelity
table. The ones only the board can test:
- `H_mux_kleene`: a LUT mux with a mid-rail select and equal data passes the
  data. Test: a masked-pin toggle into a fabric edge counter.
- The involution δ↑/δ↓ per LUT pin and edge. Test: a pulse-width sweep with a TDC.
- κ on path differences: item 5.

## 8. GLS_MODEL=fid: four primitives still disagree with the model (2026-10-27, research 5d535d7)

Evidence and reproducers: `formal/notes/A-gls-compare-2.md`, `sh formal/tools-A/glsdiff/run_all.sh` (~3 min).


- **CARRY4 and SLICE_LATX are still sample-at-fire under GLS_MODEL=fid, so
  carry-chain edges can arrive early.** Reproducer:
  `formal/tools-A/glsdiff/tb_carry_saf.v`. O0 rises 23 ps after S0 through a
  223 ps arc; latch Q rises 40 ps after D through a 100 ps arc.
  - Proposed fix for `fid_core.vh`: a `FID_CARRY4`. For each output Oi/COi, keep
    a transport copy of every support pin delayed by that pin's arc to that
    output minus 1 (`s0_o0 <= #(TS0O0-1) S0`, …). Evaluate the existing
    `prims.v` equations on the copies, and put each output through `FID_SAMPLE`.
  - The same for `SLICE_LATX`: per-pin transport copies of D/CK/CE/SR (each
    TCKQ − 1), then the zero-time latch function.
  - Acceptance: tb_carry_saf must give O0 at 1223–1233 and 1423.
- **SLICE_LATX X handling is pessimistic.** Proposed fix in `prims.v`:
  ```
  else if (CK === ~GHIGH || CE === 1'b0) q = q;
  else if (CK === GHIGH && CE === 1'b1) q = D;
  else q = (q === D) ? q : 1'bx;
  ```
  Also, for SR = x: `q = (SRVAL === qn) ? SRVAL : 1'bx`, where `qn` is the
  value the SR = 0 branch would give. Check: `tb_seq_x.v` L1–L3 should give 0,
  as Lean `LDCE_INIT` does.
- **SLICE_FFX hides X on SR and CE (default and fid).** Proposed fix: at
  posedge CK, `nv = (SR === 1'b1) ? SRVAL : (SR === 1'b0) ? (CE === 1'b1 ? D : CE === 1'b0 ? Q : (D === Q ? Q : 1'bx)) : ((CE===1'b1?D:CE===1'b0?Q:(D===Q?Q:1'bx)) === SRVAL ? SRVAL : 1'bx)`.
  Check: tb_seq_x F1 and F2 should give x.
- **FID_RESOLVE's decision point** (from a Float computation of the Lean loop recurrence plus a symmetry argument, not a proved theorem; Lean proves only that the critical gap lies in about (9, 424) ps). The 50% point is TLOOP − WIN/2 (measured
  at 349 ps for TLOOP 424). Lean's involution OR loop (the same loop as
  bd_arbcell's state, ArbInvolution `stF_runt`) decides at about TLOOP/2
  (212–246 ps for τ = 40–200), deterministically on each side.
  - Proposed fix: `delta = p - TLOOP/2 + noise` (with asymmetric arcs:
    `p - TLOOP*tf/(tr+tf)`), with `TLOOP/2` exposed as `+META_CENTRE=`.
  - Re-run tb_f3_meta: with r2 360 ps late, r1 should win about 200/200.
  - Also fix the `fid_core.vh` comment "rejected: the node never left". The runt
    is emitted to fanout at full width.
- **Scatter vs. proofs.** GLS_SCATTER(_REGION) factors are unbounded Gaussians.
  A scatter run therefore tests delays outside the κ ≤ 0.199 regime where
  rules E and A are proved sound. Either clip at a stated κ, or say so where
  scatter results are quoted.

