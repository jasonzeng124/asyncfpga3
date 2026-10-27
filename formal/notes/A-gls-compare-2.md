# A-gls-compare-2: the formal model against the research GLS, second pass

Probe GLSdiff, 2026-10-27, shard A. PROGRAM.md: "Compare the model with the
board-fidelity GLS being built on claude/research. Where the two disagree,
find out which is wrong."

- **Previous pass:** `A-gls-compare.md`, committed bd78912 at 03:20 UTC. It
  does not record the research commit. By time it used `cells/gls/prims.v` at
  or before **19a93c1 (03:09)**. `prims.v` did not change between 19a93c1 and
  eda0c0c.
- **This pass:** `origin/claude/research` at **5d535d7** (10:39 UTC).
  - Sources were copied read-only with `git show` into `formal/tools-A/glsdiff/src/`.
  - Tools: iverilog 12, `-gspecify`, the same flags as `cells/gls/build.sh`.
  - Every number below can be reproduced with `sh formal/tools-A/glsdiff/run_all.sh`
    (about 3 min).

## What changed in the GLS since the first pass

| commit | change | relevant to |
|---|---|---|
| 801db02, 7dc5dde | `fid/xray_delay.py`: prjxray RC-tree (Elmore) delays. The SDF triple is (FAST_MIN : SLOW_MIN : SLOW_MAX), so "typ" is the slow-corner minimum. Site input-pin delays, fanout loading and every slice routing-BEL mux (OUTMUX/FFMUX/CLK/CE/SR) are now charged. One RC term is added to every column. | wires, corners |
| eda0c0c | new `SLICE_LATX` (LDCE/LDPE) model. Before this, a latch was simulated as a flop. | latches |
| 5567170 | opt-in `GLS_MODEL=fid` (`fid_core.vh`). Changes: per-pin **transport** LUT and MUXF7/8 (`FID_LUT6`, `FID_MUX2`); a metastability resolver on self-loop LUTs (`FID_RESOLVE`; gen.py sets `TLOOP` = feedback wire + the feedback pin's arc); a flop aperture resolver; `GLS_SDF_FIELD=band` (one shared position b = 0.38 in [fast_min, slow_max]); `GLS_SCATTER_REGION` (a Gaussian factor per 10×10-slice region) | LUT channel, metastability, corners |
| 5d535d7 | `bd_prims_sim.v` (the cell sim, not the GLS) moved to one corner | — |

These are unchanged:
- the default model, which is still SAF on every specify path;
- CARRY4, DSP, latch and BUFG, which are SAF even under fid;
- `run_baked.vvp`, which is used for all runs and has transport ICBUF wires;
- `gate.vvp`, the annotation gate, which still has specify-path (SAF) wires.

## Per primitive (FEASIBILITY fidelity table)

| primitive | Lean model | GLS now | agree? | experiment and result |
|---|---|---|---|---|
| LUT mux tree (function, X) | `Lut.keval` = `kevalSpec` (`keval_eq_kevalSpec`, `evalTree_eq_tableEval`) | `?:` tree; under fid the same tree on the delayed pins | **yes** | `kleene_check.py`, 30 INITs × 729 vectors × {O6, O5} plus 27 MUXF7 vectors: **43,767/43,767** equal under both default and fid |
| LUT channel | per-pin bounded transport, then the zero-time Kleene function (`Events2Pin`, `Pure.Chan`; SAF ⊂ `WinR 1 d` in Substrate) | default: SAF (unchanged). **fid: per-pin transport** | **fid: yes**, as one point of Lean's band. Default: no (see the first pass) | `channel_fit.py`, 1 pin: fid transport **60/60** (SAF 2, inertial 2); default SAF 60/60. `perpin_fit.py`, XOR with arcs 100/150 checked against the reference "delay each pin by its arc, then XOR": fid **60/60**, default 3/20 |
| routing wires and pips | `Pure`/`Win [lo, hi]` per sink arc; corner model `Corner.lean` (shared c, scatter \|ε\| ≤ κ) | transport ICBUF in the baked build. xray SDF columns are each one corner. `band` is one shared lerp (= `pathAt_eq_lerp`'s single c) | **yes** for columns and band | Scatter differs, but this is not a bug. GLS region and wire factors are **unbounded Gaussians**. Region σ = 0.16 alone exceeds κ = 0.199 (`ruleE_sound`'s limit) in about 21% of regions. So a scatter GLS run samples delays outside every κ-bounded Lean theorem. A failure there does not refute a Lean rule, and a pass is not covered by one |
| MUXF7/F8 | `kmux` (`Gen.mux_kleene`); "settle within hi" | fid: per-pin transport (`FID_MUX2`) | **yes** | covered by the Kleene check above and f3's T6 |
| **CARRY4** | Gen/Netlist equations, Kleene; timing band [lo, hi] per arc | **SAF even under fid** | **no** | `tb_carry_saf.v`: S0 pulses 1000–1010, then rises at 1200. **O0 rises at 1223, 23 ps after its cause, through a 223 ps arc**, in both default and fid. Lean's band admits no edge before lo (fast min). Transport gives 1223–1233 then 1423. **The GLS is wrong**: this is the first pass's early-edge defect, still live in every carry chain (comparators and adders, i.e. exactly the bundled data cones) |
| **latch (SLICE_LATX)** | `LDCE_INIT` via `Lut.keval` (`Gen/Netlist.lean`) | `always @*` plus specify (SAF) | **no** (two bugs) | (a) SAF: an open latch with a D pulse at 3000–3010 and a rise at 3060 gives **Q rises at 3100, 40 ps after its cause** (arc 100). (b) X: `tb_seq_x.v` against `Wip/GLSdiff/SeqX.lean`: closed with CE = x → GLS **x**, Lean **0**; CLR = x with D = q = 0 → GLS **x**, Lean **0** (open and closed). **GLS wrong (pessimistic).** No current design instantiates LDCE |
| **FF (SLICE_FFX)** | FDRE as master-slave (`FDRE_M`, `FFQ_SYNC`), Kleene; timing ideal | `if (SR)` / `if (CE)` (default) and `SR === 1'b1` (fid) treat **x as 0** | **no** | R = x, D = 1, Q = 0 at the clock: GLS **1**, Lean **X**. CE = x, D = 0, Q = 1: GLS **1**, Lean **X**. **GLS wrong (optimistic: it hides X)**, in both models. Impact is small: flops have INIT values, and SR/CE are x only before reset |
| **arbiter race / state-loop metastability** | B: `ArbInvolution` (`stF_runt`: the arbiter q loop is bd_c2's OR loop), `CElemInvolution.orb`. A runt of width s latches or is lost; there is a critical s* ∈ (δ∞ − δ(0), δ∞) (`arb_eternal`) | `FID_RESOLVE`: runt p < TLOOP. The decision is random around **TLOOP − WIN/2**: delta = p − (TLOOP − WIN/2) + N(0, WIN/4) | **no**: the decision point differs | Below |

## The metastability decision point

The exact Lean OR-loop recurrence `orb` was transcribed in Float, with the
symmetric exp channel `expDelay` and δ∞ = TLOOP = 424 ps (gen.py's 300 ps
feedback wire plus the 124 ps arc). It was run with `#eval` in
`Wip/GLSdiff/Orb.lean` through slot.sh: "got slot 3", exit 0. There is a
Python twin, `orb_crit.py`.

**Involution result:**

| τ (ps) | 40 | 60 | 100 | 150 | 200 |
|---|---|---|---|---|---|
| s* (ps) | 212.1 | 212.9 | 218.0 | 230.2 | 246.5 |

- s* is about **TLOOP/2**, which is 0.50–0.58 of TLOOP.
- Above s* the runt latches deterministically. Both s = 300 and s = 360 give 'H' at every τ.
- At τ < 40 the loop is close to pure transport. Runts near 212 then oscillate
  for more than 20,000 transitions: a sweep shows an 'O' band centred near
  212, widening as τ falls. The bisection in `orb_crit.py` counts 'O' as 'L',
  so its s* for τ ≤ 20 is not meaningful.

**GLS (fid):** `tb_meta_centre.v` uses the same loop: bd_c2 INIT, a = 1,
runt b, and a 300 ps transport feedback ICBUF, with 200 resolver seeds per
width. The fraction latched (q = 1) is:

| s (ps) | ≤ 230 | 250 | 270 | 300 | 320 | 340 | 349 | 360 | 380 | 400 | 420 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| latched | 0 | 1/200 | 1/200 | 15/200 | 38/200 | 80/200 | 99/200 | 123/200 | 157/200 | 182/200 | 196/200 |

The 50% point is at **349 = TLOOP − WIN/2**, where the involution model gives
about 212–230.

**Consequence.** For runts in roughly 230 ≤ s ≤ 400 ps, Lean's gate model
latches the first request deterministically. The GLS mostly hands the grant to
the later request.
- This is the audit's "a request 360 ps later still wins 75/200" (f3 tb_f3_meta).
- The involution orbit says that request should lose 200/200.

**Which is wrong.**
- Lean has only a proved interval. `arb_eternal` gives s* ∈ (δ∞ − δ(0), δ∞),
  which is (9, 424) here, so the fid centre is **not excluded by any theorem**.
- The s* ≈ TLOOP/2 figure is a Float computation of the Lean recurrence for
  one channel family.
- It also follows from a symmetry argument for δ↑ = δ↓: a 50%-duty pattern is
  invariant.
- prjxray has no rise/fall split, so δ↑ = δ↓ is the default reading of the
  data.

The fid centre has no derivation: f3_model.md calls TAU/WIN assumptions, and
the centre is a fixed offset from TLOOP. So I grade the GLS **as the side
that is wrong in placement, pending data**. Its resolver decides on "how long
the runt lasted" relative to TLOOP. The loop actually decides on the duty
cycle of the circulating pulse, s against TLOOP − s.

The tail (TAU) and the window width are separate questions. Only the board
(`hw/arb_mtbf`) can fix them.

**Minor.** A "rejected" runt is still emitted to fanout at full swing (a 100 ps
pulse at 1124–1224 in `tb_meta_one.v`), while the loop ignores its own echo.
The `fid_core.vh` comment says "the node never left". The involution model
also emits a first, shrunk runt, so this behaviour is within Lean, but the
comment is wrong.

## For formal/out/FOR-RESEARCH.md (proposed bullets; the lead edits that file)

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
- **FID_RESOLVE's decision point.** The 50% point is TLOOP − WIN/2 (measured
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

## For the lead: FEASIBILITY fidelity table

The row "delay model in today's GLS: inertial on cell outputs" is stale. It
should say:
- default: SAF on every specify path;
- fid: per-pin transport for LUT and MUXF7/8, still SAF for
  CARRY4/latch/DSP/BUFG.

The LUT channel row can cite: fid equals per-pin transport,
60/60 + 60/60 (this note).

## Files
- `formal/tools-A/glsdiff/`:
  - `run_all.sh`, plus the build products `prims_def.v` and `prims_fid.v`;
  - `perpin_fit.py`, `tb_seq_x.v`, `tb_carry_saf.v`, `gen_meta_centre.py`;
  - the generated `tb_meta_centre.v` and `tb_meta_one.v`;
  - `orb_crit.py`, `src/` (research copies) and `out/`.
- `formal/lean/Wip/GLSdiff/Orb.lean` (Float, no imports) and `SeqX.lean`
  (imports Formal.Core.Lut). Both are `#eval` only and claim nothing.
