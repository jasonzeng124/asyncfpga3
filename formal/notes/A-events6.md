# A-events6: the netlist link `design_beh4` (W-E4n) and the checker `xevents5` (shard A)

## Verdict

**W-E4n works. W-E4g and W-E4x are not closed.** The executable checks the routed gcd control
of all 4 seeds, but every seed keeps residual items (below).

1. **W-E4n is proved: every behaviour of the parsed netlist is a `Beh4`.** `Events6.design_beh4`
   and `Events6.design_verdict` check with no sorry.
   - The semantics is per pin (`SatPin d plG x`): every LUT reads every input pin through its
     own monotone warp in the gate's band. H_ATOMIC_LUT is not used.
   - A run of the new executable `xevents5` is therefore a statement about every behaviour of
     the routed netlist, not about the model.
   - **What the checker verifies** (`Recog6`, decidable, evaluated over the real INITs):
     - every one of the 465 real nodes per seed: 405 C-element stages and 60 OR merges, from its
       LUT INIT;
     - every pin tree, steer, folded steer, feedback path and reset path, as paths of parsed gates;
     - that the `Net4` bands are those paths' bands.
   - **What it does not verify.** The 36 H_ARB virtual nodes per seed are a hypothesis (`HARB`),
     not checked.
   - Recognition passes on all 4 seeds at all 4 corners.
2. **The certificates are checked in Lean.** `cert6.py` (untrusted) emits the walk derivations,
   and Lean re-checks each of them (`DW.valid`, `UA.ok`, `backOK`/`lineOK`/`exclOK`, strict
   margins: 0 = FAIL).
   - **New rule `WDX`.** The derivations are `Events5.WD` extended so that a merge arm that is
     itself a steered pin (the cond_br acknowledge OR) is its own U-bound.
   - Without `WDX`, 85 Back/line pins and 12 merges per seed had no expressible certificate.
3. **No seed is CLEAN.** Every item `xevents5` does not certify is listed as a RESIDUAL
   obligation, and `design_verdict` carries those as explicit count-level hypotheses.
   - **At one corner and at gb there are 45 residual items, the same on every seed** (5 gb: 46).
     None of them is a timing failure. They fall into four classes:
     - **U3**: branch labels through reconverging merges, not expressible in `UArmD`;
     - **W-E4x**: the one 3-way mux merge and its 2-bit select groups;
     - **the cascaded arbiter**;
     - **6 guarded delay-line pins**: the `umux3/4/5` acknowledges.
   - **The guarded delay-line pins make the result conditional on a false hypothesis.** `Net4`'s
     guard kind has one copy, so these pins enter as `multi` pins. Their residual obligation
     (`PinOK`) is NOT expected to hold. So on gcd, as it stands, `design_verdict` is conditional on
     a hypothesis that is false in general. A guarded multi-copy pin kind (W-E4g) is needed before
     the gcd verdict is informative.
   - **The timing findings agree with ana5 (§3).** At mixed, ana5's failures all reappear: none is
     lost. xevents5 adds the pins whose ana5 margin is below the LUT's own band width, the per-pin
     effect that A-events2pin found.
4. **W-E4g is not proved.** GuardOK stays a hypothesis on the realisation. `Wip/Events6.lean`
   states the reduction I would do next: GuardOK ⟸ persistence of the guarded pin ⟸ ENTRY ∧ EXIT.
   - The first arrow is by construction once `gc` is defined from the wire's toggle count.
   - The second needs the lower-bound walk judgement.
5. **W-E4x (n-ary merges) is not done.** The 3-way merge is a residual item; it is stated in Wip.

## Files

| file | status |
|---|---|
| `formal/lean/Formal/Core/XAudit/Events6Gate.lean` | **proved**. Per-pin gate semantics (`gate_spec`), paths (`tau`), the tree checker `chkT` / **`chkT_sound`**, the copy window `pairW` / **`pairW_sound`** |
| `formal/lean/Formal/Core/XAudit/Events6Cert.lean` | **proved**. `DW` / `UA` data with `DW.sound` / `UA.sound`; `UArmX`, `WDX`, `wdx_sound`; `ExclW`, `LineW`, `BackW1`; **`Beh4F.verdictR`** (verdict with residual obligations) |
| `formal/lean/Formal/Core/XAudit/Events6Design.lean` | **proved**. Recognition data `RPin`/`RNode`, `PinR`/`NodeR`/**`Recog6`** (decidable), `ND` (per-node behaviour), `ofND`, `ccOf`, **`HARB`** |
| `formal/lean/Formal/Core/XAudit/Events6Beh.lean` | **proved**. `ndReal`, `init0`, **`design_beh4`**, `backOK`/`lineOK`/`exclOK` with soundness, **`design_verdict`** |
| `formal/lean/Formal/Core/XAudit/Events5Main.lean` | executable **`xevents5`**, audited. Checker; reads the certificate |
| `formal/lean/Wip/Events6.lean` | open shapes (`sorry`): W-E4g reduction, W-E4x, U3, cascade |
| `formal/tools-A/xaudit/events6/cert6.py` | UNTRUSTED certificate emitter (events4 Model/Ana + path enumeration + walk search restricted to steps Lean can express) |
| `…/events6/run6.sh`, `neg6.sh`, `table6.py`, `mk.sh` (private olean overlay through slot.sh), `xe5.sh` (`lean --run` of xevents5) | runs (4 seeds × 4 corners), negative controls, the comparison table |
| `…/events6/xe5_<seed>_<corner>.txt` (16), `xe5_d_slow_NEG*.txt` (3), `ana5lp_<seed>_<corner>.txt` (16), `table6.txt` | results |

### Check

From `formal/lean`:

    ../check.sh Formal/Core/XAudit/Events3.lean Formal/Core/XAudit/Events4.lean \
      Formal/Core/XAudit/Events5Line.lean Formal/Core/XAudit/Events5.lean \
      Formal/Core/XAudit/Events2Strict.lean Formal/Core/XAudit/Events2PinDesign.lean \
      Formal/Core/XAudit/Events6Gate.lean Formal/Core/XAudit/Events6Cert.lean \
      Formal/Core/XAudit/Events6Design.lean Formal/Core/XAudit/Events6Beh.lean \
      Formal/Core/XAudit/Events5Main.lean

Result:
- `[audit] 2065 declarations checked`;
- then `[audit] 2293 declarations checked` (the executable's own run);
- `[check] OK`.

There is no sorry, admit, axiom, native_decide or bv_decide; only `propext`, `Classical.choice`
and `Quot.sound` are used. Events3/4/5Line/5/2Strict/2PinDesign are listed only because lake has
not built their oleans.

### Lakefile stanza (for the lead; I did not edit the lakefile)

```toml
[[lean_exe]]
name = "xevents5"
root = "Formal.Core.XAudit.Events5Main"
```

**Usage:** `xevents5 SKEL.json BANDS.json CERT.json [--fuel F]`.
- `CERT.json` comes from `python3 tools-A/xaudit/events6/cert6.py SKEL.json BANDS.json CERT.json`.
- Until the stanza exists, `run6.sh` runs it with `lean --run` on a private olean overlay
  (`/tmp/events6/olean`, built through `slot.sh`).
- One run takes about 27 s in the interpreter.

## 1. What is proved

### The netlist semantics (`Events6Gate`)

**`plG g i = (g.lo, g.hi)`.** Every input of a gate is read through its own warp in the gate's
band.
- prjxray's LUT IOPATH rows are flat over A1..A6.
- The site-pin delay is already in the routed arc (A-events2pin §2).
- So this is exactly Events2PinDesign's per-pin semantics, without H_ATOMIC_LUT.

Under `SatPin d plG x`:
- **`gate_spec`.** A gate whose INIT passes `InitSpec g spec` (decided over the `2^k` addresses,
  constant pins fixed) outputs `spec` of its inputs, each read at its own warp.
- **`chkT_sound`.** A list of paths accepted by `chkT` from wire `w` down to source wire `sw`
  makes `x w t = par ^^ (all | any) (π ↦ x sw (tau π t))`.
  - `chkT` accepts trees of buffers, inverters (parity above the first multi-input gate), AND
    and OR gates.
  - `tau π` composes the per-pin warps along `π`, with band `[plo π, phi π]` (`tau_warp`).
  - This is how a FASTFALL / FASTRISE line, a route chain and a merge arm become the copies of an
    `Events5.Net4` pin. It is exact (an AND of ANDs is an AND over all paths) and needs no atomic
    sampling.
- **`pairW_sound`.** Two copies are read within `pairW` of each other:
  - the common head part (one warp) cancels;
  - the middle parts give `hop_skew`'s window;
  - the common tail next to the source adds its width (`prefix_skew`);
  - otherwise the whole-path window applies.

  This is contig5's window, with one difference: the meeting gate's two pins are different
  elements, so the gate's LUT band width enters. That is `contig5 --lutpin`.

### The link (`Events6Design`, `Events6Beh`)

**`Recog6 d net b rn rank rw fuel`** (decidable). For every real node:
- **stage** — the LUT INIT equals `rst ? v : cel(lit_p, q)` with `lit_p = (pin_p ^^ neg_p) &&
  [folded select pattern]`;
- **merge** — the LUT INIT equals `fany(pins)`;
- **pins** — every pin is `chkT`-checked, or is a steer gate (`InitSpec` of `ctl && pattern`)
  with checked chains above and below it;
- **feedback and reset** — the feedback is one routed arc back to the LUT's own output, and the
  reset path is checked against the reset wire;
- **bands** — `loF = hiF = 1`; each copy's band is its full path band minus 1 (the LUT pin's own
  warp moved into the copy); `loQ`/`hiQ` likewise; `dw` = `pairW` of consecutive copies;
- **merge ranks** decrease (the OR gates are acyclic).

**`design_beh4`.** Hypotheses:
- `SatPin d plG x`;
- constant wires 0/1;
- reset high on `[0, T)`;
- `Recog6`;
- `Net4.OK`;
- `HARB`.

Conclusion: for every `sel` and every monotone `gc`, there is a `Beh4` whose node `j` is `x` on
`j`'s LUT output wire (real `j`) or the H_ARB signal (virtual `j`).
- The proof builds each real node's `ND` from the chosen per-pin warps.
- **The sampling trick.** The node samples at `F t = t − 1`. The LUT's pin warp `f_p(t)` becomes
  `h_p(s) = f_p(s + 1)`, with band `[lo − 1, hi − 1]`, moved into every copy, the feedback and
  the reset. This is exact because `f_p(0) = f_p(1) = 0`.
- `init0` gives `mg0` (merges low at time 0) by induction on the merge rank.

**`design_verdict`.** This is what `xevents5` checks, plus the residual hypotheses.
- Hypotheses: `Recog6`, `Net4.OK`, and per item `backOK` / `exclOK` / `lineOK` (data
  certificates with strict margins, via `DW.sound` / `UA.sound`).
- Conclusion: for every per-pin behaviour, under H_ARB, there is a realising `Beh4` such that,
  if it satisfies SelOK, GuardOK and the residual obligations, every real LUT wire equals
  `ph (v j) (M t j)` at every time.

### Certificates (`Events6Cert`)

- **`DW` / `DW.valid` / `DW.sound`.** Data derivations for R1, fpin, R3, lift and SUB. `UA` /
  `UA.sound` are U-arm witnesses.
- **`UArmX` / `WDX` / `wdx_sound`.**
  - `Events5.WD`'s R3 and SUB require `UArmD`: a walk to a filtered STAGE pin.
  - gcd's cond_br acknowledge ORs read the two steer halves directly: the merge arm itself is the
    filtered pin.
  - `UArmX` adds that case: the arm is its own U-bound, by `P_filt_le`.
- **`Beh4F.verdictR`.** `Events5.Beh4.safe`, with each stage pin, merge and line pin either
  certified or carrying its count-level obligation (`PinOK`, `ExclOK`, `ContigF` for that item)
  as a hypothesis.

## 2. What is open (stated in `Wip/Events6.lean`)

- **W-E4g (GuardOK).** In `design_beh4`, `gc` is a free monotone argument, so GuardOK is a
  hypothesis about the realisation. The reduction (about 0.5 day) has three steps:
  1. Choose `gc := toggles(c_j up to Q j s) + [pin ≠ feedback]`.
  2. GuardOK's read-value conjunct is then true by construction.
  3. Its bound conjunct follows inside `safe`'s induction.

  What remains is `gcmono` = **persistence**: a guarded pin that shows "advanced" while its guard
  has advanced keeps showing it until the stage's feedback moves.
  - EXIT gives persistence when the advance is not stale.
  - ENTRY excludes staleness. ENTRY needs a lower-bound walk judgement, which the min-plus
    recursion lacks (about 1 day).

  A decidable per-pin inequality was NOT proved sufficient. I did not want to claim the EXIT
  inequality without the ENTRY half.
- **W-E4x.** 2-bit select patterns are their own Boolean groups (`br = true`). The 3-way merge
  needs the three `sel g` to be indicators of one value sequence, plus an n-ary `merge_excl`.
- **U3.** A merge inherits the U-label of its R3 source.
- **The cascade.** A 3-way virtual core.

## 3. Results: gcd_hw seeds d, 3, 4, 5 at slow / fast / mixed / gb

**Setup.**
- Builds and bands are A-events5's: nextpnr sha256 9c732bc6303458df, 9/9 fingerprints; SDF and
  routed-JSON md5s in `events5/builds.txt`.
- Corners: `slow` [SLOW_MIN, SLOW_MAX], `fast` [FAST_MIN, FAST_MAX], `indep` (mixed)
  [FAST_MIN, SLOW_MAX], `gb` [0.668·SLOW_MAX, SLOW_MAX].
- Bands are read in 1 ps steps (Parse's `unit` set to 1). Arcs with lo = 0 ps are raised to 1 ps.

Files: `events6/xe5_<seed>_<corner>.txt` (xevents5), `events6/table6.txt` (stage-by-stage
comparison with ana5), `events6/ana5lp_*` (ana5 `--lutpin`).

**Every row checks the recognition.** Design.WF, `Recog6` (0 node failures out of 465 real nodes)
and `Net4.OK` hold on every row.
- "Back" counts stage pins, real and virtual, that are not guarded: 836.
- Margins are strict: a margin of 0 is a FAIL.
- ana5's columns repeat `events5/table.txt` (atomic).

| seed corner | Back cert / 836, min | ana5 Back min | line cert / 164, min | ana5 contig5 min | merges cert / 69 | residual items (timing-margin items) |
|---|---|---|---|---|---|---|
| d slow | 800, **937** | 961 | 163, 2645 | 2669 | 61 | 45 (0) |
| d fast | 800, **423** | 434 | 163, 1249 | 1260 | 61 | 45 (0) |
| d mixed | 794, **−269** | −190 | 160, −2812 | −365 | 61 | 54 (6 Back, 3 line) |
| d gb | 800, **526** | 568 | 163, 1027 | 1572 | 61 | 45 (0) |
| 3 slow | 800, **748** | 772 | 163, 1818 | 2060 | 61 | 45 (0) |
| 3 fast | 800, **332** | 343 | 163, 986 | 997 | 61 | 45 (0) |
| 3 mixed | 794, **−344** | −265 | 156, −2750 | −726 | 61 | 58 (6 Back, 7 line) |
| 3 gb | 800, **416** | 458 | 163, 151 | 1486 | 61 | 45 (0) |
| 4 slow | 800, **755** | 779 | 163, 2929 | 2953 | 61 | 45 (0) |
| 4 fast | 800, **334** | 345 | 163, 1356 | 1367 | 61 | 45 (0) |
| 4 mixed | 792, **−246** | −167 | 161, −2204 | 259 | 61 | 55 (8 Back, 2 line) |
| 4 gb | 800, **417** | 459 | 163, 1034 | 2025 | 61 | 45 (0) |
| 5 slow | 800, **186** | 210 | 163, 2344 | 2478 | 61 | 45 (0) |
| 5 fast | 800, **107** | 118 | 163, 1140 | 1107 | 61 | 45 (0) |
| 5 mixed | 794, **−474** | −395 | 161, −2991 | 67 | 61 | 53 (6 Back, 2 line) |
| 5 gb | 799, **−61** | −19 | 163, 348 | 1691 | 61 | 46 (1 Back) |

### The 45 structural residual items (identical on every seed and corner)

None of them is a timing failure. They are what the Lean judgements cannot express yet.

| class | items | why |
|---|---|---|
| U3 / W-E4x | 27 Back, 7 merges, 1 line | ana certifies them with an R3/SUB step whose U-arm needs a branch label through a merge (U3), or with a 2-bit select group (W-E4x). `cert6.py` restricts its walk search to steps Lean can express (`r3ok`/`subok`) and finds no other walk |
| W-E4x | 1 merge | the 3-way merge `umux21` |
| cascade | 3 Back (1 real, 2 virtual) | `control_merge12`: no walk, as ana (NONE) |
| **guarded delay lines** | **6 Back** | see below |

**The guarded delay lines are not just inexpressible: their obligation is wrong.**
- What they are: the acknowledges of `umux3/4/5`, whose guarded pin `z_ack` arrives through a
  delay line. ana's rule for them is Guard.
- Why they cannot be guard pins: `Net4.OK` gives a guard pin exactly one copy, so they enter
  `Net4` as `multi` pins.
- Their residual obligation is therefore `PinOK`. That obligation is **not expected to hold**: the
  guarded pin fires on every transaction, the stage only on its branch.
- **Consequence: on gcd, as it stands, `design_verdict`'s conclusion is conditional on a
  hypothesis that is false in general.**
- The fix is a guarded multi-copy pin kind in `Net4` (part of W-E4g).

This is the most important limitation of the run.

### Stage by stage against ana5 (`table6.txt`)

**ana5's failures are all found.** On every row, every stage ana5 flags outside the guard rules is
also residual in xevents5 ("ana5 only 0").

**xevents5 flags more stages:**
- the 29 or 30 structural stages above;
- at mixed and gb, the pins whose ana5 margin is positive but below the LUT's own band width.

**The per-pin LUT width explains every margin difference.**
- What is not counted atomically: H_ATOMIC_LUT hides the LUT's own pin-to-O band width. Here each
  pin has its own warp in the LUT band.
- Where it enters: through `hiQ` (the feedback pin's band moves into `Q`) and at the meeting gate
  of a line (two pins, two warps).
- The width per corner: 24 ps at slow (124 − 100), 11 at fast, 79 at mixed, about 42 at gb.
- **Back minima.** Lean's minimum is ana5's minus exactly that width on every row:
  - d: 961 → 937, 434 → 423, −190 → −269, 568 → 526;
  - 3: 772 → 748, 343 → 332, −265 → −344, 458 → 416;
  - 4: 779 → 755, 345 → 334, −167 → −246, 459 → 417;
  - 5: 210 → 186, 118 → 107, −395 → −474, −19 → −61.
- **Mixed Back pins.** ana5's 2 / 4 / 7 / 4 races reappear with the same names, each 79 ps lower:
  - d: `ulink_n_falseResult_41` −190 → −269, `ucontrol_merge4.uarb1.ua2` −9 → −88;
  - 3: `ulink_n_falseResult_77` −265 → −344, `ulink_n143` −163 → −242, `umux4.uya` −138 → −217,
    `ulink_n_trueResult_28` −122 → −201;
  - 4: all 7, from −167 → −246 to −14 → −93;
  - 5: `uenv1` −395 → −474 and the other three.

  The extra pins (d: 4, 3: 2, 4: 1, 5: 2) are exactly those with an ana5 margin in (0, 79], e.g.
  d's −72 / −59 / −53 / −26. This matches A-events2pin ("the per-pin check turns 1 to 4 more pins
  per gcd seed to ≤ 0").
- **gb.** The rig environment `uenv1 ← uenv0` on seed 5 goes from −19 to −61. All other gb Back
  pins pass.
- **Lines, the residual of A-events5 §3.** It reappears: d `ulink_n168` (ushli0's line) −365 →
  −444; 3 `ulink_n139` −726 → −805. Seed 3's three −85 to −93 lines come out at −2 to −172.
  - The meeting gate's per-pin width adds 79 ps.
  - Beh4's `hskew` is stated for CONSECUTIVE copies, where contig5 takes the best pair per gate.
    `cert6.py` orders the copies greedily so that consecutive copies meet with a small window.
    The one-corner line minima are then within 11 to 24 ps of contig5's, except seed 3 slow
    (1818 vs 2060) and the gb rows.
- **Lines that are H_ARB's.** At gb and mixed, the line minimum comes from the two arbiter grant
  request lines (`control_merge4`, `control_merge12`): 3 gb 151, d gb 1027, and at mixed down to
  −2991.
  - These are VIRTUAL pins. Their `dw` is the whole band spread of the copies, which is sound for
    any warps in the bands but does not cancel the shared suffix.
  - So these are artefacts of the conservative H_ARB band, not route findings. A virtual pin with
    real paths would fix it (0.2 day).

### Guard pins

GuardOK is a hypothesis of `design_verdict`, so ana5's guard ENTRY / EXIT failures do not appear
as residual items. "ana5 guard-only bad" counts them per row: 2 to 16. They are W-E4g.

### Negative controls (`neg6.sh`, seed d slow; `xe5_d_slow_NEG*.txt`)

| control | injected | result |
|---|---|---|
| NEG-fb | +1500 ps on `ucontrol_merge4.uarb1.ua2`'s own-feedback arc | that pin becomes a residual Back item at **−382** (ana: −358; −24 = the slow LUT width); residual 45 → 46 |
| NEG-recog | certificate claims a stage's feedback input is its reset input | `Recog6` rejects exactly that node: NOT RECOGNISED |
| NEG-path | one copy path of one delay line loses its last element | `Recog6` (`chkT`) rejects exactly that node: NOT RECOGNISED |


## 4. Fidelity (gate-fidelity rule)

| item | model | status | test |
|---|---|---|---|
| LUT | INIT over physical pins; each pin through its own monotone warp in the gate's IOPATH band (`plG`); constant pins as wires 0/1 | per-pin, NO H_ATOMIC_LUT. The LUT function is exact (UG474); the band is prjxray's flat IOPATH | GLS with unisim LUT6 and per-pin IOPATH |
| routes | 1-input buffer gates, per-arc prjxray band, transport (monotone warp) | Events2's FIFO hypothesis | SDF transport GLS; TDC |
| delay lines | AND/OR trees expanded into copies (`chkT_sound`, exact); window `pairW` (suffix cancels, prefix width, meeting gate per-pin width) | proved from the netlist (was the `hskew` field) | the concrete trace of A-events5 §3 |
| merges | real OR LUTs; exclusivity from `exclOK` (binary, WDX walk) | the 3-way merge is residual (W-E4x) | GLS with a long arm |
| steers | separate steer gates or folded into the stage LUT; the select seen is a free signal; **SelOK** hypothesis | E6 | GLS: select against request |
| guarded pins | `gc` free, monotone; **GuardOK** hypothesis | W-E4g open (reduced to persistence) | GLS of `bd_mux` with z_ack fan-out skewed |
| arbiter | **H_ARB** (`HARB`): virtual nodes' behaviour in their bands; grant/R0 wires carry it. Virtual bands are ana's taps; a virtual delay line's `dw` is its whole band spread (sound for any warps in those bands) | hypothesis, unchecked | contention GLS |
| skeleton | `skel.py` cuts the select nets into free inputs | untrusted cut; every full-netlist behaviour restricted to the skeleton is a skeleton behaviour when the kept gates are copied verbatim (they are; md5 not re-checked here) | — |

## 5. Effort and what it buys

**Effort.** About 6 h:
- reading: 0.5 h;
- Lean: 3 h. Events6Gate 0.6 h, Cert 0.5 h, Design/Beh 1.3 h, Main 0.4 h, WDX 0.2 h;
- cert6.py: 1 h;
- runs and notes: 1.5 h.

**To finish.**
- W-E4g (persistence + ENTRY lower-bound judgement): about 1.5 days.
- U3: 0.5 day.
- W-E4x: 0.5 day.
- The cascade core: 0.5 day.

After that, a CLEAN verdict on gcd at one corner is in reach. The residual items at one corner
are only these classes.

**What it buys.**
- **The netlist step is closed.** The counter-domain verdict is a theorem about every per-pin
  behaviour of the routed netlist, with the recognition of all 465 real nodes checked from the
  INITs and every certificate re-checked.
- **Two trusted links are removed.**
  - The Python model's reading of the netlist is now checked.
  - `hskew` is now derived from the netlist (`chkT_sound`, `pairW_sound`); before, it was a
    field of the behaviour.
- **The residuals are explicit hypotheses.** What is not certified is listed per item and enters
  the theorem as a hypothesis. It is not silently assumed.
