# C-10m: the slice OUTMUX hop and the tie-off false path in tcheck's front end, every row re-run

Shard C, probe 10m, 2026-10-29.

**STATUS: IN PROGRESS** (routes being rebuilt; tables below are filled as runs land).

## Plan / decisions so far

- The OUTMUX/xMUX driver hop (a6lut->amux, a5lut->amux, f7amux->amux, f8mux->bmux,
  carry4_o#->xmux) is already in extract.Prjx since C-10h (`_ic`, driver hop `dh`); the audit
  (Finding M) was made against C-10g (1e7947a), before C-10h. This probe verifies it arc by
  arc against the auditor's xrc.py (`xrcarcs.py`), keeps the previous 10m's fix of
  `Prjx.split` (two sinks leaving one LUT through different site pins share nothing), and
  re-runs every tcheck row.
- Tie-off false path: rules2.py rule A now drops `$PACKER_GND_DRV`/`$PACKER_VCC_DRV` starts
  (reason in the code comment; `TCHECK_KEEP_CONST=1` restores the old start set for
  before/after only).
- "Before" = the committed C-10h/10k/10l tables (front end at dfc8edc), copied to
  `formal/tools/tcheck/results/before10m/`.

## 1. Arc by arc against the auditor's model (gcd_hw seed 4; `xrcarcs.py`)

Routes: seeds 3 and 4 rebuilt with `tcheck/route.sh` are **byte-identical** (fasm, routed json,
sdf) to the C-10e/10h routes (`results/sha_*.txt`), which the audit also rebuilt identically.
nextpnr-xilinx sha256 `9c732bc6303458df`, `cells/verify/toolchain.sh` all ok.

Every SDF arc that both models resolve (86,037 of tcheck's 90,158 / xrc's 86,778):

| class | arcs | within 15 ps (all 4 corners) | mean diff fmin/fmax/smin/smax (tc - xrc) | max abs |
|---|---|---|---|---|
| LUT cell arc | 39642 | 39642 | -0.2/0.4/-0.5/0.8 | 3/4/9/11 |
| net, LUT O6 out on A..D (no hop) | 22322 | 22322 | 0 | 0 |
| net, LUT O5 via xMUX | 10600 | 6963 | 0/1.7/0/11.5 | 0/5/0/29 |
| net, LUT O6 via xMUX | 5981 | 4223 | 0/1.6/0/11.1 | 0/6/0/34 |
| MUXF7/F8 cell arc (OUT) | 3603 | 3603 | 0 | 0 |
| net, F8 via BMUX | 2063 | 2063 | 0 | 0 |
| net, F7A/F7B via AMUX/CMUX | 394 | 394 | 0 | 0 |
| net, FF / 5FF / CARRY4 outputs | 1432 | 1432 | 0 | 0 |

- **The OUTMUX hop is in tcheck's front end** (since C-10h) and equals xrc's on the MIN side
  of both corners on every arc.
- **All 5,395 arcs outside 15 ps** are LUT-via-xMUX nets, and differ only on the MAX side
  (<= 6 ps fast max, <= 34 ps slow max). Cause: prjxray-db has two ROUTING_BEL instances per
  output mux, `xMUX` and `xMUXL` (e.g. a6lut->amux slow 168..209 ps, a6lut->amuxl 194..241 ps);
  which one a configured site uses is not decoded, so tcheck takes the HULL (sound if either
  applies; C-10h decision) while xrc reads `xMUX` only. With `TCHECK_HOP_NOL=1` (plain xMUX
  only, cross-check switch, never a verdict) **all 86,037 arcs agree within 15 ps (max 11 ps,
  LUT cell arcs)**: results/xrcarcs_4_nol.tsv.
- With `XRC_NOMUX=1 TCHECK_NO_DRVHOP=1` the two models again agree on every LUT net
  (the C-10g model), which is what the audit reproduced.
- So the audit's Finding M (OUTMUX omitted) is true of C-10g and was already fixed in C-10h,
  but the C-10h J rows still carried a related bug (below, section 2).
