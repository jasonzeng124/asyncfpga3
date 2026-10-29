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
