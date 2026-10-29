# Board-fidelity GLS: acceptance status (full stack)

Full stack = netlist decoded from the bitstream (`fasm2net.py --bit`) + prjxray RC-tree SDF (`xray_delay.py`)
+ `GLS_MODEL=fid` primitives, run by `cells/gls/fid/acceptance.py --stack full`. Grades from
`inventory.json` (research/PROGRAM.md: only HARD items are acceptance tests). Updated 2026-10-29.

| item | grade | FAST_MIN | SLOW_MAX | how it fails | evidence |
|---|---|---|---|---|---|
| lutpinmap_gcd_nofuse | hard | MATCH | MATCH | unpatched bits: 9/16, vectors 5-8,11-13 never complete, errs 0 (the board's signature; the dead set = BOARD-QUEUE #1's August list) | acceptance_full_nofuse_{min,max}.log |
| dsp_constpins | hard | MATCH | MATCH | simulated: products x (logic ALUMODE on a gated multiplier, dsp_model MUNK); NOT by decoder refusal | acceptance_full_dsp_{min,max}.log |
| dsp_constpins_inv | hard | MATCH | MATCH | as above | same |
| dsp_areg | hard (property) | MATCH (no delays read) | MATCH | unpatched bits decode AREG=2 with CEA1 tied 0: no product ever; patched AREG=1 = 1 stage | acceptance_full_dsp_areg.log |
| ring128 | hard | BLOCKED | BLOCKED | needs the August per-ring raw data (BOARD-QUEUE owner-side data request) | - |
| ring128_summary | soft | - | - | band 0.38 + region 0.16 + wire 0.126 (the full stack's model): MISMATCH, 4/7 graded stats vs the emulated pre-patch SDF (level ~+10%, 7/15-link widths too wide); vs today's nextpnr 6/7 (misses the 7-link length dependence). Across 8 rebuilt routes, not the measured one | ring128_summary.md |
| lutpinmap_gcd | hard | not run | not run | on today's fusion-on BQ#1 route the bug is harmless (the 58 corrupted LUTs change no vector, measured), so it cannot discriminate | JOURNAL 2026-10-27 |
| ring5_a / ring5_b | soft | inside band | inside band | every measured period in [FAST_MIN, SLOW_MAX]; band 0.38 within +-4% on long rings (0.38 was fitted to these rings) | acceptance_full_ring5_*.log |

Open model assumptions behind the MATCHes (each stated where it lives): a DSP control pin with neither tile
bit reads 1 (dsp_constpins depends on it entirely); AREG=2 for the unpatched areg encoding (from the patch text,
no readback); an unconfigured LUT outputs 0; metastability tau/window (150/75 ps, stress setting); flop
minimum pulse width 70 ps (no source); UG479 semantics read through yosys cells_sim.v.

Not accepted yet: ring128 is the only hard timing test and it is BLOCKED, so per PROGRAM.md the rule gates stay.
