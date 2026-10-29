# C-10f2: RT_FB with the driver-side OUTMUX (xMUX) hop

Shard C, probe 10f2 (track 10), 2026-10-29. IN PROGRESS.

## Task

Audit row (P4, on 1149aa1): RtFbGcd "0 failures in every one-corner model" is OVERSTATED, because
`formal/tools/rtfb/rtfb_design.py` had no driver-side LUT -> xMUX hop (prjxray
`a6lut -> amux (0.071::0.088)(0.168::0.209)`). Add it, regenerate every RtFb Lean certificate
(gcd_hw seeds d,2,3,4; Muller 64 seeds 1..8), report what changes.

## Progress log

- 07:30 build dirs of C-10f / C-10e are gone (gitignored, lost with the old container): every route
  must be redone. Toolchain being restored by the lead.
- Generator: the lost 10m session had already drafted `drv_hop` / `outmux_table` in
  rtfb_design.py (WIP snapshot 1553efe). Kept, relabelled C-10f2, documented; added `--lean-all`,
  `RTFB_OUTMUX` sensitivity, hop statistics line in the report.
- Muller data now from rtfb_design.py (10d's rt_all.py has no hop and is not mine); rt_all.py is
  still run as a cross-check of the RTFB_NO_HOP model.
- gcd routes: own `route_gcd.sh` (copy of C-10e's tcheck/route.sh, into rtfb/build) because 10m
  owns tcheck/build this session.
