# C-11c: bitstream import scaled to a bd_link stage + a bd_arbiter

Track 11, probe c. Shard C. 2026-10-27.  (Work in progress: notes kept current.)

## Status
- design `formal/tools/fasm2lean2/link_arb.v` (bd_link W=3 + bd_arbiter, shared rst),
  routed seeds 1..4 (toolchain.sh ok, nextpnr sha256 9c732bc6303458df, --freq 100).
- fasm2lean2.py (copy of 11b's fasm2lean.py, extended) extracts 7 LUT sites / 10 outputs
  from the read-back FASM of seed 1.
- Lean: in progress.
