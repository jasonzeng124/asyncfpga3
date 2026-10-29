# A-k3: the routed-timing checker (xevents8) on ipow and xorshift (shard A, probe K3)

PROGRAM.md north-star goal 3. Session 2026-10-29.

STATUS (07:20): started. Fresh sandbox: no FPGA toolchain yet, Mathlib compiling from source.

## Plan
1. Restore the toolchain from `origin/toolchain-cache/d7ce266cff0c8e1e` (read with `git cat-file`,
   no ref changes), apt deps (libtcl8.6, boost 1.83, zstd, iverilog); `cells/verify/toolchain.sh`
   must pass 9/9; record nextpnr sha256.
2. Build ipow_hw and xorshift_hw rigs (`k3/build_k3.sh`, left by the lost 2026-10-28 probe; review it
   first) on 4 placer seeds each, `--freq 100`, ONE nextpnr at a time. cells audits on every route.
3. Bands (`k3/bands_k3.sh`) at slow / fast / indep / gb.
4. skel -> cert7 -> xevents8 (and xevents5 for comparison); negative controls that must fail.
5. Tabulate; if E8Mux (notes/A-e8mux.md) is ready, rerun with its OUTMUX-hop bands.
6. Fix formal/out/HOWTO-new-kernel.md.

Artefacts: big files in ~/k3out (outside the repo); md5s, small logs, verdict text in
`formal/tools-A/xaudit/k3/out/`.
