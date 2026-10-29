# A-k3: the routed-timing checker (xevents8) on ipow and xorshift (shard A, probe K3)

PROGRAM.md north-star goal 3. Session 2026-10-29.

STATUS (08:20): toolchain restored and verified; 8+2 routes built and audited; bands built; Lean
overlay compiling; checker runs next.

## Progress log
- **Toolchain.** Restored from `origin/toolchain-cache/d7ce266cff0c8e1e` (= `cloud/toolchain-cache.sh
  key`) by `git cat-file blob` of its one part (no ref written, unlike `toolchain-cache.sh fetch`,
  which does `git fetch` + `update-ref`). apt: zstd iverilog libtcl8.6 libboost-{python,filesystem,
  program-options}1.83.0. `cells/verify/toolchain.sh`: 9/9 ok, nextpnr sha256 **9c732bc6303458df**
  (the gcd_hw/collatz binary), yosys 0.62. Re-run by build_k3.sh before every seed (out/*/toolchain_*.txt).
- **Builds** (`k3/build_k3.sh`, ONE nextpnr at a time via `flock /tmp/nextpnr.lock`, `--freq 100`
  through build_hw.sh's NEXTPNR_FREQ, BD_DSP default 1, sizes as in the script header):
  - ipow: seeds d 3 4 5 all routed; 1808 LUT sites, 6 DSP48E1, 74 RLOC clusters 0 dropped, fasm_audit PASS.
    17 of the kernel's 67 DELAY_ parameters are not in the T9 sizes file and keep emit.py's defaults
    (non-compute links, DELAY 0 / UACK 6 / SDELAY 3); all 50 sized names match a parameter.
  - xorshift: seeds d 3 5 routed; **4 and 6 did not place** (`post-placement validity check failed for
    Bel 'SLICE_X0Y50/A5FF'` / `SLICE_X0Y34/A5FF`, the known nextpnr legality failure); 7, 8, 9 routed.
    1357 LUT sites, 0 DSP, 59 clusters 0 dropped, fasm_audit PASS.
  - bitstream step fails (no textx); no bitstream is needed or used.
- **cells audits** (`k3/audit_k3.sh`: tighten.py --osc dhk --osc invhk, skew.py, arb_fork.py):
  - ipow d 3 4 5: rules A H I F B C 0, rule D 8 (the one-sided screen; ucond_br2..9), rule E 24/24
    measured 0 violated, arb_fork 4 ok. PASS.
  - xorshift d 5 8 9: the same. PASS.
  - **xorshift 3: rule A FAIL** (`umux0` margin −52 ps) and **rule I FAIL**
    (`ulink_n_falseResult_1.many.stage[1]` −177 ps); **xorshift 7: rule A FAIL** (`umux0` −339 ps).
    2 of 6 placed xorshift routes violate rule A, as CLAUDE.md says of rebuilds of the shipped
    xorshift (2 in 8). These two routes are NOT results; the xorshift set is d 5 8 9. 3 and 7 are
    kept only as a comparison (does the control-level checker see anything there? it is not meant
    to: rule A/I are data-vs-request bundling, which the event checkers take as SelOK / outside).
- **Netlist** (`k3/bands_k3.sh` -> `k3/routed2x_k3.py`): ipow needs `--cut-type DSP48E1_DSP48E1`
  (routed2x.py rejects DSP48E1 as not combinational); its 6 DSPs' P outputs become 64+ free
  inputs. `k3/skel_dsp_check.py`: the control skeleton reads none of them (its 7 inputs are
  rig_rst and 6 select-data nets). Without --cut-type routed2x_k3.py is byte-identical to
  routed2x.py (cmp of net.json and slow bands on xorshift d).
- xray_delay = research 7dc5dde (md5 3e69bf6a), which already charges the slice OUTMUX hop
  (`sitepip_charged_xOUTMUX 1092` on ipow d). E8Mux (notes/A-e8mux.md) reports its fixed
  calculator equals 7dc5dde on all 40083 comb->comb IC rows of gcd_hw d, so **these k3 bands
  already carry the O5/F7/F8 OUTMUX hop** the audit found missing from gcd_hw's 99b10a6d bands.
- prjxray rows with lo > hi (E8Mux's finding): routed2x.py now rejects them unless `--inverted hull`;
  bands_k3.sh passes hull and regenerates routed2x_k3.py from the live routed2x.py
  (`k3/mk_routed2x_k3.py`). Hulled rows: fast corner only, ipow 4 (4 rows), ipow 5 (2), xorshift d,
  3 (2 each), all data-latch arcs (ulink_*.lat.pair[*]) outside the control skeleton.
- Lean: `k3/mk_k3.sh` compiled the 34 Mathlib-free modules of xaudit/xevents5/xevents8 into
  ~/k3olean via lean.sh/slot.sh; all "ok", no log mentions error or sorry.
- First xevents8 row: ipow d slow **VERDICT CLEAN** (`Events8.design_verdict8`; HDsub 24 judgements;
  176/176 Back, 23/23 line, 14/14 merges, 12/12 guarded pins).

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
