# A-k3: the routed-timing checker (xevents8) on ipow and xorshift (shard A, probe K3)

PROGRAM.md north-star goal 3. Session 2026-10-29.

STATUS (09:35): **done.** Both kernels built (4 audit-passing seeds each), banded, and run through
xevents8 and xevents5 at slow / fast / gb / indep; negative controls rejected; HOWTO rewritten.
No Lean file written; nothing to check.sh. All numbers below are routed-model results, not silicon.

## Verdict

- **ipow (4 seeds d 3 4 5): `Events8.design_verdict8` CLEAN on all 12 slow / fast / gb rows.**
  indep: RESIDUAL 7 / 9 / 12 / 1, every item a timing margin ≤ 0.
- **xorshift (4 audit-passing seeds d 5 8 9): CLEAN on 9 of 12 slow / fast / gb rows.** Seed d
  is RESIDUAL 2 at slow, fast and gb, and both items are the **rig's** environment C-element pair
  (`urig.uenv0`/`urig.uenv1` Back pin1: −13/−8 slow, −4/0 fast, −202/−197 gb), not the kernel;
  every kernel item on seed d is certified at those corners. indep: RESIDUAL 8 / 9 / 9 / 10, all
  margins ≤ 0.
- The two xorshift routes that FAIL the cells/ rule A (seeds 3, 7) are CLEAN at slow/fast/gb under
  xevents8, as expected: rule A/I are data-vs-request bundling, which the control-level checker
  does not see (it is the SelOK side / outside the skeleton). The event checker is no substitute
  for the cells/ gates.
- **What a CLEAN row is**: an instance of `Events8.design_verdict8` about every behaviour of the
  parsed routed control skeleton: every real control node's output is the phase of its event
  counter. Hypotheses: per-pin SatPin (elements in the prjxray bands of that corner, through the
  trusted parser), constant wires, the reset pulse, H_ARB (8 virtual arbiter nodes, unchecked),
  SelOK (select bundling; skew.py measured 24/24 met, not proved), SelPart (vacuous: `[]` on every
  row), HDsub (24 judgements, open). GuardOK is NOT assumed: 12/12 guarded pins carry Lean-checked
  guard certificates on every CLEAN row. NOT covered: datapath values and the answer (for ipow the
  DSP outputs are free inputs of the netlist; the skeleton reads none of them), metastability,
  anything outside the bands, other routes, skel.py, the trusted reader.
- Compared with gcd_hw (A-events8: gb seed d fails ENTRY on 3 arbiter guard pins), ipow and
  xorshift pass every gb guard; the same arbiter guard ENTRY items show up only at indep.
- The rig's `uenv0`/`uenv1` pair is the lowest Back pin on most rows (ipow d slow 307 ps) and fails
  on xorshift d at 3 corners; it also was the only gb residual on gcd_hw seed 5 and collatz seed 5.
  **Lead: the shared rig environment (gcd_rig's two directly-coupled C-elements) is the weakest
  control element across four kernels; it is not part of any kernel.**

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
  3 (2 each): data-latch arcs (ulink_*.lat.pair[*]) and 3 shell (abc/FF) arcs; no skeleton band
  has lo > hi (checked on every skel_fast.bands.json).
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

## ipow: xevents8 / xevents5 (`k3/run_events_k3.sh ipow`; `k3/out/ipow/`, table `k3/out/ipow/table.txt`)

Every row: `Design.WF true; Recog6 node failures 0; Net4.OK7 true`, `select partitions (SelPart): []`
(vacuous), derivation log accepted by runLog, cert8 errors 0, `--fuel 256`. Skeleton 484 LUTs
(86 storage with reset), 104 nodes (8 virtual = H_ARB, the two control_merge arbiters), 14 merges
(none n-ary), 176 Back pins, 23 line pins, **12 guarded pins**, HDsub = 24 judgements.

| seed | slow | fast | gb | indep (mixed) |
|---|---|---|---|---|
| d | **CLEAN** | **CLEAN** | **CLEAN** | RESIDUAL 7 (xe5: 8) |
| 3 | **CLEAN** | **CLEAN** | **CLEAN** | RESIDUAL 9 (xe5: 5) |
| 4 | **CLEAN** | **CLEAN** | **CLEAN** | RESIDUAL 12 (xe5: 10) |
| 5 | **CLEAN** | **CLEAN** | **CLEAN** | RESIDUAL 1 (xe5: 4) |

- xevents5 gives CLEAN on the same 12 rows (its CLEAN assumes GuardOK; xevents8's does not).
- Min margins (ps, strict) at slow / fast / gb: Back 307..1510 / 177..790 / 126..1086; line ≥ 783;
  guard ENTRY ≥ 280, EXIT1 ≥ 1516. The lowest Back pin on d slow is the rig's `urig.uenv0` (307).
- **indep residuals are all timing margins ≤ 0, none structural** (every item has a certificate
  shape; only the number fails): the rig's uenv0/uenv1 (d), the `ulink_n_index_15` /
  `ucontrol_merge1_f` line pair (d, 3), `ucond_br*_j` lines (3, 4), link stages (3, 4) and the
  arbiter guard ENTRY bounds `ucontrol_merge{0,1}.uarb1.ua{1,2}` (−20..−481 ps; seed 4 has one at
  ENTRY **0**, a FAIL because margins are strict). These are the same arbiter re-arm items as
  gcd_hw's d-gb ENTRY failures (A-events8), here only at the mixed corner.
- xevents8 vs xevents5 at indep: xevents8 certifies 4 line pins that xevents5 leaves (d: 21/23 vs
  17/23 lines; `ucond_br2..5_j` −473 at xe5), because cert7/cert8 try every R3 candidate; it adds
  the guard items that xevents5 does not check (GuardOK is its hypothesis). Net: d 7 vs 8, 5 1 vs 4,
  3 9 vs 5 and 4 12 vs 10 (the extra ones are the guard items).

**Negative controls** (seed d slow; `out/ipow/neg.txt`, `xe8_d_slow_NEG*.txt`):
- NEG-fb5000 (+5000 ps on `ucontrol_merge0.uarb1.ua2.u/I4`, its own feedback found by negctl_k2.py):
  `RESIDUAL Back …ucontrol_merge0.uarb1.ua2.u pin1: margin -3139`, RESIDUAL 1. Rejected.
- NEG-recog (cert: `ucmpi2.ujoin` qi := ri): `RECOG-FAIL`, `VERDICT NOT RECOGNISED`. Rejected.
- NEGnoguard (`cert8.py --no-guard`): 0/12 guarded certified, RESIDUAL 12. Rejected.
- NEGentry / NEGexit on `umux3.uya.u` pin1 with gcd's neg8.sh defects (+5000 both bounds of the
  guarded arc / +18000 on the guard arc's hi): **still CLEAN — those defects are smaller than this
  pin's margins** (ENTRY 8312, EXIT2 37219 ps, read off the rerun below; the ENTRY margin includes
  the S→D walk). With +60000 ps: NEGentry `RESIDUAL Guard …umux3.uya.u pin1: … ENTRY -51688`,
  NEGexit `… EXIT2 -22781`, each RESIDUAL 1. Rejected. run_events_k3.sh now uses GPS=60000.

## xorshift: xevents8 / xevents5 (`k3/out/xorshift/`, table `k3/out/xorshift/table.txt`)

Every row: Design.WF true, Recog6 failures 0, Net4.OK7 true, SelPart `[]`, log accepted, cert8
errors 0. Skeleton 297 LUTs (75 storage with reset), 93 nodes (8 virtual), 14 merges, 152 Back pins,
25 line pins, 12 guarded pins, HDsub 24 judgements.

| seed | slow | fast | gb | indep | cells audits |
|---|---|---|---|---|---|
| d | RESIDUAL 2 (rig uenv0/1) | RESIDUAL 2 (rig) | RESIDUAL 2 (rig) | RESIDUAL 8 | pass |
| 5 | **CLEAN** | **CLEAN** | **CLEAN** | RESIDUAL 9 | pass |
| 8 | **CLEAN** | **CLEAN** | **CLEAN** | RESIDUAL 9 | pass |
| 9 | **CLEAN** | **CLEAN** | **CLEAN** | RESIDUAL 10 | pass |
| 3 | CLEAN | CLEAN | CLEAN | RESIDUAL 11 | **rule A, rule I FAIL: not a result** |
| 7 | CLEAN | CLEAN | CLEAN | RESIDUAL 4 | **rule A FAIL: not a result** |

- xevents5 gives the same verdict class on every slow/fast/gb row (CLEAN, or the same 2 rig
  items on seed d); at indep it has 6 / 6 / 9 / 6 items vs xevents8's 8 / 9 / 9 / 10 (the
  difference is guard items, which xevents5 assumes as GuardOK).
- ana5 calls d slow and d fast MET (it is not strict at 0 and uses another per-pin rule); the Lean
  checker is the one that counts.
- indep items: the rig pair, link stages (`ulink_n_trueResult_12`, `_2`, `n6`, `n12__1`), the
  `ulink_n_index_15` / `ucontrol_merge1_f` line pair, and arbiter guard ENTRY bounds
  (`ucontrol_merge{0,1}.uarb1.ua{1,2}`, −37..−278 ps). All margins ≤ 0; none structural.

**Negative controls**, on seed d (not clean at baseline; `neg_d.txt`) and on seed 5 (clean;
`neg_5.txt`, `xe8_5_slow_NEG*.txt`). On seed 5:
- NEG-fb5000 (`ucontrol_merge0.uarb1.ua2.u` own feedback): `RESIDUAL Back … pin0: margin -3122`, RESIDUAL 1;
- NEG-recog (`umux3.uya.u` qi := ri): `RECOG-FAIL`, NOT RECOGNISED;
- NEGentry (+60000 on `umux3.uya.u/I0`): `RESIDUAL Guard umux3.uya.u pin0 … ENTRY -53610`, RESIDUAL 1;
- NEGexit (+60000 on the hi of `umux3.uya.u/I3`): `… EXIT2 -27856`, RESIDUAL 1;
- NEGnoguard: RESIDUAL 12 (every guarded pin "no certificate").
All rejected. On seed d each control adds exactly its item to the 2 rig items.

## Not done
- xaudit (one-transaction X/hazard) was not run on ipow or xorshift. For ipow with the DSP cut the
  answer could not be certified anyway (the products are free inputs); xorshift has no DSP.
- No routed GLS. No board.
- The rig uenv pair finding is a model-level timing margin, not a demonstrated race.

## Files

| file | what |
|---|---|
| `k3/gen_rig.py`, `k3/{ipow,xorshift}_{rig,hw}.v` | rig + shell generator (C-derived ROM) and its outputs (from the lost 2026-10-28 probe, reviewed; expected values re-checked by hand: 3^2 = 9, xorshift(1,1) = 0x42021) |
| `k3/build_k3.sh` | export + build_hw case + sizes rename + per-seed build (toolchain.sh each seed), `NEXTPNR_FREQ=100` |
| `k3/audit_k3.sh` | cells/ audits per seed (tighten --osc dhk --osc invhk, skew, arb_fork) |
| `k3/bands_k3.sh` | xray_delay (7dc5dde) + routed2x_k3 at slow/fast/indep/gb, `--inverted hull`, DSP cut for ipow |
| `k3/mk_routed2x_k3.py` -> `k3/routed2x_k3.py` | routed2x.py + `--cut-type` (generated; byte-identical without the option) |
| `k3/skel_dsp_check.py` | does the skeleton read a cut cell's output? (ipow: no) |
| `k3/mk_k3.sh` | oleans for xaudit/xevents5/xevents8 without lake build |
| `k3/run_events_k3.sh`, `k3/table_k3.sh` | skel -> cert8/cert6 -> xevents8/xevents5 (+ ana5), negative controls; table |
| `k3/out/builds.txt` | toolchain fingerprints, md5s, unplaced seeds, audit lines |
| `k3/out/{ipow,xorshift}/` | xe8_*, xe5_*, cert8_*, cert6_*, ana5_*, skel_*, neg*.txt, table.txt |
| `k3/out/xorshift_audit_fail_3_7.txt`, `xorshift_3_audit_tighten.txt` | the rule A/I failures |
| `formal/out/HOWTO-new-kernel.md` | rewritten for k3/ and xevents8 |
