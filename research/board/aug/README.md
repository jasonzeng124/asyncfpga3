# August board data (owner's machine, committed 2026-11-04)

Every board build from `cells/build/hw/` on the owner's machine that still has its `.bit`, together with every top-level `*.tsv` summary and every
`_*.log` board/run log (331 files, in `logs/`). ro_many_top is already in `../ro_many_aug/`. Nothing here was re-measured.

Large files are xz-compressed (`xz -d`): `<name>.bit.xz`, `.fasm.xz`, `_routed.json.xz`, `.sdf.xz`. Other text files
(< 2 MB: toolchain.txt, pnr/synth logs, tcl, sizes) are copied as they are, paths kept.

**Pairing a log with its bitstream:** a log names the `.bit` it programmed (`programming build/hw/X/X.bit`). `match=yes` means
the `.bit` here is older than the log (file mtimes), so the log measured this exact file. `match=NO` means the build
was rewritten after the log, so the log measured an earlier build that is gone: use it only as soft evidence.

| build | bit md5 | bit mtime | toolchain | logs that programmed it |
|---|---|---|---|---|
| arb_mtbf | `80e60e1f3b68` | 2026-08-10 22:31 | (no stamp) | - |
| arb_prot | `f62c45307eff` | 2026-08-11 12:20 | (no stamp) | - |
| collatz64_bench_gen | `5fbb1377a78f` | 2026-08-24 06:40 | nextpnr d216cb36a370f78a  /home/jayjay/d | 37 match=yes |
| collatz_bench_gen | `6f62bf4a50fa` | 2026-08-24 06:35 | nextpnr d216cb36a370f78a  /home/jayjay/d | 41 match=yes |
| collatz_null_bench_gen | `75dc9e47e235` | 2026-08-24 06:36 | nextpnr d216cb36a370f78a  /home/jayjay/d | 4 match=yes |
| gcd_bench | `74745f8dd36a` | 2026-08-20 05:47 | (no stamp) | - |
| gcd_bench_gen | `f199866ea256` | 2026-08-24 11:45 | nextpnr d216cb36a370f78a  /home/jayjay/d | 27 match=yes |
| gcd_hw | `7f95bb1dda64` | 2026-08-22 07:54 | nextpnr d216cb36a370f78a  /home/jayjay/d | - |
| gcd_null_bench_gen | `3c3d33f5a088` | 2026-08-24 06:00 | nextpnr d216cb36a370f78a  /home/jayjay/d | 4 match=yes |
| gcd_ps | `94580e3878a1` | 2026-08-21 06:38 | (no stamp) | - |
| ipow_bench_gen | `6dbf3faec62f` | 2026-08-24 06:12 | nextpnr d216cb36a370f78a  /home/jayjay/d | 27 match=yes |
| ipow_null_bench_gen | `b41d05da1667` | 2026-08-24 06:28 | nextpnr d216cb36a370f78a  /home/jayjay/d | 4 match=yes |
| ipow_ps | `f4c39b452ef3` | 2026-08-21 14:48 | nextpnr d216cb36a370f78a  /home/jayjay/d | - |
| isprime_bench_gen | `dcf8404d572d` | 2026-08-24 05:42 | nextpnr d216cb36a370f78a  /home/jayjay/d | 32 match=yes |
| isprime_null_bench_gen | `a434e2fd0f8b` | 2026-08-24 07:38 | nextpnr d216cb36a370f78a  /home/jayjay/d | 4 match=yes |
| mult2_ps | `83369a6b145a` | 2026-08-20 11:05 | (no stamp) | - |
| mult_ps | `0a51b65d41ac` | 2026-08-20 11:07 | (no stamp) | - |
| multn_ps | `80a9a3f2b495` | 2026-08-20 07:12 | (no stamp) | - |
| ro_link_ps | `9f5ec4c2adce` | 2026-08-23 13:05 | nextpnr d216cb36a370f78a  /home/jayjay/d | - |
| ro_top | `fa1c803bfcbc` | 2026-08-23 21:16 | nextpnr d216cb36a370f78a  /home/jayjay/d | - |
| xorshift_bench_gen | `604148b326ae` | 2026-08-24 14:42 | nextpnr d216cb36a370f78a  /home/jayjay/d | 0 match=yes, 25 match=NO |

Per-log detail:

- **collatz64_bench_gen**: `_cbranch_collatz64_1024.log`, `_cbranch_collatz64_111.log`, `_cbranch_collatz64_14592.log`, `_cbranch_collatz64_16.log`, `_cbranch_collatz64_20480.log`, `_cbranch_collatz64_256.log`, `_cbranch_collatz64_26482.log`, `_cbranch_collatz64_28704.log`, `_cbranch_collatz64_32.log`, `_cbranch_collatz64_32768.log`, `_cbranch_collatz64_3584.log`, `_cbranch_collatz64_37167.log`, `_cbranch_collatz64_40288.log`, `_cbranch_collatz64_4096.log`, `_cbranch_collatz64_51968.log`, `_cbranch_collatz64_52207.log`, `_cbranch_collatz64_56496.log`, `_cbranch_collatz64_61504.log`, `_cbranch_collatz64_78.log`, `_loop_collatz64_1.log`, `_loop_collatz64_12.log`, `_loop_collatz64_16.log`, `_loop_collatz64_2.log`, `_loop_collatz64_20.log`, `_loop_collatz64_24.log`, `_loop_collatz64_28.log`, `_loop_collatz64_30.log`, `_loop_collatz64_4.log`, `_loop_collatz64_8.log`, `_repeat_collatz64_0.log`, `_repeat_collatz64_1.log`, `_repeat_collatz64_2.log`, `_repeat_collatz64_3.log`, `_rtz_collatz64.log`, `_run_collatz64_bench_gen.log`, `_rungap0_collatz64.log`, `_unif_collatz64.log`
- **collatz64_null_bench_gen**: `_run_collatz64_null_bench_gen.log` (NO)
- **collatz_bench_gen**: `_cbranch_collatz_1024.log`, `_cbranch_collatz_111.log`, `_cbranch_collatz_14592.log`, `_cbranch_collatz_16.log`, `_cbranch_collatz_20480.log`, `_cbranch_collatz_256.log`, `_cbranch_collatz_26482.log`, `_cbranch_collatz_28704.log`, `_cbranch_collatz_32.log`, `_cbranch_collatz_32768.log`, `_cbranch_collatz_3584.log`, `_cbranch_collatz_37167.log`, `_cbranch_collatz_40288.log`, `_cbranch_collatz_4096.log`, `_cbranch_collatz_51968.log`, `_cbranch_collatz_52207.log`, `_cbranch_collatz_56496.log`, `_cbranch_collatz_61504.log`, `_cbranch_collatz_78.log`, `_loop_collatz_1.log`, `_loop_collatz_10.log`, `_loop_collatz_12.log`, `_loop_collatz_14.log`, `_loop_collatz_15.log`, `_loop_collatz_16.log`, `_loop_collatz_2.log`, `_loop_collatz_20.log`, `_loop_collatz_24.log`, `_loop_collatz_28.log`, `_loop_collatz_30.log`, `_loop_collatz_4.log`, `_loop_collatz_6.log`, `_loop_collatz_8.log`, `_repeat_collatz_0.log`, `_repeat_collatz_1.log`, `_repeat_collatz_2.log`, `_repeat_collatz_3.log`, `_rtz_collatz.log`, `_run_collatz_bench_gen.log`, `_rungap0_collatz.log`, `_unif_collatz.log`
- **collatz_null_bench_gen**: `_null_collatz.log`, `_nullcyc_collatz.log`, `_rtz_collatz_null.log`, `_run_collatz_null_bench_gen.log`
- **default**: `_mem_arb_board.log` (NO)
- **gcd_bench_gen**: `_gcd_verify.log`, `_gcdcost_1023_1.log`, `_gcdcost_1024_1024.log`, `_gcdcost_1048576_3145728.log`, `_gcdcost_123456789_987654321.log`, `_gcdcost_12_18.log`, `_gcdcost_1431655765_858993459.log`, `_gcdcost_163840_7.log`, `_gcdcost_1_1.log`, `_gcdcost_1_2147483647.log`, `_gcdcost_2097152_1.log`, `_gcdcost_2147483647_1.log`, `_gcdcost_2147483647_2147483646.log`, `_gcdcost_255_254.log`, `_gcdcost_268435456_268435456.log`, `_gcdcost_3145728_5.log`, `_gcdcost_3_3.log`, `_gcdcost_46341_46337.log`, `_gcdcost_48_18.log`, `_gcdcost_50331648_83886080.log`, `_gcdcost_6291456_11.log`, `_gcdcost_65536_32768.log`, `_gcdcost_786432_262144.log`, `_gcdcost_97_89.log`, `_gcdcost_999983_999979.log`, `_rtz_gcd.log`, `_run_gcd_bench_gen.log`
- **gcd_null_bench_gen**: `_null_gcd.log`, `_nullcyc_gcd.log`, `_rtz_gcd_null.log`, `_run_gcd_null_bench_gen.log`
- **ipow_bench_gen**: `_ipow_exact_11_9.log`, `_ipow_exact_2_23.log`, `_ipow_exact_3_1.log`, `_ipow_exact_3_15.log`, `_ipow_exact_3_7.log`, `_ipow_exact_5_11.log`, `_ipow_exact_7_31.log`, `_ipow_exact_9_27.log`, `_loop_ipow_1.log`, `_loop_ipow_12.log`, `_loop_ipow_16.log`, `_loop_ipow_2.log`, `_loop_ipow_20.log`, `_loop_ipow_24.log`, `_loop_ipow_28.log`, `_loop_ipow_31.log`, `_loop_ipow_4.log`, `_loop_ipow_6.log`, `_loop_ipow_8.log`, `_repeat_ipow_0.log`, `_repeat_ipow_1.log`, `_repeat_ipow_2.log`, `_repeat_ipow_3.log`, `_rtz_ipow.log`, `_run_ipow_bench_gen.log`, `_rungap0_ipow.log`, `_unif_ipow.log`
- **ipow_null_bench_gen**: `_null_ipow.log`, `_nullcyc_ipow.log`, `_rtz_ipow_null.log`, `_run_ipow_null_bench_gen.log`
- **isprime_bench_gen**: `_isprime_cost_1000.log`, `_isprime_cost_10007.log`, `_isprime_cost_1009.log`, `_isprime_cost_121.log`, `_isprime_cost_143.log`, `_isprime_cost_15.log`, `_isprime_cost_169.log`, `_isprime_cost_2.log`, `_isprime_cost_2003.log`, `_isprime_cost_25.log`, `_isprime_cost_289.log`, `_isprime_cost_3.log`, `_isprime_cost_35.log`, `_isprime_cost_4.log`, `_isprime_cost_4001.log`, `_isprime_cost_47.log`, `_isprime_cost_49.log`, `_isprime_cost_5000.log`, `_isprime_cost_60000.log`, `_isprime_cost_65521.log`, `_isprime_cost_7919.log`, `_isprime_cost_9.log`, `_isprime_cost_97.log`, `_isprime_cost_99991.log`, `_repeat_isprime_0.log`, `_repeat_isprime_1.log`, `_repeat_isprime_2.log`, `_repeat_isprime_3.log`, `_rtz_isprime.log`, `_run_isprime_bench_gen.log`, `_rungap0_isprime.log`, `_unif_isprime.log`
- **isprime_null_bench_gen**: `_null_isprime.log`, `_nullcyc_isprime.log`, `_rtz_isprime_null.log`, `_run_isprime_null_bench_gen.log`
- **rulee**: `_xcost_0.log` (NO), `_xcost_1.log` (NO), `_xcost_12.log` (NO), `_xcost_128.log` (NO), `_xcost_16.log` (NO), `_xcost_192.log` (NO), `_xcost_2.log` (NO), `_xcost_24.log` (NO), `_xcost_256.log` (NO), `_xcost_3.log` (NO), `_xcost_32.log` (NO), `_xcost_4.log` (NO), `_xcost_48.log` (NO), `_xcost_6.log` (NO), `_xcost_64.log` (NO), `_xcost_8.log` (NO), `_xcost_96.log` (NO)
- **seedstudy**: `_rtz_xorshift.log` (NO)
- **soak_pinned**: `_soak_collatz.log` (NO), `_soak_collatz64.log` (NO), `_soak_ipow.log` (NO), `_soak_isprime.log` (NO)
- **xorshift_bench_gen**: `_repeat_xorshift_0.log` (NO), `_repeat_xorshift_1.log` (NO), `_repeat_xorshift_2.log` (NO), `_repeat_xorshift_3.log` (NO), `_run_xorshift_bench_gen.log` (NO), `_rungap_xorshift_0.log` (NO), `_rungap_xorshift_1.log` (NO), `_rungap_xorshift_127.log` (NO), `_rungap_xorshift_15.log` (NO), `_rungap_xorshift_2.log` (NO), `_rungap_xorshift_31.log` (NO), `_rungap_xorshift_4.log` (NO), `_rungap_xorshift_63.log` (NO), `_rungap_xorshift_8.log` (NO), `_soak_xorshift.log` (NO), `_trip_0.log` (NO), `_trip_1.log` (NO), `_trip_128.log` (NO), `_trip_16.log` (NO), `_trip_2.log` (NO), `_trip_256.log` (NO), `_trip_32.log` (NO), `_trip_4.log` (NO), `_trip_64.log` (NO), `_trip_8.log` (NO)
- **xorshift_null_bench_gen**: `_run_xorshift_null_bench_gen.log` (NO)

101 logs name no bitstream (build, flow and sim logs); they are in `logs/` for context.

Notes:
- `xorshift_bench_gen` and `xorshift_null_bench_gen` were rebuilt after their board runs, so their logs are soft.
- `gcd_bench_gen` is the build with the August async-latch hang (memory: async-latch-corrupts-state-register). Its cost runs
  (`_gcdcost_*.log`, `gcd_cost.tsv`) completed, and they are the board side of the gcd per-iteration cost model
  (JOURNAL 2026-11-03 07:00). With this build the comparison can be made like for like.
