# August board builds (from the owner's machine, pushed 2026-11-17)

The routed outputs of the five bench builds as they stood in `cells/build/hw/NAME_bench_gen/`
on the owner's machine: the `.fasm` and the nextpnr `.sdf`, xz-compressed (`xz -dk FILE.xz`).
All ten are dated 2026-08-24, the same day as `cells/hw/gcd_cost_results.tsv`.

| file | md5 of the uncompressed file (first 8) | uncompressed size |
|---|---|---|
| `gcd_bench_gen.fasm.xz` | 19e94eb9 | 7.2M |
| `gcd_bench_gen.sdf.xz` | 14061c44 | 17M |
| `xorshift_bench_gen.fasm.xz` | b1a95f99 | 3.9M |
| `xorshift_bench_gen.sdf.xz` | b85c627e | 7.2M |
| `collatz_bench_gen.fasm.xz` | d2491dc8 | 4.1M |
| `collatz_bench_gen.sdf.xz` | ea55fc43 | 8.4M |
| `collatz64_bench_gen.fasm.xz` | e82fdbe3 | 4.7M |
| `collatz64_bench_gen.sdf.xz` | 107c16c9 | 10M |
| `ipow_bench_gen.fasm.xz` | 24b35733 | 4.1M |
| `ipow_bench_gen.sdf.xz` | b9557e51 | 13M |

What is known and what is not:

- These are the last builds made in those directories in August. Nobody has checked that each
  one is the exact bitstream behind a given board measurement (xorshift 47.66, collatz 91.96,
  collatz64 112.71 ns per iteration; gcd's cost table). The dates agree for gcd. If the
  simulation of one of these matches its measurement, that is evidence it is the measured
  build; if it does not, first ask which build was measured.
- They were built with the August toolchain, before the later nextpnr patches. Today's flow
  will not reproduce these routes.
- The `.bit` files are on the owner's machine too and were not pushed. Write `ASK:` in the
  journal if the `.fasm` is not enough.
