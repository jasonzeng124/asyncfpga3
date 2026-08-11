# 06 — Cross-tool benchmarking

Two independent errors invalidate most HLS-vs-HLS comparisons. Both are
easy to reintroduce.

## Trap 1: simulated "ns" are LUT hops

A simulation model charging 1 ns per LUT hop reports *hop counts* wearing
a time unit. Comparing that to another tool's routed nanoseconds is a unit
error. It hides on iCE40 HX8K, where a hop really is ~1090 ps; on xc7
(~478 ps/hop) it overstates latency ~2.3×, and composite error against
routed ns has reached ~7×.

- Report `hops/call` as the primitive quantity.
- Convert only through an explicit, **measured** per-hop-ps value.
- Measure from routed `chain_ps / T`, never from LUT-arc delays (routing
  is ~74% of a hop on xc7 ⇒ arc-only is ~3× wrong).
- Quote the **tightened** build. Post-route margin tightening was worth
  ~2× on a design taken all the way through (sumT 222→112, audit still
  PASS, LC 1271→1161).

## Trap 2: the reference kernel gets constant-folded

Bambu's "33 cycles / 270 ns" gemm is reproducible and **never
multiplies**. Clang-16 `-O2` precomputed the 8×8×8 product at compile
time: 0 `mult_expr_FU`, 0 DSPs, 1 BRAM of precomputed results. Measured
behavior: stream 64 constants into a BRAM + 1 read.

- **Removing `const` is not enough** — a never-written file-scope `static`
  folds too. Data must be genuinely runtime-dependent (e.g. seeded from a
  function argument).
- Reverse direction: translating writable-memory-with-preload arrays into
  `static const` hands the competitor a strictly easier problem.

## Bambu reference numbers (xc7z010, Bambu's own measured sim cycles)

| Kernel | Cycles | Fmax | Latency |
|---|---|---|---|
| `sort(4)` | 823 | 94.09 MHz post-place / **148.90 post-route** | **5.53 µs** |
| `gemm(3,5)` runtime-data | 307 | ~100 MHz pre-route estimate only | ~3.07 µs, not signed off |

Use **post-route** Fmax. `gemm` runtime-data resources: 34 DSP48E1,
3 BRAM. These runs used zero pipelining pragmas.

## Bambu operational notes

| | |
|---|---|
| `--device-name="xc7z010,-1,clg400,VVD"` | **rejected**; use `xc7z020,-1,clg484,VVD` (HLS frontend is device-agnostic; the real part applies at nextpnr-xilinx P&R) |
| `--simulate` | unavailable here — no verilator, and the AppImage has no Icarus option. Hand-write an iverilog TB counting clock edges. |

## Fairness mechanics

- Identical inputs. A harness picking random vectors is useless against a
  fixed-input reference on a data-dependent kernel.
- Per-call latency = **inter-completion delta over repeated identical
  calls**. One vector yields one timestamp and a span of zero.
- Same device, same toolchain, same chipdb, both sides.

## Interpreting results

A 4-phase handshake design paying a full round trip per loop iteration
with zero overlap is near worst-case for dense regular kernels and
best-case for a static pipeline. Dense fixed-trip loops (e.g. 512 serial
MACs on a carried dependency) are the extreme; irregular data-dependent
control flow is where the gap narrows. Closing the gap on regular loops
requires loop pipelining (multiple tokens in flight) — an architecture
change, not a compiler pass.

Area typically favors the handshake design (no pipeline registers, no DSP
inference): 1600 LUT / 1 BRAM / 0 DSP vs. 4082 LUT / 728 FF / 3 BRAM /
34 DSP on the same kernel.
