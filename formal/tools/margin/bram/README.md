# margin/bram: memory kernels in formal's simx (shard C, 2026-11-19; UNTRUSTED simulation)

Formal's board approximator (simx on the circuit decoded from the bitstream, research's draw model) for kernels that use
RAMB18E1 block RAMs, i.e. every kernel with research's benchvec (v2) vectors.

## One command
    RS=<claude/research checkout> [FLOW=auto|default] [HOSTPORT=1] [BDC_...=..] \
      bash formal/tools/margin/bram/memtask.sh K SEED SIZES.vh|none SDF8|- OUT [NDRAWS] [K0]
builds the route in a private copy of research's tree (build_bench.sh; BDC_AUTO=1 unless FLOW=default; checks the sdf
md5 prefix SDF8 against research's, '-' for a new route), reads the bits back (prjxray bit2fasm), decodes them, and runs
NDRAWS (16) draws of research's model from K0 (10000 + 100 SEED + 1) plus NDRAWS slow draws (CARRY4 / F7F8 / FF / RAMB18
in [0.8, 1.0]). OUT/summary.txt; OUT/draws_<K0>.txt has one line per draw (RAMCHECK, RAMMARGIN, host writes, answers).
Needs research's FPGA toolchain under $TC (in a cloud sandbox: research's cloud/toolchain-cache.sh branch, see
JOURNAL-C.md 2026-11-19 07:50, plus libtcl8.6 / boost 1.83 and prjxray's python requirements).

## Pieces
| file | what |
|---|---|
| decode_bram.py | decode_dsp.py (decode_base + DSP48E1) plus every RAMB18 site in use, strict whitelist (port A x18, WRITE_FIRST, DOA_REG 0, port B never clocked); every constant control's logical value and every RAM / DSP pin's net checked one-to-one against nextpnr's routed json |
| bram_gates.py | one simx gate per read DOADO bit (flag 3): prjxray CLK->DOADO 585-2454 ps on the clock arc, setup / hold windows from BRAM_L.sdf (widest: ADDR 566 / 360, WE 532 / 197, DI 737 / 667 ps) |
| ../simx.cpp | flag 3: one RAM state per site, stepped lazily at the clock node's rising edges, pins sampled at the pin, WRITE_FIRST; setup / hold violations = RAMVIOL (not a pass); RAMMARGIN = smallest margins; `--mem` fills / expected contents; `--hostport` fills through each array's host port as gen_bench.py's sequencer drives it (payload one aclk before the request, 2-flop-synchronised acknowledge, HOSTCLK 12000 ps, HOSTGAP 8 idle edges) |
| memvec.py | research's benchvec + oracle_mem.sh (from the C, ORACLE_RUNS=1) -> pairs / want / mem file (F fill, X expected, H host write) |
| mk_bnd_mem.py | A's mk_bnd_sim.py for memory kernels: no-operand kernels, every input channel's ack waited for (xacks), host ports, void kernels (the bench's completion join is out0) |
| ramslack.py | the RAM read capture slack: every CLK->DO +X until a result goes wrong (one draw, bisection) |
| hostrace.py | the host-write race in ps: host request -> CLKARDCLK vs -> WEA / ADDR / DI, static path sums on the decoded bits, both paths named |

## Checked so far (FOR-RESEARCH C60)
16 headline memory routes of research's automatic flow, sdf-identical: every draw passes, every array read back right.
Negative controls fail: BDC_MEM_NOCAP=1 on test_bool_array (0 / 32), a perturbed fill, late RAM sampling, CLK->DO +60 ns.
Decoder controls (memsum s1): the RAM's clock inverted in the FASM (ZINV_CLKARDCLK removed) is refused; an INT pip on
a DIADI route removed leaves the pin floating and is refused (a BRAM-tile pseudo-pip removed changes nothing: the walker
re-derives it, as for any implicit pip).
With HOSTPORT=1 formal finds research's known-bad if_loop_1 s1 (host-fill WE setup race on umem0) in 2 of 64 draws.

## Not covered
The read-back is taken from the RAM's contents, not through the host port. RAMB36 / cascades / port B / registered
outputs / INITP are refused. A setup / hold violation is counted, not propagated as X. More than two operand words.
