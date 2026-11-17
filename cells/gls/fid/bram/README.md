# RAMB18E1 in the bits-decoded full stack (2026-11-17)

Until this change the bits-decoded GLS (`fasm2net.py` -> `gen.py` -> `prims.v`, the stack
`research/tools/eventgraph/bench_gate.sh` runs) REFUSED block RAM, so no kernel with a memory could be
gated: worse, a design with one decoded WRONG without a refusal -- the RAM's output pins were
undriven nodes, the tracer fell through to the IMUX default, and every flop fed by DOADO read the
constant 1 (mem_port_ps, before: 32 "SDF interconnect source differs from the bitstream's driver",
83 "pip driven from a floating node"; the only hint was in report.txt).

Now ONE configuration is decoded and simulated: the RAMB18E1 exactly as `cells/rtl/bd_mem.v`
instantiates it (TDP, port A x18, port B off, DOA_REG=0, WRITE_FIRST, no INIT). Everything else is
refused, at three places: `fasm2net.py decode_bram()/check_bram()` (the bits), `gen.py ram_config()`
(the netlist's parameters and the SDF's timing), `fasm_equiv.py` section 2c (bits against the routed
JSON). What each file does is in `../README.md` ("RAMB18E1") and in the `prims.v` model's header.

## Files

| file | what |
|---|---|
| `../fasm2net.py` | `decode_bram()`: a used RAMB18 half -> `RAMB18E1_RAMB18E1` `<site>/RAMB18E1` (nextpnr's bel name), every BRAM tile feature consumed or refused; `check_bram()`: inversions (ZINV), port B off, ADDRATIEHIGH high, CLK a net, INIT_A/SRVAL_A |
| `../xray_delay.py` | inserts the RAM's CLKARDCLK -> DOADO/DOPADOP arcs and SETUPHOLD windows from prjxray-db `timings/BRAM_*.sdf` (nextpnr writes none) |
| `../../gen.py` | the cell type, ports, parameter refusals, baked timing (TCLK_DO/DOP, TSU/THD per pin class); refuses a RAM with no clock-to-out or no SETUPHOLD in the SDF |
| `../../prims.v` | `RAMB18E1_RAMB18E1`: 1024 x 18, write-first, power-up 0; a setup/hold violation poisons the edge's word and DO with X |
| `../fasm_equiv.py` | 2c: configuration, effective CLK/EN/RST/ENB (constant XOR inversion), drivers of every ADDR/DI/DIP/WE pin |
| `gen_ps7_memport.py`, `ps7_memport.v` | a PS7 host for `cells/hw/mem_port_ps.v`'s BIST (the self-test design) |
| `memport_gate.sh` | the self-test: mem_port_ps, decoded from its .bit, at bench_gate.sh's `worst` corner |

## How to run it

    cells/hw/build_mem.sh mem_port_ps                      # (absolute path: the script cd's into cells/)
    cells/gls/fid/bram/memport_gate.sh cells/build/hw_mem/mem_port_ps/default WORK

and for a bench kernel with a memory (cells/hw/build_bench.sh K, emit --host-mem), the bench gate as usual:

    research/tools/eventgraph/bench_gate.sh HWDIR K_bench_gen WORK VEC.hex VEC.exp worst

The RAMB18E1's clock-to-out sits at `GLS_SDF_BAND` (0.288) in bench_gate.sh's `worst` and `draw:K` unless
`RAMB18E1_RAMB18E1` is added to their `GLS_SDF_BAND_CELL` lists; it was never measured on the board, so the slow end
(1 in `worst`, the unmeasured class's XK in `draw:K`) is the conservative choice for bd_mem (its DCO must cover it).

## Measured (nextpnr 9c732bc6303458df, toolchain.sh all ok)

### mem_port_ps (cells/hw/build_mem.sh, NEXTPNR_SEED=1, no --freq in that script: routed Fmax 97.98 MHz)

One RAMB18E1 (lower half, FIFO18E1 site). Before this change `fasm2net.py --ps7 --bit` decoded the eight flops fed by
DOADO as reading constant 1 (32 SDF driver mismatches, 83 "pip driven from a floating node"), with no refusal.
After: 1 `RAMB18E1_RAMB18E1`, 0 BRAM refusals, 0 BRAM features unconsumed (the one remaining unconsumed feature,
CLK_HROW_CK_IN_L0_ACTIVE, is mem_port_ps's own edge_cap clocking, not BRAM); `fasm_equiv.py`:
`VERDICT: EQUIVALENT (only the benign kinds above)`, 2c compared 1 RAM, 1556 nets with identical pip sets, 0
differ, 732/732 LUT functions identical. `gate.vvp`: ANNOTATE_DONE, 0 warning and 0 error lines (the RAM's 18
CLKARDCLK->DO IOPATHs annotate onto prims.v's specify paths).

### memsum (cells/hw/build_bench.sh memsum at 3d7e853d4, BD_NO_TIGHTEN=1 BD_SIZES=none BD_DSP=1, seed 1, 107.09 MHz)

Two RAMB18E1 (the 32-bit gang of bdc_memport_5_32_2: one lower half, one upper half -- both site types).
Decode: 2 `RAMB18E1_RAMB18E1`, 0 BRAM refusals, 0 BRAM features unconsumed. `fasm_equiv.py`: `VERDICT:
EQUIVALENT`, 2c compared 2 RAMs, 9529 nets identical pip sets, 0 differ, 5997/5997 LUTs identical. (report.txt's 69
"SDF interconnect source differs" are the bench's `$ge` comparator CARRY4s, whose yosys names hold a backslash the
SDF re-key strips; the same 69 appear in gcd/ipow/collatz bench runs without any RAM.)

`bench_gate.sh ... worst` (as shipped: the RAM's clock-to-out at band 0.288 = 1123 ps, 1343-1347 ps after the
M-scatter max over the 16 DOADO arcs), `GATE_PLUSARGS=+MEMCHECK=1`, the suite's memsum.hex (5 calls, arrays drawn
in [-1000, 1000], n = 32, 20, 1, 0, 33; expected values from `research/tools/suite/oracle_mem.sh`, the C):
**PASS 5/5**, every batch 2/2 runs agreeing, odata 00000d25 ffff359a fffffc21 00000000 000073aa = the oracle;
host read-back of all 32 words after every fill: 0 bad (5 calls); 0 RAMB18 setup/hold messages, 0 FF violations,
no memport one-hot message; t_end 89.4 us simulated, about 6 min of wall time.

PENDING
