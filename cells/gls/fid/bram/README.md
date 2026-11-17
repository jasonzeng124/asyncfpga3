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

RESULTS_PLACEHOLDER
