# Sources for the fid metastability / pulse parameters (literature search, 2026-10-29)

Web search only; nearly every publisher host was blocked by the sandbox proxy, so the numbers below come from
search snippets, not the papers themselves. Page and table numbers still need checking.
**Result: none of the fid assumptions (TAU=WIN=150 ps for LUT loops, TAU_FF 75 ps, aperture 50 ps, a minimum
CK pulse of 70 ps, LUTs passing any pulse width) has a 7-series source.** They stay assumptions.

| parameter | fid today | best sourced value | source |
|---|---|---|---|
| TAU_FF, 7-series | 75 ps | none for 28 nm. Older parts: 36.8 ps (Virtex-II Pro, 130 nm, 1/K2); 57/51/73 ps (Stratix/II/III, 130/90/65 nm) | XAPP094 v3.0 Table 1 and P. Alfke on comp.arch.fpga (2002); Beer, Ginosar et al., "The Devolution of Synchronizers", ASYNC 2010 |
| 28 nm flop tau (unread) | - | Kintex-7 measured on 4 boards at ~200 placements; the finding is that tau varies more than FO4 | Mekie, Mukim, Kale, VLSID 2018 pp. 459-460 (ieeexplore 8326975); ASYNC 2016 slides S3P3 |
| FF aperture | 50 ps | none (report_synchronizer_mtbf supports UltraScale only and its constants are not published; UG835) | - |
| TAU / WIN, LUT loop | 150 / 150 ps | none. A LUT NAND mutex on Spartan-6 resolves more slowly than a flop (qualitative) | Toan, Tung, Lee, IEICE ELEX 15(1) 2018; Polzer & Steininger, PATMOS 2013 (C-elements, FPGA) |
| flop min CK pulse | 70 ps | no document row found. Vivado report_pulse_width per-pin limits (~0.5 ns at -1, UNCONFIRMED) | run report_pulse_width (no Vivado here) |
| LUT pulse rejection | passes any width | none | - |
| no glitch on a single-input change | assumed | stated for XC3000/XC4000 only ("there can never be a decoding glitch when only one select input changes") | XAPP024 v1.0 (1997) |

How to read it:
- Measured flop tau has stayed at 35-75 ps from 130 to 65 nm, so TAU_FF 75 ps sits at the slow end of that range,
  which is the pessimistic side. TAU=150 for a LUT loop is twice that, and the only LUT-mutex study says such a
  mutex is slower than a flop, without a number. The r18 double-ack cutoff (trp cap tau*ln(WIN/2) = 647 ps)
  scales linearly with TAU, so it is no better known than TAU.
- A datasheet minimum pulse width bounds guaranteed operation; it is not a physical rejection threshold. If
  the ~0.5 ns Vivado limit is confirmed, a CK runt between 70 ps and 0.5 ns is outside spec, and GLS should
  report it as a violation instead of resolving it. Not acted on (unconfirmed).
- To get real 28 nm numbers: allow ieeexplore.ieee.org and jstage.jst.go.jp in the environment's network
  settings and read Mekie 2018 and Toan 2018, or measure on the board (an arb_mtbf-style bench; BOARD-QUEUE).
