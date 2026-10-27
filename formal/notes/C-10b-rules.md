# C-10b: would a verified checker make rules E / A / J exact?

Status: IN PROGRESS (notes written first; Lean file Formal/Timing/Rules.lean
being written). See the bottom of this file for the current state.

## Findings so far (from reading the code and the toolchain)

* The SDF every rule reads is nextpnr-xilinx's: ONE number per arc
  (min = typ = max). Interconnect = sum of `getPipDelay` over the route, where a
  tile pip costs `max(slow_min, slow_max)` from prjxray-db plus a crude RC term,
  floored at 35 ps; site entry/exit and LUT-permutation pips cost a flat 25 ps;
  LUT route-throughs 300 ps. Cell arcs = `max` over prjxray's two triples =
  slow-corner max (LUT6: 124 ps for every pin). Source: openXC7/nextpnr-xilinx
  `xilinx/arch.h` getPipDelay, `arch.cc` xc7_cell_timing_lookup,
  `common/sdf.cc` (`FIXME: min/max routing delay`), and
  `$TC/openxc7/lib/python/xilinx_device.py` lines 415-434.
* prjxray-db site INPUT pin delays (CLBLL A1..A6: slow max 516, 507, 344, 284,
  112, 5 ps) are NOT in the SDF (25 ps flat). Which physical LUT pin a net lands
  on (nextpnr permutes) changes the real delay by up to ~0.5 ns, invisibly.
