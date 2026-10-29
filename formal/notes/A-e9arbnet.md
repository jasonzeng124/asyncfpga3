# A-e9arbnet (probe E9ArbNet, shard A): lifting the cell-level arbiter core to the netlist

STATUS (2026-10-29 12:35): IN PROGRESS. Events9ArbNet.lean: req_val, ArbOK (decidable), ArbCond, arb_core
(SatPin + ArbOK + ArbCond => CoreOfR on the wires of d) compile (overlay); ND7 lift next. Nothing claimed yet.

Plan
1. ArbNet check: for each arbiter named in the certificate, a decidable check over A's parsed
   design `d` that its ustate/ugrant LUTs are bd_arbiter's (INITs ARB_ST/GRANT, pin wiring),
   and a theorem SatPin on d + per-reader conditions => the cell-level ArbPin behaviour =>
   (core_of_en_rst) HARB7'/HRst at that arbiter.
2. B1/B2/C/settle as decidable rows over the band file's per-pin arcs and the certificate's
   walks; executable; run on 16 rows.
3. What remains: Unc W, metastability (settle bound H not available for near ties).
