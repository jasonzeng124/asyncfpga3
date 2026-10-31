# A-e9arbnet (probe E9ArbNet, shard A): lifting the cell-level arbiter core to the netlist

STATUS (2026-10-31 07:55, lead): CLAIMED as left by the 2026-10-29 session (which died before claiming).
Events9ArbNet / ArbNetRows / ArbNetEdge / ArbNetMain checked on 2026-10-31 by the lead with Lean 4.35.0,
-DautoImplicit=false, in a scratch overlay of the tree (plain `lean`, same sources; lake build pending),
axiom audit: only propext / Classical.choice / Quot.sound. What is proved:
- `arb_core`, `harb_of_arbs`, `design_verdict9arbnet`: design_verdict9par with HARB7' and HRst
  replaced by the decidable checks ArbOK (bd_arbiter's four LUT functions read off the INITs, every
  read path, request nets, corrected-core shape and bands), OwnOK, RsOK, FixShape, and the
  per-arbiter TRACE conditions ArbCond (hypotheses).
- `Events9ArbNetEdge.arbCond_of_edge`: ArbCond follows from the decidable rows ArbRowsOK (B1 rows and
  start bounds) plus the edge-window hypotheses ArbEdge: QClean (q makes clean transitions: the
  digital no-metastability hypothesis), a quiet start, a settle bound H (`stall`; no band bounds it,
  and for a near tie none exists), and per reader RdEdge (no re-request while the arbiter switches
  away; settledness windows after request rises / literal flips; A0 high around request falls).
- `Events9ArbNetRows.Rows`: DEFINITIONS of printed margins only. No theorem says the printed rows imply
  ArbEdge. The run tables (results/xan_*) are from 2026-10-29: ArbOK 9/9 on all 16 rows; the printed
  B1 margin is negative on some arbiters (seed d slow: merge6.uarb1 g1 -2 ps, s1 -190 ps; merge4.uarb1
  s1 -32 ps), so ArbRowsOK fails for those arbiters at that corner and arbCond_of_edge does not apply
  to them there.

Plan
1. ArbNet check: for each arbiter named in the certificate, a decidable check over A's parsed
   design `d` that its ustate/ugrant LUTs are bd_arbiter's (INITs ARB_ST/GRANT, pin wiring),
   and a theorem SatPin on d + per-reader conditions => the cell-level ArbPin behaviour =>
   (core_of_en_rst) HARB7'/HRst at that arbiter.
2. B1/B2/C/settle as decidable rows over the band file's per-pin arcs and the certificate's
   walks; executable; run on 16 rows.
3. What remains: Unc W, metastability (settle bound H not available for near ties).
