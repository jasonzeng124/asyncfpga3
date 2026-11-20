# trim: shortening matched delay lines after routing, by LUT INIT alone (2026-11-20)

Research bot, session cluster-research-29671222-1; nextpnr 6e5d224472232d5d (toolchain.sh all ok).

## The mechanism
A bd_delay / bd_delay_gated line (cells/rtl/bd_latch.v) is a chain g[0] = LUT1(s[0]), g[k>=1] = LUT2(s[k], side) where
`side` is the line's own input (FASTFALL: AND, INIT 1000; FASTRISE: OR, 1110; gated: AND with `gate`). Setting one
element g[i]'s INIT to 1100 (O = the side input) makes g[i] the line's entry: the line is then N - i elements, with the
same edge behaviour, on the SAME placement and routes. So a routed line of LUT2s can be shortened to any length 1..N
by bits alone; lengthening still needs a route. Symmetric lines (LUT1 elements) cannot be trimmed.
- research/tools/auto/trim_lines.py ROUTED_JSON FASM_IN OUT_JSON OUT_FASM [--partial] MACRO=LEN ...: the INIT edit in
  the routed JSON and the FASM (each touched LUT site's 64-bit INIT recomputed with cells/verify/fasm_audit.py's
  expected_lut_bits, X_ORIG_PORT pins included); then the bitstream from the FASM as build_bench.sh makes it.
- The rule reads trimmed lines: cells/verify/tighten.py chain_side_arcs() no longer treats an entry's side arc as a
  fast-fall side tap (an entry has no live arc from the stage before it: false_arcs() cuts it from the INIT), and
  research/tools/corner_audit.py chain_geometry() starts a trimmed chain at its entry. Untrimmed, both are byte-
  identical (xorshift s1 it 5: neg, rule.vh, report / tighten / skew logs, lines.tsv at both corners).

## First measurement: xorshift s1, the != fixture, the loop's shipped route (ex_xorshift_1_9, sdf d947adff)
- Untrimmed: P 18.09 ns, NOT CLEAN by one row (H -30 ps on ulink_n_falseResult_9 stage 1: the rule wanted its UACK
  raised 1 -> 2). Its finish phase had pinned ucmpi1 back at 15 (11 at it 5).
- The rule's own proposal on that route shortens 15 lines; 10 macros (14 chains) are trimmable (ucmpi0 8 -> 7, ucmpi1
  15 -> 12, ucontrol_merge1 3 -> 1, ulink_n12__0 3 -> 2, three UACK lines, umux1 7 -> 3, umux2 6 -> 2, uxori2 3 -> 1);
  ulink_n12__1 and ulink_n31_folink are symmetric lines (refused); two _SDELAY macros had no chain.
- Trimmed (14 LUT INITs, nothing re-placed or re-routed): **P 15.18 ns (-2.91 ns, -16 %)**, event-graph checks PASS
  (xs_ex9_trimmed_check.txt); bits-decoded netlist **EQUIVALENT**; the rule on the trimmed route (CA_BENCHCAP=1, as the
  loop runs it): **the same single row as before trimming, H -30 / -29 ps, nothing new** (xs_ex9_trimmed_neg.txt);
  **draws 10101-10104: PASS 19 / 19 each**, no pulse under 1 ns on 172 kernel handshake nets, narrowest 2.1 ns.
- Critical cycle (cycdecomp): chains 11410 -> 9212 ps, wires 3833 -> 3833 (the same routes), cells 2845 -> 2138.

## Does NOT show
One route of one kernel; the draws' four points; that a trimmed line's entry (the side net, a fanout wire) is as well
modelled as a chain hop (the rule and the GLS both read it from the same SDF); anything about symmetric lines.
