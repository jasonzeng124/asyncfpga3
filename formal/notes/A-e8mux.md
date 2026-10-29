# A-e8mux (probe E8Mux, shard A): OUTMUX hop on O5/F7/F8 arcs, Events8 rerun

STATUS: in progress (started 2026-10-29). Nothing claimed yet.

Progress log:
- toolchain restored from origin/toolchain-cache/d7ce266cff0c8e1e (git cat-file, no fetch) into
  ~/dev2/lib/fpgatoolchain; cells/verify/toolchain.sh exit 0, 9/9 ok, nextpnr sha256 9c732bc6303458df.
  apt libs were already present; pip installed intervaltree + simplejson (prjxray imports).
- source: `git archive 520a43f` -> ~/e8src (no worktree); builds one nextpnr at a time
  (scratch e8mux/build4.sh). Seed d: SDF a9c4e265 AND routed.json b398103e = events5/builds.txt
  (both match; fasm_audit PASS; bitstream step fails on missing textx, not needed).
  Seeds 3/4/5 likewise: all 8 md5s (SDF and routed.json) equal events5/builds.txt.
- seed d, old calculator (99b10a6d) -> routed2x: net.json 5c0830d5 (= builds.txt) and band files
  identical to the committed ones key for key on slow / indep / gb; on fast exactly the 20 known
  lo > hi arcs differ (now the hull, A-kapres's data quirk).
- seed d, new calculator (e8mux/xray_delay_e8mux.py): changes 10534 O5-driven, 2459 MUXF7/F8-driven,
  298 CARRY4-driven and 264 FF(x5FF)-driven IC rows; 0 O6-driven rows. The 236 unchanged O5 rows are
  all O5 -> CARRY4 DI inside the slice (no OUTMUX). Shift at SLOW_MAX: O5 +202..+231 ps,
  MUXF +173..+195. new == research 7dc5dde (3e69bf6a) on all 40083 comb->comb IC rows.
  Seeds 3/4/5: the same (old = committed bands key for key except the 7 / 8 / 2 lo > hi fast arcs;
  nets 1d655434 / 8da9f6cf / 1537cb0a = builds.txt; 0 O6 rows changed; new == r7 on 40083 rows).
- xevents8 overlay built (e8mux/mkolean.sh, 26 modules, 0 errors). Reproduction: old bands, seed d
  gb -> results/xe_d_old_gb.txt is byte-identical to events8/xe8_d_gb.txt.

## Plan
1. Band pipeline: routed JSON + SDF -> research xray_delay.py 99b10a6d (arcs TSV) -> routed2x.py
   (net.json + bands) -> events4/skel.py -> events8/cert8.py -> xevents8. 99b10a6d charges the
   slice OUTMUX only from O6 (tile pseudo-pip X->>XMUX) and COUT; O5 / F7 / F8 / CARRY4 O,CO
   through xOUTMUX are charged 0. Fix in tools-A/xaudit/e8mux/ (copy of 99b10a6d + ROUTING_BEL
   hop for every other xOUTMUX source), cross-checked against research 7dc5dde (3e69bf6a).
2. Routed data is not on disk: restore toolchain (A-k2 procedure), rebuild gcd_hw R5 d/3/4/5,
   check SDF md5 against events5/builds.txt.
3. Rebuild bands, rerun xevents8 on 16 rows + negative controls, old vs new table.
4. Correct A-events8.md (line 74, ENTRY table).
