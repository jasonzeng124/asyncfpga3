# ro_many_top, second route: the band-transfer test (BOARD-QUEUE "Board list" item 4)

Built 2026-11-05 in the cloud with the August recipe: `cd cells && BD_NO_TIGHTEN=1 BD_RLOC=none hw/build_hw.sh
ro_many_top` (default seed), nextpnr 9c732bc6303458df (toolchain.txt: every patch ok); build_hw PASS incl. fasm_audit.
The netlist decoded from this .bit is EQUIVALENT to its routed JSON (bits_vs_routed_equiv.txt).

md5: ro_many_top.bit 8dc4f1ac77208e8f105e0ff2e8faec88; routed JSON 0f22d3851ad50cb58c9266fbbc376df7 and nextpnr
SDF 28248a6973fb8b8489cb3e361237dbd4 (both .xz here); prjxray SDF of the route (xray_delay.py) 3fb582274ae4b227...;
predicted.tsv 941dea3da5459b8ab9cef95bed863736.

`predicted.tsv` was written BEFORE any board run: per ring, the full stack's FAST_MIN and SLOW_MAX periods
(cells/gls/fid/ring_predict.py on the prjxray SDF) and band_ps = FAST_MIN + 0.288 * (SLOW_MAX - FAST_MIN), with 0.288
the band ring128 fixed on the FIRST (August) route. Whether one band transfers to another route is what this tests.
