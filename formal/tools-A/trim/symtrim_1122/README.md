# trimcheck on a BD_SYMTRIM route (shard A, 2026-11-22; FOR-RESEARCH A38)
Route: countloop, research ba7fd2f75e, `BDC_AUTO=1 BDC_AUTO_REWRITES=0 BD_DEFINES=-DBD_SYMTRIM NEXTPNR_SEED=1 BD_DSP=1
BD_NO_TIGHTEN=1 BD_SIZES_GATE=0` via cells/hw/build_bench.sh, toolchain = research's cache key 02809f4230dfd3a7
(nextpnr sha256 7c3bfb9c684a2551, toolchain.sh OK incl. const-sinks). The flow's bitstream step failed (fasm2frames:
missing python module); only the FASM is used here. Untrimmed fasm md5 1b03d8d5; trimmed fe804237.
Trims (rec.txt) by research's trim_lines.py --partial with BD_DEFINES=-DBD_SYMTRIM: three symmetric _SDELAY lines
(entry was INIT 1010) and one fast-fall line (umux0, 1000).
trimcheck.sh: OK (INIT-only diff; 4/4 LUTs as expected; kept pin = side input on all 4; live lengths 1 1 2 6 = record).
Negative control: record with N6_SDELAY=3 instead of 2 -> FAIL, rc 2.
