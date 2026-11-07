# August ring measurement, n = 128 (owner's machine, committed 2026-11-03)

Answers BOARD-QUEUE "Owner-side data request: the August n=128 ring raw data".

- **Source:** `cells/build/hw/ro_many_top/` on the owner's machine, file dates 2026-08-23 21:15-21:31 (local time).
- **Raw logs:** `raw/g00.log`-`raw/g15.log`, read by `cells/hw/ro_many_measure.py`. Measured on the board in August; nothing was re-measured.
- **Build:** `ro_many_top.bit`, `ro_many_top.fasm`, `ro_many_top_routed.json`, `ro_many_top.sdf` and `toolchain.txt` (nextpnr d216cb36a370f78a, with the lut-pinmap, dsp-areg, dsp-constpins and rloc-group patches) are the files of that build.
- **Self-check:** run from claude/research at 437054ec, with the raw dir linked in. `RO_OFFLINE=1 RO_MEAS_TSV=measured.tsv python3 hw/ro_many_measure.py` exits 0 and writes `measured.tsv` with 128 rows plus a header. The widest per-ring spread across the two windows is 0.052%.

md5:
```
8ca7e9c6918a0becd77dede69513e2a0  ro_many_top.bit
9053d67055fede07dae1c1b56cf10c7c  ro_many_top.fasm
b21995471a92870cd4829bd3036319e3  ro_many_top_routed.json
07cfac53e1d1435f75ba16cceb04816f  ro_many_top.sdf
dda74f43e602ab8c2d9b722257a7410c  toolchain.txt
5b0eee1ca6e9c0d94664b52617924141  measured.tsv
```
