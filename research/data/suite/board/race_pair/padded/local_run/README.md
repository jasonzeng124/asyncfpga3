# The padded half of BOARD-QUEUE item 46: the local run that made and judged it (committed 2026-11-22 for auditor T182)

Made by `rk_launch.sh v11 test_flatten_array 2` (copied here; it ran on the cluster node 2026-11-21, research head
e0a4b59f0d-era working tree, nextpnr 6e5d224472232d5d): flow v11's environment plus AUTO_RACE_KAPPA=0.13, SUITE_TAG=rk11.

- `result.txt`, `draws.txt`, `draw_*.txt`, `benchres_*.txt`: the four draws (10201-10204) on route rk11 it 11 (sdf
  2361eec8; 110 trims applied by LUT INIT, trimmed fasm 5fcd82f8 -- the bits item 46's spec rebuilds), each PASS 1 / 1
  with every array word equal to the C (`memexp.txt`, research/tools/suite/oracle_mem.sh; `exp.txt` the return values).
- `loop/`: the sizing loop's log (the race check padding ULINK_N101_FOLINK 1 -> 3 at it 10, the late phase from it 11),
  its result line, it 11's sizes / seed / trim record, and the race checks (race_I.txt: race_find.py in the draw model;
  racek_I.txt: race_kappa.py's split-corner bound, weakest 0.241 on it 11).
The auditor's own GLS of the rebuilt pair (T182) stands beside this.
