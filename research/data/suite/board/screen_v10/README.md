# Formal's B24 steer screen on flow v10's board candidates (run here, 2026-11-21)

Tool: formal/tools-B/auto/racescreen.sh at claude/formal 36ba04ea34 (a detached worktree of origin/claude/formal),
RS = this checkout, on each route rebuilt by research/tools/suite/board_rebuild.sh (sdf and trimmed fasm checked).

    # HW = a COPY of the rebuilt HW dir (bit made from the TRIMMED fasm) plus the build's synthesis JSON, which
    # lane2.sh does not keep: <lane worktree>/cells/build/hw/K_bench_gen/K_bench_gen.json -- without it the screen
    # prints "DECODE FAILED" and a traceback in its summary line.
    RS=$PWD bash <formal>/formal/tools-B/auto/racescreen.sh K HW OUT <lane worktree>/cells/build/gen

| route | steers bounded | min kappa_lo | latch-fed race | first pulses / first failure (path error x) | B24 guide |
|---|---|---|---|---|---|
| collatz v10 s1 (sdf 0f050078, fasm 6ef8e077) | 10 of 12 (ucond_br7: "no launch node for ucmpi2.ujoin") | 0.061 | none | none to 0.25 / 0.25 | fine |
| xorshift v10 s1 (sdf fd959b30, fasm 78aa6ac3) | 16 of 16 | 0.091 | ucond_br7 +597 / +1492 ps, no failure to kappa 0.20 | 0.25 / none to 0.25 | fine |
| collatz64 v10 s1 (sdf de88e329, fasm 9b93469d) | 10 of 12 (ucond_br7 as collatz) | 0.003 (ucond_br6: +29 / +1108 ps) | none | **0.08 / 0.15** | NOT fine (pulses at x <= 0.10) |

Files: K_s1_racescreen.txt (the one-line summary), K_s1_steersafe.txt (per steer LUT). The output-capture kappa_lo
(-0.28 / -0.19 / -0.35) is at formal's 3 ns sampling point; the PS bench samples ~24 ns after the request
(CA_BENCHCAP), as discussed in FOR-FORMAL 2026-11-20 15:40.
