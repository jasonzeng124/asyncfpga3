# Flow v10 tasks finished locally (2026-11-21)

digitsum s2, digitdiv s2 and video_filter s1: their farm tasks (and resume parts) stopped at the 240-min task limit
each time, because a resume redoes the final stack and trim. Each was finished here from the loop state its last farm
part saved (results/<part>/<task>/auto/), with /tmp/bot/scripts/v10loc.sh: the request body's own environment
(flow v10's export line), AUTO_RESUME on that state (AUTO_TRIM_ONLY where the loop had shipped), no time limit.
Per kernel: result.txt (the line the suite table reads), draw_*.txt, task.txt (the source part / task and the head the
run used), log_tail.txt (the loop's final / search / trim lines). The suite table (research/data/fifteen/README.md)
counts these as flow v10 results; digitsum and digitdiv build the same circuit (bdc's frontend rewrites digitsum's
`%` into digitdiv's v - (v / b) * b), hence the same P to the picosecond: their s2 SDFs are identical line for line once the kernel name is masked
(checked 2026-11-21 21:32).
