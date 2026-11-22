# Flow v10 tasks finished locally (2026-11-21)

digitsum s2, digitdiv s2 and video_filter s1: their farm tasks (and resume parts) stopped at the 240-min task limit
each time, because a resume redoes the final stack and trim. Each was finished here from the loop state its last farm
part saved (results/<part>/<task>/auto/), with /tmp/bot/scripts/v10loc.sh: the request body's own environment
(flow v10's export line), AUTO_RESUME on that state (AUTO_TRIM_ONLY where the loop had shipped), no time limit.
Per kernel: result.txt (the line the suite table reads), draw_*.txt, task.txt (the source part / task and the head the
run used), log_tail.txt (the loop's final / search / trim lines). The suite table (research/data/fifteen/README.md)
counts these as flow v10 results; digitsum and digitdiv build the same circuit (bdc's frontend rewrites digitsum's
`%` into digitdiv's v - (v / b) * b), hence the same P to the picosecond: their s2 SDFs are identical line for line once the kernel name is masked
(checked 2026-11-21 21:30).

Added 2026-11-22 (auditor T180: the local runs' logs were only in /tmp): per kernel `benchres_*.txt` (each draw's
BENCHRES lines: operands, results, latencies), `exp.txt` (the C's expected values; video_filter's arrays in
`memexp.txt`), `draws.txt`, `suite_auto.log`, and `loop/` (the sizing loop's full log, result line, every iteration's
lane2 line and seed, the shipped iteration's sizes and trim record). With them a draw's answers can be re-checked against
an oracle of one's own, and the shipped route rebuilt from its sizes / seed / trims.
