# Why xorshift x0.375 fails (and x0.5 passes, and x0.25 passes on 2 routes)

Analysis by a subagent (2026-11-05), checked here against muxsel_all.txt and k4 skew.log; nothing re-routed, netlists
regenerated with gen.py (s375 seed 1 byte-identical to the one simulated). Routes: bdc/fusion_bench.py, nextpnr
9c732bc6303458df (the k4 queue's toolchain.sh-checked binary; the fusion_bench toolchain.txt records only versions).

Mechanism: umux3 (the bd_mux driving out0) has its control channel through the 2-stage bd_pipe ulink_n_index_15. With the
pipe EMPTY (start of every call) request and select both launch from stage[0]'s C node: the request goes c0 -> SDELAY (1)
-> c1 -> DELAY (k links) -> uj0/A5 (2953 ps at k=4, every seed: all local hops); the select goes c0 -> latch0 -> latch1
-> s fanout -> uj0/A4 (3438-4106 ps of routed wire, no matched delay, so shrinking does not shorten it). uj0 = C(x_req,
ctl_req & ~s) sees ctl_req while s is still X: out0_req 0 -> X -> 1, the monitor's "req rose out of phase". The data stays
right (only one of x/y present), so it shows only as a protocol error.

DELAY links on ulink_n_index_15: base 10, s50 5, s375 4, s25 3. Link count does not order the outcomes; the ROUTED margin
(req - sel at the worst select pin, muxsel_all.txt) does, on all 16 routes: s50 +558..+1489 (pass), s375 -485..-1153
(fail), s25 seeds 1-2 +214/+564 (pass), s25 seed 3 umux0 -404 (fail: the same class on ulink_n12__0), s25 seed 4 a
different pair (ucmpi0's delay vs the ucond_br3 steer, rule E -82).

Audits: rule E (verify/skew.py) flags exactly this pair on all four s375 routes (-651 raw / -1882 guarded, fix +6..+8 on
ulink_n_index_15) and also fails guarded on all four s50 routes (umux3 -732/-449/-238 guarded; raw positive) -- so s50
passes the full stack with raw select margins of only +0.5..+1.5 ns. tighten.py's bd_mux screen (rule D) gives umux3 +958
ps: it measures from stage[1] only and misses the pipe filling from empty (a blind spot; rule E covers it).

Consequence for item 3: a uniform shrink is limited by the link DELAYs that rule E sized as select-race fixes, not by the
operator delays. Next: shrink operator delays only (udly), keep those link delays.
