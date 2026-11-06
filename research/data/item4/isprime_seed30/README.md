# isprime, route seed 30, FAST_MIN: the fast-mode hang (root cause)

Analysis by a subagent (2026-11-06), checked here (the META line and the fix run). Route: fusion_bench seed 30 of the
rule-E-6 pad sizes, nextpnr 9c732bc6303458df; full stack (netlist from the .bit, prjxray SDF FAST_MIN, GLS_MODEL=fid).

Not a datapath or select race. The C-element of ufork0 (start_ack = C(n0__0_ack, n0__2_ack, p_end_ack), SLICE_X36Y34/
A6LUT) sees its p_end_ack input fall 387 ps after its own output rose (342 ps wire + 45 ps arc) -- before its own
feedback (O6 -> A3: 376 ps wire + 45 ps = 421 ps) has latched the 1. The fid resolver logs it
(sim_meta.log: `runt=387 loop=421 ... -> 1 after 0 ps`) and start_ack shows a zero-width 1->0->1 dip; the fast testbench
(zero-delay environment: it drops start_req and p_end_ack in the same ps as start_ack rises; `end` is a bare wire, so
p_end_req == start_req) completes vector 0 early, raises vector 1's start while start_ack is really still high, and the
start token is lost: hang.

Race: external path (start_ack out -> p_end_ack at A5) minus the C-element's own loop, FAST_MIN: seed 29 +532, 30 -34,
31 +290, 32 +199 ps (guarded 0.772/1.155: 32 ~ -7). The loop is long on 30 and 32 (a routing detour, 376 ps), short (~100)
on 29/31. No audit flags it (rule E 0/86, arb_fork ok; arb_roundtrip.py covers arbiters only).

Fix tested on this route's netlist (sim_fix300.log): +300 ps on that one wire -> all 18 fast vectors PASS. In design
terms: a 2-link delay on the end-channel ack into ufork0 (no BD_SZ knob exists: `end` is a wire), or keep the C-element's
feedback local (placement). Caveat: the external path is this short because the testbench answers in 0 ps; the board
harness's spine latch adds delay, so whether the board would see it is not shown. It is the H_RUNT question in a
shipped kernel: an episode (387 ps) shorter than the loop (421 ps).
