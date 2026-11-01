# FOR-RESEARCH C1 on BQ#1's board-fidelity stack (2026-11-01)

formal's `formal/tools/pipe/gls/tb_pipe.v` (claude/formal, used read-only from a scratch copy; its hard-coded
`IN_ACK dut.n144588` replaced by `urig.in_ack`'s wire from this route's nets.map) on the netlist decoded from the
COMMITTED `research/board/gcd_hw_03e82630.bit` (fasm2net; fasm_equiv EQUIVALENT), with the prjxray SDF of the same
route (nextpnr sdf 6f8b99e6, bq1 seed d) and GLS_MODEL=fid, compiled with -DGLS_TRANSPORT_IC -DGLS_FID.
Provenance in `{max,min}_provenance.txt`; one log per run, filtered to the testbench's own lines.

| run | SLOW_MAX | FAST_MIN | formal's prediction |
|---|---|---|---|
| PIPE=0 9 then 4 (sequential control) | LAP1 ok (4096), LAP2 ok (1) | same | both right |
| PIPE=1 9 then 4 | only LAP1 = 1 (pair 2's); 4096 never | same | reorder (1 first) |
| PIPE=1 9 then 9 | no result | same | deadlock |
| PIPE=1 15 then 5 | both accepted, no result | same | deadlock |
| PIPE=1 2 then 4 | only LAP1 = pair 1's; pair 2's never | same | pair 2 never |
| rig env (tb_run, vec 6, 150 us) | 16 laps, 0 err | (not run) | - |

Vector 9 sequential, SLOW_MAX: request 697.5 ns, in_ack rises 928.1 ns, result 3789.0 ns; FAST_MIN: in_ack falls
400.0 ns, result 1398.3 ns. The input handshake completes long before the result (gcd_rig.v's header is wrong);
the board rig is safe only because its env waits for out0.
