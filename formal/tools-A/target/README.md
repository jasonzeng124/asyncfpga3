# tools-A/target: the target bitstream's netlist, decoded (untrusted), and a simulator over it

Shard A, THE goal (formal/PROGRAM.md). Everything here is UNTRUSTED code. Its outputs are evidence, not proof, until
the Lean round trip and checker take them.

| file | what |
|---|---|
| `decode_base.py` | shard C's `fasm2lean3.py` (copied 2026-11-01, read-only use), plus the route of every walked pin, pip by pip |
| `build_net.py` | the gate list of `Formal.Target.Spec`: pips, LUT O6/O5, MUXF7/F8, CARRY4 outputs (one gate each over its pins), output-mux hops, constants; prjxray arcs per pin; FFs/BUFG/BSCAN get no gate (free outputs) |
| `roundtrip.py` | Python mirror of the round trip: re-encode the gates as FASM features and compare with the read-back FASM |
| `boundary.py` | the kernel boundary as decoded node names (via yosys + nextpnr names; checkable) |
| `sim.py` | event-driven simulation of the decoded netlist: fixed delay per pin arc inside its band (transport), the Spec's environment (sequential or pipelined; data released early, broad, at rtz, or at the next request) |
| `run_vec16.sh` | the 16 gcd_rig.v vectors, one per run |
| `make_net.sh` | the pipeline from `formal/target/` |
| `make_net_fasm.sh` | any routed build's FASM -> `d0.json`, `net.json`, round trip (2026-11-15; for research's bench builds and C's margin tool) |
| `out/` | committed outputs |

Results 2026-11-01 (target 03e82630, decoded net md5 7c41591d after the 23-arc widening of 08:10, 200097 nodes, 199736 gates;
kernel cone 170254 gates; every result below rerun on this net):
- `out/vec16_sequential.txt`: all 16 vectors correct (sequential env, corner 0.5, mid-band).
- `out/cex_pipelined_reorder.txt`: pipelined env, (2^19, 2^19) then (3, 5): out0 = [1, 524288]. Same at c = 0 fast
  end, c = 1 slow end, and ±10% / ±20% scatter (formal/FOR-RESEARCH.md item 2).
- `out/cex_early_release.txt`: data released when req falls (acks still high): no output (livelock).
- `out/ok_broad_sequential.txt`: data released at each ack's fall: [6, 1] correct.

2026-11-15 (A): the decoder now accepts LATCH-mode slices (LDCE/LDPE, opaque storage like the FFs; research's bench
builds have two, gen_bench.py's i_ack_latched / o_req_latched) and an OUTMUX select onto any unread xMUX pin. On
gcd_ps_e6bb4aec its output is byte-identical to before. research's three delivered builds (FOR-FORMAL.md) decode, each
in ~20 s, round trip "invented 0", leftovers only storage/IO/clock configuration:
| build | fasm md5 | net.json md5 | gates (pip/hop/lut6/lut5/const/muxf/carry) | opaque |
|---|---|---|---|---|
| item25_collatz_s24 | c6404633c7d2b095a7ff4e7233a11b72 | eb3d24373ae8c5994589f9298ef40dab | 128,226 (111,270/6,100/4,433/4,433/1,079/271/640) | 1,928 |
| item23_xorshift_s10 | 56434fc43a066c25c397e8f7e4b9d1ea | d2f11df7d95e6219237f3a299de05bb8 | 130,108 | 1,920 |
| BAD_xf2_1 | f2873d4650eb67cb270ada5c9a403421 | 65fb975783eae633b49be98c1317685c | 128,040 | 1,920 |
**Bench boundary (2026-11-15, `boundary_bench.py`):** kernel ports from the DUT module header, bench nets from the
`udut (...)` port map, decoded nodes via nextpnr's BEL of each net's driver (falling back to the yosys driver cell's
name when nextpnr dropped the net name). Needs the build's yosys JSON and routed JSON, which research has not
committed; A rebuilt item 25 from FOR-FORMAL.md's command (scratch worktree of origin/claude/research f6c37b63,
cells/verify/toolchain.sh OK, nextpnr 9c732bc6303458df): SDF md5 e001dc27e644e10a14d08a7730daa958 and FASM md5
c6404633c7d2b095a7ff4e7233a11b72, both byte-identical to research's. Result: `out/item25_collatz_s24_boundary.json`
(rst SLICE_X10Y37.CQ; shared request n_req = start_req = end request = SLICE_X9Y41.DQ, the bench's req_core flop;
n_ack SLICE_X17Y32.A6; start_ack SLICE_X16Y31.D6; out0_req SLICE_X14Y38.A6; out0_ack SLICE_X6Y43.A6 (bench LUT);
p_end_ack SLICE_X17Y31.D6; n_data / out0_data 32 distinct nodes each). Untrusted naming.

## Margin helpers (shard A, 2026-11-16; untrusted analysis, on top of shard C's formal/tools/margin)
- `selrace.py NET BND OUT [--depth 1]` / `selrun.sh OUT/` (after `formal/tools/margin/run.sh BUILD OUT/`): the races C's
  candidate list leaves out, late inputs of combinational LUTs that feed storage (a select reaching a mux's data LUT
  late is one); C's rank.py, margin.py, checkrows.py and names.py unchanged; results in OUT/sel/.
- `race_ps.py NET DUMP Q PIN CORNER [--mode M|F|S] [--other PINS]`: one race in picoseconds. DUMP = simx --dump of a
  run with no slow class at kappa 0 (every delay known); pairs each arrival at PIN with the next arrival at the
  other (data) pins, traces both back to their split, and prints each path's cells and routing apart. A data path
  that starts at the environment (an input bus driven by the simulated env) is reported as such.
- `decode_base.py`: a flop placed with no D-mux bit (nextpnr FASM gap; research's ffmux_scan.py) decodes with D
  undefined and a warning (listed under "undefined_ff_d").
