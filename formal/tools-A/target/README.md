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
| `out/` | committed outputs |

Results 2026-11-01 (target 03e82630, decoded net md5 7c41591d after the 23-arc widening of 08:10, 200097 nodes, 199736 gates;
kernel cone 170254 gates; vec16 was run on the net before the widening, md5 99b3ab4a; the others were rerun after it, same results):
- `out/vec16_sequential.txt`: all 16 vectors correct (sequential env, corner 0.5, mid-band).
- `out/cex_pipelined_reorder.txt`: pipelined env, (2^19, 2^19) then (3, 5): out0 = [1, 524288]. Same at c = 0 fast
  end, c = 1 slow end, and ±10% / ±20% scatter (formal/FOR-RESEARCH.md item 2).
- `out/cex_early_release.txt`: data released when req falls (acks still high): no output (livelock).
- `out/ok_broad_sequential.txt`: data released at each ack's fall: [6, 1] correct.
