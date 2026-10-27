# Audit: research-branch GLS delay and X semantics (formal shard A claims)

Code under test: `/home/user/wt-research/cells/gls/prims.v` (claude/research @ 19a93c1,
md5 f33de0786dac08cc512adbebde23fad5), used read-only and unmodified. Simulator: Icarus
Verilog 12.0 (stable). It is the only version installed here. All testbenches and
scripts are the auditor's own, in `/home/user/asyncfpga3/audit/gls/`. Shard A's tools
were not run. To reproduce everything, run `/home/user/asyncfpga3/audit/gls/run_all.sh`.

How the research flow applies timing (from `cells/gls/build.sh` and `gen.py`):
- All cell timing is in `specify` paths. The behavioural assigns carry no `#` delay.
- There are two builds:
  - `netlist.v` + `$sdf_annotate` (`tb_gate.v`) is only an acceptance gate. It annotates and then calls `$finish` at t=0.
  - `netlist_baked.v` puts the same numbers in as parameters. It is compiled with `-DGLS_TRANSPORT_IC`, and it is the build `run.sh` actually simulates.
- In both builds, LUT/MUXF7/CARRY4 delays are module-path (specify) delays.
- ICBUF wires behave differently in the two builds: the baked build uses a transport NBA, the annotated build a specify path.

## Verdicts

| # | Claim | Verdict | Evidence |
|---|---|---|---|
| 1a | SLICE_LUTX specify paths are "sample at fire": a change at t schedules an update at t+d that copies the current function value, with no cancellation. An edge that follows an earlier change within d arrives early. | **CONFIRMED** (with one refinement) | `tb_lut_delay.v` with the research LUT as a buffer (O6=A1, arc 124 ps). For a pulse 1000-1120 and a rise at 1130, the log shows `OUT ch0 t=1244 o=1` and nothing else (`lut_baked.out`): the output arrives 114 ps after the 1130 edge, which is exactly the claimed number. For a pulse 1000-1010 and a rise at 1100 it shows `OUT ch8 t=1124 o=1`, only 24 ps after the edge. Random-trace fit (`tb_lut_rand.v` + `fit_delay.py`, 6 traces, 4000 input events each, 3 INITs, equal and unequal per-pin arcs including 516/124/60) gives: **saf_f MATCH 6/6** (8,673 output edges, exact timestamps); transport 0/6; Verilog-style inertial 0/6; saf_pin 3/6. **Refinement:** the trigger is a change of the LUT *function value*, not every pin change. Each such change schedules a fire at t + d(pin that caused it), and that fire copies f at the fire instant (pre-delta: an input change at exactly the fire time is not seen). That matches iverilog's modpath functor, which sits on the internal O6 net. Apparent pin-to-output delay goes down to **1 ps** on a 124 ps arc: 732/1700, 703/1660 and 197/1076 edges were earlier than the arc (`apparent_results.txt`). |
| 1b | It is the same in the SDF-annotated path. | **CONFIRMED** | `tb_lut_delay.v -DANNOT`: parameters are set to 7 and `$sdf_annotate(lut124.sdf)` restores 124. Every edge after t=0 is identical to the baked run (`diff lut_baked.out lut_annot.out` differs only in the t=0 X->0 initialisation, at 7 vs 124). |
| 1c | The annotated and baked builds treat wire pulses differently (LUT-like vs transport). | **CONFIRMED** | `tb_ic_delay.v` with ICBUF D=124. Baked (`-DGLS_TRANSPORT_IC`): every pulse passes as pure transport, for example a 10 ps pulse appears as 3124/3134, and 1000-1120 + 1130 gives 1124/1244/1254. Annotated (specify): identical to the LUT behaviour (1244 only; pulses of 123 ps or less vanish). Impact is low because `tb_gate.v` never simulates past t=0. However, the claims in `prims.v:44` and `build.sh:100` that the two builds were diffed with "every event timestamp identical" cannot hold for any run with a sub-D pulse on a wire, so that statement is stale or wrong. |
| 1d | Depends on iverilog version? | **UNVERIFIED** | Only 12.0 is installed (`iverilog_version.txt`). The `prims.v` header says the research flow targeted iverilog 11. Not tested. |
| 2 | "GLS with inertial LUT paths cannot show a LUT runt" (isolated pulses shorter than the arc are filtered). | **CONFIRMED for isolated pulses; false in general** (as shard A's own JOURNAL 03:20 correction says) | Isolated pulses of 10, 60, 100 and 123 ps produce no output. 124 ps passes (3124-3248) and 200 ps passes (`lut_baked.out` ch1-ch6). A train of two 50 ps pulses separated by 50 ps (9000-9050, 9100-9150) produces **one 50 ps output runt, 9124-9174** (ch10). Neither transport (two pulses) nor inertial (none) behaves this way. So the GLS can show a runt, but not a faithful one. Also, the paths are not "inertial" in the Verilog sense: they fit 0/6 traces against the inertial model. |
| 3 | SLICE_LUTX builds the mux tree with A6 at the leaves, while silicon has A6 at the root (UG474). | **CONFIRMED** (structural), **no observable GLS effect** | In `prims.v:83` the first select on raw INIT is `s5 = A6 ? INIT[63:32] : INIT[31:0]` and A1 is the last (`prims.v:88`, `O6 = A1 ? ...`). In UG474, a LUT6 is two LUT5s on A1-A5 muxed by A6, so A6 is the output (root) select. The internal model nets have zero delay, so tree order affects neither GLS timing (only the specify arcs do) nor X values (claim 4). It matters only for a physical hazard model, which this GLS does not have. |
| 4 | X-propagation of the GLS LUT/MUXF7 models equals Kleene evaluation. | **CONFIRMED** on all vectors tested | `kleene_check.py` + `tb_kleene.v` compares against an independent brute-force Kleene evaluator. It uses 6 INITs (including 0x00E800E800E800E8, XOR6, CAFEF00DDEADBEEF) x 2000 random vectors, with X density 0.1, 0.3 or 0.6 on A1..A6 and on SELMUX2_1 D0/D1/S0, checking O5, O6 and MUX: **36,000 comparisons, 0 mismatches** (`kleene_results.txt`). Z inputs were not tested. |
| 5 | Impact: the early edge can make a bundled-data margin look larger than true. | **CONFIRMED** with a concrete example | `tb_impact.v`: an XOR3 LUT (arc 124 ps). Its inputs change at 1000, 1040 and 1100 (f: 0->1->0->1, final 1). The research LUT shows one edge, at **1124** (`impact_1200.log`). A transport reference settles at **1224** (1124 up, 1164 down, 1224 up), and a Verilog inertial reference also settles at 1224. The data has really settled only 124 ps after its last input change (1100), so the GLS reports it **100 ps early**. A research SLICE_FFX capture edge at any TCAP in 1170-1223 reads the correct 1 in the GLS but 0 under both reference models (`impact_sweep.log`, for example `TCAP=1200 captured: gls=1 transport=0 inertial=0`). A request arriving at 1200 therefore looks like a +76 ps margin in GLS when it is really -24 ps. The bound is at most one arc per glitching LUT, and it compounds along a cone. How often this happens in the routed gcd_hw was not measured (out of scope). |

## Notes
- The shard's wording "a change at t schedules ..." is accurate if "change" means a change of the LUT's
  function output. A pin change that leaves f unchanged schedules nothing: the saf_pin model
  mismatches on majority (0xE8) and 0x6A traces.
- "Sample at fire" never invents a wrong *final* value for a cone that goes quiet. The error is in
  *when* the value settles (too early), plus distorted or merged intermediate pulses (claim 2, ch10).
  That is the unsafe direction for bundled-data margins.
- Files (all in `/home/user/asyncfpga3/audit/gls/`): `tb_lut_delay.v`, `lut124.sdf`, `tb_ic_delay.v`,
  `ic124.sdf`, `tb_lut_rand.v`, `fit_delay.py`, `apparent.py`, `tb_kleene.v`, `kleene_check.py`,
  `tb_impact.v`, `run_all.sh`, and logs `*.log`, `*.out` and `*_results.txt`.
