# T93 — independent static rule-E check at `bridge_i.udut.ucond_br6`

Auditor's own code. It reads only the already-generated gate-level netlists. It does not run the project's
tighten.py, skew.py or corner_audit.py, it does not run vvp, and it does not use git. It writes nothing outside this directory.

| file | what |
|---|---|
| `sta_lib.py` | parses `netlist_baked.v` and builds the timing graph. Also parses `annot.sdf`, `names.map` and `nets.map` |
| `rule_e.py` | the rule-E check for one launch link, both steer LUTs. `--bits N` restricts the counter range, `--transparent L` treats a downstream link as transparent, `--plant ic:ps` adds delay to an ICBUF |
| `run_all.py` | runs every check, plus the planted-error tests on a modified **copy** of the netlist. Writes the two files below |
| `results.txt` / `results.json` | all numbers, the critical paths and the cone listings |

Re-run with `python3 run_all.py`. It takes about 30 s and peaks at about 130 MB.

## Method

**Graph.** The graph follows `cells/gls/prims.v` and `fid_core.vh` (the GLS_FID model the gate-level sim runs). Arc delays are the baked instance parameters. I checked them against `annot.sdf`: 60 810 arcs, every one matches except the BUFG.

- **ICBUF:** one arc of `D`.
- **SLICE_LUTX:** an arc `Ak->O6/O5` (`TAkO6/TAkO5`) only for pins in the function's support.
  - The support is computed from INIT with constant pins fixed. Constants are PSEUDO_GND/VCC, propagated through ICBUFs and constant LUTs.
  - An early version without constant fixing put a false `q[0]->O6` arc through a latch LUT6_2 (via its A6=1 half). That inflated s by about 340 ps. It is fixed.
- **CARRY4:** every arc in the prims.v specify list: `CIN/CYINIT/DIi/Si -> COj/Oj`.
  - The delay is the baked `T<pin><out>` when present. Otherwise it is the prims.v default, which is what the simulator uses. annot.sdf has no DI or CYINIT arcs, so `DI->CO` is 100 ps in the sim and here.
  - An arc is dropped only if a constant S pin blocks it.
  - Otherwise the full-length carry through every CARRY4 is assumed possible. This is a static check.
- **SELMUX2_1:** `D0/D1/S0 -> OUT`.
- **Cut points:** FF, LATX, PS7, IOB and BUFG have no combinational arcs. A LUT with a feedback pin (`FB6`/`FB5` set) is a **state node** (C-element, latch, arbiter). Its feedback arc is never traversed. Its other arcs are cut unless the check explicitly allows that state node (below).

**Mapping.** Logical cell → `NEXTPNR_BEL` (nextpnr's routed JSON `/root/t65/l{5,3}_1/xorshift_bench_gen_routed.json`) → `names.map` → `c_NNNNNN`.
- The work-dir `routed.json` is the fasm-derived one and has site names, so it cannot be used for this.
- Each steer's req/s pins are found as in `t83/mon_steer.py`: the pin whose ICBUF source net carries `ucond_br6_req`, and the other non-constant pin.
- Both fractured halves are checked:
  - `u$LUT6` (req1): req=A3, s=A4 on A; req=A3, s=A5 on B.
  - `u$LUT5` (req0): same pin numbers.
- I verified the pin sources by logical net name:
  - A: `ucond_br6_j` inputs are `n31_req` (= n32__3) and `n29_req` (= n30__0); the steer's s is `n31_data`.
  - B: the same nets.

**Launch points (transparent latches handled explicitly).** The common launch event is the output of the launching link's C node, `<link>.ctl.u.u`. In `bd_link`, that one node drives both the latch enable and `rdly -> req_out` (bd_link.v). On the A RTL, `ulink_n7` is the storage link feeding `uaddi0` (n7_req/n7_data). On B, `ulink_n30__1` is inserted between the `ufork8` output n30__1 and `ucmpi1` (diff of the two kernel .v files).

- **s side.**
  - From the C node, the check may enter **only the launching link's latch LUTs** (`<link>.lat.*`), by their en pin. Their d pin is not caused by this launch: the bundling at that latch's input is the upstream sender's obligation. Every other latch or C-element is a cut.
  - The cone is then max-delay over every path to the s pin.
  - A cone: the 32 `ulink_n7` latch LUTs, the uaddi0 adder (8 CARRY4 slices plus LUTs), the ucmpi1 compare (3 CARRY4 plus LUTs), and `uz_n38`.
  - B cone: the 32 `ulink_n30__1` latch LUTs, the compare, and `uz_n38`.
- **req side ("earliest rise", a lower bound).** From the same C node, the only state nodes traversed are the join C-elements on the request path (`uaddi0.ujoin`, which is a wire for N=1, `ucmpi1.ujoin` and `ucond_br6_j`).
  - Every net in the cone is assumed to rise 0→1 once.
  - Cone-external inputs are free but stable: `ctrl_rst`, and `n11__1_req` at ucmpi1's join.
  - C-element feedback is held at 0.
  - A LUT's output rises at the earliest time its function, on per-pin-delayed inputs, can be 1. So the delay-chain AND taps (`bd_delay_gated` g[i≥1] = s[i]&gate) and the C-elements wait for their **last** launch-derived input. A plain OR would take its first.
  - The req cone is exactly: uaddi0.uor, uaddi0.udly g[0..5], ucmpi1.ujoin, ucmpi1.uor, ucmpi1.udly g[0..8] and ucond_br6_j. On B (combined check) it is also ulink_n30__1.ctl and rdly g[0..3].
- **Margin** = min req rise at the req pin − max s arrival at the s pin. Both are measured at the LUT's own pins after the interconnect ICBUF, the same place the t83 monitor measures. The margin is raw, with no guardband.
- **Counter restriction (`--bits N`).** The analysis takes the uaddi0 slices at index ≥ ceil(N/4) and the launching latch bits ≥ N as not toggling. This is valid if the loop counter stays below 2^N, so that i+1 never carries into bit N.
  - It is slice-granular, so N=11 and N=12 give the same cone (slice 2 is kept whole). This is pessimistic.
  - The adder slices were found by logical name (`uaddi0.$auto$alumacc...slice[k].carry4`) and by CIN→CO3 chaining. Latch bits come from the logical net `n7_data[j]` / `n30__1_data[j]` each latch LUT drives.

## Results (ps; LUT6 and LUT5 halves give identical numbers in every row)

"worst" is `work_*_long2_worst`. Its annot.sdf uses the xray band column: delay chains band 0.21, CARRY4/F7F8/FF band 1, the rest 0.288, plus scatter. "fastmin" is `work_*_long_fastmin`: the xray min column, no scatter.

| check | corner | max s | min req | **margin, full 32-bit** | **margin, counter < 2^12** (= < 2^11) |
|---|---|---|---|---|---|
| **A**: launch ulink_n7 (adder + compare) | worst | 6773 | 8360 | **+1587** | **+2017** |
| **A** | fastmin | 4078 | 6027 | **+1949** | **+2191** |
| **B**: launch ulink_n30__1 (compare only) | worst | 5341 | 6294 | **+953** | +953 |
| **B** | fastmin | 3429 | 4701 | **+1272** | +1272 |
| **B combined**: launch ulink_n7, ulink_n30__1 latch transparent (d→q traversed) | worst | 9072 | 10094 | +1022 | +1713 |
| **B combined** | fastmin | 5764 | 7595 | +1831 | +2223 |
| A, other operand: launch ulink_n11__1 | worst / fastmin | 4526 / 2896 | 7345 / 5336 | +2819 / +2440 | same |
| B, other operand: launch ulink_n11__1 | worst / fastmin | 5252 / 3425 | 7424 / 5494 | +2172 / +2069 | same |

Critical paths, A at the worst corner (full listing in `results.json`):

- **s, full carry.** The path is:
  1. `ulink_n7.lat.pair[0]` (q0) at 996.
  2. The adder S0 into slice 0, then CIN→CO3 through slices 1–5, then slice 6 O3 at 3035.
  3. The compare: slice 2 S1→CO2 at 5003, then `uz_n38` at 6138.
  4. The ICBUF to s, arriving at 6773.
- **s, counter < 2^12.** Slice 0, then slice 1 O0 at 2434, then the full compare carry (slices 0→2) to `uz_n38` at 5708. s arrives at 6343.
- **req.** C node → uaddi0 uor and 6 chain elements (2605) → ucmpi1.ujoin (3177) → uor and 9 chain elements (7242) → `ucond_br6_j`. That C-element's inputs arrive at 7666 (n31_req) and 2992 (n29_req), so it waits for 7666. req reaches the steer pin at 8360.

## Comparison with the research claim — NOT reproduced

- **Research says A fails at the worst corner by −3.2 ns (−4.65 ns nominal).** This static check gives A **+1.59 ns** with a full 32-bit carry at the worst corner and +1.95 ns at fastmin. I had no nominal-SDF work dir, so the −4.65 figure is unchecked.
- **Why A passes here.** In A, the uaddi0 matched delay (6 elements) is **in series** on the request path. It runs C node → n29_req → ufork8 → n30__1_req → ucmpi1.ujoin. The steer's req (`ucond_br6_j`, a `bd_c2` C-element) cannot rise until n31_req (n32__3, after the ucmpi1 chain) has risen. So the adder is covered by uaddi0's chain and the compare by ucmpi1's.
- **Diagnostics that reproduce numbers of the claimed size.** Both are false paths. They are printed by `rule_e.py` as `[diag]` and stored in `results.json`.
  - *OR-join:* `ucond_br6_j` treated as rising on its **first** input. That input is n29_req = n30__0, which arrives after the uaddi0 chain only, without waiting for the compare chain. This gives A worst **−3087** and A fastmin −1352. That is within about 0.1 ns of the claimed −3.2 ns. In B the same diagnostic stays at +953 (worst), because n30__0 there belongs to the earlier ulink_n7 event. So this pairing would also reproduce the claimed **sign pattern** (A fails, B passes). I cannot see the research's method, so this is a hypothesis, not a finding. It is consistent with tighten.py's own docstring for its select rule, which calls that rule "a SCREEN, not a measurement… it cannot see matched delay already in the request path".
  - *Plain shortest path,* ignoring AND/C semantics (the side taps of `bd_delay_gated`): A worst −5082.
- **Research's B +1.70 ns.** The closest number here is B combined, < 2^12, worst: +1713. The plain B check gives +953 at worst and +1272 at fastmin. I cannot tell which of these, if any, the research computed.

## Sanity checks

- **(a) Direction A vs B. FAILS against the research's claim.**
  - Research: B is better than A (A fails, B +1.70).
  - Here A has *more* margin than B on every comparable pairing:
    - full, worst: A +1587 vs B +953 (combined +1022);
    - < 2^12, worst: A +2017 vs B +953 (combined +1713).
  - My reading: inserting `ulink_n30__1` removes the adder from the s cone, but it also removes uaddi0's chain from the req path. The remaining compare-vs-ucmpi1-chain margin is the smaller one. Only the false-path OR-join diagnostic reproduces "A < 0 < B".
- **(b) Static vs the dynamic monitor.**
  - Static, A worst, counter < 2^11/2^12: **+2017 ps**.
  - Auditor's dynamic minimum (t83 monitor, A worst, longest exit carry 11 bits): +2040 ps.
  - Static ≤ dynamic, as it must be, by 23 ps. That pessimism is small. One plausible reason it is so small: the compare's carry chain (ucmpi1 slices 0→2), which dominates the < 2^12 path, is exercised in full by ordinary counter values. Nothing points to a missing path, but this cannot prove there is none.
  - The full 32-bit static margin (+1587) is below the dynamic figure, as expected.
- **(c) Planted error.** `run_all.py` adds 2000 ps to one ICBUF's `D` in a **copy** of `netlist_baked.v`. It reruns the whole flow, from the text parse onward. Base margins: full +1587, < 2^12 +2017.

| ICBUF | where | full margin | < 2^12 margin |
|---|---|---|---|
| ic_012664 | into the LUT6 s pin | LUT6 −413 (Δ −2000); LUT5 unchanged | LUT6 +17 (Δ −2000); LUT5 unchanged |
| ic_016575 | adder slice 0, on every critical s path | −413 (Δ −2000) | +17 (Δ −2000) |
| ic_019377 | upper adder slice, full-carry path only | −413 (Δ −2000) | +2017 (Δ 0, correctly outside the < 2^12 cone) |
| ic_022049 | inside the ucmpi1 request chain | +3587 (Δ +2000) | +4017 (Δ +2000) |

## Assumptions and limitations (read before using any number)

1. **Delay model.** The model is the simulator's: the baked arcs, prims.v defaults for missing CARRY4 arcs (DI→CO/O = 100 ps, never characterised in the SDF), FID_LEVEL_PS = 0, and no metastability resolution delay. It is not silicon. "worst" is the band-column corner described above, not a signed-off STA corner. No nominal-SDF dir was available.
2. **The launch latch's d pin is not part of this event.** Bundling at `ulink_n7`'s input (umux0 → ulink_n7) is assumed met. If it is not, s can move later than computed.
3. **B's plain check (launch ulink_n30__1) assumes the adder output is stable at that latch's d before its en rises.** It is not, statically. In the combined check the last full-carry d change reaches `ulink_n30__1.lat.pair[28]` at about 5073 ps, while that link's C node has already risen at about 3800 ps. So the latch is transparent to the late carry. The "B combined" rows trace exactly that, through d→q. Treat combined as the honest B number: +1022 full, +1713 < 2^12 at worst.
4. **Request side.**
   - The req-side bound assumes 4-phase return-to-zero: every launch-derived request net starts low, each C-element starts low, and the delay chains are flushed by their gate. It also assumes the C-elements behave as C-elements, with no runt or metastable output.
   - Free inputs (rst, n11__1_req) are chosen to make req as **early** as possible.
   - If any of the 4-phase assumptions is violated (for example an incompletely flushed FASTFALL chain, the project's rule F), req can be earlier than computed. That is not covered here.
5. **One launch event at a time.**
   - The other compare operand (`ulink_n11__1`) is checked as its own launch (+2.8 / +2.2 ns).
   - Interleavings in which the n7 and n11__1 events overlap are not modelled beyond each one's own bound.
   - Changes of s outside the req-high window (rule E's hold half: s must not move while req=1) are **not** checked.
6. **The counter restriction is slice-granular.**
   - "< 2^11" and "< 2^12" are the same cone.
   - It assumes i+1 never carries into bit N. If i reaches 2^N − 1 with a 12-bit mask, bit 12 of i+1 does toggle.
   - The masked bench's exact range was not verified by me.
7. **Request-path cells are chosen by name.** The req-path state nodes are an explicit name allow-list (`REQ_STATE` in rule_e.py, plus `--transparent`), checked against the kernel RTL. A different design would need the list reviewed. The combinational cells in both cones are found from the netlist alone. Each cone was checked to be acyclic: the script aborts on a cycle, and none occurred.
8. **Only `ucond_br6` is checked.** No other steer or mux select is checked.

## Confidence

- **High** that, under the simulator's own delay model and the 4-phase assumptions above, rule E at `ucond_br6` holds statically on A at both available corners: +1.59 ns full carry and +2.02 ns for a 12-bit counter at worst. This is supported by:
  - the exact SDF/param cross-check;
  - the planted-error tests;
  - the 23 ps agreement with the dynamic +2.04 ns.
- **High** that the claimed A failure is not a property of the routed netlist under these assumptions.
- **Medium** that it comes from pairing s with the join's n30__0 input (the OR-join diagnostic matches −3.2 ns to about 0.1 ns). I have not seen the research's method.
- **Low** on which B number the research's +1.70 ns corresponds to.
