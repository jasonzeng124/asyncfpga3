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

## All sites (sites.py)

Added after the ucond_br6 check above; nothing above this heading was changed. `python3 sites.py` (about 22 s, peak about 290 MB) writes `sites_results.txt` (one row per design, gate, launch and corner, then the summary and sanity checks) and `sites_results.json` (the same rows with critical paths, crossed C-elements and per-node notes). It reuses `sta_lib.py`, and its engine is `rule_e.py`'s code with the generalisations below. The research numbers are read as text from `research_skew_l{5,3}_1.txt`. `skew.py` was read but never run.

### Method changes relative to rule_e.py

- **Sites.** These are taken from the research output: 12 sites per design, 24 gates per design, 48 gates in all.
  - Each bd_steer is checked on both fractured halves, `u$LUT6` and `u$LUT5`.
  - Each bd_mux is checked on both joins, `uj0` and `uj1`.
    - The req pin is the one that carries the mux's `ctl_req`. The s pin is the one that carries its `s`.
    - Both are read from the kernel RTL. The pins are then found by logical net name through `nets.map`, with `assign` aliases resolved (for example `n32__3_data` = `n31_data`).
  - On all 48 gates, the pins found by net name are the same as research's pins.
- **Launches.** These are found from the netlist, not from a list of names.
  - *Direct:* every link whose latch LUTs reach the s pin through combinational logic only. Research's launch is always one of them.
    - ucond_br6–9 on A have two: `ulink_n7` and `ulink_n11__1`.
    - On B they are `ulink_n30__1` and `ulink_n11__1`.
  - *Upstream (depth 1 and 2):* for a direct launch X, every link Y whose latches drive X's latch d pins. It is checked as launch Y with X **transparent**.
    - Why this is needed: a Muller `bd_link` latch is transparent while its node is high (bd_link.v, bd_latch.v). So a d change that arrives after X's node has risen goes straight through to s inside the same transaction.
    - This generalises the old "B combined" check. It covers umux0 → ulink_n7, umux2 → ulink_n11__1, uaddi0 → ulink_n30__1, the internal stages of each pipe, and ucontrol_merge0_olink → ulink_n12__*.
    - Upstream sources that are not latches are listed in the NOTES and not launched:
      - the rounds FFs outside udut that feed `ulink_n1__1`, which are constant during a run;
      - the arbiter state, its ack C-elements and `ucond_br9`'s req0, which feed the two control-merge index latches. That is the merge's own bundling obligation.
- **Request side.** The req side may cross every request rendezvous C-element: fused-op `ujoin`, cond_br `_j`, and other muxes' `uj0`/`uj1`. It may also cross the C node of each transparent link.
  - A state LUT is entered only through a pin whose 0→1 change can raise its output from 0, with feedback held at 0.
  - So a link controller C(req_in, ~c_next) is entered only by req_in. A rising downstream ack only makes the node fall, which starts no forward wave.
  - Before this rule, ack paths closed false cycles.
- **Select side.**
  - The launch link's latches are entered **only through their en pin**. rule_e.py stated this but did not enforce it; with upstream launches it matters, because the counter loop closes through the launch latch's d.
  - Transparent latches are traversed d→q and en→q, and a transparent link's C node is traversed through its req_in. This adds the en path, which rule_e.py's `--transparent` mode left out.
  - bd_steer gate LUTs are never traversed on the select side, because they make requests, not data.
- **OR-join diagnostic.** Every C-element crossed on the request path rises on its **first** derived input. The delay-chain AND taps are still respected. This is research's semantics: its `walk()` seeds a crossed storage node with its best input and prunes the FASTFALL side arcs. For ucond_br6 on A it is identical to rule_e.py's single-join version.
- **Counter restriction (< 2^12).**
  - This is rule_e.py's slice-granular rule, applied wherever the select cone contains uaddi0's CARRY4s.
  - The latch-bit exclusion is extended to every allowed latch (launch or transparent) whose output is a bit of a counter net (n7, n6, n_trueResult_6, n29, n30__*).
- **Research's guard.** `0.772*req − 1.155*sel` comes from research's own header and reproduces its printed guarded numbers exactly. It is also applied to our numbers, as information only. The worst corner here is already a derated SDF, so guarding it counts the derating twice.

### Summary (ps, raw; the minimum over both gates of a site and over every launch; full rows in sites_results.txt)

| site | research raw / guarded (its launch, nextpnr SDF) | own worst | own fastmin | own, research launch, worst | **OR-join, research launch, worst / fastmin** | own < 2^12, worst |
|---|---|---|---|---|---|---|
| A ucond_br2 | +2997 / +200 | +2521 | +2448 | +2521 | +2521 / +2448 | = |
| A ucond_br3 | +4566 / +1708 | +3304 | +3026 | +3304 | +3304 / +3026 | = |
| A ucond_br4 | +3988 / +1151 | +3136 | +2910 | +3136 | +3136 / +2910 | = |
| A ucond_br5 | +2783 / +8 | +2512 | +2421 | +2512 | +2512 / +2421 | = |
| **A ucond_br6** | **−4651 / −7126 VIOL** | +1519 | +1918 | +1587 | **−3087 / −1352** | +1949 |
| A ucond_br7 | +1619 / −2079 VIOL | +1614 | +2004 | +1682 | +1682 / +2035 | +2044 |
| A ucond_br8 | +1722 / −1996 VIOL | +1677 | +2059 | +1745 | +1745 / +2090 | +2107 |
| A ucond_br9 | +617 / −3036 VIOL | +1464 | +1860 | +1532 | +1532 / +1891 | +1894 |
| A umux0 | +2509 / +1663 | +1970 | +1480 | +1970 | +1970 / +1480 | = |
| A umux1 | +3620 / +2521 | +2739 | +1970 | +2739 | +2739 / +1970 | = |
| A umux2 | +2941 / +1996 | +2217 | +1563 | +2217 | +2217 / +1563 | = |
| A umux3 | +1955 / +1235 | +1764 | +1213 | +1796 | +1796 / +1215 | = |
| B ucond_br2 | +2797 / −15 VIOL | +2261 | +1963 | +2261 | +2261 / +1963 | = |
| B ucond_br3 | +4473 / +1595 | +3213 | +2670 | +3213 | +3213 / +2670 | = |
| B ucond_br4 | +3355 / +600 | +2717 | +2299 | +2717 | +2717 / +2299 | = |
| B ucond_br5 | +2662 / −69 VIOL | +2296 | +1978 | +2296 | +2296 / +1978 | = |
| B ucond_br6 | +1699 / −1299 VIOL | +754 | +1137 | +953 | +953 / +1272 | +754 |
| B ucond_br7 | +2566 / −478 VIOL | +1438 | +1620 | +1637 | +1637 / +1755 | +1438 |
| B ucond_br8 | +2137 / −902 VIOL | +1087 | +1400 | +1286 | +1286 / +1535 | +1087 |
| B ucond_br9 | +1896 / −1193 VIOL | +985 | +1286 | +1184 | +1184 / +1421 | +985 |
| B umux0 | +1742 / +989 | +1111 | +904 | +1111 | +1111 / +904 | = |
| B umux1 | +3504 / +2431 | +2999 | +2177 | +2999 | +2999 / +2177 | = |
| B umux2 | +2879 / +1813 | +2165 | +1622 | +2165 | +2165 / +1622 | = |
| B umux3 | +2651 / +1773 | +1680 | +1243 | +1680 | +1680 / +1243 | = |

**Binding launches.** The binding launch, where it is not research's, is always an upstream one:

- A ucond_br6–9: `ulink_n12__0` with `ulink_n7` transparent. The umux0 select reaches s through the mux data and the transparent ulink_n7. This is 68 ps below the direct `ulink_n7` number.
- B ucond_br6–9: `ulink_n12__0` with `ulink_n7` and `ulink_n30__1` transparent. This is 199 ps below the direct `ulink_n30__1` number.
- A umux3: `ulink_n_index_15` stage[0] with stage[1] transparent, at −32 ps.

**Counts.**

- 24 sites, 48 gates and 520 rows. Every row has a result. No cycle was hit and no row lacked a request path.
- **Own model:**
  - **0 sites are negative at either corner, under any launch.**
  - The smallest margins are B ucond_br6 at +754 (worst) and A umux3 at +1213 (fastmin).
- **Research's flags:**
  - Research raw-negative: 1 site, A ucond_br6. **It is negative only because of OR-join semantics:** own +1587/+1949 against OR-join −3087/−1352 at research's launch, at worst/fastmin.
  - Research guarded-VIOLATED: 10 sites. These are A ucond_br6–9 and B ucond_br2, br5 and br6–9.
  - Of the other 9, none is negative raw under either own or OR-join semantics at either corner. Under raw margins:
    - OR-join only: 1 (A ucond_br6).
    - Both own and OR-join: 0.
    - Neither: 9.
- **Guarded view.** This is research's guard applied to our numbers at research's launch.
  - B ucond_br2 and br5 stay ≥ 0 at both corners. Research's −15 and −69 are not reproduced.
  - The other 8 flagged sites, A br6–9 and B br6–9, go guarded-negative under both semantics, mostly at the already-derated worst corner.
    - At fastmin, the only guarded-negative own numbers are A ucond_br6 (−57), A ucond_br9 (−93) and B ucond_br6/8/9 (−331, −117, −255).
    - A ucond_br6 is the only site where the guard is needed to make own negative while OR-join is negative raw: OR-join guarded is −4977/−2606.
  - So, once research's own guardband is accepted, OR-join semantics are what produce research's flag at A ucond_br6. At the other flagged sites the flag comes from the guard together with the delay model, not from the join semantics.
- **B: OR-join off research's launch.** In B, OR-join semantics give large negatives that research's launch selection does not reach. On ucond_br6 the OR-join margin is −5183 at worst for launch `ulink_n7` with `ulink_n30__1` transparent. The pairing is n30__0 against the compare chain, the same structure as A. Research does not report this, because its launches are the nearest storage of the select, which on B is `ulink_n30__1`. Own semantics give +953 there.

### Sanity checks (in sites_results.txt)

- **ucond_br6 against results.txt.** All 16 non-transparent ucond_br6 rows (A `ulink_n7`/`ulink_n11__1`, B `ulink_n30__1`/`ulink_n11__1`, both halves, both corners) are **identical** to results.txt in own, < 2^12, OR-join and plain.
- **The 4 "B combined" rows differ, and the difference is a correction.**
  - Re-run in rule_e.py's latches-only select mode, they reproduce results.txt exactly: +1022/+1713 worst and +1831/+2223 fastmin.
  - With the en path of the transparent `ulink_n30__1` added, they become **+953/+953 worst and +1272/+1272 fastmin.**
  - The en path is: ulink_n7 C node → uaddi0 chain → ulink_n30__1 C node → en → q → compare. It is later than the d path by 69 ps at worst and 559 ps at fastmin, and the counter restriction does not shorten it.
  - This equals the B main margin, as it should, because the req and en paths share the prefix up to ulink_n30__1's C node.
  - **This supersedes the "B combined" row of the table above:** the honest B number at ucond_br6 is +953 (worst) and +1272 (fastmin), full or < 2^12. The upstream launch through umux0 (+754 / +1137) is lower still.
- **Planted delays on other sites** (A, worst; +2000 ps on one ICBUF in a copy of `netlist_baked.v`, full re-parse; all PASS):

| site | ICBUF planted | own before → after | change |
|---|---|---|---|
| ucond_br3 | ic_009515, select path | 3304 → 1304 | −2000 |
| ucond_br3 | ic_008536, request path | 3304 → 5304 | +2000 |
| umux0.uj0 | ic_012683, select path | 1970 → −30 | −2000 |
| umux0.uj0 | ic_012597, request path | 1970 → 3970 | +2000 |
| both | ic_012664 (ucond_br6's s), unrelated | unchanged | 0 |

### Limitations

1. Every limitation of the ucond_br6 check above still applies: the simulator's delay model, the 4-phase / C-element assumptions, the slice-granular counter cut, and that the hold half of rule E is not checked.
2. **Launch coverage.**
   - Upstream launches go only through latches, to depth 2. Depth 2 sets a new minimum only at B ucond_br6–9, through umux0. A one-off run with `--depth 3` (308/292 rows, not saved) changed no site minimum.
   - Sources that are not latches are not launched: arbiter grants, ack C-elements, the rounds FFs.
   - The control-merge index paths (into `ucontrol_merge0_olink` and `ulink_n_index_15` stage[0]) are therefore covered only as far as the merges' own bundling holds. That bundling was not checked.
3. **Free inputs.**
   - On every upstream launch, cone-external join inputs are free and set to the value that makes req earliest. Examples: the other mux data request, `n11__1_req`, the cond_br partner channel.
   - The select of a mux on the request path (umux0's s when launching `ulink_n12__0`) is treated as a derived input that may rise. This is a lower bound for req, not an exact event.
4. **Comparison with research.** Research's raw numbers come from nextpnr's own SDF, a different delay model, so only the sign pattern and the method are compared, not the ps values. At the research launch, own and OR-join differ only where a crossed C-element has two launch-derived inputs, which is A ucond_br6. On B the same structure appears only at a launch research does not take.
5. **Requested but not done.** No nominal-SDF work dir was available, so research's corner is not reproduced. vvp was not run, by instruction.

## Collatz item 22 (sites on colsz2_26)

Added after "All sites"; nothing above this heading was changed, and `sites.py`, `sites_results.*`, `results.*` were not rewritten. Target: BOARD-QUEUE item 22 as the audit tracks it (findings/T98.md: research 514ac04a "#23", collatz full range fcolsz2, board seed 26, own build `/root/t65/colsz2_26`, sdf bc2fe0c8). Note that the `## 22.` heading in `/root/wt-r91/research/BOARD-QUEUE.md` is an older collatz64 item; the dirs given are the collatz (32-bit) ones.

| file | what |
|---|---|
| `sites_gen.py` | sites.py generalised: `python3 sites_gen.py collatz` (about 10 s, peak about 170 MB), `python3 sites_gen.py xorshift` (about 27 s, peak about 290 MB) |
| `sites_collatz_item22.txt` / `.json` | collatz: structure, one row per (site gate, launch, corner) with own / OR-join / plain, summary, data-range note, plant test, notes |
| `sites_results_regen.txt`, `sites_gen_xorshift_check.txt` | the xorshift designs A/B re-run through `sites_gen.py`, and its comparison with `sites_results.txt` / `.json` |

### Method changes (sites.py -> sites_gen.py)

- **Nothing is keyed to xorshift names any more.** The kernel Verilog is parsed hierarchically (every module defined in the file is expanded from the one top module). From it come: every `bd_steer` (gates `u$LUT6`/`u$LUT5`) and `bd_mux` (gates `uj0`/`uj1`, from `cells/rtl/bd_mux.v`) with its req and select nets read from the instance ports; every `bd_join` instance path (top-level `_j` joins and the fused ops' `ujoin`, including the 5-input tree in `uselect0`); every `bd_link` and every `bd_pipe` expanded to its stages (`<pipe>.many.stage[i].u`, from bd_pipe's generate); every `bd_delay_gated`; the fused ops (a kernel module with one bd_join and one bd_delay_gated); the arbitrated merges.
  - Request-rendezvous C-elements = state LUTs under a bd_join path or a mux's uj0/uj1 (was the regex `.ujoin.|_j.|.uj[01]`). Steer gates = the u$LUT6/5 of each RTL steer (was `ucond_br\d+`). Link latches = state LUTs under `<link>.lat.` for an RTL link or pipe stage (anything left over is reported; nothing is).
  - Sites come from the RTL (xorshift keeps research's list so that its rows are reproducible; the RTL list is checked equal to it).
  - The loop-counter restriction (`<2^12`, uaddi0 + n7/n29/n30 nets) is now per-design configuration; collatz has none.
  - New informational column `vr`: own with the CARRY4 slices that the gate vectors never reach dropped (uaddi0 slices >= 6, uaddi1 slices >= 3; chain order from CIN<-CO3, checked against the `slice[k]` names). Also recorded per row: CARRY4 count by owner in the select cone and on the critical select path.
  - Corners per design (collatz: worst, FAST_MIN, SLOW_MAX). Engine, walks, launch discovery (direct + upstream through transparent links, depth 2) and the three margins are sites.py's code unchanged.
- **xorshift still reproduces exactly** (`sites_gen_xorshift_check.txt`): `sites_results_regen.txt` is line-for-line identical to `sites_results.txt` (702 lines, 0 differences, including the summary, the ucond_br6-vs-results.txt sanity and the planted-delay section), and all 520 rows equal `sites_results.json` in every field (critical paths, crossed C-elements, notes). RTL-derived join C-elements (18/18), steer gates (16/16) and site gates (24/24) equal sites.py's regexes / research's list on both A and B; 745/745 and 777/777 latch LUTs map to an RTL link.

### Collatz structure (from the RTL, checked against routed.json)

6 steers (ucond_br2-7), 3 muxes (umux0-2), 18 gates. 11 bd_joins (ucmpi0's N=1 join is a wire; 17 C-element LUTs in all incl. the 6 mux joins). 5 fused ops: ucmpi0 (n==1, 8-element chain), uaddi0 (3n+1, 8 CARRY4, 12), uselect0 (even ? n>>1 : 3n+1, 16), uaddi1 (steps+1, 8 CARRY4, 10), ucmpi2 (n'==1, 16). 15 bd_links + 9 pipes (19 stages), 747 latch LUTs in 34 links, every one with a unique en pin. uselect0's internal select (n[0]) is inside a fused op and covered by its matched delay; it is not a rule-E site.

### Results (ps, raw, no guard; min over both gates and every launch; 474 rows, all with a result)

| site | own worst | own FAST_MIN | own SLOW_MAX | binding launch (worst) | OR-join min (worst/FM/SM) | dynamic t83 monitor min (worst/FM/SM, T98) |
|---|---|---|---|---|---|---|
| ucond_br2 | +2187 | +2095 | +5918 | ulink_n1__1 | = own | 3006 / 2679 / 7357 |
| ucond_br3 | +2099 | +2037 | +5724 | ulink_n1__1 | = own | 2918 / 2621 / 7163 |
| **ucond_br4** | **+2021** | **+1982** | **+5560** | ulink_n1__1 | = own | 2840 / 2566 / 6999 |
| ucond_br5 | +9641 | +7456 | +22309 | ulink_n14__0, T=ulink_n11 | = own | 15259 / 11390 / 33674 |
| ucond_br6 | +9706 | +7522 | +22566 | ulink_n14__0, T=ulink_n11 | = own | 15324 / 11456 / 33931 |
| ucond_br7 | +10060 | +7742 | +23055 | ulink_n14__0, T=ulink_n11 | +2782 / +2349 / +7572 | 15678 / 11676 / 34420 |
| umux0 | +6804 | +5067 | +14599 | ulink_n14__0 | = own | (monitor measures udat s vs z_req: not the same quantity) |
| umux1 | +13696 | +9677 | +28799 | ulink_n14__1 stage[1] | = own | (idem) |
| umux2 | +6228 | +4611 | +13542 | ulink_n_index_11 stage[1] | = own | (idem) |

- **No negative site, under own or OR-join semantics, at any corner or launch.** Overall minimum: +1982 at ucond_br4 FAST_MIN (launch ulink_n1__1: the ucmpi0 n==1 compare vs ucmpi0's 8-element chain). Plain shortest path is negative on every steer (it ignores the delay-chain AND taps); diagnostic only.
- Static <= dynamic for every steer at every corner (ucond_br2-4 by 0.6-1.4 ns; ucond_br5-7 by 4-11 ns, because the binding static launch is an upstream one through umux0's select and the transparent n[0] link, which the run does not exercise as a late select change).
- ucond_br7's OR-join is lower than own because its join pairs n28__0 (uselect0's output, before the ucmpi2 chain) with n31__0 (after it): the same structure as xorshift A ucond_br6, but here still positive.

### Data range vs static path

- The 13 gate vectors (n = 2..32768 powers of 2, 27, 97, 871, 6171) keep every trajectory value < 2^20 (max 975400) and the step count <= 261. So uaddi0's carries above bit 21 and uaddi1's above bit 8 are never exercised by the gate; a full-range n (up to 2^31) exercises them.
- The margins above are the **static longest path, full 32-bit carry through every CARRY4 slice** (no counter or range restriction is applied to collatz). The `vr` column is "=" on every row: no critical select path uses a carry outside the vector range.
- uaddi0 appears in the select cone of 144 rows, always as an upstream launch (ulink_n10__1/2) through the transparent adder output latch ulink_n26. There the full-carry d path reaches s at least 2745 / 2372 / 6963 ps (worst / FAST_MIN / SLOW_MAX) before ulink_n26's own en path, which is what binds; the margin of the full-carry d path alone is >= 13.4 / 10.6 / 31.1 ns. So under this delay model the 3n+1 carry for large n is covered by uaddi0's matched delay and cannot set a select margin. uaddi1 (steps) feeds no select cone. The ucmpi0/ucmpi2 compares (LUT + MUXF7/F8 trees) and n>>1 have no carry.

### Sanity

- Planted +2000 ps on one ICBUF in a copy of the worst netlist, full re-parse (all PASS): ic_012306 on ucond_br4.u$LUT6's critical select path (launch ulink_n1__1): own 2021 -> 21 (**exactly -2000**); ic_009665 on umux2.uj0's select path: 6228 -> 4228 (**-2000**); ic_012055 on ucond_br4's request path: +2000; ic_013781 (umux1.uj0's s pin, unrelated): 0.
- Depth 3 upstream launches (one-off, not saved): no site minimum changes; 72 of the extra rows close a cycle (the whole loop transparent at once) and are aborted, as designed.

### Limitations

1. All limitations of the sections above apply (simulator delay model, not silicon; 4-phase / C-element assumptions with free join inputs set to make req earliest; rule E's hold half not checked; upstream launches only through latches, depth 2).
2. Non-latch sources are not launched: the bench FFs feeding ulink_n1__1, and the arbiter state / ack C-elements feeding ucontrol_merge0_olink and ulink_n_index_11 stage[0] (the merges' own bundling obligation, not checked here).
3. Latches whose d is a constant (ulink_n19__*, 32'h1) are treated as able to change; pessimistic only.
4. The mux comparison with the dynamic monitor is not like-for-like (the t83 mux monitor watches the data-mux LUTs' select against z_req, not the uj0/uj1 joins).
5. The project's tighten.py / skew.py / corner_audit.py were not run (only read for xorshift earlier); no research rule-E numbers for this route were compared, since none were available as text here.
