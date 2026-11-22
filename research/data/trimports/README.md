# The memory port's own lines in the cycle-scoped trim: AUTO_TRIM_PORTS (2026-11-21)

**Why.** On a memory kernel the port is often the critical cycle: across flow v10's 63 rule-CLEAN memory-kernel routes
it is a median 42 % of the cycle (18-89 %, >= 50 % on 24). Its two matched lines per RAM (usetup, uco) are sized
raise-only by the loop, so the shipped route usually carries more than its own rule asks (v12's memsum s1: the rule asks
usetup 12 -> 1, uco 12 -> 8). The post-route trim (AUTO_TRIM_SCOPE=cycle, flow v10 on) shortens lines on the critical
cycle by LUT INIT only -- but research/tools/auto/cycle_macros.py maps an instance on the cycle to BD_SZ_<instance>, and
a port's lines are BD_SZ_..._UMEM_CONTROLLERn_UMEMk_USETUP / _UCO (no "_UPORT"), so the trim never listed them.
With plain bd_mem it could not have trimmed them anyway (symmetric LUT1 lines); with BDC_MEM_FASTFALL (bd_mem_ff,
FASTFALL LUT2 lines) it can: on all 17 rule-CLEAN routes of the farm's mff A/B whose port is on the cycle, the rule at
both bands would remove 4-29 elements of port lines, and none was trimmed.

**What.** cycle_macros.py --ports LIST (LIST = trim_lines.py --list on the route): a port X_uport on the cycle also
brings its trimmable lines. auto_size.sh AUTO_TRIM_PORTS=1 (opt-in) passes it. Unset: identical output on 400 saved
(cycle, sizes) pairs.

**Same-route test, mff's dot2 s2** (mff_dot2_s2/: /tmp/bot/scripts/tploc.sh -- the farm task's saved loop state, the
shipped route rebuilt with AUTO_TRIM_ONLY and checked by sdf, 0f16dbc4 = the farm's; then the flow's own trim, timing
and 4 draws). Control: the farm's result on the same route (farm_result_control.txt).

| | farm (mff_2 task 2) | AUTO_TRIM_PORTS=1, same route |
|---|---|---|
| lines on the untrimmed cycle | 6 | 10 (+ controller 3's four port lines) |
| trim rounds | round 1: 4 chains, P unchanged -> reverted | round 1: 27730 -> 27404; round 2 (20 new lines): -> 24920 |
| trims shipped | 0 | 10 (7 port lines, uaddi1, uandi0, a uack) |
| P (event graph) | 27.73 ns | **24.92 ns (-10.1 %)** |
| call latency median / sum | 957 / 5058 ns | **864 / 4584 ns (-9.7 / -9.4 %)** |
| draws | PASS 4 / 4 | PASS 4 / 4 (8 / 8 calls each; no pulse < 1 ns, narrowest 4447 ps) |
| rule / bits | CLEAN / EQUIVALENT | CLEAN / EQUIVALENT, ffmux-clean |

The port trims alone moved P by 1.2 %, but they moved the critical cycle off the port, and the next rounds could then
trim the loop's own lines (the farm's run never got there: its first round bought nothing and was reverted).

**Second route, mff's gather s2** (mff_gather_s2/, same method; sdf b08c7387 = the farm's): 14 lines on the untrimmed
cycle, 10 chains moved in round 1, all 8 shipped trims port lines (controller 2's usetup 1 / 2, uco 8 / 7; controller
3's usetup 12 / 11, uco 11 / 10). **P 43.36 -> 37.69 ns (-13.1 %), call latency median 1488 -> 1284 ns (-13.7 %), sum
9180 -> 7944 ns**; PASS 4 / 4 (9 / 9 calls each), no pulse under 1 ns (narrowest 4359 ps), rule CLEAN, EQUIVALENT.

| route (mff, same sdf) | P farm -> port trims | latency median | draws |
|---|---|---|---|
| dot2 s2 | 27.73 -> 24.92 ns (-10.1 %) | 957 -> 864 ns | 4 / 4 |
| gather s2 | 43.36 -> 37.69 ns (-13.1 %) | 1488 -> 1284 ns | 4 / 4 |
| gather s1 | 40.29 -> 37.72 ns (-6.4 %) | 1344 -> 1254 ns | 4 / 4 |
| if_loop_2 s1 | 29.79 -> 25.49 ns (-14.4 %) | 2997 -> 2562 ns | 4 / 4 |
| mul_example s2 | 58.45 -> 58.45 (no trimmable port line) | = | 4 / 4 |

Over the four routes with a FASTFALL port: P ratio geometric mean **0.89** (0.856-0.936), latency median ratio 0.89;
16 of 16 draws pass, no pulse under 1 ns (narrowest 3752 ps), every route rule-CLEAN and EQUIVALENT after its trims.

**Where it does nothing.** mul_example s2: its port's lines are LUT1 symmetric lines even under BDC_MEM_FASTFALL=1 --
bdc/mem.py's arbitrated host port (a load and a store on one memory) emitted plain bd_mem unconditionally, so the mff A/B
never treated binary_search, mul_example, test_bool_array, test_memory_1 / 2, test_stdint (byte-identical routes to
v10's). BDC_MEM_FASTFALL=2 (opt-in, e0a4b59f0d) adds that port; its GLS runs are in research/JOURNAL.md.

Not shown yet: a flow-level effect (a farm A/B); the routes are mff's (BDC_MEM_FASTFALL=1), so the gain needs that knob
(or =2) in the flow.
