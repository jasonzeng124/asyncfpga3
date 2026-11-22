# For research and the owner: THE goal (the gcd_hw bitstream theorem)

Started 2026-11-01 by shard A. Counterexamples to THE theorem go here first (PROGRAM.md). The older,
rule-by-rule list is `formal/out/FOR-RESEARCH.md`.





## C79. Scatter stress test on board items 42 / 43 and on C75's thin v11 routes: 42 and 43 never fail up to 5x your per-arc sigma; sqrtsub s4 (B32's +55 ps latch-fed race) is the weakest route tested, failing from 3x (shard C, 2026-11-22 10:43 UTC; untrusted simulation, a stress test, not a board prediction)
- **Method:** C76's, with 32 draws (K 30001-30032) per point on the bits decoded in C72 / C75. The cells count draws
  that did not pass: F = wrong answer or hang, U = event cap with no verdict.

  | route | x3 (0.378) | x4 (0.504) | x5 (0.630) |
  |---|---|---|---|
  | **item 42** collatz_v10_s1 | 0 | 0 | 0 |
  | **item 43** xorshift_v10_s1 | 0 | 0 | 0 |
  | v11 sqrtsub s4 | **1 F + 1 U** | **3 F + 4 U** | **5 F + 3 U** |
  | v11 branchloop s3 | 1 U | 1 F + 1 U | 1 F + 1 U |
  | v11 brhash s2 | 0 | 2 U | 2 U |
  | v11 test_bitint s1 (memory) | 0 | 0 | 2 F |
  | v11 factorial s1 | 0 | 0 | 1 F |
  | v11 factorial s4 | 0 | 0 | 1 U |
  | v11 cmpchain s1 | 0 | 0 | 0 |
  | v11 brhash s1 | 0 | 0 | 0 |

- **sqrtsub s4, by injection:** its 7 non-passes at x4 were re-run with +300 ps on `ucond_br6`'s inputs, LUT6 and LUT5
  together.
  - Traced from the bits: the condition comes from latch `ulink_n24_folink.lat.odd` (9 routing hops, 880 / 1617 ps).
    The request comes from the join `ucond_br6_j` (7 hops, 379 / 749 ps).
  - **With the request delayed: 3 of the 7 pass, including 2 of the 3 wrong answers.** With the condition delayed:
    none pass, and one more draw fails.
  - The rest are event-cap draws that stay undecided either way. That is another mechanism, as in C78's collatz64
    draw, and it is not traced.
  - So part of sqrtsub s4's weakness is B32's ucond_br6 race, the one your AUTO_RACE_KAPPA padded on this route
    (ULINK_N24_FOLINK 1 -> 4).
  - At your own scatter (0.126), 32 / 32 pass with and without the injection.
- **Reading:**
  - The two board candidates are the most robust routes formal has stressed.
  - The order among the v11 routes follows B's adversary only loosely. The weakest by both measures is sqrtsub s4.
    But cmpchain s1 and factorial s1 / s4 (adversary 0.06-0.10) hold almost as well as the board candidates.
- **File:** `formal/tools/margin/spec/inj_sqrtsub_v11s4_ucond_br6_req.json`.
- **Added: what an event-cap draw is.** simx now has HOTNODES=N, which prints the most-changing nodes when it hits
  the cap. On collatz64 s1 K 30010 (x4, C78) it shows a real oscillation in the model, not a simulator artefact:
  - from about 0.42 us, bits 2-8 of the loop's data toggle ~2000-7000 times, about every 66 ps;
  - the toggling runs through every data latch on the loop ring at once: `ulink_n28`, both stages of
    `ulink_n_falseResult_9`, `umux0.udat`, `ulink_n10__1..4`, then the adder `uaddi0` (CARRY4 XORs) and `uselect0`.
  - So every latch of the ring was transparent together, and the data closed a combinational loop through the adder.
    Some control failure opened them (C78's 1 ps pulses on those latches). It is not traced to which control race.
  - **Stuck, not slow:** with the event cap raised to 10^9 (10x), K 30010 reaches 8.49 us with no answer. A passing
    draw at the same scatter (K 30011) gives its first answer at 3.18 us on 2 x 10^6 events.
  - **The cause is open:** the ring's latch-enable controllers (`ulink_n10__1..4`, `ulink_n28`,
    `ulink_n_falseResult_9`, `umux0`) hand over in an orderly way up to 0.445 us, about one handshake per ~14 ns, with no
    storage pulse under 200 ps. So the trigger is not a runt on those controls. It was not found.
  - **A lead on the cause (not proved):** node histories of K 30010 and of the passing K 30011, same scatter.
    - Total LUT activity matches until ~600 ns, then grows about 2x per 50 ns.
    - The earliest narrow pulses that the passing draw does not have: `uselect0` (284 ps at 607 ns). Then, at
      630.3 ns, a 188 ps pulse on bit 6 passes `ulink_n_falseResult_9` stage 0 -> stage 1 -> `umux0.udat` ->
      `ulink_n10__1` / `__4` within ~2.5 ns.
    - That means those data latches were all transparent at once while a glitch went around the loop. It looks like a
      wrap-around (hold) race: the loop's new value comes back round through open latches before the capturing latch
      closes. This class is your rules H / I's, not the steers'.
    - The window in which every latch is open was not measured.
    - +300 ps on all 128 data arcs from `ulink_n_falseResult_9` into `umux0.udat` does not cure K 30010 (cap at
      2.35 us instead of 2.56). That neither confirms nor refutes the lead: a loop with every latch open oscillates
      at any delay, and the timing of the close that the race is lost against is unknown.
  - The other undecided draws (sqrtsub s4, brhash s2, branchloop s3) are probably the same kind. They were not
    checked.


## C78. The same test on item 45's partners: unguarded sqrtsub's failures at 5x scatter are its compare-steer race at ucond_br3, which your 10 % rule-E guard targets. Unguarded lfsrfind's are NOT at B's ucond_br5, and are not traced (shard C, 2026-11-22 10:18 UTC; untrusted simulation)
- **sqrtsub s1 (item 44's unguarded route, sdf 9c9da593).** Its 3 failing draws at sarc 0.630 (K 20008, 30053,
  30063) were re-run with +300 ps on one input of `ucond_br3`'s LUT6 or LUT5 at a time.
  - **Only LUT6 pin 1 cures them, all 3.** Every other pin leaves all 3 failing.
  - Traced from the bits:
    - pin 0 is the condition, from the compare `ucmpi0.uz_n3`: 8 routing hops, 397 / 833 ps;
    - pin 1 is the request, from the join `ucond_br3_j`: 5 hops, 133 / 301 ps.
  - So the request outruns a slow compare result at the loop's exit steer. That is B30's ucond_br3 (ctl term on
    ulink_n1__1), the race your AUTO_GUARD_E=0.90,1.10 was built for. The guarded route (item 45) has 0 / 80 failures
    at the same scatter (C76).
- **lfsrfind s1 (item 44's unguarded route, sdf 7d3fde12).** Its 2 failing draws (K 20005, 30014) were re-run with
  +300 ps on each pin of `ucond_br5`'s LUT6 / LUT5.
  - None cures either draw, including pin 3, the request from `ucond_br5_j`. Pin 0 is the condition from
    `ucmpi0.uz_n24`.
  - K 30014 goes wrong from its second answer. A 6 ps pulse at `ulink_n31__1.lat.pair[2]` appears at 418 ns, during
    start-up. So lfsrfind's separation in C76 is some other mechanism, not B's steer. Do not read it as evidence for
    the guard.
- **collatz64 s1 (item 44's unguarded route).** C76's only non-pass draw, K 30010 (undecided at both 4x and 5x),
  hits simx's event cap at the same instant, 2.563 us, with or without +300 ps on either input of B's `ucond_br6`
  (request from `ucond_br6_j`, condition from `ucmpi2.uz_n38`).
  - Its narrowest pulses are 1 ps, on the data latches of `ulink_n10__2` / `ulink_n10__4`. This is not the steer
    race, and it is not traced. It may be a simx event storm at extreme scatter rather than a circuit failure.
- **Files:**
  - `formal/tools/margin/spec/inj_sqrtsub_v10s1_ucond_br3_pin1.json`;
  - `formal/tools/margin/spec/trace_pins.py`, which names the driver of each LUT pin from the decoded net.

## C77. Item 46's hang is B36's race, shown causally: on the unpadded route, 300 ps of extra delay on ucond_br14's request input cures the hangs, and the same delay on its condition input makes every one of those draws fail (shard C, 2026-11-22 10:13 UTC; untrusted simulation)
- **Setup:** C76's 8 failing draws of item 46 unpadded at 4x per-arc scatter (K 30003, 30021, 30026, 30030, 30034,
  30054, 30058, 30059). Each was re-run with +300 ps injected on one input arc of `ucond_br14`'s LUT6
  (SLICE_X16Y27.C6), one pin at a time, and on uack's closest-race pin.

  | injection (+300 ps) | 8 draws (P pass / F fail / U undecided) |
  |---|---|
  | none (reproduction) | F F F F U F P F |
  | LUT6 pin 0, 3, 4 or 5 | unchanged |
  | **LUT6 pin 2** | **P P P P F P P P** |
  | **LUT6 pin 1** | **F F F F F F F F** |
  | uack (D6) pin 0 | F F F F U F U F |

  - K 30058 was undecided in the batch and passes when run alone. It is the one draw in the set that never failed.
- **The two signals:** traced from the decoded bits, through the pips, to the LUT that drives each.
  - **Pin 1** (delaying it makes failures certain) is the steer's condition, from latch `ulink_n101_folink.lat.odd`
    (SLICE_X16Y17). The route has 8 routing hops, 482 / 935 ps fast / slow max on routing alone.
  - **Pin 2** (delaying it cures) is the steer's request, from the join `ucond_br14_j` (SLICE_X17Y27). It has
    4 hops, 69 / 160 ps.
  - So the request can reach the steer before a late condition settles. That is B36's latch-fed race, and your
    AUTO_RACE_KAPPA padding (on the request side) is the fix the simulation agrees with.
- **With the injection on all 64 draws:**
  - at 4x scatter: 63 / 64 PASS, against 56 / 64 (+2 undecided) without it. The one remaining hang is K 30034, another
    race not traced.
  - at your own scatter (sarc 0.126): 64 / 64 PASS, so the injection itself breaks nothing.
- **Files:** `formal/tools/margin/spec/inj_item46_ucond_br14_pin2.json` (draws.py `--inject`).
- **What it does not say:** whether the die's scatter ever reaches this race. At your model's scatter it does not
  (C73). Item 46 on the board is the test.

## C76. With the random model's per-arc scatter inflated (3x to 5x your 0.126), formal's draws do separate the board pairs, and in the direction of B's adversary. Item 46 unpadded hangs from 3x, padded never. Unguarded sqrtsub / lfsrfind fail at 5x, guarded never. collatz64 shows nothing (shard C, 2026-11-22 10:06 UTC; untrusted simulation, a stress test, not a board prediction)
- **Why:** C73 / C75 found that your draw model separates none of the pairs (items 45 / 46). This asks how far the
  model's within-die scatter must grow before it does, and whether it then agrees with B's worst-case adversary.
- **Method:** the same decoded bits as C73 (each rebuilt by your board_rebuild.sh, sdf and trimmed fasm SAME), and your
  draw model with only the per-arc lognormal sigma changed (draws.py `--sarc`). Memory kernels are filled through the
  host port; out0 is sampled 23 ns after the request. Two seed sets were pooled: 16 draws (K 20001-) and 64 draws
  (K 30001-) per point.

  | pair | sarc x2 (0.252) | x3 (0.378) | x4 (0.504) | x5 (0.630) |
  |---|---|---|---|---|
  | 46 unpadded test_flatten_array | 0 / 80 | **4 / 80 hang** | **9 / 80 hang** (+3 undecided) | 2 / 16 hang (+3 und.) |
  | 46 padded | 0 / 80 | 0 / 80 | 0 hangs; 3 / 80 host-fill RAM setup violations | 0 hangs; 2 / 16 host-fill violations |
  | 44 sqrtsub s1 (unguarded) | 0 / 16 | 0 / 16 | 0 / 80 | **3 / 80** (stops after 6 of 13 answers) |
  | 45 sqrtsub (guarded) | 0 / 16 | 0 / 16 | 0 / 80 | 0 / 80 |
  | 44 lfsrfind s1 (unguarded) | 0 / 16 | 0 / 16 | 0 / 80 | **2 / 80** (wrong answers) |
  | 45 lfsrfind (guarded) | 0 / 16 | 0 / 16 | 0 / 80 | 0 / 80 |
  | 44 collatz64 s1 (unguarded) | 0 / 16 | 0 / 16 | 0 / 80 (1 undecided: event cap) | 0 / 80 (1 undecided: event cap) |
  | 45 collatz64 (guarded) | 0 / 16 | 0 / 16 | 0 / 80 | 0 / 80 |

  - The undecided collatz64 draws hit simx's event cap with no verdict. A livelock is possible, but none was traced.
- **How strong the separation is** (one-sided Fisher, failures vs none):
  - item 46 at x4: 9 / 80 vs 0 / 80, p ~ 0.002;
  - item 46 at x3: 4 / 80 vs 0 / 80, p ~ 0.06;
  - item 45 pooled at x5: 5 / 240 vs 0 / 240, p ~ 0.03;
  - each item-45 pair alone is not significant.
- **Where the failures sit.** Closest races logged by simx RACES=1 in failing draws; closest is not proved causal, and
  none is traced to a path yet:
  - item 46 unpadded hang (K 20015, x3): storage reorderings at umux8.uxa / uya (1-2 ps); feeding-storage at
    **ucond_br14.uack (3 ps)** and ucond_br14's LUT6 (78 ps). ucond_br14 is B36's latch-fed steer.
  - sqrtsub unguarded (K 30053 / 30063, x5): storage at ulink_n_index_15's stage controls and umux0 / 1 / 2;
    feeding-storage includes **ucond_br3** (155 / 65 ps), which is B30's weakest steer on that route.
  - item 46 padded's failures at x4-x5 are RAM setup violations in simx's host-port fill. That is the harness's
    write timing, not the kernel.
- **What this does and does not say:**
  - Your per-pip sigma 0.126 was fitted to the August ring data. x3 is far outside anything measured, so none of these
    rates predicts the board.
  - What it shows is order: as random scatter grows, the routes B's adversary calls thin fail first, and their
    guarded / padded partners hold longer.
  - So the random model and the adversary disagree on how likely a failure is, not on which route is weaker.
- **Reproduce:** the drawspec.sh output of C73, then `tools-B/auto/xdraws.py ... --sarc 0.378 --draws 64 --seed0 30001`
  (`--mem ... --hostport` for memory kernels).

## C75. Your 02:20 #2: flow v11's thinnest routes by B's adversary pass every one of formal's draws (8 routes, 32 + 32 each). The farm repeats C72 / C73 at 64 + 64 with the same result (shard C, 2026-11-22 09:30 UTC; untrusted simulation)
- **The routes:** the v11 rule-CLEAN PASS routes that B39-B42 call thin, plus sqrtsub s4 (B32's latch-fed race) and
  test_bitint s1 (the feeder-bound one).
- **Method:** each was rebuilt by your board_rebuild.sh from B's mk_specs_all.py --stagefix spec. The sdf was checked
  against your farm's, and the trims applied with 0 REFUSED lines. These specs carry no judged fasm, so the trimmed fasm
  md5 below is reported, not checked. Then 32 draws of your model and 32 slow-carry draws.

  | route | B's adversary | sdf | trimmed fasm | draws |
  |---|---|---|---|---|
  | branchloop s3 | kappa 0.03 | d9f4eb75 | 492d5045 (= B40's) | 32 + 32 PASS |
  | factorial s1 | 0.06 | af1de6de | a0ac8dd2 | 32 + 32 PASS |
  | factorial s4 | 0.06 | de8c6a17 | 69c789e5 | 32 + 32 PASS |
  | cmpchain s1 | 0.10 | 153e27be | c364d19d | 32 + 32 PASS |
  | test_bitint s1 (memory) | 0.10, feeder-bound | e2ae20a1 | 45fd4387 | 32 + 32 PASS |
  | brhash s1 | B's v11 table | b95072bd | 23c53a94 | 32 + 32 PASS |
  | brhash s2 | B's v11 table | 25901987 | bcc8ed5a | 32 + 32 PASS |
  | sqrtsub s4 | 0.03, latch-fed +55 ps | 89fc043c | 2e8a873b | 32 + 32 PASS |

- **Farm c_brd2, 64 + 64 draws:** every route of C72 / C73 PASS 128 / 128, built with the sdf and trimmed fasm checked.
  - Unguarded sqrtsub (item 44) is the exception: its build failed on the farm with no log returned. It rebuilt and
    passed locally (C73).
  - Guarded collatz64 is still running. *(Added 10:24: done, 128 / 128 PASS.)*
- **Reading:** across 18 routes, formal's draw model has never failed a route of your flow that B's worst-case adversary
  calls thin, even ones that fail at kappa 0.03. The random model and the adversary disagree on every one of them.
  Only the board can say which is closer to the die.
  - Items 45 / 46 are the pairs built to show it, and an unguarded or unpadded FAIL would be a point for the
    adversary.
  - Until then, the draw model's verdict on these routes is not evidence that the guards are unnecessary.

## C74. AUTO_SEARCH_KEEPDEPTH (your 07:10): quadrec's search structure with the base depths kept is LIVE in formal's exhaustive model, for one call and for two back to back (shard C, 2026-11-22 08:34 UTC; untrusted exhaustive search, formal/tools/live/check.sh)
- **Setup:** research 98c35d42a, quadrec's default fixture MLIR, BDC_AUTO=1. Three structures, each checked
  exhaustively over every reachable state, with nondeterministic conditions and no trip-count bound:

  | structure | stages | states | verdict |
  |---|---|---|---|
  | base (the floor's pipes, ulink_n_trueResult_16 / _18 / _20 at 2) | 84 | 826 | LIVE |
  | + BDC_FORK_OUT_LINK=n20__0,n23__0,n25__0,n27__0, as the flow built it (pipes lowered, floor stages none) | 84 | 826 | LIVE |
  | + the same fork links and BDC_LINK_DEPTHS=ulink_n_trueResult_16=2,_18=2,_20=2 (KEEPDEPTH) | 87 | 826 | LIVE |

  - The KEEPDEPTH structure is also LIVE with LIVE_INV=2 (two calls back to back: 5147 states).
  - 0 hazards and 0 tokens left at the end, in every row.
- **What it says:** the three kept stages add capacity to the rotation rings and do not create a token-free cycle, as
  the ring condition (S >= 2T + 1) predicts.
- **What it does not say:** nothing about timing or about the period you measured (21.2 vs 43.4 ns). It covers only
  the structure your census says the knob changes; other kernels were not rechecked.

## C73. Items 45, 44 (partners) and 46: formal's draws cannot tell any pair apart. All 8 routes pass 64 / 64, the guarded and unguarded, the padded and unpadded alike, as in your gate (shard C, 2026-11-22 08:30 UTC; untrusted simulation)
- **Method:** each route was rebuilt locally by your board_rebuild.sh from its spec, and every one was OK. The bits
  were decoded, then 32 draws of your model and 32 slow-carry draws were run on each (memory kernel: memtask.sh, with
  the sdf and trimmed fasm checked). Every draw was PASS:

  | item | route | sdf | trimmed fasm | draws |
  |---|---|---|---|---|
  | 45 guarded | collatz64 | 68789cdc | 6460090e | 32 + 32 PASS |
  | 44 partner | collatz64 | de88e329 | 9b93469d | 32 + 32 PASS |
  | 45 guarded | sqrtsub | 2366dc05 | 707d844a | 32 + 32 PASS |
  | 44 partner | sqrtsub | 9c9da593 | bd1eb34e | 32 + 32 PASS |
  | 45 guarded | lfsrfind | d5c91be0 | 802cdb87 | 32 + 32 PASS |
  | 44 partner | lfsrfind | 7d3fde12 | 4e3ef6be | 32 + 32 PASS |
  | 46 unpadded | test_flatten_array | e82284b6 | 77d4a54c | 32 + 32 PASS |
  | 46 padded | test_flatten_array | 2361eec8 | 5fcd82f8 | 32 + 32 PASS |

- **What it means:** formal's random-draw simulator agrees with your gate's 57 / 57 on both halves of each pair. In
  every model formal runs, only B's worst-case adversary (B30 / B36) separates these pairs. So:
  - an unguarded or unpadded FAIL on the board would be evidence for the adversary's corner;
  - it would be evidence against the random model. Neither simulator predicts it.
- **Caveat on item 46:** its two rows above filled the arrays directly (`--mem`), not through the host port, which is
  how C60's memory judgments and your bench fill them. drawspec.sh now sets HOSTPORT=1 by default. A host-port rerun
  of the pair, with the closest race logged per draw (simx RACES=1), is running and will be added here.
- **Added 08:33, host-port rerun of item 46:** the same decoded nets, arrays filled through the host port (1024 host
  writes per draw), with RACES=1.
  - Draws: 32 + 32 PASS on unpadded, and 32 + 32 PASS on padded.
  - The closest input reordering at any storage LUT, over all draws, is 165 ps (unpadded) and 168 ps (padded).
  - Your ucond_br14 is never the closest race on the unpadded route. On the padded route it is the closest in
    1 of 64 draws.
  - So random draws of your model do not come near B36's +1 ps split-corner slack. That slack needs the adversary's
    per-arc extremes.
  - Files: formal-side scratch only. Rerun with `RACES=1 tools-B/auto/xdraws.py ... --mem --hostport`, as in
    memtask.sh.

## C72. Board items 42 and 43 pass formal's draws on the judged bits: collatz_v10_s1 64 / 64, xorshift_v10_s1 64 / 64 (32 of your model + 32 slow-carry each) (shard C, 2026-11-22 07:55 UTC; untrusted simulation)
- **Your 04:00 #2.** Each route was rebuilt locally by your own board_rebuild.sh from its spec:
  - collatz: sdf 0f050078, trimmed fasm 6ef8e077;
  - xorshift: sdf fd959b30, trimmed fasm 78aa6ac3.
  - Both were OK on your checks, on nextpnr 7c3bfb9c684a2551 (the audit's T166 build, with the same routes as 6e5d2244).
- **Method:** the bits were read back with prjxray bit2fasm and decoded into formal's simx. Then:
  - 32 draws of your delay model (K 10101-10132);
  - 32 slow-carry draws (CARRY4 / F7F8 / FF in [0.8, 1.0], K 10151-10182);
  - on your gate vectors (col18 / xor19), checked against your kernel oracle, out0 sampled 23 ns after the request.
- **Result:** every draw PASS on both routes (95 % Wilson lower bound 0.893 per half).
  - So formal's simulator finds no failure on these two bits under your model. That is not a margin, and it says
    nothing about corners outside the model.
- **Tool:** `formal/tools/margin/spec/drawspec.sh SPEC OUT [ND]` (bash, from a clean checkout of this branch;
  RS = your checkout, TC, XRAY_DB).
  - The bit's md5 changes from build to build, because its header carries the frames path and the time. The fasm
    md5s above are the identity to check.
- **Still queued on the farm:** 64 + 64 draws on items 42 and 43 (c_brd2), item 45's three guarded routes and their
  item-44 partners, item 46's pair, and B's 37 flow-v12 specs (c_v12a).
  - Item 46 padded is checked locally: sdf 2361eec8 and trimmed fasm 5fcd82f8 match yours (132 chains,
    0 REFUSED), and 4 + 4 draws pass.

## C71. Your 00:16 board_rebuild defect does not reach any of shard C's memory-route judgments; C's draws on items 42 / 43 / 45 / 46 are queued (shard C, 2026-11-22 07:30 UTC)
- **The defect:** none of C's judgments went through board_rebuild.sh. memtask.sh applies your trim record itself
  (trim_lines.py --partial, in the task's environment).
- **Check:** all 77 trimmed memory-route judgments on the farm (fm_c_mem*): each trimmed as many chains as its record
  has lines. No record under `formal/tools/margin/bram/trims/` names an _SDELAY macro (0 of 75). So no C verdict
  (C60) was on bits that left out a recorded trim.
- **Your 04:00 #2 (C's draws before the board):** `formal/tools/margin/spec/drawspec.sh SPEC OUT [ND]` takes one of
  your board specs and runs it in four steps:
  1. your board_rebuild.sh rebuilds the route (sdf and trimmed fasm checked);
  2. the bits are read back and decoded;
  3. it runs ND draws of your model, then ND slow-carry draws (memory specs go through memtask.sh).
  - It is queued on the farm with 64 + 64 draws for items 42 and 43, item 45's three guarded routes and their
    unguarded item-44 partners, and item 46's pair. The results will come here.

## B42. Flow v12 (the 10 % rule-E guard on every route), first 25 routes (seed 1): one compare steer still loses at kappa 0.10 (brhash s1), and the rest hold to 0.15 or more (shard B, 2026-11-22 05:50 UTC; untrusted extraction and simulation)
- **Method:** `mk_specs_all.py --stagefix`, your fixed board_rebuild.sh / shard C's memtask.sh (every sdf SAME, no
  REFUSED), then the B32 screen. Table: `formal/tools-B/auto/suite/v12/census_table.md`.
- **brhash s1 (v12):** min kappa_lo 0.044 at `ucond_br7`.
  - Its condition `ucmpi1.uz_n28` comes from a one-channel compare launched by `ulink_n10`'s ctl: slack +198 /
    +566 ps.
  - Race-only adversary: **MISMATCH at kappa 0.10**. xtol: no verdict at x = 0.15.
  - So the guard did not lift this route's exit-steer race past 0.10. That is worth a look at what rule E sees on
    `ucond_br7`: B's bound counts the compare's operand latches opening on `ulink_n10`'s ctl. If rule E launches
    the select at the compare's output or at a join, it misses that path.
- **ipow s1:** min 0.116. Its latch-fed race (`ucond_br9`, +231 / +609 ps, ctl-term kappa_lo 0.116) gives no verdict
  at kappa 0.15, which B32's criterion (< 0.13) predicts. v13's AUTO_RACE_KAPPA is the knob for that one.
- **Everything else** is at least 0.064 by the bound, with the adversary holding to 0.15 or 0.20: collatz s1, lfsrfind
  s1, twoloops s1, memsum s1, factorial s1 (0.128; v11's s1 was 0.022 / adversary 0.06), xorshift s1 0.150,
  collatz64 s1 0.139, sqrtsub s1, fill s1, and the memory kernels.

## B41. Your 04:05 notes: test_int16 is now shown as "decode failed: not screened" in the tables, and formal's draws do not use tb_ps.v (shard B, 2026-11-22 04:20 UTC)
- **test_int16 s1-s4:** right. The decode stops in boundary_bench, before any steer is looked at. The race-only
  adversary's "kappa 0 (NONE)" was simx refusing to run without a net. `v10table.py` now prints "decode failed: not
  screened" for such routes. The v10 and v11 tables are regenerated, and no count in B32-B40 included them as
  failures. B32's "no route has its bound above its adversary" also excluded them: they have no bound.
- **+TEND:** B's draws and adversaries run formal's simx (`formal/tools/margin/simx.cpp`), not cells/gls/ps/tb_ps.v,
  so the 32-bit wait does not touch any B number.
- **Feeder class:** understood. I will flag a feeder-bound failure at kappa <= 0.06 on a rule-CLEAN route if one
  shows up (none in v10 / v11 / g10 / v12 so far: the only feeder-bound failure is test_bitint s1, at 0.10).

## B40. B39's redo: on every v11 route of your _SDELAY list, the steer numbers are unchanged with the judged bits. The withdrawn rows stand, and the v11 census is complete at 170 routes (shard B, 2026-11-22 04:10 UTC; untrusted extraction and simulation)
- **Non-memory routes** (branchloop s3, cmpchain s1, collatz s2, countloop s1 / s3, fold64 s2, ipow s3, nested s3,
  quadrec s3, varshift s1): rebuilt with your fixed board_rebuild.sh (88868608a, no REFUSED line) and
  TRIM_STAGEFIX=1. Every trimmed fasm differs from B33 / B36's, so B's earlier bits had the stage lines long. But
  every steer bound, every adversary and every latch-fed race is the same number as before. Examples:
  - branchloop s3: -0.015, adversary kappa 0.03 (fasm cc1763aa -> 492d5045);
  - cmpchain s1: 0.042, adversary 0.10;
  - varshift s1: 0.081.
  - The stage-0 request lines are on none of the steer races' paths.
- **Memory routes** (dot2 s1, fill s2 / s3, gather s2, memsum s1, test_loop_free s1, test_memory_2 s1): same fasm as
  before. Their specs carry BD_DEFINES=-DBD_SYMTRIM, which memtask.sh's trim step already saw in its environment, and
  no trim log has a REFUSED line.
- **So B33 / B36's rows are reinstated as stated.**
- **New with the resume parts (_r1)**, compare steers that are thin by the adversary:
  - factorial s1: 0.022, adversary **0.06**;
  - factorial s4: 0.036, adversary 0.06;
  - share_test_1 s1: 0.085, adversary 0.15;
  - quadrec s1: 0.191; spmv s1: 0.089; stencil_2d s1: 0.103.
- **Table:** `formal/tools-B/auto/suite/v11/census_table.md` (170 routes).
- **v12:** its first 5 routes are being screened.

## B39. Your 00:16 board_rebuild defect: B33 / B36's v11 rows for the 17 routes on your _SDELAY list are WITHDRAWN until redone (shard B, 2026-11-22 02:00 UTC)
- B's v11 rebuilds went through your board_rebuild.sh as it was, so on these routes the screened bits had the stage-0
  request lines at their built length. That is more margin than shipped, so the numbers are optimistic.
  - Withdrawn: branchloop s3 (B36's -0.015 / adversary 0.03 is withdrawn as a number; the true one can only be lower
    or equal), cmpchain s1, collatz s2, countloop s1 / s3, dot2 s1, fill s2 / s3, fold64 s2, gather s2, if_loop_2 s1,
    ipow s3, memsum s1, nested s3, quadrec s1 / s3, test_loop_free s1, test_memory_2 s1, varshift s1, and any other
    route of your list that B screened.
  - Not affected: v10 (B32), g10 (B34), item 45 (B35) and test_flatten_array s2 (B36: no _SDELAY trim in your list).
- Redo running with your fixed script (research 88868608a: it fails on any REFUSED line) and specs carrying
  TRIM_STAGEFIX=1 (`mk_specs_all.py --stagefix`). Memory routes go through shard C's memtask.sh, whose trim step now
  sees the spec's ENV. v10screen refuses a route whose trim log has a REFUSED line. Results follow in B40.

## B38. Your 19:06 questions: a feeder term binds the weakest steer on few routes, and only one adversary failure at kappa <= 0.10 (test_bitint s1) sits on a feeder-bound steer. There the request comes through a sibling link, so the race is not rule A's pair (shard B, 2026-11-21 20:10 UTC; untrusted extraction and simulation)
- **Q1, over the route rows of B32-B36 + g10** (v10, v11 and g10 counted separately, so v11's repeats of v10 routes
  count twice): the class of the binding term on each route's weakest steer LUT.

  | binding term on the weakest steer | min kappa_lo < 0.10 | < 0.13 |
  |---|---|---|
  | compare (the steer reads a compute directly) | 80 | 90 |
  | latch ctl term (AUTO_RACE_KAPPA's) | 21 | 28 |
  | latch feeder term | 10 | 25 |

  - **Distinct routes whose weakest-steer adversary fails at kappa <= 0.10:**
    - compare-bound, 11: branchloop s3 (v11), lfsrfind s1, binary_search s1, collatz64 s1, collatz s3, memsum s4,
      sqrtsub s1, test_memory_1 s3, brhash s1 / s2 (v11), cmpchain s1 (v11);
    - ctl-bound, 7: sqrtsub s4, test_flatten_array s2 (v11) / s3, test_stdint s1, fill s3, ipow s2, sumi3_mem s2;
    - **feeder-bound, 1: test_bitint s1** (v10 = v11, the same route).
  - Caveat: weaksweep slows the steer's whole condition cone, all terms together. "Bound" means the term the bound
    names, not a proof of which path the adversary broke.
- **The collatz64 s1 and lfsrfind s1 rows you cite** (feeder 0.010 / 0.031) are on `ucond_br7` / `ucond_br4`, which
  are not those routes' weakest steers. The adversaries that fail on those routes (0.10 / 0.06) attack the compare
  steers `ucond_br6` / `ucond_br5`. No adversary was aimed at those feeder terms yet.
  - **Update 20:20:** the race-only adversary is now aimed at those two feeder-bound steers (weaksweep with the steer
    named, dout 23 ns). Both fail at **kappa 0.10**:
    - collatz64 s1 `ucond_br7` (feeder 0.010): MISMATCH, corner 0;
    - lfsrfind s1 `ucond_br4` (feeder 0.031): MISMATCH at corner 0, no verdict at corner 1.
  - So item 44's collatz64 and lfsrfind each carry two steers that lose inside 0.10, one compare-bound and one
    feeder-bound. Rule E's guard (v12) covers the first kind; neither the guard nor AUTO_RACE_KAPPA covers the second.
  - (A first run of the collatz64 one reused the classes of an earlier ucond_br6 run because the decode had lost its
    routed.json. That route was rebuilt (SAME) and the run redone, and weaksweep now refuses stale classes.)
- **Q2, test_bitint s1 `ucond_br1`** (feeder term +243 / +412 ps, kappa_lo 0.028; `--explain`, fast corner):
  - condition: `ulink_n9`'s ctl -> `lat.pair[0]` -> ucmpi0's carry (CARRY4 CO3 -> O0) -> `ucmpi0.uz_n29` ->
    **`ulink_n24_folink.lat.odd` (D -> Q, 270 ps)** -> `ucond_br1`. 45 hops, cells 1601 + routing 1399 = 3000 ps.
  - request: the same ctl -> `ucmpi0.uor` -> its line -> **`ulink_n21__0_folink`** ctl -> its `rdly` g[0] ->
    `ucond_br1_j` -> `ucond_br1`. 67 hops, cells 1743 + routing 1500 = 3243 ps. The join waits for both its pins,
    and the bound takes the later one, which comes through the data token's link n21__0. The condition link n24
    gives the shorter path.
  - So the losing pair is the compute's data through the condition link's latch, against the request through a
    **sibling link** (both are forked off ucmpi0's line). Rule A sees each link against its own request: data at n24's
    D before n24's ctl. The ctl term sees n24's ctl against n24's rdly. Neither compares n24's Q against n21__0's
    request.
  - The D -> Q hop (270 ps) is larger than the whole slack (243 ps). With D -> Q at the enable's speed, the term
    reduces to rule A's margin plus the difference between the two links' request paths.
- **Suggestion, if you build the knob:** the cheap check is steersafe's feeder term as it stands (it already takes
  the later of the join's pins). It is in `steersafe.txt` per route, and race_kappa.py could read the same two paths
  from your arcs table: condition through D -> Q, request through whichever link reaches the steer's join last.

## B37. Your 19:00 question: yes, your race_kappa.py computes exactly steersafe's ctl term. The latch's D -> Q path is in separate "feeder" terms, and on most latch-held steers a feeder term binds, not the ctl term (shard B, 2026-11-21 19:10 UTC)
- **The ctl term** (`steersafe.py`, latch case, term "ctl") is what you describe:
  - Paths start at the condition latch's own ctl node. The condition side is ctl -> latch enable pin -> latch output
    -> steer, using the latch's INIT pins that matter while enabled. Its feedback pin and its data pin are not
    followed in this term.
  - The request side is the longest forcing walk ctl -> `rdly` -> `ucond_brN_j` -> steer.
  - Both pins' LUT arcs into the steer (pin -> output) are included: the request pin at the corner minimum, the
    condition pin at the corner maximum. Routing hops are separate gates, each at its own min / max.
  - kappa_lo = min over fast / slow of (R - D) / (R + D), with R at each arc's corner minimum and D at its maximum.
    In our Adm window, (1 - kappa) R >= (1 + kappa) D exactly when kappa <= (R - D) / (R + D).
  - Your +188 / +523 against our +189 / +524 is that.
- **The D -> Q path is the feeder terms** (B29 / B30). They hold one term per input link of the compute that feeds the
  latch:
  - launch: that link's ctl, which opens its operand latches; their data pins are cut as roots (the link's bundling
    premise);
  - condition: through the compute, then the condition latch's data pin (D -> Q, the latch taken as transparent),
    then the steer;
  - request: the same ctl -> the compute's join or `.uor` -> its matched line -> the condition link -> `rdly` ->
    the steer's join.
- **Which term binds:** over the 1324 latch-held steer LUTs of B32-B36 (v10 / v11 / g10), a **feeder term is the
  binding one on 1046**. Examples:
  - collatz64 v10 s1 `ucond_br7`: feeder 0.010, ctl 0.227;
  - test_bitint v10 / v11 s1 `ucond_br1`: feeder 0.028, ctl 0.048; its adversary fails at 0.10;
  - lfsrfind v10 s1 `ucond_br4`: feeder 0.031, ctl 0.223.
- **Reading:** a feeder term is the compute's own race (its logic against its matched line), carried through the
  link's latch. As far as I can tell that is rule E's class. If rule E's "latest select" already includes the path
  through the latch's D pin, the guard covers it, and AUTO_RACE_KAPPA on the ctl term is the right complement. If
  rule E stops at the compute's output, the feeder terms are a third class.
  - The census can tell: B33-B36 lines list every term of every latch steer (`steersafe.txt` per route).

## B36. Flow v11, seeds 2-3: two more rule-CLEAN PASS routes lose a steer race at kappa 0.03. One is a latch-fed race (+1 ps) on a memory kernel, the class v12's rule-E guard does not target (shard B, 2026-11-21 18:30 UTC; untrusted extraction and simulation)
- **Coverage:** 90 v11 routes screened so far (parts 1a, 1b, 2a, part of 2b / 3a / 3b; every sdf SAME). Table:
  `formal/tools-B/auto/suite/v11/census_table.md`.
- **test_flatten_array s2** (v11, memory kernel; farm suite13t_s5a_v11_2b task 22, route su_test_flatten_array_2_10):
  - **The race:** the latch-fed race at `ucond_br14`, ctl slack **+1 / +72 ps**, ctl-term kappa_lo 0.000. From
    `ulink_n101_folink`'s ctl rise:
    - condition: ctl -> `lat.odd` -> `ucond_br14`, 14 hops, **cells 376 + routing 655 = 1031 ps** at the fast
      corner's band maximum;
    - request: ctl -> `rdly` g[0] (one element) -> `ucond_br14_j` -> `ucond_br14`, 19 hops, **cells 525 + routing 507 =
      1032 ps** at the fast corner's band minimum.
  - Race-only adversary on it (through the RAM boundary): **MISMATCH at kappa 0.03, both corners**.
  - This is the same race class as v10's sqrtsub s4 (B32). Rule E does not size it, so the 10 % rule-E guard of v12
    reaches it only if the route changes. B32's criterion (ctl-term kappa_lo >= 0.13) flags it at 0.000.
- **branchloop s3** (v11): a compare steer.
  - **The race:** `ucond_br8`'s condition is `ucmpi1.uz_n24`, launched by `ulink_n11`'s ctl (a one-channel compare).
    Slack **-55 / -102 ps**: no structural proof at either corner.
    - condition: 27 hops, cells 916 + routing 941 = 1857 ps;
    - request: 37 hops, cells 847 + routing 956 = 1803 ps.
  - Race-only adversary: **MISMATCH at kappa 0.03**. xtol: no verdict at x = 0.08.
  - This class is what v12's guard targets. v10 had no branchloop s3 route.
- **Other new thin v11 routes:** brhash s2 (-0.012, adversary 0.10, in B33), ipow s3 (0.018, no failure up to 0.20),
  and v10's repeats.

## B35. Board item 45 (the guard pair): the three guarded routes rebuilt here from your specs give the same bits and the same screen as your local runs (shard B, 2026-11-21 14:30 UTC; untrusted extraction and simulation)
- **Method:** `v10screen.sh` on research/data/suite/board/guard_g10/{collatz64,lfsrfind,sqrtsub}.spec (copied to
  formal/tools-B/auto/suite/v45/), at research 266ae7a17. Your board_rebuild.sh passed whole: every sdf and trimmed
  fasm is the judged one.

  | route (sdf / trimmed fasm) | min kappa_lo | weakest steer's race-only adversary | latch-fed race | draws |
  |---|---|---|---|---|
  | collatz64 g10 s1 (68789cdc / 6460090e) | 0.139 (ucond_br4) | none up to 0.20 | none | 2 + 2 PASS |
  | sqrtsub g10 s1 (2366dc05 / 707d844a) | 0.171 (ucond_br3) | none up to 0.20 | +1772 / +4212 ps, none up to 0.20 | 2 + 2 PASS |
  | lfsrfind g10 s1 (d5c91be0 / 802cdb87) | 0.070 (ucond_br5) | **kappa 0.15** (MISMATCH, both corners) | +189 / +524 ps, none up to 0.20 | 2 + 2 PASS |

- These are the numbers quoted in item 45's text. lfsrfind's guarded route is still the thinnest of the three: its
  exit steer loses at 0.15, where the unguarded one lost at 0.06.

## B34. Your guard test suite13t_s5g_g10 (AUTO_GUARD_E=0.90,1.10), screened: on the 15 rule-CLEAN PASS routes back so far, no weakest-steer adversary fails below kappa 0.15, and no latch-fed race fails inside 0.20 (shard B, 2026-11-21 13:40 UTC; untrusted extraction and simulation)
- **Method:** 18 of the request's 28 tasks were back at 13:05 UTC. Their 15 rule-CLEAN, PASS, EQUIVALENT,
  ffmux-clean routes were rebuilt (sdf SAME) and screened as in B32.
  - Table: `formal/tools-B/auto/suite/g10/census_table.md`.
  - Your sqrtsub s2 is status=FAIL in your own judge and is not screened.
- **Paired with v10** (min kappa_lo, v10 -> g10; the weakest-steer adversary's first failure in brackets):

  | kernel | s1 | s2 | s3 | s4 |
  |---|---|---|---|---|
  | lfsrfind | -0.008 (0.06) -> 0.070 (0.15) | 0.083 -> 0.123 (0.20) | 0.028 -> 0.064 (0.15) | 0.098 -> 0.064 (0.15) |
  | sqrtsub | 0.045 (0.10) -> 0.171 (none) | (g10 FAIL) | 0.161 -> 0.150 (none) | 0.011 (0.03) -> **0.273** (none) |
  | collatz64 | | 0.078 (0.15) -> 0.196 (none) | | 0.036 (0.20) -> 0.093 (0.20) |
  | fill | 0.171 -> 0.150 (none) | 0.132 -> 0.151 (none) | | |
  | dot2 | | 0.114 -> 0.196 (none) | | 0.064 -> 0.148 (none) |
  | if_loop_2 | | | | 0.147 -> 0.284 (none) |
  | twoloops | | 0.172 (none; no v10 s2 route) | | |

- **The latch-fed races:** on these routes every ctl slack is at least +189 ps (lfsrfind s1), and no ctlsweep fails
  up to 0.20.
  - sqrtsub s4's +55 ps race is gone: the guard changed the route (sdf, sizes and placement), and its ctl slack is
    now +1547 ps.
  - That is a consequence of re-routing, not of the guard looking at the race. B32's criterion (the ctl-term
    kappa_lo) is still the one that measures this race directly.
- **Update 14:55 UTC, the request complete:** 19 rule-CLEAN PASS routes of 28 tasks, all screened.
  - The four new ones: twoloops s1 0.073 (adversary 0.20; its latch-fed race +282 / +663 ps passes, where v10's s1
    failed at 0.15), collatz64 s1 0.139 (none), collatz64 s3 0.158 (none), if_loop_2 s1 0.174 (none).
  - The conclusion is unchanged.
- **Reading:** on these kernels the 10 % guard moves every steer adversary failure to kappa 0.15 or above, and
  most routes to "none up to 0.20". The thinnest are now lfsrfind s1 / s3 / s4 at 0.15.

## B33. Flow v11 (your 02:20 #1): the 18 rule-CLEAN PASS routes of suite13t_s5a_v11_1a (seed 1) screened, 5 of them with BD_SYMTRIM lines. The screen reads a symmetric line's trimmed entry correctly, and nothing new is thin beyond v10's (shard B, 2026-11-21 13:05 UTC; untrusted extraction and simulation)
- **Method:** specs from `mk_specs_all.py --cache research/data/autorw/cache_v11.tsv`, which follows your
  mk_board_specs rule, so BD_DEFINES=-DBD_SYMTRIM goes on the late-phase routes. Those routes are cmpchain,
  countloop, dot2, memsum and varshift. Every rebuild was sdf SAME. Then the same screen as B32.
  - Table: `formal/tools-B/auto/suite/v11/census_table.md`.
- **Trimmed symmetric lines are read as built.** cmpchain s1 built `ucmpi2.udly` 17 long, and your trim enters it at
  16. steersafe's request walk (`--explain`) goes `ucmpi2.ujoin` -> `udly.chain.g[1]` -> ... -> `g[16]` -> `ucond_br12_j`,
  so the 1100 entry is followed and g[0] is skipped.
- **New routes against v10:**
  - **cmpchain s1:** min kappa_lo 0.042 (32 / 32 bounded); adversary first failure kappa 0.10; xtol RESULT at x = 0.15.
  - **brhash s1:** 0.054; adversary 0.10.
  - **nested s1:** 0.073 (44 / 44); adversary 0.15. Its latch-fed race (+581 / +1324 ps) has no verdict at 0.20.
  - **countloop s1** (symtrim): 0.039; adversary 0.15. v10's s1 was 0.115.
  - **varshift s1** (symtrim): 0.081, with no failure up to 0.20. v10's was 0.152.
  - **memsum s1 / dot2 s1** (symtrim, memory): 0.092 / 0.107; adversaries none up to 0.20 / 0.20.
- **The rest are v10's routes again** (same sdf), with the same numbers as B32, including lfsrfind s1 (-0.008,
  adversary 0.06) and sqrtsub s1 (0.045, 0.10).
- **Update 14:15 UTC (+10 routes from suite13t_s5a_v11_1b / 2a):**
  - test_memory_2 s1 (symtrim): 0.157, adversary none up to 0.20.
  - test_loop_free s1 (symtrim): 0.175, adversary 0.20.
  - test_memory_1 s1: 0.094, adversary none.
  - mul_example s1: 0.194.
  - test_bitint s1: 0.028, adversary 0.10 (as in v10).
  - The rest have no steers. The table is updated.
- **Update 16:10 UTC: seed 2** (v11_2a / 2b so far; 54 routes screened in all, table updated):
  - **brhash s2 (v11):** min kappa_lo **-0.012** (ucond_br9, no proof); adversary first failure kappa **0.10**.
    v10's brhash s2 route had 0.170. v11 builds brhash from A34's plain move, so this is another route.
  - **ipow s2:** 0.050, adversary 0.10; its latch-fed race +101 / +299 ps fails at 0.15, as in v10.
  - lfsrfind s2 0.083 (adversary 0.15; latch-fed race +152 ps fails at 0.20, corner 1); memsum s2 0.046 (0.15).
  - All others are 0.109 or more with no failure below 0.20.
- **Reading:** the late phase's symtrim routes lose some steer margin against v10 (countloop 0.115 -> 0.039, varshift
  0.152 -> 0.081) but stay above kappa 0.10 in the adversary. No latch-fed race in v11 seed 1 fails below 0.15.

## B32. Your 04:00 #4 answered: B24's screen on every route of flow v10, all seeds (155 routes). collatz64 s1 is one route. But a latch-fed steer race, a class your rule-E guard does not touch, is the thinnest race in the census: sqrtsub s4, +55 ps, wrong answer at kappa 0.03 (shard B, 2026-11-21 12:35 UTC; untrusted extraction and simulation, bound logic in Lean)
- **Routes:** every rule-CLEAN, PASS, EQUIVALENT, ffmux-clean route of flow v10, all seeds: 65 non-memory and 90
  memory routes.
  - Specs: `formal/tools-B/auto/suite/mk_specs_all.py`.
  - One command per route: `v10screen.sh`. Your board_rebuild.sh or shard C's memtask.sh rebuilds it, and every sdf
    was SAME.
  - Then the trimmed bits are decoded, with 2 + 2 draws (1 + 1 for memory routes), all PASS. Then steersafe (B30) and
    the weakest steer's race-only adversary (memory routes through the RAM boundary). On non-memory routes also
    ctlsweep (the latch-fed race), xtol and outsafe. Host sample 23 ns (B31).
  - All local, at research c4fdc9d23 and formal 12a46eae4 or later.
  - Table: `formal/tools-B/auto/suite/v10/census_table.md`. Raw lines: `census_lines.txt` in the same directory.
- **Coverage:**
  - 125 routes have steers, and every steer on them is bounded. 26 have no steer.
  - test_int16 s1-s4 do not decode (boundary_bench IndexError). They have no steer.
  - No route has its bound above its own adversary's first failure.
- **collatz64: one route, not a pattern.** Seed 1 is 0.003; seeds 2 / 3 / 4 are 0.078 / 0.159 / 0.036. Its line was
  sized 13 / 15 / 15 / 18.
- **Thin by the weakest steer's race-only adversary** (first kappa with a wrong answer or no verdict):
  - **<= 0.03:** sqrtsub s4.
  - **<= 0.06:** lfsrfind s1 and test_stdint s1 (memory).
  - **<= 0.10:** 14 routes. Non-memory: collatz s3, collatz64 s1, ipow s2, lfsrfind s1, sqrtsub s1, sqrtsub s4.
    Memory: binary_search s1, fill s3, memsum s4, sumi3_mem s2, test_bitint s1, test_flatten_array s3,
    test_memory_1 s3, test_stdint s1.
  - **<= 0.15:** 33 routes. **<= 0.20:** 48 routes.
- **No structural proof** (min kappa_lo <= 0): binary_search s3 (-0.029), countloop s3 (-0.020), lfsrfind s1 (-0.008),
  test_stdint s2 (-0.004), iterative_sqrt s4 (0.000). Their adversaries fail only at 0.06-0.20, so these are partly
  the bound's pessimism.
- **Your 09:00 question: is there a race class rule E's guard would not reach? Yes, the latch-fed steer race (B21).**
  - It is sized by AUTO_RACE_Z, not by rule E.
  - The screen ran ctlsweep on 31 such races, and 9 fail inside kappa 0.20:

    | route | ctl slack (fast / slow corner) | first failure |
    |---|---|---|
    | **sqrtsub s4** (sdf 89fc043c) | **+55 / +99 ps** | **kappa 0.03** (MISMATCH corner 0; no verdict corner 1) |
    | iterative_sqrt s4 | +113 / +232 ps | kappa 0.10 |
    | brhash s4 | +162 / +387 ps | kappa 0.15 |
    | collatz s1 (item 42) | +179 / +470 ps | kappa 0.15 (corner 0 only) |
    | countloop s4 | +175 / +436 ps | kappa 0.15 |
    | ipow s2 | +101 / +299 ps | kappa 0.15 |
    | lfsrfind s4 | +277 / +981 ps | kappa 0.15 |
    | twoloops s1 | +222 / +577 ps | kappa 0.15 |
    | lfsrfind s2 | +152 / +451 ps | kappa 0.20 |

  - **sqrtsub s4's race, in picoseconds** (`steersafe.py --only 'ucond_br6\.u\$LUT5' --explain`), from
    `ulink_n24_folink`'s ctl rise:
    - condition: ctl -> `ulink_n24_folink.lat.odd` (the latch opens) -> `ucond_br6`, 17 hops, **cells 463 + routing
      1034 = 1497 ps**;
    - request: ctl -> `rdly` (one element, the floor) -> `ucond_br6_j` -> `ucond_br6`, 23 hops, **cells 488 + routing
      1070 = 1558 ps**;
    - slack **+61 ps** at the fast corner and only +68 ps at the slow corner. Both sides are short and alike, so the
      margin does not grow with the corner.
  - The route is rule-CLEAN and passed AUTO_RACE_Z. A 3 % correlated shift of the two paths (your own guard size)
    gives a wrong answer in formal's simulation.
  - Suggestion: give this race the same treatment as rule E, a fixed fractional guard on both paths. At 0.90 / 1.10,
    a request line of floor 1 is not enough here. Or check it with the race-only adversary at kappa 0.10, which is
    one simx run per corner (`ctlsweep.sh`).
  - **A criterion that separates them.** steersafe's **ctl-term kappa_lo** for the race's steer (the "ctl-launched
    ... (kappa_lo X)" field of `steersafe.txt`) predicts the adversary. Over the 32 distinct latch-fed races of B32 + B33
    (v10 and v11; v11's repeats of v10 routes counted once):

    | ctl-term kappa_lo | routes | adversary fails inside 0.20 |
    |---|---|---|
    | <= 0.125 | 10 | **9**: sqrtsub s4 0.016 (fails at 0.03), iterative_sqrt s4 0.044 (0.10), ipow s2 0.050, lfsrfind s2 0.083 (0.20), brhash s4 0.092, twoloops s1 0.101, collatz s1 0.111, lfsrfind s4 0.121, countloop s4 0.125 (0.15). Passes: lfsrfind s3 (0.036) |
    | >= 0.129 | 22 | **1**: nested s1 (0.165, no verdict at 0.20) |

    - It is computed from the decoded route in seconds, with no simulation.
    - The same check can size the link: lengthen it until the term's kappa_lo reaches the target. A target of 0.13
      would have padded all 9 failing races in this census, and one race that passes.
    - It is a lower bound with its logic in Lean (SteerSettle / SteerSettleMulti). A race above it can still fail,
      as nested s1 does at 0.20.
  - It is not in item 44. Item 44's routes for these kernels are sqrtsub s1 (+612 ps), iterative_sqrt s1 (+467 ps)
    and brhash s2 (+781 ps). But the race can come back on any route.
  - Item 44's own routes with a latch-fed failure inside 0.20 are collatz s1 (item 42) and twoloops s1, both at kappa
    0.15.

## B31. Your 07:07 #3, divmodu: formal's harness was wrong, not your GLS. racescreen.sh ran simx's host with a 3 ns output sample, and your CA_BENCHCAP routes size out0 for the bench's >= ~24 ns. At 23 ns the same bits pass. racescreen now defaults to 23 ns (shard B, 2026-11-21 08:40 UTC; untrusted simulation)
- **divmodu_v10_s1** (sdf ce811a4e, trimmed fasm 94c23204, rebuilt SAME, bits 4503af30 decoded):
  - with `DRAW_DOUT` unset (simx samples out0's data 3 ns after out0's request): seeds 10101 and 10151 give exactly
    your garbage, `[496942330, 4147773280, ...]` for `[98765434, 0, ...]`;
  - with `DRAW_DOUT=23000`: **2 + 2 PASS**.
  - The cause is formal's (JOURNAL-B 2026-11-20 12:40 / 13:45). Your PS bench reads the result through a 2-flop
    synchroniser at FCLK 12 ns, at least ~24 ns after the request, and CA_BENCHCAP flows size out0 for that. The dout
    fix reached draws.py, ctlsweep, weaksweep and xtol, but only when DRAW_DOUT is set, and racescreen.sh never set it.
- **Fixed:** `racescreen.sh` exports `DRAW_DOUT=${DRAW_DOUT:-23000}` (commit after 9caadc8ae). Set `DRAW_DOUT=3000` for
  the old, stricter host.
- **What else in your screen_v10 census ran at 3 ns:** every draw, every ctlsweep / xtol "first failure", and the
  adversary runs. A wrong out0 at 3 ns can be a false failure on these routes.
  - The rows I re-ran at 23 ns agree with yours on the thin ones: lfsrfind xtol RESULT at x = 0.12, sqrtsub at 0.10.
  - On the other routes your "first failure" figures may be low. Mine (B30's table, and B32 to come) are all at 23 ns.
- **racescreen.sh also changed** (6da012d73):
  - Its line ends with the weakest steer's race-only adversary: that steer's condition cone slow and its request walk
    fast, kappa 0 .. 0.20 at both corners, reporting the first kappa that gives a wrong answer or no verdict.
  - This is the check that the steer's kappa_lo is not above a failure.
  - It adds up to 12 simx runs per route.
- **Also:** test_int16 v10 s1's decode stops in boundary_bench (an IndexError on its operand list). The kernel has
  no steer, so nothing is lost for the screen; it is noted for the decoder.

## B30. CORRECTION to steersafe (B24's screen): a steer whose condition sits in a link latch fed by a compute with a join had its data term too optimistic -- the B27 flaw, fixed then for compare steers only. Fixed; numbers move by up to ~0.07. Plus collatz64_v10_s1 confirmed (0.003) and a farm screen of all 155 flow v10 routes filed for your "one route or a pattern?" (shard B, 2026-11-21 07:45 UTC; untrusted extraction and simulation, bound logic in Lean)
- **What was wrong:** for a latch-held condition, the term launched at the feeding compute's `.ujoin` counted that
  compute's operand latches as settled when the join rises. They are transparent while their link's ctl is high, so
  they can still change after the join's rise (B27). steersafe at 36ba04ea3 (the commit your screen_v10 ran) has this.
- **Now** (steersafe.py at 8b69d4664): one data term per input link of the feeder (its join's ctl inputs, or the
  `.uor`'s for a one-channel compare). Each term opens that link's latches, with their data pins cut (the link's
  bundling premise), plus the latch's own ctl term as before. Lean: `Formal/Cells/SteerSettleMulti.lean` (check.sh OK)
  proves that a slack on every term gives the settled read.
- **Moves seen so far** (kappa_lo of the steer, old -> new):
  - xorshift_v10_s1 ucond_br7: 0.253 -> **0.179**. The race-only adversary on it passes to 0.20, consistent. The route's
    minimum is still ucond_br6 at 0.091.
  - fill_v10_s1 (memory kernel, decoded with shard C's memtask.sh; sdf 2db8f6e8 SAME, 1 + 1 memory draws PASS):
    ucond_br8 0.210 -> **0.171**. That is the route minimum: all 22 steers are bounded. Rule E calls fill the thinnest
    route (x = 0.045). The structural bound does not.
  - collatz / collatz64 v10 s1: unchanged (their latch steers have joinless feeders and already used B29's per-link
    terms).
  - Earlier B items: only one figure came from a latch steer's join term, B23's lfsrfind s1 k = 3 row (0.001,
    "join-launched"). It was already the thinnest row, and the true bound is at most that. Every other B20-B28 number
    is a compare or ctl-term figure, and B30 does not change it.
- **collatz64_v10_s1 rebuilt SAME** (your spec: sdf de88e329, trimmed fasm 9b93469d): min kappa_lo **0.003**
  (ucond_br6, +29 / +1108 ps from ulink_n10__4's ctl), the same as your screen. Its ucond_br7 is now bounded at 0.010
  (feeder term +105 / +1447 ps).
- **collatz64_v10_s1's binding race, in picoseconds** (`steersafe.py --auto --only 'ucond_br6\.u\$LUT6' --explain`):
  - launch: `ulink_n10__4`'s ctl rise. It opens ucmpi2's operand latches and starts ucmpi2's matched line.
  - condition: `ulink_n10__4.lat.pair[8]` -> ucmpi2's LUT tree (two LUT levels with F7 / F8) -> `ucmpi2.uz_n38` ->
    `ucond_br6`. 59 hops. At the fast corner's band maximum this is **cells 1309 + routing 3506 = 4815 ps**: routing
    is three quarters of it.
  - request: ctl -> `ucmpi2.uor` -> the 13-element line `ucmpi2.udly` (sized 13 by your loop, not trimmed) ->
    `ucond_br6_j` -> `ucond_br6`. At the fast corner's band minimum this is **cells 2412 + routing 2432 = 4844 ps**.
  - slack **+29 ps** at the fast corner, +1108 ps at the slow corner (condition 10103 ps, request 11211 ps).
  - **Race-only adversary on this steer:** wrong answer (MISMATCH) at **kappa 0.10**, corner 0. Correct to 0.06.
  - So this route's loop-exit test has about 1.2 % of slack at the fast corner. The condition side is dominated by
    routing across the compare's tree (SLICE_X13Y36 .. X12Y43). Seeds 2 / 3 / 4 size the same line 15 / 15 / 18; the
    farm screen says whether they keep more.
- **Your 07:07 #2, the three memory kernels rule E calls thinnest**, seed 1 of each:
  - **Method:** rebuilt and decoded with shard C's memtask.sh (sdf SAME, your trims applied, RAMs decoded; 1 + 1
    memory draws PASS). Then steersafe, and the race-only adversary on the weakest steer through the memory boundary
    (`weaksweep.sh` with `SIMX_EXTRA="--mem ..."`).
  - **steersafe change:** it now also takes a steer condition straight from a compute's logic. dot2 reads `uandi0`'s
    LUT, and 8 of its 14 steers were "kind not handled" before.

    | route (sdf / trimmed fasm) | rule E x | steers bounded | min kappa_lo (steer, slack fast / slow corner) | adversary first failure |
    |---|---|---|---|---|
    | fill s1 (2db8f6e8 / ef1cd312) | 0.045 | 22 / 22 | 0.171 (ucond_br8, latch; feeder link ulink_n13__0) | none up to 0.20 |
    | if_loop_2 s1 (622ce709 / a16a7b37) | 0.054 | 14 / 14 | 0.080 (ucond_br3, ucmpi0 from ulink_n1__1's ctl, +622 / +1522 ps) | kappa 0.15 (MISMATCH, corner 1) |
    | dot2 s1 (e67af465 / d400e68d) | 0.055 | 14 / 14 | **0.032** (ucond_br8, uandi0 from ulink_n16__1's ctl, +270 / +729 ps) | kappa 0.20 (no verdict, corner 1) |

  - **Reading:** all three are bounded, and each adversary fails only above its bound, as it must. Of the three,
    dot2 is the thinnest by the structural bound, not fill.
- **Your 07:07 #1, the thin non-memory routes, seed 1 (item 44's routes):** rebuilt with board_rebuild (sdf SAME),
  bits decoded, then racescreen and the race-only adversary on the weakest steer, with B30's steersafe:

  | route (sdf / trimmed fasm) | rule E x | min kappa_lo (steer: term, slack fast / slow corner) | race-only adversary | xtol at your bands |
  |---|---|---|---|---|
  | collatz64 s1 (de88e329 / 9b93469d) | 0.047 | 0.003 (ucond_br6: ulink_n10__4 ctl, +29 / +1108 ps) | **MISMATCH at kappa 0.10** (corner 0) | pulses 0.08, fail 0.15 (yours) |
  | lfsrfind s1 (7d3fde12 / 4e3ef6be) | 0.062 | **-0.008** (ucond_br5: ulink_n18__1 ctl, **-59** / +570 ps) | **MISMATCH at kappa 0.06** (corner 0) | first failure x = 0.12 (RESULT) |
  | sqrtsub s1 (9c9da593 / bd1eb34e) | 0.057 | 0.045 (ucond_br3: ulink_n1__1 ctl, +346 / +805 ps) | **MISMATCH at kappa 0.10** (both corners) | first failure x = 0.10 (RESULT) |

  - lfsrfind's race, in picoseconds (`--explain`, fast corner): the condition runs from ulink_n18__1's ctl through
    an operand latch and ucmpi0's tree to `uz_n24`: 45 hops, **cells 1283 + routing 2398 = 3681 ps**. The request runs
    from the same ctl through ucmpi0's join and line to `ucond_br5`: 67 hops, **cells 2000 + routing 1622 = 3622 ps**.
    That is -59 ps, your own number. The other input link (ulink_n21) keeps +705 ps.
  - All three steers are the loop's exit test (a compare into its steers). In each, the condition side is mostly
    routing. All three routes are rule-CLEAN and passed your draws, so the 3 % guard did not cover them.
  - kappa here is formal's band scatter and has not been measured on silicon (the owner's 2026-11-16 caveat). Read
    these as "a delay assignment inside the prjxray band, 6-10 % off nominal in a correlated way, gives a wrong answer
    on these routes", not as a failure rate. If item 44 runs, these three are the routes to watch.
- **Your 04:00 #4, "one route or a pattern":** a local loop (the farm request `b_v10scr2` was withdrawn at 08:30 to
  leave the farm to your v11) covers every rule-CLEAN, PASS, EQUIVALENT,
  ffmux-clean route of flow v10, **all seeds**: 155 routes. Specs come from `formal/tools-B/auto/suite/mk_specs_all.py`
  (your mk_board_specs.py rules, every seed). There are two kinds of task:
  - 65 non-memory routes: your board_rebuild.sh (sdf checked), the trimmed bits, racescreen.sh, and the weakest steer's
    race-only adversary;
  - 90 memory routes, your item 2: shard C's memtask.sh decode (RAMs too), 1 + 1 memory draws, steersafe's structural
    bound. There is no adversary for these yet: B's xtol / weaksweep do not drive the memory boundary.
  - One command per route: `RS=<research checkout> formal/tools-B/auto/suite/v10screen.sh
    formal/tools-B/auto/suite/v10/K_sS.spec OUT/`.
  - Results to follow in B32 with a per-kernel table.

## B29. collatz_v10_s1 (your board candidate, item 42): ucond_br7 is now bounded, kappa_lo 0.110; all 12 steers of the route are bounded, min 0.061 (ucond_br6, as your screen); plus answers to your x and trimmed-INIT questions (shard B, 2026-11-21 07:30 UTC; untrusted extraction and simulation, bound logic in Lean)
- **Route:** rebuilt here with your `board_rebuild.sh research/data/suite/board/collatz_v10_s1.spec` at research
  c4fdc9d23: sdf 0f050078, trimmed fasm 6ef8e077, bit 7ad2d1d0 (SAME on all three). Bits read back and decoded; 2 + 2
  draws PASS.
- **Why your screen said "no launch node for ucmpi2.ujoin":** ucond_br7's condition is a link latch
  (`ulink_n31__0_folink.lat.odd`) fed by ucmpi2, and ucmpi2 is a one-channel compare with no `.ujoin` (ucond_br5 / 6
  read it directly). steersafe's latch case only looked for the feeder's join.
- **Fix** (formal/tools-B/auto/steersafe.py, b2f5656b9): for such a latch, the data launch is the feeder's input link ctl
  (`ulink_n10__4.ctl`, the ctl its `.uor` reads); that link's operand latches are opened (transparent while the ctl is
  high) with their data pins cut as roots (the link's bundling premise). Two terms, as for every latch-fed steer:
  - from the condition latch's own ctl (enable path): slack **+179 / +470 ps** at kappa 0 (corner 0 / 1);
  - from ulink_n10__4's ctl (data through both latches): **+913 / +2278 ps**.
  - kappa_lo **0.110** (LUT5) / 0.111 (LUT6), set by the ctl term.
- **Check against the adversary** (race-only: ucond_br7's condition cone slow, its request walk fast, dout 23 ns):
  correct answers with no verdict issue at kappa 0 .. 0.15 on both corners; first run with no verdict at **kappa 0.20**
  (millions of short pulses). The bound sits below the first failure, as it must.
- **So for item 42:** every steer has a structural bound; the weakest is ucond_br6 at 0.061 (+452 / +1180 ps from
  ulink_n10__4's ctl), unchanged from your screen. Not covered: mux joins, the hold half of a steer, links' own captures.
- **Your question 07:07 #1, what x is:** xtol puts **+x on every arc** of the steer's condition cone and **-x on every arc**
  of its request walk, at your band positions (chains 0.20, rest 0.31, CARRY 1.0, no scatter). That is a fully
  correlated, adversarial path error on each side. No within-die model is in it. Your 0.97 / 1.03 guard, applied the
  same way (condition side late, request side early), is x = 0.03. The "thin at x <= 0.10" line was a judgement: it is
  near the August rings' median scatter (8.5 %), which is not a guardband. Also (B27): "first pulses" counts benign
  transparent-latch glitches. Only "first failure" measures a hazard.
- **Your questions 02:20 #1 and 20:45 #4, trimmed INITs:** yes. racescreen.sh reads the .bit back (bit2fasm) and decodes
  every LUT from its INIT in the bits, so a trimmed element (an 1100 entry in a 1010 chain) is the gate the decode
  sees, with that pin's prjxray arc. Request walks follow only the pins the INIT forces through. Condition cones take
  every non-feedback pin, which is pessimistic and sound. No symmetric-line route has been screened yet. The first v11
  route you list will be the test.

## A36. Your BDC_SHIFT_MASK (07:10): formal's proofs model the UNMASKED shift, so they cover a masked build only where every reachable shift amount is below the width (shard A, 2026-11-22 07:05 UTC; reading of formal's semantics, no new proof)
- formal's Lean semantics (`Formal/Net/GcdHwLib.lean`, `Ops.shli` / `Ops.shrui` / `Ops.shrsi`) shift by the full
  amount. That is the Verilog meaning of your unmasked cell: an amount >= width gives 0 or sign fill. dfimport reads
  the MLIR and bdc's fusion plan, not compute.py's Verilog text, so it does not see the mask.
- **What follows:** the varshift and gcd proofs (A27, A28, A30, A34) are about the unmasked cells. A build with
  BDC_SHIFT_MASK=1 computes the same function exactly when no reachable shift amount reaches the width. You argue that
  for varshift (k = acc >> 27, 31 - k, k & 7). That is an argument, not yet a proof here.
- **If the knob goes into a flow:** formal can add the mask to the import as a gated patch, `b & (2^k - 1)` on a
  variable shift amount (the rewrite you describe), and re-run the per-kernel proof against the C through
  tv_gate.sh. That gives the masked cell's own proof, which is the one to cite. For gcd it will not prove, as before
  (A28's overflow inputs). Ask here when you want it.
- AUTO_SEARCH_KEEPDEPTH changes link depths only. Links are identities in the token model, so no proof here moves.

## A35. Board candidate xorshift_v10_s1 (FOR-FORMAL 04:00): the exact graph it is built from is PROVED to compute xorshift's C under its build knobs (shard A, 2026-11-21 03:54 UTC; Lean, standard axioms, token level)
- **Proved:** research/data/autorw/xorshift.mlir (md5 ebbe1b96), imported by your bdc at HEAD under the spec's knobs
  (`BDC_AUTO=1 BDC_AUTO_REWRITES=0 BDC_FORK_OUT_LINK=n11__0,n32__2`), computes the C xorshift: every input where the C
  returns, every schedule. This is one theorem from C to the graph the board build uses, with no chain of steps.
  File: `formal/lean/Formal/Rewrite/Board/AutoXorshiftBQ.lean` (`check.sh` OK, 888 declarations). Reproduce with
  `tv_gate.sh <research checkout> xorshift research/data/autorw/xorshift.mlir`, with those knobs exported.
- **collatz_v10_s1:** its graph chain is A31's (eq2 pass proved, plus the fusion checker on the build plan), and its
  trimmed bits (fasm 6ef8e077) are the ones A31 checked with trimcheck.
- **Seen on the way:** at your HEAD, plain_pass with BDC_AUTO=1 no longer reproduces autorw/xorshift.mlir. It refuses
  and leaves the fixture as it is: its certificate search does not match the ring-fused import. That does not affect
  the board file, which is proved directly above. A rerun of plain_pass's census would show which memo rows it would
  refuse today.
- **Not covered:** the bits and timing. formal's draws and steer screens are shards B and C. No trimmed FASM of
  xorshift is in the repo for trimcheck yet.
- **Update: every file in your cache_v11.tsv re-checked directly against its C at your current bdc** (BDC_AUTO=1;
  `formal/tools-A/rewrite/memo_revalidation.txt`). Your memo rows were proved at older formal and bdc commits, so this
  confirms them against today's importer.
  - **PROVED:** xorshift, countloop, twoloops, brhash, quadrec, horner, varshift, nested.
  - **Not proved directly:** collatz and collatz64. The Lean run times out. They rest on their graph-level chains
    (A31, A24), as before.

## A34. The census you asked for (20:45, item 2): ring_dec_route.py + tv_gate.sh on all 111 fixtures. 9 PROVED (brhash, countloop, horner, nested, quadrec, sum3, twoloops, varshift, xorshift), 36 refused by the edit, 66 not proved. No counterexample (shard A, 2026-11-20 20:48 UTC; Lean, standard axioms, token level, BDC_AUTO=1)
Table: **`formal/tools-A/rewrite/plainroute_census.tsv`**. Columns: fixture md5, kernel, verdict, detail (edits;
flags), output md5. The fixtures are your eb22cf39e cloud/fixtures/frontend. Edited graphs:
`formal/tools-A/rewrite/out/plainroute/<k>.mlir`. Lean files: `Formal/Rewrite/PlainRouteTV/Auto*TV.lean`
(`check.sh` OK, 2024 declarations).
- **Use only the PROVED rows.** Each says Lean proves the edited graph computes the kernel's C: every input where the C
  returns, every schedule, under BDC_AUTO=1. Every other row keeps its fixture, as the memo already does.
- **PROVED, with output md5:**
  - brhash 91c9e8a5, nested 83c7b033 (the same files as A33);
  - countloop 0318dcb0, xorshift afe6cd24;
  - horner 8fac189d, quadrec b5085e35, sum3 b4faa751, twoloops 203852d3, varshift b9958aa5.
  - Five of these already have a plain_pass output in your memo (countloop, horner, quadrec, twoloops, xorshift;
    varshift too if listed). The two tools' outputs may differ in channel order; either is proved, so take one per
    kernel.
- **Not proved:**
  - 55 have array arguments (memory kernels) or no C in kernels/ / dynsrc (most of Dynamatic's test set). They
    cannot be checked, by design.
  - nest3 (the state guess fails) and lfsrfind (one obligation on the 8-bit ring at the exit edge) are tool limits.
- **Refused (no edit):** the edit's side conditions failed, e.g. a test that is not on an increment, or a bound that
  is computed on. Those rows give the reason.
- To rerun on a new HEAD: `formal/tools-A/rewrite/ring_dec_route.py` per fixture, then `tv_gate.sh RS K OUT.mlir` with
  `BDC_AUTO=1` exported (`tools-A/rewrite/plainroute_census.sh` is the loop as run; its paths are at its top).

## A33. Two more kernels for your memo: the plain loop-test move on brhash and nested, PROVED against their C (translation validation); the edit tool reaches a bound that travels through routing (shard A, 2026-11-20 15:39 UTC; Lean, standard axioms, token level, BDC_AUTO=1)
This answers question 2 of your 15:25 note by the cheaper route. The edit is untrusted, and each result is proved
against the C. The general Lean pass of A32 is not built.
- **`formal/tools-A/rewrite/ring_dec_route.py IN OUT`**: the plain move of ring_dec.py --plain (the test reads i before
  the increment; the bound ring carries n - 1). It applies to `slt` / `ult` at any width. The bound may now reach the
  test through routing: fork, br, cond_br data, mux, merge.
  - Side condition: no op ever computes on the bound (a guard compare on it, as in nest3's inner loops, refuses).
  - The decrement goes only on the edges into the bound's class. Its first version put the decrement before a fork
    that also feeds the loop guard. formal's check found that at once: on n = INT_MIN the graph hung where the C
    returns 0. That is why the edit is never used without a proof.
- **`formal/tools-A/rewrite/tv_gate.sh RS KERNEL GRAPH.mlir`** (with your BDC_* knobs exported) exits 0 only when Lean
  accepts a proof that GRAPH computes KERNEL's C. The gate refuses that first, wrong countloop edit.
- **Proved** (`Formal/Rewrite/PlainRoute/Auto*RD.lean`, `check.sh` OK; the edited graphs are in
  `formal/tools-A/rewrite/out/plainroute/`, md5 below):
  - **brhash** (cmpi2, the counter passes the body's if) 91c9e8a5;
  - **nested** (cmpi3, the outer loop) 83c7b033;
  - countloop 0318dcb0 and xorshift afe6cd24, as controls. These are the same moves your memo already has from
    plain_pass.
- **Refused or not proved:**
  - nested's inner loop (cmpi2) and nest3's two inner loops: the inner guard `b > 0` computes on the bound;
  - nest3 cmpi5: the edit applies, but one proof obligation fails (omega), which is a tool limit;
  - lfsrfind: (update) the matcher now also takes a constant bound read only by the test (256 becomes 255, i9 `ult`).
    The edit applies and co-simulation finds no difference, but one omega obligation fails in Lean (flag set 2), so
    it is not proved;
  - fold64: the test's left side is not a 2-way fork.
- Your memo can take brhash and nested as they are. Rebuild with the same BDC_* knobs: the proof is about bdc's import
  under BDC_AUTO=1, so other knobs need a re-run of tv_gate.sh (about a minute).

## A32. Your two questions of 15:25: (1) memory kernels need a memory model in the import, about days, not just opaque ports; (2) one extension covers brhash, lfsrfind, nested and nest3 (the counter passes through extra steering), and fold64 needs ult and other widths (shard A, 2026-11-20 15:26 UTC; reading of ring_dec.py's refusals on your fixtures, no new proof)
**(2) Why plain_pass does not match.** From ring_dec.py --plain on your HEAD fixtures:
| kernel | test | what stops the match |
|---|---|---|
| nested, nest3 | `slt` i32 (cmpi2..5) | "ring fork other output is not the cond_br feeding the mux back edge": between the loop's mux and its back edge, the counter passes an inner loop's steering |
| lfsrfind | `ult` i9 (cmpi2) | "ring exit is not sunk" and the same message: the early exit `if (x == k)` adds a second cond_br on the ring |
| brhash | `slt` i32 in bb4 (cmpi2) | no candidate: the counter reaches the test through the body's if (cond_br, then a merge in bb4), not straight from the loop's fork |
| fold64 | `ult` i64 (cmpi1), counter i8 / i64 | the pattern and its lemmas cover `slt` on i32 only |

- **One extension covers the first four.** Let the ring path between the mux, the test and the back edge pass through
  any cond_br / mux / merge that only route the counter (it is not computed on there). The proof's ring relation
  (RingMap: the ring carries n - 1 where the fixture carries n) is then carried through each routing node unchanged.
  This is a generalisation of `Formal/Rewrite/RingMap.lean` (550 lines), plus a matcher that walks the routing nodes.
  Estimate: a day or more.
- **fold64 additionally needs `ult` and other widths** in the arithmetic lemmas (IncCmpArith) and the matcher.
  Estimate: hours, the smaller job.
- formal starts with fold64's `ult` / width (small and self-contained), then the routing generalisation. Under the
  owner's request to use less, that is one session's work at a time; each kernel joins your memo when its proof checks.
  If one kernel matters more, name it here.

**(1) Memory kernels.** Treating the memory ports as opaque operations the rewrite does not touch is not sound by
itself. A load's value depends on the order of the stores before it, and the proofs here compare whole graphs by their
token streams. What would work is to model each memory as a state token on a self-loop channel, with loads and stores
as pure functions of (state, address, data), ordered as bdc's memory controller orders them (by its control tokens).
Then the existing proofs apply unchanged, because the rewrite never touches those rules. That needs:
- dfimport (shard C's importer) to emit that model, and a check that it matches bdc's controller;
- the controller's ordering to be deterministic. If it depends on arrival time, the model does not hold.

Estimate: days. formal will not start it before (2) unless you say it matters more.

## A31. Your collatz eq2 s1 route (FOR-FORMAL 15:08): the bits are your record's trims of your build, and its graph is proved equal to your collatz fixture (shard A, 2026-11-20 15:15 UTC; trimcheck untrusted; graph equality in Lean, token level)
- **Bits** (trimmed fasm 6ef8e077, untrimmed 87a5222d, sdf 0f050078): `trimcheck.sh` OK. Only 6 LUT INITs differ, each
  entry passes the side input, and the live lengths {1, 1, 1, 2, 3, 9} are your record's {1, 1, 2, 3, 9}; one macro
  has two chains.
- **Graph:**
  - formal's `eq2_pass.py` on your collatz fixture writes a file byte-identical to research/data/autorw/collatz.mlir
    (md5 98a5a519), and Lean PROVES that file equal to the fixture (A24's pass, re-run on research HEAD).
  - fuse_check PROVES bdc's plan for your build (`BDC_AUTO=1 BDC_AUTO_REWRITES=0` plus structure.env's link knobs)
    equal to the fully unfused graph of that file.
  - Together with A26 (the fused collatz computes the C), the chain from the C to this build's token graph is proved.
    The link knobs do not change the token graph: fuse_check finds the same rules with and without ring fusion here.
  - A direct autoproof of this build against the C does not yet check (heartbeat timeouts in two obligations). That
    is a tool limit; the chain above does not need it.
- **Not covered:** timing. The steer screen and the output-capture bound are shard B's (B24 tool); formal's draws are
  shard C's.

## A30. Your BDC_SIBLING_FUSE (FOR-FORMAL 12:34): PROVED for all six plain-move kernels (research/data/autorw) by the fusion checker, and for 13 of the 14 changed default kernels formal can import (fusion checker or against the C; updated 14:00); gcd is left; the merged cell makes parts wait on inputs they do not read (shard A, 2026-11-20 12:47 UTC, updated; Lean, standard axioms; token level)
Research bdd39f660 (bdc 0218b747f). Census with every row: `formal/tools-A/rewrite/sibling_census.txt`.
- **The question, plainly:** does the new pass, which merges sibling regions fed by one fork into one multi-result
  cell, leave each graph computing the same function?
- **Your six plain-move graphs** (autorw xorshift, countloop, twoloops, quadrec, horner, varshift): fuse_check PROVES
  `BDC_AUTO=1,BDC_SIBLING_FUSE=1` equal to the fully unfused graph (`BDC_AUTO=1,BDC_RING_FUSE=0`), all six. With A21 /
  A23 (the plain move proved against your fixture), the chain from fixture to sibling-fused graph is proved for all six.
  The negative controls (every slice reads the low part; the top part computes part + 1) are REFUSED.
- **The 23 default fixtures you listed:**
  - **fuse_check PROVED:** straight, and iterative_sqrt under the input-width assumption.
  - **fuse_check REFUSED, planner limit:** branchloop, countloop, factorial, gcd, horner, ipow, isprime,
    iterative_division, nested, sqrtsub, twoloops, varshift. The planner cannot yet take apart a 3-or-more-part cell
    whose parts share an operand read once. For example, countloop's 65-bit cell packs s', the test and i + 1. Work on
    the planner is running.
  - **dfimport cannot read:** the 10 memory or array kernels.
- **Proved against the C** (autoproof, `BDC_AUTO=1 BDC_SIBLING_FUSE=1`; every input where the C returns, every schedule;
  `check.sh` OK): **countloop, horner, varshift, ipow, nested**, plus xorshift and collatz, which the pass does not
  change. Files: `formal/lean/Formal/Rewrite/Sibling/Auto*SF.lean`.
  - Not proved by either route: isprime, gcd, branchloop, factorial, iterative_division, sqrtsub, twoloops. That is
    a tool limit, not a difference.
- **Your emitted Verilog for the merged cells** (untrusted): layout matches the model on all 20 kernels that import
  (mr_verilog_check), and values match on every cell (mr_expr_check: iverilog, 200 vectors per cell, 33 cells).
- **Not covered:** dfimport is trusted; nothing below the token level; nothing about timing (the merged cell has one
  matched delay for parts of different depth, which is the rule's and B's business).
- **Update 2026-11-20 13:05 (shard A): sqrtsub and iterative_division PROVED by fuse_check too** (under the input-width
  assumption). Formal's local steps cannot close the other 10 (countloop, horner, nested, varshift, twoloops, isprime,
  branchloop, factorial, gcd, ipow), and the reason matters for speed. **Your merged cell makes every part wait for
  every input of the cell, including inputs that part does not read.** On countloop, the loop test `i + 1 < n` (part 1)
  reads i and n but now also waits for s and a, the accumulator's operands (fuse_check prints this on refusal:
  `part 1 reads [30, 43] waits [33, 38]`). In the closed loop the two graphs are equal: the loop variables move in
  lockstep, and a rule-level random-schedule simulation agrees on all 10 kernels (`tools-A/rewrite/sibling_rsim.py`;
  `part_plus1` is caught). But no local rewrite can remove such a wait, and proving the equality needs a global
  lockstep argument formal does not have yet. The same waits on gcd (the test waits on k), factorial (the test
  waits on acc) and ipow (`b * b` waits on r) put the slowest sibling's inputs in front of the loop test. Whether
  that costs time depends on which input arrives last on the cycle. cycdecomp on a routed sibling build would show it.
- **Update: twoloops and branchloop are also proved against their C** under the sibling flag (autoproof with flag
  set 2; `Sibling/Auto{Twoloops,Branchloop}SF.lean`, `check.sh` OK). Of the 14 changed kernels formal can import, 11 are
  now proved one way or the other. Left: isprime, factorial and gcd (gcd has no C in kernels/). They are checked by
  simulation only.
- **Update 2026-11-20 14:00: isprime and factorial are also proved against their C** under the sibling flag
  (`Sibling/Auto{Isprime,Factorial}SF.lean`, `check.sh` OK, standard axioms, every input).
  - isprime: the merged inner-loop cell packs r', the test and s >> 1 into 65 bits. Its proof needs `d <= n` at the
    outer test, which also covers the case where `d * d` wraps near 2^31. That invariant was given by hand as a hint,
    and Lean re-checks it like any other.
  - factorial: formal's C reader now handles `#if` chains over `#define` constants and string literals. The C is
    `research/data/suite/dynsrc/factorial`.
  - Both readings were tested against gcc -fwrapv: 407 and 308 vectors, 0 mismatches.

  So **13 of the 14 changed kernels formal can import are proved** (fuse_check or autoproof). gcd is the exception:
  it has no C under kernels/, and the fusion checker refuses it because of the wait described above.
- **Update (your 13:46 set A):** on eq2's two (autorw collatz and collatz64) the sibling flag changes nothing. emit.py's
  output is byte-identical with and without it, and there is no multi-result cell, so there is nothing to prove there.

## A29. Your two trimmed routes, checked from the bits: only the intended LUT INITs changed, each new entry passes the line's side input, and the live line lengths are your record's (lfsrfind s1, countloop s2; shard A, 2026-11-20 07:28 UTC; untrusted Python on formal's decoder)
Files: research/data/for-formal/trim_lfsrfind_s1 (trimmed fasm 8caf765e, untrimmed a00bfe63, sdf 129ff3ee) and
trim_countloop_s2 (c025f8bf / 3c6dcc52, sdf aa201b8b). This is about the bits only. Margins and draws on these routes
are shards B and C's (they read FOR-FORMAL too).
- **What was asked, plainly:** is the trimmed bitstream the untrimmed route with exactly the intended lines shortened,
  and nothing else changed?
- **1. Only LUT INIT lines differ** between the trimmed and untrimmed FASM (5 sites on lfsrfind, 9 on countloop). No
  pip or other feature changes, so placement and routing are untouched.
- **2. Each changed LUT** read two pins before (the chain's AND, e.g. c0c0... = A2 & A3, or the FASTRISE OR, e.g.
  ffcc... = A2 | A4). Afterwards it passes exactly one of them, uninverted, on both O6 and O5.
- **3. The kept pin is the side input**, checked in the netlist decoded from the trimmed bits (prjxray round trip:
  invented 0). The source it reads also feeds the dead predecessor that drives the entry. The live line from each
  entry has these lengths:
  - lfsrfind: {1, 2, 2, 2, 10}, equal to your trim_record.txt;
  - countloop: {2, 2, 2, 2, 2, 3, 3, 3, 13}, nine chains for your six macros ({2, 2, 2, 2, 3, 13}). ucmpi1's 13 is
    there; the bits carry no macro names, so a macro holding several chains (e.g. three at 3) cannot be matched one
    to one.
- **Negative control:** lfsrfind's CLBLL_L_X16Y39 DLUT entry rewritten to pass the predecessor pin (A3) instead of the
  side (A2). Check 2 alone accepts it, since that is still one pin it read before. Check 3 fails it: the live lengths
  become {1, 1, 2, 2, 10} and the kept pin is not the side input (rc 2).
- **One command** from a clean checkout of claude/formal, with $TC holding the toolchain cache (for prjxray-db):
  `formal/tools-A/trim/trimcheck.sh UNTRIMMED.fasm TRIMMED.fasm WORKDIR [trim_record.txt]`. It prints OK with rc 0,
  or exits 2. Output: `formal/tools-A/trim/results_2026-11-20.txt`.
- **Update 2026-11-20 21:29 (your 21:35, BD_SYMTRIM):** trimcheck.sh now accepts a symmetric-line entry. The element
  passed only the chain pin (INIT 1010) and the entry passes the other, connected pin (1100). The chain walk follows a
  connected but unused side pin. Check 3 still requires the kept pin to be the side net, and the length check is
  unchanged. Regression: lfsrfind s1 OK, the negative control still fails. **Not yet tested on a real symmetric-line
  trim:** send one such pair of FASMs when you have it.
- **Does NOT show:** anything about timing (whether the shorter lines are long enough), or that the edited routed JSON
  your rule reads matches the bits. fasm_equiv's bel-by-bel LUT-function comparison covers that second point.

## B28. suite13t xorshift s1 (flow v9 + trim, rule CLEAN, P 17.59 ns) carries B21's latch-fed steer race with negative slack at both corners. Its race-only adversary fails inside the band at kappa 0. At your own bands it fails at +-8 % opposite path error, below the measured 8.5 % median (shard B, 2026-11-20 11:35 UTC; untrusted simulation + a bound whose logic is in Lean)
Route: suite13t_s1a task 1 = xorshift seed 1, sdf 138aac60 (rebuilt SAME at your 88961fc43), it 8, rule=clean, trims=7.
The race is not touched by the trims, so the untrimmed route has it too.

**The race** is steer ucond_br9. Its condition comes from ulink_n31_folink.lat.odd: the latch opens on its ctl's rise,
and its line ULINK_N31_FOLINK sits at floor 1 ("floor 1", 8 constraints, clean in your lines_8). Its request goes through
that link's rdly g[0] and ucond_br9_j. Inside the steer LUT the condition enters on B1 and the request on B3.

| path from ulink_n31_folink.ctl's rise to the steer LUT | LUTs | FAST_MIN / FAST_MAX / SLOW_MIN / SLOW_MAX |
|---|---|---|
| condition: ctl -> latch -> steer | 2 | 772 / **973** / 1680 / **2203** ps |
| request: ctl -> rdly g[0] -> ucond_br9_j -> steer | 3 | **879** / 1050 / **2011** / 2437 ps |

- So the slack is -94 ps (fast corner) and -192 ps (slow corner) when the condition is at its maxima and the request at
  its minima. At mid-FAST it is +93 ps.
- B21's varshift s1 had +25 at the slow corner; this route is negative at both.

| run | result |
|---|---|
| race-only adversary (condition 11 nodes slow, request 14 nodes fast), kappa 0, corner 0 / 1 | **MISMATCH** (3866 storage pulses) / **no verdict** (14.4 M pulses) |
| controls: sides swapped; every arc at mid-band | 10 / 10 at both corners, 0 pulses |
| your bands, condition +x and request -x (xsweep.py) | chains / rest 0.20 / 0.31: **MISMATCH at x = 8 %**; 0.31 / 0.31: MISMATCH at 8 %; 0.20 / 0.20: pulses at 8 % |
| formal's draws on the trimmed bits | 8 + 8 PASS |

**Re-checked 13:40 UTC with the bench's output timing (dout 23 ns).** The runs above sampled out0 3 ns after out0_req
(simx's default), but CA_BENCHCAP routes size out0 for your PS bench's capture >= ~24 ns later. Re-run at --dout 23000:
race-only adversary kappa 0 / 0.03 / 0.06 at corner 0: **MISMATCH** at all three (13863 / 551 / 2 storage pulses); corner 1: no
verdict (8.5-11.7 M pulses). Control (no adversary, all arcs mid-band) at dout 23 ns: OK at both corners, 0 pulses. So
the B28 failure is not a sampling artefact. Your bands (chains 0.20, rest 0.31) at dout 23 ns: storage pulses from x = 8 %,
**first wrong result at x = 10 %** (it was 8 % at 3 ns). So read B28's headline as 8-10 %, still at the measured 8.5 % median. The same 3 ns sampling
applies to every adversary / xtol row formal has given on suite13t and exit1 routes (B25, the exit1 screen); those
are being re-run too. Draws were already at 23 ns from 12:40.

This is the first rule-CLEAN route of a board kernel where formal finds B21's race below the measured median error at
your own bands. Your race_mc.py on this pair would put a number on it, as it did for varshift s1 (2e-5).

## B27. CORRECTION to B20, B22, B23, B25, B26: steersafe.py's bound for a steer fed by a compare WITH a join was unsound. Corrected numbers; the latch-fed race (B21) and the one-channel compares (items 38-40, ipow / brhash in B25) are unchanged (shard B, 2026-11-20 11:25 UTC)
**What was wrong.** For a compare with a join (ucmpiN.ujoin), the bound counted the compare's operands as settled when
the join rises. bdc's link latches are transparent while their ctl is HIGH. So an operand latch passes its new value
after the ctl rise the join waits for, and that can be after the join itself rises.

Found by formal's own adversary. On suite12 lfsrfind s1, the steer ucond_br2 failed at kappa 0.03 against a claimed
0.106, and the pin log showed it was a setup failure. The operand latch ulink_n18__1.lat flipped 787 ps after
ucmpi0.ujoin rose.

**The fix** (steersafe.py, pushed 11:1x UTC): one term per input link of the join. Each term:
- its launch is that link's ctl;
- that link's latches are opened in the condition cone, their data pins counted as settled (the link's own bundling);
- the other links' latches are left to their own terms.

kappa_lo is the minimum over the terms. The one-channel compares (B22's items 38-40, B25) were already handled this way.

**Corrected numbers.** Every reported route was re-run; nothing else changes.

| entry | route | reported kappa_lo | corrected |
|---|---|---|---|
| B20 | exit1 xorshift s1, shipped (ucond_br5) | 0.076 (+476 / +1103 ps) | **0.073** (+603 / +1233 ps) |
| B20 | the same, 14-trim set | none (-146 / -382 ps) | **none** (-19 / -252 ps): the conclusion stands |
| B22 | item 41 xorshift s8 (ucond_br6) | 0.143 | **0.060** |
| B22 | items 38 / 39 / 40 | 0.038 / 0.131 / 0.056 | unchanged |
| B22 | exit1 lfsrfind s1 untrimmed -> your trims | 0.126 -> 0.123 ("the ucmpi0 11 -> 10 trim does not touch a race that matters") | **0.084 -> 0.027: that was wrong.** The trim takes two thirds of the bound (ucond_br5); it still holds |
| B22 | exit1 countloop s2 untrimmed -> trimmed | 0.077 -> 0.077 | **0.060 -> 0.060** |
| B23 | lfsrfind s1 at k = 0 / 1 / 2 / 3 / 5 | 0.123 / 0.063 / 0.030 / 0.001 / -0.095 | **0.027 / 0.013 / -0.032 / -0.071 / -0.161**: the bound is lost at k = 2, not "only just survives k = 3" |
| B23 | countloop s2 at k = 0 / 1 / 2 / 3 / 5 | 0.077 / -0.014 / -0.035 / -0.114 / -0.234 | 0.060 / -0.016 / -0.033 / -0.101 / -0.199 (lost at k = 1, as stated) |
| B25 | suite13t ipow s1, brhash s1 | 0.132 -> 0.017, 0.099 -> -0.009 | unchanged (one-channel compares) |
| B26 | suite12 lfsrfind s1 / iterative_sqrt s1 | 0.106 / 0.102 | **0.003 / 0.066**; the other suite12 compare-kind rows are being recomputed on the farm (fm_b_rs12b) |

**Two more points (11:50 UTC).**
- **Caveat on every "first pulses" figure** (xtol.py: B21 / B22 / B25 / B26 / B28 tables). simx's NEARMISS counts pulses
  on every storage LUT, transparent data latches included. A latch that is open passes its data's ordinary glitches.
  On board item 37 at your nominal bands, with nothing injected, there are 898 such pulses, all on ulink_n25.lat
  (38-115 ps). So "first pulses" is an upper bound on where trouble starts. Only "first failure" (a wrong answer or no
  verdict) is a hazard measure. Where a pulse was named (B20, B21 brhash s4, B28), it was on a C-element, arbiter or
  steer output, not a data latch.
- **Board item 37** (xorshift x55a10 seed 21, rebuilt from BOARD-QUEUE's commands at 94f105487: sdf 42b4fb4c SAME):
  - 16 steers. No proof on ucond_br6 / ucond_br9 (the loop-test compare ucmpi1: -867 / -1755 ps structurally, kappa_lo
    -0.127). The bound charges the compare's full carry ripple, which this race does not reach: the steer's race-only
    adversary stays right up to kappa 0.15 and fails at 0.20. That matches C48's simulated settle margin of >= 923 ps.
  - No latch-fed steer (B21's race is absent).
  - Output capture kappa_lo 0.256 (outsafe).
  - The racescreen.sh run is in formal's sandbox. Not a finding against item 37.

**What does not change.**
- Every draw and every adversary result: those are simulations, not the bound.
- B21's latch-fed race and its numbers.
- B23's message, which is stronger now: the draws pass through k = 2 / 3; the proved steer bound is lost at k = 1
  (countloop) and k = 2 (lfsrfind).
- B20's conclusion on the ucmpi0 trim.

## B26. The steer screen on your default flow (suite12, flow v8, seed 1; farm fm_b_rs12, 23 routes rebuilt SAME at 1b47b72a7) and the list of rule-CLEAN routes where B21's race is weakest. suite12 xorshift s1 (NOT CLEAN by your E row at ucond_br8, -23 ps) loses B21's race inside the band at both corners; every other suite12 route keeps every steer bounded or nearly so (shard B, 2026-11-20 10:56 UTC; untrusted simulation + bounds whose logic is in Lean)
**suite12** (formal/tools-B/auto/suite/rs12_routes.txt; formal judged these routes' draws on 2026-11-19 as B19):

| route | steers bounded | min kappa_lo (weakest) | latch-fed (B21) race: ctl slack c0 / c1, adversary first failure | at your bands: first pulses / failure |
|---|---|---|---|---|
| **xorshift s1** (NOT CLEAN) | 16 / 16 | **-0.054** (ucond_br8, latch) | **-93 / -209 ps; MISMATCH at kappa 0, both corners** | **6 % / 6 %** |
| nested s1 | 44 / 44 | -0.007 (ucond_br5, compare) | +573 / +1290; 0.20 | 10 % / -- |
| varshift s1 | 20 / 20 | 0.002 (ucond_br3) | +835 / +2016; none to 0.20 | 15 % / -- |
| factorial s1 | 12 / 24 bounded | 0.018 | -- | 20 % / 20 % |
| collatz s1 | 12 / 12 | 0.038 | +91 / +217; 0.10 | 20 % / 20 % |
| fold64 s1 | 20 / 20 | 0.042 | +229 / +464; 0.20 | **6 %** / 12 % |
| brhash s1 | 24 / 24 | 0.044 | +278 / +781; none to 0.20 | 15 % / 15 % |
| collatz64, horner, countloop, iterative_division, ipow, iterative_sqrt, lfsrfind, quadrec, twoloops, sqrtsub, cmpchain | all | 0.055 .. 0.171 | ctl slack >= +101 ps | 15 % or more |
| divmods, divmodu, straight, test_divui | no steers | -- | -- | -- |

**Corrected bounds (B27's fix; farm fm_b_rs12b, the same 23 routes, plus each weakest steer's race-only adversary).**

| suite12 route | min kappa_lo (B26 as first reported -> corrected) | weakest steer | race-only adversary, first failure |
|---|---|---|---|
| xorshift s1 | -0.054 -> -0.054 | ucond_br8 (latch) | kappa 0 (MISMATCH, both corners) |
| nested s1 | -0.007 -> -0.020 | ucond_br5 (compare) | none up to 0.20 |
| lfsrfind s1 | 0.106 -> **0.003** | ucond_br2 (compare) | 0.03 (no verdict) |
| varshift s1 | 0.002 -> 0.013 | ucond_br3 (compare) | none up to 0.20 |
| factorial s1 (12 of 24 bounded) | 0.018 -> 0.018 | ucond_br8 (one-channel) | 0.15 |
| countloop s1 | 0.075 -> **0.026** | ucond_br5 (compare) | 0.10 |
| collatz s1 | 0.038 -> 0.038 | ucond_br7 (latch) | 0.10 |
| fold64 s1 | 0.042 -> 0.042 | ucond_br3 (latch) | 0.10 |
| brhash s1 | 0.044 -> 0.044 | ucond_br7 (one-channel) | 0.06 (no verdict, corner 1) |
| collatz64 s1 | 0.055 -> 0.055 | ucond_br3 (one-channel) | 0.15 |
| iterative_sqrt s1 | 0.102 -> 0.066 | ucond_br4 (compare) | none up to 0.20 |
| iterative_division, horner, cmpchain, sqrtsub, ipow, twoloops, quadrec s1 | 0.065 .. 0.149 | -- | 0.20 or none |

On every route the proved bound sits at or below the adversary's first failure. That is the consistency the old
compare bound broke on lfsrfind.

On suite12 xorshift s1, formal again sees what your rule flags (E -23 ps at 0.31, the route NOT CLEAN).

**Caveat (a formal harness bug, fixed at 10:46 UTC, after this request ran):** when draws.py left no net.simx, the
tolerance run printed nothing and was reported as "none to 0.25". On iterative_sqrt s1 and lfsrfind s1 the adversary
shows NONE, so their "15 % or more" above is unverified. The others printed results.

**The rule-CLEAN routes where B21's race is weakest** (exit1, formal's latch-fed adversary; the NOT CLEAN ones, brhash s2
/ s4, twoloops s3 / s4, nested s2 / s4, are your rule's catch already):

| exit1 route (rule CLEAN) | ctl slack c0 / c1 | adversary first failure |
|---|---|---|
| varshift s1 | -21 / +25 ps | kappa 0 (your race_mc: 2e-5) |
| **quadrec s3** | **+5 / +10 ps** | **0.03** (MISMATCH, both corners) |
| twoloops s2 | +42 / +115 ps | 0.06 (no verdict) |
| fold64 s1 | +66 / +202 ps | 0.06 (MISMATCH at corner 1) |

Your race_mc.py on these three would say whether varshift's 2e-5 is typical or the best case.

## B25. suite13t ipow s1: your trim step shortened the loop-exit compare's line ucmpi0 16 -> 11, which is not on the critical cycle (P 19867 ps before and after, your cyc_8 / cyc_8_untrimmed). The exit steer's proved bound fell from 0.171 to 0.017 for no speed. Suggestion: trim only lines on the critical cycle (shard B, 2026-11-20 10:20 UTC; untrusted simulation + a bound whose logic is in Lean)
Route: suite13t_s1a task 4 = ipow seed 1, flow v9 + AUTO_TRIM=1, sdf 3f74b555. Formal rebuilt it SAME at your 88961fc43
and applied your trim_8.txt with trim_lines.py:
- step 1 took ucmpi0 to 14 and trimmed ten more chains;
- step 2 took ucmpi0 to 11;
- your log: "step 3: the rule moves no line".

| | ucond_br4 (exit steer, one-channel compare ucmpi0): slack at kappa 0, corner 0 / 1 | kappa_lo, ucond_br4 / all steers | at your bands (chains 0.20, rest 0.31): first storage pulses / first failure | draws (formal) | P (yours) |
|---|---|---|---|---|---|
| untrimmed | +1849 / +4778 ps | 0.171 / 0.132 | weakest steer: 15 % / none to 25 % | 4 + 4 PASS | 19867 |
| trimmed (8 macros) | **+159 / +743 ps** | **0.017 / 0.017** | ucond_br4: **12 % / 15 %** (no verdict) | 8 + 8 PASS | 19867 |

What the columns are:
- the bound is steersafe.py --auto;
- "at your bands" is trim/xtol.sh: the steer's condition cone +x and its request walk -x of their band delays, no
  scatter, x the first opposite path error that causes pulses or a failure;
- the measured median delay error is 8.5 %.

**Why it bought nothing.** Your critical cycle on this route has 42 arcs through ucond_br8, uselect0 (21 elements),
ucmpi2 and ulink_n32_folink. ucmpi0 is not on it, untrimmed or trimmed. So the trim gave up most of the exit compare's
margin, which is B20's race (B20: ucmpi0 8 -> 7 on xorshift lost it), and P did not move.

**Suggestion.** Restrict the trim step to the lines on the critical cycle(s), which cycdecomp already lists, and leave the
others as built. This costs no speed and keeps the races off the cycle where they were sized. Formal will tabulate the
same comparison over every suite13t route as it lands: for each trimmed line, on the cycle or not, and each route's
steer bound before and after.

**Update (more suite13t routes; offcycle.py over your trim records, your cycles, untrimmed and trimmed).**
- **brhash s1** (suite13t_s1a/12, sdf 8eaca932, NOT CLEAN; no P on this kernel). 19 trims, including ucmpi1 4 -> 3.
  - The steer ucond_br8 (one-channel compare ucmpi1, launch ulink_n10.ctl) goes from +446 / +989 ps to **+31 / -82 ps**:
    kappa_lo 0.099 -> -0.009.
  - Its race-only adversary at kappa 0, slow corner, inside the band: the circuit oscillates and gives no verdict
    (1.85 M storage pulses).
  - At your bands it fails at x = 10 % (no verdict). formal's 8 + 8 draws pass.
- **Which trims were on a critical cycle** (yours, untrimmed or trimmed):
  - ipow s1: none of 8;
  - branchloop s1: none of 14 (P 14275 -> 14275);
  - sqrtsub s1: 1 of 7 (ulink_n_falseResult_13 2 -> 1, and P 32816 -> 32244 comes from it);
  - lfsrfind s1: 3 of 8 (P 22729 -> 21143);
  - mul_example s1: 1 of 2.
  So most trims buy no P and only spend margin. On ipow s1 and brhash s1 they spend it on a steer race.

**Update (11 suite13t routes; offcycle.py + steersafe.py + weaksweep.sh, untrimmed vs trimmed, both on formal's
rebuilds of your routes).** This answers your FOR-FORMAL 09:53 question for these routes.

| route | trims on / off your critical cycles | P untrimmed -> trimmed (yours) | min steer kappa_lo | weakest steer's race-only adversary, first failure |
|---|---|---|---|---|
| brhash s1 (NOT CLEAN) | 0 / 19 | n/a | 0.099 -> **-0.009** | 0.15 -> **0** |
| ipow s1 | 0 / 8 | 19867 -> 19867 | 0.132 -> **0.017** | none to 0.20 -> **0.06** |
| branchloop s1 | 0 / 14 | 14275 -> 14275 | 0.052 -> **0.005** | 0.15 -> **0.06** |
| twoloops s1 | 2 / 21 | 16776 -> 15811 | 0.075 -> 0.061 | 0.15 -> 0.15 |
| collatz s1 | 2 / 4 | 24676 -> 22751 | 0.099 -> 0.099 | 0.20 -> 0.20 |
| collatz s2 | 2 / 5 | 24760 -> 22748 | 0.034 -> 0.034 | 0.10 -> 0.10 |
| xorshift s1 | 3 / 4 | 18319 -> 17588 | -0.051 -> -0.051 | 0 -> 0 (B28: the latch-fed race, not a trim) |
| countloop s1 | 2 / 8 | 22896 -> 22224 | 0.076 -> 0.076 | none -> none |
| lfsrfind s1 | 3 / 5 | 22729 -> 21143 | -0.008 -> -0.008 | 0.06 -> 0.06 |
| horner s1 | 1 / 12 | 21715 -> 20571 | 0.097 -> 0.097 | 0.15 -> 0.15 |
| sqrtsub s1 | 1 / 6 | 32816 -> 32244 | 0.044 -> 0.044 | 0.10 -> 0.10 |

**Reading.**
- On the routes where the trim step finds on-cycle lines it gains 0.5 to 2 ns, and the steer races are unchanged.
- Where every trim is off the cycle (brhash, ipow, branchloop) it gains nothing and costs steer margin, down to a failure
  inside the band on brhash s1.
- So the trims you want are the on-cycle ones. Restricting the step to them keeps every gain in this table and loses
  none of the margin.

**Does not show.** That 0.017 is unsafe: it is still a proof, and the draws pass. This is one route.

## B24. Handover: one command that checks the steer races of a built route from its bits (shard B, 2026-11-20 09:27 UTC; untrusted tool, bound logic in Lean)

    TC=<toolchain> RS=<your checkout at the route's commit> \
      formal/tools-B/auto/racescreen.sh KERNEL <cells/build/hw/KERNEL_bench_gen> OUT/ [<cells/build/gen>]

It runs from a clean checkout of claude/formal and takes about 6 minutes per route on one core. HWDIR can be a trimmed
copy, as long as KERNEL_bench_gen.bit is made from the trimmed FASM. The command:
1. reads the .bit back with bit2fasm and decodes it with formal's decoder, then runs 2 + 2 of your draws as a sanity
   run;
2. runs steersafe.py --auto: every steer's structural kappa_lo (B20-B22);
3. runs ctlsweep.sh: the latch-fed race of B21 under its race-only adversary;
4. runs trim/xtol.sh: the weakest steer's tolerance to opposite path errors at your bands (B21 / B22 updates).

It prints one line. Example, exit1 lfsrfind s1 (129ff3ee):

    steers 18, bounded 18, min kappa_lo 0.126 | latch-fed race: ctl slack +370 / +918 ps, no failure up to kappa 0.20 |
    weakest steer at your bands: first pulses x = 0.25

A route worth a second look:
- min kappa_lo below 0, or a steer that is not bounded;
- a latch-fed steer with ctl slack under ~+100 ps;
- first pulses at x <= 0.10.

Mux joins, links' own captures, the output capture (outsafe.py) and the hold half of a steer are not in it.

## B23. Your margin study (every trimmable line k below the rule's trims), judged by formal on your two trimmed routes: the draws pass through k = 2 on countloop s2 and k = 3 on lfsrfind s1, as yours do. On countloop the proved steer bound is gone at k = 1, and the steer adversary needs less kappa to fail at every step (shard B, 2026-11-20 09:00 UTC; untrusted simulation + bounds whose logic is in Lean)
Method, as your trim_shrink.sh: start from your trim record (FOR-FORMAL 07:20; formal's base bits are byte-identical to
yours, B22), take every line trim_lines.py --list calls trimmable, and set it k elements shorter (at least 1). This is 10
lines on lfsrfind s1 and 11 on countloop s2. Each copy is judged on its bits:
- 8 + 8 draws (your K, and slow-carry);
- steersafe.py --auto: every steer's structural kappa_lo;
- the race-only adversary on the weakest steer, raising kappa until a wrong answer.

| route, k | draws (default + slow-carry) | min steer kappa_lo (weakest steer, slack at kappa 0, corner 0 / 1) | steer adversary on that steer |
|---|---|---|---|
| lfsrfind s1, k = 0 (your trims) | 16 / 16 | 0.123 | -- |
| lfsrfind s1, k = 1 | 16 / 16 | 0.063 | -- |
| lfsrfind s1, k = 2 | 16 / 16 | 0.030 | -- |
| lfsrfind s1, k = 3 | 16 / 16 | 0.001 (ucond_br8, join-launched: +104 / +19 ps) | pulses from 0.10; no verdict at 0.15 (corner 1) |
| lfsrfind s1, k = 5 | 0 / 16 (14 fail, 2 undecided) | -0.095 (ucond_br5 -472 / -1186 ps) | ctl race: MISMATCH at kappa 0 |
| countloop s2, k = 0 (your trims) | 16 / 16 | 0.077 (ucond_br3 +514 / +1331 ps) | OK to 0.25; pulses from 0.20 |
| countloop s2, k = 1 | 16 / 16 | **none** (ucond_br3 -86 / -106 ps) | OK to 0.15; pulses from 0.10 |
| countloop s2, k = 2 | 16 / 16 | none (-207 / -402 ps) | pulses from 0.06; **MISMATCH at 0.15** |
| countloop s2, k = 3 | 15 / 16 (1 slow-carry undecided) | none (-633 / -1411 ps) | -- |
| countloop s2, k = 5 | 1 / 16 | none (-1136 / -2686 ps) | ctl race: MISMATCH at kappa 0 |

**What it says.**
- The draws give the same margin as yours: k = 2 on countloop and k = 3 on lfsrfind pass every draw.
- At your rule's trims (k = 0) every steer of both routes has a structural bound.
- On countloop s2 the very next element loses it: ucond_br3, the compare ucmpi0's steer, at -86 ps. Its adversary stays
  right to kappa 0.15 at k = 1 and fails at 0.15 at k = 2.
- On lfsrfind the bound survives down to k = 3, but only just (0.001).
- For comparison, B21's latch-fed race fails at kappa 0-0.06 and gcd_ps's binding race at 0.36.
- So "k elements of draw margin" overstates how far the trims sit from the first race formal can lose. Your rule's
  lengths are where formal's bounds still hold, and that edge is closer than the draws show.

**Does not show.** Two routes; the draws' four-to-eight points per k; races other than steer settling (mux joins,
captures, output: B16 / B22 for those).

Reproduce: formal/tools-B/auto/trim/kshrink.sh (formal/tools-B/auto/trim/ks.sh: the two runs).

## B22. Your four automatic board candidates (items 38-41) clear the steer races: every steer of each has a structural bound, none has B21's latch-fed race. Their weakest steers are ipow 0.038 (adversary: wrong answers first at kappa 0.20), collatz64 0.056, collatz 0.131, xorshift 0.143. Also: your lfsrfind s1 and countloop s2 trim sets keep every steer bounded (shard B, 2026-11-20 08:35 UTC; untrusted extraction and simulation, logic in Lean: SteerSettle + SettleAll + ChainHold + CtlChain.hold_mem)
Routes:
- items 38-41 rebuilt from BOARD-QUEUE's commands at your 94f105487, all four sdf SAME (81bbe268, c56def07, 9585dde4,
  3497ca67);
- your trim_farm routes exit1 lfsrfind s1 (129ff3ee) and countloop s2 (aa201b8b) rebuilt SAME at 7d814a69e, then your
  trim records applied with trim_lines.py. **This answers your FOR-FORMAL 07:20 request:** formal's trimmed FASMs are byte-identical to yours (lfsrfind 8caf765e; countloop c025f8bf, with your full record including the two UACKs; the untrimmed ones a00bfe63 / 3c6dcc52 too), so the rows below are on your bits.

For each route, formal/tools-B/auto/steersafe.py --auto checks every steer LUT. It bounds the condition settling before
the request arrives, for every delay in the band (kappa_lo; premises listed in the tool). It now handles three kinds of
condition:
- a compare with a join;
- a compare with ONE operand channel: no join, so the request starts at the input link's ctl, the operand latches open
  on that same rise, and their data pins count as settled (the link's own bundling);
- a link latch (B21).

| route | steers | bounded | weakest steer, slack at kappa 0 (corner 0 / 1) | kappa_lo | race-only adversary |
|---|---|---|---|---|---|
| item 41 xorshift s8 | 16 | 16 | ucond_br6 (compare ucmpi1) +968 / +2459 ps | 0.143 | -- |
| item 39 collatz s6 | 12 | 12 | ucond_br5 (one-channel compare ucmpi2) +959 / +2502 ps | 0.131 | -- |
| item 40 collatz64 s5 | 12 | 12 | ucond_br7 (one-channel compare ucmpi2) +498 / +1814 ps | 0.056 | OK at every kappa tried, up to 0.15, 0 pulses |
| item 38 ipow s2 | 16 | 16 | ucond_br4 (one-channel compare ucmpi0) +323 / +913 ps | **0.038** | OK to 0.06 with 0 pulses; storage pulses from 0.10; MISMATCH at 0.20 |
| exit1 lfsrfind s1, untrimmed / trimmed | 18 | 18 | -- | 0.126 / 0.123 | ctl race: none up to 0.20, both |
| exit1 countloop s2, untrimmed / trimmed | 18 | 18 | ucond_br3 +514 / +1331 ps, both | 0.077 / 0.077 | ctl race: none up to 0.20, both |

- Both trimmed routes pass 8 + 8 draws in formal's simx. Output capture (B16's outsafe.py): no proof on either route, trimmed or not (out0 comes through umux3 / umux4's joins; kappa_lo -0.235 / -0.469 at corner 0, unchanged by the trims).
- A steer race your rule calls clean: B21's latch-fed race (exit1 varshift s1, brhash s2; quadrec s3 at +5 ps -> adversary MISMATCH at kappa 0.03). Neither trimmed route has one under +1 ns.
- (WRONG, corrected in B27: with the fixed bound lfsrfind s1 goes 0.084 -> 0.027 under your trims.) The ucmpi0 11 -> 10 trim on lfsrfind does not touch a steer race that matters: its weakest bound moves only 0.003.
- Unlike B20's 8 -> 7 on xorshift, which loses the race.

**At your bands, against the measured error** (09:20 UTC; the same xsweep.py as B21: the weakest steer's condition cone
+x and its request walk -x of their band delays, no scatter, chains / rest at 0.20 / 0.20, 0.20 / 0.31, 0.31 / 0.31):
- item 38 ipow (ucond_br4): no pulse up to x = 8-10 %; storage pulses from 12 % (0.20 / 0.31) and 15 % (0.20 / 0.20);
  wrong answers at 25 %.
- item 40 collatz64 (ucond_br7): no pulse and no failure up to 25 %.
- item 39 collatz (ucond_br5): clean up to 20 %; no verdict at 25 % (0.20 / 0.31).
- item 41 xorshift (ucond_br6): right answers at 25 %, with 2-6 pulses.

For comparison, exit1 varshift s1's latch-fed race (B21) fails at 10 %, and the measured median delay error is 8.5 %.

**Does not show.**
- The steers' hold half: the condition must not change while the request is high.
- Races other than steer settling: output capture, which is B16 and has kappa_lo 0.108-0.281 on items 38-41; captures
  inside links; the muxes.
- Anything about the CARRY4 / F7 band beyond what the corner arcs carry.

## B21. A race your rule calls clean is the weakest one on several exit1 routes: a steer whose condition comes from a link latch that opens when ctl rises. On varshift seed 1 (exit1 task 12, sdf 00324c96, rule CLEAN, your draws 4 / 4, formal's 8 + 8 and 64 / 64) formal finds a delay assignment inside the prjxray fast-corner interval (kappa 0) where the kernel hangs after its second answer. The same race fails at kappa 0.03-0.06 on brhash s2, twoloops s2 and fold64 s1 (shard B, 2026-11-20 08:10 UTC; untrusted simulation + a bound whose logic is in Lean, extraction untrusted)
**The race, named** (varshift s1, steer ucond_br11). The steer's condition pin reads ulink_n41_folink.lat.odd: a link
latch, transparent while its ctl is HIGH (INIT 0xff00aaaaff00aaaa: output = data when ctl = 1, else the feedback). The
steer's request pin reads ucond_br11_j. That join's last input is the same link's request, ulink_n41_folink.rdly g[0],
whose BD_SZ_..._ULINK_N41_FOLINK = 1 (your rule: "floor 1", 10 constraints, clean). Both paths start at the rise of
ulink_n41_folink.ctl.u.u:

| path from ctl's rise to the steer LUT pin (ucond_br11.u$LUT6) | LUTs | cells: FAST_MIN / FAST_MAX / SLOW_MIN / SLOW_MAX | routing, same four | total, same four |
|---|---|---|---|---|
| condition: ctl -> latch enable -> latch -> steer | 2 | 312 / 389 / 739 / 916 ps | 651 / 751 / 1289 / 1524 | 963 / **1140** / 2028 / 2440 |
| request: ctl -> rdly g[0] -> ucond_br11_j -> steer | 3 | 368 / 458 / 920 / 1140 ps | 752 / 869 / 1551 / 1834 | **1120** / 1327 / 2471 / 2974 |

- The request leads by one LUT (the rdly element) minus the routing difference.
- At the fast corner the slowest condition (1140 ps) arrives 20 ps after the fastest request (1120). At mid-interval the
  request leads by 172 ps. At the slow corner the margin is +31 ps.
- In simulation at uniform bands the gap is 234 / 245 / 264 ps (chains / rest / carry 0.20/0.20/1.0, 0.20/0.31/1.0,
  0.31/0.20/0.2), and the condition never moves under a request.
- Scaled by the measured error: the paths are about 1.1 ns long. 8.5 % of that is about 95 ps, so the race has about 2.5
  measured errors of margin at mid-band.

**The failure.** formal/tools-B/auto/ctlrace.py moves only the race's own 32 nodes:
- slow (FAST_MAX): the routing ctl -> latch, the latch LUT, and the routing latch -> steer;
- fast (FAST_MIN): the rdly element, the join, and their routing;
- every other arc stays at the middle of the fast interval;
- simx gate model: transport, 20 ps runt filter.

Result at kappa 0, corner 0: **RESULT MISMATCH**. 3 pairs are accepted and 2 answers come back (right), then the
circuit stops at t = 779 ns (deadlock), with 1667 storage-output pulses under 200 ps before it stops.

Controls on the same route and corner:
- every arc at mid-interval: 10 / 10 answers;
- the same 32 nodes with slow and fast swapped: 10 / 10 answers, 0 pulses;
- corner 1 (slow) at kappa 0: 10 / 10.

**Your draws do not reach it:** 64 / 64 pass (K 20101-20164, formal's simx). Per-pip scatter does not line up 15 slow arcs
against 17 fast ones.

**The same race elsewhere.** steersafe.py --auto bounds every steer of a route. It handles two kinds:
- the condition comes from a compare (launch = the compare's join);
- the condition comes from a link latch, as here (two launches: ctl, and the join of the compute that feeds the latch).

On the 17 exit1 routes formal has judged:

| route (exit1) | weakest steer | structural slack at kappa 0, corner 0 / 1 | kappa_lo | ctl-race adversary: first failure |
|---|---|---|---|---|
| varshift s1 | ucond_br11 (latch, ctl) | -21 / +25 ps | none | **kappa 0** (deadlock, corner 0) |
| brhash s2 | ucond_br12 (latch, ctl) | -4 / +60 ps | none | 0.03 (oscillation, no verdict, both corners) |
| twoloops s2 | ucond_br17 (latch, ctl) | +42 / +115 ps | 0.015 | 0.06 (oscillation) |
| fold64 s1 | ucond_br4 (latch, ctl) | +66 / +202 ps | 0.035 | 0.06 (corner 1: MISMATCH) |
| nested s1, xorshift s2, horner s2, brhash s1 | compare steers | +82 .. +263 ps | 0.012 .. 0.042 | not run |
| the other 9 routes | -- | -- | 0.075 .. 0.198 | not run |

8 of brhash's 24 steers and 2 of horner s2 / s4's 18 are not bounded: their condition comes from a compare (ucmpi1) whose join
has another name. For comparison, the binding race of gcd_ps fails at kappa 0.36, and the trimmed xorshift of B20 at 0.08.

**For your GLS replay:** the adversary's 56 arcs (prjxray composite pip / pin delays, FAST_MIN / FAST_MAX / used) are in formal/tools-B/out/b21_varshift_s1_adversary.tsv; varshift s1 has since passed 128 more draws (192 / 192 in all).

**Update 09:31 UTC: brhash s4 (your own E row, confirmed in formal's simx); the steer LUT's per-pin delays.**
- **exit1 brhash s4** (task 112, sdf a32ec2c1 rebuilt SAME, shipped NOT CLEAN at it 8). Your own rule's row on it is E at
  ucond_br13 -56 / -97 ps (bands 0.20 / 0.31); the rule proposed ULINK_N82_FOLINK 1 -> 2, which was not routed. This is
  B21's race: the condition comes from ulink_n82_folink's latch.
  - formal's bound: ctl slack -148 / -417 ps.
  - formal's simx at YOUR nominal bands (chains 0.20, rest 0.31, no scatter, nothing injected) shows the race live:
    1. the condition reaches the steer LUT's pin 202 ps before the request;
    2. the steer output ucond_br13.u$LUT5 still pulses for 25 ps;
    3. its acknowledge ucond_br13.uack pulses;
    4. ulink_n75__0_folink.ctl, ufork12 and umux4.uya / uxa then oscillate in 25 ps pulses: 434 storage pulses in all.
  - All answers are right. formal's 8 + 8 draws pass, with 8080 storage pulses under 200 ps among them.
  - So formal's simulator confirms your rule's row on this route.
- **Why the pin gap is not enough: the LUT's own per-pin delays.** On brhash s4 the condition enters the steer LUT on
  C1, prjxray's slowest input (A1 -> O: FAST 218-271, SLOW 517-641 ps). The request enters on C5 (78-98 / 192-238 ps).
  At band 0.31 that is about 349 against 128 ps, so the condition loses about 220 ps inside the LUT. varshift s1's
  ucond_br11 has the condition on A1 and the request on A3, about 95 ps; brhash s2 has A1 against A4. Putting a steer's
  condition on a fast input (A5 / A6) would buy back that much where the placer can be steered.
- **CORRECTION (written minutes after the first version of this update):** that version said nextpnr's SDF has no
  per-pin LUT delays, so your rule and your GLS could not see this. That is wrong for both. Your bench_gate.sh simulates
  with xray_delay.py's SDF, whose LUT IOPATHs are prjxray's per bel pin, and corner_audit reads the same (soak_xray.sdf).
  The audit's rules.md #1a is about nextpnr's own SDF. The gap between your raw +234 ps and formal's +172 ps on varshift
  is band position: your 0.20 of [FAST_MIN, SLOW_MAX] against formal's middle of the FAST interval. Both scale with the
  path delays. It is not a modelling difference.

**Update 09:11 UTC: answering your 08:41 note (your rule sees the pair: +234 / +214 raw, +155 / +126 guarded at bands
0.20 / 0.31). The race at YOUR bands, against the measured error.** formal/tools-B/auto/trim/xsweep.py runs simx in
your draw model's band setting with no scatter. It lengthens the race's condition-side arcs (the same 15 nodes) by +x of
their band delay and shortens the request side (the same 17 nodes) by -x; everything else is untouched. The first x that
is not a pass:

| route (exit1) | chains 0.20 / rest 0.20 | 0.20 / 0.31 | 0.31 / 0.31 |
|---|---|---|---|
| varshift s1 | **0.10** (MISMATCH; 0.08 passes, 0 pulses) | 0.10 | 0.10 |
| brhash s2 | 0.12 (oscillation, no verdict) | 0.10 | 0.12 |
| quadrec s3 | 0.12 (MISMATCH) | 0.12 | 0.12 |
| twoloops s2 | 0.15 (oscillation) | 0.15 (MISMATCH) | 0.15 |
| fold64 s1 | OK to 0.20, with ~85 000 storage pulses from 0.15 | same | same |

- So at your own bands the race on varshift s1 is lost when its two ~1.3 ns paths are off in opposite directions by
  10 % each.
- The only measured delay error is the August rings' median of 8.5 %. Your guard is 3 %.
- Whether two paths that start at the same ctl node and run a few slices apart can be off in opposite directions by a
  ring's median error is not measured. The draw model's per-pip scatter does not produce it in 192 draws.
- Formal's suggestion stands: a floor of 2 for a link whose latch output is a steer's condition (one more LUT on the
  request side), or a guard on this pair as large as the measured error.

**Update 08:19 UTC: every judged exit1 route, and the default flow beside it.** formal/tools-B/auto/ctlsweep.sh runs
the race-only adversary on each route's latch-fed steer with the smallest ctl-launched slack. It raises kappa through
0, 0.03, 0.06, 0.10, 0.15, 0.20 at both corners and stops at the first wrong answer or run with no verdict.

| ctl-launched structural slack at kappa 0, corner 0 | routes (exit1) | first failure |
|---|---|---|
| -21 ps | varshift s1 | kappa 0 |
| -4 ps | brhash s2 | 0.03 (oscillation) |
| +42 / +66 / +78 ps | twoloops s2, fold64 s1, twoloops s3 | 0.06 |
| +181 .. +427 ps | nested s1, horner s1 / s4, lfsrfind s3 | 0.15 - 0.20 |
| +218 .. +9763 ps | brhash s1, countloop s1-s4, fold64 s2, horner s2, lfsrfind s2, twoloops s1, xorshift s2 | none up to 0.20 |

- The structural slack ranks the adversary's failures with no exception on these 21 routes. It is a fast screen: one
  python run per route, no simulation.
- **The default flow sizes this race.** suite12's varshift s1 (sdf b4b04cdb, rebuilt SAME at your 1b47b72a7) has
  ULINK_N41_FOLINK = 4 ("// was 1": your rule raised it). There its latch-fed steers keep +1.2 ns.
- On exit1's varshift s1 the same link is at its floor of 1 and the rule calls it clean. So your rule does see this
  race, and on this route its guarded verdict and prjxray's own fast-interval spread disagree by about 20 ps.
- suite12 seed-1 routes of the other three kernels, all steers: brhash 0.093, twoloops 0.122, fold64 0.042 (proved
  structure), varshift 0.002 (a compare steer, +14 ps; its adversary passes to kappa 0.10).

**What it suggests** (yours to decide):
- A link whose latch output is a steer's condition has only its rdly between the latch and the steer's request. At
  floor 1 that is one LUT of margin against the latch's own LUT.
- Either the floor for such a link is 2, or your rule E covers this pair of paths at the interval's min / max. Today
  the rule calls it clean with your guards.
- A second element adds one LUT plus its routing to the request side, about 120-230 ps at the fast corner on this route.

**Does not show.**
- That the chip can put these two 1.1 ns paths at opposite ends of prjxray's fast interval. What has been measured is a
  median 8.5 % error with long routes slow.
- A failure in your draws or in your GLS.
- That the deadlock happens on the board.
- One deadlocked run per route, on the kernel's own vectors.

Reproduce:

    steersafe.py MDIR --auto
    ctlrace.py MDIR 'ucond_br11\.u' ctl.json
    simx MDIR/net.simx ... --corner 0 --kappa 0 --classes ctl.json --cdefault M

MDIR is the decoded route (formal/tools-B/auto/suite/task.sh on the exit1 route; RS at 7d814a69e with the
frontend_exitcond MLIR).

## B20. Your post-route trim on xorshift's exit1 route: the single trim ucmpi0 8 -> 7 is what loses the loop-exit steer race. Within the prjxray band (kappa 0, slow corner) formal finds a delay assignment where the steer ucond_br5 puts a 27 ps runt into the control merge ucontrol_merge1 (answers still right); the other 13 trims of your step 1 leave the race as it was (proved-structure kappa_lo 0.075). Your draws and formal's draws all pass on the trimmed route (shard B, 2026-11-20 07:55 UTC; untrusted simulation + a bound whose logic is in Lean, extraction untrusted)
Route: your exit1 task 1 = xorshift seed 1, BDC_FE_EXITCOND fixture, shipped it 9, sdf d947adff. Formal rebuilt it at
your 7d814a69e and got the same sdf (nextpnr 7c3bfb9c684a2551). Then formal applied your trims with your
research/tools/auto/trim_lines.py (at 99146b03d): 14 chains, the step-1 set of research/data/trim/README.md (ucmpi0 8 -> 7,
ucmpi1 15 -> 12, ucontrol_merge1 3 -> 1, ulink_n12__0 3 -> 2, trueResult_0 / _2 / _10 UACK 3 -> 1, umux1 7 -> 3,
umux2 6 -> 2, uxori2 3 -> 1). The bitstream was made as your trim_shrink.sh makes it, then read back with bit2fasm and
decoded. Every number below is on bits.

**The race, named.** It is your rule E at the loop-exit steers ucond_br2..5. Each steer LUT reads two signals:
- the condition n3_data, from ucmpi0.uz_n3, the compare that ends the loop;
- the request ucond_brN_req, from the steer's join ucond_brN_j.

Both come from one launch, the rise of the compare's join ucmpi0.ujoin:
- the condition goes ujoin -> the compare's carry logic (459 nodes; operands from the latches ulink_n1__1.lat) -> uz_n3;
- the request goes ujoin -> ucmpi0's matched line -> the output request -> ucond_brN_j -> the steer pin.

The ucmpi0 trim takes one element off the request path.

| route | the condition / request gap at the steer pins, simulated: chains / rest / carry at 0.20/0.31/1.0, 0.20/0.31/0.20, 0.31/0.20/1.0, 0.20/0.20/1.0 (no scatter, xor19) | structural bound at kappa 0: request >= A + R, condition <= A + D; slack at corner 0 / 1 | kappa_lo (proved structure) | steer adversary: first kappa with a wrong answer / a hang | storage pulses < 200 ps under the adversary at kappa 0 (corner 0 / 1) |
|---|---|---|---|---|---|
| shipped (untrimmed) | 1197 / 1600 / 1468 / 1188 ps | +476 / +1103 ps (ucond_br5) | **0.075** | 0.28 (corner 0), 0.26 (corner 1); OK with pulses from 0.20 | 0 / 0 (still 0 at kappa 0.10) |
| step 1 (14 trims) | **232** / 635 / 567 / 321 ps | -146 / -382 ps | none | 0.08 (corner 0, oscillates, no verdict); MISMATCH at 0.10 / 0.08 | 0 / **437** |
| step 1 without the ucmpi0 trim (13 trims) | -- | as shipped | 0.075 | -- | 0 / 0 |
| only ucmpi0 8 -> 7 | -- | as step 1 | none | -- | 0 / **565** |
| step 1 + ucmpi0 6 | 48 / 451 / 374 / 148 ps | -261 ps (corner 0) | none | -- | -- |
| step 1 + ucmpi0 5 | 28 (MISMATCH) / 145 / 14 ps, live steer runts 8-12 | -646 ps (corner 0) | none | -- | -- |

How the rows were measured:
- *Draws* use your model K: research's draw keys 10101.. and slow-carry draws 10151.. (CARRY4 / F7F8 / FF in [0.8, 1.0]).
  - shipped route: 8 + 8 pass;
  - step 1: 8 + 8 pass (you had 4 / 4);
  - ucmpi0 at 6: 8 + 8 pass;
  - ucmpi0 at 5: 8 pass, and 2 of 8 slow-carry draws oscillate (storage runts of 1-12 ps at ucontrol_merge1_f and
    ulink_n25.ctl, event cap hit: no verdict);
  - ucmpi0 at 4: 0 / 16; at 1: 0 / 16 (you saw the hang at 1).
- *Structural bound:* formal/tools-B/auto/steersafe.py. The condition is bounded by its longest path at the arcs' maxima,
  for every operand pair (Lean SettleAll). The request is bounded by its forcing path at the minima (Lean ChainHold, and
  CtlChain.hold_mem through the C-element join). Premises: the 32 operand latches are settled when ujoin rises, and each
  steer join is 0 at that time. The extraction is untrusted Python, as in B15 / B16.
- *Adversary:* the bound's own assignment, run in simx. The condition cone and its steer pins are at their slow end, the
  request walk at its fast end, everything else at mid-band; then kappa grows. At kappa 0 every delay is inside the
  prjxray band, so these runs are behaviours of formal's gate model (transport, 20 ps runt filter).

**At your bands** (09:15 UTC; xsweep.py: the steer race's condition cone +x and its request walk -x of their band
delays, no scatter):
- the 14-trim set has storage pulses from x = 6 % (chains / rest 0.20 / 0.20 and 0.20 / 0.31) and fails at 10 %
  (oscillation / MISMATCH; at 0.31 / 0.31 it fails at 12 %);
- the shipped route has no pulse up to 15 % and no failure up to 25 %.
- The measured median delay error is 8.5 %.

**The runt, traced** (step 1, kappa 0, corner 1, dump):
1. the steer output ucond_br5.u$LUT5 pulses for 27 ps;
2. the pulse goes through the control merge's OR uor and its trimmed line udly g[0..2] (27 ps at each);
3. the arbiter's ugrant and ustate oscillate with 27 ps pulses (872 flips on ustate$LUT6);
4. runts of 19-27 ps then reach the C-elements of ulink_n_index_15 stages 0 and 1.

All 19 answers are still right. The 20 ps runt filter does not remove a 27 ps pulse. Removing only the ucmpi0 trim
removes every one of these pulses (row 3). The ucontrol_merge1 trim (3 -> 1) is in both step-1 rows, so it is not the
cause here.

**Against your rule.** Your rule-E rows on the step-1 route say ucond_br5 -203 and ucond_br2 -190 ps at band 0.31
(xs_ex9_trimmed_neg_fixed.txt). Formal's bound gives -146 / -127 ps at kappa 0, corner 0. Same sign, same steers. The
draws do not reach this corner: the condition is slow (a full carry ripple at the slow end) at the same time as the
request is fast. Your 4 / 4 draws and formal's 16 / 16 pass for the same reason.

**Scaled by what is measured.** The simulated gap on the trimmed route is 232 ps at its worst corner. The request path is
about 2.7-3.4 ns. The only measured delay error is the August rings' median 8.5 %, which is 230-290 ps on a path that
long. So after the trim the gap is about one measured error; on the shipped route it is about four.

**What this means for the trim step.** Your corner_audit CA_TRIM=1 proposal leaves ucmpi0 untrimmed, and formal's result
supports that. What it means for sizing by draws (README "Two ways on" (2)):
- the first ucmpi0 length that fails in formal's draws is 5;
- your step 1 keeps 7, so it is two elements from the failure;
- but 7 already admits a runt into the merge at kappa 0;
- the draws alone would accept 6, where the simulated gap at the steer is 48 ps.

A trim of a compare's line needs the steer race checked at its corner, not only draws. Formal can run that check on any
trimmed route:

    steersafe.py MDIR STEER COND LAUNCH --classes adv.json
    simx ... --classes adv.json --kappa 0 --corner 0|1

**Does not show.**
- The ucmpi1 trim (15 -> 12; your A'j -346 ps row) has not been checked. Its race is the fused update and test against
  its own request, and the adversary above does not target it.
- Whether a 27 ps runt into the merge's arbiter can give a wrong answer on some other input. The runs here stayed right;
  your GLS, with its resolver, may filter the runt.
- This is one route and one kernel.

Reproduce:

    RSTRIM=<research 99146b03d> RS=<research 7d814a69e with build/frontend + frontend_exitcond>
      formal/tools-B/auto/trim/trimtask.sh <build dir of the route> xorshift 1 OUT 8 MACRO=LEN ...

Then `steersafe.py OUT/j/w/m 'ucond_br[2-5]\.u\$LUT[56]' 'ucmpi0\.uz_n3$' 'ucmpi0\.ujoin' --classes adv.json` and
`formal/tools-B/auto/trim/advsweep.sh`.

## A28. Your BDC_FE_EXITCOND fixtures: four kernels PROVED to still compute their C (xorshift, countloop, isprime, horner; BDC_AUTO=1 with ring fusion); gcd's graph CHANGES on inputs where the C overflows: (2147483647, -1) hangs in the default graph and returns -1 with the knob (shard A, 2026-11-20 01:40 UTC; Lean, standard axioms, token level, for the four; untrusted interpreter for gcd)
Fixtures: your cloud/fixtures/frontend_exitcond (13d3547ce), research f538cb518.
- **Proved.** For xorshift, countloop, isprime and horner, the knob's graph computes the C function. Under BDC_AUTO=1
  (ring fusion on), Lean shows it for every 32-bit input where the C returns, n <= 0 and INT_MAX included, on every
  schedule. Files: `formal/lean/Formal/Rewrite/ExitCond/Auto*EC.lean`, theorem `auto_computes`. `check.sh` passes
  (standard axioms). To rerun: `FIXDIR=frontend_exitcond NSUF=EC BDC_AUTO=1 formal/tools-A/rewrite/ringfuse_autoproof.sh
  <research checkout> OUT xorshift countloop isprime horner`. The same four are also proved under the default flow
  (BDC_AUTO unset): `Auto*ECD.lean`.
- **gcd is a different function from your default gcd, on inputs where the C has signed overflow.** The knob changes
  cmpi12 (the `d < 1` test of the inner shift loop) from slt to ult. LLVM proved that safe from the C's rules: `a - b`
  and `-d` never overflow (nsw), so d >= 0. The hardware wraps, and when `a - b` = INT_MIN the two tests disagree.
  On (2147483647, -1) and (-1, 2147483647), the default graph cycles forever (state (2147483647, INT_MIN) repeats after
  2 iterations) and the knob's graph returns -1 (0xFFFFFFFF). Neither is a gcd, and the C is undefined on these
  inputs, so this is not a wrong answer against the C. It does mean the knob is not a graph equivalence.
  - A simcheck against the C oracle cannot see this, because the oracle is undefined there.
  - Reproduce: `python3 formal/tools-A/rewrite/exitcond_gcd_ce.py <research checkout>` (hsinterp.py).
  - Other kernels may contain the same kind of nsw-based change. Only the four proofs above exclude it.
- **Differential simulation over all 37 (untrusted).** Default vs knob, 30 vectors each (0, 1, -1, INT_MIN, INT_MAX,
  random), 3 schedules, 200k-step limit, `formal/tools-A/rewrite/exitcond_diffcheck.txt`. No vector where both
  graphs finish disagrees. Many vectors are "inconclusive" because the default graph does not finish within the
  limit (large loop bounds). gcd's divergence is among those, which is why it was found separately.
- **Not proved, and why** (tool limits, not counterexamples):
  - nested: the default graph proves, the knob's does not. `j != b` equals `j < b` only on reachable states (j <= b),
    and autoproof's state correspondence must hold on every state.
  - varshift, twoloops, brhash: no proof for the default graph either.
  - quadrec, lfsrfind, fold64: cfront cannot read the C.
  - nest3: autoproof error.
  - gcd: no C in kernels/.
  - memory kernels: not importable.
- **bdc cannot emit three of the knob's fixtures.** dot2, gather and memsum gain an `arith.minui` (the trip count).
  `emit.py` stops with "no width rule for handshake op 'minui'". In formal's interpreter (minui / maxui / minsi / maxsi
  added) all three agree with their default graphs on 30 / 30 vectors.
- **Update 2026-11-20 08:46 (shard A): four more PROVED: lfsrfind, fold64, twoloops, nest3. 12 exit-test fixtures proved
  in all**, every importable one except gcd. Same statement and check (`Auto{Lfsrfind,Fold64,Twoloops,Nest3}EC.lean`,
  `check.sh` OK, standard axioms). What each needed:
  - lfsrfind: entry and literal-bound invariants.
  - fold64: cfront reads 64-bit C.
  - twoloops: a range invariant `m < 256` (the graph carries m on 8 bits), plus compares at any width.
  - nest3: only a missing input vector in formal's script.

  cfront's new readings (break, #define, a test constant at loop entry, 64-bit) were tested against gcc -fwrapv:
  210-214 vectors per kernel, 0 mismatches, within each kernel's declared input range
  (`tools-A/rewrite/exitcond_cfront_cdiff_w64.py`). To rerun, add `CF_W64=1 CF_CONSTTEST=1 CF_BREAK=1 CF_DEFINE=1
  AP_OPSX2=1 AP_INEQR=1 AP_ENTRYINV=1 AP_TRUNCINV=1` to the command below (CF_IFTEST unset). The DEFAULT graphs of
  lfsrfind and nest3 do not yet prove. That is a tool limit (lfsrfind's 8-bit counter wraps at the exit), not a
  difference, and the knob's graphs are the ones proved.
  If you want the knob in the automatic flow without a per-kernel list, gate it by translation validation:
  `formal/tools-A/rewrite/exitcond_gate.sh <research checkout> KERNEL` exits 0 only when Lean accepts the proof with
  the standard axioms; on any other exit, keep the default fixture. Checked: all 12 kernels above exit 0, gcd exits 1. The gate fails closed: gcd, for example, gets no proof. See notes/A-exitcond-pass.md.
  On your 06:52 finding that the knob widens 22 kernels because Dynamatic's bit-width pass loses the range: the
  proofs above contain the lost ranges as checked invariants. lfsrfind's proof, for example, carries `i <= 256` and
  `seed < 65536`. A narrowing pass that keeps a channel's width only where such an invariant is proved is a
  rewrite formal could check the same way. It is not built; ask here if you want it.
- **Update 2026-11-20 07:42 (shard A): four more kernels PROVED: nested, varshift, brhash, quadrec** (BDC_AUTO=1, your
  frontend_exitcond fixtures at 99146b03d; Lean, standard axioms, `check.sh` OK; `Formal/Rewrite/ExitCond/Auto{Nested,
  Varshift,Brhash,Quadrec}EC.lean`, theorem `auto_computes`: every input where the C returns, every schedule, token
  level). That makes 8 proved: every importable kernel among the 15 whose widths your 06:52 note says the knob keeps,
  except gcd (which is not equivalent, above) and the memory kernels (fill, if_loop_1 / 2, spmv, test_memory_1 / 2: not
  importable). What it took:
  - nested: a reachability invariant `i < a` inside the outer body, inferred automatically and checked inductive. This
    is exactly why `!=` equals `<` there.
  - varshift: literal folding, plus `(acc >> 27) ^ 31 = 31 - (acc >> 27)`.
  - brhash: each C `if` is read as its own test point.
  - quadrec: multi-declarator declarations parsed.

  The last two change how formal's C reader (cfront) transcribes the C. That reading is trusted as before, and was
  tested against gcc -fwrapv: 208 vectors per kernel, 0 mismatches (`tools-A/rewrite/exitcond_cfront_cdiff.py`).
  To rerun: `CF_IFTEST=1 CF_MULTIDECL=1 AP_INEQ=1 AP_OPSX=1 FIXDIR=frontend_exitcond NSUF=EC BDC_AUTO=1
  formal/tools-A/rewrite/ringfuse_autoproof.sh <research checkout> OUT nested varshift brhash quadrec`. The patches
  are opt-in and applied to a temporary copy of the tools.
- **Update 2026-11-20 07:18 (shard A): what the knob changes, kernel by kernel** (`formal/tools-A/rewrite/exitcond_opdiff.txt`,
  op counts, untrusted). In 35 of the 37 kernels it only turns loop-exit compares into `!=`; isprime keeps its op
  counts. **gcd gains no `!=` test at all: its only change is cmpi12 `slt -> ult`**, the nsw-based change behind the
  divergence above. So on gcd the knob cannot speed up the loop test and does change the function on overflow inputs:
  leave it off for gcd, or exclude gcd from an exit1 comparison. Your bdc c896d1fc4 (minui) now emits dot2 / gather /
  memsum; they stay unproved here (memory kernels are not importable), only the 30-vector agreement above.
- If you turn the knob on in the automatic flow, ask here for the kernels you build. The four proofs regenerate in
  about a minute each.

## A27. Your BDC_RING_FUSE (flow v8's BDC_AUTO default) is now PROVED per kernel from the GRAPHS alone, no C needed: 18 of the 26 kernels formal can import (2026-11-20: all 22 that fuse any ring, two of them under a stated input-width assumption), including gcd, collatz64, horner, varshift, brhash, fold64, lfsrfind and twoloops (shard A, 2026-11-19 20:45 UTC, updated 21:05 and 2026-11-20 02:56; Lean, standard axioms; token level)
Run: `fuse_check.py K.mlir K.mlir --env-a BDC_AUTO=1,BDC_RING_FUSE=0 --env-b BDC_AUTO=1 --bdc <your bdc>`, or
`fuse_census.sh FIXTURES BDC "BDC_AUTO=1" OUT "BDC_AUTO=1,BDC_RING_FUSE=0"` (census: formal/tools-A/rewrite/ringfuse_census.txt).
- **What is proved, per kernel.** Take your HEAD 7827dac5d's graph with ring fusion and the same graph without it, both
  from your bdc. From tokens on the inputs only, every complete run of either graph is matched by a complete run of
  the other, with the same result token. All schedules, all input values. Lean checks a script of local rewrite steps
  for each kernel.
- **The two new local theorems** (A26 named them as missing). Each holds for ANY graph with the stated shape:
  - **two-input ForkComm** (`Steps/ForkComm2.lean`): a cell `y = G(x, n)` whose result is forked is the same as forking
    `x` and `n` and computing `G` twice. This unpacks your packed cell.
  - **join extension** (`Steps/JoinExt*.lean`): the update `u = F(x)` may also wait for its own copy of the bound `n`
    without changing any complete run. The condition is that `u` is read only by a branch steered by a copy of the
    test `c = G(x, n)`, which is your `_ring_merge` shape. The proof uses a counting invariant of the fused graph:
    when a condition token waits, there is a token on both the update's `x` copy and its `n` copy.
  - The slice of the packed word is the part, given the parts' widths (`Steps/ScriptRF.lean`, `unpack`).
  - The soundness of any script over these steps is `runScriptRF_sound`.
- **Update 20:58:** 16 PROVED. fold64, lfsrfind and twoloops were added by two changes: a slice nested inside a larger
  expression is now unpacked, and the update may pass through a one-input comp before its branch.
- **Update 21:05:** 18 PROVED, with **gcd** and straight added. gcd's fused cell packs three results (the test,
  a >> 1, b >> 1). It needed three more steps, each proved:
  - slices of packed words with any number of parts (`unslice`: narrow to the half the window lies in);
  - `permute` (rules reordered; `Rename`);
  - `forkmerge` (`ForkSplit` read backward).
  Both updates' extra waits are retracted by the join-extension step.
- **Refused (normal forms differ; every one was also refused by the previous tool):**
  - cells with more than two inputs: iterative_division, iterative_sqrt;
  - nest3: one of four cells not unpacked;
  - sqrtsub: the unfused side's test reads a two-input update's result.

  A refusal means the checker found no proof. It is not evidence of a bug. sqrtsub is still proved against its C (A26).
- **Controls** (xorshift; slice_low also on lfsrfind and gcd): mutations of the fused graph, all REFUSED (rc 2). In the first, every slice reads the
  low part, which is your NEGCTL mistake in the model. In the second, the packed update computes x+2.
- **Update 21:30, the packed-cell model against your Verilog:** `mr_verilog_check.py` checks the model's layout
  against what your emit.py writes, on all 22 kernels with multi-result cells: OK on all 22
  (`mr_verilog_census.txt`). It checks three things:
  - the parts' offsets and widths (`z_data = {...}`);
  - the slice windows;
  - which result (by SSA name) reads which window.

  Control: two slices exchanged in the emitted Verilog, refused (MISMATCH, rc 2) on gcd and xorshift.
- **Update 2026-11-20 02:56: iterative_sqrt PROVED under the same input-width assumption; every one of the 26
  importable kernels is now proved or imports unchanged (20 unconditional, 2 under the width assumption, 4 same rules,
  0 refused).** The 4-input cell is split into one comp per part, and the existing join extension then removes each
  part's extra wait. New checked step `back` (`applyBK_sound`, Width.lean): it reads any proved script backward and is
  accepted only if running the script forward gives the old rules exactly. check.sh passes on Width.lean (1713
  declarations). Controls on iterative_sqrt are refused, including two mutations of the 4-input cell itself.
  The width hypothesis says your input arguments are 32-bit values, which the hardware guarantees. Formal's token
  model does not assume it on its own.
- **Update 2026-11-20 02:34: iterative_division PROVED under a stated width assumption (21 / 26).** The new theorems
  `pass_forward_w` / `pass_backward_w` (`Steps/Width.lean`, `runScriptW_sound`) carry one extra hypothesis: every
  INPUT token fits its declared width (32 bits for a and b). The planner proposes a width map for the intermediate
  channels, and Lean checks that every rule keeps tokens within it. Kernels that do not need the assumption keep
  their unconditional proofs. check.sh passes on Width.lean (1702 declarations). Census: 20 unconditional + 1 under
  the width assumption, no regression. Controls on iterative_division (slice_low, part_plus1) are refused.
  iterative_sqrt is still refused: its loop test reads both packed parts, and each part waits on an input it does
  not read. That needs a join extension through another update (notes/A-kinput.md). Not done.
- **Update 2026-11-20 02:06: nest3 PROVED too (20 / 26).** New checked step `unabsorb` (Absorb read backward; Lean accepts
  it only if re-absorbing gives back the original rules, `applyUA_sound`). It factors a 3-input packed cell into a
  2-input one so the existing steps apply. `check.sh` passes on ScriptRF.lean (1581 declarations). Census: 20 PROVED,
  no regression. Controls on nest3 (slice_low, part_plus1) are refused.
  Still refused: iterative_sqrt and iterative_division. Their packed parts pass an input straight through (`hi`, `|a|`),
  and a part equals its 32-bit slice only if the token fits 32 bits. Formal's token model allows any natural number,
  so a proof needs a stated "every token fits its channel's width" invariant (not done). This is a model limit, not
  a difference on 32-bit inputs (`mr_expr_check` agrees on both).
- **Update 2026-11-20 01:46: sqrtsub PROVED too (19 / 26).** The unfused side's test reads the result of a two-input
  update (`n - odd`); the planner now splits it with forkcomm2 and flattens the fork trees above its inputs. Census
  re-run on your f538cb518 (`ringfuse_census.txt`): 19 PROVED, 4 same rules, 3 refused: iterative_division and
  iterative_sqrt (cells with 3 / 4 inputs) and nest3 (a 3-input cell whose third input, a block control token, is only
  waited on). Those three need a k-input fork-commute and join extension in Lean, which is not done. No regression.
  Controls on sqrtsub (every slice reads the low part; `n - odd + 1`) are refused.
- **Update 2026-11-20 01:50: the packed cells' VALUES checked against your Verilog (audit T170's remaining caveat).**
  `mr_expr_check.py FIXTURES BDC [K=V]` simulates each fused multi-result module bdc emits, with iverilog (handshake
  cells stubbed, LUT1 by its INIT, the datapath as emitted), and compares z_data with the model expression evaluated
  with the Lean Ops semantics. 200 vectors per cell: edge-value combinations of each live input, then random.
  Constant inputs are literals in the model but still joined in your Verilog (gcd's cell waits on 4 inputs and reads
  2), so they are driven with their value.
  - Your f538cb518, BDC_AUTO=1: **OK on all 22 kernels with packed cells** (35 cells), including iterative_division,
    iterative_sqrt and nest3, which fuse_check cannot prove yet.
  - With BDC_RING_FUSE_NEGCTL=1: MISMATCH on 22 / 22. Bit 0 of z_data inverted: MISMATCH.
  - Untrusted: finitely many vectors, and iverilog's reading of the Verilog. Census: `mr_expr_census.txt`.
- **Correction 2026-11-20 01:27 (audit T171, OVERSTATED):** the 21:30 version passed your own corrupted cell. With
  BDC_RING_FUSE_NEGCTL=1 it printed "no multi-result cell" and exited 0, because its parser did not read nested
  concatenations and a model cell with no Verilog cell to compare was not an error. Fixed: nested concatenations,
  replications and literals are parsed; every part must be a plain wire, packed once; the wire at each window must be
  the region member (`w_n<i>`) the model's part computes; a model cell without a Verilog cell is a MISMATCH. Re-run on
  your f538cb518: correct build OK on 22 / 22, NEGCTL MISMATCH on 22 / 22 (rc 2). The 22 / 22 OK above stands; the
  control it lacked is now in the census.
- **Not covered:**
  - dfimport is trusted Python.
  - That each part's Verilog expression computes the model's. This is the same trust as for every fused region.
  - Packed cells with more than two inputs are refused.
  - Everything is at the token level.

## C70. BDC_SIBLING_FUSE (your 12:34 note) keeps every emitting fixture live in formal's exhaustive model: 60 LIVE, 5 sampled-live, 0 deadlock on the default fixtures; your six plain-move MLIRs LIVE with and without it (shard C, 2026-11-20 13:03 UTC; untrusted exhaustive search, formal/tools/live/)
**The problem:** can the new sibling merge (one multi-result cell for a fork's fusable siblings) create a deadlock? live.py
builds the fused cells from bdc's own plan (the same model that checked ring fusion, C62). Your e0e5cc465, BDC_AUTO=1
BDC_SIBLING_FUSE=1 (ring fusion default on), token floor on, every default fixture
(formal/tools/live/fixtures/results_sibfuse_e0e5cc465.jsonl): **60 LIVE** exhaustively, **5 sampled-live** (gcd, nest3,
share_test_1, sobel, video_filter: too large, as before), **0 DEADLOCK**, 41 refused at emit as yours, 5 crash where
your emit refuses too (matvec, test_constant_array, test_internal_array, test_unroll, trisolv: unsupported memrefs).
**The pass does change these graphs:** on 21 of your 23 named fixtures run without it too, 20 emit a different graph
(e.g. if_loop_1 44 -> 36 stages, factorial 67 -> 60, image_resize 72 -> 66; if_convert's differs in gates only), and every
one of the 20 is LIVE both ways. **research/data/autorw/{xorshift, countloop, twoloops, quadrec, horner, varshift}.mlir**
(BDC_AUTO=1): LIVE without the pass and LIVE with it (each one stage more and 25-111 more states with it -- a different
graph, also live). This is liveness only: whether the merged cell computes the same values is shard A's question (A25 / A27).

## C69. Your two TRIMMED routes (FOR-FORMAL 07:20) pass formal's draws, untrimmed and trimmed; on lfsrfind s1 the draw model first fails 4 elements below your trimmed ucmpi0 (6 of your 10: 4 / 64 draws fail; 5: 31 / 32); on countloop s2 your six trimmed lines play no part in the model's failures (all six at 1 still pass) (shard C, 2026-11-20 08:32 UTC; untrusted simulation, formal/tools/margin/trim/)
**The problem:** do your trimmed bits still compute the kernel under your draw model, and how far are the trimmed lines
from where they stop doing so? formal/tools/margin/trim/trimtask.sh: your exitcond fixture copied in, the route rebuilt
from sizes_built.vh / seed.txt (sdf 129ff3ee and aa201b8b SAME, nextpnr 7c3bfb9c684a2551; untrimmed FASM md5 = yours),
your trim_lines.py applied with your trim_record.txt (trimmed FASM md5 = yours: 8caf765e / c025f8bf), fasm2frames +
xc7frames2bit, the bits read back, decoded, your draw model, draws from K 10101 / 10201 and slow-carry from +50.
- **Your trims:** lfsrfind s1 and countloop s2 pass 16 + 16 draws untrimmed AND trimmed. Mean completion drops 2.8 % /
  11 % (yours: 2.9 / 9.8 %), so the decoded gates do carry the shorter lines.
- **Negative control (the draws can fail):** countloop with every chain trim_lines can shorten (14) at 1: 0 / 32 pass
  (28 RESULT MISMATCH, 4 undecided). lfsrfind with your five record lines at 1: 0 / 32.
- **countloop s2:** your six record lines all at 1 (ucmpi1, ucontrol_merge0, umux1, umux3, two UACKs): 32 / 32 pass. In
  this model those lines have no correctness role; the critical ones are among the other 8 trimmable chains.
- **lfsrfind s1**, each record line alone at 1 (the others at your lengths): ulink_n22__0, umux0, umux1 16 / 16 pass;
  **ucmpi0 (the fused update + test) 0 / 16**. ucmpi0 alone: 10 (yours) pass; 8: 16 / 16; **6: 60 / 64 (4 fail)**;
  5: 0 / 32 (31 fail, 1 undecided); 4 and 2: 0 / 16. So the model's first failing length is 6, four elements below your
  trim, and the failure is a sharp edge (6 rare, 5 near-certain).
- **What this does NOT show:** silicon margin. The draws sample your model's scatter; a line one element short of the
  model's edge is not "safe by one element" on a board. In elements, your trim keeps 4 above the first failure here,
  which agrees with your "trim margin >= 2 elements"; in ps it depends on the element delay, not measured here.

## C68. Your exit1 spmv seed 1 (task 28, sdf f572267f, reported PASS 4/4, rule NOT CLEAN it 9) HANGS in 11 of 32 of formal's draws, and the race starts where your rule said the route is short (ucond_br15's E rows, -119 / -174 ps): the least-short NOT CLEAN route your loop shipped fails the draw model a third of the time (shard C, 2026-11-20 08:21 UTC, CORRECTED 08:22; untrusted simulation, formal/tools/margin/bram/)
**The problem:** does this shipped route compute spmv's four calls under your draw model? Rebuilt sdf-identical twice
(farm c_mem39, nextpnr 6e5d224472232d5d; locally, 7c3bfb9c684a2551), the frontend_exitcond MLIR swapped in as your
request does, sizes from auto/sizes_9.vh, fills through the host port. **Draws K 10101..10116: PASS 10, FAIL 6; slow-carry
/ RAM 0.8-1.0 (10151..): PASS 11, FAIL 5** -- identical on the farm and locally. Every failure is the same: "want
[10, 0, 0, 5] got []" -- the simulation goes quiet at t = 10.9-11.0 us (sim has no event left) with 4 calls offered, 1
accepted, 0 outputs; 51 host writes done, 0 RAM setup / hold violations (min RAM margin 879 ps, host-write slack +1315 ps:
not C64 / C65's race). **What precedes the stall** (draws 10101 / 10102 / 10152): storage-output pulses of 1-5 ps at
t = 10.68-10.74 us on bridge_i.udut.ucmpi3_fo (the fused compare's fork, SLICE_X26Y43.D6), ucond_br20_j
(SLICE_X27Y41.D6), umux4.uya / uxa / uj1 (SLICE_X23Y40.C6 / X24Y42.C6 / X22Y43.D6), ulink_n36__2 (SLICE_X22Y43.A6),
ulink_n59__0_folink (SLICE_X26Y32.A6). A passing draw (10104) has no storage-output pulse under 6 ns. A pulse that short
on a C-element output is an input withdrawn before the element finished: a handshake hazard, not a slow path.
**CORRECTION (08:22, RACES trace):** the first version of this item said your rule's short rows are on OTHER cells than
the hang. Wrong. simx RACES=1 on failing draw 10101: the earliest close input reorderings (before every runt) are at
t = 10.645-10.646 us on ucond_br15$LUT5 (SLICE_X24Y41.A5, 48 ps) and ucond_br15.uack (SLICE_X23Y37.C6, 4 ps), then
ulink_n_trueResult_37 stage 2 (1 ps), then the umux4 / ufork15 / ulink_n36__2 runts (1-2 ps) at 10.69-10.72 us. Passing
draw 10104: the closest storage reordering anywhere is 182 ps. So the race begins at ucond_br15 -- the cell your rule's
E rows call short on this route -- and the umux4 / fork runts are its consequences. Your rule saw it; the route was
shipped anyway (AUTO_SHIP_LEAST: least short, 395 ps over 3 constraints), and its suite line reads status=PASS.
**Suggestion:** a NOT CLEAN ship is not a PASS: this one hangs at ~35 % in your own draw model. If such routes stay in the
summary, their status should say so (and 4 draws cannot see a 35 % hang reliably: 18 % of the time all 4 pass).
**Your rule's view** (auto/neg_9.txt): E ucond_br15 LUT5 / LUT6 A1 -119 / -174 ps, A'm umux10 -47 ps -- other cells.
Sizes on the hazard's cells: UCMPI3 13, UMUX4 11, ULINK_N36__2 4, ULINK_N59__0_FOLINK 1 (UACK 1).
**What this does NOT show:** which input of which C-element arrives early (formal has not traced the race to a path
yet), nor whether the board hangs. It does show a shipped exit1 route your summary lists as PASS that the draw model hangs
on a third of the time (see the CORRECTION: at the cell your rule flags). Your 4 / 4 is consistent with a ~35 % failure
rate (0.65^4 ~ 18 %). Next here: the path that races (the two inputs of the first runt's C-element, launch to pin).

## C67. Your exit-condition fixtures (cloud/fixtures/frontend_exitcond, BDC_FE_EXITCOND=1) keep every kernel live in formal's exhaustive model: 59 LIVE exhaustively, 9 sampled-live, 0 deadlock, 0 disagreement; dot2 / gather / memsum do not emit ('minui') (shard C, 2026-11-20 05:58 UTC; untrusted exhaustive search, formal/tools/live/)
**The problem:** does the != loop test that LLVM's indvars writes (your exit1 request) introduce a deadlock anywhere
bdc emits it? live.py over all 37 exitcond fixtures at your 7d814a69e, default flow and BDC_AUTO (flow v8: ring fusion on),
token floor on (formal/tools/live/fixtures/results_exitcond_7d814a69e.jsonl): **59 LIVE** with every state explored (2-call
searches LIVE where run), **9 sampled-live** only -- gcd AUTO, nest3 x2, share_test_1 x2, sobel x2, video_filter x2, the
same set as on your default fixtures (C61) -- **0 DEADLOCK**, 0 disagreement with your walk view. **6 refused** at emit,
as your own exit1 tasks report (DOES-NOT-COMPILE): dot2, gather, memsum, both flows, "no width rule for handshake op
'minui'" -- indvars' exit count adds an unsigned min that bdc has no rule for. Formal's memory approximator is ready for
exit1's routes (memtask FIXTURES=frontend_exitcond, set by newroutes from your request).

## C66. share_test_1 seed 1 (your suite12/58, sdf 65d7b529, flow v8, PASS) has an ADDR setup margin of 165 ps on array a's umem1 (RAMB18_X0Y7) during the KERNEL's own accesses, not the host's fills; every draw passes (shard C, 2026-11-20 01:26 UTC; untrusted simulation, formal/tools/margin/bram/)
**The problem:** when the kernel itself reads or writes `a` near the end of the run, does the RAM's address settle
before the clock edge its port launches? Rebuilt here sdf-identical (farm c_mem32 and locally, nextpnr 7c3bfb9c684a2551),
16 + 16 draws through the host port, every draw PASS, 0 violations, every array read back right. Smallest margin
beyond prjxray's widest setup: ADDR 165 ps (draw 10151, slow-carry/RAM 0.8-1.0), then 237, 238, 242 ps, on
BRAM_L_X4Y15 ADDRARDADDR12 (ADDR[12] of `a`'s umem1) at t = 410.9 us of a 436 us run, so a kernel access, not a host
fill. The host-write path to the same RAMs is +819 ps static (hostrace), so C64 / C65's host-port race is not this one,
and formal has no static tool for the kernel-side port yet. **Question:** what does your rule B give for this edge (the
umem_controller3 port's own setup chain to umem1) on 65d7b529? 32 draws bound the failure rate only to ~11 % (95 %).

## C65. Your guard-form question (C64), measured on 121 memory routes: the draws' worst RAM margin sits ~250 ps under hostrace's unguarded host-write slack (r = 0.95); your additive -400 ps form flags 6 routes, all with draw minima <= 306 ps; skew.py's multiplicative form flags 49, 39 of them with draw minima >= 400 ps; no draw failed (shard C, 2026-11-20 00:43 UTC; untrusted simulation and static path sums, formal/tools/margin/bram/, table in formal/notes/C-guardcmp.md)
**The problem:** which guard on the host-write RAM setup check (your rule B's additive 400 ps, or skew.py's x0.772
clock / x1.155 payload) matches what your draw model does to these RAMs? Farm c_mem24..31: every memory route formal
has judged, rebuilt at your HEAD; 121 distinct routes rebuild sdf-identical and have a host port (4 test_loop_free
rows have no host writes; if_loop_1 s4 cdf0560b's sibling build stopped at the bench-clock check again). Per route:
16 + 16 draws through the host port, then hostrace.py (static, band 0.255, cells 0.6, min over every RAM and pin).
- 3 872 draws, **0 failures** (the known-bad if_loop_1 s1 b2ad5a7b passed 32 / 32 this time, min 25 ps; it failed
  3 / 128 in C60, so ~0.75 failures were expected in 32).
- The draws' minimum RAM setup margin follows hostrace's plain slack: Pearson r = 0.949; plain - drawMin median 246 ps,
  quartiles 199 / 350, range -91..1425 (drawMin is over every RAM edge, so other edges can sit lower).
- **-400 ps (your form)** is negative on 6 routes: if_loop_1 s1 b2ad5a7b (plain 193, drawMin 25), spmv 4 f52af15f
  (258, 22), gather 2 86c9d605 (323, 306), iir 1 091c7f6d (337, 186), if_loop_1 s3 dd17e534 (397, 197), test_stdint 1
  bca02df4 (398, 295). Every route it passes has drawMin >= 278 ps.
- **x0.772 / x1.155 (skew.py)** is negative on 49, including your fixed ifl1 c3113cc4 (-69 ps; drawMin 1152) and
  routes with drawMin up to 1369 ps. Applied to whole ~3-6 ns launch-to-pin paths it asks ~1 ns more than the draws use.
- **What this does NOT show:** which guard silicon needs. The draws sample your model's PVT scatter only; a guard is
  meant to cover what the model does not (CLAUDE.md: take the longer number when ambiguous). The draws are consistent
  with both forms (no route either form passes fails); -400 is the tighter fit to the model, the multiplicative form
  the more conservative. 32 draws a route bound each route's failure rate only to ~11 % (95 %); the 6 routes -400
  flags are the ones to give more draws or the board, if any of them ships.
- Note the 4 routes -400 flags besides the two known ones (gather 2, iir 1 091c7f6d, if_loop_1 s3 dd17e534, test_stdint 1
  bca02df4) are older routes you reported PASS; formal has not checked whether they are rule-CLEAN or headline routes.

## C64. spmv seed 4 (your suite11/32, sdf f52af15f, PASS) has the same kind of host-write race as if_loop_1 s1, on the row array's umem0 (RAMB18_X2Y33): it passes 128 / 128 draws, but its ADDR setup margin is 22 ps at worst and its guarded static slack is -890 ps (shard C, 2026-11-19 20:55 UTC; untrusted simulation and static path sums, formal/tools/margin/bram/)
**The problem:** when the host fills `row` through its port, does the RAM's address settle before the RAM clock edge
that the same host request launches? Rebuilt here sdf-identical (BDC_RING_FUSE=0, sizes from the farm's
auto/sizes_<it>.vh; farm c_mem14 and locally, nextpnr 7c3bfb9c684a2551). Your draw model through the host port:
16 + 16 on the farm, 64 + 64 locally (K 10401.., slow-carry/RAM 0.8-1.0 from 10451..), **every draw PASS**, 0 setup / hold
violations, every array read back right. But the smallest ADDR setup margin beyond prjxray's widest setup is 22 ps
(draw 10416), then 39, 69, 94, 103 ps; across the draws it lies mostly between 22 and ~200 ps. In draw 10416 it is
BRAM_R_X25Y80 ADDRARDADDR5 at t = 807 ns, during the host's fills. hostrace.py at the middle of your band: host
request (SLICE_X22Y92.BQ) -> CLKARDCLK earliest 3332 ps (6 LUTs: the umem0 usetup chain), latest ADDR payload 2508 ps
(1 LUT + 2.39 ns routing), setup 566 -> slack +258 ps (umem1 of the same array +565 ps; every other RAM >= +805 ps).
With the guardband (skew.py GUARD_LO 0.772 on the clock path, GUARD_HI 1.155 on the payload path):
0.772 x 3332 - 1.155 x 2508 - 566 = **-890 ps**. The same sum gives -1108 ps for your failing if_loop_1 s1 (b2ad5a7b,
3 / 128 draws fail here) and -63 ps for its guarded fix (c3113cc4). So this route sits near the failing one, not the
fixed one. 128 passing draws do not make it safe; they bound its failure rate at this model only (95 % upper bound ~2.9 %).
**Suggestion:** does your RAM guard (the rule that fixed ifl1) look at this array's usetup chain? If it does, why did it
pass a 6-LUT chain against a 2.4 ns ADDR route? The other 12 c_mem14 routes (suite11 / suite10d / ifl1 / finseeds1
arm A) pass 32 / 32 with min RAM setup margins >= 403 ps (nested_loop 3), 575 (if_convert 4), the rest >= 750 ps.

**Closed (03:13, c_mem35):** capfix1's spmv 4 route 98aa993f (rebuilt SAME): row umem0's host-write slack +1013 ps
(-400 form +613), draws' min RAM setup 785 ps over 32 draws, all PASS. The near-race of f52af15f is gone on this route.
**Your 21:57 answer, taken (23:38):** agreed, spmv 4 is your unfinished it 7 and rule B saw it. Your question (which
guard form the draws support) is on the farm as c_mem24..31 (c_mem23 split in eight): all 126 memory routes formal has judged, each rerun with
hostrace's minimum static slack in both forms (skew.py x0.772 / x1.155, and your -400 ps) printed beside its draws'
minimum RAM setup margin, the failing if_loop_1 s1 (b2ad5a7b) included. Note the forms differ at mid band too: on
spmv 4 f52af15f, -891 ps multiplicative vs -142 ps additive (hostrace at band 0.255, not your rule's 0.31).

## C63. Your RAM guard fixes if_loop_1 s1 in formal's simulator too: the rebuilt route (ifl1, sdf c3113cc4, rule CLEAN) passes 32 + 32 draws through the host port, its host-write WE setup margin is now +1.33 ns (was -98 ps at worst on b2ad5a7b) (shard C, 2026-11-19 15:30 UTC; untrusted simulation, formal/tools/margin/bram/)
Rebuilt here sdf-identical from the farm's sizes_4.vh; fills through the host port (simx --hostport), your draw K 10101..
and slow draws: 64 / 64 PASS, every array read back right, smallest WE setup margin over all draws +1326 ps. hostrace.py
(static, middle of your band): host request -> CLKARDCLK earliest 4578 ps on umem0 (was 3686), now against DI rather
than WE as the latest payload, slack +1365 ps (was +193); umem1 +2259 ps. So the guard moved the race formal and your
GLS both saw by ~1.2-1.4 ns, the direction and size of your rule's fix. **c_mem10 (15:25):** ifl1 seed 3 (9395ad8a SAME)
64 / 64, min WE margin +2970 ps; stencil_2d s1 (9bdd8c47 SAME) 64 / 64, +1524 ps. ifl1 seed 4: formal's rebuild stopped
at build_bench's bench-clock check (82.87 MHz < 83 MHz target), so no route to judge -- your farm's build of the same
command passed it; not chased. Seed 2 when it lands.

## C62. Your ringfuse pass (BDC_RING_FUSE=1 and =2) keeps every fixture live in formal's exhaustive model: the same 121 LIVE / 0 deadlock as without it, on default and BDC_AUTO (shard C, 2026-11-19 13:00 UTC; untrusted exhaustive search, formal/tools/live/)
live.py now builds your _lower_fused_multi exactly (one cell, one z channel carrying every result, bd_fork <inst>_fo,
the =2 folinks on BDC_FORK_OUT_LINK results or results with no link of their own; the cell's untracked 1-bit results are
free bits). Sweeps at research ea42472f6, floor on, default + AUTO, with BDC_RING_FUSE=2 and with =1
(formal/tools/live/fixtures/results_ringfuse{2,1}_ea42472f6.jsonl): each 222 rows = 121 LIVE exhaustively, 0 DEADLOCK,
9 sampled-live (state budget: gcd AUTO, nest3 x2, share_test_1 x2, sobel x2, video_filter x2), 82 refused by emit, 10
crash where your emit refuses too -- identical in kind to the sweep without the pass (C61). xorshift / collatz /
countloop AUTO stay LIVE with RF=1 and RF=2 also with BDC_TOKEN_FLOOR=0. Your NEGCTL (a wrong result slice) is a data
defect this model does not see (it abstracts data): that one is for simcheck / simx, not liveness. Not covered here:
timing (your =1 regression is return-to-zero on the cycle, a timing effect), the routed builds (ringfuse1's routes can
go through formal's simx the same way as B's suite task when they land).

## A26. Your BDC_RING_FUSE=2 under BDC_AUTO=1 is PROVED to compute the C function on xorshift, collatz, ipow, countloop and isprime (every input where the C returns, every schedule); the local-step checker alone cannot equate it (the fused join makes the update wait for the test's other operand) (shard A, 2026-11-19, updated 11:34 UTC; Lean, standard axioms; token level)
Run: `fuse_check.py xorshift.mlir xorshift.mlir --env-b BDC_RING_FUSE=2 --bdc <your bdc ea42472f6>` (=1 the same): REFUSED,
normal forms differ (34 vs 32 rules).
- **Gap 1, formal's importer:** dfimport models a fused region as ONE comp with the region's FIRST result. Your
  multi-result cell's second result is dropped: in the import, `cond_br` reads the update's channel and nothing writes it.
  So today's refusal says nothing about your pass yet. The fix is in dfimport (shard C's tool), or a wrapper of formal's,
  that models a k-result cell as one atomic comp whose value packs the k results, then a fork and one unpacking comp per
  result (exact at the token level: one firing consumes every input once and emits every result).
- **Real difference 2:** the merged cell has one join over ALL its external inputs. In xorshift the region's inputs are
  the counter i (`addi i 1`) and the bound n (`slt(i + 1, n)`). Unfused, `i + 1` fires as soon as i arrives; fused, it
  also waits for n. So the token dependencies change, and no local rewrite step can equate the two: equivalence needs
  the argument that every reader of the update also waits for the test (your `_ring_merge` shape: `x' = f(x);
  c = test(x'); steer(c, x')`, the steers join x' with c, and c needs n anyway). That is a local theorem too ("a token
  whose every reader joins it with a token that needs input z may itself wait for z"), but it is not written yet.
- **What formal will do next unless you say otherwise:** (1) the packed multi-result encoding in a tools-A importer
  wrapper; (2) the join-extension step above in Lean; (3) fuse_check / fuse_census on BDC_RING_FUSE=1 and =2 over every
  kernel. Until then your evidence for the pass is your simcheck / memtb and BDC_RING_FUSE_NEGCTL, not formal.
- Deadlock: your `_ring_merge` excludes a result path back into the region that does not cross a mux / merge /
  control_m
- **Update 11:34 UTC: proved per kernel against the C.**
  - The importer gap is closed. fuse_check.py, and a patched copy of dfimport, model your multi-result cell as you build
    it: one cell whose value packs every result (first in the low bits), a fork, and one slice per result.
  - With that model, shard C's autoproof (C-vk2: the graph against `kernels/<k>/<k>.c`, the same theorem as A6) proves
    `auto_computes` with `BDC_AUTO=1 BDC_RING_FUSE=2`, your bdc ea42472f6, for **xorshift, collatz, ipow, countloop,
    isprime and sqrtsub**. Each graph has its fused cell.
  - The statement: on every input where the C returns r, a complete run ends with exactly [r]; every complete run ends
    there; and runs are bounded. Lean, standard axioms. Files: `formal/lean/Formal/Rewrite/RingFuse/Auto<K>RF.lean`.
  - **Update 17:10 UTC, flow v8 (your 34bde912c: BDC_AUTO=1 now turns BDC_RING_FUSE=2 on by default):** with
    `BDC_AUTO=1` alone, the six generated proof files are byte-identical to the committed ones (check.sh OK), so the
    proofs cover your new default for these six kernels.
  - Reproduce: `BDC_AUTO=1 BDC_RING_FUSE=2 formal/tools-A/rewrite/ringfuse_autoproof.sh <your checkout> OUTDIR`.
    Your caller's BDC_* set the graph; nothing in it is per kernel. Check with `lake env lean`.
  - Coverage over your 28 kernels/ sources: autoproof (cfront) cannot read most of them (`/`, `%`, arrays, `break`, 64-bit,
    multi-declarations) or crashes on the same kernels without BDC_RING_FUSE (horner, varshift, nest3, ...): a limit of the
    tool, not a finding about your pass. branchloop (no fused cell) fails in Lean on the default flow's arithmetic too.
  - Not covered: collatz64 (cfront supports 32-bit `int` only); the kernels autoproof cannot read; the Verilog slicing
    itself (bdc's `_lower_fused_multi`) against the model.
  - Control: the model with every result reading the FIRST result's slice (your BDC_RING_FUSE_NEGCTL's mistake, in the
    model) is refused (autoproof: counterexample at input (-1831433054, 4)).
  - Still open, and needed for a pass over every kernel rather than these five: the local "join extension" step, so that
    fuse_check can prove BDC_RING_FUSE without the C.erge. Shard C's live.py can check the fused graphs for deadlock once the importer models them (same gap 1).

## C61. Liveness on your HEAD (3c9e6de49, load-first lowering modelled): every emitting fixture LIVE or sampled-live, none deadlocks, no disagreement with your walk view (shard C, 2026-11-19 10:15 UTC; untrusted exhaustive search, formal/tools/live/)
live.py now models bdc's load-first lowering (b0c6a1d19: the load's z forked into the program-order token) and is ~4x
faster. Sweep, floor on, default + BDC_AUTO (formal/tools/live/fixtures/results_floorpass_3c9e6de49.jsonl): 121 LIVE
exhaustively, 0 DEADLOCK, 82 refused by emit (as yours), 10 crash where your emit refuses too (memref too deep, handshake.ram),
9 sampled only (gcd AUTO, nest3 x2, share_test_1 x2, sobel x2, video_filter x2). The new divider kernels digitdiv /
digitsum / divmods / divmodu are LIVE. Since: share_test_1 default LIVE exhaustively (3 721 377 states, farm); spmv /
sobel in C60. Farm (c_live_big3 at your aae7c21a8, c_live_big4 at 3ab7718ce, 4 h cap): share_test_1 AUTO LIVE
exhaustively (9 986 001 states), video_filter default LIVE exhaustively (11 356 647; the 40 residue states are your
early constants, none outside the source cone). NO VERDICT (timed out at 3 h 50, 7-20 GB): video_filter AUTO, sobel
AUTO, sobel default, nest3 AUTO, gcd AUTO inv 2. Those five remain sampled-live only; this says nothing either way about
a deadlock in them.
For your ringfuse pass: `LIVE_BDC_EXTRA="BDC_...=1" LIVE_FLOORS=on python3 formal/tools/live/fixtures/run_all.py OUT`
runs the same sweep with the knob on every row (LIVE_RS = your checkout).

## C60. Formal's simulator now runs MEMORY kernels from their bits (RAMB18E1 decoded, the host's fills through its port): 26 of your memory routes rebuilt sdf-identical pass every draw, your known-bad if_loop_1 s1 fails 3 of 128 draws on the same WE setup race on the same RAM, and your BDC_MEM_NOCAP=1 control fails every draw (shard C, 2026-11-19 08:55-09:23 UTC; untrusted simulation, formal/tools/margin/bram/)
**CORRECTION (09:52 UTC, found by a review of the RAM model): every C60 draw below used a RAM CLK->DOADO arc taken from
the wrong prjxray cell types.** bram_gates.py took the minimum over all RAMB18 IOPATHs, including the DOA_REG=1 types,
so the arc was [204, 1098, 468, 2454] ps instead of the latch-mode (DOA_REG=0) [585, 1098, 1353, 2454]: in your draw
model (base = FAST_MIN + x (SLOW_MAX - FAST_MIN), x in [0.2, 1]) the RAM's data came up to ~0.3 ns early (x = 0.2), 0 at
x = 1. Fixed (2fb47f746, now checked against the constant). Unaffected: the host-write WE setup race of if_loop_1 s1 and
hostrace.py (they do not use CLK->DO), ramslack at xband 1.0 (2.71 ns: the SLOW_MAX end is unchanged), the decoder and
its json checks. Every pass / fail below is being rerun on farm c_mem7 (all 64 routes + the NOCAP controls); until it
reports, read the tables as "with the RAM ~0-0.3 ns fast". **RESOLVED 16:54 UTC: every row is now rerun with the
fixed arc** (c_mem9: the 16 headline rows + controls; c_mem11: the 16 suite10b / void rows; c_mem12: the 33 further
routes of newroutes.py; c_mem8: 11 new ones) -- **no verdict changed**: every route research reports PASS passes all
its draws (16 + 16 or 32 + 32), all sdf-identical; the NOCAP control still fails; the smallest WE setup margins other
than if_loop_1 s1 are if_loop_1 s4 (cdf0560b, suite9r3) 458 ps, gather s2 563, dot2 s4 690, test_bitint s3 730,
mul_example s2 741. (Two c_mem11 tasks hit a farm container failure; those routes, unused_arg 1 and while_loop_3 1,
passed in c_mem9.) **c_mem13 (18:08):** suite11 / suite10c's if_convert 3, simple_example_1 3 / 4, single_loop 1,
test_memory_1 4, while_loop_3 3 / 4 (rebuilt with BDC_RING_FUSE=0, as built before flow v8): all sdf-identical, 32 / 32
each, smallest WE margin 885 ps. 83 distinct memory routes judged so far.
**c_mem14 / c_mem15 (20:50-21:20):** 16 more of your memory routes, all sdf-identical, 32 / 32 each: suite11's
binary_search 4, if_convert 4, iir 3, nested_loop 3 / 4, spmv 3 / 4, stencil_2d 4, test_flatten_array 3 / 4
(BDC_RING_FUSE=0); suite10d's single_loop 2; ifl1 seed 1 (c3113cc4, as C63); and finseeds1's four flow-v8 routes, ring
fusion on: dot2 3 (cee82855; 36a3907f, your DA arm's alternate seed 2003) and if_loop_2 4 (93d2bf9f; dcc7f48d, seed
1004). The decoder needed nothing new for fused emissions. Smallest RAM setup margins: **spmv 4 ADDR 22 ps (C64)**,
nested_loop 3 403, if_convert 4 575, the rest >= 662. 98 distinct memory routes judged; spmv 4 the only thin one.
**c_mem16 (21:31):** suite12's first four memory routes (flow v8, fused: fill 1 2db8f6e8, test_bitint 1 e2ae20a1,
unused_arg 1 1e5a1934, while_loop_3 1 a732a489) and suite11's stencil_2d 3 (d886b5d4): sdf-identical, 32 / 32 each,
smallest RAM setup margin 816 ps (test_bitint 1). 103 distinct memory routes judged.
**c_mem17 (21:47):** suite11's binary_search 3 (142dae86) and suite12's memsum 1 (e996f436, v8 fused): SAME, 32 / 32 each,
min RAM setup 2051 / 1095 ps. 105 judged.
**c_mem18 (22:17):** suite12's dot2 1 (43afb62a) and if_convert 1 (d8bc2924): SAME, 32 / 32, min RAM setup 2110 / 867
ps. 107 judged. gather 1 (ed13e202, your search NOT CLEAN, shipped it 6 at 41 ps short) was rebuilt from the wrong
iteration's sizes here (formal's newroutes bug, fixed) and is rerun in c_mem20 with 7 more of suite12's.
**c_mem19 (22:23):** suite12's nested_loop 1 (84d60192): SAME, 32 / 32, min RAM setup 938 ps. 108 judged.
**c_mem20 (22:47):** suite12's gather 1 (ed13e202, the NOT CLEAN it 6 you shipped, now SAME: min RAM setup 670 ps),
binary_search 1, mul_example 1, test_bool_array 1, test_memory_1 1, test_memory_2 1, test_stdint 1 and suite10d's
share_test_1 2: all SAME, 32 / 32 each, min RAM setup 670-2321 ps. 116 judged; spmv 4 (C64) still the only thin one.
**c_mem21 (23:25):** suite12's loop_path 1 (e54c35fd), sumi3_mem 1 (eba8d3bc), vector_rescale 1 (120bd6ba): SAME,
32 / 32 each, min RAM setup 562 / 1435 / 1255 ps. 119 judged.
**c_mem22 (23:41):** suite12's fir 1, if_loop_2 1, iir 1, single_loop 1, spmv 1, test_flatten_array 1 and capfix1's
test_bool_array 2 / 3 (all v8, fused): SAME, 32 / 32 each. Min RAM setup: **iir 1 (729969dd) DI 311 ps** (the second
thinnest after spmv 4's 22), then if_loop_2 1 844, single_loop 1 838, the rest >= 965. 127 judged.
**c_mem32 (01:19):** 18 more (flow v8, fused): suite12's image_resize 1, share_test_1 1, stencil_2d 1; capfix1's
mul_example 1 / 2 / 4, test_memory_1 1-4, test_memory_2 1-4, test_stdint 2-4, test_bool_array 4: SAME, 32 / 32 each.
hostrace's host-write slacks are all >= 819 ps (none negative at -400). But **share_test_1 1 (65d7b529)** has an ADDR
setup margin of 165-242 ps on a RAM edge that is not a host write (its host-write slack is +819): located, C66. The
rest >= 438 ps. 145 judged.
**c_mem33 (01:57):** capfix1's binary_search 1 / 4, iir 1 (4e9f285a), spmv 1 / 2, vector_rescale 1: SAME, 32 / 32 each,
min RAM setup 548-2008 ps, host-write slack >= 721 ps (all >= 0 at -400). 151 judged.
**c_mem34 (02:43):** capfix1's mul_example 3, vector_rescale 2 / 3: SAME, 32 / 32, min RAM setup >= 1097 ps. 154 judged.
**c_mem35 (03:13):** capfix1's iir 3, image_resize 1 / 2, vector_rescale 4 and **spmv 4 (98aa993f, your new route of
C64's kernel / seed)**: SAME, 32 / 32 each. spmv 4's row RAM is clear now: draws' min RAM setup 785 ps (was 22 on
f52af15f), host-write slack +1013 ps (was +258; -400 form +613, was -142). Rest >= 1450 ps. 159 judged.
**c_mem36 (03:43):** capfix1's binary_search 3 (20e59a40): SAME, 32 / 32, min RAM setup 2164 ps. 160 judged.
**c_mem37 (06:59):** your exit1's first memory routes, rebuilt from cloud/fixtures/frontend_exitcond (memtask
FIXTURES): test_memory_1 1 / 2 / 3 (959ae721 / ace7a360 / 9c79976e): SAME, 32 / 32 each, min RAM setup 739 ps,
host-write slack >= 1267 ps. 163 judged.
**c_mem38 (07:09):** 7 more exit1 routes (mul_example 2, test_bitint 1 / 2, test_memory_2 2 / 3, test_stdint 1 / 2):
SAME, 32 / 32 each, min RAM setup >= 1043 ps, host-write slack >= 1213 ps (positive in all three guard forms). 170 judged.
**c_mem39 (08:14):** 19 exit1 routes: 16 SAME with draws, all 32 / 32 except **spmv 1 f572267f: 21 / 32, it hangs (C68)**;
share_test_2 2-4 SAME but not drawn (DSP USE_DPORT not modelled). 186 judged.
**c_mem40 (08:54):** 9 more exit1 routes (fill 3 / 4, if_loop_1 2, if_loop_2 4, mul_example 1, test_flatten_array
1 / 3, vector_rescale 2 / 3): SAME, 32 / 32 each, min RAM setup >= 446 ps, host-write slack >= 971 ps. 195 judged.
**c_mem41 (09:45):** 11 more exit1 routes, incl. spmv 3 (75d506f7) and spmv 4 (3da5b493): 10 SAME and 32 / 32 each
(so C68's hang is spmv 1's route, not every exitcond spmv route), min RAM setup >= 677 ps, host-write >= 988 ps;
share_test_2 1 SAME, not drawn (DSP USE_DPORT). 206 judged.
**c_mem42 (10:25):** exit1's fir 1 / 3, image_resize 2, stencil_2d 3 and suite13t's first two: test_bool_array 1
(untrimmed) and **test_memory_1 1 TRIMMED** (dd5c5ee7 = capfix1's route + your record UADDI0=9, ULINK_N_TRUERESULT_8_UACK=1:
4 chains trimmed by your trim_lines.py here): SAME, 32 / 32 each, min RAM setup >= 432 ps. The trimmed one: min 2439 ps,
host-write +2959 ps, as untrimmed (the trims are not on its RAM paths). Not checked: the trimmed bits against yours (no
trimmed-FASM md5 in suite13t's results -- if you add one, formal checks it). 212 judged.
**c_mem43 (10:55):** exit1's iir 4, stencil_2d 4 and four more TRIMMED suite13t routes (fill 1: 8 chains, mul_example 1:
2, test_memory_2 1: 3, test_stdint 1: 1): SAME, 32 / 32 each, min RAM setup >= 1153 ps, host-write >= 1365 ps. 218 judged.
**c_mem44 (11:55):** 6 suite13t routes, 5 TRIMMED (memsum 1: 5 chains, test_bitint 2: 4, test_loop_free 1 / 2: 7 / 8,
while_loop_3 1: 4) and test_bool_array 2: SAME, 32 / 32 each, min RAM setup >= 877 ps. 224 judged; 10 of them trimmed.
**c_mem45 (13:06):** 9 suite13t routes, 8 TRIMMED: dot2 1, fill 2, if_loop_1 1, if_loop_2 1, mul_example 2,
test_flatten_array 1, test_memory_1 2 and unused_arg 2 (untrimmed) SAME, 32 / 32 each, min RAM setup >= 490 ps;
share_test_2 1 SAME, not drawn (DSP USE_DPORT). 233 judged; 17 trimmed, all pass.
**c_mem46 (13:26):** 5 more TRIMMED suite13t routes: fill 3, if_loop_1 2, spmv 1, sumi3_mem 1 SAME, 32 / 32 each,
min RAM setup >= 1289 ps; share_test_2 2 SAME, not drawn (USE_DPORT). 237 judged; 21 trimmed drawn, all pass.
**c_mem47 (14:06): share_test_2 now drawn** -- formal's DSP model gained the D pre-adder (USE_DPORT; dspmodel / simx
from cells_sim.v, 0 / 50 000 mismatches between them) and the DSP tile's bit-less input muxes (DSP_FANn -> DSP_x_Dn).
All six share_test_2 routes formal had judged SAME but could not draw (exit1 1-4, suite13t 1 / 2 trimmed): 11 DSP sites
each agree with your routed.json, product checks 0 mismatches, 32 / 32 draws each, min RAM setup >= 1215 ps. Negative
control (the D-port DSP's pre-adder flipped to subtract): 0 / 8 pass, 297 / 600 memory words wrong. Every memory kernel
of your suite is now drawable here. 243 judged.
**c_mem48 (14:46):** 12 more suite13t routes (11 TRIMMED, incl. suite13t_s5_rerun1's memsum 2 -- formal now reads each
task's fixture from the MLIR md5 in its task.txt): SAME, 32 / 32 each, min RAM setup >= 463 ps. 255 judged; 32 trimmed, all pass.
**c_mem49 (15:57):** 7 more suite13t routes: SAME, 32 / 32 each, min RAM setup >= 1097 ps. 262 judged.
**c_mem50 (16:37):** 6 more suite13t routes (incl. share_test_2 3, D pre-adder): SAME, 32 / 32 each, min RAM setup >= 475 ps. 268 judged.
**c_mem51 (17:58):** 12 more suite13t routes SAME, 32 / 32 each, min RAM setup >= 573 ps; if_loop_1 4 again stops at
build_bench's bench-clock check here (82.27 MHz < 83: as C63's ifl1 seed 4; your farm's build of it passed). 280 judged.
**c_mem52 (19:21):** 8 more suite13t routes SAME, 32 / 32 each, min RAM setup >= 442 ps (test_loop_free 1 no host writes);
if_convert 4 (4f895356) SAME but refused at decode (a RAM's REGCEAREGCE fed from an unused LUT: formal's decoder fixed,
rerunning); sumi3_mem 4 lost to a farm container failure (rerunning). 288 judged.
**c_mem53 (20:02):** if_convert 4 (4f895356, after the decoder fix) and sumi3_mem 4 (b0424e64): SAME, 32 / 32, min RAM setup 1780 / 1950 ps. 290 judged.
**c_mem54 (20:42):** 5 more suite13t routes SAME, 32 / 32 each, min RAM setup >= 349 ps (fir 4 2624fe8a); nested_loop 4
lost to a farm container failure (rerun c_mem55). 295 judged. suite13t (all 8 requests) is finished: every memory route
it shipped is judged or rerunning.
**c_mem55 (21:23):** nested_loop 4 (8219f27a, trimmed): SAME, 32 / 32, min RAM setup 1028 ps. 296 judged; every suite13t memory route judged.
**c_mem56 (22:04):** suite13t_s5a_v10_2b's test_bitint 2 / test_loop_free 2 (untrimmed this time): SAME, 32 / 32. 298 judged.
**c_mem57 (22:45):** suite13t_s5a_v10_2a's memsum 2 (d8efd9ad, untrimmed): SAME, 32 / 32, min RAM setup 1755 ps. 299 judged.
**c_mem58 (23:25):** suite13t_s5a_v10's dot2 2, gather 2, if_loop_1 2 (untrimmed): SAME, 32 / 32 each, min RAM setup >= 1830 ps. 302 judged.
**c_mem59 (00:06):** fill 3, if_loop_2 2 (suite13t_s5a_v10): SAME, 32 / 32, min RAM setup 1289 / 3865 ps. 304 judged.
**c_mem60 (00:46):** 7 more suite13t_s5a_v10 routes: SAME, 32 / 32 each, min RAM setup >= 562 ps. 311 judged.
**c_mem61 (01:27):** test_bitint 3, test_stdint 3: SAME, 32 / 32, min RAM setup 947 / 1975 ps. 313 judged.
**c_mem62 (02:07):** dot2 3, gather 3: SAME, 32 / 32, min RAM setup 2536 / 1274 ps. 315 judged.
**c_mem63 (02:48):** share_test_1 1, single_loop 1: SAME, 32 / 32, min RAM setup 1628 / 838 ps. 317 judged.
**c_mem64 (03:29):** 6 more suite13t_s5a_v10 routes: SAME, 32 / 32 each, min RAM setup >= 771 ps. 323 judged.
**c_mem65 (04:09):** gather 4, if_convert 3, test_flatten_array 3: SAME, 32 / 32 each, min RAM setup >= 573 ps. 326 judged.
**c_mem66 (04:50):** if_loop_2 4, test_flatten_array 4: SAME, 32 / 32, min RAM setup 442 / 3037 ps. 328 judged.
**c_mem67 (05:30):** loop_path 4 (5eab3e6b): SAME, 32 / 32, min RAM setup 1083 ps. 329 judged.
**c_mem68 (06:11):** 5 more routes SAME, 32 / 32 each, min RAM setup >= 720 ps. single_loop 4 failed your bench-clock
check here (79.31 MHz) -- formal's error: your loop shipped iteration 8 placed with seed 104 (auto/seed_8.txt), formal built
it with 4; if_loop_1 4's earlier bench-clock failures here (C63, c_mem51) are the same. Both rerun with 104 (c_mem69). 334 judged.
**First results with the FIXED arc (farm c_mem8, 13:18 UTC; your newest memory routes, all sdf-identical, host port,
16 + 16 draws):** fir 1 / 2 / 3 / 4 (01a9e080 / b95f54ea / 42e919b6 / 4060231b), sumi3_mem 1-4 (448634ea / 26f31958 /
77e26098 / 9d874530), memsum 1 (95dfac83), image_resize 1 (1e81bd80), nested_loop 2 (4f755025): **every draw passes,
every array read back right**; smallest WE setup margin 820 ps (fir 4).
**The 16 headline rows and the controls with the FIXED arc (farm c_mem9, 14:03 UTC, 16 + 16 draws, host port):** every
headline route passes 32 / 32 again, all sdf-identical; smallest WE setup margins: if_loop_1 s1 +25 ps (the race: no
failing draw among these 32; with the earlier 128 it fails in about 1 draw in 40), test_stdint 795, mul_example 741,
test_bitint 830, fill 975, the rest >= 1 ns. BDC_MEM_NOCAP=1: test_bool_array 0 / 32 (fails, as before), test_memory_1
32 / 32 (as before). **So the correction changed no verdict.** (The other 52 rows of the C60 tables still carry the old
arc until c_mem7 runs; the fix moves the RAM data later by at most ~0.3 ns, and the 11 fixed-arc rows above and these 16
show no route within that of failing except if_loop_1 s1, whose race does not involve CLK->DO.)

**What is new.** Until today formal's simx refused every benchvec kernel (no RAM model), so the 30-odd memory kernels of
your suite had no independent judge. margin/bram/ decodes each RAMB18 site from the bitstream read back by bit2fasm
(strict whitelist: port A x18, WRITE_FIRST, DOA_REG 0, port B never clocked; every constant control's logical value and
every DSP / RAM pin's net checked one-to-one against nextpnr's routed json), simulates it as a clocked RAM inside the
decoded netlist (prjxray CLK->DOADO 585-2454 ps on the clock arc, drawn in your CARRY4 / F7 / FF band; setup / hold
windows from BRAM_L.sdf, widest values; a violation is not a pass), writes your vectors' arrays into the RAMs before each
call and reads every array back after it against oracle_mem.sh's contents (ORACLE_RUNS=1). Void kernels: the bench's
completion join is the result. One command: `RS=<research checkout> bash formal/tools/margin/bram/memtask.sh K SEED
SIZES SDF8 OUT [NDRAWS]` (as shard B's suite/task.sh: build, sdf md5 check, bits read back, decode, draws).

**Results (16 draws of your model K = 10000 + 100 s + 1.. and 16 slow draws, CARRY4 / F7F8 / FF / RAMB18 in [0.8, 1.0];
routes rebuilt from your farm sizes, sdf md5 = yours):**
| kernel s | sdf | draws (yours + slow) | arrays read back |
|---|---|---|---|
| dot2 1 | cd975c99 | 16 + 16 PASS | right |
| gather 1 | 33b77519 | 16 + 16 PASS | right (2 arrays) |
| if_loop_1 1 | b2ad5a7b | 16 + 16 PASS | right |
| if_loop_1 2 | 25d24290 | 16 + 16 PASS | right |
| if_loop_2 4 | 7cb58e52 | 16 + 16 PASS | right |
| memsum 3 | b6a797f9 | 16 + 16 PASS | right |
| test_bitint 1 | cf69bd3e | 16 + 16 PASS | right (2 arrays) |
| test_bool_array 1 | 8759dc8d | 16 + 16 PASS | right |
| binary_search 2 | d1f73792 | 8 + 8 PASS | right |
| fill 2 | 87090c0b | 8 + 8 PASS | right |
| mul_example 2 (void, LS) | eaafdc60 | 8 + 8 PASS | right (600 words) |
| simple_example_1 1 (void) | 5b20a707 | 16 + 16 PASS | right |
| test_memory_1 1 (void, LS) | 0e95d2ca | 16 + 16 PASS | right |
| test_stdint 1 (void) | bca02df4 | 16 + 16 PASS | right |
| while_loop_3 1 (void) | 2918dcd1 | 16 + 16 PASS | right |
| **test_bool_array 1, BDC_MEM_NOCAP=1** (new route fd65979d) | | **0 / 16 + 0 / 16** | call 0 returns 0 for 1 |
| test_memory_1 1, BDC_MEM_NOCAP=1 (new route f162f5a9) | | 16 + 16 PASS | right |
| unused_arg 1 | db282072 | 8 + 8 PASS | right |
So 16 of your headline memory routes pass every draw here. NOCAP is a control that CAN fail (test_bool_array, LL: the
second load clocks the RAM while the first load's consumer reads), not one that must: on test_memory_1 (LS) the store
behind the program-order token clocks the RAM only after the load's consumer has taken its word on this route (your
18 / 18 NOCAP failures were spmv's, memorder.md). test_loop_free has 4 operand words (formal's bench drives two: not run).

**if_loop_1 s1 is your known-bad route (the host-fill race) and it passes in the table above** because there the arrays
are written straight into the RAMs. **UPDATE 09:03 UTC: with the fills driven THROUGH the host port** (`HOSTPORT=1`,
simx --hostport: gen_bench's sequencer -- address / data / we one aclk before the request, the request once the
2-flop-synchronised acknowledge is low, dropped when it is seen high, aclk 12 ns), **formal finds your race on its own:
2 of 64 draws of your model (10138, 10144) FAIL with WE setup violations at every host write to RAMB18_X0Y22** (= your
c_000008, umem_controller1_uport.umem0, the low half), WE moving 523 / 498 ps before the edge it must precede by 532.
Over the 64 draws the smallest WE setup margin (beyond prjxray's 532 ps) is -55 ps, median +198, max +401 ps; your
draw 10101 (-17 ps in your GLS) has +188 ps here and your 10104 +317 ps. So the two simulators agree on the race and its
place and disagree by ~0.2 ns on where its distribution sits (formal: per-arc scatter on RC-tree arcs; yours: per-pip).
**The race in picoseconds** (margin/bram/hostrace.py, static path sums on the decoded bits at the middle of your
U[.20, .31] band, cells 0.6, no scatter): umem0 (RAMB18_X0Y22): host request flop SLICE_X8Y99.CQ -> CLKARDCLK earliest
**3686 ps** (4 LUTs 1229 ps: m_req, usetup g[0], g[1], ubuf; routing 2457 ps) against WEA latest **2962 ps** (1 LUT, m_we,
322 ps; routing 2640 ps), setup 532 -> **slack +193 ps**; your GLS table at draw 10101: 3566 vs 2949-3051, -17 ps. umem1
(5 usetup elements): +801 ps. So the path lists agree element for element with your ifloop.md section 2, and the
binding term is the m_we route to the RAM (2.6 ns of wire for one LUT), as you found.
**Every memory route through the host port (farm c_mem4 / c_mem5, 09:22 UTC; draws of your model + slow cell / RAM draws;
"WE" = the smallest WE setup margin beyond 532 ps over all draws and all RAM writes, host or kernel):**
| route (sdf, all = yours) | draws passing | WE margin min |
|---|---|---|
| binary_search 2 d1f73792 | 64 / 64 | 2627 ps |
| dot2 1 cd975c99 | 64 / 64 | 1835 |
| fill 2 87090c0b | 64 / 64 | 957 |
| gather 1 33b77519 | 64 / 64 | 1707 |
| **if_loop_1 1 b2ad5a7b** | **63 / 64** (one slow draw: WE setup violations, umem0) | **-98** |
| if_loop_1 2 25d24290 | 64 / 64 | 2047 |
| if_loop_2 4 7cb58e52 | 64 / 64 | 2592 |
| memsum 3 b6a797f9 | 64 / 64 | 3884 |
| mul_example 2 eaafdc60 | 64 / 64 | 680 |
| simple_example_1 1 5b20a707 | 64 / 64 | 1069 |
| test_bitint 1 cf69bd3e | 64 / 64 | 810 |
| test_bool_array 1 8759dc8d | 64 / 64 | 3699 |
| test_memory_1 1 0e95d2ca | 64 / 64 | 2901 |
| test_stdint 1 bca02df4 | 64 / 64 | 795 |
| unused_arg 1 db282072 | 64 / 64 | 2669 |
| while_loop_3 1 2918dcd1 | 64 / 64 | 1559 |
| if_convert 1 a99380fc / 2 c990d905 (suite10b, + BDC_FORK_OUT_LINK=n8__1,n8__2) | 32 / 32, 32 / 32 | 1216, 1556 |
| test_memory_2 1 36c3a48b / 2 6b132f6f | 32 / 32, 32 / 32 | 1169, 1393 |
| spmv 1 6caf1111 / 2 fe1740d4 | 32 / 32, 32 / 32 | 1389, 1339 |
| test_flatten_array 1 ce6c6a19 / 2 96248d2a | 32 / 32, 32 / 32 | 2940, 1154 |
| iir 1 091c7f6d | 32 / 32 | 1605 |
| nested_loop 1 089fc849 | 32 / 32 | 1861 |
So: 26 of your memory routes, every one you report PASS, pass here too; the one you report WRONG (if_loop_1 s1) is the
only one with a negative margin, and it fails in formal only on 3 of 128 draws (2 / 64 locally, 1 / 64 on the farm):
formal sees the race and places it ~0.2 ns kinder than your GLS. The next-closest routes (mul_example 680 ps,
test_stdint 795, test_bitint 810) are 0.7-0.8 ns clear. Your ifloop rule fix should show as if_loop_1 s1's successor
route moving up this column; give formal its sdf and it will be run the same way.
Without HOSTPORT the host port is not exercised;
with it, the read-back is still taken from the RAM's contents, not through the port.

**The capture race in picoseconds (margin/bram/ramslack.py:** every RAM's CLK->DO arc +X until a result goes wrong, one
draw, a consequence slack): test_bool_array 1 (8759dc8d): **2.71 ns** with the RAM and cells at SLOW_MAX (draw 10101,
xband 1.0), 3.78 ns at the draw's own band; gather 1 (plain ports, no capture latch): 12.9 ns. Your capmargin.py's
static worst for "test_bool_array s1" is 2490 ps (memorder.md; if that is the same route, the static bound sits 220 ps
inside formal's dynamic one, the expected direction). Nothing measured is near failing, as you found.

**Liveness of the two default-flow memory deadlocks (live.py with the load-first lowering modelled):** spmv: floor on
LIVE exhaustively (93 562 states; floor stages falseResult_20 / 36 / 40 -> 2), BDC_TOKEN_FLOOR=0 DEADLOCK, token-free walk
ulink_n7 -> n10 -> n19__0 -> n24 -> falseResult_20. sobel: BDC_TOKEN_FLOOR=0 DEADLOCK after ucmpi0=0, ucmpi1=0,
ucmpi3=0, ucmpi4=1, walk ulink_n88 -> n99[2] -> n120__2 -> n101__2; the floor puts ulink_n88 at 2 stages and that run
(exhaustive) is still on the farm. So both deadlocks your memorder note attributes to the missing floor are, in formal's
model, exactly a token-free walk through the link the floor lengthens.

Not covered: the host port (above); RAMB36 / cascades / port B / registered outputs (refused); X after a setup / hold
violation (counted, not propagated; none occurred); INIT contents (none on these routes); kernels with more than two
operand words. Reproduce one row: the command above with `formal/tools-B/auto/suite/sizes/hl/K_S.vh` and the sdf.

## A25. Operator fusion checked in Lean: for every kernel dfimport can read, bdc's fused graph (default), its fully unfused graph, a fusion cap of 8, and BDC_AUTO=1 (with BDC_CONST_DATA) are the same graph up to proved local rewrites; a one-command checker for your fusion pass (ringfuse) (shard A, 2026-11-19 08:24 UTC; Lean, standard axioms; token level)
- **Why:** your ringfuse lead (fewer handshake units per loop ring, an opt-in fusion pass) changes what bdc fuses. A
  fusion that reads a value twice, drops a token, or wires a region port to the wrong source changes what the circuit
  computes, and simulation finds that only on the vectors it runs.
- **The checker:** `python3 formal/tools-A/rewrite/fuse_check.py A.mlir B.mlir [--env-a K=V,..] [--env-b K=V,..]
  [--bdc YOUR_BDC_DIR]`. It imports both (dfimport builds each fused region from bdc's own region wiring, `reg.ref`:
  which port reads which external input, constant or inner op), takes each import to a maximal-fusion normal form by a
  script of proved local steps, compares the two normal forms by renaming, and has Lean check the scripts and the
  renaming. Exit 0 = PROVED: from tokens on the inputs only, every complete run of A has a complete run of B with the
  same result tokens, and vice versa. 2 = refused. 3 = A and B import to the same rules.
  - To check ringfuse: `fuse_check.py K.mlir K.mlir --env-b <your ringfuse knob>=1 --bdc <your bdc>` on every kernel
    (or `A.mlir B.mlir` if the pass rewrites the MLIR).
  - Every kernel in one command: `formal/tools-A/rewrite/fuse_census.sh cloud/fixtures/frontend <your bdc> "<KNOB>=1"
    out.txt` (one line per kernel).
- **New proved steps (any graph, both directions; `formal/lean/Formal/Rewrite/Steps/`):** `Dedupe` (a comp reading two
  outputs of one fork reads one of them twice), `Wire` (a one-output fork feeding a comp is removed), `ConstData`
  (your BDC_CONST_DATA: a comp reads a channel that only ever carries the constant v as the literal v; proved with the
  channel invariant). With A24's Absorb / ForkJoin / ForkSplit / ForkComm / Cong, all in `runScript`. check.sh OK on
  Steps/*.lean (1242 declarations).
- **Census over your 111 fixtures** (research 96e069513, your bdc; `formal/tools-A/rewrite/fuse_census.txt`):
  - 26 kernels import (85 do not: memory ops / parse errors in dfimport): branchloop, brhash, cmpchain, collatz,
    collatz64, countloop, factorial, fold64, gcd, horner, ipow, isprime, iterative_division, iterative_sqrt, lfsrfind,
    nest3, nested, quadrec, sqrtsub, straight, sum3, test_int16, test_loop_free, twoloops, varshift, xorshift.
  - default fusion vs fully unfused (`BDC_OP_FUSION=0,BDC_FORK_FUSION=0`): **24 PROVED**, 2 import identically.
  - `BDC_MAX_FUSE_NODES=8` vs default: **10 PROVED**, 16 identical.
  - `BDC_AUTO=1` vs default: **16 PROVED**, 10 identical (iterative_division needed `ConstData`: AUTO reads a
    constant-0 channel as the literal 0).
  - No refusal in any mode. gcd (the largest) takes ~65 s; most take 5-15 s.
  - Note (17:10 UTC): from your flow v8 on, BDC_AUTO=1 includes BDC_RING_FUSE=2, which fuse_check cannot equate yet (A26);
    the `auto` column above is for your bdc 96e069513. Run it with `--env-b BDC_AUTO=1,BDC_RING_FUSE=0` for v8.
- **Controls** (`tools-A/rewrite/controls/fuse/README.md`): collatz with `shli` replaced by a logical right shift, and
  collatz with one fork output read twice (another never): both refused.
- **What it does not cover:** the Verilog bdc emits for a fused region (compute.py) against the region's expression
  (dfimport's op semantics) is trusted, as everywhere in formal's token-level work; memory kernels (dfimport cannot
  read them); timing. The check says the fused graph computes the same tokens, not that it is faster.

## B19. Your suite12 (flow v8, ring fusion default, seed 1) in formal's simx as its routes land (shard B, 2026-11-19 from 20:20 UTC; untrusted simulation + B16's Lean-logic bound; updated as tasks finish)
Each finished route rebuilt from research 34bde912c (bdc / cells identical to suite12's 1b47b72a7) with its
`sizes_<it>.vh` and the search phase's ENV, sdf checked, bits decoded, 8 draws of your K + 8 slow-carry, storage pulses
< 200 ps counted, output-capture kappa_lo (`outsafe.py`). Array kernels: C's memtask. Helper: `tools-B/auto/suite/watch_suite.sh`.
**Summary (2026-11-20 01:15 UTC, suite12 61 of 62 finished):** every non-array route that finished with a result, 22
kernels, rebuilt to your sdf md5 and passed all 8 + 8 formal draws with 0 storage pulses; your 29 array kernels are C's
(memtask). test_int16 (sdf SAME) has a constant output, which simx refuses; share_test_2 is NOT-A-BOARD-ROUTE in your result.
Eight tasks (gcd, isprime, nest3, branchloop, digitsum, digitdiv, sobel, video_filter) hit the farm's 240 min limit with no
result; so did task 37 (if_loop_1, an array kernel; suite12 done 02:14 UTC). Output-capture kappa_lo (B16 structure, Lean-logic bound) 0.062-0.431 on 19 routes; no
proof (negative) on iterative_sqrt -0.450, test_divui -0.012, nested -0.007 (passing draws, so no failure shown either). Where the bound falls short: nested, at the fast corner, out0's
request reaches the capture >= 1381 ps after umux13.uj1 fires and the data cone (566 nodes, longest path) settles <= 1401 ps
(20 ps short; slow corner +0.060); test_divui, the divider cone (29233 nodes) settles <= 93.6 ns vs the request line
>= 91.4 ns (B17's -0.012 kind: the value-independent longest path through the divider, not a path a value takes).
Two formal-side fixes on the way (no effect on your routes): the search ENV is applied only when the shipped route is
the search's (ipow s1 shipped it 10, countloop s1 it 9); iterative_sqrt's square is mapped by yosys as (x >> 1)^2 in the
DSPs plus a LUT fix-up for bit 0, which C's DSP check rejected (B's `dsp_gates_sq.py` accepts that form; the 16 passing
draws are the end-to-end check).
| task | kernel | sdf | formal draws | pulses | kappa_lo |
|---|---|---|---|---|---|
| 1 | xorshift | 9dd1f661 SAME | 8/8 + 8/8 | 0 | 0.191 |
| 2 | collatz | 119e89fc SAME | 8/8 + 8/8 | 0 | 0.279 |
| 3 | collatz64 | 921c6f7d SAME | 8/8 + 8/8 | 0 | 0.142 |
| 4 | ipow | 03bda888 SAME | 8/8 + 8/8 | 0 | 0.137 |
| 7 | straight | 524c6161 SAME | 8/8 + 8/8 | 0 | 0.260 |
| 8 | countloop | 6c6b5316 SAME | 8/8 + 8/8 | 0 | 0.418 |
| 9 | sqrtsub | 33ec83be SAME | 8/8 + 8/8 | 0 | 0.239 |
| 11 | twoloops | 73d89e84 SAME | 8/8 + 8/8 | 0 | 0.388 |
| 12 | brhash | f95be139 SAME | 8/8 + 8/8 | 0 | 0.232 |
| 13 | lfsrfind | 0a834c15 SAME | 8/8 + 8/8 | 0 | 0.347 |
| 14 | quadrec | bdf8e2b6 SAME | 8/8 + 8/8 | 0 | 0.354 |
| 15 | horner | 33bf6da3 SAME | 8/8 + 8/8 | 0 | 0.273 |
| 16 | fold64 | a0e6b77b SAME | 8/8 + 8/8 | 0 | 0.431 |
| 17 | varshift | b4b04cdb SAME | 8/8 + 8/8 | 0 | 0.160 |
| 18 | cmpchain | 738df70c SAME | 8/8 + 8/8 | 0 | 0.120 |
| 19 | nested | 5cfb38c8 SAME | 8/8 + 8/8 | 0 | none (-0.007) |
| 23 | divmodu | 99effc30 SAME | 8/8 + 8/8 | 0 | 0.246 |
| 24 | divmods | ccaa7fa4 SAME | 8/8 + 8/8 | 0 | 0.412 |
| 25 | test_divui | ecbc22cc SAME | 8/8 + 8/8 | 0 | none (-0.012) |
| 30 | factorial | a853b143 SAME | 8/8 + 8/8 | 0 | 0.062 |
| 31 | iterative_division | ed5e281e SAME | 8/8 + 8/8 | 0 | 0.325 |
| 32 | iterative_sqrt | f8ef55a7 SAME | 8/8 + 8/8 | 0 | none (-0.450) |
| 34 | test_int16 | 21440296 SAME | - (constant output) |  | none |
| 49 | share_test_2 | - | research: share_test_2 1 status=NOT-A-BOARD-ROUTE P=NA lat_max_cyc=NA  | | |
(table continues as the farm returns)

B19 note (22:25 UTC), cmpchain s1 (v8, sdf 738df70c): the N-way mux decode race of B13, measured with `decslack.py` on
draws 10101 / 10102 / 10151 / 10152 (two default, two slow-carry): every request rise at every decode LUT of umux0 / umux1
/ umux2 comes after the last index flip; smallest slack +986 ps (umux1, input 3), umux0 >= +1307, umux2 >= +3038. So the
v8 route has none of B13's pulses in these draws (simulation, 4 draws; not a bound; MuxNDecode's theorem says rule E's
inequality per pin is what would make it one).

## B18. Your ringfuse routes (BDC_RING_FUSE=2, farm ringfuse1) in formal's simx: every finished one passes, including xorshift's counter preloaded across its 2^30 carry (control fails as it must) and collatz's full-range values; output-capture kappa_lo 0.02-0.35 (shard B, 2026-11-19 13:57 UTC; untrusted simulation + B16's Lean-logic bound)
Rebuilt from research a15e5a5f1 (bdc with ringfuse) with each task's `sizes_<it>.vh`, BDC_RING_FUSE=2, the task's seed;
sdf SAME on all 29 here (every BDC_RING_FUSE=2 route of farm ringfuse1 that finished: countloop s7 / s8 hit PNR-TIMEOUT there) (countloop s1 / ipow s1 with their search-phase ENV, BDC_FORK_OUT_LINK / BDC_LINK_DEPTHS, from auto/search.txt); bits decoded by formal; 8 draws of your K + 8 slow-carry; `outsafe.py` for the output race.
| task | route (sdf) | draws | output kappa_lo |
|---|---|---|---|
| 1-8 | xorshift s1-s8 (ef141b74 / 61631e55 / acb8a72d / 1931be20 / abc056ef / 7dc74a74 / 32ae504c / 2d1029ae) | 8 + 8 each, 0 pulses | 0.225 / 0.146 / 0.056 / 0.218 / 0.344 / 0.273 / 0.204 / 0.292 |
| 9-16 | collatz s1-s8 (9881f22a / 707608d0 / bd157c2e / 7ed75da9 / d8b7c9d3 / 86b0c6c5 / 192c8a42 / 5a801ad9) | 8 + 8 each, 0 pulses | 0.351 / none (-0.012) / 0.260 / 0.149 / 0.201 / 0.201 / 0.338 / 0.326 |
| 17-22 | countloop s1-s6 (84dad03e becb3043 ebf1bbc6 544cf8c4 67b575ac a1658752) | 8 + 8 each, 0 pulses | 0.323 / 0.152 / 0.352 / 0.337 / 0.126 / 0.055 |
| 25-30, 32 | ipow s1-s6, s8 (d0d6f410 840293d4 a8281ece 6684bc94 027c6811 793da4b1 e9c1079e) | 8 + 8 each, 0 pulses | 0.128 / 0.049 / 0.170 / 0.247 / 0.231 / 0.021 / 0.226 |
| 31 | ipow s7 (01894137) | 8 + 8, but pulse bursts in 4 of 16; your failing draw is start-up X (below) | 0.269 |
- **The fused counter's long carry (xorshift s4):** the loop counter preloaded at 0x3ffffff0 through ulink_n6 (B8's
  check), 7 vectors crossing 2^30: 8 / 8 pass. Control: +20 ns on the carry-in of the fused cell's bits 16-19 slice
  (ucmpi1 slice[4], SLICE_X26Y55): preloaded 0 / 2, ordinary xor19 2 / 2 -- the preload reaches the carry and the
  unmodified route handles it.
- **collatz full range (s4, s5):** c32hi (31-bit trajectories), 4 + 4 slow-carry draws each, pass (and item 39 too, same
  vectors). (A first try with kernel_oracle.sh as the oracle "failed" identically on item 39: that oracle applies the
  bench's 16-bit input mask, formal's boundary drives all 32 bits. Not a finding.)
- **Your one failing ringfuse route, ipow s7 (task 31, 01894137, your draw 10707: 16 / 17, batch 0's second ipow(3, 1)
  call hangs, runts at ucontrol_merge0.uarb1.ustate.q 119 ps and the branch steers):** rebuilt here SAME. Formal's simx
  passes all 8 + 8 draws (answers right, also draw 10707 without the 20 ps runt filter, and the exact two-call sequence
  (3, 1), (3, 1)), but it is the ONLY one of the 15 ringfuse routes (and of item 38) where formal sees bursts of pulses
  under 200 ps on storage-LUT outputs: draws 10707 / 10755 / 10756 / 10757 with 188 / 825 / 702 / 225 such pulses late in
  the run (t = 3.7-4.0 us), narrowest 15 ps at ucontrol_merge1.uarb1.ustate (6 ps at ucontrol_merge0.uarb1.ustate without
  the filter), 1-5 ps at ucontrol_merge0_rlink's controller, a uselect0 join and a ulink_n_trueResult_10 latch; every other
  route and draw: 0 (also on every headline route judged on the farm for B14, b_hl1-5: no draw there had a single such pulse). So both simulators single out this route and the same control-merge arbiters; yours resolves the
  near-tie into a hang, formal's into a right answer. Not traced further: the difference is in the arbiter's resolution
  model (your state-node resolver; formal's transport LUTs) and the host's re-request timing (formal's two-call run never
  forms the tie). Shard C's C56 (the control_merge index race: A2 still high when the next entry token wins) is the
  candidate mechanism.
  **TRACED (17:15 UTC): your failure is the start-up X of your GLS, not a timing failure.** Your own bench_gate.sh,
  run here on the rebuilt route (draw:10707, GATE_RUNTS=1), reproduces your verdict exactly (FAIL 16/17, 100 869 cycles,
  the same runts): 28 handshake nets go X at t ~1.645 us in batch 0, the first call after reset (control merges, branch
  steers, ulink_n7), and batch 0's second call hangs with an X in the host's FSM (fsm=000005X4); every later batch is DONE.
  With your fid_core.vh power-up option (GATE_PLUSARGS=+META_INIT=0, and again =1: storage LUTs start at a value, as the
  configured chip does) the same draw **PASSES 17/17 in 902 cycles, x 0**, on both. What remains in all three runs are
  the near-tie pulses (narrowest 85-119 ps at ucontrol_merge0.uarb1.ustate.q and the branch steers ucond_br2 / ucond_br5):
  the same place formal's simx shows its pulse bursts. So: not a failing route (both simulators agree once the X is
  removed), but the most marginal of the 29 at that arbiter. C17 found the same start-up X behind your select-join
  injections on 2026-11-16; draws that fail only in batch 0 with x > 0 are worth rerunning with +META_INIT=0 / 1 before
  they count.
  **The near-tie, named and in picoseconds:** your loop shipped this route NOT CLEAN with rule-E rows at the branch steers
  ucond_br5 (-578 / -1019 ps at 0.20 / 0.31), ucond_br2 (-317 / -729), ucond_br3 (-290 / -687), ucond_br4 (-330 at 0.31)
  and A'j at ucmpi0 (-428 / -863). The steers' condition is the fused compare's output `ucmpi0.uz_n4` (ring fusion put the
  loop test in that cell); the request is each steer's join `ucond_brN_j`. Formal's C steermargin (no scatter, at draw
  10707's bands 0.20 / 0.30 / CARRY 0.92): the condition settles at the steer LUT only **57-61 ps (ucond_br2), 102 ps
  (br3), 147-154 ps (br5)** before the request, and at br5 it **moves under a live request in 1 of 17 calls** (a steer
  runt). All bands at FAST_MIN: 77 ps at br5, 282 at br2; all at SLOW_MAX: >= 847 ps. So the slow-carry / fast-LUT corner
  (the compare's carry chain slow, the join's request fast) is where it closes -- B7's failure mode, at the fused test --
  and your rule-E rows name exactly these steers: they are real, and the route is the thinnest of the 29. In Lean
  (`Formal/Cells/MuxNDecode.lean`, the steer section, check.sh OK): `decode_no_pulse` covers a steer's not-taken output
  too -- rule E at a steer (condition settled at the LUT pin no later than the request) is sufficient for no pulse there,
  every delay in the band, glitches included; the steer LUT2s' forcing facts are decided, with a negative control.
- Not run here: tasks still on the farm; the v7 baselines (task 33 did not reproduce its sdf from a15e5a5f1).

## B17. Your divsize fix, checked: its test_divui routes pass formal's draws, but sit on the edge of what can be proved -- seed 1 (line 332) has no proof even at kappa 0, seed 3 (338) 0.006, seed 2 (386) 0.082 (shard B, 2026-11-19 11:00 UTC; untrusted simulation + B15's Lean-logic bound)
Your divsize1 seeds 1-3 (journal 10:52) and the farm's seeds 4-8 (sizes_<it>.vh of divsize1), rebuilt here with UDIVUI0 332 / 386 / 338 and the other lines as before: sdf
ecbc22cc / 96c7d776 / 14c880c4 / a43e6557 / 827a8a2d / 20c9d09e / baf58131 / ede592d7, all SAME. Formal's simx, your K: **8 / 8 + 8 / 8 slow-carry on each**. B15's bound for
the divider capture (`tools-B/auto/outsafe.py`; data settled by A + D at maxima, request not before A + R at minima):
| seed (line) | R (c = 0 / 1) | D (c = 0 / 1) | kappa_lo |
|---|---|---|---|
| 1 (332) | 91.4 / 215.8 ns | 93.6 / 220.0 ns | **none (-0.012)** |
| 2 (386) | 107.9 / 254.0 | 91.5 / 215.3 | 0.082 |
| 3 (338) | 95.9 / 226.3 | 94.7 / 222.2 | 0.006 |
| 4 (1111, a43e6557) | | | 0.515 |
| 5 (359, 827a8a2d) | | | 0.032 |
| 6 (348, farm divsize1 20c9d09e) | | | 0.037 |
| 7 (516, baf58131) | | | 0.180 |
| 8 (324, ede592d7) | | | 0.003 |
**All eight divsize1 seeds:** every one passes formal's 8 + 8 draws; kappa_lo -0.012 / 0.082 / 0.006 / 0.515 / 0.032 /
0.037 / 0.180 / 0.003 (seeds 1-8): one with no proof, four more below 0.04. The fix is right; the proved margin it leaves
is near zero on most seeds.
**digitdiv s1 (divres1, 7582477a, UDIVUI0 325; its divider feeds links inside the digit loop):** 8 + 8 pass, 0 pulses;
on the same placement the line can shrink to 0.875 (284 elements) and pass 2 + 2 draws, 0.8125 (264) gives wrong answers:
about 13-19 % headroom in the draws, and again the ~268-element enable-chain edge.
So the fixed rule sizes the divider about where every arc at its band extreme just balances: it removes the bug, and
leaves no proved within-die margin on seed 1 (the draws, which never put every arc at its extreme at once, pass with room:
B12's re-placed edge was ~288-320). If you want a proved margin there, the line has to be longer than the rule now asks: on these placements the proof
starts between ~335 and ~385 elements (placement-dependent), i.e. about 1.35-1.5 x the enable chain's 256 hops; B15's 384
gives 0.067, 528 gives 0.240. Your seed 4 (1111) is
far above any of these.

## B16. Proved-structure lower bounds (kappa_lo) for the OUTPUT CAPTURE race of your board items 38-41 and other routes: xorshift 0.117, collatz 0.281, collatz64 0.108, ipow 0.169; gcd / iterative_sqrt get no proof (shard B, 2026-11-19 10:10 UTC; Lean logic, untrusted extraction; one race per route)
B15's method made generic (`formal/tools-B/auto/outsafe.py MDIR`, on any decoded bench route): the race between out0_data
(its whole combinational cone, every operand: Lean `SettleAll.settle_all`) and out0_req (a chain of gates each forced to
0 by one pin, constant-tied pins at their values: Lean `ChainHold.chain_hold` / `chain_hold_side`), both from the rise of
the join J that launches the request. Where several joins can launch it (a mux), the bound is the worst one. g = 1;
kappa_lo = min over the two corners of (R - D) / (R + D).
| route (sdf, all SAME as yours) | launching join (worst) | request >= A + (c = 0 / 1) | data <= A + (c = 0 / 1) | kappa_lo |
|---|---|---|---|---|
| item 41 xorshift s8 (3497ca67) | umux3.uj1 | 1.31 / 3.10 ns | 1.04 / 2.22 ns | **0.117** |
| item 39 collatz s6 (c56def07) | umux2.uj0 | 2.32 / 5.38 | 1.30 / 2.53 | **0.281** |
| item 40 collatz64 s5 (9585dde4) | umux2.uj1 | 1.69 / 3.89 | 1.36 / 2.69 | **0.108** |
| item 38 ipow s2 (81bbe268) | umux3.uj1 | 1.85 / 4.35 | 1.31 / 2.60 | **0.169** |
| straight s2 (23c31cf3) | uaddi3.ujoin | 2.75 / 6.22 | 1.44 / 3.43 | 0.290 |
| divmodu s1 (99effc30) | uaddi0.ujoin | 10.53 / 24.46 | 6.37 / 14.74 | 0.246 |
| cmpchain muxn1 s1 (67cb2cfa) | uxori0.ujoin | 3.61 / 8.45 | 2.46 / 5.65 | 0.189 |
| test_divui line 528 (2e6ac4e7) | udivui0.ujoin | 149.2 / 352.8 | 91.4 / 215.5 | 0.240 (B15) |
| gcd s3 (190535ff) | umux21.uj1 | 0.98 / 2.18 | 1.40 / 2.99 | none (-0.17) |
| iterative_sqrt s1 (b6aaa2f9) | umux3.uj1 | 0.86 / 1.96 | 2.06 / 3.88 | none (-0.41) |
- **Premises (other races, not proved here):** the cone's roots (input / select latches) hold their values from J's rise
  to the capture; for a mux, the other joins stay 0 while the request walks (the mux's exclusivity); out0 is captured at
  out0_req's rise (your bench samples a host cycle or more later, so gcd's / iterative_sqrt's "none" says only that the
  bound, taken at out0_req, cannot prove them: both pass every draw); H_DECODE.
- **Reading:** on the board items this race is not the weak spot: at kappa 0.11-0.28 (every arc of the race at its
  extreme, the two sides at opposite ends of their per-arc scatter) it still holds. The margin tool's kappa_hi for the
  same builds (C's) is where the failures are.
- **Farm b_os2: every non-array headline route (38, all sdf SAME), output-capture kappa_lo per route (min of the two
  corners):**
| kernel | routes | worst |
|---|---|---|
| branchloop | s1 0.277, s2 0.222, s3 0.037, s4 0.152 | 0.037 |
| cmpchain | suite9r3 s2 0.309, s3 0.179; muxn1 s1 0.189, s2 0.161, s3 0.315, s4 0.150 | 0.150 |
| divmodu | s1 0.246, s2 0.269 | 0.246 |
| fold64 | s1 0.478, s2 0.520, s4 0.558 | 0.478 |
| gcd | s1 0.074, s3 none (-0.17), s4 none (-0.42) | no proof on 2 of 3 |
| iterative_division | s1 0.168, s2 none (-0.04), s3 0.217, s4 none (-0.03) | no proof on 2 of 4 |
| iterative_sqrt | s2 none (-0.53), s1 none (-0.48), s3 none (-0.41), s4 none (-0.47) | no proof on 4 of 4 |
| nested | s1 0.307, s2 0.442, s3 0.133, s4 0.246 | 0.133 |
| quadrec | s1 0.391, s2 0.447, s3 0.461, s4 0.387 | 0.387 |
| straight | s2 0.290, s1 0.319, s3 0.186, s4 0.190 | 0.186 |
| twoloops | s1 0.272, s2 0.049, s3 0.296, s4 0.198 | 0.049 |
  "none" = no proof (not a failure: every one of these routes passes every draw, B14). The routes without a proof all end
  in a mux whose data path is long against its line at the extremes (gcd's / iterative_sqrt's N-way mux; iterative_division
  s2 / s4 at corner 0 only); since the bench samples out0 at least a host cycle after out0_req, the race that matters
  there is wider than the one bounded here.

## B15. A PROVED lower bound (kappa_lo) for one race of a real route: test_divui's divider capture is safe for every delay in the band up to kappa 0.240 with the line at 528, 0.067 at 384, and has no proof at 320 (where your draws and formal's pass) (shard B, 2026-11-19 09:25 UTC; Lean logic, untrusted extraction of the numbers)
The owner's question (PROGRAM: can lower bounds be proved at all?) answered for one capture race. Race: out0_data
(the quotient, through the divider's gated stages) against out0_req (the divider's matched line), both launched by the
divider's `joined` rise at A.
- **Data side, Lean `Formal/Cells/SettleAll.lean` (`settle_all`, check.sh OK):** an acyclic island whose gates take any
  consistent valuation shows it on windows given by the longest / shortest path recurrences, independent of the values,
  so one computation covers every operand. Island = the backward cone of out0_data stopped at storage LUTs and boundary
  nodes (30 020 nodes incl. routing, acyclic); roots: the 32 operand latch outputs (ulink_n_arg0), joined, out0_ack.
- **Request side, Lean `ChainHold.chain_hold` (v = 0):** out0_req stays 0 until A + the sum of the minimum pin delays
  along joined -> uor -> the line's elements (each element forced to 0 by its chain pin, checked on its INIT).
- **Numbers** (`formal/tools-B/auto/divsafe.py` on the decoded bits; g = 1; max = (1+k) lerp(FAST_MAX, SLOW_MAX, c),
  min = (1-k) lerp(FAST_MIN, SLOW_MIN, c); each side is linear in c, so c = 0 and 1 suffice):
| UDIVUI0 (seed 1, sdf) | data settled by A + (c = 0 / 1) | request not before A + (c = 0 / 1) | kappa_lo | formal draws (b_divui2/3) |
|---|---|---|---|---|
| 5 (yours, 9875e724) | 91.6 / 215.9 ns | 1.9 / 4.4 ns | none (-0.96) | 0 / 64 |
| 272 (aa53bf21) | 92.4 / 217.2 | 76.2 / 180.4 | none (-0.09) | 13 / 16 + 16 / 16 |
| 320 (d1b3ec06) | 94.5 / 220.6 | 88.9 / 209.7 | none (-0.03) | 16 + 16 |
| 384 (8ce6d49c) | 93.1 / 218.2 | 106.4 / 251.5 | **0.067** | 16 + 16 |
| 528 (2e6ac4e7) | 91.4 / 215.5 | 149.2 / 352.8 | **0.240** | 16 + 16 |
- **Premises (not proved here):** the operand latches hold their value from A until the capture (the divider's input
  bundling and the hold at out0: other races); out0_ack stays low until after the request; the host reads out0 at or
  after out0_req (the bench); H_DECODE (the bits decode to this netlist). The extraction (cone, sums, INIT checks) is a
  Python script; the arithmetic is reproducible from the decoded net.
- **Reading:** the draws pass from ~288-320 elements (B12); a proof at kappa = 0 needs ~340+ (between 320 and 384),
  because the bound takes every arc at its band's extreme at once. For the flow: a proved-safe divider line is about
  1.2 x the length the draws need, and 0.24 of within-die scatter is covered at 528.
- Reproduce: `bash formal/tools-B/auto/suite/task.sh test_divui 1 formal/tools-B/auto/suite/sizes/test_divui_d528.vh -
  OUT 1` then `python3 formal/tools-B/auto/divsafe.py OUT/w/m`.

## B14. Your headline (38 of 62), judged in formal's simx on 33 of its routes: every route you count as passing passes here too (16 + 16 slow-carry draws each, 8 + 8 for gcd), and test_divui fails as in yours; no disagreement. Not covered: the 15+ array kernels, factorial, test_int16 (shard B, 2026-11-19 08:20 UTC; untrusted simulation)
Each route rebuilt from claude/research HEAD with its farm task's own `sizes_<it>.vh` and seed, sdf md5 equal to yours on
every one, bits read back and decoded by formal, your draw K (suite: 10000 + 100 * seed + 1) and the same draws with
CARRY4 / F7F8 / FF at 0.8-1.0, your C oracle (oracle.sh; gcd: gcd8 + gcd_oracle.sh). Farm b_hl1-4, local divmodu.
| kernel | seeds (sdf) | result |
|---|---|---|
| branchloop | 1-4 (6563082b 4095a20d 702616b7 8f1515d7) | 4 / 4 routes pass |
| cmpchain | 2, 3 (0383012b 4b738a97) + B13's three muxsel routes | pass, but 0383012b / 4b738a97 carry decode runts down to 94 ps (B13) |
| fold64 | 2, 3, 4 (ebe73b38 20548857 a5c6fab7) | pass (after a formal harness fix: one 64-bit argument = both words) |
| iterative_division | 2, 3, 4 | pass |
| iterative_sqrt | 1-4 | pass |
| nested | 2, 3, 4 | pass |
| quadrec | 1, 2, 4 | pass |
| twoloops | 1-4 | pass |
| straight | 1-4 | pass |
| gcd | 3, 4 (190535ff efddb3d1) | pass (8 + 8) |
| divmodu | 1, 2 (99effc30 2ce27c67) | pass (its divider lines: B12) |
| digitdiv (divres1) | 1 (7582477a; UDIVUI0 325) | pass 8 + 8, 0 pulses (output kappa_lo 0.200) |
| digitsum (divres1) | 2 (1617737c; UDIVUI0 333; rebuilt with its search ENV and BDC_RING_FUSE=0) | pass 8 + 8, 0 pulses (output kappa_lo 0.334) |
| divmods (divres1) | 1 (ccaa7fa4; UDIVSI0 340, link pads 173 / 183) | pass 8 + 8 (output-capture kappa_lo 0.412; its divider's capture is internal, not bounded) |
| nested / fold64 / iterative_division / quadrec (suite10b's new routes) | s1 cf7458c5, s1 f50aee65, s1 e3188230, s3 91affd4d | pass (farm b_hl5, 16 + 16 each) |
| test_divui | 1, 2 | fail every draw, as yours (B12) |
With B8 / B11 (collatz, collatz64, xorshift, ipow, countloop, sqrtsub, isprime, lfsrfind, brhash, varshift, horner,
pipeline), formal's simx agrees with your verdict on every non-array kernel it can run.
**Array kernels: see C60** (shard C, same morning): formal's simx now runs them (memory host, RAMB18 model), 11 headline
array routes pass there and your if_loop_1 s1 known-bad is reproduced with the host port. B's own probe (B's decode path,
`tools-B/auto/decode.sh`) still refuses BRAM features; use C's memtask for those kernels. Still not covered by either:
factorial (formal's DSP decoder refused its cascade in B's run; C60 says decode_dsp now accepts a DSP P into another
DSP's operand: to rerun), test_int16 (constant output).

## B13. Your N-way mux select race (muxsel): formal's simx reproduces it on your routes -- runts on exactly the four umux0 decode LUTs you list, of similar width, and none with the guarding line at 7 (shard B, 2026-11-19 08:00 UTC; untrusted simulation, one route pair, two draws each)
Your cmp25 / cmp25f (research/data/muxsel/gls/), rebuilt here sdf-identical (cmpchain s2 it5 1c13ff02, ULINK_N63__0 = 1;
and a44b35aa, = 7), decoded from the bits, your draws 20001 / 20002 (`formal/tools-B/auto/pulses.py`: output pulses of any
LUT whose cell matches `udut.umux*`, 453 LUTs, in one simx run with H_RUNT 20 ps):
| route | draw | pulses < 1 ns on umux LUTs | narrowest per decode LUT ($23189 / $23188 / $23187 / $23186), formal | yours |
|---|---|---|---|---|
| 1c13ff02 (line 1) | 20001 | 12, all on umux0 sel[0..3] | 232 / 624 / 398 / 413 ps | 247 / 786 / 544 / 585 |
| 1c13ff02 (line 1) | 20002 | 12, same four LUTs | 129 / 692 / 459 / 493 ps | 226 / 751 / 456 / 500 |
| a44b35aa (line 7) | 20001, 20002 | **0** | - | 0 |
Answers right in every run (as in yours). Two simulators with different LUT models (formal: transport per pin + 20 ps runt
filter; yours: fid with the state-node resolver) agree on which nets pulse and roughly how wide, and that 7 elements remove
it. Formal's NEARMISS (storage outputs only) misses these: B12's "neither confirmed nor contradicted" is now confirmed.
**Your fix, checked (08:36):** muxn1's four cmpchain routes (BD_SKEW_MUXN=1 in the loop; ULINK_N63__0 5 / 3 / 6 / 7;
sdf 67cb2cfa / 943d0ebf / a4399dd0 / 04d1197e, all SAME here), your suite draws K 10S01 / 10S02: **0 pulses under 1 ns on
every umux LUT (446-450 LUTs) in all 8 runs**, every answer right. Agrees with your 07:33 entry.
muxn1's iterative_sqrt s1 / s2 (b6aaa2f9 / 4e88f397, SAME), draws 10S01 / 10S02: answers right; 0 pulses on umux3's
decode LUTs; 67-88 pulses < 1 ns per run on umux3's 32 data-mux LUTs (the z_data bits that out0's register reads):
data settling before the request, which your handshake-net monitor leaves out by design. No disagreement.
**The cmpchain routes your headline counts** (suite9r3 s2 0383012b, ULINK_N63__0 = 1; s3 4b738a97, = 3; both SAME),
draws 10S01 / 10S02: answers right, but 7-10 pulses per run on the decode LUTs (umux0 $23187 / $23189; umux1 $23248 /
$23249 / $23251), narrowest **94-100 ps**. So the cmpchain PASS in the 38-of-62 table rests on routes with the race your
muxsel rule now sizes away; the muxn1 routes (above) are the clean replacement. (Checked with
`tools-B/auto/lutreaders.py`: every pulsing LUT there is read by a join, umux0.uj1 / uj3, umux1.uj0 / uj1 / uj3.)
The headline gcd route s3 (190535ff): 18-20 pulses per run on umux21, all on data-mux bits read by out0's register,
none on the decode LUTs: no decode race there.
**Lean (08:56, `formal/lean/Formal/Cells/MuxNDecode.lean`, check.sh OK, standard axioms):** your new rule-E row at a
decode LUT is a sufficient condition in the Spec gate model, glitches included, for every delay in the band, with no
runt filter: if the request pin's source is 0 on `[a0, tr]`, the index pins' sources hold a value other than k on
`[ts, b]`, and `ts + U_s <= tr + L_r` (latest index arrival at the LUT, per pin, no later than the earliest request
arrival), then `sel[k]` stays 0 on all of `[a0 + U_r, b + L_s]` (`decode_no_pulse`). The two forcing facts are Bool and
decided per LUT INIT (examples on a 4-way decode, with a negative control). Not shown: that a route meets the
inequality (no row emitted), and the selected input's decode (its single rise is a handshake fact, not this race).
**The race in picoseconds** (`tools-B/auto/decslack.py`, one draw each: at every decode LUT, every rise of the request PIN
against the last flip of any index PIN, both at the LUT after routing; negative = the index moved after the request
arrived): the worst mux of each route --
| route | draw | umux0 | umux1 | umux2 | your rule (guarded) |
|---|---|---|---|---|---|
| 1c13ff02 (s2 it5, line 1) | 20001 | **-552 ps** (53 of 75 rises) | +704 | +479 | -762 ps (muxsel note) |
| a44b35aa (line 7) | 20001 | +1656 | +792 | +735 | - |
| 0383012b (headline s2) | 10201 | **-347 ps** (45 of 75) | +556 | +566 | - |
| 67cb2cfa (muxn1 s1) | 10101 | +1160 | +1346 | +1652 | sized by it |
All four muxn1 routes over 6 draws each (K 10S01-04 + slow-carry 10S51-52; 24 runs, every answer right, no index flip
after a request rise): smallest slack s1 +1160, **s2 +351** (its line is 3), s3 +964, s4 +1304 ps. s2's 351 ps is the
thin one (not yet scaled by the measured delay error of its paths), so worth a look at s2's row in your rule output. Same sign as your rule on the two routes where both exist; simulation is one draw, the rule a guarded bound, so the
sizes differ as expected.
Emitted from a real route since: `formal/tools-B/select/muxn_rows.py` reads your muxn1 cmpchain s1 (67cb2cfa) decoded
from its bits, finds the 15 decode LUTs of umux0-2 (read by the joins), the request pin (shared by the mux's decodes and
a positive literal in each) and the index pins after nextpnr's permutation, and writes `Formal/Cells/MuxNRowsCmp.lean`:
for each LUT the kernel decides that the request at 0 forces 0 and that exactly one of the 8 index assignments does not
(check.sh OK). Those are the forcing premises of `decode_no_pulse`; the timing premise (your rule-E row) is not emitted.

## B12. test_divui: formal's simx agrees the automatic divider is wrong (0 / 16 draws at UDIVUI0 = 5, research's route), and the full-length line passes; on that placement the line needs 268 of 528 elements -- the 256-LUT2 enable chain plus the last stage, so on test_divui the line must outrun the enable chain, not the subtracts; divmodu needs far less (see the correction) (shard B, 2026-11-19 07:48 UTC, corrected 08:18; untrusted simulation, one placement for the edge)
**The race, named.** Both ends launch at `udivui0`'s `joined` rise. Data: the stage-enable chain `tp[0..256]`
(`uhold` then 256 kept LUT2s, DIV_TAP 8 x 32 stages, bdc/compute.py div_datapath), whose tap `tp[8(s+1)]` releases stage s;
quotient bit 0 is final only after `tp[256]` plus the last subtract / select. Request: `udivui0.udly`, UDIVUI0 elements of
`bd_delay_gated`. So the line must be about as long as 256 LUT hops plus one stage, whatever the operands. Your rule saw the
quotient settle ~3.4 ns after the operand (your 06:54 entry), i.e. it did not follow the enable chain (the docstring says rule
A's data peak runs through it; on these routes it did not).
- **Research's route, rebuilt here** (suite10b seed 1, `sizes_2.vh` UDIVUI0 = 5, sdf 9875e724 SAME, nextpnr 7c3bfb9c, a
  local compile of the 02809f42 cache with all 10 patch fingerprints): K 10101-10108 **0 / 8**, slow-carry K 10151-10158
  **0 / 8**; every answer reads 0 (formal's host takes out0 ~12 ns after its request, before the first stage enable; your
  bench, 5 host cycles later, reads the first ~12 stages: 0x00300000 for 0xffffffff / 1083). Same failure, same cause.
- **Control:** the same seed with UDIVUI0 = 528 (bdc's estimate; sdf 2e6ac4e7, the farm built the same md5): 4 / 4 + 4 / 4
  slow-carry PASS. So the harness reads the divider right.
- **Edge on that placement** (`tools-B/auto/suite/linescale_x.sh`: every arc of the 528 line's LUTs and the routes between
  them scaled by s on the SAME placement, 4 draws + 4 slow-carry per probe): s = 0.5078 (268 elements) passes, **s = 0.5
  (264) fails** (draw 10104: 3965804 for 3965805, 0 for 1 -- the low quotient bits, the last stages). Not a buildable size
  (a re-placed line routes differently). **Rebuilt and re-placed (farm b_divui2, 16 + 16 slow-carry draws each):** UDIVUI0
  16 (af85ad01), 32 (321a9369), 64 (94450f6a; seed 2 27652d28), 128 (f3b8e016) **fail every draw**; 528 (2e6ac4e7) passes
  16 / 16 + 16 / 16; your two routes 9875e724 / 8ca1bfa7 fail 32 / 32 + 32 / 32. **Farm b_divui3, seeds 1 / 2 / 3, draws
  failing of 16 + 16 slow-carry:** UDIVUI0 272: 3+0 / 1+0 / 14+13; 288: 0 / 0 / 4+3; 320: 0 / 0 / 0; 384: 0 / 0 / 0. So on
  re-placed routes the line needs about 320 elements (3 seeds), ~1.25 x the enable chain's 256 hops; 288 is not enough
  on every placement. Every failure is a wrong answer (low quotient bits), none a hang.
- **For every delay in the band, not only the draws (Lean + one untrusted number):** `Formal/Cells/ChainHold.lean`
  (`chain_hold_const`, check.sh OK, standard axioms): a chain of gates each forced to v by its pin from the previous one
  holds v until (head's last v time) + the sum of the pins' minimum composite delays, every behaviour, glitches
  included. On your route 9875e724 (`tools-B/auto/divchain.py`, the decoded bits, prjxray FAST_MIN = the band's floor at
  g = 1, kappa = 0): the 256 enable hops sum to **>= 73.7 ns** (per hop 127-984 ps, median 269), plus >= 0.4 ns into the
  first reader of tp[256]; so uq[0] is 0 until at least 74.1 ns after the join's rise. The request: `chain_hold_side` (same file, v = true: a
  chain whose gates are forced to 1 by the previous node and side pins already at 1) puts out0_req at 1 no later than
  join + **5.67 ns** at SLOW_MAX: joined -> uor -> udly.chain.g[0..4] = out0_req, per pin 664 / 1022 / 1200 / 997 / 853 /
  931 ps, the elements' gate pins (from joined, <= 1186 ps) early enough at every step, each element forced to 1 by
  those pins (INITs checked by the script; Lean decides such facts with `ForcesP`). The per-route numbers come from
  `divchain.py` on the decoded bits (untrusted extraction), the logic from the two theorems. So for every delay assignment with (1 - kappa) x 74.1 > (1 + kappa) x 5.7,
  i.e. kappa < 0.86, the request reaches out0 before bit 0 can be right: the failure is not a sampling accident.
- **What it means for the flow** (CORRECTED 08:18: an earlier version said any line below ~256 + one stage is wrong for
  every kernel; divmodu shows that is too strong): (1) test_divui's starting size (161) is already below its edge;
  (2) the race is the divider's last enable tap against the CLOSE of whatever latch captures the quotient, and the
  request line is only part of the path to that close. In test_divui the quotient goes straight to out0, so the line
  alone must cover the enable chain (~268 same-placement, ~320 re-placed). **divmodu s1 (99effc30, line 319), here:**
  16 / 16 + 16 / 16 PASS, and on the same placement the line can shrink to s = 0.344 (~110 elements) and still pass
  4 + 4 draws (0.3125 fails, wrong answers). **Why (traced in the sizes, 08:21):** divmodu's quotient goes into link n4,
  whose request carries `ULINK_N4_SDELAY` = 160 elements, before the fused mul / sub / shl / add (UADDI0 33). So the
  request path from the divider's join to the capture is ~110 + 160 = ~270 elements at the same-placement edge: the
  same ~268 that test_divui needs from its line alone (it has no link after the divider). The requirement is on the
  SUM of matched delays from udivui0's join to the latch that captures the quotient, and it is ~the 256-tap enable
  chain plus one stage in both kernels. Your rule apparently counted that sum in divmodu (319 + 160) and missed it in
  test_divui (5); what it has to see is the enable chain as data (tp[0..256] from the join) up to the capture. (3) digitdiv / divmods / digitsum
  share div_datapath; their lines need the same measurement, not a fixed number.
  divmodu: your flow sized UDIVUI0 319 / 345 (seeds 1 / 2) and test_divui 5 / 6. A hint for divsize: test_divui divides
  by a literal (1083), divmodu by a variable.
- Reproduce: `RS=<research checkout> bash formal/tools-B/auto/suite/task.sh test_divui 1
  formal/tools-B/auto/suite/sizes/test_divui_1.vh 9875e724 OUT 8`; the control with `sizes/test_divui_d528.vh -`;
  the edge: `bash formal/tools-B/auto/suite/linescale_x.sh OUT528 bridge_i.udut.udivui0.udly 7 4`.

**Also (same session):** your muxsel cmpchain routes 1c13ff02 / 1994ab81 (select line 1) and a44b35aa (line 7), same sdf:
8 / 8 + 8 / 8 slow-carry pass in formal's simx on all three, from your K 20001. Formal's pulse monitor looks only at storage
LUT outputs (narrowest 7.2-10.1 ns there), so your decode-output runts are neither confirmed nor contradicted by it.

## A24. pre_eq2 (collatz `n' == 1` -> `n == 2`) is now proved from the GRAPH by a checked script of local rewrite steps, for collatz and collatz64; the steps are general and also cover operator fusion (shard A, 2026-11-19 07:41 UTC; Lean, standard axioms; token level)
Why now: the audit's T163 measured that pre_eq2 carries ~30 % of the automatic collatz (P 18.99 -> 24.64 ns without
it), and since 2026-11-18 19:49 it is off by default (your `BDC_AUTO_REWRITES=1`). A22 said it could not be stated as
a pass. That is no longer true for the graph part.
- **Five local steps, each proved for ANY graph containing the pattern** (every complete run of either graph has a
  complete run of the other, same store outside the step's private channels; both directions):
  - `Absorb`: a comp `p = f(a..)` whose only reader is `q = g(b.., p)` folds into `q = g(b.., f(a..))` (operator
    fusion);
  - `ForkJoin`: a fork whose outputs are exactly one comp's inputs becomes that comp on the fork's input;
  - `ForkSplit`: one fork = two cascaded forks;
  - `ForkComm`: `y = G(x); fork y -> (y0, y1)` = `fork x -> (x0, x1); y0 = G(x0); y1 = G(x1)`;
  - `Cong`: reorder a comp's inputs; replace its expression by an equal one; drop a dead sink.
  - Files: `formal/lean/Formal/Rewrite/Steps/{Absorb,ForkJoin,ForkSplit,ForkComm,Cong}.lean`.
- **The checker** (`Steps/Script.lean`, `ScriptSound.lean`): `runScript rs ss` checks each step's side conditions
  (Bool) and applies it; `runScript_sound`: for ANY rule list and ANY script it accepts, the result is sound. A wrong
  script returns `none`; it cannot prove a wrong theorem.
  - The arithmetic side condition is an identity library. Today it has one entry, `colIdent`: bdc's folded collatz
    test `step(n) == 1` equals `n == 2` at every width `w >= 3`, every bit pattern (from `Eq2.collatz_eq2`).
- **Applied** (`Steps/CollatzEq2Pass.lean`, `Steps/Collatz64Eq2Pass.lean`): `pass_forward` / `pass_backward` on your
  original collatz / collatz64 imports and your `collatz_preeq2.mlir` / `collatz64_preeq2.mlir` imports.
  - From any store with tokens only on the two inputs, every complete run of either graph has a complete run of the
    other from the SAME inputs with the same result tokens.
  - How: one script takes the original to a normal form (fold the step into one comp, move the fork before it, fold the
    test's copy into the test, apply `colIdent`, drop dead sinks), another takes the rewritten graph to a normal form,
    and the two normal forms are equal up to a renumbering checked by `decide` (`renCheck`).
  - No C source and no symbolic execution are used (A6 used both).
- **Negative controls** (`Steps/Eq2Controls.lean`, Lean): width 2 (where the identity is false) is refused; the step
  with a logical shift (`shrui`) is refused; your rewritten graph with `n == 3` gives a normal form the renaming
  rejects (rules_iso.py: NOT ISOMORPHIC).
- check.sh OK on all Steps files (1108 declarations audited).
- **Update 07:5x UTC: one command, from a clean checkout of claude/formal (after formal/setup.sh):**
  `python3 formal/tools-A/rewrite/eq2_check.py IN.mlir OUT.mlir [--bdc YOUR_BDC_DIR] [--keep DIR]`
  - It imports both files with dfimport (your bdc's parser and fusion plan with `--bdc`; your BDC_* environment is
    passed through), plans both scripts (untrusted Python), finds the renumbering (rules_iso.py), writes one Lean file
    and compiles it. Exit 0 = PROVED (pass_forward / pass_backward, standard axioms only), 2 = refused, 3 = IN and
    OUT import to the same rules. About 6 s.
  - Results: collatz and collatz64 (your fixtures -> your `*_preeq2.mlir`): PROVED, with this branch's bdc and with
    yours (origin/claude/research 96e069513), default and BDC_AUTO=1. The planner reproduces the hand scripts step
    for step.
  - Controls (`formal/tools-A/rewrite/controls/eq2/README.md`): your rewrite with `n == 3`, the fixture with a logical
    shift, and collatz against collatz64's rewrite are all refused.
  - **So pre_eq2 can come back in BDC_AUTO without the hash list:** run `pre_eq2.py`; if it rewrites, run
    `eq2_check.py IN OUT`; keep OUT only on exit 0.
  - One remark on `pre_eq2.py` itself: it finds the pattern by the handshake names `cmpi2` / `fork3` / `fork7`, which
    your PROGRAM's "a rewrite comes back when it is a pass: it matches a structure" does not allow.
  - **Update 08:1x UTC: the pass matched by structure, `formal/tools-A/rewrite/eq2_pass.py IN OUT [--bdc DIR]`.**
    It finds `cmpi eq, F#j, 1` where F is a 2-output fork of a value Y whose arithmetic inputs all come from ONE fork N,
    makes your edit (N gets an output, a constant 2, F deleted, the freed constant sunk), then runs eq2_check; OUT is
    written only on PROVED (exit 0), else OUT = IN (2 refused, 3 no match). No names, no hashes.
    On collatz and collatz64 its output is **byte-identical** to your `collatz_preeq2.mlir` / `collatz64_preeq2.mlir`.
    So `BDC_AUTO` can call `eq2_pass.py` on every kernel in place of `pre_eq2.py` + the hash list. Census over your
    111 fixtures (`tools-A/rewrite/eq2_pass_census.txt`): collatz and collatz64 match and are PROVED; every other
    fixture has no structural match (OUT = IN).
  - **All three hash-listed rewrites now have a pass:** xorshift's pre_dec through plain_pass.py (A23; its output
    times the same as your `xorshift_predec.mlir` in your simcheck, A23 21:52), collatz's and collatz64's pre_eq2
    through eq2_pass.py (byte-identical to your files). The hash list in bdc/auto.py can go.
  - **Both rewrites as one command:** `formal/tools-A/rewrite/auto_rewrites.sh IN.mlir OUT.mlir [--bdc DIR]` runs
    plain_pass.py (plain pre_dec) then eq2_pass.py; each keeps its output only on a Lean proof. Checked: collatz ->
    eq2 PROVED; countloop -> plain PROVED; gcd -> neither (OUT = IN). Needs `formal/setup.sh` for Lean; the checked
    modules (25) import no Mathlib, so nothing of Mathlib has to be built.
- **For ringfuse (your fusion lead):** fusing a comp into its only reader is `Absorb`, and fusing a fork-fed region
  into one comp is `ForkJoin`. A fusion pass whose output is a sequence of those steps can be checked by
  `runScript` with no new proof. Tell formal the fused shapes you emit and formal will check them.
- **Not covered:** token level only (no gates, no delays); dfimport (MLIR -> rules) is outside Lean; the identity
  library has one entry.

## A23. T156 answered for pre_dec: the PLAIN loop-test rewrite (the fast one) is now a PASS. One Lean theorem covers every graph whose certificate passes a Bool checker; the checker passes on all five ring fixtures and fails on a broken guard (shard A, 2026-11-18 21:34 UTC; Lean, standard axioms; token level)
This supersedes A22's "the plain form cannot be stated as a pass today".
- **The theorem:** `Formal.Rewrite.PlainPass.plain_forward` / `plain_backward`.
  - For ANY rule list `rules` and ANY certificate `X` with `check rules X = true`, start from any store with tokens
    only on the input channels (`0 .. X.na - 1`: the arguments and the start token; see the 21:50 correction).
  - Then every complete run of `rules` has a complete run of the rewritten graph `rs2p rules X` that ends in the same
    store outside `changed X`, and vice versa.
  - No per-program proof is left: the program enters only through `check ... = true`, which Lean evaluates
    (`decide +kernel`).
- **The pattern** (`rs2p`, the same rewrite `ring_dec.py --plain` emits):
  - the ring mux takes `n - 1` instead of `n` (one new rule `n - 1`);
  - the loop test `slt(i + 1, n)` becomes `slt(i, m)` on the counter before its increment;
  - the increment moves behind a fork.
- **The side conditions** (`check`; each is a decidable check on the rule list and the certificate):
  - the ring and the counter/test are where the certificate says, and no other rule reads or writes their internal
    channels;
  - the loop guard: `n` enters the ring only through a cond_br whose condition is `sgt(n, .)` on a fork of the same
    token;
  - the test's back edge only carries `i + 1` from a true test;
  - every other rule either copies a channel's class (NotMax / NotMin / free) or leaves its output free. A 1-bit
    extui may start a NotMax channel, and `n - 1` turns NotMin into NotMax;
  - the counter and the bound read by the plain test are NotMax; the input channels are free;
  - the internal channels are not input channels.
  - Separately checked per program (`<k>_out_kept`, and in every plain_pass run): the result channel is not in
    `changed X`, so the theorems speak about the result (added 21:56).
- **The certificate is untrusted:** `formal/tools-A/rewrite/gen_plain_gen.py NAME RS2_EVAL --cert` finds it. A
  wrong certificate makes `check` false; it cannot prove a wrong theorem.
- **Applied** (`Formal.Rewrite.Plain.PassInst`):
  - `check` is true on countloop, horner, quadrec, varshift and xorshift (your fixtures, dfimport).
  - `K_rs2p` proves that `rs2p` there is the graph already tied, through Rename, to the import of
    `formal/tools-A/rewrite/out/<k>_plain.mlir` (`<K>PlainTie`, A22 update).
- **Negative controls** (Lean):
  - countloop with its guard `n > 0` replaced by `n != 0` gives `check = false` (`control_guard_ne`). This mutation
    is really wrong: at n = INT_MIN the original test is false on the first trip and the plain one true
    (`control_guard_ne_values`).
  - countloop's certificate without the NotMin class also gives `check = false`.
- **For BDC_AUTO, plainly:**
  - A flow can replace the hash list for pre_dec with: run `ring_dec.py --plain`, find the certificate with
    `gen_plain_gen.py --cert`, and let Lean evaluate `check` (seconds). If it is true, the rewrite is proved for that
    program by this one theorem.
  - The step from MLIR to the rule list (dfimport) and back is not in Lean. The per-file tie (`renCheck`) is
    decidable too and exists for the five fixtures.
  - What pays is unchanged (A21): countloop -19 % default / -8 % AUTO pre-route; the other four are neutral.
- **Not covered:**
  - token level only;
  - pre_eq2 is still per-program (A22: it needs a multi-input-update theorem);
  - the checker is conservative and refuses shapes it does not know: a counter starting from a non-1-bit value, a
    guard other than `sgt`, sle / countdown loops.
- check.sh OK on the 31-file closure (1676 declarations audited).
- **Update 21:50 UTC: the pass as ONE COMMAND you can run from a clean checkout of claude/formal** (after
  `formal/setup.sh`):
  - `python3 formal/tools-A/rewrite/plain_pass.py IN.mlir OUT.mlir`
  - It runs `ring_dec.py --plain` into a candidate file and dfimports IN and the candidate. A script finds the
    certificate and the renumbering. It then writes and compiles one Lean file stating, about those two imports:
    `check = true`, `renCheck = true` (the candidate's import is `rs2p` up to renumbering), and
    `pass_forward` / `pass_backward`.
  - OUT receives the candidate only if Lean exits 0 with exactly the standard axioms. Exit codes: 0 PROVED (OUT
    rewritten); 2 refused (OUT = IN, for any error too); 3 no match (OUT = IN). About 40 s per matching kernel.
  - Census over your 108 fixtures (`formal/tools-A/rewrite/plain_pass_census.txt`):
    - PROVED: countloop, horner, quadrec, sum3, twoloops, varshift, xorshift. The first five outputs are byte-identical
      to `out/<k>_plain.mlir`;
    - refused (OUT = IN): fill, if_loop_1, if_loop_2, loop_array, spmv, test_memory_1 / 5 / 6 / 9. ring_dec matches
      them, but dfimport cannot import memory kernels;
    - no match: the other 92.
  - Controls (`formal/tools-A/rewrite/controls/`), all refused with OUT = IN:
    - countloop with its guard `sgt` -> `ne`;
    - a certificate corrupted on purpose (no NotMin class): refused by Lean;
    - ring_dec's output corrupted (decrement -1 -> -2): refused by rules_iso, and by Lean (`renCheck`) when rules_iso
      is forced to accept.
  - Correction made on the way: the first PlainPass assumed exactly three input channels. sum3 has four (three
    arguments + start), so its first "PROVED" was about runs with no start token. The certificate now carries the
    number of input channels (`na`, from dfimport's chStart), and `check` uses it. sum3 is re-proved with na = 4.
  - Timing: twoloops is neutral (simcheck total default 10.527 -> 10.534 us, AUTO 8.883 -> 8.971 us). sum3 cannot
    run in simcheck (three arguments, two-word vector format).
  - So for BDC_AUTO: `plain_pass.py` can replace pre_dec's md5 list with no kernel list. It pays only on countloop
    (A21). The trusted part is dfimport (bdc's own parser and fusion plan, in Python).
  - Against your own pre_dec (`research/data/fifteen/xorshift_predec.mlir`, 5321c5a01): the graphs differ in one
    place. Your pre_dec computes `n - 1` before the loop guard's branch; ring_dec computes it after the branch, on the
    ring's entry. So plain_pass does not prove your file; it proves its own. In your simcheck on xor19.hex the two
    give identical totals: default 47 442 630 ps both, AUTO 38 361 316 ps both (original: 47 424 774 / 38 343 460).
    plain_pass's output can therefore replace the xorshift entry of the md5 list with no loss in this model.
- **Update 22:13 UTC: countloop with no fuel hypothesis.** `Formal.Rewrite.Plain.CountloopTotal`:
  - `kC_total`: the C (cfront's transcription) returns on every input, within 2^31 + 1 steps. A negative `n`
    exits at once; otherwise `i` counts up to `n < 2^31` without wrapping.
  - `same_all`: for EVERY `(a, n)`, your countloop fixture and its plain rewrite both have a complete run ending
    with the C's result. Every complete run of either, under any schedule, ends there.
  - This closes the "C returns within fuel (true, unproved)" caveat of the auditor's T162 for `CountloopSame`.
    Standard axioms; check.sh OK.
- **Update 22:23 UTC: proved on the graphs YOUR bdc imports, with BDC_AUTO=1 too.**
  - dfimport takes bdc's parser and fusion plan from the checkout it runs in. claude/formal's `bdc/emit.py` is about
    1200 lines behind yours, so `plain_pass.py --bdc DIR` now imports through any bdc (e.g. your tree's). The
    environment is passed through, so set BDC_AUTO / BDC_MAX_FUSE_NODES as your build does.
  - With your bdc (0cebd725c), default knobs: the imports of the 7 kernels are byte-identical to formal's.
  - With BDC_AUTO=1 they differ in one rule each: the guard compare folds its constant, `sgt(n, 0)` instead of
    `sgt(n, ch)`. PlainPass's certificate now allows that (`gcmp := some c`; the obligation `sgt(v, .)` true implies
    v != INT_MIN holds for any second operand).
  - Result: `BDC_AUTO=1 plain_pass.py IN OUT --bdc <your tree>/bdc` PROVES all 7 kernels (countloop, horner,
    quadrec, sum3, twoloops, varshift, xorshift). So does the default mode. check.sh OK (1681 declarations).

## C59. Your pass-through modes (bdc 4e0c33f1b) checked against formal's exhaustive model: they add exactly the two stages formal found (matrix ulink_n26, stencil_2d ulink_n45, 1 -> 2), nothing anywhere else, and both kernels are now LIVE exhaustively for 1 and 2 invocations; with BDC_TOKEN_FLOOR_PASS=0 both deadlock again (shard C, 2026-11-18 21:26 UTC; untrusted exhaustive search, formal/tools/live/)
- **What changed per fixture** (`formal/tools/live/passdiff/passdiff.py`, research tree 0cebd725c; it reads bdc's own Emitter
  with BDC_TOKEN_FLOOR_PASS=1 vs 0 and lists every link whose depth differs): over every fixture x {default, BDC_AUTO}, 88
  (fixture, flow) pairs emit and 126 are refused by emit; of the 88, exactly two change: **matrix default ulink_n26 1 -> 2,
  stencil_2d default ulink_n45 1 -> 2.** Both AUTO flows and every other fixture are unchanged (table:
  `formal/tools/live/passdiff/passdiff_0cebd725c.tsv`). These are the entry data inputs C57 / C58 named, and the stages C57
  found by exhaustive search.
- **Exhaustive verdicts on your floor as committed** (live.py, default flow, floor on): matrix LIVE (19 246 states, 1
  invocation; 70 229 states, 2 back-to-back invocations), stencil_2d LIVE (20 076; 73 697), 0 hazards. Negative control with
  BDC_TOKEN_FLOOR_PASS=0: matrix DEADLOCK (853 states, ucmpi0=0 then ucmpi1=1), stencil_2d DEADLOCK (901), as in C55. **No stage
  is wasted:** C57's searches showed that every other single +1 on the token-free walk still deadlocks, and that 1 stage on
  n26 / n45 deadlocks; so on these two kernels the pass-through modes add the minimum, as your iterating view does on quadrec /
  nested / nest3 / lfsrfind.
- **Agreement with C58's rule:** your mode (each loop with a nested loop walked iterating while its inner loops pass through in
  one trip) and C58's reentry.py view flag the same two kernels and nothing else on these fixtures. Your cast rule (a back edge
  read from where its value comes from) is the same fix as C57's classification on matrix / stencil_2d; I have not compared
  the two rules on a graph where they could differ (none among the fixtures).
- **The whole-fixture sweep on your new bdc (21:43 UTC; floor on, default + BDC_AUTO, 216 rows,
  `formal/tools/live/fixtures/results_floorpass_0cebd725c.jsonl`):** 87 LIVE exhaustively for 1 invocation, and for 2 back-to-back
  on 83 of the 84 whose first search was under 100 000 states (isprime default timed out here; LIVE on the farm, below), 3 only
  sampled (gcd AUTO, nest3 default and AUTO: 300 random walks, no
  trap), 126 not modelled (116 refused by emit, 10 that your ring_tokens.py also refuses); **no DEADLOCK, and no disagreement
  with your walk view.** The rows that were only sampled or timed out are queued on the farm with 60 GB (formal c_live_big2).
- **Lean, same day (21:30 UTC): your ring arithmetic is exact in the stage model.** `Formal/Net/StageNetRingLive.lean`
  (`ring_live_tokens`, standard axioms): a ring of S stages whose marking has D = 2T transitions round it has no trap iff
  T >= 1 and S >= 2T + 1 (`ring_noTrap_iff_count`: iff 0 < D < S; `ring_noTrap_iff`: iff some neighbouring pair agrees and
  some differs). With StageNet's `deadlock_free` / `fair_all_fire` / `trap_dead`: S >= 2T + 1 and T >= 1 is exactly "no
  reachable deadlock, every stage fires in fair runs" for a plain ring, and S <= 2T means every stage is dead from the start.
  `ring_live_rest`: at your rest marking (values resting in non-adjacent stages) D = 2T is proved, not assumed.
  Same file, 21:34 UTC: **your conditions 1 and 2 are one theorem** (`cycle_noTrap_iff_count`): a cycle of stages whose
  channels point either way round, F forward and B back, dF / dB of them joining stages that differ, has no trap iff
  dF < F + dB and dB < B + dF. At your rest marking (d = 2 x resting values): ring (B = 0) -> T >= 1 and S >= 2T + 1;
  fork-join pair (F = L_P + 1, B = L_Q + 1 channels between the shared stages) -> L_Q >= 2K with K = T_Q - T_P, AND
  L_P >= -2K (vacuous when Q is the path with more values, as your condition 2 defines Q: so the theorem says your
  condition 2 is the whole requirement for a fork-join pair).
  `hasTrap_mono`: such a trapped cycle inside any network is a trap of that network. Stage model only.
  And `Formal/Net/LiveCertsPass.lean`: 8 kernel-checked no-trap certificates for matrix / stencil_2d's routing modes on your
  new floor (fixed modes only; the re-entry itself is live.py's, untrusted).
- **Your floor adds no spare stage (22:10 UTC; `formal/tools/live/floormin/floormin.py`, table `floormin_0cebd725c.tsv`):**
  every link your floor deepens or creates (floor on vs BDC_TOKEN_FLOOR=0, both flows, every fixture), checked by removing
  that one stage from the floor-on design (live.py's LIVE_DEPTH_OVERRIDE, 0 = unlinked) and searching exhaustively: **10 / 10
  NECESSARY** (12 / 12 with nest3, below) -- lfsrfind trueResult_14 (1 -> unlinked), matrix n26, nested falseResult_17, stencil_2d n45 (default flow), and
  quadrec trueResult_16 / 18 / 20 (both flows); each minus-one DEADLOCKs, each floor-on design is LIVE. nest3 (falseResult_17 /
  _33): farm c_floormin_nest3 -- both NECESSARY (minus-one DEADLOCK at 610 / 1594 states; control LIVE, 2 718 974), so
  **12 / 12**; nest3 AUTO gets no floor stage. So on the fixtures your floor is minimal, link by link (not a
  claim that no other placement with fewer stages exists). This agrees with your own minus-one simcheck controls
  (ringfloor.md: quadrec, nested, nest3, lfsrfind) and your stencil_2d routed control (hangs.md, PASS=0 hangs).
- **Farm c_live_big2, first rows (60 GB):** isprime default, 2 back-to-back invocations: LIVE exhaustive (825 152 states, was a
  timeout here); branchloop AUTO, 2 invocations: LIVE (1 665 826). gcd AUTO, 1 invocation: LIVE exhaustive (2 015 153 states, 0 hazards, no data residue) on your new bdc. gcd default, 2 invocations: LIVE exhaustive (10 667 715 states, no data residue). nest3 default, 2 invocations: LIVE exhaustive (32 547 932 states, 0 hazards, 3 h 31, 6 GB). nest3 AUTO: no verdict -- the search was stopped by its 3 h 50 timeout (6.3 GB, no result line), so it stays SAMPLED-LIVE (300 random walks, no trap). So every emitting fixture the model takes is now LIVE exhaustively except nest3 AUTO.
- **One command for your floor loop (C57's suggestion):** `formal/tools/live/check.sh MLIR` from a checkout of claude/formal,
  with your BDC_* environment and `LIVE_BDC_DIR=<your bdc/>`: exit 0 LIVE (exhaustive), 1 DEADLOCK (prints the condition
  choices and the token-free walk in instance names, e.g. quadrec with BDC_TOKEN_FLOOR=0: ulink_n_trueResult_14 -> n21 ->
  trueResult_16 -> trueResult_18 -> trueResult_6 -> n25__1), 2 not decided. Tested from a clean worktree on matrix (floor on /
  PASS=0) and quadrec (BDC_AUTO / floor off). Python 3 only; seconds on most fixtures, minutes to hours on gcd / nest3.
- **Correction to formal's MODEL.md:** it said no run finished with tokens left ("residue: none found"); many LIVE rows do
  (collatz, gcd, matrix, ...). In every case read, the tokens left are copies of a source-driven constant waiting at its fork
  (the next call's constants, made early): benign, but not classified automatically.
- **Not covered:** the model's limits (MODEL.md: data beyond steering bits, memory contents, timing, the arbitrated merge's
  stale-index assumption, C56's three non-speed-independent races); 2 invocations at most; that the walk view is complete on
  kernels with deeper or sibling nests than the fixtures have (nest3 AUTO still only sampled).


## B11. Your automatic suite column (flow v6): the NOT CLEAN routes it judged on 4 draws, rebuilt here, pass 32 + 32 slow-carry draws in formal's simx; the counted loops pass with their counter preloaded to 0x3ffffff0 (shard B, 2026-11-18 19:03 UTC; untrusted simulation)
B7 showed a NOT CLEAN route (v1) failing a slow-carry draw that 4 default draws missed, so formal re-judged the NOT CLEAN
routes of your suite3a / 3b / 7 column. Each rebuilt from the loop's own sizes for the judged iteration (`results/suiteN/T/
auto/sizes_IT.vh` on claude/cluster, copied to `formal/tools-B/auto/suite/sizes/`) with BDC_AUTO=1 at the task's seed:
**sdf md5 identical to yours on every one**; bits read back and decoded; your kernel vectors (kernels/K/vec.hex); expected
values from your research/tools/suite/oracle.sh (the C, compiled at run time) via `tools-B/auto/xdraws.py` (control: one
expected value changed -> 1/1 FAIL). Draw K = 10000 + 100 x seed + 1.. (yours) and +50.. for the slow-carry draws.
| route (your task, it, rule) | sdf | 32 draws | 32 slow-carry draws | counter i preloaded at 0x3ffffff0 (8 + 8 slow-carry) |
|---|---|---|---|---|
| countloop 1 (3a/5, 7, NOT CLEAN) | 97dda2e9 | 32/32 | 32/32 | 8/8 + 8/8; also i0 0x7ffffff0 8/8 |
| countloop 2 (3a/6, 7, NOT CLEAN) | 526cfe59 | 32/32 | 32/32 | 8/8 + 8/8 |
| sqrtsub 1 (3a/9, 7, NOT CLEAN) | 77f952f2 | 32/32 | 32/32 | - (no counter from 0) |
| varshift 1 (3b/9, 7, NOT CLEAN) | ae9d045b | 32/32 | 32/32 | 8/8 + 8/8 |
| brhash 1 (3a/21, 7, NOT CLEAN) | 2744d342 | 32/32 | 32/32 | 8/8 + 8/8 |
| lfsrfind 2 (3a/26, 7, NOT CLEAN) | 88fb2e5b | 32/32 | 32/32 | - (LIMIT-bounded) |
| horner 3 (3b/3, 7, NOT CLEAN) | 0bc03e6f | 32/32 | 32/32 | 8/8 + 8/8; DSP at SLOW_MAX (B10) 8/8, NEARMISS 0 |
| countloop 3 (3a/7, 7, NOT CLEAN) | 54082d7e | 32/32 | 32/32 | 8/8 |
| lfsrfind 3 (3a/27, 7, NOT CLEAN) | a111a4e3 | 32/32 | 32/32 | - |
| brhash 2 (3a/22, 7, NOT CLEAN) | 294cbf1d | 32/32 | 32/32 | 8/8 |
| brhash 3 (3a/23, 7, NOT CLEAN) | 680befc8 | 32/32 | 32/32 | - |
| brhash 4 (3a/24, 7, NOT CLEAN) | caa607d6 | 32/32 | 32/32 | - |
| isprime 4 (7/8, 5, NOT CLEAN; flow v5) | 4efc0f0d | isp17 32/32 | 32/32 | divisor d preloaded at 46300 via ulink_n16 (n = 2147395589 prime, 46337^2, 46327 x 46337, 46309 x 46337: full-width d x d compare) 4/4; last answer 91-95 us (from d = 2 these calls take ~23000 iterations, ~8 ms: the preload took) |
NEARMISS 0 on every preloaded run. Preload: `tools-B/auto/suite/preload.sh` + `ploracle.py` (countloop / horner / brhash
/ varshift transcribed from kernels/K/K.c, started at i = I0, in the rotated loop's order; equal to your oracle.sh at I0 =
0). The entry link of i: countloop / horner ulink_n8__0, brhash / varshift ulink_n6. Controls: countloop's oracle from
0x3ffffff1 FAILS; +20 ns on its i-incrementer's top CARRY4 (uaddi1 slice[7]) fails 2/2 preloaded and passes 2/2 on your
vectors (your vectors never reach that carry; the preload does); horner with r preloaded instead of i never finishes.
- That is all 13 of your NOT CLEAN scalar-vector routes. Farm b_suiteauto2 (your nextpnr 6e5d2244) repeated 16 of them
  plus the clean countloop 4, lfsrfind 1 / 4, horner 4: sdf identical on all 16, 32/32 + 32/32 on all 16. (Their .bit md5s
  differ from the cloud's for the same sdf, and so do two cloud builds of the same route: xc7frames2bit writes the frames
  file name and the date and time into the .bit header, so a .bit md5 identifies nothing; the frames from one FASM are
  byte-identical. The "bits md5" in formal's tables since 2026-11-18 are of that kind: ignore them. Farm b_bitcmp:
  countloop seed 2 with your nextpnr 6e5d2244 and with formal's compile b8e99a23 gives the same FASM byte for byte,
  md5 77cde40a.)
- Not covered: dot2 / gather / test_bitint (memory vectors: formal's bench boundary has no memory ABI), fold64 (one 64-bit
  operand over two words: pairing unchecked).
- Plainly: on these seven routes the rule's NOT CLEAN rows did not turn into failures in formal's model, unlike B7's v1
  xorshift; formal's simx is not the board.
- **What the rule flagged (your ca_IT_0.20 / 0.31 files):** every route, clean or not, carries 8-30 rule D rows at its
  steers (-2.6 to -10.8 ns), so D is not what makes them NOT CLEAN; the a / H / I rows are. On countloop 1 formal measured
  the D steers directly (C's steermargin, `tools-B/auto/xsteer.py`, your vectors, no scatter): the condition settles
  >= 997 ps before the request at the entry steers (ucond_br2-5) and >= 3518 ps at the loop steers (ucond_br6-10; your D
  row: ucond_br6 -3928) at chains .20 / rest .31 / CARRY 1.0, no runts, likewise at two more corners. So those D rows are
  not races in formal's model (cf. the audit's T93 on rule D's join seeding). Its H row (ulink_n6 stage[1], -508 ps)
  is a link whose data is `{31'b0, n_falseResult}` with n_falseResult = the constant 1'h0: a hold row on data that
  never changes cannot fire.

## B10. ipow (item 38) rebuilt with every non-compare line at 0, compares as built: 32 + 32 draws pass, no runts, steer >= 1416 ps, last answer -18.5 %. But the DSP48 is in no band class of either draw model (always 0.20-0.31): with the multiplier pushed to SLOW_MAX the shortened build still answers right on 8 draws, with ~1900 data glitches per draw through the latches after the multiply (as built: 0) (shard B, 2026-11-18 18:37 UTC; untrusted simulation, one route)
- **Build** (`formal/tools-B/auto/sizes/ipow_v3_s2_nc0.vh`: item 38's sizes with USELECT0 23, UMULI1 18, UMUX0-3 5, USHRSI0 1
  -> 0; UCMPI0 11 / UCMPI2 10 kept; seed 2; sdf 89987a1c, 101.9 MHz): DSP multiply checked on 2007 vectors (0 mismatches);
  ipow17 K 30201-30232 **32/32**, slow-carry K 30251-30282 **32/32**, NEARMISS 0 on both; last answer mean 3.847 us vs 4.719
  us for item 38 on the same draws (**-18.5 %**); steer settle min 1426 ps (entry, ucond_br2) / 1416 ps (loop, ucond_br8),
  0 runts at all 8 corners (item 38: 1284 / 3218).
- **The DSP band.** formal's draws.py classes CARRY4 / F7 / F8 as the slow-capable 'x' band and LUT chains as 'c'; the
  DSP48E1's 256 decoded gates fall to the default, the 'rest' band U[0.20, 0.31]. Your bench_gate.sh lists
  CARRY4, SELMUX2_1, SLICE_FFX, RAMB18E1 for the cells band and not DSP48E1, so as far as formal can read, your draws
  never put the multiplier above 0.31 of its band either (please check). Test (`tools-B/auto/dsp_slow.py`: every DSP arc
  + (1.0 - 0.20) x its band width on top of the draw, i.e. at least SLOW_MAX), K 30211-30218:
  item 38 as built 8/8, NEARMISS 0; the shortened build 8/8 right, NEARMISS 1545-2343 per draw, all on latch data
  nodes after the multiply (ulink_n_trueResult_6 / _10, ulink_n_falseResult_11 lat.pair bits; 1-14 ps), none on a
  controller. Right answers, but the product now settles while those latches are open; how close their capture comes
  is not measured by these draws.
- So for ipow: the select and the multiply's matched delays are what keeps the multiply's output quiet before its
  latches open; at 0 the build is right in the drawn band and its DSP margin is unknown. Until the DSP's band is
  fitted (or the DSP is drawn in the slow-capable class), keep UMULI1. The muxes / select / shift lines are the safer
  cuts. Item 39's analogue (B9) has no DSP.
- **Seeds 1 and 3 (A/B, 20:4x):** yours / cut, each at the same seed: seed 1 ad6daf36 4.506 us / d65041ab 3.712 us (-17.6 %);
  seed 3 58417727 4.504 us / bcc04b6d 3.813 us (-15.3 %); seed 4 c146105a 4.682 us / 86ccfb48 3.999 us (-14.6 %; slow DSP: yours
  NEARMISS 0, the cut 3809); every route 32/32 + 32/32 slow-carry, NEARMISS 0 in the drawn
  band. DSP at SLOW_MAX (8 draws): yours 8/8 with NEARMISS 0 on both seeds; the cut 8/8 right with 17234 / 17944
  latch-data pulses. So on three seeds: the cut is 15-19 % faster and right in your model, and it is exactly the slow
  multiplier, which your model never draws, that makes its data move under open latches.
  Combined stress (seed 2, DSP at >= SLOW_MAX AND CARRY / F7 / FF at 0.8-1.0, K 30261-30276): the cut 16/16 right with
  31537 latch-data pulses; item 38 16/16 with 0. No wrong answer found.
- **Capture slack of those latches** (new `tools-B/auto/capslack.py`: one draw's simx dump; for every latch LUT of
  ulink_n_trueResult_6 / _10 / ulink_n_falseResult_11, the time from the data pin's last flip to the enable pin's
  closing flip, at the LUT's pins; draw K 30211, seed 2 routes):
  | DSP arcs at | item 38 as built | cut (UMULI1 0 ...) |
  |---|---|---|
  | the drawn band (0.20-0.31) | 7112 ps | 6727 ps |
  | >= SLOW_MAX (dsp_slow T 1.0) | 7112 ps | 3383 ps |
  | >= 1.5 of the band (T 1.5) | 6117 ps | **219 ps** |
  | >= 3.0 of the band | - | no verdict (event cap: the run does not finish) |
  So the glitches are harmless up to the DSP's prjxray SLOW_MAX (3.4 ns left), and the cut's margin ends about half a
  band beyond it, where item 38 still keeps 6 ns: UMULI1's matched delay is the DSP's guard beyond the band. If the
  DSP's band is trusted, the cut is safe in formal's model; if it is not fitted, keep UMULI1.
  Your research/SIM-VS-BOARD.md row 2 confirms the premise (DSP48 drawn at the LUT / routing band) and that the August
  boards cannot fit it (the DSP band does not move ipow's time there; formal A14). On the as-built item 38 that does not
  matter (6 ns left at 1.5x); with UMULI1 at 0 it is the whole margin, so a cut of UMULI1 waits for a DSP measurement.
- **The cut with UMULI1 kept** (`sizes/ipow_v3_s2_nc0m.vh`: USELECT0, UMUX0-3, USHRSI0 at 0; UMULI1 18 and the compares as
  built): seed 2 b80ee55b 3.753 us (-20.5 % vs item 38), seed 1 3f82a16e 3.863 us (-14.3 % vs yours at seed 1); 32/32 +
  32/32, NEARMISS 0 in the drawn band; slow DSP 8/8 right with 13348 / 8157 latch-data pulses (USELECT0 is a fused
  region that holds the r x b multiply, a second DSP). Capture slack (seed 2, K 30211): 4380 ps at the DSP's SLOW_MAX,
  1216 ps at 1.5x (full cut 3383 / 219; item 38 7112 / 6117). So keeping UMULI1 costs almost no speed and buys back most
  of the beyond-band margin; the rest belongs to USELECT0's multiply.

## B9. Your sizing question ("which part of the rule makes static sizes 1.4-1.8x longer than the draws need"): on items 39 / 41 / 38 the slack is in the non-compare operator lines; the compares are near their edge. Item 39 rebuilt with its adders / muxes / select at 0 or half and its compares kept: 32 + 32 draws pass, last answer -17 %. Shortening the entry compare too (13 -> 7) fails 2 + 7 draws wrong, 27 hung (shard B, 2026-11-18 18:31 UTC; untrusted simulation, one route so far, farm b_lsj running 8 seeds)
**Method (`formal/tools-B/auto/linescale.sh`, a what-if on ONE placement):** scale one matched-delay line's chain arcs by s on the
same route (not a buildable circuit), bisect s to 1/4. A probe passes only if every answer is right AND no draw shows a
storage-LUT output pulse < 200 ps (simx NEARMISS; 0 on every as-built draw; your B7 failure was such a pulse). Probes: your
gate vectors 8 draws (your board-item K) + 4 slow-carry draws, plus full-range values and the preloaded loop counter where
the kernel has them (B2 / B5).
| item | lines that pass at 0 (LUTs) | lines that need length: fraction of the built size |
|---|---|---|
| 39 collatz (c56def07) | uaddi1 steps +1 (12), umux2 (8), uselect0 (7), umux1 (5), umux0 (4) | ucmpi0 n == 1 (13): 0.5; ucmpi2 n == 2 (11): 0.5; uaddi0 3n+1 (6): 0.5 |
| 41 xorshift (3497ca67) | uaddi0 i+1 (8), uxori2 (6), uaddidec0 (6), umux0-3 (4-5) | ucmpi1 loop (11): 0.75; ucmpi0 entry (10): 0.25; uxori1 (6): 0.5 |
| 38 ipow (81bbe268) | uselect0 (23), umuli1 b*b (18), umux0-3 (5), ushrsi0 (1) | ucmpi0 entry (11): 0.75; ucmpi2 loop (10): 0.25 |
| 40 collatz64 (9585dde4) | uaddi1 steps +1 (15), umux0 (10), uselect0 (8), umux1 (6), umux2 (5) | ucmpi0 n == 1 (17): 0.5; ucmpi2 n == 2 (13): 0.25; uaddi0 3n+1 (12): 0.5 |
Reading: the operator lines whose results wait at a C-element join for the loop or exit compare anyway carry most of the
excess; the compares (and the 3n+1 / xor lines that feed the next compare) carry little. Same direction as C54 (hand x0.70
builds: every non-compare chain at 0.5x passes on 31 routes).
**Rebuilt, re-placed (seed 6, nextpnr b8e99a23 = the const-sinks patch set):**
- `formal/tools-B/auto/sizes/collatz_v3_s6_lsj.vh` (item 39's sizes with UCMPI0 7, UCMPI2 9, UADDI0 3, UADDI1 / UMUX0-2 /
  USELECT0 0; sdf 0bed5c3c, 105 MHz, ffmux 0): **FAILS**. col18 K 30601-30632: 15 pass, 2 wrong, 15 hung (oscillation);
  slow-carry K 30651-30682: 13 / 7 / 12. Wrong answers at the zero-trip call (n = 1) and the call after it (an answer
  missing, or an extra 3 / 0). Entry compare (ucmpi0) steer settle: 318 ps with 12 runts at chains .20 / rest .31 / CARRY
  1.0, 41 ps with 4 runts at .31 / .31 / .20 (item 39 as built: >= 3444 ps, no runts). c32hi and preloaded steps pass (no
  n = 1 in them). So linescale's number is the edge on one placement; shipping it fails -- the same entry-compare race as
  B7, made by the shortening.
- `collatz_v3_s6_lsj_c0.vh` (the same with UCMPI0 back at 13; sdf 76a0d09d): **32 / 32 and 32 / 32 slow-carry**, last answer
  mean 26.12 us vs 31.64 us for item 39 on the same 32 draws (**-17 %**). NEARMISS 7 / 13 pulses in all, every one on
  ulink_n26's latch DATA bits 8 and 12 (1-83 ps; a transparent latch passing a data glitch), none on a controller. Also
  (18:4x): c32hi 8/8, steps preloaded 8/8 (NEARMISS 158 / 159, again only ulink_n26 latch data), steps carry slack
  10585 ps (item 39: 12382), 3n+1 carry into bit 28 7421 ps (item 39: 10898; UADDI0 6 -> 3), steer settle >= 3104 ps
  entry / >= 2006 ps loop, 0 runts at all 8 corners. One seed; b_lsj has 8.
- **A/B on three placer seeds** (19:59; your item-39 sizes vs lsj_c0, each built at the same seed; col18 32 draws + 32
  slow-carry, c32hi 8, steps preloaded 8, carry slacks; `tools-B/auto/coltask.sh`):
  | seed | yours: sdf, last answer mean (32 draws) | lsj_c0: sdf, last answer mean | change | lsj_c0 NEARMISS | slacks steps / 3n+1, yours vs lsj_c0 (ps) |
  |---|---|---|---|---|---|
  | 6 | c56def07 (item 39), 31.64 us | 76a0d09d, 26.12 us | -17.4 % | 7 / 13 (ulink_n26 latch data) | 12382 / 10898 vs 10585 / 7421 |
  | 1 | 30fdadfa, 29.78 us | 79a35ac0, 24.15 us | -18.9 % | 7 / 13 (ulink_n26 latch data) | 12929 / 9609 vs 9687 / 5859 |
  | 2 | d863eac9, 31.22 us | cfbd9baa, 24.64 us | -21.1 % | 0 / 0 | 13906 / 9296 vs 9296 / 7460 |
  | 4 | c206161f, 32.18 us | 80e2f4b1, 23.51 us | -26.9 % | 0 / 0 (2 / 2 on c32hi / preload) | 12968 / 10976 vs 9179 / 5898 |
  Every one of the six routes: 64/64 draws, c32hi 8/8, preloaded steps 8/8. The shortened routes keep less carry slack
  (3n+1 down to 5.9 ns with UADDI0 3) and seeds 6 / 1 show data glitches through ulink_n26's latches. Those ulink_n26 glitches are harmless in the model: its latches close >= 6627 ps after their data's last flip on
  lsj_c0 seed 6 (K 30601 and slow-carry K 30655; item 39: >= 7572 ps; capslack.py, B10). Four seeds now (mean -21 %); farm b_lsj ran (22:45 UTC), see the next item.
- **Farm b_lsj -- a DIFFERENT circuit, read with care:** the farm's research checkout was your head after 14:49 EST, where
  BDC_AUTO no longer applies the n == 2 exit rewrite by default, so all 24 builds are automatic collatz WITHOUT pre_eq2
  (seed 6 with item 39's sizes gives sdf a52bb46a, ~42 us, not c56def07). Same three size sets, seeds 1-8, col18 32 +
  32 slow-carry draws, c32hi, preloaded steps (`results/fm_b_lsj/N/summary.txt` on claude/cluster):
  - your item-39 sizes: 8/8 seeds pass everything, NEARMISS 0;
  - lsj (UCMPI0 halved to 7): seeds 1-7 pass (latch-data pulses), **seed 8 fails: 18 wrong + 3 hung of 32, slow-carry 23
    wrong + 5 hung**, controller pulses (ulink_n14__1, ulink_n7 ctl, 1-2 ps) around the third call -- the same entry
    race as the cloud's seed 6 (rewrite on). Two of nine routes across both circuits fail with the entry compare halved;
  - lsj_c0 (UCMPI0 kept): 7 seeds pass everything (seed 3 did not build: bench clock), last answer vs yours on the same
    seed: -19.8 / -21.5 / -25.6 / -24.0 / -31.7 / -26.1 / -23.1 % (seeds 1, 2, 4-8). NEARMISS 102-31900 per 32 draws on
    some seeds, every one examined on latch data nodes (ulink_n28__0_folink / ulink_n28__1 / ulink_n26 lat.pair), none
    on a controller.
  So without the rewrite too, the non-compare lines carry the slack and the entry compare does not.
- **To reproduce any row here:** `RS=<your checkout> KERNEL=<k> bash formal/tools-B/auto/coltask.sh SIZES.vh SEED OUT/` from
  a clean checkout of claude/formal (formal/tools-B/auto/README.md: what it runs, what it needs, 20-45 min on 4 cores).
- **The same cut on the other automatic board items** (each at its board seed; the lines linescale found unneeded set to 0,
  the compares and the lines it said need length kept as built; same checks as B8):
  | item | sizes file (formal/tools-B/auto/sizes/) | sdf | draws + slow-carry | long paths | last answer, as built -> cut | NEARMISS |
  |---|---|---|---|---|---|---|
  | 38 ipow s2 | ipow_v3_s2_nc0.vh (USELECT0 23, UMULI1 18, UMUX0-3, USHRSI0 -> 0) | 89987a1c | 32/32 + 32/32 | (B10: slow DSP glitches) | 4.72 -> 3.85 us (-18.5 %) | 0 |
  | 39 collatz s6 | collatz_v3_s6_lsj_c0.vh (above) | 76a0d09d | 32/32 + 32/32 | c32hi, preload, slacks >= 7.4 ns | 31.64 -> 26.12 us (-17.4 %) | latch data only |
  | 40 collatz64 s5 | collatz64_v3_s5_nc0.vh (UADDI1 15, UMUX0-2, USELECT0 -> 0) | 27c5d16f | 32/32 + 32/32 | c64hi, preload, slacks >= 9.8 ns | 100.20 -> 86.94 us (-13.2 %) | 440 in one draw, ulink_n_falseResult_9 latch data |
  | 41 xorshift s8 | xorshift_v3_s8_nc0.vh (UADDI0, UXORI2, UADDIDEC0, UMUX0-3 -> 0) | 8e1a90d4 | 32/32 + 32/32 | preload 8/8, +20 ns control fails only preloaded | 38.49 -> 36.46 us (-5.3 %) | 3 in one draw, latch data |
  More seeds (A/B, yours vs the cut, same seed; all checks as above, NEARMISS 0 on all four routes): collatz64 seed 1
  6333dd2d 101.27 us / 7af7feb2 85.31 us (-15.8 %), seed 2 1e34ade0 104.48 us / d33e28ec 90.51 us (-13.4 %); seed 4 100.00 us / 678659e5 81.32 us (-18.7 %;
  the cut's c64hi / preload NEARMISS 112 / 112, all on ulink_n_falseResult_9 latch data); slacks steps /
  3n+1 >= 16.3 / 8.9 ns on the cut. ipow seeds 1 / 3 in B10. So four seeds each for collatz, collatz64 and ipow (collatz -17..-27 %, collatz64 -13..-19 %, ipow -15..-19 %).
  xorshift A/B (yours / cut; xor19 32 + 32, counter preloaded 8/8, +20 ns control fails only preloaded, counter carry
  slack >= 12.8 ns on both arms): seed 1 48e1223a 37.02 us / e742c6d3 36.10 us (-2.5 %); seed 2 3ad28938 40.68 / dc446a7d
  34.82 (-14.4 %); seed 3 3d908be7 38.71 / 7822c3bc 34.60 (-10.6 %); with seed 8 (-5.3 %) four seeds, NEARMISS <= 81
  (latch data). Board seeds otherwise; xorshift gains least because its period is set by the x datapath ring and its
  compares (B4).
- **Which part of your rule (read in your code and docs, 21:0x; not traced on every route):** the lines formal cut are the
  ones your rule A'j sizes against their OWN request because it gives no join credit there. Your
  research/data/sizerule/joinaware.md (lines 18-23, 200-213) says it: collatz's uaddi1 / ucmpi2 join at ucond_br5 is not
  credited (the siblings meet only through the loop's control merge, more than one crossing back, and the structure
  check rejects acknowledge laps), so UADDI1 is padded to 3 with the flag and 11 without; item 39 ships 12. Then
  ratchet.py (lines 40-50) pins every raise, adds +1 headroom in the raise-only phase, and merge_rules takes the max of
  the two corners, so a raise made on one route is never undone on the next. Rows whose knob is not a sized line are
  padded on the line with the steepest measured slope (corner_audit pad_target), which can be an adder / mux / select
  line on the request leg of a compare race. Formal's data say the uncredited joins are safe to credit on these four
  kernels: UADDI1 at 0 passes everywhere on three collatz seeds and the collatz64 / ipow / xorshift analogues at their
  board seeds. A credit carried through the loop's control merge (the forward-firing argument over more than one
  crossing) is the rule change this points at; the compares themselves have no such slack.
Plainly: in formal's model, item 39's adders, muxes and select lines can go to 0 and its 3n+1 line to half on a rebuilt
route, for about a sixth off the last answer; its entry compare cannot be halved. Which part of your rule sizes those
non-compare lines is yours to find; candidates: sizing each operator to its own datapath without crediting the join
where a slower compare result is awaited anyway.

## B8. Board items 38-41 (the four automatic builds) in formal's simx on their own bits: every draw passes, the counters' and 3n+1's long carries are reached and keep >= 10.9 ns, loop-steer settle >= 1.28 ns with no runts (shard B, 2026-11-18 17:37 UTC; untrusted simulation)
Each rebuilt here from its BOARD-QUEUE command with nextpnr built from bfdeaf7c + all nine patches/ (toolchain.sh 10/10 ok;
binary sha256 b8e99a23, another compile of 6e5d2244's patch set): **sdf md5 identical to yours on all four**, ffmux_scan
exit 0. Formal decodes the bitstream read back by prjxray bit2fasm (not nextpnr's FASM), RC_TREE=1 arcs; your draw K
and your DRAW_CARRY mapping (formal's DRAW_XBAND). Vectors: your gate hex files; full range from formal's vec/.
| item (sdf) | your 32 draws | 32 slow-carry draws (CARRY/F7/FF 0.8-1.0) | full range / preloaded counter | long-carry slack (4 draws) | loop-steer settle, min over 8 corners |
|---|---|---|---|---|---|
| 38 ipow (81bbe268) | ipow17 K 30201-30232: 32/32 | K 30251-30282: 32/32 | e spans 31 bits in ipow17 already; DSP multiply checked on 2007 vectors | - | entry e > 0: 1284 ps at ucond_br4; loop: 3218 ps at ucond_br9; 0 runts |
| 39 collatz (c56def07) | col18 K 30601-30632: 32/32 | K 30651-30682: 32/32 | c32hi 8/8; steps preloaded 0x3ffffff0 8/8 | steps carry into bit 16, last increment: 12382; 3n+1 into bit 28: 10898 | entry n == 1: 3444 at ucond_br3; loop n == 2: 2165 at ucond_br6; 0 runts |
| 40 collatz64 (9585dde4) | c6419 K 30501-30532: 32/32 | K 30551-30582: 32/32 | c64hi (63-bit) 8/8; steps preloaded 8/8 | steps carry: 18046; 3n+1 into bit 56: 13007 | entry n == 1: 4396 at ucond_br2; loop n == 2: 3607 at ucond_br5; 0 runts |
| 41 xorshift (3497ca67) | xor19 K 30801-30832: 32/32 | K 30851-30882: 32/32 | counter preloaded 0x3ffffff0 8/8 | counter carry into bit 16: 12851 | entry 0 < rounds: 2834 at ucond_br5; loop: 1955 at ucond_br6; 0 runts |
- **Negative controls:** each slack is a bisection whose top fails (+X ps on that CARRY4's carry-in; e.g. item 41: +20 ns
  passes ordinary xor19 2/2 and fails the preloaded run 2/2), so each long carry is reached and the check can fail.
- **Settle** = C's steermargin at chains/rest {0.20, 0.31} x CARRY {0.20, 1.0}, no scatter, base vectors (xorshift: xor19 +
  xorlong): the smallest gap between the condition's last move and a request rise at the steer LUT; runts = the
  condition moving while a request is high. Your B7 race (item 41's seed, flow v1: a 21 ps steer pulse from the entry
  compare) is gone on v3's route: 2.8 ns at the same steer class. The audit's T152 reads 483-584 ps at ucond_br4 on item
  38 in its GLS; formal's 1284 ps is another delay model (no scatter, RC arcs); not traced.
- Files: tools in formal/tools-B/auto/ (kdraws.sh, cchecks.sh, fasm_bits.py: bit2fasm writes DSP inverter bits as a vector
  line; split per bit they equal nextpnr's FASM). Decodes are scratch here; one command per item rebuilds them.
- Plainly: on everything formal can simulate, the four automatic items are right with room to spare; none of this is the
  board, and the CARRY / F7 band is still unfitted (PROGRAM "where does the board sit").





## A22. Answer to the auditor's T156: which of pre_dec / pre_eq2 can be a PASS (pattern, side conditions, a proof for every matching program) -- pre_dec only in the corrected form, which is slower; its fast plain form and pre_eq2 cannot be stated that way today (shard A, 2026-11-18 20:53 UTC; Lean where stated)
**pre_dec (the loop test `i + 1 < n` -> `i < n - 1`):**
- *As a pass, proved for every matching program: yes, but only in the corrected form.*
  - Pattern: the imported graph holds the ring `mux sel [ne, nb] -> fork [r0, k]`, with `cond_br cnd r0 -> nb` and its
    false exit sunk, and the compare is the ring's only other reader. The counter is `comp [e] s (addi +1)`, then
    `fork s [s0, s1]`, then `comp [s1, k] c slt`. Fresh channels; nothing else touches the internal ones.
  - Side conditions: none on values.
  - Rewrite: the ring carries `n - 1`, and the test is `slt(i, m) xor (i = INT_MAX) xor (m = INT_MAX)`.
  - Proof: `RingMap.forward/backward` + `IncCmp2.forward2/backward2` + `IncCmpArith.ring_T1_id/ring_T2_id`, plus
    `SplitComp` for bdc's region split. These are any-graph theorems; the matcher is `ring_dec.py`.
  - **This form is 7-68 % slower (A20). So it is a correct general pass that should not be on.**
- *The plain form (`slt(i, n - 1)`, what pre_dec emits):*
  - **Not provable as a pass from the local pattern alone.** It is false for i = INT_MAX, n = 0
    (`IncCmpArith.slt_inc_plain_false`).
  - Its side condition is a loop property: whenever the loop is entered, the counter's entry value is `<s` n. Today
    that is proved only per program:
    - xorshift: A6, by hand;
    - countloop: `Plain.CountloopSame`, generated by `formal/tools-A/rewrite/autoproof_x.py` and checked by Lean.
  - What would make it a pass:
    - EITHER a theorem from the entry guard's shape (the guard `cmpi` steers the counter and the bound together into
      the loop; not written);
    - OR translation validation: the pass applies `ring_dec.py --plain` and runs autoproof_x + Lean on each output.
      That is a per-program proof generated by the flow, not a list. It fails today on horner, quadrec, varshift and
      xorshift, because autoproof's tactics fail on the original kernels too.
  - It pays only on countloop (A21).
- *Checked: the slowdown is not only bdc's region split.* countloop with `BDC_MAX_FUSE_NODES=5`, so the corrected
  test is one region (simcheck suite, all PASS): default original 6.82 / corrected 10.00 / plain 5.55 us; BDC_AUTO
  5.30 / 8.56 / 4.86 us. The correction's depth itself costs more than the add it removes. So the fast general pass
  needs the entry-invariant theorem; no knob makes the corrected form pay. (formal/tools-A/rewrite/fuse5_simcheck.txt)
- *Update, later the same evening: the plain form proved from the GRAPH, not the C.*
  `Formal.Rewrite.Plain.CountloopPlainGen.plain_forward` / `plain_backward` (Lean, standard axioms) cover research's
  countloop fixture and the plain rewrite, every complete run, both directions.
  - The side conditions are graph facts, each checked by `decide` on the program:
    - a branch pair at the loop guard: `n` enters the ring only through a cond_br whose condition is `sgt(n, .)` on
      a fork of the same token;
    - a branch pair at the loop test: the counter's back edge only carries `i + 1` whose test was true;
    - the counter's entry value is a zero-extended bit;
    - every other rule only copies or ignores those channels.
  - The supporting theorems are generic:
    - `ChanInv.chan_inv`: reachable-state channel invariants with branch pairs;
    - `Swap`: two compares that agree on every reachable input have identical runs.
  - So the plain pre_dec CAN be a pass, of the kind "a structural check + a per-program proof generated and checked
    by Lean" (no C, no autoproof). It is instantiated for countloop only so far; formal can write the generator
    if you want it.
  - Tied to the file: `Formal.Rewrite.Plain.CountloopPlainGenTie.tie_forward` / `tie_backward` state the same
    result about dfimport's import of `formal/tools-A/rewrite/out/countloop_plain.mlir` (md5 d562c024). The
    renumbering is checked in Lean, so no script remains in that chain. check.sh OK on the chain.
- *Update 21:24 UTC: the generator exists, and the plain form is proved on all five ring kernels.*
  `formal/tools-A/rewrite/gen_plain_gen.py NAME RS2_EVAL` finds the two branch pairs and the channel classes from
  the graph, and writes `Formal/Rewrite/Plain/<NAME>PlainGen.lean`.
  - The classes come from a backward closure from what the plain test needs: the counter and the bound are never
    INT_MAX, and `n` entering the ring is never INT_MIN.
  - It refuses (exits) if a channel on that closure is produced by anything other than a fork, a mux, a non-pair
    branch, a 1-bit extui, `n - 1`, or a pair's true side.
  - Everything it finds is re-checked in Lean, so a wrong guess fails to compile; it cannot prove a wrong theorem.
  - Proved (`plain_forward` / `plain_backward`, standard axioms) for horner, quadrec, varshift and xorshift, on
    research's fixtures. No per-kernel hand edits: the files are the generator's output.
  - Tied to the files with `<NAME>PlainTie.tie_forward` / `tie_backward`, about dfimport of
    `formal/tools-A/rewrite/out/<k>_plain.mlir`. md5 prefixes: horner c3937812, quadrec 52440267, varshift 281e44fb,
    xorshift ebbe1b96. The tie generator is `gen_plain_tie.py`; it regenerates countloop's tie byte for byte.
  - So the plain pre_dec is now a pass of the kind "structural match (ring_dec.py --plain) + generated per-program
    Lean proof (gen_plain_gen + gen_plain_tie) + Lean check". The side conditions are graph facts checked by
    `decide`, not a C source and not autoproof.
  - It is still not a single theorem for every matching graph. The obligations that make it per-program are
    `PairOK` (two branch pairs) and the per-rule `RuleSafe` check. Both are decidable checks on the rule list, so
    the remaining step to a stated pass is a theorem that the checker's `true` implies them for any rule list.
  - Timing is unchanged: the plain form pays only on countloop (A21).
**pre_eq2 (`n' == 1` -> `n == 2`, n' = the collatz step):**
- The per-token identity is general: `Rewrite.Eq2.collatz_eq2`, for every width w >= 3 and every n. That would be the
  side condition: w >= 3.
- **The graph part does not match today's theorems.** In the imported collatz graph the step is a 3-input region
  (parity, `n >> 1`, and `3n+1` from another region), all derived from n through forks. IncCmp* need a single-input
  update.
- So pre_eq2 is proved only per program (A6: collatz, collatz64), and **cannot be stated as a pass today**. It needs a
  theorem for "a multi-input update whose inputs are all forks of one value" (the same method as IncCmp2, not
  written). Any matcher would also be specific to the collatz step function.
**Bottom line for BDC_AUTO:**
- The hash list (now off by default, behind your `BDC_AUTO_REWRITES=1`, T160) can be replaced by a general pass only
  for the corrected pre_dec, which is slower.
- The rewrites that pay (plain pre_dec on countloop and xorshift, pre_eq2 on collatz and collatz64) are per-program
  proofs.
- If you want them general, the cheapest route is translation validation (autoproof_x in the flow). Formal can make
  that robust if you ask.

## A21. The PLAIN loop-test rewrite: countloop proved equal to your fixture (Lean, every input where the C returns) and FASTER in your simcheck (-19 % default, -8 % BDC_AUTO total time); on horner, quadrec, varshift and xorshift it is timing-neutral and not yet proved (shard A, 2026-11-18 18:53 UTC)
- **What:** `formal/tools-A/rewrite/ring_dec.py --plain` on your fixtures: the ring carries `m = n - 1` (set once on
  entry) and the test is plain `slt(i, m)`, with no correction (A20 showed the correction is the slow part). Outputs are
  in `formal/tools-A/rewrite/out/<k>_plain.mlir`: countloop d562c024, horner c3937812, quadrec 52440267,
  varshift 281e44fb, xorshift ebbe1b96.
- **Proof (countloop only):** `Formal.Rewrite.Plain.CountloopSame.same` (Lean, standard axioms). For every input on
  which countloop.c returns r, the fixture's graph and the plain-rewritten graph each have a complete run ending in
  [r], and every complete run of either, under any schedule, ends there. Both halves were generated by
  `tools-A/rewrite/autoproof_x.py`, an extension of C's autoproof: it adds `v +/- 1` candidates and signed-inequality
  invariants pruned until inductive. It found `m = n - 1` and the invariant `1 <= i <= n` itself. The other four:
  autoproof's Lean tactics fail on the ORIGINAL kernels too (bit operations; a recursion limit), so those files are in
  `formal/lean/Wip/PlainRewrite/` and are not claimed.
- **Timing** (your simcheck, pre-route arc timing, same vectors; total simulated time, original -> plain):

| kernel | default, suite | BDC_AUTO, suite | all 4 runs |
|---|---|---|---|
| countloop | 6.82 -> 5.55 us (-19 %) | 5.30 -> 4.86 us (-8 %) | PASS |
| horner | 9.23 -> 9.24 | 8.51 -> 8.53 | PASS |
| quadrec | 8.59 -> 8.61 | 8.59 -> 8.60 | PASS |
| varshift | 13.42 -> 13.44 | 11.44 -> 11.45 | PASS |
| xorshift | 47.42 -> 47.44 | 38.34 -> 38.36 | PASS |

  The edge-vector runs show the same picture (countloop default 17.48 -> 14.05 us). countloop's critical cycle is
  its counter test; in the other four the loop body sets the cycle, so moving the test changes nothing in this model.
  That is consistent with your automatic table, where countloop is the counted loop furthest behind Dynamatic.
  Raw lines: `formal/tools-A/rewrite/plain_simcheck.txt` (its pass= field counts nothing; the res= field is the
  verdict).
- **lfsrfind (literal-bound tool, inc_cmp.py):** simcheck vec.hex PASS; default 11.07 -> 11.30 us, BDC_AUTO 10.02 ->
  10.01 us: no gain, so not proposed (and not proved: its bound is a control-fired constant).
- **fold64 (A19's widened form, hand-made, not proved):** simcheck vec.hex PASS; default 17.45 -> 17.46 us, BDC_AUTO
  15.50 -> 15.52 us: no gain. Conclusion over all of today's measurements: moving the loop test only pays where the
  counter test IS the critical cycle (countloop); elsewhere the body sets it.
- **To turn it on for countloop:** md5 d562c024 is a proven file in the A6 sense; your PROVEN dict could take it.
  Measure it on routes and draws first; pre-route arc timing is not the board.

## A20. Correction to A19's value: the corrected ring rewrite is CORRECT but SLOWER -- do not turn it on as is (shard A, 2026-11-18 18:44 UTC; your simcheck, pre-route arc timing, untrusted simulation)
formal ran your bdc/simcheck.py --c-oracle on the five A19 kernels, original vs formal's rewritten MLIR (out/<k>_rd.mlir),
default flow and BDC_AUTO=1, suite + edge vectors (n = 0, 1, 2, -1, INT_MIN, INT_MIN+1, 254-256 ...): **40 / 40 PASS**.
But ns per iteration (n = 256 vector), original -> rewritten:

| kernel | default | BDC_AUTO=1 |
|---|---|---|
| countloop | 16.49 -> 25.18 (+53 %) | 12.51 -> 21.07 (+68 %) |
| horner | 21.05 -> 25.18 (+20 %) | 19.29 -> 21.07 (+9 %) |
| quadrec | 21.21 -> 26.71 (+26 %) | 21.20 -> 24.81 (+17 %) |
| varshift | 32.45 -> 32.45 | 27.36 -> 27.36 |
| xorshift | 25.51 -> 27.27 (+7 %) | 20.54 -> 22.35 (+9 %) |

- Likely cause (from the graph, not timed per node): bdc's 4-op fusion limit splits the corrected 5-op test into two
  regions in series, so the loop test that drives the branches gains a handshake stage. Countloop and horner both
  land on exactly 25.18 / 21.07 ns, which fits that chain being the slowest cycle.
- **So:** the A19 proofs stand, but the CORRECTED form costs more than the add it removes. The form that pays is the
  plain one, `slt(i, n - 1)` with no correction terms (your pre_dec on xorshift). It is exact only under the loop's
  entry guard (n > i at entry), which today is proved per kernel (A6) only. formal's next step is that invariant,
  proved generally from the entry guard's shape, so the plain form gets the same any-graph proof. fold64's widened form
  (A19 list) needs no correction at all.
- Same caution for the literal-bound tool (A19): BDC_AUTO was slightly slower there too (test_bitint, dot2).
- Caveats: pre-route simulation with bdc's arc timing, one run per kernel, not routes or draws. Under simcheck,
  BDC_AUTO does not run auto.rewrite_mlir, so no pre_dec. Every command is in formal/tools-A/rewrite/ring_simcheck.txt.

## A19. The loop-test rewrite, made general: moving a test before its increment is proved for ANY graph containing the pattern (Lean, every input, both directions); the ring shape needs one extra LUT of correction, or a per-kernel invariant; applied end to end to countloop (shard A, 2026-11-18 17:35 UTC; Lean, standard axioms; token level)
Your `bdc/auto.py` turns on pre_dec / pre_eq2 only where the output md5 is one of A6's proven files, so it fires on
xorshift, collatz and collatz64 only. These results replace the per-kernel proof with a per-pattern one:
- **The literal-bound test** (`ult (addi (extui x) k), C`, 117 of the 166 loop tests in the 108 frontend fixtures,
  mostly memory kernels): `cmpi ult, (extui x), C - k` is exact for every input if `2^sw + k <= 2^w` and
  `k <= C mod 2^w`. `Formal.Rewrite.IncCmp.forward` / `backward` (IncCmpGraph.lean) + `ult_lit_E` (IncCmpArith.lean).
- **A bound that is a channel** (the ring value n: countloop, horner, brhash, xorshift, fill, if_loop_*, nested...;
  or a constant fired by a control token: lfsrfind): `forward2` / `backward2` (IncCmp2.lean). The compare's identity
  must hold for every value of the second input.
- **The ring itself** (n -> m = n - 1, computed once on the ring's entry; the compare precomposed): `RingMap.forward`
  / `backward` (RingMap.lean). The ring must be mux -> fork(two outputs) -> cond_br -> back, with the false exit sunk
  and the compare its only other reader.
- **The arithmetic** (IncCmpArith.lean): `slt(i + 1, n) = slt(i, n - 1) xor (i = INT_MAX) xor (n - 1 = INT_MAX)` for
  every 32-bit i and n. **Without the two correction terms the plain form `slt(i, n - 1)` is false** (i = INT_MAX,
  n = 0: `slt_inc_plain_false`). pre_dec's plain form is right for xorshift only because of xorshift's own loop
  invariant (A6); a general pass either emits the corrections (`i == INT_MAX` and `m == INT_MAX` are 32-input ANDs
  computed in parallel with the compare, then one XOR3 LUT after it) or needs that invariant proved per kernel.
- **Applied:** `CountloopRewrite.same_forward` / `same_backward`: your countloop fixture (md5 edcfff62), imported by
  dfimport, then both rewrites; every pattern hypothesis discharged by `decide +kernel`; every complete run of the
  original is matched by one of the rewritten graph with the same output token, and vice versa.
- **Meaning:** same terminal store (outputs) for every input and every schedule; both terminate on the same inputs.
  Token level: no gates, delays, sizes. What it does NOT cover yet: that a rewrite pass's MLIR output imports to the
  graph the theorem talks about (needs a tool plus a per-kernel structural check, in progress here); `sle` / `sgt` /
  negative steps (factorial, insertion_sort); the 45 tests of other shapes.
- **countloop, as an MLIR file (added 17:45 UTC):** `formal/tools-A/rewrite/out/countloop_rd.mlir` (first version md5 0d43ba36, superseded by the tool output below; made
  from your fixture edcfff62 by hand: decrement on the ring entry, test moved before the increment, the corrected test
  as `cmpi slt` / two `cmpi eq` / two `xori`). bdc's fusion limit (4 ops) splits that 5-op test into two regions, so a
  fourth theorem was needed: `SplitComp.split_forward` / `split_backward` (a two-input region split in two, any graph).
  `CountloopRewrite.same3_forward` / `same3_backward` chain all three to `rs3`; dfimport's import of countloop_rd.mlir
  is the same graph as `rs3` up to channel numbering and rule order (`formal/tools-A/rewrite/rules_iso.py`: ISOMORPHIC,
  45 rules, 71 channels; the original fixture against it: NOT MATCHED, the negative control). That last step is a
  script, not Lean (graph semantics under renaming is not proved). With it, the file is one BDC_AUTO could
  accept the way it accepts A6's files. Not simulated or built here; timing unmeasured.
- **Now a tool, and five of your automatic-path kernels (17:51 UTC):** `formal/tools-A/rewrite/ring_dec.py IN OUT`
  does the ring rewrite on any MLIR where the exact shape matches (refusing, with the reason, everywhere else). It
  rewrites 18 of the 108 fixtures. `gen_ring.py KERNEL NAME` writes a per-kernel Lean proof
  (`formal/lean/Formal/Rewrite/Ring/<Name>.lean`, `same3_forward` / `same3_backward`, every hypothesis by
  `decide +kernel`) and checks that the import of ring_dec's output is that graph (rules_iso.py, untrusted). Results:

  | kernel | rewritten MLIR (formal/tools-A/rewrite/out/) | md5 | Lean (compiled, axioms) | import vs rs3 |
  |---|---|---|---|---|
  | countloop | countloop_rd.mlir | 6ecca11f | OK, propext / Classical.choice / Quot.sound | ISOMORPHIC (45 rules) |
  | horner | horner_rd.mlir | 856aee38 | OK, same | ISOMORPHIC (45 rules) |
  | quadrec | quadrec_rd.mlir | ac3dbd02 | OK, same | ISOMORPHIC (68 rules) |
  | varshift | varshift_rd.mlir | 445f1ea1 | OK, same | ISOMORPHIC (56 rules) |
  | xorshift | xorshift_rd.mlir | 37c81058 | OK, same | ISOMORPHIC (39 rules) |

  Each one: every input, every schedule, the same output token and the same termination as your fixture. None of these
  rewritten files has been built, simulated or timed here. Whether the extra LUT costs more than the add it removes
  from the test is yours to measure. brhash, nested, nest3, if_loop_3 and insertion_sort are refused: their ring shape
  differs.
- **No script left in the chain (later the same evening):** `Ring/<K>Tie.lean` (`tie_forward` / `tie_backward`) state the
  result directly about dfimport's import of each `out/<k>_rd.mlir` above, the renumbering checked in Lean
  (`Rename.lean`). Five kernels compiled, standard axioms. What is trusted: that dfimport (bdc's own parser and fusion
  plan) is what the MLIR means, and the token-level model.
- **Literal-bound tool (18:23 UTC):** `formal/tools-A/rewrite/inc_cmp.py IN OUT --log L` (119 rewrites in 53
  fixtures). Proved in Lean only for a bound fired by a `source` (117 cases, IncCmpGraph + ult_lit_E; per-kernel import
  not checked, dfimport refuses most memory kernels). lfsrfind's and covariance's control-fired bounds are changed in
  place and are covered by simulation only (simcheck --c-oracle 10/10 + 14/14 edge vectors for lfsrfind). In formal's
  pre-route RTL runs BDC_AUTO was slightly slower WITH this rewrite (test_bitint 2.31 vs 2.07 us, dot2 8.54 vs 8.19 us),
  so measure before turning it on. Details: formal/tools-A/rewrite/inc_cmp_diffcheck.txt.
- **Still off, and what each would need (18:40 UTC):**
  - *fold64* (automatic path): `ult9(ext(i) + 1, ext(n))`, with n an i8 on a ring and the loop entered only when
    n > 0. A cheaper exact form exists: the ring carries a 9-bit `m = ext(n) - 1`, and the test is `slt9(ext(i), m)`.
    It needs no correction term, because n = 0 gives m = -1 and slt is then false, as the original is. It needs a
    RingMap variant with the `extui` between the ring fork and the compare (not written).
  - *lfsrfind, covariance* (bound = a constant fired by a control token): the tool changes the literal in place. A
    proof needs a "constant channel" lemma (every token on it is C), plus IncCmp2 with its identity required only at
    w = C. Today these two are simulation-only.
  - *countdowns* `sgt(i - k, C)` (factorial, triangular, insertion_sort, test_memory_2/4/10): the same method with
    `sgt` identities (not written).
  - *rings of another shape*, refused by ring_dec.py: brhash, nested, nest3, if_loop_3, insertion_sort.
  - *sqrtsub* (2.53x): the test is data-dependent (`n - odd < odd + 2`), not a counted loop. That is a different
    rewrite (compare against `2*odd + 2` computed from the loop-start values), with its own wrap conditions.
- **What you would need to turn it on in BDC_AUTO:** a pass that matches the two shapes structurally (formal is
  writing `formal/tools-A/rewrite/inc_cmp.py` for the literal case) and an md5-free acceptance rule: "the pass's
  matcher checked the pattern hypotheses of IncCmpGraph / IncCmp2 / RingMap". Timing value is yours to measure: the
  test no longer waits for the 32-bit add; the ring form adds one LUT after the compare.


## C58. A static rule that catches the re-entry deadlock: your condition 2 in the "inner loop passed through in one trip" mode your walk leaves out -- 183 / 183 agreement with formal's exhaustive checker, matrix and stencil_2d default flagged, nothing else (shard C, 2026-11-18 18:17 UTC; untrusted prototype, formal/tools/live/reentry/reentry.py; the agreement is with live.py, not a proof)
- **The fork-join pair at matrix's deadlock:** fork = the inner header control_merge2 (result and index leave together). P: index ->
  fork11 -> n49__5 (1 stage) -> mux5's select. Q: result -> the inner loop's EXIT steer (cond_br10 false) -> control_merge3 ->
  fork22 -> cond_br15 continue -> trueResult_35 (the middle loop's back edge, 0 stages, 1 token) -> control_merge1 -> fork5 ->
  constant5 -> fork6 -> extui9 -> n26 (1 stage) -> mux5's ENTRY data input. Join = mux5. Q carries K = 1 token more than P, so it
  needs >= 2 stages between fork and join (your condition 2); it has 1. stencil_2d: the same with n45. test_flatten_array: the same
  shape, but its n28 already has 2 stages (ring_depths) -- live, as live.py says. This also explains every fix and non-fix in C57:
  n26 / n45 / the cm1 olink add a stage or turn on Q; n32 is before the fork, n49__5 on P, n35 / n54 after the join.
- **The view** (reentry.py, research's token_graph patched in memory, nothing of yours edited): for each loop L, a "pass-through"
  view: L's back-edge inputs dropped, its entry inputs walked with no token, the steers on L's condition walk their EXIT branch and
  drop the continue branch; every other loop as in your view. Mux back edges classified by C57's rule (by the control_merge index),
  not by bb numbers. Flag (exit 1) if any view is short.
- **Agreement with live.py (exhaustive unless noted):** floor on, every non-refused fixture x {default, AUTO}: 90 / 90 (flagged:
  matrix default, stencil_2d default -- both DEADLOCK; gcd AUTO, nest3 only sampled); fixes / non-fixes from C57: 8 / 8; formal's
  34 validation configurations: 34 / 34 (the 19 deadlocks flagged, by the iterating view); floor off: 51 / 51. Reproduced here:
  matrix / stencil_2d rc 1, test_flatten_array / gcd / quadrec / nested rc 0, matrix + ulink_n26=2 rc 0, matrix AUTO rc 0.
- **Proposed for bdc:** run token_floor over these pass-through views too (add a stage on Q -- the entry data input -- as it does
  for the iterating view). **Limits:** only matrix and stencil_2d exercise the new view (about 9 of 45 emitting fixtures have more
  than one loop); the view stands in for the marking at re-entry after many trips -- that the counts match is shown only by these
  results; it may over-ask like your view can; inherits live.py's model limits (MODEL.md).

## C57. The matrix / stencil_2d deadlock (C55): your token_graph counts the inner header mux's ENTRY input as a back edge (Dynamatic put its producer in the header's basic block); fixing that alone does not expose the deadlock, which lives in the loop-RE-ENTRY mode no view models; one more stage on that entry input fixes it in the model (shard C, 2026-11-18 18:08 UTC; untrusted, formal/tools/live/entrywalk.py + live.py)
- **Misclassification (your code, read-only here):** `token_graph` marks a mux data input as a back edge when its producer's
  handshake.bb >= the mux's. matrix `%26 = extui9` (bb 3) feeds mux5 operand 1 = the input selected by control_merge2's index 0 =
  control_merge2's ENTRY input `%32 = br16`; token_graph prints it as `n26 extui -> umux5 op 1, stages 1, tok 1` while it skips
  `%32` as entry -- the same loop entered through two inputs classified two ways. Same in stencil_2d (`n45 = extui8 -> umux4`) and,
  reclassified the same way by the rule below, n10 -> umux1 (matrix), n11 -> umux1 (stencil_2d), n10 -> umux1 and n28 -> umux5
  (test_flatten_array). Rule used in the prototype: a mux data input k >= 1 is a back edge iff the control_merge whose index drives
  the select (through forks / pass-throughs) has a back edge at input k - 1.
- **With that fixed, your iterating-mode walk view is still clean on matrix and stencil_2d** (and on test_flatten_array, quadrec,
  nested, gcd): the deadlock is not in the iterating mode. live.py's trace (C55): inner loop leaves, middle loop iterates, inner
  loop re-entered -> stuck. A naive "entering" view per header bb (that header's entry inputs walked with the token, its back edges
  dropped) misses both deadlocks AND falsely flags test_flatten_array (bb1) and gcd (bb11), which live.py proves live: so not that.
- **What fixes it in the model, exhaustively:** one more stage on the entry data input -- matrix `BDC_LINK_DEPTHS=ulink_n26=2`
  LIVE (19 246 states), stencil_2d `ulink_n45=2` LIVE (20 076); a stage on any other channel of the token-free walk (matrix n32 ->
  4, n49__5 -> 2, n35 -> 2; stencil n54 -> 2) still DEADLOCKs; the header olink on ucontrol_merge1 (C55) also fixes both.
  Predictions for your simcheck, default flow.
- **Suggestion:** until the re-entry mode has a rule, use live.py as the oracle in the floor's loop (it prints the token-free
  walk at the deadlock; adding a stage on the entry data input that walk crosses is what worked on both), or run it as a gate.

## C56. Three handshake races that are not speed independent, found by exhaustive search on the real cell LUTs: the control_merge index (A2 still high when the next entry token wins), FASTFALL's head buffer, and bd_mux's x_ack at a select change -- each a timing obligation with a large but unstated margin; plus bd_ctree 5/6, bdc_muxn 3 and FASTFALL agree with the stage model (shard C, 2026-11-18 18:05 UTC; untrusted exhaustive search, formal/tools/live/cells/)
Gate-level speed-independent search from the verbatim INITs, with a four-phase protocol monitor and a select / index stability
monitor (formal/tools/live/cells/run.sh; RESULTS.md, RESULTS2.md, muxglitch.txt):
- **control_merge index (bdc_amerge2, a real loop header with an entry reservoir of k tokens).** k = 1: fixed and free mode (enter,
  iterate, exit) clean: 0 protocol / bundling violations, every stuck state predicted by the stage model. **k = 2 (an entry
  request really competing with the back edge):** after a back-edge handshake A0 falls, but A2 = C(g2, A0) has not fallen yet; if
  in0 then wins, q and R0 rise while the index reads won[1] = g2 | A2 = 1 -- "back edge" for an entry token -- and moves when A2
  falls, mid-handshake (2352 index-moved, 1036 mux-z, 36 ctl-ack violations in the reported loop). So DELAY_<cm> must also cover
  A2's (A1's) fall after A0 falls; emit's comment on `won` argues only the hold side. Margin ~1 LUT against arbiter LUT + uor +
  DELAY: large, but it is an obligation. (This is the same assumption formal's fixture checker needed in C55.) Loops reach only one
  entry token at a time in today's kernels (one invocation in flight), so k = 2 needs the pipelined environment.
- **FASTFALL delay line, DELAY >= 2:** the head buffer rdly1 is still falling when the link's c rises again (trace `L0- L0.rdly2-
  L2+ L1- L2.rdly1+ L2.rdly2+`, then L0+ disables L0.rdly1-): your rule F's "the line must drain first". Liveness unaffected.
- **bd_mux x_ack at a select change** (C53): in the speed-independent model only a LATE fall (0 lost / duplicated tokens, with the
  fall disabled or completed). If it becomes a real runt (x_ack dips, the producer offers its next token, x_ack recovers to 1 via
  C(j0 = 0, z_ack = 1)), the producer takes it as the acknowledge and withdraws a token the mux never joined: **a lost token**.
  Obligation: x_ack's fall (one LUT) beats the select change plus the next y handshake raising z_ack.
- **Agree with the stage model, 0 hazards, 0 violations:** bd_ctree 5 and 6 (fork-join, 1140 starts), bdc_muxn N = 3 at each select
  (3 x 3150), FASTFALL DELAY = 1 and = 2 (deadlocks; DELAY = 2 rings show the hazard above). A bd_merge (unarbitrated) header,
  which emit never builds, misroutes tokens with ONE token: a control, not a finding.
- **Not covered:** real timing and the arbiter's time to decide, data through link latches, bdc_amerge N > 2, more than one loop,
  bdc_muxn free mode, 9 of 32 k = 2 configurations (state cap).

## C55. matrix (default flow) deadlocks in formal's exhaustive model and your token floor does not see it: your walk view says "every walk holds a token", your cycle view says -2; the deadlock needs a loop to be LEFT and the enclosing loop's back edge taken (a mode change, which the walk view excludes). One merge out-link on ucontrol_merge1 makes it live in the model; BDC_AUTO matrix is live (shard C, 2026-11-18 17:41 UTC; untrusted exhaustive search, formal/tools/live/fixtures/live.py)
- **The checker** (independent of token_graph / short_walk / ring_tokens; reads only the Emitter's design: links and depths, olinks,
  rlinks, fork-out links, fusion, memory stations, store / end joins): exhaustive state search of every state-holding element of
  the emitted cells (Muller stages, fork / join / compute / mux / cond_br C-elements, the arbiter's q from bd_arb.v's INITs, memory
  stations and memport), conditions as nondeterministic bits copied by forks, one invocation; finite state space, so LIVE means
  for EVERY trip count including 0 / 1, entering and leaving loops. It reproduces your 34 validation rows so far (30 run, 30 agree,
  every negative control deadlocks; nest3's olink / rlink rows only sampled -- state budget).
- **matrix, emitted from cloud/fixtures/frontend/matrix at 7197d85c2:** default flow (floor on; the floor adds nothing):
  **DEADLOCK** after 853 states, choices `ucmpi0 = 0` (innermost loop leaves) then `ucmpi1 = 1` (middle loop's back edge);
  token-free closed walk at the deadlock through ulink_n26[0], ulink_n32[2], ulink_n49__5[0], ulink_n35[0]. With the real trip
  counts (every compare 29 x true then false, i.e. 30 trips) it also deadlocks, at the first re-entry of the inner loop. So this is
  your default-flow hang. `ring_tokens.py` on the same design: cycle view "worst cycle -2 (short)", walk view "every walk holds a
  token" -- the floor follows the walk view, which leaves out loop entry / exit channels, and this cycle runs through them.
- **What fixes it in the model** (BDC_MERGE_OUT_LINK on the default flow, exhaustive): all five control_merges LIVE (40 873
  states); **ucontrol_merge1 alone LIVE** (17 900); merge0, merge2, merge3 or merge4 alone still DEADLOCK. BDC_AUTO=1 (which puts
  olinks on the headers): **LIVE**, 56 577 states. Prediction for your simcheck: default flow + `BDC_MERGE_OUT_LINK=ucontrol_merge1`
  completes.
- **Suggested change to the floor:** count the walks that cross a loop's exit channel into the enclosing loop's back edge (the
  "inner loop left, outer iterates" mode), or at least fail when the cycle view is short and the walk view is not -- matrix is a
  fixture where the two views disagree and the cycle view is the right one.
- **One timing assumption the zero-delay search needed** (a bundled-data obligation you may want named): the arbitrated merge's
  output request (R0, behind its matched delay) must not rise before the previous winner's acknowledge has fallen, or the
  control_merge index can be read stale; without it gcd "deadlocks" in the zero-delay model through a stale index.
- **Update 17:45 -- a second fixture, and where your two views stand on all 108:** `formal/tools/live/views.tsv` = your
  ring_tokens.py, both views, every fixture x {default, AUTO} x floor {on, off} (432 rows; refused ones marked). With the floor ON
  only three fixtures are flagged by either view, all by the cycle view alone: matrix (default), **stencil_2d (default)** and
  test_flatten_array (both flows). formal's exhaustive search on each: **stencil_2d default DEADLOCK** (901 states, `ucmpi0 = 0`
  then `ucmpi1 = 1` -- the same shape as matrix; token-free walk through ulink_n45[0], ulink_n51[2], ulink_n67__2[0],
  ulink_n54[0]); stencil_2d AUTO LIVE (59 318); default + `BDC_MERGE_OUT_LINK=ucontrol_merge1` LIVE (18 476), any other single
  control_merge still DEADLOCK. **test_flatten_array LIVE in both flows** (19 246 / 56 913) although the cycle view is short: so
  "fail whenever the cycle view is short" would over-ask there; the condition you want is the walk view extended to the "inner
  loop left, enclosing loop iterates" mode, not the cycle view. With the floor OFF the walk view alone flags lfsrfind / nest3 /
  nested and both views quadrec, as in your ringfloor.md.
- **Which mode it is (matrix, read off the walk):** ulink_n26 = `%26 = extui9`, mux5's ENTRY data input (bb3); ulink_n32 (3
  stages) = `%32 = br16`, control_merge2's ENTRY input; ulink_n49__5 = mux5's select `%49#5`, from control_merge2's index; n35 =
  extui10 -> addi0. So the token-free walk runs through the inner loop's entry channels while it is being RE-ENTERED (the middle
  loop's next iteration): the "loop being entered" mode, where a header's entry inputs play the part of its back edges. Your walk
  graph drops every entry channel ("never walks a loop's entry channels"), so it cannot see this mode at all. A cheap fix to try:
  a second walk graph per loop with that loop's entry channels in and its back edges out (the entering mode), checked the same way.
- **To run the checker yourself** (single file, standard library only, imports your bdc): `git show
  origin/claude/formal:formal/tools/live/fixtures/live.py > /tmp/live.py; LIVE_BDC_DIR=$PWD/bdc [BDC_AUTO=1 ...] python3 -B
  /tmp/live.py build/frontend/K/comp/handshake_transformed.mlir` prints one JSON line (verdict LIVE / DEADLOCK / SAMPLED-LIVE,
  states, trace choices, the token-free walk at the deadlock). Seconds on the suite kernels; semantics in MODEL.md next to it.
- **Sweep finished (18:36; formal/tools/live/fixtures/RESULTS.md, results.jsonl):** 648 rows (108 fixtures x default / AUTO / AUTO
  after auto.py's rewrites x floor on / off). Floor ON, fixtures that FAIL: **matrix (default) and stencil_2d (default)**, nothing
  else; the only disagreements with your walk view are those two (both floors). Everything else that emits is LIVE-exhaustive,
  except gcd AUTO and nest3 (both flows) which exceeded the 1.2M state budget (rerun at 6M, 18:59: gcd AUTO LIVE 2.0M states,
  nest3 default LIVE 2.7M states, both exhaustive; nest3 AUTO still only sampled); isprime's two-invocation run
  timed out (one invocation LIVE). Floor off: quadrec (both flows), nested / nest3 / lfsrfind (default) deadlock, as your
  ringfloor.md says. 232 rows refused by bdc, 20 crash in bdc's own memory check (matvec, test_constant_array,
  test_internal_array, test_unroll, trisolv) -- your refusals, not formal's.
- **Status of the sweep, as written at 17:41** (every fixture x {default, AUTO} x floor on / off, plus your ring_tokens verdict per row): 122 rows done
  (branchloop .. gcd), all non-refused designs LIVE-exhaustive and agreeing with your walk view; the rest is running and will be
  added here. Formal's Lean results (C53) are for a fixed mode; this deadlock is a mode-change one, so it is outside them: at the
  real-trip deadlock the stage projection has no token-free cycle (two steers never got a condition).

## C54. Farm results left unread at the 03:00 stop: cand3b (x55a10) 256 / 256 draws on 32 routes, steer >= 404 ps at slow CARRY; collatz / ipow x0.70 with every non-compare matched delay at 0.5x pass 248 / 248 draws on 31 routes, -12 % / -18 % last answer (shard C, 2026-11-18 17:17 UTC; untrusted simulation, formal's simx, RC-tree arcs)
- **fm_c_c41x32** (your cand3b: item 35's sizes with UCMPI0 10, seeds 1-32, formal's decode of each route): 4 default draws (K =
  100S+1..4) + 4 slow-carry draws (K = 100S+51..54, CARRY4 / F7F8 / FF in [0.8, 1.0]) per route: **256 / 256 PASS**. Steer settle
  margin (C36's method, chains 0.20 / rest 0.31 and 0.20 / CARRY 1.0, both compares): worst **404 ps** (route 18, then 462 route
  14, 514 route 26), no runts on any route. Adds 32 routes to C41 / C49.
- **fm_c_half16** (collatz x0.70 seeds 1-16, ipow x0.70 seeds 1-16; 8 draws plain and 8 with every non-compare chain at 0.5x via
  DRAW_INJECT, same K): collatz 16 / 16 routes 8/8 + 8/8; ipow 15 / 15 routes 8/8 + 8/8 (seed 14's task lost its routed.json: no
  result). Mean last-answer change at 0.5x: collatz **-12.2 %** (-14.1 to -8.8), ipow **-18.5 %** (-19.8 to -16.2). Extends C51 /
  C52 from 2-4 routes to 31: on these two kernels the non-compare matched delays are not what keeps answers right; the compares
  are (chainscale per route: the compare chains are the ones with s_min > 0, ucmpi2 up to 0.62).
- Files: `git show origin/claude/cluster:results/fm_c_c41x32/N/{draws_summary_*.txt,steer.txt}`, `results/fm_c_half16/N/`.

## C53. Liveness: your token-floor condition is exactly right for the stage model, proved in Lean -- a network of half-buffer stages with the routing fixed can only lose a stage forever through a cycle of the marked graph that holds no token, and with none, no reachable state deadlocks and every stage fires infinitely often in fair runs (shard C, 2026-11-18 17:09 UTC; Lean, core only; per-fixture results to follow in this item)
Your ringfloor.md "Derivation" argued it; `formal/lean/Formal/Net/StageNet.lean` proves it, for any finite network:
- **Model** (yours): stage t excited iff every stage feeding it (through joins / forks / a mux select join / a steer routed one
  way) differs from it and every stage it feeds equals it; one fires at a time, any order. For a stage with one feeder and one
  consumer this is exactly the bd_c2n LUT in run mode (`StageNetRing.excited_single`, from the verbatim INIT).
- **Proved:** a *trap* (a nonempty set of stages each with a token-free arc into it from the set) exists iff some closed walk
  of token-free arcs exists (`trap_of_cycle`, `cycle_of_trap`) -- your "closed walk, forward along some channels and backward
  along others, that holds no token". A trap is invariant under every firing, both ways (`trap_step_iff`); every stage in it is
  never excited again (`trap_dead`); without one, no reachable state is a deadlock (`deadlock_free`) and every weakly fair
  infinite run fires every stage infinitely often (`fair_all_fire`). So "no short walk" is necessary AND sufficient in a fixed
  mode -- not only for the iterating loop you checked, for any fixed routing.
- **Certificates:** `StageNetCert.Cert.check` (edge list, state, a rank that rises along every token-free arc) is decidable and
  sound; formal/tools/live/gencert.py makes one per exported stage graph, so a fixture's verdict can be kernel-checked rather
  than trusted.
- **Update 17:22 -- the C-element circuit, not only the stage abstraction:** `StageNetTree.tree_deadlock_free` and
  `StageNetTreeFair.tree_fair_all_fire`: stage controllers C(req, not ack) with ANY acyclic network of C-elements and buffers
  between them (matched delay lines, bd_ctree joins, fork acknowledge trees), under a wiring condition WF and an invariant Inv
  that holds at the all-zero reset: no trap in the stage bits => no reachable deadlock, and every weakly fair run fires every
  stage infinitely often. So your "joins and forks add arcs, not tokens" is now a theorem for C-element joins / forks.
- **Exhaustive check on the real LUTs** (`formal/tools/live/cells/`, run.sh, ~40 s): gate-level speed-independent BFS from the
  verbatim INITs (bd_c2n links, bd_c2 / bd_c3, bd_mux uj0 / uj1 / uor / uxa / uya, cond_br = bd_join + bd_steer as emit builds
  it), every stage vector as a start, up to 11 stages. Fixed routing, consistent internal state: **0 disagreements** between gate
  and stage model on 45 516 starts (rings, fork-join, fork-mux, fork-cond_br, 3-way, with buffers); your arithmetic (S >= 2T+1,
  L_Q >= 2K) and the token-free-cycle test predict the deadlock exactly on every rest marking.
- **Two things for you from that check:** (1) **bd_mux is not speed independent where its select changes** (the loop-header mux
  going from entry to first iteration): after an x handshake, x_ack = C(j0, z_ack) is due to fall once z_ack has fallen; if the
  select changes then and the next y handshake raises z_ack first, x_ack's fall is disabled and it falls one handshake late
  (trace in cells/RESULTS.md, "free mode"). It is a race of one LUT against a round trip through the loop, so it is safe in
  practice if that round trip is longer; no timing rule of yours names it that we know of. (2) A token placed by a _set link
  next to a join or fork whose C-element comes up 0 is NOT the same marking (the C-element disagrees with it): emit does not do
  this today; if a hand-placed token ever is, its join / fork needs the set variant too.
- **Kernel-checked per fixture (19:50):** `Formal/Net/LiveCerts.lean`, 189 certificates, one per routing mode reached by
  live.py on every emitting fixture (floor on, both flows): no token-free cycle in each. The export itself is untrusted.
- **Still not covered:** mode changes (entering / leaving a loop, a one-trip inner loop), the arbitrated merge / control_merge,
  the steer and select AND gates outside a fixed mode, FASTFALL's AND, data and timing. The independent per-fixture check
  (including mode changes by bounded exhaustive search) is still running; results will be added here.

## B7. Your rule's NOT CLEAN on AUTO xorshift seed 3 (ea3c2aad) is real in formal's draws: slow-carry draw 5104 returns a wrong answer through the flagged entry-compare race (UCMPI0 6); the draws suite_one would run (4 default) pass (shard B, 2026-11-18 02:00 UTC; untrusted simulation)
Same bits as B6 (formal's decode of ea3c2aad, RC_TREE=1). Your ca_4.txt for this route already says VIOLATION at ucond_br5 /
ucond_br3 (rule D, -3.3 ns) and ucmpi0 (rule a, -1029 ps), "raised UCMPI0 6->7": the loop stopped at MAXIT 4 before that
route was built, and suite_one.sh sends the last route (NOT CLEAN) to the draws.
- **Draws:** your K 2101-2104 (default bands) 4/4 PASS. Slow-carry draws (DRAW_XBAND=0.8,1.0, K 5101-5116; xor19 + xorlong):
  15/16; **K 5104 FAILS**: xorshift(0x2468ace0, 0) (xor19's last vector, zero trips) returns 0x92d78cb6. Reproduced on
  xor19 alone. Same draw with CARRY/F7 moved down: 0.9965 / 0.990 FAIL, 0.980 / 0.970 / 0.950 PASS. Draw 5104's bands:
  chains 0.259, rest 0.287, CARRY 0.997 -- inside your default model (CARRY U[0.2, 1.0]); P(CARRY >= 0.985) ~ 2 % a draw,
  times whatever share of its scatter does this.
- **The race (simx dumps, fail at 0.990 vs pass at 0.980, same draw):** first call, (0x92d68ca2, 0), zero trips. At the
  data steer ucond_br3's LUT (SLICE_X24Y52 ALUT, INIT 0x00aa00aa) the request pin rises at 1002264 ps while the
  condition pin (ucmpi0.uz_n3, the compare `0 < rounds`) is still in a carry-chain glitch: up at 1002075, down at 1002413,
  i.e. the condition moves 149 ps AFTER the request. The steer output then pulses for 21 ps (16 ps at 0.980, removed by
  H_RUNT(20)); the 21 ps pulse enters ulink_n_falseResult_1 stage 0's controller (SLICE_X22Y52 ALUT, reads its own
  output), which oscillates (21 ps high every ~295 ps, from 1003109 ps on) and its 32 latch bits with it; the call's
  answer is still right, the last zero-trip call reads the corrupted link. Without scatter, at the same bands, steermargin
  gives ucond_br3 175 ps and ucond_br5 141 ps; at chains 0.20 / rest 0.31 / CARRY 1.0, 63 and 27 ps (no runts).
- **What depends on the model:** the 21 ps pulse is 1 ps over formal's runt filter, and an oscillating controller is how
  simx (transport, no resolver) treats it; your gate's resolver rejects 20-40 ps pulses into a C-element (your C19
  answer), so your gate may pass K 5104. The race itself -- the entry compare still glitching when its steers' requests
  arrive -- is in the arrival times, not in the pulse model, and it is the one your rule flags. Same class as item 35's
  UCMPI0 (C36 / C41 / C48).
- **Other routes:** formal's seed 1 (694d657d, UCMPI0 7): ucond_br2 / ucond_br3 keep 602 / 689 ps at chains 0.20 /
  CARRY 1.0; collatz64 s5 (84cbd5fa): ucmpi0 / ucmpi2 steers >= 1020 ps. Your suite1 xorshift seeds and their final
  UCMPI0: s1 7, s2 8, s3 6, s6 9, s7 7, s8 5 -- seed 8 has the smallest.
- So: a NOT CLEAN route that reaches the draws can carry the very race the rule names, and 4 default draws do not see it.
  Either let the loop run until clean (MAXIT) or add slow-carry draws to suite_one for NOT CLEAN routes. Yours to choose.

## B6. Your AUTO xorshift routes' "NOT EQUIVALENT" (suite1 seeds 3 and 7) looks like a false positive of fasm_equiv: the one hard difference is a packer GND LUT whose value is 0 on both sides; formal's decode of seed 3's bits returns right answers, preloaded counter included (shard B, 2026-11-18 01:2x UTC; untrusted simulation + reading of your equiv.txt)
**Your suite1 tasks 3 and 7** (xorshift, BDC_AUTO=1, seeds 3 / 7, it 4, sdf ea3c2aad / 302ff749) report `bits=NOT-EQUIVALENT`,
so suite_one.sh calls them NOT-A-BOARD-ROUTE and runs no draws. Rebuilt here from your sizes_4.vh with your lane2.sh
(seed 3: sdf ea3c2aad, byte-identical; same verdict). `r/rs_xorshift_3_4/fid/equiv.txt`, the one hard difference:

    DRIVER DIFFERS  SLICE_X17Y65/F7BMUX/1  json ('bel', 'SLICE_X17Y65/C6LUT', 'O6')  bits ('const', 0)
    HARMLESS        SLICE_X17Y65/C/A1 json 0 bits 1 (the bits' LUT function does not read that pin)

In the routed JSON that C6LUT is `$PACKER_GND_NET$LUT$66`, INIT 0b10 (O6 = A1), and A1 is on `$PACKER_GND_NET` (driver
PSEUDO_GND): nextpnr's own value is 0. The bits: the same LUT with INIT 0 (formal's decoder agrees: SLICE_X17Y65.CLUT.O6
init 0 into F7B), i.e. constant 0. Same value. nextpnr left that A1 unrouted (the IMUX then reads VCC) and wrote the LUT's
INIT already folded to the constant, which is the safe way round. fasm_equiv folds a constant LUT on the BITS side
("compared as that constant") but not a LUT whose only read pin is tied to a constant on the JSON side, so it sees
"bel vs const". Every AUTO route here has 160-211 such packer GND LUTs into F7 muxes (hand routes have them too); only
ones whose A1 nextpnr leaves unrouted should show up like this.
**Formal's simx on seed 3's bits** (formal's own decode of the FASM, RC_TREE=1 arcs, your draw K): xor19 4/4 draws
(K 2101-2104) PASS; loop counter preloaded at 0x3ffffff0 (B2's set A) 8/8 PASS; control +100 ns on the incrementer's
bits 16-19 carry-in: ordinary 2/2 PASS, preloaded 2/2 FAIL (as it must); the counter's carry keeps 13.5 ns (bisected,
4 draws); period 24.2 ns per iteration at K 2101 (your P = 23.18), set by ucmpi1, ucontrol_merge0 + its olink rdly,
ulink_n12__1 (both stages' rdly), ulink_n8 / ulink_n_trueResult_8 uack, umux1 (linesens dP/dX 1; every other line 0;
`formal/tools-B/preload/out/ls_auto_rs3_2101.txt`).
**Every NOT EQUIVALENT route checked is this one pattern (01:45 UTC).** Rebuilt here from your suite1 sizes_4.vh (sdf
md5-identical to yours), fasm_equiv run with `--max 50` where it truncated:
| route (sdf) | hard differences | all of them |
|---|---|---|
| xorshift s3 (ea3c2aad) | 1 | F7BMUX input from `$PACKER_GND_NET$LUT$66` |
| xorshift s7 (302ff749) | 1 | F7BMUX input from `$PACKER_GND_NET$LUT$262` |
| ipow s4 (1ac15af5) | 5 | CARRY4 DI0-3 of SLICE_X12Y72 from `$PACKER_GND_NET$LUT$672/668/..` (the bench's own `cycles` counter, harness not kernel) and an F7BMUX input from `$PACKER_GND_NET$LUT$334` |
| collatz64 s5 (84cbd5fa) | 1 | F7BMUX input from `$PACKER_GND_NET$LUT$34` |
Each: a packer GND LUT, INIT 0b10 (O = its one logical input), that input on $PACKER_GND_NET; bits: INIT folded to 0, the
pin unrouted ("HARMLESS ... json 0 bits 1"). Value 0 on both sides in every case.
**Formal's draws on the same bits, with YOUR suite draw points (K = 10000 + 100 S + j, j = 1..4) -- the draws suite_one.sh
skipped:**
| route | vectors | draws | full range |
|---|---|---|---|
| xorshift s3 (ea3c2aad) | xor19 | 4/4 PASS (K 2101-2104; above) | counter preloaded 8/8, carry slack 13.5 ns |
| ipow s4 (1ac15af5) | ipow17 | 4/4 PASS (K 10401-10404) | (no counter; ipow17 reaches e = 0x7fffffff) |
| collatz64 s5 (84cbd5fa) | c6419 | 4/4 PASS (K 10501-10504) | c64hi (63-bit values) 4/4; steps counter preloaded at 0x3ffffff0 4/4 |
| xorshift s1, local (694d657d, EQUIVALENT) | xor19 | 4/4 PASS (K 2101-2104) | preloaded 8/8; control fails only preloaded |
**Suggestion (yours to decide):** in fasm_equiv, fold a JSON LUT whose read pins are all tied to constants (here A1 on
$PACKER_GND_NET) into its constant before comparing drivers, as the bits side already is. Until then the suite reads
every such AUTO route as not a board route. **Seed 7 (302ff749), rebuilt here, same verdict, same single
pattern:** DRIVER DIFFERS at SLICE_X12Y61/F7BMUX/0, json D6LUT = `$PACKER_GND_NET$LUT$262` (INIT 0b10, A1 on
$PACKER_GND_NET), bits const 0, A1 "HARMLESS json 0 bits 1". Not checked: whether the C6LUT's unrouted A1 is benign in silicon beyond the INIT (with INIT 0
the LUT ignores A1, so the pin's value cannot matter).

## B5. Every current board candidate at full range (preloaded counters, 63-bit / 32-bit values): all pass, no long-carry path within 8 ns of failing (shard B, 2026-11-18 00:00 UTC; untrusted simulation, RC arcs)
Each rebuilt here from its BOARD-QUEUE command, sdf md5-identical to yours. xorshift: xor19 8 draws + 4 slow-carry, counter
preloaded at 0x3ffffff0 (set A) 16 + 8 slow-carry and at 0x7ffffff0 (set B) 16; collatz family: base vectors 8, full range
8, steps counter preloaded 8. Carry slack = extra delay the long carry survives on 4 preloaded draws (B2; for collatz the
steps counter's carry in the LAST increment). Settle = C's steermargin at chains 0.20 / rest 0.31 / CARRY 1.0.
| item (sdf) | all draws | carry slack, ps | period (2 draws), ps | settle ucmpi1, ucmpi0, ps |
|---|---|---|---|---|
| 33 xorshift (7f0c0592) | pass | 13398 | 19799 / 19541 | 3216, 2306 |
| 27 xorshift (a9bdac53) | pass | 12226 | 20611 / 20194 | 2148, 2842 |
| 35 xorshift (9145cd49) | pass (B3) | 11289 | 17719 / 17402 | 566, 204 |
| cand3 x55a10 (four routes, B3) | pass | 8632-11484 | ~17300 | 1026-1354, 1134-2250 |
| 28 collatz (d86bdde5) | pass | 16953 | 27161 / 26410 | - |
| 31 collatz (7aefc4bd) | pass (B2) | 10546 (default arcs) | - | - |
| cand4 collatz x0.70 s27 (f11ff1ee) | pass (B3) | 10000 | 20423 / 19500 | - |
| 30 collatz64 (637ff02e) | pass | 18828 | 35206 / 35444 | - |
| 32 collatz64 (842dd4d7) | pass (B3) | 18320 | 30986 / 32509 | - |
Plainly: for these kernels the inputs the bench cannot deliver (counter carries past 12 bits, 63-bit collatz values) do not
expose any defect in formal's simulator on any candidate; the incrementers and step counters have >= 8.6 ns to spare.
Not covered: ipow (its loop has no counter; ipow17 already reaches e = 0x7fffffff), gcd, the select race class (B's Lean
work), anything outside the draw model.
## B4. Which matched delays set the period, per route: on research's candidates 3-5 of ~55 delay lines do, and they are loop RINGS, not the datapath; the rest cost area, not speed (shard B, 2026-11-17 23:21 UTC; untrusted simulation, RC arcs)
For the sizing rule (formal PROGRAM "Research's first lead"). `formal/tools-B/preload/linesens.py` (18 s a route): for every
delay line (each `...chain.g[0].u`), +500 ps on its first LUT, alone, and the change of the loop header's per-iteration
period (umux0's request OR, median over a long call; your draw K, w 20). dP/dX = 1: the line is on the cycle that sets the
period; 0: shortening it buys nothing on this route (another cycle is longer by >= 500 ps); between: within 500 ps of it.
Raw tables: formal/tools-B/preload/out/ls_*.txt.
| build (route, draw) | reference period | lines with dP/dX > 0 (dP for +500 ps) |
|---|---|---|
| xorshift x55a10 seed 21 (42b4fb4c), K 2101 / 2102 | 17469 / 17286 ps | uaddi0.udly, umux0.udly, ulink_n12__0.rdly, ulink_n7f__1.uack, ulink_n_trueResult_6 stage[0].uack: 500 each, both draws |
| xorshift x55a10 seed 4 (05a84ea0), K 2101 | 17333 | ucmpi1.udly, umux2.udly, ulink_n11__0_folink.uack, ulink_n11__1.rdly, ulink_n12__2.rdly: 500; the seed-21 five: 238; ulink_n_trueResult_10 stage[0].uack: 27 |
| same, K 2102 | 17308 | the same five: 500; ulink_n_trueResult_10: 160; the seed-21 five: 32 |
| collatz x0.70 seed 27 (f11ff1ee, your cand4 route), K 3101, n = 0xee2f | 20423 | uaddi0.udly, uselect0.udly, ulink_n_falseResult_9 stage[0].uack: 500 |
| collatz64 item 32 (842dd4d7), K 3201, n = 0x1ed6135ab2dfefd1 | 30986 | uaddi0.udly, uselect0.udly, ulink_n_falseResult_9 stage[0].uack, ulink_n10__4.uack: 500 |
- **xorshift:** the period is set by the counter's ring (umux0 -> forkdec0 -> uaddi0 -> ucond_br6 -> ulink_n_trueResult_6 ->
  umux0, with its control link ulink_n12__0) or by the n ring (umux2 -> ucmpi1 -> ucond_br8 -> ulink_n_trueResult_10 ->
  umux2, ulink_n11 / n12__2), within 0.03-0.47 ns of each other on seed 4; the xorshift datapath (uxori*, ushli*, ushrui*)
  is off the cycle on both routes. So after UADDI0 (B3) the next lines to shorten are umux0 / umux2's and those links'
  acknowledge / request lines, and the two rings have to come down together.
- **collatz / collatz64:** 3n + 1 (UADDI0) and the select (USELECT0) are on the cycle; their long carries ARE reached by
  inputs (c32hi / c64hi, B2), so shortening them is judged by full-range draws, not by preload.
- **Headroom, same placement (zeroline.py what-if: the named lines' LUTs at 20 ps and the pips between them at 0; not a
  buildable circuit; one call, draw 2101):** seed 21 / seed 4 periods 17469 / 17333 ps as built. Counter ring's 5 lines
  zeroed: 16538 / 17333 (seed 4's n ring takes over). The n ring's lines zeroed INCLUDING ucmpi1.udly: wrong answers on
  both (the loop test needs its compare's delay). The n ring without ucmpi1 (umux2, ulink_n11__0_folink.uack,
  ulink_n11__1.rdly, ulink_n12__2.rdly) plus the counter ring's 5: 15354 / 15822, right answers: -12 % / -8.7 %. So about
  1.5-2 ns per iteration sits in nine mux / link lines of the two rings, not in the datapath; whether they can be cut is
  for the draws (their own capture margins are not measured here). Three of the nine are acknowledge lines, and
  ulink_n_trueResult_6's UACK 1 is your hold pad (hold_pads.py: "was 0; 2 rows below 0"): the what-if removes hold
  protection a single draw cannot judge. Formal is building the request-side cut only (next entry).
- **The request-side cut, built (23:39 UTC):** x55a10 with UADDI0, UMUX0, UMUX2, ULINK_N11__1, ULINK_N12__0, ULINK_N12__2 at 0
  (hold pads and UCMPI1 kept), seeds 21 / 4 (sdf 6e9becc5 / cb8ae7f7, ffmux clean): xor19 8/8 + slow-carry 4/4, preload
  16/16 + 8/8 on both; period 16508 / 15670 ps (as built 17378 / 17321; UADDI0 0 alone 15871 / 16181). But the loop test
  (ucmpi1 -> ucond_br6) settles only 154 ps before its request at chains 0.20 / rest 0.31 / CARRY 1.0 on seed 21, with 4
  live runts (the condition moves under the request), and 162 ps on seed 4 (no runts); UADDI0 0 alone kept 1527-1789.
  So cutting the rings' request lines spends the loop test's settle margin; formal does not recommend it. UADDI0 0 alone
  (B3) is the cut that kept its margins here.
- One route a row; the farm's b_u0xor gives the period on 12 routes a side but not this map. The map moves with the route
  (seed 4 vs 21): a sizing rule that shortens only the on-cycle lines needs it per route, or a margin for the swap.
## B3. On your current xorshift candidate (x55a10), UADDI0 0 keeps every draw and every preloaded draw on every route tried; on a fixed route the line costs 0.82 ns (seed 21) or nothing (seed 4), and rebuilt UADDI0 0 routes were 4.6-8.7 % faster, partly by re-placement; collatz / collatz64's UADDI1 0 is safe but buys nothing (shard B, 2026-11-17 22:31 UTC; untrusted simulation)
Follow-up to B2, same tools and model (formal's simx on the decoded bits, your draw K, w 20, host 12 ns). Rebuilt here with
your flow; the four x55a10 routes are md5-identical to C41's (8f165305 / f1da196a / 9a68cb56 / 05a84ea0).
| x55a10 seed | UADDI0 12: xor19 last answer (us) / period (ps) / carry slack / settle ucmpi1, ucmpi0 (ps) | UADDI0 0: sdf, same columns |
|---|---|---|
| 1 | 26.55 / 14169, 14002 / 8632 / 1202, 2080 | 11cc22bd: 25.92 / 13785, 13717 / 9062 / 1182, **319** |
| 2 | 26.45 / 14041, 13925 / 8789 / 1026, 1134 | 1ef5450b: 24.53 / 12929, 12813 / 7773 / **194** (ucond_br8), 1820 |
| 3 | 26.32 / 14005, 13658 / 8007 / 1283, 2250 | 9e4de472, **FFMUX-FLAG** (ffmux_scan: CLBLM_R_X9Y34.SLICEL_X1.CFF): 24.84 / 13190, 13030 / 8164 / - |
| 4 | 26.88 / 14163, 14353 / 8984 / 1046, 1047 | c5751262: 24.49 / 13242, 13170 / 7812 / 1047, 1674 |
Every build: xor19 8/8 (K 2101-2108) and 4/4 with CARRY / F7 / FF at 0.8-1.0 (DRAW_XBAND), counter preloaded at 0x3ffffff0
16/16 and 8/8 at slow carry. Period = median per-iteration ps of umux0's request over a 271-iteration preloaded call
(draws 2101 / 2102); carry slack = extra delay the incrementer's carry into bit 16 tolerates (B2); settle = C's
steermargin.py, smallest gap of the condition before a steer request at chains 0.20 / rest 0.31 / CARRY 1.0 (xor19 +
xorlong), no live runts anywhere. Seeds 1 / 2 / 4 (clean on both sides): xor19 last answer 26.63 -> 24.98 us (-6.2 %),
period 14.11 -> 13.28 ns (-5.9 %).
- **The trade:** with UADDI0 0 the request at ucond_br6 / 7 / 8 / 9 comes from ucmpi1 alone, so the loop test's margin is
  UCMPI1 (5) against the compare's chain. Its worst corner fell to 194 ps on seed 2 (from >= 1026 on the UADDI0 12 routes);
  ucmpi0's 319 ps on seed 1 is the entry compare, not touched by UADDI0, so that one is route scatter. Three clean routes a
  side are a sample: farm b_u0xor (12 seeds a side, same measurements) is queued behind the 200-core ceiling. If 194 ps is
  too little for you, UADDI0 0 with UCMPI1 6 is the variant to try; formal has not built it.
- **The FFMUX-FLAG route** (seed 3, UADDI0 0) passes every draw here: formal's simx does not show that defect on this route.
  Excluded from the comparison above, as you exclude it.
- **collatz x0.70, UADDI1 7 vs 0** (seeds 27 / 2 / 3 / 4; sdf f11ff1ee, 0063fe05, e963d572, 60058e36 vs dd684146, c03c2484,
  d94d3040, 6fee8e19): every build col18 8/8, c32hi (full 32-bit range, formal/tools-B/preload/vec/) 8/8, steps counter
  preloaded at 0x3ffffff0 8/8; the steps counter's last-increment carry keeps >= 7.07 ns with UADDI1 0 (>= 7.77 with 7);
  period 16.06 -> 15.81 ns, all of it from seed 27 (seeds 2-4: 15.91 -> 15.95). UADDI1 (7) is already shorter than UCMPI2
  (12) at the same join (ucond_br5), so it was never on the cycle: 0 saves its delay LUTs only.
- **collatz64 item 32, UADDI1 12 vs 0** (seed 22; 842dd4d7 vs 65a92f2d): c6419, c64hi (63-bit trajectories) and the preloaded
  steps counter all pass; last-increment carry 14609 vs 14804 ps; period 25.67 / 26.95 vs 25.42 / 26.51 ns (one route a side).
- **For the sizing rule** (formal PROGRAM "Research's first lead"): `formal/tools-B/preload/joinscan.py KERNEL_bench.v SIZES.vh`
  lists the joins fed by two sized operators. Where the two start from the same token (xorshift's uaddi0 /
  ucmpi1, collatz's and collatz64's uaddi1 / ucmpi2), only the larger delay is ever on the path, and the draws (with the
  counters preloaded) say the smaller one can be 0. The static rule sizes each operator alone; a rule that sizes a join's
  inputs together (the later request must cover every input's data) would drop these. Formal has checked it on these three
  joins only. `formal/tools-B/preload/constlinks.py NET ROUTED DUMP` lists the entry links that can be preloaded in any build (for your automatic builds).
- **Redone on RC_TREE=1 decodes (your arcs, C48), 23:02 UTC; pass / fail unchanged everywhere, every ps value larger:**
  | build | UADDI0 / UADDI1 | draws (base, slow-carry, preload) | carry slack | period, ps (K 2101 / 2102) | settle ucmpi1, ucmpi0 |
  |---|---|---|---|---|---|
  | x55a10 seed 4 | 12 (05a84ea0) | 8/8, 4/4, 16/16 + 8/8 | 11484 | 17333 / 17308 | 1354, 1710 |
  | x55a10 seed 4 | 0 (c5751262) | 8/8, 4/4, 16/16 + 8/8 | 10039 | 16247 / 16114 | 1789, 2300 |
  | item 35 (seed 21) | 12 (9145cd49) | 8/8, 4/4, 16/16 + 8/8; B 16/16 | 11289 | 17719 / 17402 | 566, 204 (= C48) |
  | item 35 sizes, seed 21 | 0 (96a395ab) | 8/8, 4/4, 16/16 + 8/8; B 16/16 | 10351 | 16774 / 16732 | 1527, 166 |
  | collatz x0.70 s27 | UADDI1 7 (f11ff1ee) | col18 8/8, c32hi 8/8, steps 8/8 | 10000 (steps, last increment) | 20423 / 19500 | - |
  | collatz x0.70 s27 | UADDI1 0 (dd684146) | 8/8, 8/8, 8/8 | 8867 | 19931 / 19383 | - |
  | collatz64 item 32 | UADDI1 12 (842dd4d7) | c6419 8/8, c64hi 8/8, steps 8/8 | 18320 | 30986 / 32509 | - |
  | collatz64 item 32 | UADDI1 0 (65a92f2d) | 8/8, 8/8, 8/8 | 18554 | 31848 / 33075 | - |
  On RC arcs UADDI0 0 is 6.6 % (seed 4) and 4.6 % (seed 21) faster; the loop-test settle gap is larger on both UADDI0 0
  routes, so seed 2's 194 ps above (default arcs) is not a pattern on these two. The negative control holds on RC (+20 ns
  into bit 16: xor19 2/2 PASS, preloaded 2/2 FAIL). ucmpi0's 166-204 ps on seed 21 is item 35's UCMPI0 6 (C48; C41's 10
  lifts it). Farm b_u0xor (12 seeds a side) runs on RC decodes.

- **Your preload1 vs this, on speed (23:14 UTC, RC arcs, x55a10, period ps averaged over draws 2101 / 2102; xor19 last answer us):**
  | UADDI0 | seed 21 (sdf) | seed 4 (sdf) |
  |---|---|---|
  | 12 | 17378, 32.44 (42b4fb4c = C41's) | 17321, 32.68 (05a84ea0) |
  | 4 | 17981, 33.44 (e3a39490) | 16866, 31.31 (d122d782) |
  | 1 | 17064, 31.69 (57fee21d) | 17223, 32.15 (3881aa40) |
  | 0 | 15871, 29.66 (27a25487) | 16181, 30.52 (c5751262) |
  Every build: xor19 4/4, preload A 8/8. So 12 / 4 / 1 sit within route scatter of each other, which agrees with your
  preload1's P (16.73 / 16.29 / 16.23 / 16.75 for 12 / 8 / 6 / 4: no trend), and only 0 is faster here (by 0.7-2.1 ns over
  the next on both seeds). Traced on the same route (zeroline.py: the line's 12 LUTs and the pips between them set to
  20 ps / 0 in the decoded net, everything else as placed): seed 21 17378 -> 16558 ps (the line costs 0.82 ns there; +500
  ps on its first LUT moves the period by exactly +500), seed 4 17321 -> 17321 (off the cycle; the compare's request is
  later at the join). On the UADDI0 1 route of seed 21, +500 ps on its one LUT moves the period by 0. So the line is on
  the cycle on some routes, by up to ~0.8 ns, and off it on others; the rest of the rebuilt UADDI0 0 builds' gain (0.7 ns
  on seed 21, 1.1 on seed 4) is re-placement of the smaller netlist, which a 2-route sample cannot tell from luck. That
  is consistent with your no-trend P for 12 / 8 / 6 / 4. Farm b_u0xor has 12 routes a side.
- **Farm b_u0xor (11-18 00:01 UTC; RC arcs; 21 of 24 tasks back; table formal/tools-B/preload/out/farm_b_u0xor.txt):**
  x55a10 UADDI0 12 vs 0 on seeds 1-12 (seed 9 and seed 10's 12-arm not back). Every route: xor19 4/4 and preloaded counter
  8/8. On the 9 seeds clean on both sides (1, 2, 4-8, 11, 12): period 17360 -> 16786 ps mean (-3.3 %), per seed -1217 to
  +1094 ps (seed 6 is SLOWER with UADDI0 0). Loop-test settle (ucmpi1, worst corner): UADDI0 12 min 1020 / median 1517 ps;
  UADDI0 0 min 344 / median 1315; no live runts on any clean route. Entry (ucmpi0): 12 min 1710, 0 min 725.
  **The FFMUX-FLAG route (seed 3, UADDI0 0) has its loop test at 9 ps** (draws still pass): keep excluding those routes.
  Bottom line for UADDI0 0: safe in every draw and at every carry formal can reach; ~3 % faster on average with wide route
  scatter; it moves the loop test's worst settle from ~1.0 ns to ~0.35 ns, so pick its route by that margin (as with C41).
## B2. Paths no vector can reach, reached: with the loop counter preloaded, xorshift's incrementer (UADDI0) can go from 12 to 0 -- 112/112 preloaded draws pass on 4 routes, its 30-bit carry keeps >= 8.0 ns, and the routes run ~5 % faster; collatz / collatz64 counters and 63-bit values the same way (shard B, 2026-11-17 20:58 UTC; untrusted simulation)
Your PROGRAM "Paths no vector can reach" asked for exactly this; formal's PROGRAM gave it to B. Formal's simx on the circuit
decoded from each bitstream, your draw K, H_RUNT(20), host 12 ns. Every build here was rebuilt locally from your command
(nextpnr 9c732bc6303458df); sdf md5s below.
- **How (one command, `formal/tools-B/preload/prun.sh`):** a loop counter enters its loop from a CONSTANT (xorshift's i = 0
  goes through the pipe `ulink_n6`, whose 64 latch halves read GND; collatz's steps = 0 through `ulink_n7`). The tool gives
  those latch state nodes the constant value I0 from t = 0, after checking on an ordinary run that they are constant 0 there,
  so the run is the same bitstream with the entry constant tied to I0 instead of 0; nothing else changes. The expected
  answers come from `oracle.c`, the kernel's C loop copied verbatim with `int i = i0` (`int steps = s0`), refusing inputs
  where the two cannot agree (xorshift needs I0 < rounds: the hardware's loop runs the body once before testing).
  Checks: bit 30 of i + 1 (ulink_n_trueResult_6) flips 7 times in a preloaded run and never in xor19; the same run checked
  against the oracle at I0 + 1 fails.
- **The preload can fail where your vectors cannot (negative control):** +20 ns on the carry-in of uaddi0's slice[4] (the
  carry into bit 16; formal's simx injection, like your SDF injections): xor19 PASS (that carry never moves for rounds <=
  4095), preloaded FAIL, wrong exactly on the calls that use i + 1 = 0x40000000.
- **Vectors.** A: I0 0x3ffffff0, rounds 0x3ffffff1 / 0x3fffffff / 0x40000000 / 0x40000001 (x2) / 0x40000002 / 0x40000010
  (1-32 iterations; i + 1 = 0x40000000, the longest carry the C can ever produce, since i < rounds <= 2^31 - 1, in 5
  calls, its result used in 4; n - 1 = 0x3fffffff in one). B: I0 0x7ffffff0, rounds 0x7ffffff1 .. 0x7fffffff (the compares
  at the top of the range). Ordinary vectors with rounds = 0x80000000 / 0xffffffff / 0xc0000000 (loop skipped): 8/8 on item 35.
| xorshift, item 35's sizes with UADDI0 = | route (sdf) | xor19 draws | preload A | preload B | carry-into-bit-16 slack, ps | period, ps (2 draws) |
|---|---|---|---|---|---|---|
| 12 (item 35) | 21 (9145cd49) | 2/2 | 32/32 (+ 32/32 at CARRY 0.8-1.0) | 32/32 | >= 9140 (fails 9179) | 14427 / 14214 |
| 12 | 2 (b2470514) | 8/8 | 16/16 | 16/16 | >= 8906 | 14213 / 13982 |
| 12 | 4 (ee6304d0) | 8/8 | 16/16 | 16/16 | >= 9453 | 14855 / 14402 |
| 12 | 5 (7a448319) | 8/8 | 16/16 | 16/16 | >= 9531 | 14137 / 14020 |
| 7 (x0.55) | 21 (0a993f62) | 4/4 | 16/16 | 16/16 | >= 8164 | 13901 / 14123 |
| 2 | 21 (fafe42b5) | 4/4 | 8/8 | 8/8 | - | 13883 / 13590 |
| 0 | 21 (96a395ab) | 4/4 | 8/8 | 8/8 | >= 8828 | 14193 / 14196 |
| 0 | 2 (2b8ef891) | 8/8 | 16/16 | 16/16 | >= 8125 | 13331 / 13421 |
| 0 | 4 (f5223fdd) | 8/8 | 16/16 | 16/16 | >= 8046 | 13245 / 13307 |
| 0 | 5 (b4b07f06) | 8/8 | 16/16 | 16/16 | >= 8359 | 13510 / 13454 |
Draws are your K from 2101; preload columns are formal's draws with the oracle from the preloaded state. "Slack" =
carryslack.sh: the largest extra delay on the carry into bit 16 at which 4 preloaded draws (K 2101-2104) all stay right,
bisected to 50 ps: a consequence slack (an upper bound of the settle margin). "Period" = median per-iteration time of
umux0's request OR over a 271-iteration preloaded call, draws 2101 / 2102 (formal's simx time scale, not your P).
- **Reading.** Every preloaded draw passes at every UADDI0 down to 0, and the 30-bit carry keeps >= 8.0 ns with UADDI0 = 0.
  i + 1 goes to the loop steer ucond_br6, whose join also waits for ucmpi1 (i < n - 1, UCMPI1 = 5, its own 32-bit chain);
  nothing captures i + 1 until the next iteration, ~14 ns later. Same 4 seeds, UADDI0 12 -> 0 (each a different route,
  since the netlist changes): period mean 14.28 -> 13.58 ns (-4.9 %; per seed 21 / 2 / 4 / 5: -0.13 / -0.72 / -1.35 /
  -0.60 ns), xor19 last answer 26.95 -> 25.55 us (-5.2 %). Reading (an inference, not traced): at that join UADDI0's 12
  units outlast UCMPI1's 5, so the incrementer's matched delay sits on the critical cycle of most routes while buying
  nothing a draw can see, even at its worst carry. Four routes a side are a sample; your P on the same routes decides.
- **For the sizing rule (formal PROGRAM, "Research's first lead"):** the part of the static rule this exposes is that it
  sizes an operator's delay for its own worst carry, as if its result were captured when its request arrives. Here the
  result is joined with a sibling (the compare) and then held by transparent latches for a whole iteration; the static
  size pays for a capture that does not happen. Formal has not checked how general this is beyond the counters below.
- **collatz, item 31** (nl6s3a, seed 20, sdf 7aefc4bd = yours): col18 4/4; full-range 32-bit n (0x15555555, i.e. 3n + 1 =
  2^30, and five more peaking to 0x746c9680, all below 2^31) 8/8; steps preloaded at 0x3ffffff0 on those + col18 (n = 1
  excluded: the hardware answers it from a constant) 8/8. Steps carry into bit 16, the carry in the LAST increment (n =
  0x10000: steps ends at exactly 0x40000000): >= 10546 ps. 3n + 1's carry into bit 28: >= 9765 ps.
- **collatz x0.70 seed 27** (your cand4 route; sdf f11ff1ee here): col18 4/4, full-range 16/16, steps preloaded 16/16;
  steps last-increment carry >= 8007 ps (UADDI1 7); 3n + 1 into bit 28 >= 8320 ps. So x0.70's UADDI1 7 is safe for the
  steps counter's full range on this route.
- **collatz64, item 32** (h4s3p, seed 22, sdf 842dd4d7 = yours): its kernel boundary in the decoded net takes all 64 bits
  (the bench's high-word mask is outside the kernel), so 63-bit values are ordinary inputs here: n = 0x1555555555555555
  (3n + 1 = 2^62, a 62-bit carry), 0x0555555555555555, and four odd 62-bit n peaking in [2^62, 2^63) without overflow:
  8/8. Your c6419 already reaches bit 48 (+20 ns on the 3n + 1 carry into bit 48 fails it). The carry into bit 56 keeps
  >= 16484 ps on these vectors. Steps preloaded: 8/8; last-increment carry into bit 16 >= 14609 ps.
- **Which long paths by what:** xorshift: incrementer carries > 12 bits by preload only; compare ripple, entry compare and
  n - 1 at full width by inputs (they are inputs at the kernel boundary). collatz / collatz64: 3n + 1 at full width by
  inputs outside the bench's mask; the steps counter's carries > ~10 bits by preload only. Not reached by anything here:
  none known for these three kernels; ipow's (e > 0 loop, r * b) were not looked at.
- Reproduce: `formal/tools-B/preload/prun.sh BASE OUT I0 LINK "PAIRS" N SEED0` on a margin/run.sh decode dir (KERNEL=,
  TMAX=), `carryslack.sh` for the slack; commands per row in formal/JOURNAL-B.md (2026-11-17).
- **Caveat (C48, 22:25):** every ps number above was measured on formal's DEFAULT decoded arcs (~20 % fast against your
  model). The RC_TREE=1 reruns (your arcs) are in B3: pass / fail unchanged; item 35's carry slack 11289 ps (default 9140),
  UADDI0 0 seed 21 10351 ps (8828), periods ~22 % longer on both sides. On speed, B3 supersedes the ~5 % here: on a fixed route
  the line costs 0-0.82 ns; the rest of the rebuilt routes' gain is re-placement.

## C-status at the STOP (shard C, 2026-11-18 03:00 UTC)
Finished: C36-C52 (newest: C52 min1 sizes, C51 compares bind, C49/C48 RC-arc corrections). Unread but done on the farm: c_c41x32
(your cand3b on 32 routes in formal's simx, default + slow-carry draws, steer margins) and c_half16 (collatz / ipow x0.70, 16 routes
each, plain vs 0.5x non-compare delay); results on claude/cluster under results/fm_c_c41x32 and fm_c_half16. Formal C reads them
after the reset; you may read them first.

## C52. A real build with EVERY matched delay except the two loop compares at size 1 -- collatz x0.70's sizes, seed 27 -- passes formal's 16 draws AND your own gate (draw:2701 and worst, 17/17, EQUIVALENT) (shard C, 2026-11-18 00:50 UTC; simulation, untrusted; one route)
Following C51: research/data/collatz_sizes_T3cdb_nl6s3a_x70_bench.vh with all 39 BD_SZ_ lines except UCMPI0 (6) and UCMPI2 (12)
set to 1 (file: formal/tools/margin/vec/collatz_sizes_nl6s3a_x70_min1_bench.vh), your collatz flow (pre_eq2, COL knobs,
NEXTPNR_SEED=27), nextpnr 9c732bc6303458df: sdf b691adef, fasm b04daa0d.
- formal's simx (RC-tree arcs, your draw model), col18, K 2701-2716: **16/16 PASS**, last answer 27.2-29.5 us (x0.70 s27: 31.8-33.8).
- **your bench_gate.sh** (origin/claude/research at 20:3x UTC, run here, XRAY_DB = the toolchain's prjxray-db/zynq7):
  `draw:2701` -> `PASS 17/17 cycles 4984 VERDICT: EQUIVALENT`; `worst` -> `PASS 17/17 cycles 4768 VERDICT: EQUIVALENT`.
- loop-steer settle margins (formal, chains 0.20 / rest 0.31): ucmpi0 -> ucond_br2 689 ps (CARRY 0.20) / 519 ps (CARRY 1.0),
  ucmpi2 -> ucond_br5 3185 / 3015 ps, no runts.
- **More routes (01:00-02:50 UTC, RC arcs, 8 draws each, steer margin at chains 0.20 / rest 0.31 / CARRY 1.0):**
| build | seed (sdf) | formal draws | entry compare -> steer | loop test -> steer |
|---|---|---|---|---|
| collatz x0.70 min1 | 1 (d246602e) | 8/8 | **183 ps, 2 runts** | 2127 |
| | 2 (7cf5d88d) | 8/8 | 299 | 2261 |
| | 3 (bf0d0dcc) | 8/8 | 337 | 1977 |
| ipow x0.70 min1 (same recipe: 48 sizes to 1, UCMPI0 8 / UCMPI2 13 kept) | 31 (e8967775) | 8/8 | 515 | 518 |
| | 1 (089ac93d) | 8/8 | 1643 | 1139 |
| | 2 (ef7fc773) | 0/8 -- **NOT a timing result:** your gate's fasm_equiv says NOT EQUIVALENT, `SLICE_X19Y61/F7AMUX/S0 json ('const', 0) bits ('const', 1)` (the F7-select defect, as route 19); formal's run stops in the first call | | |
  Your gate, `worst`: collatz x0.70 s27 unshrunk PASS 17/17 cycles 5516; min1 s27 4768 (-14 %); ipow min1 s31 PASS 17/17 cycles 920.
  With every other size at 1 the entry steer loses margin on collatz (183-337 ps vs 677 unshrunk, C49): the request path
  that the entry compare races got shorter too. So for a board build keep UCMPI0 a step longer than x0.70's 6 (C43's 8).
- **Reading:** in both simulators, on this route, collatz's request paths (joins, C-elements, latches, links at size 1) already
  cover every data path except the loop compares. If that holds on 32 routes and in your draws, the sizing rule's job reduces to
  the compares (their steer race), and every other matched delay can sit at its floor. Not shown: hold-side races that only the
  board's real glitch behaviour would expose (runts, C19), other routes, and your event-graph period for this build (please
  run eval_task / itercost on it; formal's last-answer ratio suggests ~-14 % end to end on col18).

## C51. For your "which part of the sizing rule over-sizes" question: on item 35's route every matched delay EXCEPT the two loop compares can be scaled together to 0.31x and the answers stay right; the compares are what bind (shard C, 2026-11-18 00:15 UTC; untrusted simulation, consequence measure)
New tool formal/tools/margin/chainscale.py: scale the routed path of matched-delay chains (every arc g[0]..g[n-1], pips
included; an injection of -(1-s) x the arc, never negative) and find the smallest s that still returns all right answers.
Item 35 route 21 (sdf 9145cd49), RC-tree arcs (= your model's), xor19, two corners of your box, chains 0.20 / rest 0.31 with
CARRY 0.20 and 1.0 (the corners where chains are fastest against the logic), no scatter:
- one chain alone: ucmpi0.udly (6 stages, 3.2 ns) s_min 0.38, ucmpi1.udly (5 stages, 2.3 ns) 0.44; EVERY other kernel chain
  (51: link rdly / uack, umux0-3, uxori1/2, uaddi0, uaddidec0, the merges) can go to 0 alone -- others in series cover it.
- all 51 non-compare chains TOGETHER: s_min 0.31 (all at 0 fails; 0.5 passes). Negative control: that joint run at s = 0
  returns wrong answers, so the injection acts.
- **Reading:** in your model's arcs, item 35's sizes (already x0.55 of item 33's) still hold ~3x the delay the data paths
  need at the fast-chain corner, except at the two compare -> steer races, which is where every x0.55 / x0.40 failure so far
  sat (C24, C29, C35, C43, C48). So the over-sizing is not uniform: a sizing rule that treats a compare's condition like any
  other data bit gives the compares too little and everything else too much. A rule that sizes the compare chains by their
  steer race (the condition's settle before the request, steermargin.py) and the rest by data settle would cut much more.
- **Same scan on your cand4 routes** (RC arcs, same two corners; col18 / ipow17): collatz x0.70 s27 -- all 843 non-compare
  arcs jointly to 0 still right; ucmpi0.udly alone 0.38, ucmpi2.udly 0.31. ipow x0.70 s31 -- all non-compare chains to 0 still
  right; ucmpi2.udly 0.12, ucmpi0.udly 0. So in collatz and ipow the request paths' own cells (joins, C-elements, latches)
  already cover every data path except the compares at these corners, and in xorshift the rest needs ~0.31x. This is the
  strongest version of the pattern; it needs the draws (per-pip scatter) and the slow-chain corners before anyone trusts it.
- **Draws check (00:25):** your draw model (per-pip scatter), 8 draws each, with every non-compare chain's routed path at 0.5x
  (injection computed at band 0.20, so no arc goes negative): collatz x0.70 s27 8/8 PASS, last answer 27.9-29.8 us vs
  31.8-33.8 unscaled (~-12 %); ipow x0.70 s31 8/8, 4.72-5.09 vs 5.85-6.21 us (~-18 %); item 35 r21 **7/8** (one draw fails),
  26.4-28.5 vs 32.2-33.6 us. So collatz / ipow keep passing with half their non-compare delay under scatter; xorshift
  starts to lose draws at 0.5 (its two-corner joint factor was 0.31: the scatter is what the corners miss).
- **Two more routes each (00:20)**, same check (8 draws plain, then the same 8 with non-compare chains at 0.5x): collatz x0.70
  seeds 1 / 2 (sdf 0cdf4a34 / 0063fe05) 8/8 -> 8/8, mean last answer 32.9 -> 28.9 / 32.8 -> 29.2 us; ipow x0.70 seeds 1 / 2
  (f6e10793 / 92e06139) 8/8 -> 8/8, 6.12 -> 4.91 / 6.03 -> 4.93 us. So 3 routes per kernel, 48/48 draws at half. Farm
  c_half16 (16 routes each) is queued.
- **Limits:** consequence, not settle margin (runts the model absorbs count as fine -- read it as an upper bound of how far
  the sizes could go); two uniform corners, no per-pip scatter; xor19 does not reach uaddi0's 31-bit carry (B's B2/B3 preload
  runs do: UADDI0 to 0 passed there); slow corners (chains 0.31, rest 0.20) not included, where chains are relatively slow
  and the answer would only be easier. Before any size is cut on this: draws on 32 routes.

## C50. ipow x0.55 route 12: on the identical bits (c3542c6d, your confirmation) YOUR OWN gate passes the three draws your farm reported hung -- the difference is between your farm run and your gate, not between the simulators (shard C, 2026-11-18 00:05 UTC)
From C45 (updated 20:55): research/tools/eventgraph/bench_gate.sh from origin/claude/research (20:3x UTC), run in formal's
sandbox on this build, ipow17: draw:1201 PASS 17/17 cycles 998, draw:1203 PASS 17/17 cycles 1030 (also with
GATE_PLUSARGS=+META_INIT=0), draw:1204 PASS 17/17 cycles 1062, each ~380 s on one core, VERDICT EQUIVALENT; the draw file
reads chains 0.2187 rest 0.2370 carry 0.2025 = yours. Formal's simx passes the same draws on default and RC arcs. Things that
differ between the two runs of your gate: the farm's `timeout 100m` per draw with 4 draws sharing 8 cores (shrink8's run()
writes "TIMEOUT/none" when it fires -- is "hang" that?), the checkout of bench_gate.sh / cells/gls at the time shrink8 ran
(before the 2026-11-17 gate fixes?), and XRAY_DB (here the toolchain's prjxray-db/zynq7). Worth one rerun of task 12 on the
farm with the current tree before x0.55 ipow is written off on this route.

## C49. C37 / C40 / C43 / C46 and collatz64 x0.70 rerun on RC-tree arcs (your model's): verdicts unchanged, margins larger, except collatz x0.55 route 8 which now FAILS (shard C, 2026-11-17 23:00 UTC; untrusted simulation)
Each build decoded again with RC_TREE=1 (the margin tool's default since 22:30); 8 draws of your model (K 100r+1..8) and
steercorners.sh at chains 0.20 with (rest, CARRY) = (0.31, 0.20), (0.31, 1.0), (0.20, 1.0); worst settle gap, ps:
| build (route) | draws RC | entry compare -> steers | loop test -> steers | default arcs said |
|---|---|---|---|---|
| collatz x0.55 (20) | 8/8 | 721 | 842 | 681 / 712 (C37) |
| ipow x0.55 (3 / 5 / 8) | 8/8 each | 1873 / 1832 / 1432 | 1441 / 2226 / 2224 | >= 789 (C40) |
| item 29 ipow (19) | 8/8 | 3672 | 5395 | 3054 / 4605 |
| collatz x0.70 cand4 (27) | 8/8 | 677 | 2617 | 622 / 1764 (C46) |
| ipow x0.70 cand4 (31) | 8/8 | 2763 | 2779 | 2199 / 2498 (C46) |
| collatz64 x0.70 (1 / 2) | 8/8 each | 1420 / **581** | 2045 / 1813 | 961 / 176 (journal) |
| collatz x0.55 (4) | 8/8 | **205** | 1360 | 22 (C43) |
| collatz x0.55 (8) | **7/8, 1 livelock** (K 803, event cap) | **104, 6 runts, WRONG answers** at 0.31 / 1.0 | 1, 12 runts | 6 (C43) |
| collatz x0.55 + UCMPI0 8 (4 / 8) | 8/8 each | 1467 / 914 | 2282 / 2343 | 1172 / 691 (C43) |
(collatz x0.55 route 8: the other two corners' runs printed no rows -- they did not finish inside the memory here, i.e.
probably the same livelock; not counted.) Last answers ~20 % longer than on default arcs, as expected.
- **cand3b (x55a10) on RC arcs, seeds 1-13** (00:00 UTC 11-18): slow-carry draws (K 100S+51..54, CARRY in [0.8, 1.0]) 52/52
  PASS; at CARRY 1.0 (rest 0.31 / 0.20) ucmpi0 >= 1591 ps, ucmpi1 896 (route 3) / 959 (5, 13) / 1054 (10) / 1089 (6) and
  >= 1354 on the rest; route 21: 1425 / 923 (C48). For a board route, any of 1, 4, 7, 8, 9, 11, 12 keeps both above 1.3 ns.
- So on your model's arcs: collatz x0.55 fails on routes 30 (C48) and 8, and route 4 keeps only ~0.2 ns, all on the loop-entry
  steer; keeping UCMPI0 at 8 (C43) clears all three. The ipow leads, item 29, cand4 and collatz64 x0.70 have >= 0.58 ns.

## C48. CORRECTION to C36 / C38 / C40 / C41 on formal's RC-tree arcs (= your model's, A18): item 35 is not on a knife edge -- its loop-entry steer keeps 204 ps at CARRY 1.0 with no runts; the shrink leads gain 250-730 ps; collatz x0.55 route 30 still fails (shard C, 2026-11-17 22:25 UTC; untrusted simulation)
Same builds as before, decoded again with build_net RC_TREE=1 (formal's arcs then match your xray.sdf to ~1 ps per net, A18,
and your ring predictions within 0.5 %, carryring/). Smallest settle gap at chains 0.20, rest 0.31, ps (runts in brackets);
draws = your K, 8 per route, on the RC decode:
| build (route) | condition | CARRY 0.20 | CARRY 1.0 | default arcs said (C36-C41) | draws RC |
|---|---|---|---|---|---|
| item 35 (21) | ucmpi0 -> ucond_br2 | 665 | **204 (0 runts)** | 12 (10 runts) | 8/8 |
| item 35 (21) | ucmpi1 -> ucond_br6 | 566 | 566 | 321 | |
| x55a10 / cand3b (21) | ucmpi0 / ucmpi1 | 1933 / 1465 | 1425 / **923** | 916 / 387 | 8/8 |
| collatz x0.55 (3) | ucmpi0 -> ucond_br4 | 1020 | **850** | 583 | 8/8 |
| ipow x0.55 (11) | ucmpi2 -> ucond_br6 | 1219 | **898** | 166 | 8/8 |
| collatz x0.55 (30) | ucmpi0 -> ucond_br2/4 | 47 (8 runts), WRONG answers | 124 (10 runts), WRONG | 24-28 (12-14), wrong | 2 PASS, 2 FAIL, 4 UNDECIDED |
- **What changes:** C36 / C38's "item 35 lives on absorbed runts at the slow-CARRY end" was an artefact of formal's fast
  default arcs. On your model's arcs item 35 keeps ~0.2 ns at CARRY 1.0 (chains 0.20 / rest 0.31) and ~0.4 ns at chains 0.31.
  C38's sweep on these arcs (ucmpi0 -> ucond_br2, chains 0.20, rest 0.31): CARRY 0.2 / 0.4 / 0.6 / 0.8 / 0.9 / 1.0 ->
  665 / 551 / 436 / 322 / 265 / 204 ps (rest 0.20 at 1.0: 231), no runts anywhere: ~-58 ps per 0.1 as before, but from a
  higher start, so it never reaches 0 inside the band. C42's argument is weaker: item 35 does not need the fit to be safe in
  your model; ~0.2 ns is about one median SDF error (8.5 %) of a ~2 ns path at the slow-CARRY end.
- **What stands:** the direction (slow CARRY with fast chains is the worst corner); C41's UCMPI0 = 10 still more than
  quadruples the entry margin (204 -> 1425 ps) at no speed cost and is the safer board build; collatz x0.55 route 30 fails in
  formal on either arcs (your 3001 / 3003 too), on the same entry-steer race, and C43's fix (UCMPI0 8) removes it.
- Absolute times on the RC decode are ~22 % longer (item 35 last answer on xor19 33.0 vs 27.0 us), as A17 predicts.
- Every other C-number of 2026-11-17 (C37, C40 rest, C43-C47) is on default arcs; treat their ps values as lower than your
  model's (margins here grew 250-730 ps on RC), their pass/fail as unchanged unless rerun.

## C36-C47 caveat (shard C, 2026-11-17 22:05 UTC): every ps margin and draw in C36-C47 used formal's DEFAULT arcs, which A16-A18 show are ~20 % fast; being redone on RC_TREE=1 decodes
Formal's default build_net arcs lack output-pin drive x net C, node-wire RC and a few site arcs; on item 36's rings they come
out 8-33 % short of your model, while build_net RC_TREE=1 matches it within 0.5 % on all 128 rings (formal/tools/margin/
carryring/, an independent check of A18). So C36-C47 ran your band numbers on faster arcs (A17: your [0.20, 0.31] is about
[0.365, 0.49] in formal's default coordinates). A settle margin is a difference of two paths that are both short, so its
sign and the ranking of routes / fixes may hold, but the ps values are not your model's. Rerunning the key rows (item 35
route 21, x55a10 route 21, collatz x0.55 routes 30 / 3, ipow x0.55 route 11) on RC_TREE=1 decodes; results here next.

## C47. Slow-carry draws (CARRY/F7/F8 in [0.8, 1.0]) on item 35's and item 29's board routes in formal's simx: all pass (shard C, 2026-11-17 21:10 UTC; untrusted simulation; for comparison with your slowc1b)
DRAW_XBAND=0.8,1.0 (your draw K with its CARRY number mapped into [0.8, 1.0], = your DRAW_CARRY draw for draw):
- item 35 route 21 (sdf 9145cd49), K 2151-2166: xor19 16/16 PASS (last answer 25.4-28.4 us); xor19 + xorlong (rounds to 4095)
  16/16 PASS (245-274 us).
- item 29 route 19 (sdf b521630f), K 1951-1966, ipow17: 16/16 PASS (5.52-6.12 us).
So in formal's model item 35 survives the slow-carry end: the 8-15 ps settle margins and runts of C36 / C38 are absorbed
(transport LUTs, 20 ps filter). Your slowc1b prediction ("item 35 loses draws") tests the same race under your resolver; a
loss there and a pass here would be the runt-absorption question (C19 / BOARD-QUEUE item 2) again, not a timing number --
which is why C41's UCMPI0 = 10 (no runts at any corner) is the safer board build.

## C46. Your cand4 routes in formal's simx: collatz x0.70 seed 27 and ipow x0.70 seed 31 pass 32/32 default + 16/16 slow-carry draws; loop-steer margins >= 622 ps (collatz) and >= 2199 ps (ipow) at all 8 corners, no runts (shard C, 2026-11-17 21:05 UTC; untrusted simulation)
Built here (your x70 sizes files; collatz with pre_eq2), sdf f11ff1ee (collatz s27) and 3d6fba5c (ipow s31) -- please compare
with yours. Draws: K 2701-2732 / 3101-3132 (your model), and 16 slow-carry draws each with CARRY/F7/F8 in [0.8, 1.0]
(DRAW_XBAND; K 6701-6716 / 7101-7116, not your slowc1 numbering): all PASS. Last answer: collatz col18 25.97-28.59 us
(slow-carry 25.30-28.37), ipow ipow17 4.71-5.29 us (4.64-5.19).
| route | ucmpi0 -> entry steers worst / best | ucmpi2 -> loop steers worst / best |
|---|---|---|
| collatz x0.70 s27 | 622 (ucond_br2; chains 0.20 / rest 0.31 / CARRY 1.0) / 1062 | 1764 / 2425 |
| ipow x0.70 s31 | 2199 (ucond_br5; 0.20 / 0.20 / 1.0) / 2968 | 2498 / 3476 |
- Collatz x0.70's entry steer keeps ~0.6 ns at the worst corner here; C43's recipe (UCMPI0 unshrunk) would raise it further at
  no per-iteration cost, if wanted.

## C45. Your two x0.55 disagreement candidates, draw for draw (shard C, 2026-11-17 20:45 UTC, updated 20:55; untrusted simulation)
Built here with your flows (shrink8 / shrink9 sizes, nextpnr 9c732bc6303458df): ipow x0.55 seed 12 (sdf c3542c6d), collatz
x0.55 seed 30 (sdf 9d3f9fea) -- please confirm these md5s are your routes. Formal's simx on the decoded bits, your draw K:
| build | draw | yours | formal |
|---|---|---|---|
| collatz x0.55 r30 | 3001 (CARRY 0.91) | FAIL | FAIL (wrong counts) |
| | 3002 (0.59) | PASS | PASS |
| | 3003 (0.75) | FAIL | FAIL |
| | 3004 (0.55) | PASS | **FAIL** |
| ipow x0.55 r12 | 1201 | hang | **PASS** (17/17, last answer 4.15 us) |
| | 1202 | PASS | PASS |
| | 1203 (CARRY 0.20) | hang | **PASS** |
| | 1204 | hang | **PASS** |
- **collatz route 30, the race:** the loop-entry steer again (ucmpi0.uz_n4 -> ucond_br2/3/4), steercorners.sh: 28 ps with 12
  runts at chains 0.20 / rest 0.31 / CARRY 0.20, 24 ps / 14 runts at CARRY 0.6, 104 ps / 14 runts at 1.0, and the uniform
  runs at those three corners return WRONG answers -- in formal this route fails without any slow carry; the trigger is fast
  chains against a slower rest. Your gate absorbs some of those runts (resolver), which would explain 3004. ucmpi2 keeps
  >= 1.4 ns. With UCMPI0 at 8 (C43's recipe; a different route, sdf 2a0586e4) seed 30 passes 8/8 draws (3001-3008).
- **ipow route 12:** formal does not reproduce your hangs. Not the DSP delay (formal with nextpnr's DSP SDF arcs: same 4/4
  PASS; +10 ns on every DSP arc still passes on route 5). Known difference that produced hangs before (C17): your GLS
  starts every LUT state node at X. **Your own gate passes too:** research/tools/eventgraph/bench_gate.sh at origin/claude/
  research 20:3x UTC, run here on this build (HW = the build dir of sdf c3542c6d; XRAY_DB pointed at the toolchain's
  prjxray-db/zynq7), ipow17: draw:1203 `PASS 17/17 cycles 1030 VERDICT: EQUIVALENT`, the same with GATE_PLUSARGS=
  +META_INIT=0, draw:1201 `PASS 17/17 cycles 998`, draw:1204 `PASS 17/17 cycles 1062` (each ~380 s on one core here; the
  draw file reads chains 0.2187 rest 0.2370 carry 0.2025 = yours). So the hangs are not in your model on this route as
  built here. Either your shrink8 route 12 is a different bitstream (please compare its sdf md5 with c3542c6d), or the
  farm runs ended for another reason (shrink8's run() records "TIMEOUT/none" when `timeout 100m` fires: is "hang" a
  timeout?). Logs: /home/user/runs/rg12_* in formal's sandbox (not committed; the command is above).

## C44. ipow x0.55's per-iteration loop test: UCMPI2 10 -> 13 lifts the slow-CARRY margin from 166-398 ps to >= 2.1 ns, but costs ~5-9 % end to end; choosing the route is cheaper (shard C, 2026-11-17 20:20 UTC; untrusted simulation)
Your ipow x0.55 sizes with only UCMPI2 = 13 (unshrunk 18), seeds 1 / 4 / 11 (sdf b072ad55 / 9fe3a5a0 / 405ab163), ipow17,
steercorners.sh at chains 0.20, CARRY 1.0, rest 0.31 / 0.20:
| seed | x0.55: ucmpi2 worst (C40) | UCMPI2 13: ucmpi2 worst | ucmpi0 worst | draws | last answer mean, x0.55 -> UCMPI2 13 |
|---|---|---|---|---|---|
| 1 | 357 | 2368 | 1515 | 8/8 | 4.22 -> 4.60 us |
| 4 | 398 | 2451 | 1398 | 8/8 | 4.39 -> 4.65 us |
| 11 | **166** | 2095 | 997 | 8/8 | 4.25 -> 4.60 us |
- ucmpi2 is per iteration, so this one is paid in speed (+6-9 % of ipow17's total; per-iteration figure not measured).
  Three steps were more than needed; 11 or 12 would likely do, untested. Alternatively keep x0.55 and take a route whose
  ucmpi2 margin is large (3, 5, 8: >= 789 ps at all 8 corners).

## C43. Collatz x0.55: the same recipe -- keep the per-call entry compare UCMPI0 at its unshrunk 8 (x0.55 has 5) -- lifts routes 4 / 8 from 6-52 ps with runts to >= 691 ps at all 8 corners (shard C, 2026-11-17 20:15 UTC; untrusted simulation)
Your nl6s3a_x55 + pre_eq2, col18, built here; steercorners.sh (C36's method, 8 corners, no scatter); ucmpi0.uz_n4 -> entry
steers ucond_br2/3/4, ucmpi2.uz_n36 (the n == 2 loop test) -> ucond_br5/6:
| build | route (sdf) | ucmpi0 worst / best, ps | runts | ucmpi2 worst | draws (K 100r+1..8) | last answer mean |
|---|---|---|---|---|---|---|
| x0.55 | 4 (bc2b7d14) | **22** (0.20/0.20/1.0) / 402 | 2 at 0.20/0.31/1.0 | 1006 | 8/8 | 23.98 us |
| x0.55 | 8 (55cd1694) | **6** (0.20/0.31/0.20) / 451 | 3 at 0.20/0.31/0.20, 6 at 0.20/0.31/1.0 | 578 | 8/8 | 23.68 us |
| x0.55, UCMPI0 8 | 4 (40d5ea59) | 1172 / 1697 | 0 | 1476 | 8/8 | 25.69 us |
| x0.55, UCMPI0 8 | 8 (fa596415) | 691 / 1369 | 0 | 1392 | 8/8 | 21.99 us |
(x0.55 routes 20 / 3, C37: 681 / 583 ps worst, no runts.) Every corner run returned all 17 right answers.
- On route 8 the knife edge is there with CARRY/F7 at its FAST end (6 ps, 3 runts at chains 0.20 / rest 0.31 / CARRY 0.20):
  this race is not only a CARRY-band question; fast chains against a slower rest close it.
- Cost: the restored UCMPI0 is per call; last answers moved +7 % (route 4) and -7 % (route 8), i.e. inside route scatter.
- **Recommendation for both shrink leads:** shrink the per-iteration delays, keep the loop-ENTRY compares (UCMPI0 here,
  UCMPI0 in xorshift C41) at their unshrunk sizes. With that, the remaining slow-CARRY exposure is the per-iteration loop
  test (ucmpi1 in xorshift, ucmpi2 in ipow: 166 ps on ipow route 11, C40), which is where route choice still matters.

## C42. With A13 (CARRY/F7 not pinned by any August loop time), the "redraw at the fitted CARRY/F7 band" step cannot narrow it: take C41's fix instead of waiting for the fit (shard C, 2026-11-17 19:50 UTC)
- A13 (shard A, 18:28): on the August board bitstreams, moving the CARRY/F7 band over {0.2, 0.39, 1.0} changes collatz /
  collatz64 per-iteration time by 0.00 ns -- in bundled data the cycle is set by matched delays (LUT chains), and the carry
  chains only have to settle inside them. So board LATENCIES can never place CARRY/F7; only a carry-chain-specific board
  measurement (a CARRY4 ring or delay line) could.
- The races that depend on that band are exactly the ones that decide item 35 (C36 / C38: ucmpi0 -> ucond_br2 goes from 408
  ps at CARRY 0.2 to 0 near 0.9). So the fit will leave item 35's weakest race where it is: anywhere in [0.2, 1.0].
- C41 removes the dependence at no speed cost: UCMPI0 = 10 keeps >= 916 ps (entry) and >= 387 ps (loop test) at CARRY 1.0 on
  8 routes. Recommendation: rebuild item 35 with UCMPI0 = 10 and pick the route by ucmpi1's slow-CARRY margin; the collatz
  (C37, >= 583 ps) and ipow (C40, >= 789 ps) x0.55 leads already keep their margin at CARRY 1.0.
- For A's fit: ipow's August bitstream can now be decoded too (C39's DSP48E1 path; run.sh picks it when the FASM has DSP
  config lines).

## C41. A near-free fix for item 35's weak race: UCMPI0 back to 10 (item 33's size) keeps >= 387 ps at CARRY/F7 1.0 on 3 routes, at no measurable cost; 8 is not enough (shard C, 2026-11-17 19:25 UTC; untrusted simulation)
ucmpi0 is the loop-ENTRY compare (once per call), so its matched delay is paid per call, not per iteration. Item 35's sizes
(fr4a_x55a) with only BD_SZ_..._UCMPI0 changed (6 -> 8, 6 -> 10), built here on seeds 21 / 2 / 4 (sizes files:
x55a with that one line edited; the netlist change reroutes, so each is a new route). steermargin.py at chains 0.20 / rest
0.31 (C36's worst corner), xor19 + xorlong; smallest settle gap, ps (runts = requests under which the condition moved):
| UCMPI0 | route | ucmpi0 -> entry steers, CARRY 0.2 / 0.6 / 1.0 | ucmpi1 -> loop steers, CARRY 0.2 / 0.6 / 1.0 |
|---|---|---|---|
| 6 (item 35) | 21 | 408 / 194 / **12, 10 runts** | 620 / 604 / 321 (C36) |
| 6 | 2 / 4 | C36: 114 / 124 at 1.0 | C36: **114, 2 runts** (route 2) / 622 |
| 8 | 21 (sdf c50cea4f) | 951 / 693 / 436 | 431 / 160 / **19, 6 runts** |
| 8 | 2 (c48e1518) | 730 / 523 / 289 | 1241 / 675 / 414 |
| 8 | 4 (4bfc5a87) | 1262 / 1016 / 771 | 1345 / 1083 / 822 |
| 10 | 21 (42b4fb4c) | 1424 / 1170 / 916 | 917 / 646 / 387 |
| 10 | 2 (f1da196a) | 1592 / 1370 / 1134 | 1026 / 1026 / 1026 |
| 10 | 4 (05a84ea0) | 1504 / 1275 / 1047 | 1337 / 1317 / 1046 |
Every run returned all right answers. Draws (your model, xor19, K 100r+1..8): 8/8 PASS on all six builds.
- **UCMPI0 10 on 5 more routes** (19:45; seeds 1 / 3 / 5 / 6 / 7, sdf 8f165305 / 9a68cb56 / b073c245 / d7201a17 / dca58e5f), CARRY
  1.0 corner: ucmpi0 2080 / 2250 / 1297 / 1700 / 1477 ps, ucmpi1 1202 / 1283 / 742 / 765 / 1701 ps, 0 runts; draws 8/8 each;
  last answer 25.97-27.44 us. Over 8 routes the worst is route 21's ucmpi1, 387 ps.
- **x55a10 (your cand3b file, same netlist) on seeds 8-13** (21:45; sdf 1f3323ed 22075b66 592d08a1 4a3bf9dd cf3572af
  a413481b): your K 100S+1..4 4/4 and slow-carry K 100S+51..54 (DRAW_XBAND 0.8,1.0 = your DRAW_CARRY) 4/4 on every route
  (48/48); at CARRY 1.0, rest 0.31 / 0.20: ucmpi0 >= 1005 ps, ucmpi1 >= 758 ps (route 11), 0 runts. Over 14 routes now
  (1-13, 21) the worst is route 21's ucmpi1, 387 ps; next 742. The farm repeat on 32 routes (c_c41x32) is queued.
- **Cost:** last answer on xor19, same 8 draws on seed 21: item 35 mean 26.98 us, UCMPI0 8 26.55 us, UCMPI0 10 26.76 us;
  seeds 2 / 4 at 10: 26.57 / 26.32 us. No cost visible above route scatter, as expected for a per-call delay.
- **But the loop test is the other half:** with UCMPI0 at 8 the new route 21 puts ucmpi1 -> ucond_br6 at 19 ps with 6 runts
  at CARRY 1.0 (UCMPI1 is 5 in every row), and item 35's route 2 already had it at 114 ps. ucmpi1 is per ITERATION, so
  lengthening it costs speed. With UCMPI0 10 its worst is 387 ps on these three routes; three routes are a sample.
- **Suggestion:** if item 35 goes to the board, take UCMPI0 = 10 (no speed cost) and choose the route by ucmpi1's margin at
  the slow-CARRY corner (formal can run steermargin on any route you name in under 10 minutes).

## C40. ipow x0.55 routes 3 / 5 / 8: 32/32 draws each; loop-steer settle margins >= 789 ps at all 8 corners, no runts (shard C, 2026-11-17 18:10 UTC; untrusted simulation)
Same builds as C39 (md5-identical to yours), ipow17 (reaches e = 0x7fffffff), formal's simx with the DSP48E1 decode.
- **Draws (your model, K = 100r+1..32):** route 3 32/32 (last answer 4.33-4.81 us), route 5 32/32 (4.11-4.64 us), route 8
  32/32 (4.35-5.01 us). Wilson lower bound 0.893 per route.
- **Settle margins** (steermargin.py, 8 corners as C36/C37; ps; 0 runts everywhere; all answers right at every corner):
| route | ucmpi0 (e > 0 entry) -> steers, worst / best | ucmpi2 (loop test) -> steers, worst / best |
|---|---|---|
| 3 | 1131 (ucond_br4) / 1828 | **789** (ucond_br8; chains 0.20 / rest 0.31 / CARRY 1.0) / 1593 |
| 5 | 1378 (ucond_br5) / 2321 | 1350 (ucond_br9) / 2239 |
| 8 | 1493 (ucond_br5) / 2066 | 2135 (ucond_br8) / 2952 |
- **8 more routes (20:00; seeds 1 2 4 6 7 9 10 11, sdf f0ea1d9f 65fe87c1 fa33c8ae 2064e904 8adfc041 e47afcf8 8ae050c7
  bc8ddf0f):** draws K 100r+1..8: 64/64 PASS (last answer 3.99-4.88 us). Slow-CARRY corner only (chains 0.20 / rest 0.31 /
  CARRY 1.0), ucmpi0 / ucmpi2 settle margins: 891/357, 1387/1468, 1074/398, 1300/1509, 453/1499, 695/516, 1176/1320, **617/166**
  ps; no runts. So over 11 routes ipow x0.55's loop test (ucmpi2 -> ucond_br6) goes down to **166 ps on route 11** (357 / 398 on
  routes 1 / 4): like collatz x0.55, the shrink is route-sensitive at the slow-CARRY end, and the board route should be
  chosen by this margin (3, 5, 8 keep >= 789 ps at all 8 corners).
- **Item 29 itself (the ipow board candidate, h4s3m, seed 19, sdf b521630f = yours; first time formal could run it):**
  K 1901-1932 32/32 PASS (last answer 5.52-6.19 us); settle margins ucmpi0 -> ucond_br4 3054-3951 ps, ucmpi2 -> ucond_br7
  4605-5894 ps over the 8 corners, no runts. So x0.55 spends ~2-3.8 ns of these races' margin (worst 789 ps on route 3).
- **Reading:** on these races ipow x0.55 keeps 0.8-1.5 ns at the worst corner of your box, more than collatz x0.55 (C37,
  >= 583) and far more than item 35 (C36/C38, ~0 at slow CARRY). The worst corner is again CARRY/F7 slow with fast chains.
  Not covered here: the select race at ipow's muxes (shard B's class) and the DSP's internal glitches (one arc per input
  group; prjxray's DSP arcs are faster than nextpnr's SDF, C39).

## C39. ipow in formal's simulator (DSP48E1 now decoded); your route-19 failure IS the F7-select bit: wrong at every corner as built, right with that one select set to the netlist's 0 (shard C, 2026-11-17 18:05 UTC; untrusted simulation)
- **New:** the margin tool now decodes DSP48E1 sites from the bits (formal/tools/margin/dsp/: wraps A's decoder, every
  register must be off, OPMODE/ALUMODE/INMODE/CARRYIN decoded from tie-offs and inverter bits, anything else refused;
  checked against routed.json on 4 routes and against x*y mod 2^32 on 2007 operand pairs per multiply, 0 mismatches).
  Delay: prjxray's DSP_{L,R} timing (A->P 0.9-3.8 ns), which is FASTER than nextpnr's SDF (A->P 5.4 ns, what your GLS
  uses); `DSP_SDF=` widens to it. On route 5 draws 501/502 the answers and their times are identical either way, and +10 ns
  on every P arc still passes (+20 ns fails): the multiply is not ipow's binding path on that draw.
- **Your ipow x0.55 routes, built here md5-identical** (seeds 3 / 5 / 8 / 19, sdf 0b333646 / e7c5057d / 70048ae0 /
  d63bfd80), ipow17, your draws: route 3 (301/302), 5 (501/502), 8 (801/802) PASS 2/2 each: no disagreement. 32 draws
  each and the loop-steer margins at 8 corners are running (next item).
- **Route 19 (your 11:51 attribution, which the audit marked UNVERIFIED):** formal's decode of the bits gives SLICE_X19Y65's
  F7AMUX select = constant 1 (AX has no active pip; the walker reaches VCC through prjxray's default BYP_ALT0 path), while
  the netlist cell (ushrsi0 mux7, the e >> 1 shifter) has S0 = GND. As built: your draws 1901/1902 FAIL, all FAST_MIN FAIL,
  all SLOW_MAX FAIL, the same 11/17 every time; each wrong answer is the right answer for e >> 4 (the shifter ends the loop
  early) -- a logic defect, not timing. With that one select forced to 0 in the decoded net (force_pin.py): 1901/1902
  PASS, FAST_MIN PASS, SLOW_MAX PASS. So the failure is the F7-select defect and nothing else that formal can see.

## C38. Item 35's weakest race against the CARRY/F7 band alone: the settle margin falls ~55-65 ps per 0.1 of band and reaches 0 at CARRY/F7 ~ 0.9 (shard C, 2026-11-17 17:55 UTC; untrusted simulation; for PROGRAM "First: where does the board sit")
For your fit of the LUT/routing band and the CARRY/F7 band as two numbers: what the second number does to item 35.
Board route 21 rebuilt here (sdf 9145cd49 = yours), vectors xor19 + formal/tools/margin/vec/xorlong.hex (rounds to 4095),
steermargin.py (C36's method: uniform bands, no scatter), chains at 0.20, CARRY4/F7/F8 band swept 0.2..1.0. Smallest
settle gap of the loop-entry condition (ucmpi0.uz_n3) before ucond_br2's request, and of the loop test (ucmpi1.uz_n41)
before ucond_br6/7, ps; runts = requests under which the condition moved:
| CARRY/F7 band | 0.2 | 0.3 | 0.4 | 0.5 | 0.6 | 0.7 | 0.8 | 0.9 | 1.0 |
|---|---|---|---|---|---|---|---|---|---|
| ucmpi0 -> ucond_br2, rest 0.31 | 408 | 354 | 301 | 247 | 194 | 137 | 72 | **8** | **12, 10 runts** |
| ucmpi0 -> ucond_br2, rest 0.20 | 490 | 436 | 383 | 329 | 271 | 207 | 142 | 78 | **14** |
| ucmpi1 -> ucond_br6/7, rest 0.31 | 620 | 620 | 620 | 620 | 604 | 539 | 473 | 408 | (C36: 321+) |
| ucmpi1 -> ucond_br6/7, rest 0.20 | 683 | 683 | 683 | 683 | 643 | 578 | 513 | 382 | 317 |
Every run returned all right answers (runts absorbed in formal's simulator, as in C36).
- **Reading:** the margin is nearly linear in the CARRY/F7 band: ~-55 ps per 0.1 (rest 0.31), zero near 0.9. If your fit
  puts CARRY/F7 where the August kernels put everything (0.22), item 35 keeps ~0.4-0.5 ns here (~2-3 median SDF errors of a
  ~2 ns path); at 0.5 about 0.25-0.33 ns; above ~0.85 it lives on absorbed runts. So the fit needs to bound CARRY/F7 below
  ~0.6 for this race to keep one median error of margin.
- **Identifiability note:** in this race the chains and the rest are at fixed bands; the CARRY band alone moves it. If the
  August kernels' per-iteration times depend on CARRY/F7 only weakly (their carry chains are a small part of an iteration),
  the board timings will pin the CARRY/F7 band loosely; a kernel whose loop is carry-dominated (collatz's 3n+1 select, the
  compares) is what pins it.
- Collatz x0.55 (C37, routes 20 / 3) moves by ~170 ps between CARRY 0.20 and 1.0 and keeps >= 583 ps at the worst corner.

## C37. Collatz x0.55 on your two EQUIVALENT routes (20, 3), col18: 64/64 draws each, loop-steer settle margins >= 583 ps at all 8 corners, no runts (shard C, 2026-11-17 17:25 UTC; untrusted simulation)
Built here, md5-identical to yours: nl6s3a_x55 + pre_eq2, seed 20 (sdf b2b0dad9), seed 3 (sdf d8884e45); nextpnr
9c732bc6303458df. Vectors: your col18 (inside the bench's 16-bit mask, peaks to 30 bits).
- **Draws (your model, formal's simx on the decoded bitstream):** route 20 K 2001-2064 64/64 PASS (Wilson 0.943-1.000),
  last answer 23.8-27.2 us; route 3 K 301-364 64/64 PASS, 22.7-26.0 us. Your 2001/2002 and 301/302 are among them: no
  disagreement.
- **Settle margins** (steermargin.py, C36's method: uniform bands, no scatter; all 8 corners of your box, chains / rest in
  {0.20, 0.31}, CARRY/F7 in {0.20, 1.0}); smallest gap of the condition before a request, ps; 0 runts everywhere; every
  corner returns all 17 right answers:
| route | ucmpi0 -> entry steers (ucond_br2/4), worst corner | best corner | ucmpi2 (n == 2 exit) -> ucond_br6, worst | best |
|---|---|---|---|---|
| 20 | **681** (ucond_br2; chains 0.20 / rest 0.31 / CARRY 1.0) | 1138 | 712 (same corner) | 1375 |
| 3 | **583** (ucond_br4; same corner) | 1073 | 1144 | 1771 |
- **Reading:** the 18-24 ps knife edge of C35 (x0.55 routes 4 and 8, one corner, col17) does not occur on the two routes
  you would take to the board: their worst corner keeps ~0.6-0.7 ns, about 3-4 median SDF errors (8.5 %) of a ~2 ns
  path, and below the August long-route error (~1 ns slow) only if the condition's path is that long. As with item 35
  (C36), the worst corner is CARRY/F7 at the slow end (1.0) with fast chains; the margin moves ~170 ps between CARRY 0.20
  and 1.0. Route choice matters for this shrink: pick 20 or 3, not 4 or 8.
- Files: the commands are in formal/JOURNAL-C.md (progress 17:25); the scripts are the margin tool's (draws.py via run.sh
  DRAWS=64 DRAW_MODEL=research, steermargin.py).

## C36. Item 35 (board route 21) at your model's slow-carry corners: its loop-entry steer runs with LIVE RUNTS -- the condition moves under the request on 5 of 23 calls; answers still right (shard C, 2026-11-17 11:20 UTC; untrusted simulation)
Redo of C33 / C34 after the audit's T143: all 8 corners of your box (chains, rest in {0.20, 0.31}, CARRY/F7 in {0.20, 1.0}),
vectors xor19 + formal/tools/margin/vec/xorlong.hex (rounds 4095, 4094, 2048, 2047), steermargin.py, uniform bands, no
scatter. Smallest settle margin of the condition before the request at the loop steers (ps), and runts = requests under
which the condition moved:
| route | ucmpi0 -> ucond_br2, worst corner | ucmpi1 -> ucond_br6/7, worst corner | all 8 corners: right answers? |
|---|---|---|---|
| 21 (board, 9145cd49) | **15 ps, 5 runts** at chains 0.20 / rest 0.31 / CARRY 1.0; 17 ps at 0.20 / 0.20 / 1.0 | 321 ps (0.20 / 0.20 / 1.0) | yes, all 8 |
| 4 (ee6304d0) | 124 ps (0.20 / 0.31 / 1.0) | 622 ps | yes |
| 2 (b2470514) | 114 ps (0.20 / 0.31 / 1.0) | **114 ps, 2 runts** (0.20 / 0.31 / 1.0) | yes |
With CARRY/F7 at 0.20, every route keeps >= 245 ps; the edge is the slow end of the CARRY/F7 band you have never measured.
- **Where (route 21):** the tight calls are at 4.37 us, 25.35 us and 27.23 us (gaps 15, 24, 57 ps), xor19 calls, not only
  the long rounds. ucmpi0 is the loop-entry test (per call), so these are calls whose entry compare ripples through the
  carry chain late.
- **Consequence:** the run still gives every right answer, and only fails when ucmpi0's condition is delayed a further
  1.03-1.13 ns at those corners (sideslack). The steer's runts are absorbed downstream in formal's simulator (transport
  LUTs with the 20 ps filter), as in your gate's resolver model and the audit's T136. Whether silicon absorbs a runt at a
  steer is exactly the open runt question (C19 / your BOARD-QUEUE item 2).
- **Reading:** at the slow-carry end of your model, item 35's board route works by absorbing steer runts, with no settle
  margin at all. The audit's T143 (140 ps at advA on long rounds) points the same way; formal's number is lower. If the
  board shows item 35 failing, this race is the first place to look; the fix is ucmpi0's matched delay (UCMPI0, item 33's
  size keeps 1.48 ns, C34).

## C33 / C34 / C35 correction (shard C, 2026-11-17 10:05 UTC): the margins are minima over ONE corner and short vectors -- OVERSTATED (audit T143)
The audit (T143, interim) reproduces formal's figure at formal's corner (ucond_br2 400 ps vs formal 321 ps at ucond_br7) but
finds lower inside the same model: advA (chains 0.20, rest 0.31, CARRY 1.0) puts item 35's ucmpi0 -> ucond_br2 at 264 ps
on xorshift_17 and 140 ps on rounds up to 4095. A slow "rest" delays the compare's condition more than the request, and
long round counts reach states xor19 does not. So "321-614 ps at the model's slow-carry corner" is not the model's minimum;
read C33-C35's numbers as upper bounds. Being redone over all 8 corners of your box (chains, rest in {0.20, 0.31}, CARRY/F7
in {0.20, 1.0}) with long-round vectors (formal/tools/margin/vec/xorlong.hex: rounds 4095, 4094, 2048, 2047).

## C35. Collatz x0.55 (every size): on 2 of 8 routes the loop-entry steer's condition settles only 18-24 ps before its request at your model's slowest-carry corner (shard C, 2026-11-17 10:05 UTC; untrusted simulation)
Your x55 sizes, routes 1-8, col17 (C29: 16/16 draws on each), steermargin.py on ucmpi0.uz_n4 -> ucond_br2/3/4 (C33's
method). Smallest settle margin per route (ps; no request ever has the condition move under it):
| route | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|---|---|
| all FAST_MIN | 724 | 577 | 559 | 134 | 300 | 820 | 422 | 192 |
| rest 0.20, CARRY/F7 1.0 | 841 | 614 | 658 | **24** | 216 | 946 | 451 | **18** |
- **Where:** the tight request is the zero-trip call n = 1 (route 8: ucond_br2 at 1.8927 us, ucond_br3 64 ps; route 4:
  ucond_br3 at 1.9093 us). That call's input was driven at ~0.42 us and was stable since, so the late condition is inside
  the kernel: the compare ucmpi0 on the value the loop header has just passed, against the steer's request through
  ucmpi0's matched delay -- the same race that fails x0.50 on routes 2 and 6 (C29). The next-smallest request on those
  routes has >= 397 ps.
- **Consequence:** adding delay to ucmpi0's last LUT, the run first fails at +218-234 ps (route 8) and +562-577 ps (route 4)
  at that corner (+327 / +515 ps at FAST_MIN): the steer tolerates a little lateness, but 18 ps of settle margin is far
  inside one median SDF error. Your draws pass there because CARRY/F7 at 1.0 with the rest at 0.20 is the edge of the box.
- **Reading:** collatz x0.55 is not uniformly one step above the edge: on routes 4 and 8 its loop-entry steer is on a
  knife edge at the slow-carry corner. If x0.55 goes to the board, pick a route by this margin (routes 1, 3, 6 have > 550
  ps at both corners), or keep UCMPI0 at its x0.70 size.
- The current board candidates on the same race (unshrunk sizes): item 31 (route 20, ucmpi0 -> ucond_br2/3/4) 1506 ps at
  FAST_MIN, 1970 ps at the slow-carry corner, 4676 ps at SLOW_MAX; item 32 (route 22, ucmpi2 -> ucond_br6) 2928 / 3806 /
  9001 ps. So the knife edge appears only with the x0.55 shrink.
- For comparison, collatz64 x0.55 (C31), ucmpi2 -> ucond_br6, routes 1-4: FAST_MIN 1338 / 818 / 1023 / 610 ps, slow-carry
  corner 1498 / 806 / 1029 / 454 ps: no knife edge on those four routes.

## C34. Item 35's sizes (fr4a_x55a) on 5 routes: loop-steer settle margins 166-341 ps at your model's slowest-carry corner (shard C, 2026-11-17 09:45 UTC; untrusted simulation)
Built here (nextpnr 9c732bc6303458df), xor19, steermargin.py (C33's method; no row has the condition moving under a request).
Draws: your K = 100r+1..8 on routes 1-4 all PASS (8/8 each); route 21 = C28. Smallest settle margin per route:
| route (sdf) | ucmpi1 steers, FAST_MIN | ucmpi1 steers, rest 0.20 + CARRY/F7 1.0 | ucmpi0 steers, FAST_MIN | ucmpi0 steers, rest 0.20 + CARRY/F7 1.0 |
|---|---|---|---|---|
| 21 (9145cd49, board) | 484 (br6) | 321 (br7) | 363 (br2) | |
| 1 (33852d52) | 601 (br9) | 341 (br9) | 674 (br2) | 394 (br2) |
| 2 (b2470514) | 272 (br6) | 323 (br6) | 541 (br2) | **181 (br2)** |
| 3 (7b649492) | 501 (br9) | 230 (br9) | 519 (br5) | 283 (br5) |
| 4 (ee6304d0) | 820 (br7) | 622 (br7) | 497 (br2) | **166 (br2)** |
- The race: the loop compares' outputs (ucmpi0.uz_n3, ucmpi1.uz_n41) against the requests of the steers they feed
  (ucond_br2/5 from ucmpi0, br6-9 from ucmpi1), both from the steer's join. Positive on every route at both corners.
- Scaled by the measured error: 166 ps is about one median SDF error (8.5 %) of a ~2 ns path, so on routes 2 and 4 at
  the slow-carry end this race has roughly one median error of margin, and less than the August data's long-route error
  (~1 ns slow). Your rule E rows for ucond_br2 on these routes would be the number to set beside this.
- Against item 33 (unshrunk fr4a, route 27, sdf 7f0c0592, built here; 8/8 draws): ucmpi0 steers 1480 ps (FAST_MIN) / 1527 ps
  (slow-carry), ucmpi1 steers 2075 / 2767 ps. So x0.55a spent ~1.2 ns of this race's margin (1.48 -> 0.32-0.36 ns on the
  board routes) to save ~2 ns per iteration (C28 / your shrink5).
- These are uniform-band margins on one draw each (no per-pip scatter). The board route (21) is not the tightest.
- Route 4 (the tightest) with 256 draws of your model (draws 1-256, per-pip scatter included): 256/256 PASS (Wilson lower
  bound 0.985). So the 166 ps margin does not turn into failures inside your model; it is the model's error that would.

## C33. Settle margins at the loop steers, in ps, for item 35 and the x0.55 shrinks (shard C, 2026-11-17 09:35 UTC; untrusted simulation)
steermargin.py: every LUT that reads the compare's output; per request rise, the time since the condition last arrived
at that LUT pin (arrival = source flip + copy and pin arcs at the corner; no scatter). Smallest over the whole vector set;
"runts" = requests under which the condition moved (0 in every row). Agrees with the audit's T139 on item 35's ucond_br2
(363 ps at FAST_MIN vs 264-485 ps).
| build (route, vectors) | condition -> binding steer | all FAST_MIN | rest 0.25, CARRY/F7 1.0 | rest 0.20, CARRY/F7 1.0 | all SLOW_MAX |
|---|---|---|---|---|---|
| item 35 (21, xor19) | ucmpi1 -> ucond_br7 | 600 ps | 419 ps | **321 ps** | 1830 ps |
| item 35 | ucmpi1 -> ucond_br6 | 484 ps | 739 ps | 685 ps | 1501 ps |
| item 35 | ucmpi0 -> ucond_br2 | 363 ps | | | |
| collatz x0.55 (2, col17) | ucmpi0 -> ucond_br2 | 577 ps | 672 ps | 614 ps | 1590 ps |
| collatz x0.55 (6, col17) | ucmpi0 -> ucond_br4 | 820 ps | | | 2282 ps |
| collatz64 x0.55 (4, c6418) | ucmpi2 -> ucond_br6 | 610 ps | 520 ps | **454 ps** | 1497 ps |
| collatz64 x0.55 (1, c6418) | ucmpi2 -> ucond_br6 | 1338 ps | | | 3914 ps |
(The 321 ps on item 35's ucond_br7 is one request of 1839; the next smallest is 923 ps.) Read these, not the C29 / C31 /
C32 sideslack numbers, as the margins: sideslack measures how late until a WRONG answer, which includes runts the model
absorbs. All rows are one route each, uniform bands; the per-pip scatter of your model (sigma 0.126 per pip) is not in them.

## C32. (note on C29 / C31 / C32 slack numbers) sideslack.py's numbers are CONSEQUENCE slacks (how much later until a wrong
answer); the settle margin at the steer (condition settled before the request) can be smaller, as on item 35's ucond_br2
(0.36 vs 1.08 ns). Read them as upper bounds of the settle margin.

## C32. Item 35's two loop compares, slack in ps in formal's simx (shard C, 2026-11-17 09:20 UTC; untrusted simulation)
Route 21 (sdf 9145cd49), xor19, sideslack.py: extra delay on every input arc of the compare's last LUT (its condition comes
later), uniform bands, no scatter, bisected to 16 ps; first failing extra:
| compare (last LUT) | all FAST_MIN | rest 0.25, CARRY/F7 0.6 | rest 0.25, CARRY/F7 1.0 | all SLOW_MAX |
|---|---|---|---|---|
| ucmpi1 (uz_n41, the loop test) | 0.61 ns | 0.69 ns | **0.42 ns** | 1.86 ns |
| ucmpi0 (uz_n3) | 1.08 ns | 1.42 ns | 1.17 ns | 3.20 ns |
- The tightest: ucmpi1's condition may come 0.42 ns later at the slowest CARRY band your model allows. That is the race
  xorshift's x0.40a / x0.50a failures were on (C24 / C25); at x0.55a it keeps 0.4-0.7 ns at the model's bands.
- **Against the audit's T139** (ucond_br2, fed by ucmpi0: 264-485 ps at the fast corners). Traced (09:30): in formal's own
  all-FAST_MIN run, at ucond_br2's pins (request p2 from ucond_br2_j, condition p3 from ucmpi0.uz_n3; arrival = source flip +
  path FAST_MIN), the condition settles >= **363 ps** before each of the 19 requests (next: 392, 392, 397, 399 ps) and never
  moves while a request is high: **agrees with T139**. The consequence slack is larger (1.08 ns) because between +0.36 and
  +1.08 ns the condition moves under a live request -- a steer runt -- and the answers still come out right in formal's
  simulator (as the audit saw in T136). Per CLAUDE.md, the number to use is the settle margin, 0.36 ns at FAST_MIN; the
  1.08 ns says only that the runts formal's model produces in between are absorbed downstream.

## C31. Collatz64 below item 32's sizes in formal's simx: x0.55 24/24 on routes 1-4 (63-bit trajectories); x0.50 fails route 4 via ucmpi2 (the 64-bit n == 2 exit compare) (shard C, 2026-11-17 08:30 UTC; untrusted simulation)
Sizes made with your shrink_sizes.py from collatz64_sizes_T4cdb_h4s3p (x0.55: 21 sizes moved, x0.50: 29). c6418 (full 64-bit
n, peaks 63 bits), your model, draws 1-6, host 12 ns.
| sizes | route 1 | route 2 | route 3 | route 4 | last answer (c6418) |
|---|---|---|---|---|---|
| item 32 (h4s3p), route 22 | | | | | 98.0 us (C30, 8/8) |
| x0.55 | 6/0/0 | 6/0/0 | 6/0/0 | 6/0/0 | 64.9-69.9 us |
| x0.50 | 5/0/1 | 6/0/0 | 6/0/0 | **2/4/0** | 68.2-73.0 us |
(PASS / FAIL / UNDECIDED; sdf x0.55 d70a99da d3a30a8c 0415dd53 3c6d6f4f, x0.50 8c0229a0 c1011df9 e686e1a5 1801a64e.)
- x0.50 is no faster than x0.55 on these routes, and fails on route 4 (results stop after 3 or 5 answers).
- **The path (route 4, chainfix.py, +2000 ps on one of 57 chains at a time, no scatter):** with every non-carry arc at band
  0.25 and CARRY4/F7/F8 at 0.6 the run fails and only `ucmpi2.udly` fixes it; with every arc at SLOW_MAX the run hits the
  event cap and only `ucmpi2.udly` clears it; with every arc at FAST_MIN it passes. ucmpi2 is the exit test n == 2 on 64 bits,
  an equality yosys built from LUTs into F7/F8 wide muxes (8 mux8 trees, final LUT ucmpi2.uz_n38; corrected 08:50: not a
  CARRY4 chain); UCMPI2 = 16 (h4s3p), 9 (x0.55), 8 (x0.50). The compare's mux tree against its shortened matched delay,
  failing when the F7/F8 band (the same unmeasured U[0.2, 1.0] class as CARRY4) is slow: the same kind of race as
  xorshift's x0.40a (C24).
- **The same race's slack at x0.55, in ps** (sideslack.py: extra delay on every input arc of ucmpi2.uz_n38, the compare's
  last LUT, i.e. the condition arrives later; uniform bands, no scatter; bisected to 16 ps; the run must pass at 0):
  | route | rest 0.25, F7/F8/CARRY 0.6 | rest 0.25, F7/F8/CARRY 1.0 | all SLOW_MAX | all FAST_MIN |
  |---|---|---|---|---|
  | 4 | 0.69 ns | 0.53 ns | 1.47 ns | 0.63 ns |
  | 1 | 1.86 ns | 1.69 ns | 3.97 ns | 1.34 ns |
  Route 4 is the tight one; its slack stays positive across the model's band range, and is 0.53 ns at the slowest F7/F8
  the model allows. (An injection outside the prjxray band; it says how much later this side may come, not a probability.)
- **Reading:** x0.55 looks like the collatz64 candidate formal's simulator would pick (no failure on 4 routes, ~30 % less
  time than item 32 on the same vectors, though item 32's number is from route 22). Keep UCMPI2 >= 9 if shrinking further.
  On your c6419 (inside the bench's domain) x0.55 routes 1-4 pass 6/6 each too (last answer 74.9-80.6 us vs item 32's
  113 us on route 22, C30).

## C30. Collatz64 item 32 (seed 22, sdf 842dd4d7) on c6419 and on 63-bit trajectories: 8/8 each in formal's simx (shard C, 2026-11-17 07:50 UTC; untrusted simulation)
Your model, draws 1-8, host 12 ns. c6419: 8/8 PASS (last answer mean 113 us). c6418 (your deleted file: n ~ 2^59, peaks at
63 bits, outside the bench's domain, driven by formal as the full 64-bit n; oracle 267 / 282 / 285 = your c6418.exp): 8/8
PASS. So item 32's kernel handles carries to bit 62 on these draws; the board's bench cannot feed such n.

## C29. Collatz below x0.55 in formal's simx: x0.55 clean on routes 1-8 (col17); x0.50 fails routes 2 and 6 at every corner; the path is ucmpi0 -> ulink_n1__1 (shard C, 2026-11-17 07:45 UTC; untrusted simulation)
Sizes: your x55 file, and x0.50 / x0.45 made with your shrink_sizes.py from nl6s3a (it reproduces your x55 file exactly).
Routes 1-8, col17 (full 32-bit n, no bench mask), your model, your K = 100r+1..4 plus formal draws. PASS/FAIL/UNDECIDED:
| route | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|---|---|
| x0.55 (16 draws) | 16/0/0 | 16/0/0 | 16/0/0 | 16/0/0 | 16/0/0 | 16/0/0 | 16/0/0 | 16/0/0 |
| x0.50 (12) | 12/0/0 | **0/12/0** | 11/0/1 | **2/0/10** | 12/0/0 | **0/11/1** | 12/0/0 | 12/0/0 |
| x0.45 (12) | **0/11/1** | **7/5/0** | 12/0/0 | **9/3/0** | 12/0/0 | **8/4/0** | 12/0/0 | **9/1/2** |
- **The race (routes 2 and 6 at x0.50):** fails with every arc at FAST_MIN, at band 0.25 and at SLOW_MAX, no scatter:
  right after the zero-trip call n = 1 the next call answers 0 or never answers. Adding delay to one chain at a time
  (formal/tools/margin/chainfix.py, 57 chains): only `ucmpi0.udly` and `ulink_n1__1.rdly` fix it, always at the same
  threshold (one request path, in series). Shortfall: route 2 0.2-0.4 ns at FAST_MIN, 0.4-0.7 at band 0.25, 0.7-1.0 at
  SLOW_MAX; route 6 0.4-0.7 / 0.7-1.0 / 1.5-2.0 ns. Sizes there: UCMPI0 8 -> 5 (x0.55) -> 4 (x0.50); ULINK_N1__1 2 -> 2 -> 1.
- **Reading:** collatz's edge lies between x0.55 and x0.50, one step below x0.55 (as for xorshift, C25). The failure at
  x0.50 is a every-corner shortfall on the loop-entry compare's request path, which a static check on that path would see.
  If you shrink below x0.55, keeping UCMPI0 >= 5 and ULINK_N1__1 >= 2 is what formal's simulator says to try first.
  x0.55's slack on this path is not measured yet. Route 4 at x0.50 hits the event cap on 10 of 12 draws (a livelock or a
  very long run; not traced).
- **Which signals race (route 6, x0.50, band 0.25; failing run vs the same run with +1000 ps on ulink_n1__1.rdly,
  diverge.py):** the first storage / steer LUTs whose event counts differ, in order: ulink_n1__1.rdly.chain.g[0] ->
  ucmpi0.uor -> ucmpi0.udly.chain.g[0..3] -> the joins ucond_br2/3/4_j -> the steers ucond_br4, ucond_br2, ucond_br3
  (7 flips vs 4) -> ulink_n7 stage 0, ulink_n_falseResult_3 stage 0. So the loop-entry steers ucond_br2/3/4 receive their
  request (through ucmpi0's matched delay) before ucmpi0's compare result has settled, and fire both ways: your rule E at
  those steers (the C21 row named ucond_br3/4 from ulink_n1__1). Both sides start at the common launch ulink_n1__1.
- **x0.55's slack on the same race (added 09:05; sideslack.py, extra delay on ucmpi0.uz_n4 = the compare's last LUT,
  uniform bands, no scatter):** route 2: 0.80 ns (all FAST_MIN), 1.08 ns (rest 0.25, CARRY 0.6), 2.25 ns (all SLOW_MAX);
  route 6: 1.02 / 1.36 / 2.27 ns. With x0.50's shortfall (route 2: 0.2-0.4 / 0.4-0.7 / 0.7-1.0 ns), one step of
  UCMPI0 and ULINK_N1__1 is worth ~1.2-3 ns on this path: x0.55 keeps about one ns of it at the model's bands.

## C28. Item 35 (xorshift x0.55a seed 21, sdf 9145cd49) in formal's simx: your draws2 K 2101-2132 32/32, and 256/256 on draws 1-256 (shard C, 2026-11-17 06:25 UTC; untrusted simulation)
Built in formal's sandbox with the same toolchain (nextpnr 9c732bc6303458df; sdf md5 equals yours). Your model, xor19, host
12 ns after each acknowledge. Draw for draw with your draws2: no disagreement. 256 further draws: no failure (95 % Wilson
lower bound 0.985). Last answer (xor19) 24.8-28.8 us. Formal's decode keeps FFs opaque (C23): not a check of FF-mux bits.

## C27. col17 in formal's simx (no bench mask): item 31 and x0.55 return the right counts for 31-bit-peak trajectories (shard C, 2026-11-17 06:00 UTC; untrusted simulation)
Your 05:39 correction: the bench masks n to 16 bits. Formal's simx drives the kernel boundary itself with the full n, so
col17 tests the kernel. Route 20, your model, draws 1-6, fixed host: item 31 (sdf 7aefc4bd) 6/6 PASS, x0.55 of every size
(sdf b2b0dad9) 6/6 PASS, including 77671 -> 231, 94959 -> 301, 109881 -> 309 (oracle kernels.py from kernels/collatz).
So the long carries are right on these draws in the kernel; the board's bench cannot feed them. If full-range correctness
of the kernel matters beyond the bench's domain, formal can run such vectors; col17 is kept at formal/tools/margin/vec/.
The C26 correction below stands for col14 (blind to long carries), not for col17.

## C26 correction (shard C, 2026-11-17 05:45 UTC): formal's "x0.55 clean on 8 routes" is col14-limited
Your 05:07 result (item 31 x0.55 route 20 fails col17's three 30-31-bit-peak vectors) applies to C26 as well: c_shrink2 ran
col14 only, whose trajectories stay below ~21 bits, so its 32/32 on 8 routes says nothing about the long carries. Read C26's
x0.55 row as "no failure on col14", not as margin. Formal's col17 runs (c_shrink7, your shrink7 mirrored) are queued on the
full farm; the same check on item 31's own board route is being run locally. Also from C26's x0.40 failures (c_x40col2,
c_x40r12, untrusted simx): routes 20 and 7 pass with slower delay chains (a shortened matched delay losing to its logic);
route 12 fails at every uniform corner (all arcs FAST_MIN, all SLOW_MAX), so on that route x0.40 is wrong with no scatter at
all -- a static (rule A-like) failure, not a draw-model one.

## C26. Collatz item 31's sizes in formal's simx: clean to x0.55 on 8 routes (as your shrink2); first failures at x0.40 (shard C, 2026-11-17 01:05 UTC; untrusted simulation)
Your model, draws 1-32, col14, fixed host. fm_c_shrink2 (your shrink2 sizes) and fm_c_shrink2b (x0.40-0.10 made with your
shrink_sizes.py from nl6s3a inside the task; files `collatz_sizes_T3cdb_nl6s3a_fx*` exist only there). PASS / FAIL / UNDEC.:
| factor | route 20 | route 3 | route 7 | route 12 | more routes |
|---|---|---|---|---|---|
| 0.85 / 0.70 | 32/0/0 | 32/0/0 | 32/0/0 | 32/0/0 | |
| 0.55 | 32/0/0 | 32/0/0 | 32/0/0 | 32/0/0 | routes 1, 2, 4, 5: 32/0/0 each |
| 0.40 | **10/19/3** | 32/0/0 | **2/27/3** | **0/32/0** | |
| 0.30 | 32/0/0 | 31/1/0 | 32/0/0 | **8/22/2** | |
| 0.20, 0.10 | 0/32 | 0/32 | 0/32 | 0/32 | |
(Each factor is a different route, so the rows need not be monotone.) Last answer (col14) mean: 16.5 us at x0.85,
13.4 us at x0.55, ~12.5 us at x0.40. Your shrink2: x0.85-0.55 8/8 on routes 20, 3, 7, 12: agree. **Reading:** as for item
33 (C25), the first failure in formal's simulator lies between x0.55 and x0.40; x0.55 is clean on 8 of 8 routes. The
failing races at x0.40 are not traced yet.

## C25. Your shrink5 (item 33 x0.55a / x0.50a, routes 1-32) in formal's simx: x0.55a 1024 / 1024; x0.50a fails rarely on routes 7 and 18, at slow-carry draws (shard C, 2026-11-17 00:45 UTC; untrusted simulation)
Farm fm_c_shrink5: per route your draw numbers K = route x 100 + 1..4, plus formal's draws 1-28; your model, xor19, fixed
host. Formal's decode keeps FFs opaque (C23), so your FFMUX-FLAG routes (50a_29) are not judged here.
- **Draw for draw (your K):** every one of your 4-draw sets passes in formal too (all 64 routes x factors where you have
  results): no disagreement.
- **x0.55a, 32 routes x 32 draws: 1024 / 1024 pass.**
- **x0.50a, 32 routes x 32 draws: 1016 / 1024.** Failures only on route 7 (draws 5, 10, 21 of 28: a hang after 7 answers,
  twice; a wrong value at vector 8 once) and route 18 (draws 4, 5, 10, 12, 21: a hang after 5 answers). Their CARRY4 / F7 /
  F8 band is 0.95-0.99 except draw 12 (0.58): the compare's carry chain at the slow end of your unmeasured U[0.2, 1.0]
  against the shortened UCMPI matched delays -- the same race as x0.40a (C24), now rare.
**Reading.** Both simulators put item 33's first failing factor (with the counter's add kept) between x0.55a and x0.50a:
formal finds it at x0.50a on 2 of 32 routes with ~2-4 % of draws; your 4 draws per route are too few to see a rate that
low. x0.55a is clean in both, one step above the first failure; the margin there depends on how slow CARRY4 really is
(the one band your model has never measured). A board run at x0.55a would be the measurement that settles it.

## C24. Your shrink3 / shrink4 sizes for item 33 in formal's simx: x0.40c passes everywhere; x0.40a and x0.30a fail on most routes (shard C, 2026-11-17 00:00 UTC; untrusted simulation)
Same builds (sdf md5s equal yours on every route compared), your model, draws 1-32 per route, xor19, fixed host 12 ns.
Farm fm_c_shrink34. PASS / FAIL / UNDECIDED (event cap) of 32:
| route | x0.40c | x0.40a | x0.30a |
|---|---|---|---|
| 1 | 32/0/0 | **1/26/5** | **0/25/7** |
| 2 | 32/0/0 | **13/6/13** | **4/10/18** |
| 3 | 32/0/0 | 32/0/0 | **11/11/10** |
| 4 | 32/0/0 | **0/32/0** | **0/31/1** |
| 5 | 32/0/0 | 32/0/0 | 32/0/0 |
| 6 | 32/0/0 | **14/17/1** | **0/22/10** |
| 7 | 32/0/0 | **7/20/5** | **1/31/0** |
| 8 | 32/0/0 | **26/6/0** | **0/13/19** |
| 9 | 32/0/0 | 32/0/0 | **8/11/13** |
| 10 | 32/0/0 | 32/0/0 | **0/32/0** |
| 11 | 32/0/0 | 32/0/0 | 31/1/0 |
| 12 | 32/0/0 | **13/16/3** | **17/8/7** |
| 13 | 32/0/0 | 28/0/4 | 31/0/1 |
| 14 | 32/0/0 | **2/28/2** | **0/31/1** |
| 15 | 32/0/0 | 32/0/0 | **0/26/6** |
| 16 | 32/0/0 | **12/18/2** | **0/9/23** |
Also every-size x0.30 / 0.20 / 0.10: route 2 32/0/0, 0/28/4, 0/24/8; route 5 8/20/4, 0/19/13, 0/24/8.
**Against yours so far (your draws are K = route x 100 + 1..4, not 1-32, so this compares rates, not draws):** x0.40a
route 14: you 2/4, formal 2/32 (agree: it fails). x0.30a route 9: you 3/4, formal 8/19 decided (agree: it fails).
x0.40a route 7: **you 4/4, formal 7 of 27 decided** -- if formal's rate held, 4/4 has probability ~0.005: a disagreement.
x0.40a routes 2 and 8: you 4/4, formal 13/19 and 26/32 decided: not decisive with 4 draws. Routes 3, 5, 9-11, 13, 15
agree (all pass). **Reading:** in formal's simulator, shrinking UCMPI0 / UCMPI1 with the rest (x0.40a) breaks item 33 on
about 10 of 16 routes, while keeping them (x0.40c) passes all 16. So the compares' matched delays are the part that
cannot be cut, in this model -- which bears on your 22:02 correction ("the compares' long carry is simulated"): simulated
or not, formal's draws say their current sizes are needed. Your x0.40a failures on route 14 point the same way.
**Next (running, fm_c_shrink4k):** the same builds with YOUR draw numbers (K = route x 100 + 1..4), for a draw-for-draw
table; then a trace of route 4 (0/32 in formal) to name the race.

**Addendum (00:25 UTC): draw for draw, with YOUR draw numbers (fm_c_shrink4k; P pass, F fail, U formal event cap).**
| build | your draws | formal, same K |
|---|---|---|
| x0.40a route 12 | 1201 F, 1202-1204 P | 1201 F, 1202-1204 P (exact) |
| x0.40a route 14 | 1401 P, 1402 F, 1403 P, 1404 F | 1401 F, 1402 F, 1403 U, 1404 P |
| x0.40a route 16 | 1601 F, 1602 P, 1603 F, 1604 P | 1601 F, 1602 F, 1603 F, 1604 P |
| x0.40a route 7 | all P | 701 U, 702 F, 703 U, 704 F |
| x0.40a route 2 | all P | all U (event cap) |
| x0.30a route 9 | 901 P, 902 F, 903 P, 904 P | 901 F, 902 P, 903 P, 904 U |
| x0.40a routes 3, 5, 6, 8-11, 13, 15; x0.30a route 11 | all P | all P (13: 1302 U) |
So the two simulators agree on WHICH routes break when the compares are shrunk (12, 14, 16, 9 at x0.30a), and on 4 of
the 9 failing draws exactly; they differ on route 7 (formal fails, you pass) and on single draws of 14, 16 and 9. Both say
x0.40a is not safe on every route. **The race (fm_c_x40a4, route 4, draw 1):** the 4-round call returns the seed itself
(0 rounds), i.e. the loop test (`i < n-1`, compare ucmpi1) sends the token to the exit; it fails the same with the chain
band at 0.31 or 0.40, the rest at 0.20, no pip scatter, and gets further only with the CARRY4/F7/F8 band at 0.20. So it is
the compare's carry chain (CARRY4 band, the unmeasured part of your model) against its shortened matched delay (UCMPI).

## C23. Your shrink1 (item 33 sizes x0.85 .. x0.40, routes 27 / 2 / 5 / 9) in formal's simx: formal finds the first timing failures at x0.40 on routes 2 and 9; your x0.55 failures are the FF-mux defect formal cannot see (shard C, 2026-11-16 23:30 UTC; untrusted simulation)
Same builds (sdf md5s equal yours), your model, draws 1-64 (yours 1-8), xor19, fixed host 12 ns. Farm fm_c_shrink1.
| factor | route 27 | route 2 | route 5 | route 9 |
|---|---|---|---|---|
| 0.85 | you 8/8, formal 64/64 | 8/8, 64/64 | 8/8, 64/64 | 8/8, 64/64 |
| 0.70 | 8/8, 64/64 | 8/8, 64/64 | 8/8, 64/64 | 8/8, 64/64 |
| 0.55 | **you 0/8 (NOT EQUIVALENT, FFMUX-FLAG), formal 64/64** | 8/8, 64/64 | 8/8 (NOT EQUIVALENT, ffmux-clean), 64/64 | **you 0/8 (FFMUX-FLAG), formal 64/64** |
| 0.40 | 8/8 (NOT EQUIVALENT), 64/64 | running, **formal 22 PASS / 24 FAIL / 18 undecided** | running, formal 64/64 | running, **formal 1 / 63** |
- **x0.55 routes 27 and 9:** your gate fails 11/19 on every draw, the same way, and your fasm_equiv / ffmux_scan flag the
  bitstream. Formal passes them 64/64 because **formal's decoder treats slice flip-flops as opaque** (it simulates LUTs,
  muxes, carries and routing; an FF output stays at its initial value unless the harness drives it). So a formal PASS says
  nothing about FF-mux / packing defects; your fasm_equiv and ffmux_scan remain the only checks for them (as your PROGRAM
  says). Not a timing disagreement.
- **x0.40 routes 2 and 9:** formal's failures are timing: they change with the draw (wrong values from vector 6 to 11,
  hangs after 5-6 answers, some draws at the event cap). Route 27 passes in both of us. **Prediction for your running
  tasks:** route 9 fails most draws, route 2 about half, route 5 passes. A miss there is a disagreement to trace.
So in formal's simulator item 33's matched delays can go to x0.55 on all four routes (x0.40 on 2 of 4); the first timing
failure is between x0.55 and x0.40, and it is route-dependent.

## C22. (00:10 UTC: your draws1 is complete; final: 0 disagreements on candidates, 1 on the control -- +3000 draw 15) The disagreement table, your draws1 vs formal's simx on the same routes and draws: no disagreement so far (shard C, 2026-11-16 22:20 UTC; both untrusted simulation)
Same route (sdf md5 equal), same draw K and its bands (Random(7919K+17), checked against your logs), your vectors.
| candidate | your GLS (draws1, finished draws) | formal simx (fixed host; draws 1-32, and 1-128) | disagreements |
|---|---|---|---|
| item 33 fxa s27 | 32 / 32 | 32 / 32 | none |
| item 27 fxd s2 | 32 / 32 | 32 / 32 | none |
| item 31 fcsel3a s20 | 32 / 32 | 32 / 32; 128 / 128 | none |
| item 28 fcsel3m s20 | 32 / 32 | 32 / 32; 128 / 128 | none |
| item 30 fc64sel3 s10 | 32 / 32 | 128 / 128 | none |
| item 32 fc64sel3p s22 | 32 / 32 | 128 / 128 | none |
| item 29 ipow | 24 / 24 | not decodable (DSP48E1) | -- |
Your control (fxd s2, ucond_br6's condition +3000 / +8000 ps by SDF injection) has no counterpart yet: formal's
simulator reads the bitstream, not the SDF, but simx can add the same delay to the same pins (an `I` injection). I will
run it when your +8000 half reports, so the two controls compare.
**Your control, in formal's simx (fm_c_ctl1, 22:25 UTC):** item 27 fxd s2, the condition input of ucond_br6.u$LUT6 / LUT5
(pin 1, from ucmpi1.uz_n41, the arc your sdf_inject regex selects) + PS, your model and draws:
| injection | your GLS | formal simx |
|---|---|---|
| none, draws 1-32 | (candidate row c1) 32 / 32 | 32 / 32 |
| +3000 ps, draws 1-16 | 16 / 16 | **15 / 16: draw 15 hangs** after 17 correct answers (before 0x12345678, 100 rounds) |
| +8000 ps, draws 17-32 | 0 / 16 | **0 / 16**: every draw returns the 3-round value again at vector 6 (2497366906 for vector 5's 2064144800 ...) |
So formal's model fails your +8000 control as you require, and it disagrees with your gate on ONE draw: +3000, draw 15
(bands chain 0.2157, rest 0.3099, cells 0.3674). That is the first row of the disagreement table; I will trace it.
**The disagreement measured (fm_c_ctl2 / fm_c_ctl4, 23:05 UTC).** On draw 15 the hang does not depend on the runt filter
(the same at w 0, 20, 30, 40); it is a threshold: +2000 and +2500 pass, +3000 hangs, +3500 fails after 4 answers. The
threshold injection (bisection to 31 ps; a run counts as FAIL only on a RESULT MISMATCH) over your draws 1-32:
**+2906 to +4000 ps, median +3281.** At or below +3000: draws 15 (+3000), 21 (+2906), 27 (+2968), 31 (+2906). Draw 8 gives
no verdict at +3500 (event cap, 3 tries). So formal's model puts this steer's slack (condition vs request, plus what the
rest of the circuit tolerates) about 0.1-0.6 ns above +3000 on most draws, and below it on four. **Ask:** your threshold
on a few draws (15 and one with a high formal threshold, e.g. 4 or 24 at +3500), or at least your verdict at +3000 on
draws 21, 27 and 31. If yours sits well above +3000 everywhere, the two models' delays on this path differ by a few
hundred ps, and that is the calibration question to settle (prjxray pip delays in formal's decode vs your xray.sdf).
Both simulators agree that every candidate passes every draw. Neither has shown the model can fail a known-bad build
under YOUR parameters (formal: xf2_1, nc64_7 64 / 64 each); under the wider fid parameters formal's simx fails them in
~2-3 % of draws (C20). So "1.00" from either of us is weak evidence until the model is shown to fail something real.

## C21-RETRACTED. Item 30's "token split" was formal's harness offering n = 97 before its data (shard C, 2026-11-16 21:55 UTC)
**C21 below is withdrawn.** fm_c_x30ps put the race in picoseconds: at ucond_br3 the request (pin 4, from the join)
rises at 3,537,286 ps in both runs; the condition (pin 3, ucmpi0.uz_n4, computed from the kernel INPUT n) moves at
3,535,148 with a 1-ps host and at 3,538,491 with the 12-ns host. The 12-ns host moved n at 3,535,019 (12 ns after
n = 1's acknowledge fell), but formal's simulated host had already raised the request for n = 97 at 3,530,886, 1 ns
after the previous answer: **a host that presents its data after its own request**, which no real host does
(bench / PS writes the operand, then requests). The thresholds fit this: hosts up to 8 ns pass, 16 ns and more fail.
simx is fixed (the request now waits for its data plus su; checked: with an 8-us host the old harness reported a false
MISMATCH on gcd_ps, the fixed one answers right). Every PASS in C20 / C21 stands (a later operand can only make it
harder); the item 30 failures, item 32's design s1 failure, and the rates in C21 are void. Reruns with the fixed host:
fm_c_draws6. Research's rule E row for this steer on item 30 (skew.py -v, unchanged): ucond_br3/4 +1947 raw, -1331
guarded (launch ulink_n1__1.ctl) -- a lead only, as before.

## C21. (WITHDRAWN, see C21-RETRACTED) Item 30 (collatz64 h4s3 s10, sdf 637ff02e) fails 5 of 32 of YOUR draws in formal's simulator: a token split at the entry steers after the zero-trip call n = 1 (shard C, 2026-11-16; untrusted simulation)
**Problem.** Your draws1, mirrored in formal's simulator of the decoded bitstream: your model (draw K = 1..32; bands
from Random(7919K+17) per class -- my values equal those your logs print for K = 1, 2, 9; region 0.02; per-pip 0.126),
the same routes (sdf md5s equal yours), your vectors (xor19, col14, c6415). Formal's LUTs: transport with the 20-ps
filter; host 12 ns after each acknowledge. Farm fm_c_draws4.
| build | draws passing |
|---|---|
| item 27 s2, item 33 s27, item 28 s20, item 31 s20, item 32 s22 (and item 26 s25) | 32 / 32 each |
| **item 30 s10** | **27 / 32: draws 5, 8, 12, 13, 21 fail** |
| BAD xf2_1, BAD nc64_7, pc64_7 (64 draws) | 64 / 64 each: your model's spread never reaches their races |
**The failure (all five draws the same).** Vectors 27, 1, 97, ...: answers 111, 0, then **0 again** for n = 97 (and 118
arrives later as an extra 4th answer), so the stream is one call behind from there on. Traced on draw 5 (fm_c_x30dbg,
fm_c_x30dbg2): the n = 97 call is offered at 3.5309 us; the entry steers `ucond_br3`, `ucond_br4`, `ucond_br2`
(SLICE_X16Y21.A6 / B6, SLICE_X16Y29.C6) fire twice where the passing variant fires once (first difference 3.5374 us),
then `ucontrol_merge1.uarb1` and `ulink_n8` / `ulink_n_index_11` carry two tokens: one copy leaves on the exit side
at once (the wrong 0 at 3.5462 us) and one runs the loop (118 at 6.82 us). The steers' condition was left at "exit"
by the zero-trip call; the request for the next call reaches the steer before the condition has moved. Your rule E
at the entry steers, after a zero-trip call.
**What it needs (variants of draw 5, bands b_c / b_r / b_cells = 0.217 / 0.225 / 0.987):**
- fails as drawn, with b_r 0.27, b_cells 0.50-0.90, no per-pip scatter, no runt filter (w 0), host 12 ns or 100 ns,
  and with vectors (1, 97);
- passes with **b_c 0.27** (delay chains slower), **b_cells 0.40**, **a 1-ps host**, or with (97), (27, 97), (2, 97).
So it needs the zero-trip call just before, delay chains near the fast end of your U[0.20, 0.31] and the CARRY4 / F7 /
F8 band at 0.5 or more (the part of your model you mark "never measured"). The filter and the pip scatter play no
part, so this is not a runt-pulse artefact of formal's LUT model.
**What I would like from you:** your draws1 result for item 30 on draws 5, 8, 12, 13, 21 (tasks 21-24 were still
running at 21:15 UTC). If your GLS passes them, this is the disagreement the owner asked for and the next thing to
trace (start-up, host model and the steer LUT model are the candidates). If it fails them too, item 30 should not go
to the board as is. Files: fm_c_draws4/7 (draws.txt), fm_c_x30dbg (variants), fm_c_x30dbg2 (diverge_*.txt,
boundary_fail.txt). Reproduce: `DRAWS=32 DRAW_MODEL=research run.sh` (formal/tools/margin/README.md).

**Addendum (21:30 UTC, fm_c_draws5: 128 of your draws per route, your vectors).** Item 30's board route: **108 / 128
pass (0.84, Wilson 95 % 0.77-0.90)**; all 20 failures are this split ([111, 0, 0 ...]). Item 30's design on seeds 1, 2, 3:
128 / 128 each. Item 32's design (h4s3p): board route s22 128 / 128; seeds 2, 3 128 / 128; **seed 1 127 / 128, the same
split**. Items 25, 26, 28, 31: 128 / 128. So the race is in the h4s3 / h4s3p collatz64 family and its rate depends on
the route; item 30's board route is the worst of the eight routes measured.

## C20. The board approximator in formal's simulator of the decoded bitstream: every board candidate 64/64; both known-bad builds fail some draws (shard C, 2026-11-16; untrusted simulation)
**Problem.** Your PROGRAM and ours (owner, 2026-11-16: "the board decides"): judge a build by the fraction of random
delay draws that return the right answers. This is the same question asked in formal's own simulator: the circuit
decoded from the bitstream's FASM (not the netlist), prjxray bands per pin, transport LUTs with the 20-ps runt filter
(H_RUNT(20); no metastability resolver), host 12 ns after each acknowledge, formal's start-up.
**Model (first run, before your FOR-FORMAL model was published):** your fid GLS parameters: every pin arc at
FAST_MIN + 0.38 (SLOW_MAX - FAST_MIN), times exp(0.16 N) per 10x10-slice region and exp(0.126 N) per arc. Your gate
vectors (xor19, col15, c6416), oracles from kernels/*.c (formal/tools/margin/kernels.py). `run.sh DRAWS=64`,
farm fm_c_draws1 / fm_c_draws2. Every rebuilt SDF md5 equals yours.
| build | sdf | PASS / FAIL / UNDEC. of 64 | last answer, mean (range) |
|---|---|---|---|
| item 27 xorshift s2 | a9bdac53 | 64 / 0 / 0 | 36.5 us (33.0-40.4) |
| item 33 xorshift s27 | 7f0c0592 | 64 / 0 / 0 | 36.0 us (33.0-39.5) |
| item 33's design, seeds 1 / 3 / 4 | 796b669f / .. | 64/0/0 each | 35.8 / 36.2 / 36.0 us |
| item 28 collatz s20 | d86bdde5 | 64 / 0 / 0 | 23.1 us |
| item 31 collatz s20 | 7aefc4bd | 64 / 0 / 0 | 19.3 us |
| item 25 collatz s24 | e001dc27 | 64 / 0 / 0 | 32.8 us |
| item 26 collatz64 s25 | 6982a9d5 | 64 / 0 / 0 | 100.1 us |
| item 30 collatz64 s10 | 637ff02e | 64 / 0 / 0 | 96.4 us |
| item 32 collatz64 s22 | 842dd4d7 | 64 / 0 / 0 | 88.1 us |
| item 32's design, seeds 1 / 2 / 3 | .. | 64/0/0 each | 91.4 / 84.7 / 83.2 us |
| **BAD xf2_1** | dc138ea2 | **60 / 2 / 2** | 43.6 us |
| **BAD nc64_7** | 98809562 | **62 / 2 / 0** | 165.6 us |
| pc64_7 (nc64_7's good neighbour) | acc06847 | 64 / 0 / 0 | 167.5 us |
The failing draws: xf2_1 draw 56 returns 2068339104 for xorshift(0x92d68ca2, 3) (bit 22 wrong) and draw 18 stops after
5 answers, both at the 3-round vector where your trace puts its ulink_n7 hold race; nc64_7 draws 18 and 38 return
wrong step counts (e.g. 133 for 6171, 862 for 77031). Deterministic: the xf2_1 task, run twice, gave the same draws.
**Correction (22:15 UTC, after C21-RETRACTED; fm_c_draws7, fixed host, same fid model):** BAD xf2_1 **61 / 1 / 2** (draw 56
was the harness artefact: it followed the zero-trip vector; draw 18 still fails, stopping after 5 answers); BAD nc64_7
62 / 2 / 0 unchanged (draw 18 is wrong at the first vector, 239 for 27); pc64_7 64 / 0. Under YOUR model (fm_c_draws4,
64 draws) all three pass 64 / 64, and with the fixed host every candidate route passes 128 / 128 (fm_c_draws5/6:
items 25, 26, 28, 30, 31, 32 and items 30 / 32's designs on seeds 1-3; items 27 and 33 32 / 32 in fm_c_draws4).
**Reading.** In this model the candidates are clean and the known-bad builds are below their neighbours, but only by
~3 % of draws: the model's spread rarely reaches the races that broke them at your FAST_MIN gate. A fraction of 1.00
over 64 draws says the failure rate is below ~6 % (95 %), not that it is zero. "Last answer" includes the 400-ns
reset and the host's 12-ns reaction per handshake; it is the whole vector list, not ns per iteration.
**Next (running, fm_c_draws3):** your draws1 exactly: your model (draw K = 1..32, bands from Random(7919K+17),
region 0.02, per-pip 0.126), your eval_task.sh routes, your vectors (col14, c6415). That gives the per-draw
disagreement table. Tool: `formal/tools/margin/draws.py`, `run.sh DRAWS=N` (README "The board approximator").

## C19. The "steer-cone" failures are runt request pulses into a link controller, at the edge of the 20-ps filter (shard C, 2026-11-16; search, untrusted)
**Problem.** Since C11 I have reported failures from "steer cones" (every arc into a steer/merge LUT slowed at once,
host 2 ns) at kappa 0.35-0.44, without naming the race. explain.py looked at the storage LUT where the failure
surfaced, and that LUT was not where the run went wrong. **New tool:** simx `--tcut T` keeps the slowed arcs slow
only for input changes before T. `formal/tools/margin/tcut.py` bisects T until run(T) fails and run(T-1) passes;
the first storage LUT that then differs is where the outcome is decided. It also traces the deciding pulse upstream
(`run.sh TCUT=1`). Farm fm_c_tcut1 (same routes as c_min1, builds rebuilt from your recipes), plus a local run on
item 25.

**Finding.** Every one of these failures has the same shape. A pulse 20-41 ps wide leaves a steer or merge LUT and
reaches a link controller's request pin while the request it gates is already high. In formal's transport-delay
model the pulse then circulates in the controller's own feedback loop (it oscillates with a period of 68-128 ps)
and the run fails.
| build | kappa (w 20) | pulse source -> controller | pulse width |
|---|---|---|---|
| item 27 xorshift s2 | 0.28 (PHYSICAL hang), 0.42 | ucond_br9 (SLICE_X16Y32.C6) -> ulink_n_trueResult_12.ctl | 37 / 32 ps |
| fcsel3m s2 | 0.37 | ucond_br5 (SLICE_X18Y26.C6) -> ulink_n_trueResult_4 st0 ctl | 20 ps |
| fcsel0 s24 | 0.37 | ucontrol_merge1.udly.chain.g[1] (SLICE_X18Y24.C6) -> ulink_n_index_11 st0 ctl | 20 ps |
| item 25 collatz s24 (local) | 0.62 | compare-tree F8 glitch -> SLICE_X16Y34.A5 -> ulink_n_falseResult_3 st0 ctl | 41 ps |
| item 25, w 0 | 0.38 | ucond_br6 (SLICE_X16Y26.A5, out = !A1 & A2, inputs 3 ps apart) -> ulink_n_falseResult_7 st0 ctl | 1 ps |

On item 25 (the case traced end to end) the steer's condition comes from a compare tree whose F8 mux glitches for
29-47 ps (its select and its data input arrive at different times). In the all-fast reference that glitch reaches
the steer about 900 ps before the request, and the steer masks it. With the cone at 1.62 x fmax it arrives after the
request, so the steer passes it on as a request pulse. This is your rule E (the select or condition reaches the
steer before the request it gates), broken by a glitch rather than by a late final value.

**What this means.**
- Two of the w=20 rows fail on pulses EXACTLY 20 ps wide, the H_RUNT threshold. The others are 32-41 ps. These
  kappas measure the filter setting as much as the circuit. At w 0 the same cones fail on 1-ps pulses.
- Whether such a pulse sustains an oscillation in a LUT feedback loop on silicon is a question about the device, not
  about routing. Formal's model says yes for any pulse wider than w, because it has no pulse shrinkage. These rows
  should NOT be read as races with a picosecond slack, and I do not rank builds on them. The binding races I
  reported with picosecond slack (C13/C16 feedback, C11/C18 latch holds) are two-path races and are unaffected.
- A question for you: can your GLS show a 20-40 ps pulse on a ctl input (`ulink_*.ctl` pin from a cond_br / merge
  delay LUT)? If your gate passes such pulses with transport interconnect, a forced one (a pulse injected on
  ucond_br9's output while ulink_n_trueResult_12's request is high) would show whether your model also oscillates.
Files: fm_c_tcut1/*/tcut_*.txt on claude/cluster; tool formal/tools/margin/tcut.py; JOURNAL-C 07:2x-07:4x.
**Correction to C11/C15 wording:** the c_min1 explanations of minimised w=0 rows ran the wrong row (explain.py took
the w=20 row's arc set). Their "not a two-path race" verdicts are void; this item replaces them.

## C18. Board candidates 29-32 (your FOR-FORMAL 5feabe72), with your host and with a 1-ps host (shard C, 2026-11-16; search, untrusted)
Farm fm_c_margin_bq29: every race class, each broken race traced at your SDF; hosts at 1 ps and 12 ns; files in
`formal/tools/margin/out/farm_bq29_*`. Kappas only order the search.
- **item 32 (collatz64 h4s3p s22, sdf 842dd4d7).** The first finite failure, with either host, is your ulink_n13 hold
  race: `ulink_n13.lat.pair[4]` (LUT5); common launch `ulink_n13.ctl`; path A, ctl -> the latch's enable: 1 LUT + 6 routing
  arcs, 972 ps at the fast-band maximum, **SDF 1752 (routing 1600)**; path B, ctl -> `uack` chain (3 LUTs) -> `umux1.uya` ->
  `ulink_n_falseResult_5` stage 1 ctl -> its latch -> `umux1` data -> the ulink_n13 latch's data pin: 8 LUTs + 43
  routing, SDF 5613. Slack +987 ps worst in-band, **+3861 ps at your SDF** (1.46 x the worst short-ring error). A KERNEL
  race, same structure as items 26 and 28 (C14); keeping ULINK_N13_UACK at 3 leaves it nearly 4 ns at the SDF here.
  ulink_n28 does not appear among the races the search breaks up to 0.45. Hangs (kernel acks a/b, not start) from
  0.44 (a steer cone, not traced). The falseResult_7 controllers: +838 ps at the SDF (fbslack), as on item 28's routes.
- **item 30 (collatz64 h4s3 s10, sdf 637ff02e).** No finite failure up to 0.45 with either host; a livelock at 0.44
  (12-ns host) and hangs from 0.41 (steer cones, not traced). falseResult_7 controllers +838 ps at the SDF.
- **item 31 (= fcsel3a s20):** C15 (uselect0's capture holds to 0.45; falseResult_7 stage 0 controller +174 ps worst
  in-band, +764 at the SDF).
- **item 29 (ipow h4s3 s19, sdf 4a92cdf3): not analysed.** Its multiplier is a DSP48E1, and formal's bitstream decoder
  refuses DSP sites (it models LUTs, MUXF, CARRY4, flops and latches only). A margin for item 29 needs a DSP48 model.

## C17. Your select negative controls (research/data/selneg) in formal's model: the request-join injections never fail; the same select at the mux DATA LUTs fails from +6 ns (shard C, 2026-11-16; search, untrusted)
`formal/tools/margin/selneg.py` (simx with an extra delay on chosen arcs; farm fm_c_selneg2; outputs
`formal/tools/margin/out/farm_selneg2/`). Same routes as yours (items 27, 28, 26; rebuilt, SDFs = yours), every other arc
at its prjxray fast-band minimum (your FAST_MIN column), host releasing operands 12 ns after the acknowledge, transport
delays everywhere. Two injections from the select link's latch (`lat.odd`):
- **join**: into `umuxN.uj0` / `uj1` -- your arcs, as your README describes them;
- **data**: into the mux's 32 data LUTs (`umuxN.udat.*`) -- the select reaching the data late (rule E's race).
| mux | join +1 / +3 / +6 / +12 ns | data +1 / +3 / +6 / +12 ns | your gate, FAST_MIN, join +3 / +6 / +12 |
|---|---|---|---|
| item 27 umux0 | ok ok ok ok | ok ok **WRONG** no-verdict | PASS / no completion / no completion |
| item 27 umux1 | ok ok ok ok | ok ok no-verdict **WRONG** | PASS / FAIL 16/17 / no completion |
| item 27 umux2 | ok ok ok ok | ok ok ok ok | no completion / no completion / no completion |
| item 27 umux3 | ok ok ok ok | ok ok ok **WRONG** | PASS / PASS / PASS |
| item 28 umux0 | ok ok ok ok | ok ok no-verdict **WRONG** | no completion / no completion / no completion |
| item 28 umux1 | ok ok ok ok | ok ok no-verdict **WRONG** | no completion / no completion / no completion |
| item 28 umux2 | ok ok ok ok | ok ok ok **WRONG** | PASS / PASS / PASS |
| item 26 umux0 | ok ok ok ok | ok ok ok **WRONG** | -- / no completion / no completion |
| item 26 umux1 | ok ok ok ok | ok ok ok no-verdict | PASS / PASS / no completion |
| item 26 umux2 | ok ok ok ok | ok ok ok **WRONG** | PASS / PASS / PASS |
("no-verdict": event cap, typically a livelock; "WRONG": a wrong answer.)
- In formal's model a late select at the REQUEST join only delays the mux's request (the runs end later by about the
  injected time, and every answer is right): that is the safe direction for the bundle. Your gate fails on 20 of
  these runs. We checked one obvious difference and it is not it: your gate's interconnect is transport too
  (`build_ps.sh` compiles with `-DGLS_TRANSPORT_IC`). Others remain: your clocked PS host, your LUT cells (specify
  IOPATH: inertial at ~124 ps), your 17 vectors vs our 3-4. A trace of one failing run (item 28 umux0, join +3000,
  FAST_MIN: which handshake stops, and where) would tell which; formal can replay the same injection with a dump.
- The data-LUT injection is the arrival race: in formal's model it breaks item 27 umux0/umux1 and item 28 umux0/umux1
  from +6 ns, five more lines at +12 ns, never item 27's umux2; +3 ns passes everywhere. So on these routes the select
  can arrive 3+ ns late at the data LUTs before a capture breaks; your corrected rule E (arrival at the mux) is the
  check that matches this race.

## C16. C13's controller-feedback race over 32 routes, from your SDFs (shard C, 2026-11-16; static screen, untrusted)
`fbslack.py` on 16 routes of item 28's structure (fcsel3m, seeds 1-16) and 16 of item 27's (xorshift pre_dec fr4, seeds
1-16), rebuilt on the farm (fm_c_fbroutes; table: `formal/tools/margin/out/fbroutes/table.txt`). Slack = B (the fastest SDF
return from the controller's output to another of its pins) - A (its own feedback interconnect + IOPATH), at your SDF.
| controller | routes | median | min (route) | max |
|---|---|---|---|---|
| `ulink_n_falseResult_7.many.stage[0].u.ctl` (item 28's structure) | 16 | +1119 ps | +906 (s1) | +1402 |
| `ulink_n_falseResult_7.many.stage[1].u.ctl` | 16 | +1117 | **+764** (s4, s14: feedback via 5 routing arcs, A 772) | +1124 |
| `ulink_n_index_11.many.stage[0].u.ctl` (select link) | 16 | +2269 | +1774 | +2715 |
| `ulink_n_index_15.many.stage[0].u.ctl` (item 27's structure, select link) | 16 | +1397 | **+845** (s2 = item 27's own route) | +1813 |
- On 12 of the 16 fcsel3m routes the smallest controller slack anywhere in the kernel is one of the falseResult_7
  stages (0, 1 or 2); on the xorshift routes it is most often the select link `ulink_n12__1`'s controller (+706 to +1118).
- The feedback interconnect A is 295 ps when the placer keeps it in the slice (A = 419 with the LUT) and about 650 ps
  when it leaves it (A = 772): that single placement choice moves the slack by ~350 ps, and the fast-band worst split
  (C13, C15) by more. Route minimum over all 32 routes: +684 ps (fcsel3m s10, `ulink_n8` stage 1 ctl).
- So at your SDF this race has 0.7-1.4 ns everywhere we looked, about 1-1.6 x the worst short-ring error of a path that
  long. The dynamic runs (C13, C15) show where it bites: inside the fast band, when the feedback route is the long
  one (fcsel1 s24 +45 ps, fcsel3a s20 +174 ps). A check that keeps every controller's feedback inside its slice, or
  that requires B - A above a guard, would remove the tail.

## C15. Your two asks of 2026-11-16 (FOR-FORMAL 1b00b6ae): C10's routes with a 12 ns host, and fcsel3a seed 20 (shard C, 2026-11-16; search, untrusted)
`formal/tools/margin/run.sh` with `HOSTDELAY=12000` (the host moves the next operand 12 ns after the acknowledge it
reacts to; still a Spec.Env behaviour), every race class, each reported race traced to two paths and timed at your SDF
(farm fm_c_margin_r12; files there and in `formal/tools/margin/out/`). The kappas only order the search.
**C10's routes, 12 ns host.** The falseResult_3 stage-0 races C10 reported are gone on every route (they were
input-hold races against a 1-ps host, as the audit and C11 said). What the search still breaks:
| route | first finite failure (kappa) | the race, in ps | hang (kernel acks a/b, not start) |
|---|---|---|---|
| fcsel2 s1 (5b538ca5) | none <= 0.45 | -- | 0.37: `ulink_n_falseResult_7` stage 1 ctl feedback (4 routing arcs) vs rdly g[0] -> stage 2 ctl -> back: +132 worst in-band, **+904 SDF** |
| fcsel2 s2 (fb1efc41) | 0.44, a steer cone (not traced to two paths) | -- | 0.45 |
| fcsel1 s24 (afab5445) | none <= 0.45 | -- | 0.09: falseResult_7 st0 ctl feedback (5 routing arcs): **+45** worst in-band, +406 SDF (C13) |
| fcsel1 s1 (4445b56c) | 0.42: a fork near `ulink_n_falseResult_9` stage 0's latch (SLICE_X17Y54.D6 pin 0 direct vs pin 4 through 2 LUTs) | +111 worst in-band, +657 SDF | 0.40 |
| fcsel0 s24 (bb5fbbdb) | 0.37, a steer cone (got [0]; not traced) | -- | -- |
**fcsel3a seed 20 (7aefc4bd).** 1-ps host: the first race is again the input-hold race at falseResult_3 stage 0 (through
the host: +393 worst in-band, +1216 SDF). 12-ns host: no single-route or capture race below 0.45; the falseResult_7
controllers hang the kernel: stage 0 from 0.24 (no filter): feedback 1 LUT + 5 routing (SDF 772) vs rdly g[0] -> stage 1 ->
back (SDF 1536): **+174 ps worst in-band, +764 ps at your SDF** (0.71 / 1.06 x the worst short-ring error); stage 1 from
0.44: +399 / +1117. **uselect0's line** does not appear among the races our search breaks up to 0.45 on this route
(single routes, whole data cones, steer cones); its own slack in ps (its data vs its request) is not computed yet --
the tool explains races it breaks, and this one it did not break.
**fcsel3a seed 20, capture races swept to kappa 0.90 (12-ns host; fm_c_margin_usel2).** The first one broken (0.46) is
the select link's own latch, `ulink_n_index_11.many.stage[0].lat.odd`, against `ucontrol_merge1`'s bundle: common launch
`ucontrol_merge1.uarb1.ustate`; path A (data): `uarb1.ugrant` -> merge1's data LUT -> latch pin: 3 LUTs + 12 routing,
740 ps fast mid, SDF 1555; path B (enable): `ustate` -> merge1's matched delay `udly.chain.g[1]` -> the link's ctl ->
latch enable: 4 LUTs + 16 routing, 850 ps, SDF 1985. Slack **+110 ps fast mid, +430 ps at your SDF (0.46 x the worst
short-ring error), and -93 ps at the worst split inside the fast band** (A at its band maximum, B at its minimum). So
merge1's matched delay (two elements here) covers its data by about 0.1-0.4 ns. uselect0 is on neither path, and on none of the
paths explained for the other captures that fail up to 0.90 (ulink_n14__1 at 0.82, +1679 ps SDF; three others at
0.84-0.88 with 2.2-9.6 ns of SDF slack; three more traces were rejected as inconsistent). **uselect0's line itself (farm c_margin_usel3, `conenames.py`):** the only capture whose data cone runs through
uselect0 is `ulink_n_falseResult_9.many.stage[0]` (32 latch bits; cone includes uselect0's data LUTs and `uselect0.uz_n29`).
With that whole cone slowed to (1+k) x its fast-band maximum and everything else at (1-k) x the minimum, the kernel is
correct at k = 0.45 (20 ps filter; fm_c_margin_r12 task 7) and the run at k = 0.90 is undecided (event cap). So
uselect0 at 7 holds its capture far beyond every race above in this search. Its slack in ps is not computed (the tool
traces races it breaks). **Checked (farm c_verify1): this race alone does
NOT fail** -- with exactly path A slowed to (1+k) x its fast-band maximum and everything else at (1-k) x the minimum,
the kernel is correct at every k from 0 to 0.45. The -93 ps split is arithmetic on two path sums; the latch does not
lose a value from it on these vectors. The cone failure at 0.46 needs more of the data cone slow at once. Same
structure on item 27 (C12): +1418 / +1423 ps SDF there.
**fbslack.py agrees.** Run on the farm's SDFs, the static screen gives the same controller slacks as the dynamic traces:
fcsel3a s20 st0 ctl +764 ps, fcsel2 s1 st1 ctl +904 ps (both identical to explain.py). So `fbslack.py BUILD.sdf --grep .ctl.`
is a 5-second check of this race on any route of yours.

## C14. The ulink_n13 race (item 28's and item 26's first finite failure) in picoseconds: a kernel race with 2.5-3.1 ns of slack at your SDF (shard C, 2026-11-16; search, untrusted)
Traced by `tools/margin/explain.py` (trigger chains; farm fm_c_explain6). KERNEL race on both: the enable of a
`ulink_n13` latch bit against the NEXT value reaching its data pin after ulink_n13's acknowledge reopens the upstream link.
| build | path A: ulink_n13.ctl -> enable pin | path B: ctl -> uack chain -> umux1.uya -> falseResult_5 st1 ctl -> its latch -> umux1 data -> data pin | slack mid / worst in-band / SDF | x 8.5 % / x 47 % (SDF) | your row |
|---|---|---|---|---|---|
| item 28 (lat.pair[6] LUT6) | 1 LUT + 7 routing: 609 ps mid, SDF 1142 | 6 LUTs + 34 routing: 1958, SDF 4273 | +1348 / +965 / **+3131** | 8.6 / 1.56 | H +1337 (enable 1241, data 2628); hold_bits ulink_n13 min 1566 ps |
| item 26 (lat.pair[6] LUT5) | 1 LUT + **12 routing**: 964, SDF 1975 | 8 LUTs + 38 routing: 2179, SDF 4523 | +1215 / +710 / **+2548** | 6.6 / 1.20 | (not looked up) |
| fcsel3m seed 24 (item 28's structure; host 2 ns): `ulink_n10__3.lat.pair[20]` (LUT5), launch `ucond_br7.uack` | ulink_n10__3.ctl -> enable: 2 LUTs + **22 routing**: 1518 mid, SDF 3337 | ufork8 -> ulink_n10__4 ctl -> ufork3 -> umux0.uya -> falseResult_9 st1 ctl -> its latch -> umux0 data -> pin: 8 LUTs + 48 routing: 2930, SDF 6373 | +1413 / +670 / **+3036** | 5.6 / 1.01 | (not looked up) |
- Your rule H and our trace agree on the enable side (1241 vs 1142 ps at the SDF) and differ on the data side (2628
  vs 4273): our path B is the chain that actually fired in the run (through umux1 and falseResult_5's stage 1 latch);
  your H takes the earliest possible sender, which can be shorter. Both say clean by more than a nanosecond.
- The kappa (0.42 on item 28, 0.26 on item 26) is only this slack's ratio: the race is lost once (1+k) x path A's
  fast-band maximum exceeds (1-k) x path B's fast-band minimum: k = (1872 - 1162) / (1872 + 1162) = 0.23 on item 26.
  Item 26 sits lower because its enable route is 12 routing arcs long, not because its kernel is closer to failing at
  the SDF. For the audit (T119, replay correct with this arc at 1.26 x FAST_MAX and the kernel at 0.74 x FAST_MIN):
  formal's prjxray fast band puts path A at [1162 max] and path B at [1872 min] ps; if the audit's FAST_MIN for
  path B's routing is larger than prjxray's, the replay keeps a positive margin (393 ps there), which would explain it.

## C13. A race none of your rules checks: a link controller's own feedback against the next stage's acknowledge (`ulink_n_falseResult_7` stage 0; shard C, 2026-11-16; search, untrusted)
The hangs in C12 (the kernel acknowledges a and b, never start, and stops) come from one controller,
`ulink_n_falseResult_7.many.stage[0].u.ctl` (a C-element LUT that reads its own output). Traced by `tools/margin/explain.py`
(farm fm_c_explain4; KERNEL race: neither path goes through your host):
- Common launch: that controller's output.
- Path A (must arrive first): its own feedback route back into it (the state it holds).
- Path B: through stage 0's request delay `rdly.chain.g[0]` (one element) to stage 1's controller and back into stage 0's
  controller as the acknowledge.
| route | path A (feedback) | path B (rdly g[0] -> stage 1 ctl -> back) | slack mid / worst in-band / your SDF | x 8.5 % / x 47 % (SDF) | kappa (search order) |
|---|---|---|---|---|---|
| fcsel1 seed 24 (sdf afab5445) | 1 LUT + **5 routing arcs**, 384 ps mid (SDF 851: routing 727) | 3 LUTs + 10 routing, 570 (SDF 1257) | +186 / **+45** / +406 ps | 3.8 / **0.69** | 0.09 |
| item 28 = fcsel3m seed 20 | 1 LUT + 2 routing arcs, 290 (SDF 419) | 3 LUTs + 12 routing, 744 (SDF 1536) | +454 / +335 / +1117 ps | 8.6 / 1.55 | 0.36 (no filter) |
- So the controller has to see its own new state before stage 1's acknowledge comes back, and with stage 0's request
  delay at one element that return is only three LUTs long. On fcsel1 seed 24 the placer gave the feedback route five
  routing arcs (727 ps at your SDF), and the slack inside the fast band is 45 ps. Your rows on that route:
  H +936 / I +467 at stage 1's ctl and F (matched-delay drain) rows elsewhere. None of them is this race (a C-element's
  own feedback against the acknowledge it waits for). We have not found it in your rule set.
- What the failure looks like: the controller misses its state for one event, the link's handshake is left half done,
  and the kernel stops after acknowledging a/b but not start. Formal's frozen Spec calls such runs vacuous; on a board
  this is a hang. A proposed fix in formal's Spec (`SpecWF`) would count it.
- Suggestion: a check that every link controller's feedback route is shorter than its shortest acknowledge return,
  with a guard, on every route. It is a one-route quantity, so it moves with placement (5 routing arcs on one seed,
  2 on another): measure it over routes.
- **A screen you can run on any route now:** `python3 formal/tools/margin/fbslack.py BUILD.sdf --grep .ctl.` (formal's
  branch, needs only your nextpnr SDF, ~5 s): for every LUT that reads its own output, A = its feedback interconnect +
  that pin's IOPATH, B = the fastest SDF path from its output back to another of its pins, slack = B - A, also as a
  multiple of 8.5 % and 47 %. On item 25's route it gives `ulink_n_falseResult_7.many.stage[0].u.ctl` A 419, B 1536,
  slack +1117 ps through rdly g[0] -> stage 1's ctl, the same race and numbers explain.py traced dynamically on item
  28. B is the fastest STRUCTURAL return, so a small slack is a race to check, not a failure. Outputs for items 23, 25,
  BAD xf2_1 and gcd_ps: `formal/tools/margin/out/fbslack/`.

## C12. Item 27 (xorshift board candidate) and item 28: the races formal's tool breaks first, in picoseconds, beside your rows (shard C, 2026-11-16; search, untrusted)
All from farm runs of `formal/tools/margin/run.sh` with every race class (single routes, whole data cones, steer
cones) and the checks of C11; files `origin/claude/cluster:results/fm_c_margin_all2/<task>/` and
`fm_c_explain3/7/explain_*.txt`. "Slack" = path B minus path A from their common launch (positive: the required order
holds), at the prjxray fast-band midpoint, at the worst split inside the fast band, and at YOUR nextpnr SDF; then as a
multiple of the ring data's median error (8.5 %) and worst short-ring error (47 %, 7-link rings). The kappa column is
only the order in which our adversary breaks things.
**item 27 (sdf a9bdac53 = your fxd seed 2).** No single route breaks it in our range; two capture races do:
| latch (capture) | common launch | path A (must be first) | path B | slack mid / worst in-band / SDF | x 8.5 % / x 47 % (SDF) | your rows | kappa |
|---|---|---|---|---|---|---|---|
| `ucontrol_merge0_olink.lat.odd` | `ucontrol_merge0.uarb1.ustate` | data: 3 LUTs + 11 routing, 767 ps (SDF 1397) | enable via the olink ctl: 6 LUTs + 27 routing, 1484 (SDF 3173) | +716 / +451 / **+1776 ps** | 6.6 / 1.2 | none found in fxd seed 2's files (your fr3 build fxf4_s seed 2 has H +3492 at the olink ctl) | 0.39, wrong count (2 of 4 answers), checked |
| `ulink_n_index_15.many.stage[0].lat.odd` (a select link) | `ucontrol_merge1.uarb1.ustate` | data: 3 LUTs + 12 routing, 787 ps (SDF 1540) | enable: 6 LUTs + 25 routing, 1284 (SDF 2958) | +498 / **+243** / **+1418 ps** | 5.6 / **1.0** | your hold_bits on fxd seed 2: the same LUT (SLICE_X14Y33.B6) is the tightest hold bit, min 1159 ps (fxf4_s, fr3: H +1394 at the st0 ctl) | 0.28-0.29: the kernel acknowledges a/b, not start, and stops |
(Update, farm c_verify1: with the host moving data 12 ns after the acknowledge, the olink capture race first fails at
kappa 0.61, not 0.39 as with a 1-ps or 2-ns host, and that 0.61 run breaks Spec.Env (not a counterexample). So although
both of its paths are inside the kernel, how early your host offers the next operand changes whether it bites.)
Both are KERNEL races: neither path goes through your host (unlike C10's and item 25's, which close through the host
releasing the next input; formal's tool now separates the two, `HOSTDELAY=`). Both are setup (capture) races at the merge-arbiter's output: the arbiter's state flip reaches the latch's data through
3 LUTs and its enable through 6, so the bundling here is the difference of two short paths, about 0.5 ns. Your rules
H and hold_bits look at the other direction (hold) of the same latches; rule E looks at the mux select arrival; we have
not found a row of yours for this setup race at the latch's data pin. At your SDF the second race has a slack equal to
the worst error measured on short rings. Path A is the data path that is critical in the all-fast reference run; the
adversary slows the whole data cone, so the path that actually lost can be a longer one inside it (being traced). Not
yet checked on other routes of item 27 (one route is a sample).
**item 27's structure on 4 more routes (seeds 1, 3, 4, 5; sdf e2914f00, e6719b93, 32142fab, 2ae1a2b5; host moving
data 2 ns after the acknowledge, so kernel races only; farm fm_c_margin_x27r).** Seed 5 has the same capture race at
the merge1-arbiter-fed select-link latch: split `ucontrol_merge1.uarb1.ustate`, data 3 LUTs + 11 routing (SDF 1398 ps),
enable 6 LUTs + 24 routing (SDF 2821): slack **+1423 ps at your SDF (1.07 x the worst short-ring error)**, vs +1418 on
seed 2. So this race is about 1.4 ns at the SDF on two routes out of two where it shows. On all five routes the search
also breaks steer cones (a branch condition reaching its C-element late: 0.30-0.45) and finds partial-ack hangs
(0.23-0.31); the steer races are not yet traced to two paths (the tool reports them UNRELIABLE rather than guess).
**item 28 (sdf d86bdde5).** Besides A8's ulink_n13 race (your H +1337, hold_bits 1566 ps, kappa 0.42): from kappa 0.36
(no filter) the kernel can stop after acknowledging a and b but not start, at `ulink_n_falseResult_7.many.stage[0]`'s
controller reading its own output late (a feedback race). The same controller does this on fcsel1 seed 24 from kappa
0.09, on fcsel3m seeds 2 and 24 at 0.35-0.37, and on items 25 and 26 at 0.37-0.38. Formal's frozen Spec calls these runs
vacuous (A: `SpecWF`); on a board they are hangs. Picosecond form: farm c_explain4, running.
**Livelocks** (periodic, never answering; `simx --periodic`): item 28 at 0.42, item 26 0.38, fcsel3m s2 0.38, s24
0.40, item 27 0.35 (no filter).

## C11. What formal's margin tool now looks at beyond A8: whole data paths slow at once (capture races), livelocks, and three checker fixes (shard C, 2026-11-16; search, untrusted)
Item 28's single-route result is A8 (same farm builds, same numbers; C's run: `formal/tools/margin/out/farm_item28_fcsel3m_s20/`).
Per the owner's rule (PROGRAM.md, "A kappa is not a result") the kappas below only say which race our adversary
breaks first; the picosecond form of each race (both paths from their split, cells and routing, slack at your SDF,
your rule row) is what C builds next, in the tool.
- **Capture races (new class, `tools/margin/cones.py`, run.sh `CONES=1`).** A8's sweeps slow ONE route. A bundled-data
  capture fails when the whole data path into a latch is slow and its request path fast. Per link stage, the tool now
  slows the entire combinational cone into the latch bits (datapath, carry, mux data LUTs and the routes of their
  select inputs) and keeps everything else fast. `STEER=1` does the same for a C-element or steer reading data (a
  branch condition). On every collatz/collatz64 route tried, the first capture race the adversary breaks is the
  one-bit latch of **`ulink_n_index_11.many.stage[0]` (lat.odd)**, one of your select links, whose data cone is the
  index computation (~770-1550 arcs); on xorshift item 27 it is `ulink_n_index_15` stage 0 (also a select link) and
  `ucontrol_merge0_olink`'s latch. Checked so far: **item 27 fails as a capture at `ucontrol_merge0_olink`** (2 of 4
  answers, then quiet), where no single-route race fails in the same search range; fcsel3m seed 2 at
  `ulink_n_index_11` stage 0 returns a spurious first answer (106, then 111, 170 for want 111, 170, 350). These rest on
  the old checks; farm c_margin_all2 reruns all classes with the fixes below on items 28, 25, 27, 26, fcsel0 s24,
  fcsel1 s24, fcsel3m s2/s24.
- **Checker fixes that change what is reported (all in `tools/margin`, `tools/huff/envcheck.py`):** (1) runs where no
  20 ps runt filter is consistent with the delay windows are not behaviours and no longer count as failures; (2) a
  run where only the simulated harness broke the protocol (it released data on an acknowledge that then glitched) is
  re-run with a harness that holds data until its next request; (3) envcheck's "request low at the end" was stronger
  than the Spec; a run where your kernel acknowledged a and b but never start and stopped is now reported as
  PHYSICAL: a real harness hangs, but the frozen Spec is vacuous there (A proved it: `SpecWF.env_unsat_partial_ack`).
  Item 25 shows such hangs from steer-condition races without the filter.
- **Livelocks.** `simx --periodic` recognises a run that repeats for ever without answering; the tool reports it on its
  own line (liveness). On gcd_ps it finds the 0.36 livelock with period 79 ps, the period A's Lean proof found.
- **First race in picoseconds (tool: `tools/margin/explain.py`, run.sh now writes `explain_*.txt` for every reported
  race).** item 25 (sdf e001dc27), the race the adversary breaks first without the filter: latch
  `ulink_n_falseResult_3.many.stage[0]` lat.pair[12] (SLICE_X14Y55.A6). Common launch: that stage's `ctl` output
  (SLICE_X16Y38.A6). Path A, ctl -> the latch's enable pin: 1 LUT + 6 routing arcs, 550 ps at the prjxray fast-band
  midpoint (1243 slow-band). Path B, ctl -> 3 LUTs -> the kernel's input acknowledge (a_ack, SLICE_X17Y32.A6) -> the
  harness puts the next input on the bus -> 8 routing arcs -> the same latch's data pin: 1745 ps (4174), with the
  harness taking 1 ps. Slack +1196 ps = 8x the 8.5 % ring error (+838 ps at the worst in-band split). So it is a hold
  race through your harness: the kernel acknowledges its input before the latch holding it has closed, and only a
  harness that changes the data within about 1 ns of that acknowledge can break it. Formal's Spec allows a 0 ps
  harness; your clocked bench does not. Does any rule of yours look at a_ack against that latch's close? The same
  form for items 28, 26, 27 and fcsel3m s1/s2/s24 is on the farm (c_explain1); nominal-SDF slacks next (prjxray band
  midpoints for now).
- Not covered: two independent slow routes outside one cone, the slow corner, kappa_lo (none for any build).

## A18. Formal's decoder now has your RC tree (build_net RC_TREE=1): formal's arcs match your xray.sdf to ~1 ps per net, and both models' band positions coincide (kernels 0.216, rings 0.286); A17's translation is no longer needed with it (shard A, 2026-11-17 21:18 UTC; simulation, untrusted)
- tools-A/target/build_net.py, opt-in RC_TREE=1 (the default output is byte-identical, so the Lean proofs are
  untouched), uses prjxray's Elmore tree the way your xray_delay.py does:
  - routing node wire R / C summed over its tile wires;
  - buffered pips R / in_cap, pass pips R;
  - site output pin drive R and delay, input pin C;
  - the slice OUTMUX routing-BEL arc (AMUX-DMUX), which formal had at 0;
  - LUT route-through input pin delay.
- Checked against your xray.sdf on item 36 route s1 (tools-A/target/rc_tree_check.py). Formal routing plus site-pin
  delay minus your INTERCONNECT, median [p05, p95], FAST_MIN and SLOW_MAX alike:
  - 192 L-ring LUT -> LUT sinks: +1 [0, 2] ps (default build: -83 / -219);
  - 192 F7 select sinks: +1 [1, 2] (default: -99 / -190);
  - 3,884 other LUT <- LUT sinks: +5 [1, 11];
  - LUT <- FF: +2 [0, 5].
  The small positive bias comes from rounding each RC term up.
- Still short: FF CE / SR / D sinks, by 26-95 ps fast and 91-213 slow. You also charge the FF-side site muxes and pin
  delays, and formal's FFs are opaque. Not compared: site-internal sinks, constants, clocks.
- Effect:
  - Item 36 rings at x 0.288 now agree with your predicted.tsv within 1 % for every kind, the F7 rings included, so
    A16's 15 % F7 disagreement disappears under RC_TREE.
  - The August collatz per-iteration time needs b = 0.216 (yours: 0.222), collatz64 0.223, and gcd's long-pair
    difference 0.214. The audit's own GLS (T138 / T140) gives collatz / collatz64 0.223 / 0.226.
  - The 128 August rings need b = 0.286 (yours: 0.288). The per-ring spread is 0.274-0.302 (p05-p95), down from
    formal's earlier +-5 %.
- So with RC_TREE the two simulators sit in ONE coordinate system. The ring/kernel gap (0.29 vs 0.22) remains: it is
  in the silicon or the sessions, not in either model (A14).
- For C: decode with RC_TREE=1 and research's draw numbers then apply as they are (A17 is moot there). Without it,
  formal's arcs remain ~20 % fast.

## A17. For shard C and research: formal's draws use your band numbers on formal's arcs, which are ~20 % faster; in formal's own coordinates your draw range [0.20, 0.31] is about [0.365, 0.49] (shard A, 2026-11-17 21:08 UTC; arithmetic on A14 / A16, untrusted)
**Superseded in part by A18:** with build_net RC_TREE=1, formal's arcs match research's and no translation is needed.
- A14: the same measured silicon sits at 0.222 (kernels) and 0.288 (rings) in your model, and at 0.39 and 0.465 in
  formal's. Interpolating linearly between those two anchors, your draw range [0.20, 0.31] for chains and rest
  becomes ~[0.365, 0.49] in formal's coordinates.
- A16: the CARRY band means the same in both models: CARRY rings agree within 1-2 %, with the same swing. So CARRY / F7
  y needs no translation.
- C's draws.py and steercorners.sh draw chains and rest on [0.20, 0.31] with formal's arcs. Their LUT chains and
  routing therefore run ~20 % faster against CARRY than either model says the board does.
- For the races that decide item 35 (C36 / C38: a carry-chain condition against a request that waits on a LUT chain),
  that is the PESSIMISTIC side. The knife edge "margin 0 near CARRY 0.9" was measured with chains at 0.20 and rest at
  0.31 in formal's coordinates. At formal's board-faithful 0.365-0.49 it should move up, possibly past 1.0.
- Checked on one build (the measured August collatz, whose margins are large; tools-A/board/out/aug_board/
  collatz_steer_coords.txt), with C's steercorners.sh at CARRY 1.0:
  - entry steer (ucmpi0): 4,742 ps at C's 0.20 / 0.31, against 5,961-6,600 ps across formal's [0.365, 0.49];
  - loop steer (ucmpi2): 2,421 ps, against 3,023-3,610 ps.
  So the margin rises 25-49 % at the slow-CARRY corner. On item 35 the size of the shift is still a prediction, not
  a run. **Request to C:** steercorners.sh on item 35's route (and the x0.55 / x0.70
  leads) with chains / rest in (0.365, 0.49) x CARRY / F7 in (0.2, 1.0), next to the corners8 numbers already
  reported.
- For research: if your own GLS also places the knife edge at CARRY ~0.9 with chains at 0.20-0.31 in YOUR coordinates,
  that number stands as is. Only formal's runs need the translation.

## A16. Formal's pre-registered prediction for item 36 (CARRY4 / MUXF7 rings, research/board/carry s1 / s2), before any board run: formal agrees with yours on the LUT and CARRY rings and disagrees by ~15 % on the F7 rings (shard A, 2026-11-17 21:04 UTC; simulation, untrusted)
**Note (A18):** under build_net RC_TREE=1 formal's predictions match research's within 1 % on every ring kind, F7 included. The table below is the DEFAULT (no RC tree) build.
How it was made:
- Both routes were decoded from their FASMs with tools-A/target (all 64 rings per route found).
- tools-A/board/carry_ring_predict.py takes each loop as the shortest cycle from `inv` through the ring's own LUT,
  CARRY4 and MUXF sites plus routing, and splits it into CARRY/MUXF arcs and the rest.
- Files: tools-A/board/out/carry_rings/ (per ring, x 0.465 and 0.39; summary.txt).

Medians, ns (formal at x 0.465, the August ring b in formal's coordinates; yours at x 0.288, from predicted.tsv):

| route, ring | formal y 0.2 | formal y 1.0 | swing | yours y 0.2 | yours y 1.0 | swing |
|---|---|---|---|---|---|---|
| s1 L8 / L16 | 7.96 / 15.27 | same | 0 | 7.88 / 15.12 | same | 0 |
| s1 C1 / C4 | 6.15 / 6.92 | 6.81 / 7.97 | 0.66 / 1.05 | 6.65 / 6.78 | 7.22 / 7.72 | 0.58 / 0.94 |
| s1 C16 / C32 | 9.59 / 11.01 | 12.07 / 15.51 | 2.48 / 4.50 | 9.59 / 11.09 | 11.98 / 15.47 | 2.39 / 4.39 |
| s1 F8 / F16 | **7.24 / 13.87** | 9.77 / 18.93 | 2.53 / 5.06 | **8.48 / 16.19** | 11.01 / 21.23 | 2.53 / 5.04 |
| s2 (same pattern) | F16 13.74 | 18.87 | 5.13 | F16 16.24 | 21.33 | 5.08 |

- **LUT and CARRY rings: the two models agree** within ~1-2 % at x 0.465 vs 0.288. The CARRY swings agree within 5 %.
  So item 36's CARRY_BAND y will mean the same in both models.
- **F7 rings: formal is ~2.3 ns (15 %) shorter at every y, with the same swing.**
  - The MUXF7 arcs themselves are identical (S0 -> OUT 93 / 296 ps in both), so the difference is in the path around
    each F7: out through the slice's output mux, through routing, into the CX bypass pin.
  - prjxray's CX site pin has zero delay. The output pins carry drive resistances (AMUX 1,853 ohm vs the LUT output A
    1,326), which your RC tree multiplies by the downstream wire capacitance.
  - Formal's RC_ALL=1 closes only part of it: F rings go from 0.68 to 0.73 of your FAST_MIN, LUT rings from 0.78 to
    0.80.
  - Traced on route s1 (192 F-ring nets into S0, your xray.sdf against formal's routing): your INTERCONNECT is
    234 ps at FAST_MIN (smax 653), formal's is 126 ps (smax 460), and 145 ps with RC_ALL. The source cell makes no
    difference.
  - CORRECTED (same hour; the first wording blamed the BYP pip's R, which prjxray gives as 3,490 ohm against
    IMUX's 1,611 ohm): the same comparison on the 192 L-ring LUT -> LUT nets shows that the gap is general.
    - Your INTERCONNECT, minus formal's routing, minus prjxray's site-pin delay, is +40 / +56 / +85 / +86 / +83 ps
      for A1 / A2 / A3 / A4 / A5. On the CX (S0) nets it is +108 ps.
    - So formal's arcs lack ~40-110 ps of RC on EVERY net, not mainly on bypass pins. Your tree has the output-pin
      drive R x the whole net's C plus every node's wire RC; formal has only pip R x pip input C.
  - Why the F7 rings stand out: a LUT stage carries 100-170 ps of site pin plus IOPATH, which a single band
    position can stretch to cover the missing RC. An F7 stage is mostly routing, so the same band position leaves
    it short.
  - The same holds for any race whose two sides differ in routing share: formal makes the routing-heavy side look
    early by tens of ps per net, relative to a LUT-heavy side.
  - Fix candidate: build_net with research's RC tree (outpin R and node wire caps). Not done.
- **What the board will decide:**
  - Your fit and formal's differ by about 0.45 in the F7 band's y at a given period, so F8 / F16 discriminate between
    the models.
  - If the board's F16 sits near your numbers, formal under-prices the bypass path. That path carries every
    F7-select race, including C36 / C38's loop-entry steers, and formal would read those races as later-arriving
    selects than silicon has.
- Formal will fit item 36 after the run the same way it is written here:
  - x from the L rings;
  - y_carry from C16 / C32;
  - y_F7 from F8 / F16, by least squares on the median periods;
  - the two routes reported separately.

## A15. Formal's pre-registered prediction for the second ring route (ro_many_2, BOARD-QUEUE item 4), written before any board run (shard A, 2026-11-17 21:00 UTC; simulation, untrusted)
**Added (A18):** with RC_TREE=1, formal's periods at b 0.288 are 1.0019 of research's predicted.tsv (median; p05-p95 1.0013-1.0024): the two models now make the SAME prediction for this route, so the board run tests the shared model, not a disagreement (tools-A/board/out/ro_many_2_formal_rctree_predicted.tsv).
tools-A/board/out/ro_many_2_formal_predicted.tsv has, per ring of research/board/ro_many_2:
- formal's FAST_MIN and SLOW_MAX loop periods, decoded from that build's FASM;
- the period at b = 0.465 (the August ring route's median, A14);
- the period at 0.39 (the August kernels).
- Formal at 0.465 against research's predicted.tsv (0.288 in its model): median ratio 1.010 (p05 0.946, p95 1.059).
  The two models agree on the median and differ by about +-5 % ring by ring.
- What the board run will say: whether ONE b per model transfers across routes. If it does, the ring-to-ring spread
  shows which model prices individual routes better (on the August route: research +-1.8 %, formal +-5 %).
- With collatz_bench_gen in the same session (A14), it also settles whether the ring/kernel gap belongs to the day or
  to the builds.

## A14. Where the board sits in the band, and which measurement decides it. LUT vs routing: no August measurement separates them. CARRY/F7: no August measurement places it. Rings and kernels disagree by the same amount in both models, cause unknown (shard A, 2026-11-17 20:33 UTC, corrected 20:38; simulation, untrusted)
This answers PROGRAM ("Research says 0.22 to 0.29 and you said 0.75 to 0.9: say which measurement decides"). It also
records A13, which until now was only in JOURNAL.md (18:28; C42 cites it).
The data are the MEASURED August bitstreams (research/board/aug/builds, decoded by formal; names come from
tools-A/board/aug_synth.py) and the 128 August rings (research/board/ro_many_aug).
b is a position in each model's own [FAST_MIN, SLOW_MAX], so b values from the two models are not comparable as numbers.
In formal's arcs (build_net.py), the measured delays sit at:

| measurement | formal, one b | research, one b (yours) |
|---|---|---|
| collatz per iteration (board 92.7 ns) | 0.387 | 0.222 (full stack) |
| collatz64 per iteration (117.9 ns) | 0.383 | |
| gcd: (2^31-1, 2^31-2) minus (1, 1), 11.70 us; per-coefficient fit 0.387-0.405 | 0.396 | |
| ipow per iteration (60.85 ns; DSP48E1 decoded) | 0.409 | |
| isprime, n = 97 / 1009 minus n = 2 (8.1 / 40.3 us) | 0.389 / 0.388 | |
| 128 rings, median (p05 / p95) | **0.465** (0.420 / 0.512) | **0.288** (+-1.8 %) |

- **Kernels vs rings.** In both models the rings sit higher: +0.078 in formal's, +0.066 in yours. The kernels agree with
  each other to 0.026 (five kernels: 0.383-0.409; ipow and isprime added 20:52,
  out/aug_board/ipow_isprime.txt). The DSP band has no effect on ipow's per-iteration time (B_DSP 0 vs 1: 60.31 ns
  both), so it is not placed either, like CARRY/F7. Your RC-tree model fits the rings more tightly (per-ring spread 1.8 % vs formal's ~5 %), so for
  absolute LUT and wire delay it is the more faithful of the two. Formal's arcs are ~20 % faster in absolute terms.
- **LUT vs routing (b_lut for LUT cell arcs, b_route for pips and site hops; scale_net.py B_LUT).** Each kernel is linear
  in the two: per-iteration = t0 + aL b_lut + aR b_route, fitted from three simx runs. The LUT share of the span is
  0.61 / 0.64 / 0.66 for the kernels and 0.69 for the rings (p05-p95 0.62-0.77). That is nearly the same mix, so these
  measurements cannot tell the two bands apart:
  - Kernels alone give one line: b_lut 0.3 -> b_route 0.53-0.56; b_lut 0.4 -> b_route 0.35-0.39.
  - Rings alone, bootstrap 90 %: b_lut 0.35-0.43, b_route 0.55-0.72. The rms error falls from ~5 % to 3.0 %. The high
    b_route probably absorbs routing that formal underprices: 52k pips with no prjxray record are taken as 0 ps.
  - **No single pair fits both.** At the rings' pair, the kernels come out ~10 % slow (collatz 102.0 vs 92.7 ns).
    The joint fit (0.575, 0.092) leaves the rings at 5.9 % rms and the kernels up to 2.8 % off.
  - So the ring/kernel gap is not a LUT-vs-routing split.
- **WITHDRAWN 20:38: the rise/fall candidate.** The first version of this entry said every kernel delay LUT is a
  bd_delay FASTRISE (OR) stage. That came from a misread INIT. The routed cells are LUT1 buffers: INIT 2'b10, A1
  unconnected, e.g. uselect0.udly.chain.g[9].u. The chains are SYMMETRIC in collatz, collatz64, gcd, xorshift, ipow,
  isprime, gcd_ps, gcd_hw and ro_link_ps. A four-phase cycle therefore pays both edges through them, as a ring does,
  and an edge difference would not separate rings from kernels. The ring/kernel gap is UNEXPLAINED. Untested
  candidates:
  - load and routing that only the rings have (each ring node also drives the BUFG mux);
  - the measurement path;
  - a global difference between the ring run and the kernel runs (temperature or voltage on the day).
- **Added 20:57: the same stage is ~9 % slower in the ring build than in the kernels.**
  - In formal's arcs a ring stage and a kernel delay-chain stage are the same thing: median FAST_MIN LUT arc 154 ps and
    routing 38 ps (mean 55-61) in collatz, gcd and the rings alike (chainstage.py).
  - The rings' excess over the model at b = 0.39 is proportional to length: x1.088-1.095, ~74 ps per stage at 7, 15,
    31 and 63 links. It is per stage, not a readout constant.
  - Splitting each kernel into its delay chains and the rest (scale_net CHAIN / B_CHAIN), the four kernels fit best
    with the chains at b 0.35 and the rest at 0.52 (errors <= 0.9 %). With isprime added, five kernels give chains
    0.36 and rest 0.48 (errors <= 1.0 %). Bootstrap 90 % for b_chain: 0.29-0.43, which excludes the rings' 0.465.
  - Forcing the chains to the rings' 0.465 needs the rest at 0.19 and leaves errors up to 2.7 %. So the kernel data do
    not support "the chains run as slowly as the ring stages".
  - Same stage, different speed: the leading explanation is a difference between the two builds or sessions (ring
    build Aug 23 ~21:15 local, kernels Aug 24), not between kinds of stage. Not shown.
  - Data: out/aug_board/chain_vs_rest.txt.
  Neither model can represent a rise/fall difference anyway: the August collatz SDF has rise = fall on all 54,592
  entries.
- **CARRY/F7 (A13).** With LUT and routing at 0.39, moving CARRY4 and MUXF7/F8 over {0.2, 0.39, 1.0} changes collatz and
  collatz64 per-iteration time by 0.00 ns. The cycle is set by the matched delays, and the carry chains only have to
  settle inside them. No August measurement places this band, so the CARRY band of ~0.9 at which C38 / C35's races
  close cannot be confirmed or ruled out by the board data in hand.

**PROGRAM's "0.22-0.29 vs 0.75-0.9".**
- Formal's 0.75-0.9 is WITHDRAWN. It came from my tightened REBUILDS of the August kernels (A11). Their tighten loops
  did not converge, so their delay sizes differ from the bitstreams that were measured.
- On the measured bitstreams, formal says 0.38-0.41 and research says 0.22-0.29. These are the same silicon in two
  coordinate systems: formal's arcs are ~20 % faster in absolute terms than research's RC-tree arcs, so the same ns
  sit higher in formal's band.
- The two models agree on both shapes:
  - kernels lower than rings;
  - one b fits every kernel, within 0.026 in formal's coordinates and 1 % in research's.
- "A kernel is mostly carry chains where a ring has none" does not explain the difference. Moving CARRY/F7 over its
  whole band changes no kernel's per-iteration time (0.00 ns). The kernels' per-iteration time is ~73 % delay-chain
  LUT stages, the same stages the rings are made of.

**Rows for research/SIM-VS-BOARD.md** (formal's simx, the measured August bitstreams, one b = 0.39 for every arc;
F / S = all arcs at FAST_MIN / SLOW_MAX):

| kernel | measured | formal F | formal S | formal at b 0.39 | error |
|---|---|---|---|---|---|
| collatz, ns / iteration | 92.73 | 50.35 | 159.81 | 93.04 | +0.3 % |
| collatz64, ns / iteration | 117.89 | 64.43 | 204.16 | 118.92 | +0.9 % |
| gcd, (2^31-1, 2^31-2) minus (1, 1), ns | 11695 | 6305 | 19911 | 11611 | -0.7 % |
| ipow, ns / iteration | 60.85 | 32.41 | 102.16 | 59.61 | -2.0 % |
| isprime, n 97 minus n 2, ns | 8100 | 4411 | 13901 | 8112 | +0.1 % |
| isprime, n 1009 minus n 2, ns | 40335 | 21972 | 69250 | 40410 | +0.2 % |
| 128 rings, median period error | - | - | - | - | +8.8 % (rings slower) |

(xorshift is left out: the August README marks 25 of its board logs match=NO against the bitstream.)

**Which measurement decides:**
1. **For kernel margins: the kernel loop times, not the rings.** The kernel loop times share the kernels' edge mix and
   placement style; the rings do not. Until (2) is done, reading kernel delays at the ring b over-states their delays
   (safe for request delays, unsafe for data paths).
2. **The ring/kernel gap: a kernel and the rings measured in ONE session, with NO new build.** Load ro_many_top.bit
   and run ro_many_measure.py, then load collatz_bench_gen.bit and run its loop sweep, back to back on the same board
   within minutes (both bitstreams are on claude/research). If the rings still read ~9 % slower per stage than
   collatz's chains, the cause is in the builds; if not, it was the day. The cheapest slot is BOARD-QUEUE item 4
   (research/board/ro_many_2, the second ring route, not yet run): add the August collatz_bench_gen.bit and its loop
   sweep to the same session. Also useful: plus a ring whose
   nodes drive nothing but the next stage (rules out the readout load). research/board/aug/builds/ro_link_ps, a ring of
   bd_links that WAS built and has a routed JSON, is the closest thing in hand: a handshake ring with the kernels'
   cells. If it has a board period, formal can place it next. **ASK:** the ro_link_ps bitstream is on claude/research,
   but no board laps are. cells/hw/ro_link_fit.py reads build/hw/ro_link_sweep, and neither the August logs nor
   research/data hold it. If the owner's August sweep output (the "ring N: S stages L laps X ns/lap" lines) still
   exists, please push it. It is the only measurement in hand that crosses rings and kernels.
3. **LUT vs routing: rings whose routing share differs.** For example, the same N with stages forced one per tile
   against packed four per slice. That moves the LUT share from ~0.7 to ~0.4 or ~0.9, enough leverage for a two-band fit.
4. **CARRY/F7: a CARRY4 delay line or ring (C42),** or a kernel whose request path waits on a carry chain.

Files: tools-A/board/{ring_period.py, scale_net.py (B_LUT), twoband.sh, loop_latency.py, gcd_latency.py, aug_synth.py};
outputs tools-A/board/out/aug_board/ and ring_band.txt. Toolchain: none (decoded from the measured FASMs; prjxray arcs).
Not shown: (a) why rings and kernels differ; (b) anything about the August builds' sizes at other routes;
(c) a b with RC on all corners (RC_ALL changed the rings by little, A13).

## A12. REQUEST for the August board builds (shard A, 2026-11-17): the yosys and routed JSONs
For PROGRAM's "where does the board sit in the delay band?": formal's simulator decodes the FASM but names the kernel's
boundary (request, acknowledges, data buses) from \`<k>_bench_gen.json\` + \`<k>_bench_gen_routed.json\` +
\`build/gen/<k>_kernel_bench.v\`, \`<k>_bench_gen.v\`. Only FASM and SDF were pushed. If the owner's August build
directories still hold those four files per kernel, please push them next to the FASMs. Until then A is matching the
SDF's instance names to sites from the PS7 outwards (slower, may not be complete).

Note from shard C (2026-11-17 18:15 UTC), for A: the routed JSONs (plus .bit, .fasm, .sdf, .xdc, pnr/synth logs) of the
MEASURED August bench builds are already on claude/research under research/board/aug/builds/<k>_bench_gen/ (committed
2026-11-04; its README pairs every board log with its bitstream, match=yes for collatz, collatz64, gcd_bench_gen, ipow,
isprime). The yosys synth JSON and the gen Verilog are not there. ipow now decodes (C39: DSP48E1 path, run.sh picks it up).

## A11. Your draw model's band position looks ~35 % too fast against the gcd board data: the decoded August gcd design reproduces all 20 measured latencies at b = 0.39 of [FAST_MIN, SLOW_MAX] (shard A, 2026-11-16; simulation, untrusted)
**WITHDRAWN IN PART (A, 2026-11-17 ~04 UTC): the band-position claim does not hold up.** The same method on two
more August designs rebuilt from their measuring commits gives b = 0.745 for collatz (1b81a36f2; its tighten loop
converged: 35.7 ns of matched delay) and b = -0.03 for xorshift (648f3d106; loop did not converge, untightened
estimate shipped; the board's 49.6 ns per round is BELOW the simulated all-FAST_MIN 53.4 ns). gcd's 0.39 came from an
untightened rebuild too. The spread (-0.03 to 0.75) tracks whether each rebuild's matched-delay sizes match the
measured bitstream's, which were never archived; so these rebuilds cannot pin the board's band position, and "your
draws are ~25 % too fast" is NOT supported. What stands: within one design (gcd), the decoded circuit reproduces the
board's relative costs of its four loops and all 20 per-input latencies to 0.9 % RMS with one scale factor. Pinning b
needs a bitstream that formal has AND that ran on the board (the ASK below stands).
**Added: collatz64** (1b81a36f2, tighten loop converged, 41.5 ns matched delay): board 117.7 ns/step vs sim 44.7 /
141.7 -> **b = 0.752**. So the two rebuilds whose tighten loops converged (collatz 0.745, collatz64 0.752) agree; the
two that shipped bdc's untightened estimate (longer chains than a tightened build) give lower b (gcd 0.39, xorshift
-0.03), the direction expected if the measured August builds were tightened. A tentative reading only: b ~ 0.75 of
[FAST_MIN, SLOW_MAX] for kernels whose sizes plausibly match, i.e. the board slower than your U[0.20, 0.31] draws;
still rebuilds with today's toolchain, not the measured bits.

For PROGRAM's "the board decides": how close is formal's simulator (simx on the circuit decoded from the bitstream) to
the board? The only per-input board data: your `cells/hw/gcd_cost_results.tsv` (ca475ffdb, 24 pairs x 3 x 200 calls,
measured on the August `gcd_bench_gen.bit`, route and sizes not archived).
- Rebuilt gcd_bench_gen from ca475ffdb with today's cloud toolchain (its build_bench.sh, default and BD_SKIP_RULE_E=1:
  both ship bdc's untightened estimate, SDF dee2e292 / FASM 878c0858); decoded; each pair simulated alone with every
  arc at FAST_MIN and at SLOW_MAX; kernel latency = out0 request rise - request rise.
- Your four per-iteration costs (k 126.8, pre-ctz 124.3, main 158.0, inner ctz 114.9 ns, refitted from latmin/latmax)
  fall at b = 0.397, 0.398, 0.388, 0.396 of the simulated [FAST_MIN, SLOW_MAX] range: **one b for all four loops**.
  One b and one harness offset fitted to all 20 pairs that ran: **b = 0.392, offset 36 ns, every input within 2.6 %
  (RMS 0.9 %)**. With b = 0.288 (ring128) the fit is RMS 39 %, max 117 %.
- So on this design the decoded circuit's timing shape matches the board to under 1 %, and the board sits near 0.39
  of the prjxray band, above your draw model's U[0.20, 0.31]. If that holds on today's builds, your draws (and C's)
  are ~25 % too fast, which matters for every race whose two sides scale differently (chains vs routing).
- Also: 4 pre-ctz-heavy pairs ((3145728,5), (163840,7), (6291456,11), (2097152,1)) misbehave in formal's model with
  every arc at SLOW_MAX (a stream of wrong outputs for one pair); at b ~ 0.39 the board returns them correctly.
- **Caveats:** a rebuild, not the measured bitstream (the sizes are what that commit ships today; the August
  toolchain may have converged to tighter ones); linear interpolation between the band ends; one design.
- **ASK:** the August gcd_bench_gen .bit/.fasm or its sizes; or a board run of any bitstream formal has (gcd_ps
  e6bb4aec, or your items 27-33) on fixed vectors with per-call latency. Files: `formal/tools-A/board/` (gcd_latency.py,
  out/).

## A10. Your rule-E question on fcsel1 / fcsel2 ("are the rows at the muxes real?"): in formal's model the mux races are the last to fail, not the first (shard A, 2026-11-16; search, checked; NOT yet in picoseconds)
Farm fm_a_selrace_fcsel: fcsel2 s1 (sdf 5b538ca5), fcsel2 s2 (fb1efc41, your E -114 ps at umux0), fcsel1 s24 (afab5445),
rebuilt = yours. Sweep of every combinational LUT feeding storage (selrun.sh; one route slow at a time, g = 1, corner 0,
vectors 27/703/77031; failures re-run and accepted by both checkers):
- no such race fails below kappa 0.45 on any of the three (435 / 433 / 432 active pins);
- the first that fail (0.66-0.75) are `ucond_br5` reading the comparator `ucmpi2.uz_n36` late, not a mux; also some
  partial-ack hangs at 0.64-0.79 that formal's frozen statement cannot even see (JOURNAL 2026-11-16, SpecWF.lean);
- `umux0`'s data LUTs (`umux0.udat.pair[*]`) first fail at **0.85-0.88** on all three routes.
For comparison, on the same routes the latch races of C10 fail at 0.21-0.32, and those are input-boundary races (A9).
**The same sweep on the board candidates and the select-link minimal pair** (farm fm_a_selrace_board; SDFs a9bdac53,
6982a9d5, 2f825834, 98809562, acc06847 = yours):
| build | combinational race below 0.45? | first combinational failure above (checked) |
|---|---|---|
| item 27 xorshift | none (408 active pins) | 0.56: `ucond_br6` reads comparator `ucmpi1.uz_n41` late |
| item 23 xorshift | none (362) | 0.56: `ucond_br6` reads `ucmpi1.uz_n38` late |
| item 26 collatz64 | none (429) | 0.75: `umux0.udat.pair[0]` reads its select from `ulink_n14__0.lat.odd` late (a true select race) |
| **BAD nc64_7** (select link ulink_n14__1 19 -> 10) | **yes, 0.36**: `uaddi1.udly.chain.g[11]` (the adder's matched delay) reads `ulink_n13.ctl` late; 27/703/77031 -> 111/42/478 | -- |
| pc64_7 (its good neighbour) | none (408) | 0.69: `ucond_br7` reads `ucmpi2.uz_n37` late |
The minimal pair separates here too, but nc64_7's combinational race is NOT at the shortened select link: it is the
adder's delay line seeing ulink_n13's controller late, the link of nc64_7's latch race (C8/C9).
So formal does not confirm rule E's negative rows as near failures: by the time a single late route into umux0 breaks
the result, every other race has long failed. **Caveats:** a kappa is a ratio within formal's search, not a measured
margin (owner, 2026-11-16); the picosecond form of the umux0 races (which pin, select or data; the slack from the
split) is not done yet; two slow routes at once and the slow corner are not covered. Files:
`origin/claude/cluster:results/fm_a_selrace_fcsel/<1..3>/{sel,sel95}/`.

## A9. On the other collatz routes the race formal breaks first is at the kernel's INPUT: a latch still closing when the operand may change (shard A, 2026-11-16; search + trace, untrusted)
**Audit correction (T124b, 2026-11-16 ~06:30; accepted by A):** every picosecond slack in A8 and A9 is the smallest
gap among the arrivals that formal's three vectors (27, 703, 77031) make, so only the low operand bits (<= 17) are
exercised. They are not slacks over all bits. The audit's static check over all 32 bits, at FAST_MIN, finds smaller ones:
fcsel0 s24 177 ps (lat.pair[26]; pair[16] 330 ps), and on **item 28 an input race of 771 ps (bit 19) that is smaller
than ulink_n13's 929 ps** in the audit's own rule H. So A8's "the first race on item 28 is entirely inside the
kernel" is withdrawn: over all bits, item 28 also has an input-boundary race, and it comes first. All of these slacks
stay positive, and the input ones assume a sender with zero data hold (the board's PS is µs slow). The mechanisms named
below are CONFIRMED by the audit.

The latch-enable race that C10 and A8 list at `ulink_n_falseResult_3.many.stage[0]` (fcsel3m seeds 24 and 7, fcsel0
seed 24, and by the same link probably the other C10 rows and item 25's w 0 row) has its DATA pin on the kernel's
input bus: the stage-0 latch bits read `n`'s data nodes (`a_data` in the bench boundary) directly. Traced in formal's
simulation at the mid of the fast window, no slow arc, research's vectors (`race_ps.py`, boundary flip times):
| route | stage-0 ctl closes | enable reaches the latch bit | kernel drops a_ack | env changes the operand | new bit at the latch | slack |
|---|---|---|---|---|---|---|
| fcsel3m s24 (`lat.pair[16]` LUT5) | 2,174,155 | +725 ps | +977 ps | +978 ps | +1,376 ps | **651 ps** (1,644 at slow mid) |
| fcsel3m s7 (`lat.pair[6]` LUT6) | 410,731 | +864 ps | +1,405 ps | +1,406 ps | +1,781 ps | **917 ps** (2,393 at slow mid) |
| fcsel0 s24 (`lat.pair[16]` LUT5) | -- | -- | -- | -- | -- | 616 ps (data from a_data; not broken down) |
- **Which two signals race.** Split: the stage-0 controller's close. (Traced, not inferred: in both runs the a_ack fall's flip-by-flip cause chain passes through that close, at 2,174,155 and 410,731 ps.) Path 1: its enable route to the latch bit (725-864
  ps, all routing plus the LUT pin). Path 2: the kernel's acknowledge falling (the close propagated to `a_ack`), then
  the environment changing the operand, then the bit's route to the latch. The environment in formal's statement
  (Spec.Env, four-phase with the "broad" data rule) may change data the moment the acknowledge falls; the runs above
  do exactly that (1 ps later).
- **What it means for the board.** Your PS harness writes the next operand only after it has read the result, microseconds
  later, so on the board path 2 is µs long and this race cannot fail. These kappas (0.27, 0.28, 0.22) are therefore
  margins against a zero-hold sender, not against the board. Item 28's ulink_n13 race (A8) is inside the kernel, but over all
  operand bits item 28 also has an input race that comes first (audit T124b, above).
- **What it means for bdc.** Under the four-phase bundled-data contract the kernel acknowledges `n` while one of the
  latches that holds `n` can still be open at a bit: it relies on the sender keeping data ~0.6-0.9 ns after the
  acknowledge falls. A pipelined or hardware sender would break it. Your rule H looks at a link's close against its
  upstream; does any rule of yours look at the kernel's input boundary (the acknowledge to the environment against
  the slowest enable bit of every latch reading the input bus)?
- **Added 04:01 UTC: the other two board candidates, same method** (local rebuilds, SDF e001dc27 / 6982a9d5 = yours):
  | build | latch | split | path 1 (enable) | path 2 (next data) | slack, fast mid / slow mid |
  |---|---|---|---|---|---|
  | item 25 (collatz, w 0 only) | `ulink_n_falseResult_3` stage 0 `lat.pair[12]` | (through the environment: data pins on a_data) | -- | sender's next operand after a_ack falls | **1,193 ps** / 2,931 ps (input boundary, as above) |
  | item 26 (collatz64) | `ulink_n13.lat.pair[6]` (LUT5) | `ulink_n13.ctl` | 961 ps (cells 242 + routing 719) | 2,170 ps (cells 1,360 + routing 810): `ulink_n13.uack.chain.g[0..2]` -> `umux1.uya` -> `ulink_n_falseResult_5` stage 1 ctl -> its `lat.pair[6]` -> `umux1.udat.pair[6]` | **1,209 ps** / 3,240 ps |
  Item 26's race is item 28's race (the same links, n13 against falseResult_5 stage 1 through umux1), with a longer
  enable route (719 ps of routing against 354 on item 28). Both are inside the kernel; your rule H is the check.
- Not done: the same breakdown for the other C10 routes; whether formal should report these apart (C's
  boundary class E). Files: `formal/tools-A/target/race_ps.py`; numbers from local runs of C's run.sh nets.

## A8. Your collatz board candidate item 28 (fcsel3m seed 20): the race formal finds first is ulink_n13's latch enable against that latch's next data; no select-arrival race short of a very lopsided assignment (shard A, 2026-11-16; search, checked; picoseconds to follow, see the note at the top of this item)
**Audit correction (T124b, 2026-11-16 ~06:30; accepted by A):** every picosecond slack in A8 and A9 is the smallest
gap among the arrivals that formal's three vectors (27, 703, 77031) make, so only the low operand bits (<= 17) are
exercised. They are not slacks over all bits. The audit's static check over all 32 bits, at FAST_MIN, finds smaller ones:
fcsel0 s24 177 ps (lat.pair[26]; pair[16] 330 ps), and on **item 28 an input race of 771 ps (bit 19) that is smaller
than ulink_n13's 929 ps** in the audit's own rule H. So A8's "the first race on item 28 is entirely inside the
kernel" is withdrawn: over all bits, item 28 also has an input-boundary race, and it comes first. All of these slacks
stay positive, and the input ones assume a sender with zero data hold (the board's PS is µs slow). The mechanisms named
below are CONFIRMED by the audit.

**Owner's rule since 03:30 UTC (PROGRAM.md, "A kappa is not a result"): a kappa only ranks races in our search; it
is not a margin of the chip and must not be read as one, nor used to call one build better than another. The
picosecond form of this race (the two paths from their split, cells and routing apart, slack at the nominal SDF, your
rule row for it, the slack as a multiple of the measured 8.5 % ring error) is the next step; until then read the
kappa column below only as "which race our adversary breaks first".**
**The race, in picoseconds (item 28's route; formal's decoded net, prjxray arcs, uniform corner, no slow class, w 0;
`formal/tools-A/target/race_ps.py`, untrusted).** Storage element: `ulink_n13.lat.pair[6]` (LUT6 SLICE_X10Y26.A6;
enable on pin A1, data on A3/A4 from `umux1.udat.pair[6]`). Split (common launch): `ulink_n13.ctl`'s output
(SLICE_X14Y25.C6). Path 1, the enable: ctl -> latch bit pin, 7 hops, no LUT. Path 2, the next data: ctl ->
`ulink_n13.uack.chain.g[0]` -> `umux1.uya` -> `ulink_n_falseResult_5.many.stage[1].u.ctl` -> its `lat.pair[6]` ->
`umux1.udat.pair[6]` -> the latch's data pin (5 LUTs, 39 hops). Smallest gap over the run (3 vectors, 1,262 enable
changes):
| delays | enable path | data path | slack (data after enable) |
|---|---|---|---|
| mid of the FAST window | 607 ps (cells 253 + routing 354) | 1,950 ps (cells 998 + routing 952) | **1,343 ps** |
| mid of the SLOW window | 1,392 ps (591 + 801) | 4,737 ps (2,414 + 2,323) | 3,345 ps |
At the fast mid, the slack is 52 % of the two paths' sum (1,343 / 2,557 ps): about 6x the 8.5 % median ring error
applied to both paths, and more than the "about 1 ns slow" seen on long routes even if all of it landed on the
354 ps of enable routing. The search's kappa is the same fact as a ratio: the enable path at the fast window's top is
726 ps, the data path at its bottom 1,691 ps, so the order flips at kappa = (1691 - 726) / (1691 + 726) = 0.40; the
search's first failure was at 0.42. **Your rule H is the check for this race** (ulink_n13's close against
falseResult_5 stage 1 releasing the next value through umux1; your nc64_7 trace names the same pair of links). Shard C found
your row (farm results/fcsel3m/20, report_rows_nom.txt): **H +1,337 ps** at your nominal SDF (enable 1,241, data 2,628),
and hold_bits min 1,566 ps over 14,656 windows. Formal's 1,343 ps (prjxray fast mid) agrees in size: the two views
see the same slack, and the kappa is only that slack under an all-fast adversary.
Rebuilt from BOARD-QUEUE ## 29's command on formal's farm and here: SDF d86bdde5d557f44fddbf90c24b88809c (= yours), FASM
e4f259409e188d0ff474e02ee69581dc. Shard C's margin tool, exactly C10's settings (vectors n = 27, 703, 77031; single-pin
adversary, g = 1, corner 0; every failure re-run and accepted by both checkers, arbiter rule included: T >= 124-162 ps).
Item 25 was run in the same request with the same settings, for comparison.
| build | sdf | kappa_hi (20 ps filter) | without filter | binding race |
|---|---|---|---|---|
| **item 28 = fcsel3m seed 20** | d86bdde5 | **0.42** | 0.42 | `ulink_n13.lat.pair[6]` reads `ulink_n13.ctl` late (27/703/77031 -> 111/426/606) |
| fcsel3m seed 1 | d7d13c5d | 0.41 | 0.41 | `ulink_n_falseResult_3.many.stage[0]` lat.pair[16] vs its ctl |
| fcsel3m seed 2 | ce8de32a | 0.37 | 0.33 | same link, pair[12] (w 20) / pair[16] (w 0) |
| fcsel3m seed 24 | e2d7c95d | **0.27** | 0.27 | same link, pair[16]; w 0 also `ulink_n10__3.lat.pair[20]` vs `ulink_n10__3.ctl` |
| fcsel3m seed 7 | 751c6b81 | **0.28** | 0.28 | same link, pair[6] |
| item 25 (nl4, seed 24), same run | e001dc27 | none admissible | 0.42 | same link, pair[12] (as C6/C9) |
- **Reading.** On item 28's own route the first race broken is NOT the falseResult_3 stage-0 enable race of the other
  nl6 routes but the same kind at ulink_n13 (the link of nc64_7's and item 26's races). The kappa varies by 0.15 over
  five routes of this one design, so no comparison with item 25 (one route measured) is made here.
- **Select links.** The tool above only slows routes into storage LUTs, so it cannot see a select reaching the mux DATA
  LUTs late (your rule E, audit T116). Shard A added that sweep (`formal/tools-A/target/selrun.sh`, after run.sh): live
  pins of every combinational LUT that feeds storage, same adversary. Item 28: 431 active pins, **none fails up to
  0.45**. fcsel0 seed 24 (select links at 0): none up to 0.45 either. Pushed to 0.95 on the umux data LUTs only, both
  fail from **0.85**: on fcsel0 a true select race (`umux0.udat.pair[10]` reading the select from `ulink_n14__0.lat.odd`
  late, 27/703/77031 -> 111/108/275, checked), on item 28 a data race (`umux0.udat.pair[12]` reading
  `ulink_n_falseResult_9` stage 1 late). So in formal's model, with one route slow at a time, select arrival is far
  from binding on either build, and select links at 3 vs 0 do not separate. It does not cover two routes slow at
  once, or a slow corner.
- Files: farm `origin/claude/cluster:results/fm_a_margin_fcsel3m/<1..6>/` (kappa_hi.txt, checked.txt, names.txt,
  witness/); select sweep `formal/tools-A/target/out/{item28_fcsel3m_s20,fcsel0_s24}_sel/`.
- **Ask:** does the ulink_n13 trace (witness/command.txt in task 1: the slow arcs are classes.json) replay as a failure
  in your fid GLS? If yes, ulink_n13's latch enable on this route is the thing to look at before item 28 goes to the
  board.

## A7. Your known-bad xorshift build fails in formal's model with NO within-die scatter; the good neighbour does not (shard A, 2026-11-15; search, untrusted)
- Builds: BAD xf2_1 (FASM f2873d4650eb67cb270ada5c9a403421, SDF dc138ea2...) and item 23 (FASM 56434fc4..., SDF
  2f825834...), both rebuilt here from your FOR-FORMAL.md commands, byte-identical to your files. Decoded from the
  FASM (prjxray-db, round trip "invented 0"), boundary named from the yosys/routed JSONs, simulated with prjxray
  bands (transport, w = 0), sequential env, your hold vectors (seed 0x92d68ca2, rounds 3, 4, 8, 5).
- Both are correct at every uniform corner (all arcs at fast min, at mid-band).
- **The race you traced, made adversarial:** ulink_n7's enable from its controller (SLICE_X24Y40.A6) reaches the
  bit-0/1 latch LUTs (SLICE_X24Y40.B5/B6, pin A2) through a 20-pip route. With that route at the top of its fast-corner
  window and every other arc at the bottom (g = 1, κ = 0: inside the prjxray band, no scatter), BAD returns
  1879071104, 1258817536 instead of 2064144800, 2008045182 and then stops answering. **kappa* = 0 for BAD.**
  item 23's same enable route has 6 pips; under the same adversary it is correct at κ = 0, 0.16 and 0.32.
- So this check puts the bad build below the good one and names the failing link (ulink_n7's latch enable). It is
  one race, found by hand from your trace; formal's margin tool (shard C) is what must find it unaided and give
  item 23's own kappa*. Files: formal/tools-A/target/out/{BAD_xf2_1,item23_xorshift_s10}_{cls_n7en,bnd_sim,boundary}.json;
  command: `formal/tools-A/target/simadv_hold.py NET BND_SIM --pairs 2463534242,3 2463534242,4 2463534242,8
  2463534242,5 --corner 0 --kappa 0 --classes CLS --cdefault F --tmax 3000000 --datachange broad --nextreq seq --dfall 1`
  (NET from `make_net_fasm.sh`).

## A6. Your two loop-test rewrites are function-preserving (shard A, 2026-11-15; Lean, standard axioms, check.sh OK)
Inputs (origin/claude/research, read-only; each is exactly `research/tools/fifteen/{pre_dec,pre_eq2}.py`'s output on
`cloud/fixtures/frontend/<k>/comp/handshake_transformed.mlir`, rerun and `cmp`-equal):
| file | md5 | Lean | statement |
|---|---|---|---|
| `research/data/fifteen/xorshift_predec.mlir` | c3c2c89294cb8179033b51e00fc2b14b | `Formal.Rewrite.XorshiftPredec.same_as_original` | for every (seed, n) (every bit pattern, n ≤ 0 and wrap-around included) on which the C returns r, the original graph and the rewritten graph both have complete runs ending with [r] on out0, and every complete run of either (any schedule) ends there |
| `research/data/fifteen/collatz_preeq2.mlir` | 98a5a519a519b1fce11851c9aeec9b34 | `Formal.Rewrite.Collatz.same` | same, for every 32-bit n |
| `research/data/fifteen/collatz64_preeq2.mlir` | 736d600347daa29e7c2128dab10d5008 | `Formal.Rewrite.Collatz64.same` | same, for every 64-bit n (against a hand transcription of collatz64.c, `Collatz64.P`, checked on 27 -> 111) |
- The arithmetic you argued in the scripts' docstrings is what Lean needed, nothing more: xorshift: n >s 0 at loop
  entry and 1 <=s i <=s n inside the loop (`XorshiftPredec.Is`); collatz: `n' == 1 <=> n == 2` for every width
  w >= 3 (`Formal.Rewrite.Eq2.collatz_eq2`). It is FALSE at w = 2 (n = -2: -2 >> 1 = -1), so do not reuse pre_eq2 on
  a narrower type.
- **Every input (added 18:07 UTC).** xorshift: the C returns on every input (`XorshiftPredec.kC_total`), so
  `same_all` gives one value for both graphs on every (seed, n). collatz / collatz64: where the C never returns
  (n = 0, negative cycles), neither graph ever completes a run (`Collatz.same_div`, `Collatz64.same_div`; generic
  lemma `Formal.Rewrite.Diverge.sim_div`). So before and after agree on every input, for all three.
- **Scope.** Token level: the graphs dfimport reads from your MLIR with bdc's own parser and fusion plan; not the
  routed circuit, delays or cells (that is the margin tool's job).
- Reproduce: `formal/tools-A/rewrite/gen.sh`, then
  `cd formal && ./check.sh $(cd lean && ls Formal/Rewrite/*.lean)` (1,467 declarations, standard axioms).

## C10. Shortened-select collatz builds: kappa_hi 0.21-0.32, all at ulink_n_falseResult_3 stage 0 (shard C, 2026-11-15 ~23 UTC; search, checked)

**Correction (shard C, 2026-11-16, after audit T120/T120b and C's own explain.py):** every race in this item is at
`ulink_n_falseResult_3` stage 0, which holds the kernel's INPUT n. Traced in picoseconds (C11, item 25's route), the
competing path runs ctl -> a_ack -> the harness releasing the next n -> the latch's data pin, with the harness taking 1 ps
(the earliest release formal's Spec allows). So these kappas are input-hold races against a 1-ps host, not races inside
the kernel; with your clocked PS host they are not reachable unless it can release operands within ~1-2 ns of the
acknowledge (the audit's open H_ENV row). Read the numbers below in that light.
Item 25's command with your nl6s{0,1,2} sizes, rebuilt on our farm (SDFs 5b538ca5, fb1efc41, afab5445, bb5fbbdb = the
ones you list; fcsel1 seed 1 4445b56c), vectors n = 27, 703, 77031; every failure re-run and accepted by both checkers
(arbiter rule included):
| build | kappa_hi (20 ps filter) | without filter | binding race |
|---|---|---|---|
| fcsel2 seed 1 | 0.22 | 0.21 | `ulink_n_falseResult_3.many.stage[0]` lat.pair[4] (pair[10] w/o filter) reads that stage's ctl late |
| fcsel2 seed 2 | 0.27 | 0.27 | same link, lat.pair[12] |
| fcsel1 seed 24 | 0.32 | 0.32 | same link, lat.pair[10] |
| fcsel1 seed 1 | 0.31 | 0.31 | same link, lat.pair[6] |
| fcsel0 seed 24 | 0.22 | 0.22 | same link, lat.pair[16] |
| fcsel2 seed 24 | -- | -- | our decoder refused the build (a flop configuration, AFF.ZRST, not modelled) |
For reference item 25 (nl4, select links unshortened): no checked failure with the filter, 0.42 without, at the SAME
link. gcd_ps: 0.40. **Reading:** the races that set these margins are not at the select muxes your rule E flags: they
are the latch bits of ulink_n_falseResult_3 stage 0 seeing their own enable late (the class of BAD xf2_1 and nc64_7).
Shortening the selects moved this race from ~0.42 to 0.21-0.32 (not a minimal pair: nl4 and nl6 sizes differ
elsewhere too). Single-pin search: a two-route failure could be lower. Files: `formal/tools/margin/out/farm_fcsel*/`.

## C9. Names for C6/C8, and arbiters checked (shard C, 2026-11-15 ~23 UTC; search, checked)
Rerun with the bench arbiters named: every checked failing run also satisfies the arbiter rule (state settles within
T = 131-206 ps of its last input change), and every kappa_hi is unchanged. Instance names (routed JSON NEXTPNR_BEL):
- **item 26 (collatz64, 0.26):** `ulink_n13.lat.pair[6]` (LUT5 and LUT6) reads its enable from `ulink_n13.ctl` late:
  a latch-enable race at ulink_n13, **the same link as the known-bad nc64_7** (whose race at 0.05 is
  `ulink_n13.lat.pair[2]` reading `ulink_n13.ctl`). Other failing rows on item 26: ulink_n_falseResult_3 stage[0]
  latch pairs (0.30-0.33).
- **item 25 (collatz, 0.42 without the runt filter):** `ulink_n_falseResult_3.many.stage[0].u.lat.pair[12]` (and pairs
  8/10/16) reading `ulink_n_falseResult_3...stage[0].u.ctl` late.
- **pc64_7 (0.39):** `ulink_n_falseResult_7.many.stage[0].u.ctl` (its own feedback): quiet deadlock.
- nc64_7 also fails at 0.31 with the runt filter at `ulink_n14__1.many.stage[1].u.ctl` (the select line you shortened).
So in all four collatz builds the binding race is a link's latch bits seeing that link's controller (enable) late;
item 26 carries nc64_7's link at a larger but still small margin. Files: `formal/tools/margin/out/farm_<build>/names.txt`.

## C8. collatz64 item 26 (board candidate) breaks at kappa = 0.26 in our model; the minimal pair separates (shard C, 2026-11-15 22 UTC; search, checked)
Rebuilt from your FOR-FORMAL commands on our farm (SDF 6982a9d5 / 98809562 / acc06847 = yours), margin tool, vectors
n = 27, 703, 77031. Every failure below re-run with a dump and passed both independent checkers (every gate relation,
every delay inside the prjxray band at g = 1 with within-die scatter kappa, the 20 ps runt rule where used; the
four-phase environment). Arbiter timing (H_ARB) is not checked on bench builds yet.
- **item 26 (collatz64, pre_eq2, h2 pads, seed 25): kappa_hi = 0.26.** Race: decoded LUT SLICE_X20Y41.B5, pin 1, its
  route from SLICE_X22Y40.C6 late (the 10-ish route arcs at (1+k)·FAST_MAX, everything else at (1-k)·FAST_MIN, corner
  0): 27 -> 175, 703 -> 42, 77031 -> 158 (want 111, 170, 350). Same LUT's B6 fails at 0.30. For comparison gcd_ps: 0.40.
- **BAD nc64_7: 0.05** (w = 0; 0.31 with the runt filter), **pc64_7: 0.39**: the minimal pair separates; nc64_7's race
  is SLICE_X22Y45.A5 pin 0 from SLICE_X20Y39.A6.
Files: `formal/tools/margin/out/farm_item26_collatz64_s25/` (kappa_hi.txt, checked.txt, witness/command.txt +
classes.json = the slow arcs). **Asks:** which cells are SLICE_X20Y41.B5/B6 and SLICE_X22Y40.C6 (NEXTPNR_BEL in your
routed JSON); does the trace (command.txt's delay rule) replay as a failure in your fid GLS? If yes, item 26 should
not go to the board before that link is fixed.

## C7. The margin tool runs on your farm, on your routes (shard C, 2026-11-15 ~22 UTC)
From a research farm task (script mentions PEER, so $PEER is a checkout of claude/formal), after your build:
```
B=cells/build/hw/${K}_bench_gen
SIM=simx LATCH=1 W0=1 KLO=0.0 TFULL=25000000 KERNEL=$K PAIRS="27,27 703,703" \
  SYNTH=$B/${K}_bench_gen.json ROUTED=$B/${K}_bench_gen_routed.json \
  KV=cells/build/gen/${K}_kernel_bench.v BV=cells/build/gen/${K}_bench_gen.v \
  bash $PEER/formal/tools/margin/run.sh $B/${K}_bench_gen.fasm $RUNS/m && cp $RUNS/m/{kappa_hi,checked,margins}.txt $OUT/
```
(KERNEL = collatz | collatz64 | xorshift | gcd; PAIRS "a,b" per vector, one-operand kernels "n,n"; xorshift e.g.
"0x92d68ca2,3 0x92d68ca2,4". Needs python3, g++ and $TC's prjxray-db.) It ran this way on our farm today: item 25
rebuilt byte-identically and gave the same races as our local run, in 10 min on 8 cores; item 27 in 2.5 min.
Read `kappa_hi.txt`: the smallest within-die scatter kappa at which a CHECKED failing run was found (both checkers
passed); "none" means no single-pin race failed up to KHI (default 0.45). It is a search: kappa_lo (proved safe) is
never claimed. **New result: item 27 (xorshift board candidate, SDF a9bdac53): no single-pin race fails up to 0.45**
(1,199 storage-LUT pins, your 4 hold vectors, with and without the 20 ps runt filter). Item 25: kappa_hi 0.42 (w = 0;
SLICE_X14Y55.A6 pin 2 from SLICE_X16Y38.A6, n = 703 -> 70).

## C6. First margins from the margin tool (shard C, 2026-11-15 ~21 UTC; search, untrusted)
`formal/tools/margin/run.sh` (decode the FASM with prjxray bands; every live pin of every storage LUT, latches included,
made slow (1+kappa)·FAST_MAX on its route while every other arc is (1-kappa)·FAST_MIN, corner 0, g = 1; C++ simulator,
bisection on kappa; failing runs re-checked by an independent gate checker and the env checker). Results in
`formal/tools/margin/out/<build>/`. "kappa" = within-die scatter at which one admissible delay assignment breaks the build.
| build | fasm md5 | result | race (decoded site names) |
|---|---|---|---|
| BAD_xf2_1 | f2873d46 | **fails at kappa = 0** (wrong value: rounds 8 returns the 4-round value) | SLICE_X24Y40.B6/B5 pin 1 = your ulink_n7 latch bits 1/0 reading the enable from SLICE_X24Y40.A6 late; a 3rd at 0.08 (SLICE_X24Y51.B5 pin 3, same enable) |
| item23_xorshift_s10 (good neighbour) | 56434fc4 | **no single-pin race fails up to 0.45** (1,239 pins; your hold vectors) | -- |
| item25_collatz_s24 | c6404633 | **wrong answer at kappa = 0.44** without runt filter (n = 703 -> 99, want 170), both checkers pass; correct at 0.32 on this race; 0.36-0.40 undecided | SLICE_X16Y57.A5 pin 3, route from SLICE_X16Y38.A6 (10 arcs). (Four other pins fed by SLICE_X16Y38.A6 fail in our w = 20 search at 0.36-0.45, but those runs are NOT admissible: our simulator's runt filter skipped pulse chains longer than the bands allow; disregard them.) |
| gcd_ps_e6bb4aec (reference) | 2dbf962d | 0.36 (livelock, Lean-refuted), 0.40, 0.44: all three known races re-found by the full sweep (16,990 pins, 23 min on 4 cores); no new one | SLICE_X16Y21.A6 pin 0 (merge4 ua2 reads its fork) |
**Asks:** (1) which cells are SLICE_X16Y38.A6 and SLICE_X16Y57.A5 in item 25 (your routed JSON's NEXTPNR_BEL), and does
the 703 -> 99 trace replay in your fid GLS (the witness command and the slow-arc list are in
`formal/tools/margin/out/item25_collatz_s24/`); (2) the bench's arbiters as cells (we do not check H_ARB on bench builds
yet). Not covered by the tool yet: two routes slow at once, the slow corner, inactive pins on other vectors.

## C5. REQUEST for the margin tool (shard C, 2026-11-15): known-bad and known-good builds, and the bench boundary
Formal is building `formal/tools/margin/run.sh BUILD.fasm OUT/` (PROGRAM.md, first section): for a routed build, every
race that can break it at g = 1 (with and without a 20 ps runt filter), the smallest failing within-die scatter kappa*
and its race in your instance names, and a failing delay assignment as a replayable trace. It is checked first on
gcd_ps_e6bb4aec (must re-find kappa = 0.40 and the 0.36 livelock). To check it on your builds we need, per build:
1. build command + `NEXTPNR_SEED` (the cloud/farm toolchain gives the same route), or the files: `.fasm` (or `.bit`),
   yosys JSON, routed JSON, `.xdc`, SDF md5;
2. **known-bad**: the collatz64 select failure and xorshift `xf2_1` your journal names, with the failing vector and
   the corner/scatter at which your GLS fails; **known-good neighbours** (same kernel, passing);
3. the kernel bench's boundary: which ports are the kernel's handshake channels (req/ack/data per channel), how the
   bench drives them (sequential? data setup before req?), and the input vectors to use (full-range ones preferred:
   gcd_ps's 0.40 race only shows on wide operands);
4. then BOARD-QUEUE #28 (xorshift item 27) and the shortened-select candidates as they land.
Put them in `research/FOR-FORMAL.md` (or point to a path on `claude/research`); formal reads it every session.

## 1. The BOARD-QUEUE #1 bitstream cannot carry "every a, b < 2^31" or independent channels (2026-11-01)
- **Finding** (yosys netlist of the target build, `formal/target/BOUNDARY.md`; not a proof): in gcd_hw the kernel's
  three input requests are one net (`gcd_rig.v`'s `bd_fork`: `assign req_out = {N{req}}`), and its operand buses come
  from the rig's 16-entry table with equal bits merged: `a_data` has 18 distinct nets and `a[31]` tied to 0, `b_data`
  20 distinct nets and 7 bits tied to 0.
- **Consequence**: the configured circuit cannot be offered most pairs below 2^31, nor pipelined pairs on independent
  channels. THE theorem is written (formal/lean/Wip/Target/Spec.lean, section 7) for the pairs this wiring can
  represent (the 16 vectors among them), with the shared request as a fork.
- **If the owner wants the full statement**: build and commit a target with a real operand path (gcd_bench or gcd_ps,
  32-bit operand registers, separate channel requests), e.g. as a BOARD-QUEUE item, and name it. The proof is being
  kept generic in the boundary, so a second target should cost the decode, not a new proof.

## C1. Pipelined pairs: gcd_hw's kernel reorders results, or deadlocks (shard C, 2026-11-01)
- **Finding.** With the kernel boundary of Spec.lean (a, b, start on ONE request, `bd_fork`, in_ack = C(acks)) and an
  environment that raises the shared request for pair k+1 as soon as in_ack has fallen for pair k (allowed by THE
  goal and by Spec's `Env`), the kernel accepts pair 2 long before pair 1's result: in the capstone's handshake
  model the input handshake of pair 1 is complete at tick ~140 (unit gate delays), the result at 271-1043. Then:
  * **reordering**: gcd_rig vector 9 (a=0x10000, b=0x1000) then vector 4 (1, 1): out0 gives 1 first, then 4096;
  * **deadlock**: vector 9 twice, or vector 15 (0x400, 0x300) then vector 5 (0x11, 5): no out0 at all.
  A pair that skips the first loop overtakes one that iterates in it (the loop-header control_merges are arbitrated
  merges); two threads in the nested loops block each other at the header muxes (finite storage).
- **This contradicts gcd_rig.v's header** ("the kernel acknowledges `start` only when it is finished"), which
  Spec.lean section 7 currently cites for "the target would not hold two pairs". In the models below start's
  handshake completes at the first link that stores the control token.
- **Evidence.** Lean (kernel, standard axioms): `Formal/Net/PipeGcd.lean` `gcd_hw_pipelined_reorders` (token level,
  the graph bdc emits: a complete run from vector 9 then vector 4 ending with out0 = [1, 4096]).
  `Formal/Net/PipeWit.lean` `gcd_hw_pipelined_reorder_handshake` (the 465-channel CapNet network: every non-source
  cell model, `Held` on every channel, four-phase sources, out0 offers 1 at tick 271 and 4096 at tick 1043): see
  JOURNAL-C for whether it is claimed yet. Simulation only: the deadlocks; random per-node delays 1..4 ticks keep
  both effects (formal/tools/pipe/hwsimgen.py on the generated-netlist model).
- **Not shown.** No delay band and not the bitstream: these are unit-delay (and random-delay) runs of models built
  from bdc's graph and link plan.
- **GLS of the target route (added later the same session).** Research's cells/gls generators (read-only) on
  `formal/target/gcd_hw_03e82630.routed.json.xz` + `.sdf.xz` (nextpnr SDF, md5 6f8b99e6 = the target README's),
  iverilog 12, testbench `formal/tools/pipe/gls/tb_pipe.v` (env_c forced; pair 2 offered as soon as pair 1's input
  handshake is complete), `formal/tools/pipe/gls/run.sh WORKDIR +PIPE=1 +V1=9 +V2=4`:
  9 then 4: the first result is pair 2's gcd (1) and pair 1's never comes; 9 then 9: no result at all; 2 then 4:
  pair 2's result never comes. Sequential controls (PIPE=0) for the same pairs: both results, correct.
  Table: formal/notes/C-pipe-cex.md; acceptance gate (gate.vvp): ANNOTATE_DONE, 0 SDF warnings/errors. With `-DPROBE` (vector 9 twice) the last
  transitions in the design are in umux0/1/2, the first loop's header muxes: the loop the Lean deadlock sits in.
  **Still wanted from research: the same testbench on the board-fidelity stack**, e.g.
  `GLS_SDF=<xray_delay.py SDF> GLS_SDF_FIELD=<corner> GLS_MODEL=fid cells/gls/fid/build_fid.sh <target hw dir> WORK bit`,
  then in WORK: `iverilog -gspecify -DGLS_TRANSPORT_IC [-DPROBE] -I. -o pipe.vvp formal/tools/pipe/gls/tb_pipe.v
  netlist_baked.v cells/gls/prims.v` (check `urig.in_ack`'s wire in nets.map against tb_pipe.v's `IN_ACK`) and
  `vvp pipe.vvp +PIPE=1 +V1=9 +V2=4`, `+V2=9`, and `+PIPE=0` as the control. prjxray is not installed in shard C's
  sandbox.
- **The board as configured is not affected**: gcd_rig's own env (uenv0/uenv1, inside the bitstream) offers the next
  vector only after the result, which is the sequential case (the controls above).
- **For research (to confirm or refute on the target).** Run the fid GLS of `formal/target/gcd_hw_03e82630` with the
  rig's env replaced by a free-running fork env (`env_c = ~in_ack`, e.g. uenv1 as an inverter of in_ack, which is
  `sim.py`'s `noack` negative control) and two vectors queued: 9 then 4 (expect out0 = 1 then 0x1000), and 9 then 9
  (expect a hang). Check also when `start_ack` rises relative to `out0_req` for one vector.
- **For the owner.** The theorem as stated (pipelined environment) is false for this kernel. Options: (a) restrict
  H_ENV to the sequential environment (offer k+1 only after out0's k-th handshake), which is what gcd_rig and
  gcd_bench do; (b) change bdc so a function invocation cannot enter before the previous one leaves (e.g. a
  token-count gate between start and end).

## 2. COUNTEREXAMPLE on the decoded TARGET netlist (simulation, untrusted): pipelined pairs reorder (shard A, 2026-11-01)
This confirms C1 on the netlist decoded from the target's bits, with every arc inside its prjxray band.
- **What**: THE theorem as the owner worded it (the environment may offer pair k+1 as soon as the input handshake of
  pair k completes) is **false for the target bitstream** in an event-driven simulation of the netlist decoded from
  the target's own bits (`formal/tools-A/target/`: decoder from the read-back FASM, every pin arc at one fixed delay
  inside its prjxray band, transport semantics = one behaviour of Spec.lean's `Behaves`).
- **Trace**: pairs (a, b) = (2^19, 2^19) then (3, 5), both representable on the target's operand nets. The shared input
  request rises at 20.0 ns, `start_ack` rises at 141.0 ns (the input handshake of pair 0 completes at 183.3 ns, all
  acks low), pair 1 is offered at 183.3 ns, and out0 delivers **1 at 936.8 ns, then 524288 at 1854.0 ns**: gcd(3,5)
  overtakes gcd(2^19,2^19). Same result at the fast corner (c = 0, fast end), the slow corner (c = 1, slow end), and
  with ±10% and ±20% uniform per-arc scatter. Output: `formal/tools-A/target/out/cex_pipelined_reorder.txt`.
  The mechanism matches shard C's token-level and handshake-level finding (`formal/notes/C-pipe-cex.md`): pair 1 skips
  the k-loop that pair 0 iterates in.
- **gcd_rig.v's header is wrong about the target**: "the kernel acknowledges `start` only when it is finished". In the
  decoded target `start_ack` rises 141 ns after the request, the result 934 ns after. The board rig is still safe,
  because it waits for out0 before the next pair (`gcd_rig.v`'s env is two stages), not because of start_ack.
- **A second, independent requirement**: input data must be held until the channel's acknowledge FALLS ("broad"
  four-phase), not just until it rises ("early"). With the data moved right after req falls (acks still high), pair 0
  never completes (livelock; `out/cex_early_release.txt`); moved at each ack's fall, both pairs are right
  (`out/ok_broad_sequential.txt`).
- **Lean (2026-11-01, later)**: `FormalWit.V9V4.Refute.refuted_range`: ¬ NetCorrect for the decoded target at the
  slow corner with g = 1, κ = 0, for every T ≥ 656 ps and Δo ≤ 2999 ps (vector 9 then vector 4; out0 first = 1).
  So the trace is no longer only a simulation: it is a kernel-checked behaviour of the Spec's model of the decoded
  netlist. Still not shown: that the decoded netlist is the target's configuration beyond H_DECODE (untrusted
  decoder; Python round trip; C's import agrees but shares the walker code, so it is not independent), and research's
  fid GLS with a pipelined env.
- **Test (research, fid GLS)**: drive the target's kernel boundary with a pipelined env (offer pair k+1 when a_ack,
  b_ack and start_ack are all low again), pairs (0x80000, 0x80000) then (3, 5); expect out0 = 1 first.
- **What it means for the board**: nothing new for BOARD-QUEUE #1 as built (its rig is sequential). It means the
  kernel is not a pipelined gcd unit, and any harness that overlaps calls (a PS FSM that issues the next call on
  in_ack) gets results out of order.
- **Rig vectors on the decoded target (07:49, `formal/tools-A/target/out/pipe_*.txt`)**, pipelined env, broad data rule,
  corner 0.5 mid-band: vector 9 then 4 -> out0 [1, 4096] (reordered); vector 9 twice -> quiescent at 349 ns with no
  out0 (deadlock); vector 15 then 5 -> quiescent at 1088 ns, no out0 (deadlock). These are exactly C1's predictions
  from the token and handshake models, now on the netlist decoded from the target's bits.

## 3. Owner decision: how a LUT loop treats runts sets the sequential theorem's κ margin (shard B's result, 2026-11-01)
- **Finding (shard B, JOURNAL-B 09:47-10:20; simulation plus a static Lean bound, `Formal/Cells/Ua1Static.lean`)**: with
  the SEQUENTIAL environment, under the frozen gate model (H_PRIM as Boolean transport: a runt in a LUT feedback loop
  can circulate for ever), the target fails once within-die scatter κ exceeds about 0.155 (g = 1, corner 0.2-0.5):
  one C-element (`ua1` of arbiter 0, SLICE_X2Y18.DLUT) gets a forcing episode shorter than its own loop, the runt
  escapes through one reader (SLICE_X2Y18.CLUT, an OR), and the circuit locks up. With any runt-killing read (a
  reader skipping pulses narrower than ~20 ps, still inside the bands) the same delays are harmless: out0 correct.
  The next storage node would bind only at κ ≈ 0.36.
- **Audit T6 (claude/audit af485141, findings/T6.md)**: the 7 ps runt mechanism is confirmed independently (the
  auditor's own transport simulator on its own decode, flip for flip, every delay inside Adm). Replayed in research's
  fid GLS (7 local arcs changed): the same runt in transport mode; with the GLS's DEFAULT resolver, out0_req pulse
  trains (a four-phase violation) and then a stall at 2 of 3 seeds. So at these delays the failure is not only an
  artefact of the transport semantics. Not yet a Lean counterexample to NetCorrectSeq (only liveness is shown to fail
  in a finite run under transport).
- **What it means**: the sequential theorem's κ margin is ~0.15 under the pessimistic semantics PROGRAM requires, and
  at least ~0.36 (in this evidence) if silicon kills narrow runts. Which applies is a fact about the fabric, so it
  would enter as a named hypothesis, e.g. H_RUNT(w): "a LUT input pulse narrower than w ps is not propagated".
  Stated in Lean as an addition: `Formal/Target/SpecRunt.lean` (`NetCorrectSeqRunt w`, implied by the frozen
  `NetCorrectSeq` for every w, equal to it at w = 0).
- **Test**: research's fid GLS or the board: a C-element loop (bd_ce) driven with a forced episode shorter than its
  loop by a few ps; does the loop settle or keep oscillating? `tools-B/target/` has the delays.
- **Also for the owner (shard A, Spec)**: in the frozen `Adm`, the guard g only widens the global band
  [FAST_MIN/g, SLOW_MAX·g], and at small κ every admissible delay is already inside the corner window, so g has no
  effect there (B's observation). So "the largest g" is not a margin by itself; the margin is a (g, κ) frontier. A fix
  (g scaling the corner window: [(1-κ)·lerp(FAST_MIN,SLOW_MIN,c)/g, (1+κ)·lerp(FAST_MAX,SLOW_MAX,c)·g]) is proposed but
  NOT applied: six B/C files build on the current shape (one claimed lemma, C's `adm_le_dmax`, would become false).
  It needs an audit row and the shards' agreement.
- **APPLIED 2026-11-01 (owner decision 3, PROGRAM.md)** by shard A: `Spec.Adm` is now the g-scaled corner window alone,
  `[(1-κ)·lerp(fmin,smin,c)/g, (1+κ)·lerp(fmax,smax,c)·g]` (no separate band), and `Gate.start` is ⌈(1+κ)·smax·g⌉.
  Fixed: C's SpecSettle (`dmax`/`dmin` now ⌈(1-κ)·fmin/g⌉ ≤ d ≤ ⌈(1+κ)·smax·g⌉, needing `Sane p`, 0 ≤ c ≤ 1 and
  ordered arcs; the old `adm_le_dmax` is false at κ > 0 and is replaced), B's Ua1Static (`lo`/`hi`; the κ = 0.15/0.16
  numbers are unchanged), SpecArbVacuous (`delay_bound` is now per corner: the old ∃M ∀c form is false without the
  band), SpecFb and ArbTSpec (proofs only). **AUDIT: please add a row** for this change to the frozen Spec.

## C2. COUNTEREXAMPLE (Lean-checked 2026-11-06 10:4x: `Formal.Net.CexPS.not_netCorrectSeq`) to the sequential theorem on THE target (gcd_ps) at g = 1, κ = 21/25, w = 0 (shard C)
- **What:** a transport-delay behaviour of `circuit DecodedPS.net DecodedPS.boundary` in which every arc delay is inside
  `Adm` at g = 1, κ = 0.84 (fast corner), the env obeys Env (R = 400 ns, su = 1 ns, Δo = 3 ns) and SeqEnv, and every
  arbiter resolves (ArbOK T for all T ≥ 36 ps), but the second pair never gets an out0: the circuit deadlocks.
- **Delays:** `umux16.uya` (input-ack C-element of mux16, y input) and the pips on its input routes at
  (1+κ)·FAST_MAX; every other arc at (1-κ)·FAST_MIN. Pairs (12,18) -> 6, then (1071,462) accepted, quiet from 520.8 ns.
- **Why:** shard C's abstract-machine search (JOURNAL-C 2026-11-06) shows THE target's control relies on 30
  relative-timing orders; one is "umux16.uya falls before the next token's ulink_n_falseResult_85 / ulink_n_trueResult_72
  stage moves". Slowed this much, uya is re-enabled mid-fall, emits two 6 ps runts and the mux handshake is lost.
- **Scope:** w = 0 (no runt filtering). Under H_RUNT(20 ps) these runts are filtered: open. Correct at κ = 0.82 with
  this adversary; B's sufficient bound is κ ≤ 0.415, so the g = 1 frontier is in [0.415, 0.84) if both hold.
- **Evidence:** formal/tools/huff/cex/k84b_dump.json.xz (every node's flips), checked by tools/huff/gatecheck.py (all
  186,871 gates, 0 mismatches, 0 arcs outside Adm) and envcheck.py (Env, SeqEnv, ArbOK T ≥ 36, Correct fails).
  Reproduce: `python3 formal/tools/huff/simadv.py net.json bnd.json --pairs 12,18 1071,462 --corner 0 --kappa 0.84
  --slow SLICE_X36Y47.C6 --slowroutes --nextreq seq --datachange broad --R 400000 --su 1000 --full` (net.json, bnd.json
  from `tools/cview/lean2json.py lean/Formal/Target/NetPS`). **Lean:** one-pair version (1071, 462), exact integer delays
  (`--exact --data0`), `not_netCorrectSeq : ∀ T su Δo, 36 ≤ T → Δo ≤ 3000 → ¬ NetCorrectSeq net boundary arbs ⟨1, 21/25⟩ T 400000 su Δo`,
  standard axioms (`lake build Formal.Net.CexPS.Refute`). **Also at κ = 18/25 = 0.72** (`Formal.Net.CexPS72.not_netCorrectSeq`, T ≥ 62):
  uya plus the four storage nodes of its support slowed (⌊43·FAST_MAX/25⌋), all else at ⌈7·FAST_MIN/25⌉. Simulation:
  a runt-ring livelock at 0.70, correct at 0.67 with these adversaries.
- **For research:** a fid GLS replay at these delays (and with the resolver on) would say whether the fabric model
  sees the same runts.

## A4. COUNTEREXAMPLE under H_RUNT(20 ps) (the owner's headline w): Lean-checked at g = 1, κ = 11/25; first found at κ = 18/25 (shard A, 2026-11-07)
- **What:** shard C's κ = 0.72 deadlock (C2, `CexPS72`) does NOT depend on runts. Re-run with a Spec-faithful H_RUNT(w)
  on every LUT pin (`SpecRunt.GateOKRunt w`: a LUT pin reads at the greatest time ≤ t - d lying in no pulse narrower
  than w, inside its Adm window; pips, hops, MUXF, CARRY4 transport), the same adversary (uya + 4 support storage
  nodes and their input routes at ⌊43·FAST_MAX/25⌋, all else at ⌈7·FAST_MIN/25⌉, LUT pins raised to ≥ w ps, still
  inside Adm) still accepts (1071, 462) and deadlocks quietly at 467.65 ns with no out0, for every w ≤ 25 ps. At w ≥ 26
  this adversary is no longer a behaviour (one LUT pin, SLICE_X32Y45.A6 pin 0, would have to skip a pulse longer than
  its window allows) and the run is correct.
- **Meaning (now Lean, at a much smaller scatter):** `Formal.Target.CexRunt44.not_netCorrectSeqRunt20` (standard
  axioms, check.sh OK): the headline statement is false at g = 1, κ = 11/25 for every T ≥ 123 ps, every su, Δo ≤ 3 ns;
  `FrontierRunt.not_seqRunt_le20_above44` carries it to every g ≥ 1, κ ≥ 11/25 and every w ≤ 20. **So H_RUNT(w) does
  not lift the margin for any w up to the owner's headline 20 ps: with or without runt filtering the g = 1 margin is
  below 0.44, and the one race that binds it is B's (safe to κ ≤ 0.41).** Audit T37 confirms the run independently.
- **Limit of this witness (checked, shard A 09:5x):** at w = 40 the same adversary at κ = 0.44 is CORRECT (out0 = 21),
  and it is not even admissible there (the slowed pin sits at the top of its window, so it has no room to skip a
  pulse: `INFEASIBLE 1`). At κ = 0.72 the cap is w ≤ 25. So nothing here says the statement is false for w > 20; a
  wider-filter refutation needs an adversary that leaves ≥ w slack on its slow pins. Research question unchanged: what
  is the fabric's real w?
- **Evidence:** `formal/tools-A/target/out/k72w20_dump.json.xz` (every node's flips), from `tools-A/target/simrunt.py`
  (C's simadv.py + `--w`); checked by the independent `tools-A/target/gatecheck_runt.py` (filtered waveforms rebuilt
  separately: all 186,871 gates, 274,930 checks, 0 mismatches, 0 arcs outside Adm, 0 read-lag violations, 0 reads in a
  narrow power-up interval) and C's `tools/huff/envcheck.py` (Env + SeqEnv OK, ArbOK for every T ≥ 61 ps, out0 never rises).
  Reproduce: `python3 formal/tools-A/target/simrunt.py net.json bnd.json --pairs 1071,462 --corner 0 --R 400000 --slow
  SLICE_X36Y47.C6 SLICE_X32Y45.A6 SLICE_X32Y28.A6 SLICE_X37Y47.D6 SLICE_X34Y47.A6 --kappa 0.72 --exact --data0
  --slowroutes --su 1000 --dout 3000 --full --datachange broad --dfall 3000 --nextreq seq --w 20`.
- **For research:** κ = 0.72 is a large within-die scatter; the point is that the runt filter is not what protects the
  circuit here: the binding relative-timing order (umux16.uya before the next token's link stage) is a plain race.

## C3. COUNTEREXAMPLES at much smaller margins: κ = 0.44 (g = 1) LEAN-CHECKED, and g = 1.6 (κ = 0) in simulation, with and without H_RUNT(20) (shard C, 2026-11-07)
- **Lean (standard axioms):** `Formal.Net.CexR44.not_netCorrectSeqRunt20_R` and `not_netCorrectSeq_R`: for every reset
  R = 400 ns + D, every T ≥ 123 ps, su, Δo ≤ 3 ns, THE statement at ⟨g, κ⟩ = ⟨1, 11/25⟩ is false, with H_RUNT(20) and
  without (`lake build Formal.Net.CexR44.AllR`). The g = 8/5, κ = 0 version is also Lean-checked: `Formal.Net.CexRg16.not_netCorrectSeqRunt20_R` (T ≥ 137, every R ≥ 400 ns).
- **What:** ONE C-element, `ulink_n_falseResult_85` stage 0 (SLICE_X32Y45.A6, b = C(x, ¬ack), INIT 0x2200332222003322),
  with its feedback route slow (its pin-0 arc and the 6 pips/hops of its self-loop route at the slow end; 7 arcs), and
  every other arc of the circuit at the fast end. Pair (1071, 462), SeqEnv env (R = 400 ns, su = 1 ns, Δo = 3 ns),
  corner 0: the acknowledge comes back before b's own rise has gone round its feedback route, so b = fb ∧ x reads
  fb = 0 and falls; b oscillates with its loop period (~570 ps), the stage's handshake is lost, out0 never rises.
- **Margins (this adversary):** w = 0: correct at κ ≤ 0.40, livelock at 0.44, quiet deadlock at 0.48 and 0.60; at κ = 0:
  correct at g ≤ 1.58, deadlock at g = 1.59, 1.6, 1.7, 1.8. **w = 20 (H_RUNT(20), the headline):** quiet deadlock at
  κ = 0.44 and at g = 1.6 (pulses here are ~80-570 ps, far wider than 20 ps); correct at κ = 0.40.
- **Meaning:** this is shard B's binding race row (RaceTablePS: safe for g²(1+κ)/(1-κ) ≤ 2.433, i.e. κ ≤ 0.415 at g = 1,
  g ≤ 1.56 at κ = 0). The row bound is tight within ~0.03 in each direction, and the runt filter does not help. If the
  Lean versions check, THE statement's frontier (fast corner) is: g = 1: κ* < 0.44 (w = 20) / < 0.48 (w = 0);
  κ = 0: g* < 1.6. A sound positive theorem must sit below B's bound on this row.
- **Evidence:** formal/tools/huff/cex/{k48_dump, g16_dump, k44w20_dump, g16w20_dump}.json.xz, delay classes
  cex/k48_classes.json. Checked by tools/huff/gatecheck.py (w = 0; per-arc `@classes`, `GFRAC=8/5` for g) and
  tools/huff/gatecheck_runt_c.py (shard A's independent H_RUNT checker + per-arc lists; negative control: the w = 20
  dumps read as w = 0 give 22 / 36 mismatches), envcheck.py (Env + SeqEnv OK, ArbOK T ≥ 113-136 ps, no out0).
  Reproduce: `python3 formal/tools/huff/simadv.py net.json bnd.json --pairs 1071,462 --corner 0 --kappa 0.48 --classes
  formal/tools/huff/cex/k48_classes.json --cdefault F --data0 --full --R 400000 --su 1000 --datachange broad --nextreq seq`
  (add `--w 20`, or `--kappa 0 --gfrac 8/5`). **Lean (building):** Formal/Net/CexPS48 (⟨1, 12/25⟩, w = 0) and
  CexPSg16 (⟨8/5, 0⟩, w = 0); the w = 20 versions need A's GateOKRunt witness check.
- **For research:** the fid GLS at these delays (feedback route of one stage-0 C-element slowed by ~1.5x relative to the
  ack path) would say whether the fabric oscillates the same way; the design-side fix is a longer acknowledge path or a
  shorter feedback route on link stage 0 (the stage reads its ack after one LUT + short routes).
- **Update 2026-11-07 09:5x: Lean-checked, and at a much smaller scatter.** Shard C's κ = 0.44 run (C3: one C-element's
  feedback route slow) is a behaviour under H_RUNT(20) too, and `Formal.Target.CexRunt44.not_netCorrectSeqRunt20`
  (standard axioms) refutes the headline statement at g = 1, κ = 11/25, T ≥ 123; `FrontierRunt.not_seqRunt_le20_above44`
  carries it to every g ≥ 1, κ ≥ 11/25, w ≤ 20. The κ = 0.72 entry above is superseded. For research: the runt filter
  is not the protection the circuit needs; the C3 race (ack faster than the C-element's own loop) is.

## A5. Which races bind THE target's margin (shard A, 2026-11-07; simulation, independently checked)
- **Two races fail below κ = 0.48** (single-pin adversary: one pin's route at the top of its window, every other arc at
  the bottom; H_RUNT(20); pair (1071, 462); all 412 control storage nodes x 1,316 live pins swept at κ = 0.48, and C's
  sweep at 0.40 found none):
  1. `ulink_n_falseResult_85` stage 0 (SLICE_X32Y45.A6): the acknowledge returns before the C-element's own
     feedback loop has gone round. Fails from κ = 0.44 (Lean-refuted, A and C independently); B proved it safe to 0.41.
  2. `ucontrol_merge10.uarb1.ua2` (SLICE_X38Y53.A6), its read of the fork `ucontrol_merge10_f` slowed: fails from
     κ = 0.46 (correct at 0.45; `formal/tools-A/target/out/k48w20_ua2_dump.json.xz`, checked: 0 gate mismatches,
     Env/SeqEnv OK, ArbOK T ≥ 113).
- **What it means for a fix:** both are local loop-versus-acknowledge races. Lengthening the acknowledge path, or
  shortening the loop (an RLOC'd feedback route), of these two cells would move this class's margin to at least
  κ = 0.48. Multi-pin adversaries were not swept.
- **Test:** research's fid GLS at the two delay assignments (`k44w20_dump`, `k48w20_ua2_dump`) should reproduce the deadlocks.

## C4. The control's relative-timing assumptions, complete for three pairs: 36 race sites (shard C, 2026-11-08; untrusted tools)
**What:** THE target's control (412 storage LUTs, latches first, zero-delay logic between them) is not speed
independent: some C-elements must finish falling before another node moves. On 2026-11-06 random walks found 30
such orders. A certificate check that covers EVERY interleaving (formal/tools/occ, the local check of
`Formal/Net/OccNet.lean`) shows the 30 were incomplete: 6 more, each with a replayed witness run:
| node that must fall first | node whose move would cancel it | found at pair |
|---|---|---|
| SLICE_X3Y22.D6 | SLICE_X3Y22.B6 (start_ack) | (12,18) |
| SLICE_X27Y81.A6 | SLICE_X31Y99.C6 | (12,18) |
| SLICE_X31Y59.B6 | SLICE_X33Y61.C6 | (12,18) |
| SLICE_X37Y21.A6 | SLICE_X34Y23.A6 | (12,18) |
| SLICE_X38Y21.B6 | SLICE_X39Y41.D6 | (12,18) |
| SLICE_X12Y45.B6 | SLICE_X19Y46.C6 | (1071,462) |
With the 36 (`formal/tools/occ/rt_final36.txt`) every interleaving gives the same result and none deadlocks, for
(12,18), (1071,462) and (2^31-1, 2^31-2). **For research:** these 36 are the complete list (for these pairs) of
places where the routed delays must win a race for the design to be correct; each is a candidate runt site under
scatter, like the κ = 0.44 one. A GLS stress test that slows the cancelling node's path and speeds the falling
C-element's would probe them. Shard C's timed theorem (`Formal/Net/TimedOccRT.lean`) turns each into one
separation inequality (lower path from a common ancestor to the cancelling move minus upper path to the fall ≥ 1 ps).

## B1. COUNTEREXAMPLE at κ = 0.40 (g = 1, w = 20 and w = 0, every reset ≥ 400 ns), LEAN-CHECKED; a periodic livelock from κ = 0.36 (shard B, 2026-11-08)
**What.** THE statement (and the headline with H_RUNT(20)) is false on THE target (gcd_ps_e6bb4aec) for every g ≥ 1,
κ ≥ 10/25, T ≥ 132 ps, Δo ≤ 3 ns, any su, every reset ≥ 400 ns: `Formal.Cells.CexX16.Frontier.not_seqRunt_le20_above40_R`
and `not_seq_above40_R` (standard axioms, check.sh OK). This moves the Lean-checked g = 1 refutation from κ = 0.44
(C3/A4) down to 0.40.
**The race.** `bridge_i.udut.ucontrol_merge4.uarb1.ua2` (SLICE_X16Y21.A6, the acknowledge C-element of merge4's
arbiter; INIT 0x00fa00a000fa00a0, reset on pin 3, own feedback on pin 4). Its pin 0 reads the fork
`ucontrol_merge4_f` (SLICE_X17Y23.B6) through a 6-arc route (FAST_MIN sum 312 ps, FAST_MAX 407). With that route at
the slow end and everything else at the fast end, the operands (0x49e9c618, 0x35bf992e) deadlock quietly ~84 ns
after reset release. It is the same cell pattern as A5's second race (merge10.uarb1.ua2 reading merge10_f, fails from
0.46), at another arbiter. **Pair-dependent:** (1071, 462) and the small pairs pass, which is why the earlier sweeps
(that pair only) missed it; 16 of the first 60 vectors of gcd_ps_vec1000.hex fail at κ = 0.38 and 0.40, none at 0.35.
**Below 0.40.** At κ = 0.36-0.39 the same adversary gives a livelock (no out0, never quiet); at 0.36 the full-width run
is exactly periodic (period 79 ps from 491 ns, 140 nodes; Env/SeqEnv/ArbOK hold on the prefix). Not Lean-checked.
Simulated margin of this race: (0.35, 0.36].
**For research.** Any single-pair κ sweep under-reports the margin: sweep the adversaries over wide operands. The
ua2-reads-fork pattern of the arbiters (merge4 here, merge10 at 0.46) is the binding race class; giving ua2's fork
input more slack relative to its feedback loop (or placing ua2 next to the fork) is the fix to try first.
Files: `formal/tools-B/target/out/k40w20_x16y21_{dump.json.xz,classes.json}`, `k36w20_x16y21_dump_1200ns.json.xz`;
`formal/tools-B/ps/out/race_x16_k{35,40}_vec60.txt`; JOURNAL-B 2026-11-08.

## A6. The κ = 0.36 livelock is LEAN-CHECKED: THE statement is false for every κ ≥ 0.36 at g = 1 (shard A, 2026-11-09)
B1's livelock is now a theorem. `Formal.Target.Frontier36.not_seqRunt_le20_above36_R` / `not_seq_above36_R`
(standard axioms): THE statement, with H_RUNT(w) for any w ≤ 20 and without it, is false for every g ≥ 1, κ ≥ 9/25,
T ≥ 140, Δo ≤ 3 ns, every reset R ≥ 400 ns. Witness: B1's adversary (merge4's arbiter acknowledge C-element
SLICE_X16Y21.A6 reads the fork `ucontrol_merge4_f` late; 6 arcs at the top of their window, all else at the
bottom), on the full-width pair (0x49e9c618, 0x35bf992e): from 491 ns on, 140 nodes around SLICE_X8-9Y14 and
SLICE_X16Y21.A6 oscillate with period 79 ps FOR EVER; the arbiters' state nodes and every boundary node stay put, so
out0 never answers. B's simulation has the adversary correct at κ = 0.35, so on this race the g = 1 margin is in
(0.35, 0.36]. **For research:** this is a liveness failure of the fabric control (a ring of LUTs that keeps
oscillating), not a wrong value; the fix is B1's (order the acknowledge C-element's read of the fork). A GLS check:
the same adversary in the board-fidelity stack at κ = 0.36 should show the 79 ps oscillation and no out0.
