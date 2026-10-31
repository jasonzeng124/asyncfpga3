# B probe Bag: the held arbiter's timing conditions on the 36 routed gcd_hw arbiters

> **Correction (probe Bar, notes/B-gcd-arb-a0.md).** The routed rows this file
> reads (C's Timing/RuntAckInst, from tcheck's `extract.Prjx.split`) mis-split
> nets whose driver leaves the site through two site pins (O6 on both B and
> BMUX; 16 pairs on these routes): sink a's OUTMUX hop (73-86 ps FMIN, up to
> 241 ps SMAX) is counted as shared and sink b's is dropped. For seed 2
> merge10.uarb1 client 1, `drg` is understated by 75 ps (FMIN) / 211 ps (SMAX):
> its RT1 margin is about +174 ps, not +249, at FMIN (still positive), and its
> box need about 594 ps, not 383. The theorems are correct for the rows as
> given; the rows are optimistic there. Re-proved from the corrected
> extraction in OnGcdArbFix.lean (notes/B-gcd-arb-fix.md), which supersedes
> this file's numbers: no corner margin changes sign.

Shard B, 2026-10-27. File: `formal/lean/Formal/Cells/OnGcdArb.lean` (core Lean, 1082 lines,
generator in the scratchpad `Bag/gen.py`). No route was rebuilt and no committed file was edited.

## Answer

| condition | consistent corner (FMIN, FMAX, SMIN, SMAX, each alone) | independent box (each delay in [FMIN, SMAX]) |
|---|---|---|
| **RT1 / RT1b** (g1/g2 exclusion across a handover, 7h/7j) | **Proved in Lean** on 36 arbiters × 4 corners × 2 directions, **for every server** (no H_SERVER_MIN needed). Worst raw margin **+33 ps** (seed 3 merge12.uarb1, RT1b, FMIN) | Server-free margin negative on 64/72 rows. Exact need: server + A0 branch + ustate arc + q prefix ≥ **711 ps** worst (seed 3 merge12.uarb1). Proved exact both ways in Lean. |
| **A0 fork** (H_A0_FORK, rule J' with per-pin site pins and per-pin arcs) | **Not instantiated in Lean** (the per-element data are gone, see "Blocked"). Shard C's tcheck (C-10h, `tools/tcheck/results/compare5_*.tsv`, flavour Jx) passes on 72/72 clients within the fast column and within the slow column. Worst **+222 ps fast, +523 ps slow** (seed 2 merge12.uarb1 client 1); guarded worst **−9 ps** (seed 4 merge12.uarb2 client 2, fastG) | **Unknown on gcd_hw.** C computed no full-box J. On link_arb it was negative on 8/8 pairs (OnNetlistArb). |
| RT2 / RT2b (A1/A2 exclusion) | not covered: these need A0Fork and the A0 branches | not covered |

What this means: at any one die corner the routed gcd_hw arbiters keep their grants exclusive
across a handover, whatever the server does. This holds by routing, with tens to hundreds of
ps to spare. If each delay can sit anywhere in its range independently, exclusion leans on the
on-chip server path (plus the A0 branch, the ustate arc and the q prefix) being up to 0.71 ns. That needs the corner model, as it did on
link_arb.

## Blocked: the routed artefacts are not on disk

The probe was to extract per-pin arcs from the FASM, as B-pin-assign does. That cannot be done
in this container:
- Br's four `--freq 100` routes (`7f52…/scratchpad/gcdr/`) are gone.
- C-10e's four routes (`formal/tools/tcheck/build/tree_{d,2,3,4}/`) are gone too. `build/` is
  gitignored and was never committed.
- The toolchain (`~/dev2/lib/fpgatoolchain`) and prjxray-db are absent.
- The only gcd_hw bitstream on disk is `research/board/gcd_hw_03e82630.bit`. It is a fifth
  route (the board's) and has no placement or SDF beside it.

Two kinds of data are left, both committed by shard C:
- (a) `Formal/Timing/RuntAckInst.lean` (C-10j). Per arbiter, client and consistent corner, it
  has the prefix-split routed quantities: physical pins, site pins, per-pin prjxray arcs. It
  carries the r_k and q nets, the ugrant arcs and the g_k → ua_k wires. It has **no A0
  branches**.
- (b) tcheck's rule J margins per client (compare5_*.tsv). These are margins only, not
  elements.

(a) is enough for RT1/RT1b, because the missing terms all sit on the safe side. Nothing on
disk is enough to instantiate ArbA0Fork or RT2.

**Routes used.** These are C-10e's routes: nextpnr 9c732bc6303458df, `BDC_SELECT_PADS`,
`BD_RLOC=v4`, seeds default (d), 2, 3, 4, no `--freq`. They are not Br's `--freq 100` seeds.
gcd_hw has 8 arbitrated control_merges, and merge12 has two arbiters, so there are 9
`bd_arbiter` per route and 36 in total.

## Check

    /tmp/claude-0/-home-user-asyncfpga3/2410103a-6b9c-55d0-893c-8f5f867f7a22/scratchpad/bchk.sh formal/lean/Formal/Cells/OnGcdArb.lean
    [bchk] OK: formal/lean/Formal/Cells/OnGcdArb.lean     (no warnings; ~8 s once deps are built)

- Dependencies: ArbHeldTimed2 and RuntAckInst. RuntAckInst builds in about 1 min the first time.
- `#print axioms` was run on a scratch file:
  - `gcd_rt1_all`, `gcd_rt1b_all`, `allRows_sat`, `rt1_iff`, `box_cex1` and the per-row
    `_ok`/`_cex`: `[propext, Classical.choice, Quot.sound]`;
  - `box_rt1`: `[propext, Quot.sound]`;
  - `_box`: no axioms.
- No sorry, admit, axiom or native_decide.

## Theorems (namespace `Formal.Cells.OnGcdArb`)

The routed numbers are **not copied**. `ofRows c1 c2` reads C's rows
`Formal.Timing.RuntAck.Inst.<seed>_<inst>_<corner>_c<k>` directly, and every per-row fact is
decided by the kernel on them.

The record `Q` holds, per client k, five fields, plus one shared field:

| field | meaning |
|---|---|
| `drg k` | r_k net suffix to ugrant's pin |
| `drs k` | r_k net suffix to ustate$LUT5's pin |
| `agr k` | ugrant arc r_k pin → g_k |
| `aRr k` | ustate arc r_k pin → O5 (R0) |
| `agq k` | ugrant arc q pin → g_k |
| `dqg` (shared) | q net suffix to ugrant |

The margins:
- `m1 = drs1 + aRr1 + dqg + agq2 − (drg1 + agr1)`;
- `m2` is the mirror.

The theorems:
- **`rt1_iff` / `rt1b_iff`** (exact accounting). Assume `Real1 x cr cq D`: 7h's delay record
  realises the row, with the r1 prefix `cr` shared by both sums and a q prefix `cq ≥ 0`. Then
  `RT1 D ↔ 0 ≤ m1 + (smin + wa0s + qf + cq) ∨ agq1 ≤ agq2`.
- **`rt1_of`, `excl1`, `excl2`**:
  - Assumed: `Real1`/`Real2`, 7h/7j's `Run` and `Scn`/`Scn2`, and `m ≥ 0`.
  - Proved: g1 and g2 are never both high before the horizon. This holds for every
    `smin ≥ 0`, every A0 branch and every ustate O6 arc. It instantiates
    `ArbHeldTimed.rt1_exclusion` and `ArbHeldTimed2.rt1_exclusion2`; nothing is re-derived.
- **`<seed>_<inst>_<corner>_ok`** (144 theorems), **`allRows_ok`** and **`allRows_length = 144`**.
  On each row, C's two client rows agree on `dqg`, every field is ≥ 0, `m1 ≥ 0` and `m2 ≥ 0`.
- **`gcd_rt1_all` / `gcd_rt1b_all`** (headline). For every one of the 144 rows, every record
  realising it, and every run and handover scenario, the grants stay exclusive.
- **`allRows_sat`** (non-vacuity of the instantiation hypotheses). For every row and every
  server `sm ≥ 0`, a valid `Dl` realises the row (`mk1`/`mk2`). The model's own non-vacuity
  (a `Run` together with a `Scn`/`Scn2`) is `ArbCorners.nonvacuous_corners`. A per-instance
  trace witness was not built.
- **The box.** `mix1 lo hi` takes FMIN on RT1's safe side and SMAX on its unsafe side. The
  theorems over it:
  - `box_rt1`/`box_rt1b`: every record in `BoxReal1 lo hi` satisfies RT1 once
    `smin + wa0s + qf + cq ≥ −m1(mix1)`;
  - `mix1_in`: the worst point is in the box;
  - `<seed>_<inst>_box`: the exact box margins, by `decide`;
  - **`<seed>_<inst>_cex{1,2}`** (64 theorems), the counter-record. A record in the box with
    `wa0s = qf = cq = 0` and `smin = need − 1` violates RT1/RT1b. With a server answering in
    exactly `smin`, 7h's `rt1_counter_minserver` (7j: `rt1_counter2_minserver`) turns it into
    a trace in which both grants are high.

  So `need` is exact.

## Hypotheses (named)

- **H_ONE_CORNER**: every delay of the arbiter sits at one prjxray column (C's row).
- **H_R_SHARED (`cr`)** and **H_Q_PREFIX (`cq ≥ 0`)**: the net prefix before each branch point
  is one wire with one delay. This is C-10i's H_SHARED_PREFIX.
- **7h's model**: per-pin routes, rise/fall arcs per output (O5 per pin), and the real INITs.
- **H_FLAT_O6**: the model has one O6 arc per LUT.
  - On these rows ugrant's O6 arc from q equals its arc from r2 at every corner (difference 0
    ps, checked), so nothing is lost there.
  - ustate's O6 arc and the A0 branch are only bounded below, by 0.
  - In `Scn`, q changes only through A0, so the flat `qf` is the A0-pin arc.
- **UNTRUSTED extraction** (C-10j `extract.py`): prjxray-db plus the RC tree, with physical pins
  from X_ORIG_PORT.

## Worst margins (ps)

| reading | RT1 (client 1 releases) | RT1b (client 2 releases) |
|---|---|---|
| FMIN | +53 (seed d merge9.uarb1) | **+33** (seed 3 merge12.uarb1) |
| FMAX | +68 (d merge9) | +46 (2 merge3) |
| SMIN | +102 (d merge9) | +92 (2 merge3) |
| SMAX | +122 (d merge9) | +111 (2 merge3) |
| per seed, FMIN, min over 9 arbiters (RT1/RT1b) | s2 +94/+36, s3 +117/+33, s4 +169/+169, sd +53/+125 | |
| guarded (0.772·safe − 1.155·unsafe), server-free, arithmetic | negative on 9/10/8/8 of 36 at FMIN/FMAX/SMIN/SMAX; worst −112 / −132 / −237 / −284 (3 merge12.uarb1 RT1b) | |
| box, server-free (Lean `_box`) | negative 32/36 | negative 32/36; worst −711 (3 merge12.uarb1); need per seed: s2 587, s3 711, s4 525, sd 563 |

The guarded and box rows are **server-free**: smin, the A0 branch, ustate's arc and the q
prefix are all set to 0 there. Any one of them covers the guarded deficit at one corner:
ustate's O6 arc alone is at least about 42 ps at FMIN and about 93 at SMIN, and the on-chip
server is the amerge's own logic. This probe does not discharge that bound. C-10j's certificate
`P` lower-bounds R0 → A0 at ua_k's pin (at least 1057 ps on its live rows), not at ustate's pin.
Only seed 2 merge11.uarb1 passes the box with no server at all.

## The corner-model caveat

- **One corner.** RT1/RT1b hold everywhere, server-free, by routing: the q hop and two arcs
  out-run the r_k branch skew.
- **Box.** In the box reading they hold only with an on-chip server latency of up to 0.71 ns.
  The 7h exactness theorems say that deficit is real in the model: a box record with a faster
  server overlaps the grants.
- **A0 fork.** C's Jx shows it safe within each column on all 72 clients. The full box is
  unknown on gcd_hw, and on link_arb it is negative 8/8. So the A0 fork, and with it RT2, has
  the same dependence on the corner model as link_arb.

This is unchanged from Bt3: the board or a GLS kappa estimate has to decide it.

## Per-instance table (ps)

- RT columns come from Lean (`_ok`, `_box`).
- A0-fork columns are C-10h tcheck Jx in the `fast`/`slow` column boxes, unguarded, with
  `fastG`/`slowG` guarded in parentheses. These are evidence, not B theorems.
- "need" = max(0, −box m1, −box m2).

| seed | arbiter | RT1 m1 FMIN/FMAX/SMIN/SMAX | RT1b m2 FMIN/FMAX/SMIN/SMAX | box m1 / m2 (need) | A0 fork Jx c1 fast/slow (fastG/slowG) | A0 fork Jx c2 fast/slow (fastG/slowG) |
|---|---|---|---|---|---|---|
| 2 | merge2.uarb1 | 94/112/289/346 | 229/281/563/692 | -556 / -208 (556) | 536/1296 (323/790) | 494/1079 (255/529) |
| 2 | merge3.uarb1 | 254/311/606/742 | 36/46/92/111 | -165 / -494 (494) | 518/1209 (315/722) | 368/859 (159/368) |
| 2 | merge4.uarb1 | 374/458/904/1107 | 389/477/943/1169 | -136 / 33 (136) | 478/1129 (244/572) | 709/1617 (363/879) |
| 2 | merge6.uarb1 | 362/456/831/1062 | 235/290/635/788 | -137 / -339 (339) | 728/1643 (473/1054) | 513/1122 (298/622) |
| 2 | merge9.uarb1 | 169/210/442/545 | 166/210/484/607 | -379 / -357 (379) | 466/1175 (293/752) | 308/753 (87/226) |
| 2 | merge10.uarb1 | 249/333/636/872 | 407/544/974/1360 | -383 / -9 (383) | 724/1733 (501/1191) | 386/911 (151/359) |
| 2 | merge11.uarb1 | 949/1091/1800/2119 | 718/810/1353/1576 | 263 / 98 (0) | 1381/2632 (832/1570) | 949/1723 (411/692) |
| 2 | merge12.uarb1 | 100/119/256/306 | 109/139/327/404 | -447 / -587 (587) | 222/523 (16/44) | 274/653 (56/143) |
| 2 | merge12.uarb2 | 395/494/983/1218 | 196/247/566/709 | 131 / -402 (402) | 555/1358 (303/747) | 1017/2262 (700/1534) |
| 3 | merge2.uarb1 | 170/212/445/550 | 183/230/470/586 | -278 / -75 (278) | 537/1233 (214/481) | 524/1198 (279/622) |
| 3 | merge3.uarb1 | 165/204/416/506 | 242/301/579/716 | -389 / -178 (389) | 352/817 (177/394) | 361/822 (154/332) |
| 3 | merge4.uarb1 | 407/503/1050/1301 | 271/345/730/911 | -43 / -234 (234) | 636/1548 (364/892) | 797/1638 (396/758) |
| 3 | merge6.uarb1 | 259/320/619/764 | 320/405/810/1011 | -99 / -100 (100) | 488/1213 (282/700) | 428/1010 (177/416) |
| 3 | merge9.uarb1 | 203/249/505/618 | 122/149/316/385 | -380 / -401 (401) | 524/1269 (278/681) | 750/1664 (475/1027) |
| 3 | merge10.uarb1 | 395/478/961/1171 | 198/258/565/716 | -12 / -490 (490) | 663/1524 (383/853) | 669/1473 (372/787) |
| 3 | merge11.uarb1 | 117/145/310/381 | 115/148/315/396 | -437 / -305 (437) | 464/1129 (232/568) | 421/977 (196/452) |
| 3 | merge12.uarb1 | 181/226/436/537 | 33/47/141/179 | -357 / -711 (711) | 813/1870 (519/1179) | 509/1228 (310/737) |
| 3 | merge12.uarb2 | 294/360/662/806 | 118/152/319/400 | -258 / -492 (492) | 482/1179 (230/597) | 342/814 (26/149) |
| 4 | merge2.uarb1 | 508/580/1020/1209 | 169/213/493/616 | 167 / -525 (525) | 905/1890 (613/1241) | 789/1544 (523/975) |
| 4 | merge3.uarb1 | 241/291/606/734 | 652/759/1385/1657 | -408 / 190 (408) | 720/1508 (433/868) | 547/1167 (258/533) |
| 4 | merge4.uarb1 | 226/277/590/721 | 217/261/631/771 | -421 / -299 (421) | 458/1163 (229/597) | 577/1355 (310/760) |
| 4 | merge6.uarb1 | 363/440/860/1046 | 240/299/663/821 | -280 / -215 (280) | 742/1776 (489/1159) | 544/1266 (294/674) |
| 4 | merge9.uarb1 | 257/314/671/821 | 249/309/706/875 | -162 / -281 (281) | 733/1750 (484/1139) | 473/1124 (241/566) |
| 4 | merge10.uarb1 | 368/453/865/1060 | 424/519/981/1210 | -144 / -81 (144) | 698/1534 (414/865) | 674/1516 (394/867) |
| 4 | merge11.uarb1 | 169/209/450/555 | 173/220/496/621 | -394 / -264 (394) | 550/1324 (314/764) | 350/840 (145/348) |
| 4 | merge12.uarb1 | 218/270/477/584 | 255/320/652/819 | -490 / -441 (490) | 620/1475 (331/789) | 861/1939 (581/1287) |
| 4 | merge12.uarb2 | 357/430/941/1144 | 212/255/609/738 | 93 / -386 (386) | 353/860 (116/295) | 235/594 (-9/39) |
| d | merge2.uarb1 | 169/209/450/555 | 172/220/489/619 | -394 / -345 (394) | 300/777 (102/290) | 581/1377 (386/909) |
| d | merge3.uarb1 | 245/305/623/775 | 382/476/969/1201 | -420 / -38 (420) | 550/1378 (299/762) | 602/1467 (341/833) |
| d | merge4.uarb1 | 266/329/631/771 | 269/349/798/1008 | -139 / -233 (233) | 727/1762 (478/1149) | 441/1066 (216/526) |
| d | merge6.uarb1 | 397/487/961/1181 | 448/557/1140/1415 | -20 / 174 (20) | 297/717 (46/132) | 508/1169 (252/561) |
| d | merge9.uarb1 | 53/68/102/122 | 125/165/332/417 | -395 / -398 (398) | 364/898 (157/397) | 816/1649 (485/931) |
| d | merge10.uarb1 | 375/508/862/1222 | 305/420/783/1098 | -44 / -52 (52) | 516/1195 (302/679) | 421/903 (205/408) |
| d | merge11.uarb1 | 267/333/632/785 | 375/462/917/1137 | -472 / -62 (472) | 775/1801 (515/1179) | 861/1923 (527/1196) |
| d | merge12.uarb1 | 316/390/768/945 | 229/286/621/772 | -132 / -287 (287) | 877/2036 (566/1299) | 635/1462 (395/893) |
| d | merge12.uarb2 | 353/408/813/923 | 203/218/551/566 | -339 / -563 (563) | 581/1336 (365/820) | 392/903 (177/396) |


## Next step to close the A0 fork

Rerun C-10e's `route.sh` for seeds d, 2, 3, 4. The toolchain is needed. This is the same
command as before, so the routes should be byte-identical: check against `results/sha_*.txt`.
Then extend `runtack/extract.py` to emit the A0 branch suffixes, A0's arcs into ustate and
ua_k, and `cq`. With those, `ArbA0Fork.client{1,2}_iff`/`_box` and 7h's `A0Fork`/RT2 can be
instantiated exactly as RT1 is here (about 0.5 d). The alternative is to read the board
bitstream back with prjxray, which is a different route and needs INIT-based cell
identification.
