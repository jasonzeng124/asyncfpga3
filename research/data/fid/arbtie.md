# bd_arbiter near tie under the fid model (S12, 2026-10-29)

Audit r18 found that under `GLS_MODEL=fid`, a near tie on `bd_arbiter` can
acknowledge BOTH clients in ONE server transaction when the server is fast.
This re-measures that with the resolver of 055edd7 (the feedback pin is taken
from the committed state, there is no echo window, and a drive away from the
held value ends a resolution, `BREAK`). It then derives the requirement this
puts on the environment and checks gcd_hw's arbiters against it.

Files: `cells/gls/fid/f3/tb_f3_arbtie.v` (bench), `cells/gls/fid/f3/arbtie_sweep.sh`
(the sweep), `cells/gls/fid/arb_roundtrip.py` (the static check), and three
new arms in `run_f3.sh`.
Inputs: fid_core.vh md5 39948014, prims.v 55a2e75f, bd_arb.v 27dfc230 (at 0cb79ec7).

## Method

The bench builds `bd_arbiter` by hand the way gen.py builds a routed one. I
built it by hand rather than synthesising it so that TLOOP, the wires and S
could be swept. The construction:
- Each LUT6_2 is split into two SLICE_LUTX bels, one per output, both reading
  the same pins. That is how nextpnr packs it: gcd_hw_routed.json has
  `ustate$LUT6/$LUT5` and `ugrant$LUT6/$LUT5` in one site.
- Every sink pin gets its own transport ICBUF (`-DGLS_TRANSPORT_IC`).
- A bel whose output is routed back into one of its own pins is a state node:
  `META6=1`, `TLOOP6` = feedback wire + that pin's arc, and `FB6` = that pin.
  This is gen.py's `fid_loop`/`fid_fb` rule. The state nodes are ustate$LUT6
  (q) and ua1/ua2 (bd_c2). R0 (ustate$LUT5) reads q from another bel, so it is
  not a state node, just as gen.py decides.
- INITs are taken from bd_arb.v/bd_ce.v, with the pins in logical order.
  gen.py pre-applies nextpnr's pin permutation, so a permuted route differs
  only in which arc each pin gets.

The rest of the setup:
- **Server:** `A0 <= #S R0` (transport). A0 then reaches each pin through its
  own wire.
- **Clients:** four-phase, dropping r 200 ps after their ack.
- **Trial:** a lone transaction puts q at QP (both directions). Then the
  client that must flip q rises at t0 and the other at t0+W.
- **W sweep:** 1 ps steps, from -50 to TLOOP+100. This covers the rejected
  band, the whole metastable band and the clean band past it.
- **Checks per trial:**
  - no g1&g2 overlap wider than |O5-O6| + 2 ps (30 for A, 5 for B);
  - at most one A1/A2 rise per A0 cycle;
  - acks = server transactions = 2;
  - no hang;
  - no x at the end.
- **Resolver events:** the counters of ustate (META, BREAK, rejected runt) and
  of ua1+ua2 are recorded per trial. They were cross-checked against
  `+META_VERBOSE` META/BREAK/RUNT lines on A S=600 (seeds 1, 2) and A S=200
  (seed 1): they agree, and every violation is in a trial with a ustate
  META or RUNT line.

The two configurations, each with 8 seeds:
- **A:** O6 arcs 124 ps, O5 arcs 152 ps, feedback wire 300 ps, so TLOOP 424.
  9200 trials per S.
- **B:** arcs 50/53 ps, feedback wire 150 ps, so TLOOP 200. 5616 trials per S.

## Violations per S (8 seeds, both race directions)

| S (ps) | A: TLOOP 424, viol / 9200 | A: with META | A: rejected runt only | B: TLOOP 200, viol / 5616 | B: with META | B: rejected runt only |
|---|---|---|---|---|---|---|
| 200 | 6536 | 2119 | 4417 | 2427 | 1661 | 766 |
| 600 | 303 | 303 | 0 | 74 | 74 | 0 |
| 800 | 83 | 83 | 0 | 23 | 23 | 0 |
| 900 / 905 | 49 / 49 | all | 0 | 6 / 6 | all | 0 |
| 915 | 49 | all | 0 | **0** | | |
| 1000 | 21 | 21 | 0 | 0 | | |
| 1050 / 1080 | 11 / 11 | all | 0 | 0 | | |
| 1095, 1100, 1150, 1200, 1500, 3000 | **0** | | | 0 | | |

Notes on the table:
- Metastable trials: 2351 per S in A and 2325 in B.
- Grants never overlapped beyond the decode skew: the widest overlap was 28 ps
  in A and 3 ps in B, which is the O5/O6 delta.
- There were no hangs and no x at the end of any trial.
- Every violation is a double ack. 8 trials in B at S=200 also have acks ≠
  server transactions.
- No violating trial had a `BREAK`, and there was no `FOLD` anywhere. With
  this arbiter, a drive away from the held value never happens during a
  resolution.

**Comparison with r18** (A, S=600, inside r18's window W 200..460):
- The rate is now 303/4176 = 7.3%. With the old resolver it was 1097/10440 =
  10.5%.
- The clean threshold moved down. It is now S ≥ 1095 at TLOOP 424 and
  S ≥ 915 at TLOOP 200. With the old resolver both were coarser, at
  ≥ 1200 and ≥ 1000.

**Controls** (A, S=600, seeds 1-4):
- `+META_OFF=1` (pure transport): 846/1150 violations at every seed, with no
  resolver event.
- `+META_X=1`: 92/107/95/99 violations per 1150, against about 38 with the
  resolver on. There was no x at the end.
- The default prims.v model: 354/1150 at S=600 and at S=1200 alike, with
  grant overlaps up to 151 ps. That model cannot answer this question at any S.

## Mechanism, and the requirement

**The metastable case (every violation at S ≥ 600).**
1. With both requests up, R0 = r1.q + r2.~q is 1 whatever q is. So R0 rises
   with the second request, the same edge that ends q's runt. It does not
   wait for q to decide.
2. While q resolves, it holds its runt-end value. That value is handed to the
   grants as a full-swing pulse up to trp wide.
3. If A0 reaches ua_k while that pulse is still on g_k, client k is
   acknowledged. The winner is acknowledged afterwards.

The hold on A0 does not help: the hold is the loop itself, and the node still
commits.

**The requirement** (all at one corner):

    RT_k + a_k  >=  trp_max + GP_k + c_k - skew

| Term | Meaning |
|---|---|
| RT_k | R0 output to A0 at ua_k's pin |
| a_k, c_k | ua_k's arcs from the A0 pin and from the g pin |
| GP_k | q to ugrant pin, plus the ugrant arc to g_k, plus g_k to ua_k's pin |
| skew | R0's lag behind q for the same request edge (the O5-O6 arc difference here) |
| trp_max | TAU ln(WIN/2) = 647 ps, the model's ceiling (\|delta\| ≥ 1 ps) |

Checked against the bench:

| Config | Predicted S | Measured: violations at | Measured: clean at |
|---|---|---|---|
| A | 1088 | 1080 | 1095 |
| B | 909 | 905 | 915 |

So the formula holds to under 10 ps. **TLOOP does not appear in it.** TLOOP
only places the band of W that produces events, because the model's TAU and
WIN are constants. The cell's stated obligation, "a consumer must not read a
grant within one loop delay of the decision", is therefore not sufficient.
The obligation is "trp_max + the grant path after the decision", and R0 itself
gives no lower bound on that.

In silicon there is no trp_max. The slack m = RT_k + a_k - (GP_k + c_k -
skew) buys a per-event failure probability of about exp(-m/TAU) under the
model's law. That is an MTBF quantity (verify/MTBF.md), not a structural one.

**The fast-server case (S=200, most of it).** This is a model artefact on the
pessimistic side. The traced case is A, QP=0, W=-14:
1. r1 reaches ustate 1 ps before r2. This gives a 1 ps runt, which is
   correctly rejected.
2. The model has already emitted that edge, so q shows a 1 ps full-swing
   pulse.
3. That pulse becomes a 1 ps glitch on g1, and with A0 already high it
   becomes a 1 ps A1 pulse (itself a rejected runt at ua1).
4. The client's `wait (A1 === 1)` takes it as an ack.

The resolver cannot retract an edge it has already emitted. A fix would be
pulse rejection on fanout pins below some width, but no 7-series figure for
that exists (f3_model.md section 1). I have not made it, and the resolver is
unchanged. Benches that count acks should report pulses narrower than one
LUT arc separately.

## gcd_hw: every bd_arbiter against the requirement

`arb_roundtrip.py` was run on bq2/wt-6 `cells/build/hw/gcd_hw`
(gcd_hw_routed.json md5 e0d4010c, gcd_hw_xray.sdf md5 1f7f03ea). The route
came from nextpnr 9c732bc6303458df with all toolchain.txt patches ok, and the
placer seed was not recorded in pnr.log. The script uses the FAST_MIN column
of the prjxray SDF.

How RT_k is computed:
- It is a static shortest path over every routed wire and annotated arc. It
  ignores constant nets.
- Two max rules apply, both sound from the idle-low four-phase state: another
  arbiter's ack C(g, A0) needs both of its inputs, and a bd_delay FASTFALL AND
  link (LUT2 INIT 1000) needs both of its inputs. The rise must come down the
  chain; the direct taps of R0 only flush the fall.
- Every other cell passes its earliest input, so RT_k is a lower bound.
- Without the max rules (`--naive`), 3 of the 18 ack C-elements fail. Their
  paths go through the cascade's downstream ua1 or through a delay-line tap.
  Neither path can carry a rising edge.

| arbiter (urig.udut.) | TLOOP | ua1: RT_min / required / margin | ua2: RT_min / required / margin |
|---|---|---|---|
| ucontrol_merge2.uarb1 | 151 | 4097 / 1218 / 2879 | 4013 / 1042 / 2971 |
| ucontrol_merge3.uarb1 | 152 | 3309 / 1205 / 2104 | 3309 / 1108 / 2201 |
| ucontrol_merge4.uarb1 | 137 | 4725 / 1244 / 3481 | 4469 / 1196 / 3273 |
| ucontrol_merge6.uarb1 | 144 | 4783 / 966 / 3817 | 4841 / 1005 / 3836 |
| ucontrol_merge9.uarb1 | 145 | 2212 / 1134 / 1078 | 2025 / 1147 / **878** |
| ucontrol_merge10.uarb1 | 374 | 2915 / 1036 / 1879 | 2998 / 1040 / 1958 |
| ucontrol_merge11.uarb1 | 321 | 5676 / 1072 / 4604 | 5717 / 1095 / 4622 |
| ucontrol_merge12.uarb1 | 144 | 3349 / 1127 / 2222 | 3414 / 1028 / 2386 |
| ucontrol_merge12.uarb2 | 145 | 2591 / 1040 / 1551 | 2476 / 1286 / 1190 |

The worst row is merge9.uarb1 ua2. Its path is R0 → uor → a 4-link
udly chain → ulink_n143 stage 0 ctl → the fork C-element → A0, 2025 ps.

At other corners:
- SLOW_MAX column: worst margin 3887 ps. Every arc scales but trp_max does
  not, so the margins grow.
- nextpnr SDF × 0.9: worst margin 2375 ps.
- **Every margin is positive at every corner.**

**Conclusion.** gcd_hw's arbiters are not exposed to the near-tie double ack
as the model defines it. The narrowest slack beyond trp_max is 878 ps at
FAST_MIN, which is 5.9 TAU at the assumed TAU of 150. In silicon terms that is
about exp(-(647+878)/150) ≈ 4e-5 per metastable event still failing. It is an
MTBF figure, and it rests on an assumed TAU.

## Hold release (S12 follow-up, 2026-10-29)

The idle-start sweep above never raced a request against A0's fall, which is
where the hold on q opens. This section sweeps that case.

**What was swept.** I used `tb_f3_arbtie.v` with `MODE=1`, plus
`f3/arbhold_sweep.sh`. MODE 0 is unchanged: it still gives 41 violations at
S=600 and PASSes at S=1200. A trial runs like this:
1. The holder is client 1 for QP=0 or client 2 for QP=1. It takes the
   resource.
2. The other client's request comes up and waits. The hold keeps its grant
   low.
3. The holder drops its request, so R0 falls and A0 falls S later.
4. The holder re-raises its request at offset D from the A0 fall at the server.

Details of the sweep:
- D runs in 1 ps steps. For A it covers -215..824; for B it covers -215..600.
  The offset is measured as `off=`, and is 15 ps less than W for QP=1.
- Configs A and B, 8 seeds, S ∈ {600, 1200, 3000}. I added 905/915/1080/1095
  to locate the threshold.
- The checks are the same as in the idle sweep, with `acyc` starting at 1
  because the holder's ack is already in the current A0 cycle.

**Which offsets a four-phase client may produce.**
- A trial is **legal** when the holder's old ack was already low at the moment
  it re-raised. That needs D ≥ d(A0 → ua_h) + arc, which is 394 ps in A and
  190 ps in B.
- Smaller D is a client re-requesting while its own ack is still high. It is a
  forced protocol violation, and I report it only as a proxy for A0 being
  routed late to ustate.
- Client 2 abandoning its waiting request was **not swept**: four-phase does
  not let a request fall before its ack.

**Where the race is.** At ustate, q's release edge is followed by the
re-request. If the re-request arrives less than TLOOP after that edge, it is a
runt of width D. So the hold release does open the same kind of race, in the
band D ≈ TLOOP-300..TLOOP. A client with zero turnaround reaches the legal end
of that band: D 355..422 in A and 157..194 in B.

| config, S | trials (legal) | legal violations | illegal violations (no event / META / rejected runt) |
|---|---|---|---|
| A, 600 | 16400 (7080) | **100** (all META, D 355..422) | 3088 / 214 / 88 |
| A, 905 / 915 / 1080 / **1095** | 16400 (7080) each | 8 / 13 / 2 / **0** | varies with S |
| A, 1200 and 3000 | 16400 (7080) each | **0** | 3088 / 0 / 88 |
| B, 600 | 12816 (6760) | **7** (all META, D 157..194) | 1608 / 1409 / 109, and 144 hangs |
| B, 905 / **915** / 1080 / 1095 | 12816 (6760) each | 1 / **0** / 0 / 0 | |
| B, 1200 and 3000 | 12816 (6760) each | **0** | 2928 / 19 / 109, and 144 hangs |

Every legal violation is the idle-start mechanism: a double ack from a META on
q while A0 returns. No trial had a grant overlap beyond the decode skew, an x
at the end, or a BREAK. All 144 hangs are illegal trials in B.

**The requirement is unchanged.** The legal threshold falls exactly where the
idle formula predicts: violations at 1080 and none at 1095 for A (predicted
1088), violations at 905 and none at 915 for B (predicted 909). That is
expected from the mechanism. In the band, R0 rises with the re-request edge
that ends q's runt, and the server's round trip again starts before q has
decided. The rate per legal trial is 1.4% for A at S=600 (100/7080). It is
lower than the idle start's 3.3% (303/9200) because only the top ~30 ps (A)
or ~10 ps (B) of the band is legally reachable.

**Is the race reachable in gcd_hw?** Whether a real client reaches the band
depends on its turnaround. The race is reachable when

    d(A0→ua_h)+arc + [A_h → … → r_h at ustate] + arc  <  d(A0→ustate)+arc + TLOOP

`cells/gls/fid/arb_holdreach.py` checks this on the bq2/wt-6 gcd_hw route,
using the prjxray FAST_MIN column and naive shortest paths. Naive paths are a
lower bound on the re-request path, so a positive slack is robust. Every
holder's re-request arrives at least **399 ps** after the window closes; the
tightest is merge4.uarb1 h2, then merge10.uarb1 h1 at 430 and
merge6.uarb1/merge10.uarb1 h2 at 521. So in this route the hold-release race
cannot be reached at all. It is one route at one corner, and the scatter
(GLS_SCATTER) was not applied.

## What this does NOT show

- The bench uses one hand-built topology: uniform arcs, chosen wires and an
  ideal transport server. It is not a GLS of the routed arbiter. The formula
  is what carries over to a route, and it was checked only against this bench.
- The idle-start races miss the hold release. The section above covers it,
  with the same requirement.
- trp_max = 647 is the model's clip. TAU = WIN = 150 is assumed. There is no
  PVT scatter (GLS_SCATTER) in the bench.
- The gcd_hw check is static, on one route at one corner column per row. RT
  is a lower bound, and C-elements other than the arbiters' ack C-elements
  take their earliest input. It is not a GLS of gcd_hw, and it says nothing
  about other designs (arb_mtbf, arb_prot, mem_arb_ps), which were not
  checked.
- The fast-server, rejected-runt double ack is a model pessimism. Whether a
  real LUT passes a 1-50 ps runt is unknown.

## More routes (main session, 2026-10-29)
arb_roundtrip.py, prjxray SDF column 0 (FAST_MIN), BQ#2 recipe (R5 sizes, v4 placement), nextpnr 9c732bc6:

| route | ack C-elements below the requirement | worst margin | where |
|---|---|---|---|
| BQ#2 seed 6 | 0 of 18 | 878 ps | merge9.uarb1 ua2 |
| BQ#2 seed 7 | 0 of 18 | 1168 ps | merge12.uarb2 ua2 |
| BQ#2 seed 8 | 0 of 18 | 1020 ps | merge9.uarb1 ua1 |
| BQ#2 seed 9 | 0 of 18 | 1035 ps | merge9.uarb1 ua2 |
| BQ#3 (FASTFALL) seeds d,3,4,5,6,7,8,9 | 0 of 18 on each | 691 / 720 / 845 / 1213 / 1241 / 1090 / 866 / 1335 ps | merge12.uarb2 or merge9.uarb1 |

BQ#3 default-seed SDF md5 61e14755 reproduces the BOARD-QUEUE record. Worst over 12 routes: 691 ps (BQ#3 seed
d, 4.6 TAU at the assumed TAU 150). The link fast fall shortens arbiter round trips (BQ#3 minimum 691 vs BQ#2
878) but stays clear in the model.
