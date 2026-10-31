# glsq: QQuiet monitor on the research routed GLS (lead, 2026-10-31; UNTRUSTED evidence, not a theorem)

**SUPERSEDED (audit P15a, 2026-10-31): the results below came from monitors that checked LESS than the Lean
hypotheses**: the QQuiet window ignored the pin-to-output delay TA_k (pin changes in (tau - TA_k, tau] and the last
TA_k of the window were unchecked); lowmon watched .O6 of the LUT5 cells (18 of 27 outputs were dead nets);
ord_static's reset filter also dropped O5-driven requests and never checked the R0 readers. The scripts are fixed
(`lutnet.py`, `gen_qqmon.py`, `gen_lowmon.py`, `ord_static.py`) and rerun into `out2/` (`run_all2.sh`); use those
numbers. The GLS is the 520a43f research GLS (nextpnr SDF points, no fid model), not the current research GLS.

`gen_qqmon.py GLS_WORK` writes a Verilog monitor for every bd_arbiter state LUT (`*.ustate$LUT6`) of a
`cells/gls/build.sh gcd_hw` work dir: it finds the cell's own-feedback pin (the pin whose ICBUF is driven by
the cell's O6), the loop delay W = ICBUF D + TA<pin>O6, and flags any change of another pin of the cell within
W after an O6 change (QQ_VIOL). That is `Events9ArbB1.QQuiet` for this behaviour's fixed delays (the Lean
hypothesis uses the band hi phi(PqQ), a wider window). `WSCALE=k` multiplies W (negative control).

Run (2026-10-31): gcd_hw R5 seed 5 (git archive 520a43f, md5s = events5/builds.txt; GLS provenance in
provenance_seed5.txt: SDF delays, scale 1, scatter sigma 0, GLS default LUT model), `vvp run_qq.vvp +VEC=v
+TEND=150000 +QUIET=200000` for v = 0..15 (tb_run.v + netlist_baked.v + prims.v + qqmon.v, -DGLS_TRANSPORT_IC):
16/16 vectors errs=0; 20387 q flips; **0 violations after rig reset release**; on every vector the same 9
violations at 3-7 ns, during power-up settling while rst is high (qq_viol_vec6_prereset.txt). Loop windows: 419 ps
on 7 arbiters, 772 / 731 ps on merge2 / merge9. Negative control: WSCALE=20 gives 100 post-reset violations on
vector 6, so the check can fail. NOT covered: other seeds, corners, scatter, the band-hi window of the Lean
hypothesis, and the pre-reset period (QQuiet as stated in Lean quantifies over all times, so it is FALSE on this
run at 3-7 ns; a version of qclean_of_quiet from T0 on would be needed).

Quiet start (`gen_lowmon.py`, ArbEdge's `low` field): vector 6, same build, all 27 grant/R0 LUT outputs of the 9
arbiters: the only edges before rig reset release (478.5 ns) are X->0 resolutions at 2.3-4.7 ns; no rise before
release; the first grant rise is at 610.0 ns (`low_vec6_head.txt`). So `low` holds here for any T0 up to ~607 ns
after time 0 (the Lean model is binary from t = 0; the GLS starts at X, which the SatPin model does not have).

ArbOrd with the GLS's own fixed delays (`ord_static.py`, seed 5): for every grant LUT and every pin it shares a
driver net with ustate$LUT6 (the two requests, and also the reset/A0 pins, so more pairs than ArbOrd needs),
`Dr + 2 <= DQ + Dq` holds, worst margin 293 ps (`ord_static_seed5.txt`). These are nextpnr SDF point delays, not
prjxray bands; with independent prjxray bands the row fails on 2-6 arbiters (notes/A-e9arbnet.md).

All four seeds (`run_seed.sh <seed>`; outputs `out/<seed>/`; md5s equal events5/builds.txt; toolchain.sh 9/9 each):

| seed | vectors errs=0 | q flips | QQuiet violations after reset | before reset (power-up) | ArbOrd worst (GLS delays) |
|---|---|---|---|---|---|
| d | 16/16 | 20106 | 0 | 96 | 280 ps |
| 3 | 16/16 | 18669 | 0 | 96 | 293 ps |
| 4 | 16/16 | 19567 | 0 | 80 | 293 ps |
| 5 | 16/16 | 20387 | 0 | 144 | 293 ps |

(seed 5 from the first run above; its per-vector logs were not kept beyond `qq_table_seed5_1031.txt`.)
Still one GLS model (nextpnr SDF, no scatter, default LUT model), no corner sweep.

**Correction (same day):** the first `ord_static.py` also paired pins driven by the global reset net (A6, ~5 ns
paths). ArbOrd is about the request reads only, so the script now skips pins whose driver is not a LUT. The
no-scatter results above were all positive with the extra pairs, so they stand.

Scatter (`SIG=0.05 run_scatter.sh seed4`, GLS_SCATTER = 0.05 per arc, unclamped Gaussian, draws 1-3; seed 4 route):

| draw | vectors errs=0 | q flips | QQuiet violations after reset | ArbOrd worst (requests only) |
|---|---|---|---|---|
| 1 | 16/16 | 19637 | 0 | 394 ps |
| 2 | 16/16 | 19467 | 0 | 49 ps |
| 3 | 16/16 | 19629 | 0 | 347 ps |

(With the reset pins included, draws 2/3 gave -76 / -262 ps on the reset pin pairs; those pairs are not ArbOrd's.)

σ = 0.10 (seed 4, draws 1-2): 16/16 vectors and 0 QQuiet violations after reset on both draws. ArbOrd: draw 1 worst
371 ps; **draw 2 FAILS on a real request pin** (`ucontrol_merge6.uarb1` g1 LUT5, pin A1 from `ucond_br26`: Dr 3010,
DQ 2385, Dq 306, margin -321 ps), yet the run is correct on all 16 vectors. So ArbOrd can fail while the circuit
works, as `Events9ArbB1.grant_fall_after_req_fall` predicts: it is a condition of the C-element grant abstraction,
stricter than what the circuit needs. (One draw, one model; the monitor did not look for the q-pin fall itself.)

## Corrected rerun (`run_all2.sh`, outputs `out2/`; monitors fixed after audit P15a)

QQuiet window per pin k: (tau - TA_k, tau + W - TA_k] (checked both ways: pin changes after an output change and
output changes shortly after a pin change); W = the cell's own loop delay in this GLS (not the Lean band hi).
lowmon on the port each cell drives (27 outputs). ord_static on every reader (both grants and R0) and every
request net (LUT-driven input of ustate$LUT6 other than q; may include A0, conservative): 72 pairs per seed.
gcd_hw R5 rebuilt per seed (md5s = events5/builds.txt, `out2/<seed>/md5.txt`), research GLS at 520a43f.

| run | vectors errs=0 | q flips | QQuiet viol. after reset | before reset | grant/R0 rise before reset | first rise after release | ArbOrd worst (72 pairs) |
|---|---|---|---|---|---|---|---|
| seed d | 16/16 | 20106 | 0 | 80 | 0 | +40.1 ns | 278 ps |
| seed 3 | 16/16 | 18669 | 0 | 80 | 0 | +41.2 ns | 380 ps |
| seed 4 | 16/16 | 19567 | 0 | 48 | 0 | +41.9 ns | 382 ps |
| seed 5 | 16/16 | 20387 | 0 | 128 | 0 | +41.4 ns | 382 ps |
| seed 4, σ 0.05, draw 1 | 16/16 | 19637 | 0 | – | – | – | 298 ps (was "-12 ps": a reset-pin pair, P17 2d) |
| seed 4, σ 0.05, draw 2 | 16/16 | 19467 | 0 | – | – | – | 19 ps |
| seed 4, σ 0.05, draw 3 | 16/16 | 19629 | 0 | – | – | – | 286 ps (was 142: A0/rst pin) |
| seed 4, σ 0.10, draw 1 | 16/16 | 19701 | 0 | – | – | – | 214 ps (was "-410": reset-pin pair) |
| seed 4, σ 0.10, draw 2 | 16/16 | 19359 | 0 | – | – | – | **-346 ps** (merge6 g1, r1) |

CORRECTION (audit P17 row 2d): ord_static's old filter ("any LUT-driven ustate input other than q") admitted
the LUT-buffered reset (one net at the ustate of all 9 arbiters) and A0, which R0 = r1 q + r2 !q does not read.
The scatter-row ord numbers above are P17's recount on the request pairs only (the old 72-pair worst in
parentheses); the filter now takes the request nets from the R0 INIT's support (54 pairs; OLD=1 restores the
old filter). Own rerun (run_ordscat.sh, seed-4 route by md5, provenance per draw in out2/ordscat/): 298 / 19 / 286
ps (σ 0.05 draws 1-3), 214 / -346 ps (σ 0.10 draws 1-2) = P17's recount. The -346 draw fails at merge6 g1
(-346) and R0 (-161), both on r1 from ucond_br26. P17 also notes the σ 0.05 draw 2 change
49 -> 19 ps came from the O5-arc fix, not the pair filter.

So with the corrected checks: QQuiet after reset holds on every run (0 violations), the quiet start holds (no
rise before release, first rise ~40 ns after), ArbOrd holds at the GLS point delays (>= 278 ps) but fails under
per-arc scatter in 1 of 5 draws while every
run computes all 16 vectors: ArbOrd is stricter than the circuit needs. Limitations: GLS model at 520a43f (SDF
points, no fid), W is the GLS loop delay rather than phi(PqQ), only vector 6 for the quiet start, one route for scatter.

Detection controls for the corrected QQuiet monitor (`out2/negctl.txt`): WSCALE=20 -> 90 post-reset violations
(weak: it only shows the pipeline prints). CONTROL=1 (near-threshold): the monitor also watches each ustate's own
feedback pin, whose change lands exactly at the window's end after every flip; on vector 6 it flags 1713 of 1713
post-reset flips, so a pin change at the edge of the window is detected. Remaining limitations (audit P15a): the
GLS run is not shown to be a SatPin(W) behaviour of the Lean model (nextpnr SDF point delays, not shown inside the
prjxray bands); W is the GLS loop delay, not phi(PqQ); ord_static pairs each reader with every request net it
shares with ustate (a superset; simq.py's INIT-based choice is exact); raw flip times are not kept.

## ArbEdge's no-re-request window (RdEdge.nore) for the grant readers (`gen_noremon.py`, `out2/nore4/`)

Window algebra from the Lean field (see the script's docstring): after a flip of q away from branch b at tau, the
request's driver net must be low on [tau - DQ, tau + hi Dq + 2 - lo Dr), with DQ = ustate's ICBUF D + TA on that
request (GLS point delay) and lo Dr / hi Dq the slow-corner bands xarbnet prints for the same route
(`arbnet/results/xan_4_slow.txt`). Each grant's own request is picked by evaluating its INIT (q on the branch, the
other inputs low; GND/VCC ties from PSEUDO_GND/VCC). Seed 4, no scatter, 16 vectors: 18/18 readers mapped,
**0 violations after reset** (8 per vector before reset, X resolution); windows: 0 empty, 12 end before tau,
6 extend past it. Controls (vector 6): window +20 ns -> 0 hits (no re-request that soon), +5 us -> 3195 hits, so
the monitor detects re-requests; from the latter, the earliest re-request after a flip-away is 29.1 ns
(merge10 g2), a margin of >= 29.4 ns over nore's window on every reader. Not covered: the R0 readers (e3/e4),
other seeds/corners, scatter; the GLS delays are not shown inside the prjxray bands; the pre-check looks at the
request's last high interval only.

## ArbEdge's C window (RdEdge.fall) for the grant readers (`gen_cwmon.py`, `out2/cw4/`)

Window from the Lean field: around each fall sigma of the reader's request (driver net), ustate reads A0 high for
u in [sigma + lo Dr - hi Dq, sigma + hi Dr + 2 - lo Dq); with ustate's A0 pin delay DA (GLS point) the A0 driver net
must be high on [sigma + lo Dr - hi Dq - DA, sigma + hi Dr + 2 - lo Dq - DA). A0 and rst are picked from ustate's
INIT (A0: the input with which the output holds q; rst: the input that forces it high); A0's last 16 low intervals
are kept per arbiter. Seed 4, no scatter, 16 vectors (`out2/cw4/table.txt`): all 18 grant readers mapped; every
reader passes on every vector EXCEPT `ucontrol_merge10.uarb1` g1, which misses by exactly **5 ps** on every lap of
12 of 16 vectors (A0 rises 1380 ps before r1 falls; the window needs 1385; e.g. vector 6: A0 rise 1180480, r1 fall
1181860). The run is correct on all 16 vectors. Reading: ArbEdge's C window is tight to a few ps at that reader
(its window end comes from slow-corner band ends mixed with the GLS's point delays, so a 5 ps miss is within the
mismatch of the two delay models; neither the violation nor its absence is established for the chip). It is the
first ArbEdge field found tight on a real route, and the obvious target for the next session (the window comes
from `c_of` in Events9ArbNetEdge; whether a weaker window suffices is open). Not covered: R0 readers, other seeds,
scatter.

Pointwise C (`POINT=1 gen_cwmon.py`, the c_k fields of `Events9ArbB1.ArbEdgeSP`, at the GLS's own point delays;
`out2/cwpt4/`): seed 4, 16 vectors, 18 grant readers: **0 violations over 63995 request falls after reset**
(merge10 g1: A0 read point 244 ps after A0's rise on the lap examined). So the pointwise form, unlike the band
window, has margin on this run. R0 readers not monitored.

Other seeds (`run_edge.sh <seed>`, outputs `out2/edge_<seed>/`; routes rebuilt, md5s = events5/builds.txt; slow
xarbnet bands of the same seed): nore 0 violations (d 19962 / 3 18525 / 5 20243 flip-aways after reset), pointwise C
0 violations (d 66837 / 3 63469 / 5 67193 request falls), 16/16 vectors errs=0 on each. The band C window on seed 5:
0 violations over 67193 falls, so the 5 ps tightness found on seed 4 (merge10 g1) is route-specific.

## ArbEnv window fields (gen_evmon.py + check_env.py, run_env.sh)

gen_evmon logs every change of q, A0, r1, r2 of each arbiter's ustate (EV lines) and writes info.json with the
GLS point delays DA (A0 read), DQ1/DQ2 (ustate's request reads) and per reader Dr/Dq. check_env.py evaluates
Events9ArbB1.ArbEnv's window fields for a fixed-delay behaviour, at the 4 readers g1, g2, s1, s2 of all 9
arbiters, with xarbnet's slow bands for the same route (xan_<seed>_slow.txt; R0 bands minus 2 as in ArbEdgeS):
nore (no re-request after a flip away), rise and flip (every u in the B2 window Settled: A0 read low and q constant
while it stays low), C (A0 read high at the reader's q-read time after a request fall). Only events after the
rig's reset release count.

| seed | vectors 16/16 | events | violations |
|---|---|---|---|
| 5 | yes | 349,792 | 0 |
| d | yes | 347,234 | 0 |
| 3 | yes | 328,020 | 0 |
| 4 | yes | 333,736 | 0 |

Negative controls (seed 5, vector 6): CTRL_DA=3000 (A0 read 3 ns late) and CTRL_E=5000000 (windows widened)
both produce many violations. Limits: GLS at 520a43f with SDF point delays (not the bands, no scatter), the
settle bound H is not monitored, raw EV logs are not kept (only per-vector check_v*.txt and summary.txt).

## QQuiet with the Lean window (XAN=)

gen_qqmon with XAN=xan_5_slow.txt uses W = phi(PqQ) (hi end of the own-q read band, 409..919 ps) instead of the
GLS loop delay. Seed 5: 16/16, 20,387 q flips, 0 violations after reset release, 112 before (out2/qqphi_5).
