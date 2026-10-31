# glsq: QQuiet monitor on the research routed GLS (lead, 2026-10-31; UNTRUSTED evidence, not a theorem)

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
