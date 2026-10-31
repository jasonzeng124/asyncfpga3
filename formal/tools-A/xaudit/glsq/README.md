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
