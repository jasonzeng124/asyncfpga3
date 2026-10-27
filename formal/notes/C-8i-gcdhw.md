# C-8i: the gcd graph bdc emits for gcd_hw, imported, computes the C gcd

(interim notes, being filled in)

* gcd_hw (cells/hw/gcd_hw.v, build_hw.sh) instantiates bdc_gcd emitted from
  build/frontend/gcd/comp/handshake_transformed.mlir = Dynamatic's gcd fixture
  (cloud/fixtures/frontend/gcd/comp/). No separate kernel source; the C is the
  fixture's cf_transformed.mlir (Dynamatic integration-test gcd.c, binary gcd).
* Importer formal/tools/dfimport/mlir2lean.py: imports bdc/hs/parse.py and
  bdc/emit.py read-only, uses bdc's Emitter widths and fusion plan.
  239 MLIR ops -> 158 rules, 252 channels, spine 34 control channels.
* Formal/Net/GcdHwLib.lean: checks (no sorry). Formal/Net/GcdHw.lean (generated):
  WF/spine checks by decide +kernel, ~15 s. Formal/Net/GcdHwSeg.lean (generated):
  18 symbolic segments, 10 templates, ~3 min, 1.7 GB.
