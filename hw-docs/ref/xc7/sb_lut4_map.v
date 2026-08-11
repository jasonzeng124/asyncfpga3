// techmap: SB_LUT4 (iCE40) -> LUT4 (Xilinx 7-series), used by synth.ys AFTER
// synth_xilinx and immediately before loop_breaker dissolution.
//
// Init-bit math: both cells index their init word with the SAME bit order,
//   O = INIT[{I3, I2, I1, I0}]
// (compare the mux trees in yosys's +/ice40/cells_sim.v SB_LUT4 and
// +/xilinx/cells_sim.v LUT4 -- they are line-for-line identical), and the
// Vivado/prjxray LUT4 INIT convention is the same. So the mapping is the
// identity: pins pass through 1:1 and INIT = LUT_INIT with NO permutation.
//
// Do not take that on faith: boards/xc7/check_lut_map.sh SAT-proves this
// exact file against both vendors' simulation models for a battery of
// asymmetric init values, and run_flow.sh runs it on every build.
module SB_LUT4 (output O, input I0, I1, I2, I3);
  parameter [15:0] LUT_INIT = 16'h0000;
  LUT4 #(.INIT(LUT_INIT)) _TECHMAP_REPLACE_ (
    .O(O), .I0(I0), .I1(I1), .I2(I2), .I3(I3));
endmodule
