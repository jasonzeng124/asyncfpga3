// ledtest -- EBAZ4205 first-light bitstream: proves the openXC7 bit
// format, the JTAG load path, and live fabric (LUTs, routing, FFs,
// clocking) with ZERO dependencies on the boot chain, the PS, or any
// external clock -- the EBAZ4205 has no PL oscillator, and this design
// doesn't need one: a 15-stage ring oscillator (kept LUT1 inverters,
// ~1-2 ns/stage -> roughly 15-35 MHz) feeds a divider through a BUFG.
// Signature: red LED solid on, green LED blinking ~1-2 Hz. A loaded but
// dead fabric shows red-only; an unloaded PL shows neither.
//
// Build (same chipdb/xdc as zynq/build_xc7.sh; ring is a combinational
// loop, hence --ignore-loops):
//   yosys -q -p "read_verilog zynq/ledtest.v; synth_xilinx -flatten \
//     -arch xc7 -top ledtest; write_json build/ledtest/ledtest.json"
//   nextpnr-xilinx --chipdb <xc7z010.bin> --xdc zynq/ebaz4205.xdc \
//     --json build/ledtest/ledtest.json --fasm build/ledtest/ledtest.fasm \
//     --ignore-loops --timing-allow-fail
//   fasm2frames + xc7frames2bit as in zynq/build_xc7.sh
module ledtest (
  output led_red,
  output led_green
);
  wire [14:0] ring;
  genvar i;
  generate for (i = 0; i < 15; i = i + 1) begin : stage
    (* keep *) LUT1 #(.INIT(2'b01)) inv (.I0(ring[i]), .O(ring[(i + 1) % 15]));
  end endgenerate

  wire oscclk;
  BUFG gb (.I(ring[0]), .O(oscclk));

  reg [23:0] div = 24'd0;
  always @(posedge oscclk) div <= div + 24'd1;

  assign led_red   = 1'b1;
  assign led_green = div[23];
endmodule
