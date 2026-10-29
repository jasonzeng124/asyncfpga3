`timescale 1ps/1ps
// bd_c2 (cells/rtl/bd_ce.v:34) as the fid GLS builds it: SLICE_LUTX (GLS_FID) with
// q routed back to A3 through a transport ICBUF; gen.py's TLOOP = wire + A3 arc.
module tb_c2;
  parameter integer TW = 100, T3 = 100, T = 50;   // feedback wire, A3 arc, other arcs
  reg a = 1'b1, b = 1'b0, rst = 1'b1;
  wire q, qfb;
  ICBUF #(.D(TW)) fb (.I(q), .O(qfb));
  SLICE_LUTX #(.INIT(64'h00E8_00E8_00E8_00E8), .TA1O6(T), .TA2O6(T), .TA3O6(T3), .TA4O6(T),
               .META6(1), .TLOOP6(TW + T3), .SEED(7)) u
    (.A1(a), .A2(b), .A3(qfb), .A4(rst), .A5(1'b0), .A6(1'b0), .O6(q), .O5());
  integer w, tb0, k;
  initial begin
    $monitor("%0t q=%b", $time, q);
    #2000 rst = 1'b0;
    // runts and wide pulses on b, each followed by a reset that empties the cell
    for (k = 0; k < 12; k = k + 1) begin
      w = (k == 0) ? 20 : (k == 1) ? 100 : (k == 2) ? 120 : (k == 3) ? 125 : (k == 4) ? 140 :
          (k == 5) ? 150 : (k == 6) ? 160 : (k == 7) ? 175 : (k == 8) ? 190 : (k == 9) ? 199 :
          (k == 10) ? 200 : 300;
      #5000 $display("PULSE tb=%0t w=%0d", $time, w); b = 1'b1; #(w) b = 1'b0;
      #10000 rst = 1'b1; #2000 rst = 1'b0;
    end
    #5000 $finish;
  end
endmodule
