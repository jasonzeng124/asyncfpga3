`timescale 1ps/1ps
// GLSResolveGen.late_runt on the fid GLS: bd_c2 (as tb_c2.v), a runt W on b, a 1 ps gap,
// then b high for W2 ps (W2 >= TLOOP: B's c2_follow_hold sets the C-element).
module tb_late;
  parameter integer TW = 100, T3 = 100, T = 50, W = 140, W2 = 300;
  reg a = 1'b1, b = 1'b0, rst = 1'b1;
  wire q, qfb;
  ICBUF #(.D(TW)) fb (.I(q), .O(qfb));
  SLICE_LUTX #(.INIT(64'h00E8_00E8_00E8_00E8), .TA1O6(T), .TA2O6(T), .TA3O6(T3), .TA4O6(T),
               .META6(1), .TLOOP6(TW + T3), .SEED(7)) u
    (.A1(a), .A2(b), .A3(qfb), .A4(rst), .A5(1'b0), .A6(1'b0), .O6(q), .O5());
  initial begin
    $monitor("%0t q=%b", $time, q);
    #2000 rst = 1'b0;
    #5000 $display("LATE tb=%0t w=%0d w2=%0d", $time, W, W2);
    b = 1'b1; #(W) b = 1'b0; #1 b = 1'b1; #(W2) b = 1'b0;
    #20000 $finish;
  end
endmodule
