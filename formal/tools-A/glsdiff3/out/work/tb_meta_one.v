`timescale 1ps/1ps
module tb_meta_centre;
integer S, i, n1, nx; reg b = 0, rst = 1;
wire [0:0] q, qf;
SLICE_LUTX #(.INIT(64'h00E8_00E8_00E8_00E8), .META6(1), .TLOOP6(424), .SEED(1)) u0 (.A1(1'b1), .A2(b), .A3(qf[0]), .A4(rst), .A5(1'b0), .A6(1'b0), .O6(q[0]), .O5());
ICBUF #(.D(300)) w0 (.I(q[0]), .O(qf[0]));
always @(q[0]) $display("Q %0d %b", $time, q[0]);
initial begin
  if (!$value$plusargs("S=%d", S)) S = 100;
  #500 rst = 0; #500 b = 1; #(S) b = 0;
  #40000;
  n1 = 0; nx = 0;
  for (i = 0; i < 1; i = i + 1) begin if (q[i] === 1'b1) n1 = n1 + 1; else if (q[i] !== 1'b0) nx = nx + 1; end
  $display("S %0d q1 %0d qx %0d of 1", S, n1, nx);
  $finish;
end
endmodule
