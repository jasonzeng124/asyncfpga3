#!/usr/bin/env python3
"""gen_meta.py N [WIRE] (copy of glsdiff/gen_meta_centre.py with the feedback wire a parameter; TLOOP = WIRE + 124)  --  N > tb_meta_centre.v -- N independent bd_c2 self-loops (fid resolver
SEED 1..N), each the Lean CElemInvolution OR loop: a=1, rst=1 until 500 then 0, b a runt [1000,1000+S),
q fed back through a 300 ps ICBUF, so TLOOP = 300 + 124 = 424 (gen.py's rule)."""
import sys
N = int(sys.argv[1]) if len(sys.argv) > 1 else 200
WIRE = int(sys.argv[2]) if len(sys.argv) > 2 else 300
L = ["`timescale 1ps/1ps", "module tb_meta_centre;", "integer S, i, n1, nx; reg b = 0, rst = 1;",
     "wire [%d:0] q, qf;" % (N - 1)]
for i in range(N):
    L.append("SLICE_LUTX #(.INIT(64'h00E8_00E8_00E8_00E8), .META6(1), .TLOOP6(%d), .SEED(%d)) u%d "
             "(.A1(1'b1), .A2(b), .A3(qf[%d]), .A4(rst), .A5(1'b0), .A6(1'b0), .O6(q[%d]), .O5());" % (WIRE + 124, i + 1, i, i, i))
    L.append("ICBUF #(.D(%d)) w%d (.I(q[%d]), .O(qf[%d]));" % (WIRE, i, i, i))
L += ["initial begin", '  if (!$value$plusargs("S=%d", S)) S = 100;',
      "  #500 rst = 0; #500 b = 1; #(S) b = 0;", "  #40000;", "  n1 = 0; nx = 0;",
      "  for (i = 0; i < %d; i = i + 1) begin if (q[i] === 1'b1) n1 = n1 + 1; else if (q[i] !== 1'b0) nx = nx + 1; end" % N,
      '  $display("S %%0d q1 %%0d qx %%0d of %d", S, n1, nx);' % N, "  $finish;", "end", "endmodule"]
print("\n".join(L))
