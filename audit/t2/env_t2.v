// auditor's pipelined-environment replay (audit/t2): replaces gcd_rig's env node in the fid netlist of the target
// +PIPE=1: pair 2 offered right after pair 1's input handshake; +PIPE=0: only after pair 1's result. +A1 +B1 +A2 +B2 (hex)
module env_t2;
  reg [31:0] A1, B1, A2, B2; integer pipe, nout; reg [31:0] r;
  task offer(input [31:0] av, input [31:0] bv); begin
    force tb_run.dut.n8529 = av[0]; force tb_run.dut.n8530 = av[1]; force tb_run.dut.n10935 = av[2]; force tb_run.dut.n8642 = av[3]; force tb_run.dut.n9502 = av[4]; force tb_run.dut.n10257 = av[5]; force tb_run.dut.n9797 = av[7]; force tb_run.dut.n8619 = av[8]; force tb_run.dut.n10936 = av[9]; force tb_run.dut.n10258 = av[10]; force tb_run.dut.n8839 = av[11]; force tb_run.dut.n8842 = av[12]; force tb_run.dut.n8617 = av[13]; force tb_run.dut.n9471 = av[14]; force tb_run.dut.n10937 = av[15]; force tb_run.dut.n11108 = av[16]; force tb_run.dut.n9189 = av[17]; force tb_run.dut.n10238 = av[19]; force tb_run.dut.n10230 = bv[0]; force tb_run.dut.n10231 = bv[1]; force tb_run.dut.n10240 = bv[2]; force tb_run.dut.n10229 = bv[3]; force tb_run.dut.n10539 = bv[4]; force tb_run.dut.n10523 = bv[5]; force tb_run.dut.n10938 = bv[6]; force tb_run.dut.n9509 = bv[7]; force tb_run.dut.n9501 = bv[8]; force tb_run.dut.n9230 = bv[9]; force tb_run.dut.n10522 = bv[10]; force tb_run.dut.n8840 = bv[11]; force tb_run.dut.n8618 = bv[12]; force tb_run.dut.n8650 = bv[13]; force tb_run.dut.n9690 = bv[14]; force tb_run.dut.n10538 = bv[15]; force tb_run.dut.n10239 = bv[16]; force tb_run.dut.n9689 = bv[17]; force tb_run.dut.n9235 = bv[18]; force tb_run.dut.n8775 = bv[19];
    #2000; force tb_run.dut.n7234 = 1'b1; $display("T2B %0t offer a=%h b=%h", $time, av, bv);
    wait (tb_run.dut.n7239 === 1'b1); #500; force tb_run.dut.n7234 = 1'b0;
    wait (tb_run.dut.n7239 === 1'b0); $display("T2B %0t input handshake done a=%h b=%h", $time, av, bv);
  end endtask
  initial begin
    if (!$value$plusargs("PIPE=%d", pipe)) pipe = 1;
    if (!$value$plusargs("A1=%h", A1)) A1 = 32'h20; if (!$value$plusargs("B1=%h", B1)) B1 = 32'h12B87CA0;
    if (!$value$plusargs("A2=%h", A2)) A2 = 32'h5; if (!$value$plusargs("B2=%h", B2)) B2 = 32'h5;
    nout = 0; force tb_run.dut.n7234 = 1'b0; force tb_run.dut.n5852 = 1'b0;
    #2000000;  // well after reset release
    offer(A1, B1);
    if (pipe == 0) wait (nout >= 1);
    offer(A2, B2);
  end
  always @(posedge tb_run.dut.n8600) if ($time > 2000000) begin
    #3000; r = {tb_run.dut.n4497, tb_run.dut.n4472, tb_run.dut.n4459, tb_run.dut.n5009, tb_run.dut.n4499, tb_run.dut.n4461, tb_run.dut.n5011, tb_run.dut.n4463, tb_run.dut.n5013, tb_run.dut.n4438, tb_run.dut.n5015, tb_run.dut.n4474, tb_run.dut.n4476, tb_run.dut.n4478, tb_run.dut.n5017, tb_run.dut.n4503, tb_run.dut.n4501, tb_run.dut.n4505, tb_run.dut.n5019, tb_run.dut.n4507, tb_run.dut.n4509, tb_run.dut.n5048, tb_run.dut.n5050, tb_run.dut.n5021, tb_run.dut.n5052, tb_run.dut.n5054, tb_run.dut.n5023, tb_run.dut.n5468, tb_run.dut.n5457, tb_run.dut.n5056, tb_run.dut.n5452, tb_run.dut.n5454};
    nout = nout + 1; $display("T2B %0t out0 #%0d = %h", $time, nout, r);
    force tb_run.dut.n5852 = 1'b1; wait (tb_run.dut.n8600 === 1'b0); #500; force tb_run.dut.n5852 = 1'b0;
  end
endmodule
