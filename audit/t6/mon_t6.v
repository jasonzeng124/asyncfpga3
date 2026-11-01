// T6 monitor (auditor): edges around arbiter 0's acknowledge C-element ua1 in the fid netlist of the target.
// n7330 = SLICE_X2Y18/D6LUT/O6 (ua1, cell c_007111), n7327 = SLICE_X2Y18/A6LUT/O6 (c_007108),
// n30 = SLICE_X0Y18/A6LUT/O6 (g, c_000021), n3416 = ua1's A3 (A0) source, n8600 = urig.out0_req.
module mon_t6;
    integer nu = 0, ng = 0, na = 0, nr = 0, cap = 60;
    always @(tb_run.dut.n7330) begin nu = nu + 1; if (nu <= cap) $display("T6 %0t ua1=%b", $time, tb_run.dut.n7330); end
    always @(tb_run.dut.n30)   begin ng = ng + 1; if (ng <= cap) $display("T6 %0t g=%b", $time, tb_run.dut.n30); end
    always @(tb_run.dut.n7327) begin na = na + 1; if (na <= cap) $display("T6 %0t alut=%b", $time, tb_run.dut.n7327); end
    always @(tb_run.dut.n3416) if ($time < 3000000) $display("T6 %0t A0src=%b", $time, tb_run.dut.n3416);
    always @(tb_run.dut.n8600) begin nr = nr + 1; if (nr <= cap) $display("T6 %0t out0_req=%b", $time, tb_run.dut.n8600); end
    always #500000 $display("T6COUNT %0t ua1_edges=%0d g_edges=%0d alut_edges=%0d out0_req_edges=%0d", $time, nu, ng, na, nr);
endmodule
