// auditor's monitor (audit/t2): edges of the gcd kernel's boundary handshakes in the fid netlist of the target
// n7232 urig.a_ack, n7231 urig.b_ack, n7237 urig.in_acks[2] (start_ack), n7239 urig.in_ack (fork join), n8600 urig.out0_req
module mon_t2;
    always @(tb_run.dut.n7232) if ($time < 30000000) $display("T2 %0t a_ack=%b", $time, tb_run.dut.n7232);
    always @(tb_run.dut.n7231) if ($time < 30000000) $display("T2 %0t b_ack=%b", $time, tb_run.dut.n7231);
    always @(tb_run.dut.n7237) if ($time < 30000000) $display("T2 %0t start_ack=%b", $time, tb_run.dut.n7237);
    always @(tb_run.dut.n7239) if ($time < 30000000) $display("T2 %0t in_ack=%b", $time, tb_run.dut.n7239);
    always @(tb_run.dut.n8600) if ($time < 30000000) $display("T2 %0t out0_req=%b", $time, tb_run.dut.n8600);
endmodule
