`timescale 1ps/1ps
// Auditor probe: edge times at one flop's pins (c_001621 = hk_cnt[1] flop, slice$4760)
module probe_ff;
  integer n = 0; time tck = 0; always @(posedge tb_run.dut.c_001621.CK) tck = $time;
  always @(tb_run.dut.c_001621.D or tb_run.dut.c_001621.CE or tb_run.dut.c_001621.Q)
    if (n < 60) begin n = n + 1;
      $display("PROBE t=%0t (CK rose %0t ago) CK=%b D=%b CE=%b Q=%b TSU=%0d THD=%0d", $time, $time - tck, tb_run.dut.c_001621.CK,
        tb_run.dut.c_001621.D, tb_run.dut.c_001621.CE, tb_run.dut.c_001621.Q,
        tb_run.dut.c_001621.TSU, tb_run.dut.c_001621.THD); end
endmodule
