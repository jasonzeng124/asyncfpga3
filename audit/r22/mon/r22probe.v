`timescale 1ps/1ps
// negative-control probe: the A-pins of c_002643 (drives rig_res_data[5]) at every lap
module r22probe;
    always @(posedge tb_run.`RIG_LAP)
        $display("R22PROBE t=%0t A1..A6=%b%b%b%b%b%b", $time, tb_run.dut.c_002643.A1, tb_run.dut.c_002643.A2,
                 tb_run.dut.c_002643.A3, tb_run.dut.c_002643.A4, tb_run.dut.c_002643.A5, tb_run.dut.c_002643.A6);
endmodule
