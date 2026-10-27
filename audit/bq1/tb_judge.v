// Audit judge: independent of the rig's MISM/err/ok.  Drives the routed
// netlist exactly as cells/gls/tb_run.v does (ring kick + idx force), and
// prints the delivered gcd (rig_res_data) at every rig_lap rise and fall.
`timescale 1ps/1ps
module tb_judge;
    top dut ();
    `include "judge.vh"
    integer vec, tend, laps, chg;
    reg [31:0] at_rise;
    initial begin
        vec = 0; tend = 150000; laps = 0; chg = 0;
        if ($value$plusargs("VEC=%d", vec)) ;
        if ($value$plusargs("TEND=%d", tend)) ;
        $display("J VEC %0d TEND %0d", vec, tend);
        force `J_IDX0 = vec[0]; force `J_IDX1 = vec[1];
        force `J_IDX2 = vec[2]; force `J_IDX3 = vec[3];
    end
    initial begin force `J_FB = 1'b0; #50000; release `J_FB; end
    always @(negedge `J_RST)
        $display("J RSTREL t=%0t idx=%b%b%b%b", $time, `J_IDX3, `J_IDX2, `J_IDX1, `J_IDX0);
    always @(posedge `J_LAP) begin
        laps = laps + 1; at_rise = `J_RES;
        $display("J RISE %0d %0t %h", laps, $time, `J_RES);
    end
    always @(negedge `J_LAP) if (laps > 0)
        $display("J FALL %0d %0t %h", laps, $time, `J_RES);
    always @(`J_RES) if (`J_LAP === 1'b1) begin
        chg = chg + 1;
        $display("J CHG %0d %0t %h", laps, $time, `J_RES);
    end
    initial begin #(tend * 1000); $display("J END laps=%0d chg=%0d t=%0t", laps, chg, $time); $finish; end
endmodule
