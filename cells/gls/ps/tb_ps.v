`timescale 1ps/1ps
// tb_ps -- GLS testbench for hw/gcd_ps.v.  All stimulus and checking lives in
// the behavioural PS7_PS7 (ps7_master.v): it is the only driver gcd_ps has.
// +TEND=<ns> bounds the run (default 5 ms); +ANNOTATE=1 as cells/gls/tb_run.v.
module tb_ps;
    top dut ();
    integer tend; reg annotate;
    initial begin
        tend = 5000000; annotate = 0;
        if ($value$plusargs("TEND=%d", tend)) ;
        if ($value$plusargs("ANNOTATE=%d", annotate)) ;
        if (annotate) begin $sdf_annotate("annot.sdf", dut); $display("# sdf annotate done"); end
        #(tend * 1000);
        $display("PSSUMMARY TIMEOUT at %0d ns (the PS7 model never finished)", tend);
        $finish;
    end
endmodule
