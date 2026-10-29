`timescale 1ps/1ps
module tb_gate;
    top dut ();
    initial begin
        $sdf_annotate("annot.sdf", dut);
        $display("ANNOTATE_DONE");
        $finish;
    end
endmodule
