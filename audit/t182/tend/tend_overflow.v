`timescale 1ps/1ps
module t; integer tend; reg d;
initial begin d=0; if (!$value$plusargs("TEND=%d", tend)) tend=5000000; #(tend*1000); d=1; $display("FIRED at %0t", $time); $finish; end
initial begin #(64'd30000000000); $display("NOT FIRED by 30 ms"); $finish; end
endmodule
