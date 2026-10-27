`timescale 1ps/1ps
module tb;
  reg a1=0, a2=1, a3=0;
  wire o5, o6; wire f = a1 & a2;
  SLICE_LUTX #(.INIT(64'h8888888888888888)) u(.A1(a1),.A2(a2),.A3(a3),.A4(1'b0),.A5(1'b0),.A6(1'b0),.O5(o5),.O6(o6));
  initial begin
    $monitor("%0t a1=%b a3=%b f=%b o6=%b", $time, a1, a3, f, o6);
    #1000 a1=1;
    #50 a1=0;
    #50 a3=1;
    #100 a1=1;
    #1000 $finish;
  end
endmodule
