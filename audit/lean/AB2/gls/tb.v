`timescale 1ps/1ps
module tb;
  reg a1=0, a2=0;
  wire o5, o6; wire f = a1 ^ a2;
  // XOR of A1,A2 on O6 (INIT 0x6 replicated)
  SLICE_LUTX #(.INIT(64'h6666666666666666)) u(.A1(a1),.A2(a2),.A3(1'b0),.A4(1'b0),.A5(1'b0),.A6(1'b0),.O5(o5),.O6(o6));
  initial begin
    $monitor("%0t a1=%b a2=%b f=%b o6=%b", $time, a1, a2, f, o6);
    // T1: simultaneous a1,a2 rise (f constant)  -> expect no output event
    #1000 a1=1; a2=1;
    #1000 a1=0; a2=0;
    // T2: f changes at 3000 (a1 up), pin a2 changes at 3050 (f back to 0), a2 down at 3100 (f=1 again)
    #1000 a1=1;
    #50 a2=1;
    #50 a2=0;
    // T3: pulse narrower than d then later pulse (early propagation)
    #1000 a1=0;
    #10 a1=1;
    #110 a1=0;
    #10 a1=1;
    // T4: tie: pulse of width exactly d
    #2000 a1=0;
    #124 a1=1;
    #2000 $finish;
  end
endmodule
