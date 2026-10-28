`timescale 1ps/1ps
module arb_handover;
  reg rst=1, r1=0, r2=0, A0=0;
  wire A1,A2,R0,g1,g2;
  bd_arbiter dut(.rst(rst),.r1(r1),.A1(A1),.r2(r2),.A2(A2),.R0(R0),.A0(A0),.g1(g1),.g2(g2));
  initial begin
    $monitor("%7t r1=%b r2=%b q=%b g1=%b g2=%b R0=%b A0=%b A1=%b A2=%b",
             $time,r1,r2,dut.q,g1,g2,R0,A0,A1,A2);
    #2000 rst=0; #2000;
    // both clients ask, server serves
    r1=1; r2=1; #2000;
    A0=1; #2000;          // server acknowledges the (single) request
    r1=0;  #2000;         // client 1 completes its request phase
    A0=0; #3000;          // server returns to zero
    #4000;
    $finish;
  end
endmodule
