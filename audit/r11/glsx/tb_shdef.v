`timescale 1ps/1ps
// Auditor tb (r11): DEFAULT SLICE_FFX setup/hold check, per pin.
// a: parameters as NEW gen.py bakes a D+CE+SR flop (TSU 109 = CE setup, THD 262 = D hold)
// b: as OLD gen.py baked the same flop (only SR 100/100 parsed)
// c: as OLD gen.py baked a D+CE flop (nothing parsed -> TSU=THD=0)
module tb;
  reg ck=0, d=0, ce=1, sr=0;
  wire qa, qb, qc;
  SLICE_FFX #(.TCKQ(340), .TSU(109), .THD(262)) a (.CK(ck), .D(d), .CE(ce), .SR(sr), .Q(qa));
  SLICE_FFX #(.TCKQ(340), .TSU(100), .THD(100)) b (.CK(ck), .D(d), .CE(ce), .SR(sr), .Q(qb));
  SLICE_FFX #(.TCKQ(340)) c (.CK(ck), .D(d), .CE(ce), .SR(sr), .Q(qc));
  task pulse; begin ck = 1; #1000 ck = 0; #1000; end endtask
  initial begin
    #1000 pulse;
    $display("-- T1 D 0->1 50 ps before CK (inside every window)");
    d = 1; #50 pulse; $display("   qa=%b qb=%b qc=%b", qa, qb, qc);
    $display("-- T2 D 1->0 150 ps after CK (inside D hold 241/262, outside SR's 100)");
    ck = 1; #150 d = 0; #850 ck = 0; #1000 $display("   qa=%b qb=%b qc=%b", qa, qb, qc);
    d = 0; pulse; pulse;
    $display("-- T3 CE 1->0 80 ps after CK (CE hold is -9 in the SDF: legal; model flags it)");
    ck = 1; #80 ce = 0; #920 ck = 0; #1000 $display("   qa=%b qb=%b qc=%b", qa, qb, qc);
    ce = 1; pulse; pulse;
    d = 1; pulse; pulse;
    $display("-- T4 SR 0->1 10 ps before CK (inside SR's 100/100 window): Q=1 before");
    sr = 1; #10 pulse; $display("   qa=%b qb=%b qc=%b", qa, qb, qc);
    $display("-- T5 SR 1->0 20 ps after CK");
    ck = 1; #20 sr = 0; #980 ck = 0; #1000 $display("   qa=%b qb=%b qc=%b", qa, qb, qc);
    $finish;
  end
endmodule
