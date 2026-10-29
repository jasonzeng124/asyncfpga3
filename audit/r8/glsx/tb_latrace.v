`timescale 1ps/1ps
// Auditor tb (r8): SLICE_LATX D change at / near the closing CK edge (GHIGH=1, TCKQ=100).
// Silicon: within the setup/hold window the stored value is undetermined (x or metastable).
module tb;
  reg ck, d, ce, sr; wire q;
  SLICE_LATX #(.INIT(1'b0), .GHIGH(1'b1), .TCKQ(100)) L (.CK(ck), .D(d), .CE(ce), .SR(sr), .Q(q));
  initial begin
    ck = 1; ce = 1; sr = 0; d = 0;
    #1000 d = 1; ck = 0;                 // same instant
    #1000 $display("T1 D rise == CK close        : Q=%b", q);
    ck = 1; #500 d = 0; #500;            // reopen, q=0
    #0 d = 1; #3 ck = 0;                 // D 3 ps before close
    #1000 $display("T2 D rise 3ps before close  : Q=%b", q);
    ck = 1; #500 d = 0; #500;
    #0 ck = 0; #3 d = 1;                 // D 3 ps after close
    #1000 $display("T3 D rise 3ps after close   : Q=%b", q);
    $finish;
  end
endmodule
