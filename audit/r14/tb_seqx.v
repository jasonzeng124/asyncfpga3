// audit r14: X semantics of SLICE_FFX / SLICE_LATX (research prims.v, 6524fa3 == wt-r13).
// Expected = Kleene (the value is forced only if every resolution of the x agrees).
`timescale 1ps/1ps
module tb_seqx;
  reg ck = 0;
  // flops: name, INIT, SRVAL; inputs held constant, one clean clock edge at 5000
  reg  [5:0] fd, fce, fsr;
  wire [5:0] fq;
  //            case: 0       1       2       3       4         5
  //  meaning:  SR=x  SR=x    CE=x    CE=x    SR=x,D=SRVAL  CE=x,D=Q
  //  INIT:     0     1       0       1       0             1
  //  D:        1     1       1       0       0             1
  //  CE:       1     0       x       x       1             x
  //  SR:       x     x       0       0       x             0
  //  expect:   x     x       x       x       0             1
  SLICE_FFX #(.INIT(1'b0), .SRVAL(1'b0)) f0 (.CK(ck), .D(fd[0]), .CE(fce[0]), .SR(fsr[0]), .Q(fq[0]));
  SLICE_FFX #(.INIT(1'b1), .SRVAL(1'b0)) f1 (.CK(ck), .D(fd[1]), .CE(fce[1]), .SR(fsr[1]), .Q(fq[1]));
  SLICE_FFX #(.INIT(1'b0), .SRVAL(1'b0)) f2 (.CK(ck), .D(fd[2]), .CE(fce[2]), .SR(fsr[2]), .Q(fq[2]));
  SLICE_FFX #(.INIT(1'b1), .SRVAL(1'b0)) f3 (.CK(ck), .D(fd[3]), .CE(fce[3]), .SR(fsr[3]), .Q(fq[3]));
  SLICE_FFX #(.INIT(1'b0), .SRVAL(1'b0)) f4 (.CK(ck), .D(fd[4]), .CE(fce[4]), .SR(fsr[4]), .Q(fq[4]));
  SLICE_FFX #(.INIT(1'b1), .SRVAL(1'b0)) f5 (.CK(ck), .D(fd[5]), .CE(fce[5]), .SR(fsr[5]), .Q(fq[5]));
  // aperture case (fid only path): CE = x, D moves 10 ps before CK, INIT 0
  reg ad = 0, ack = 0;
  wire aq;
  SLICE_FFX #(.INIT(1'b0), .SRVAL(1'b0)) fa (.CK(ack), .D(ad), .CE(1'bx), .SR(1'b0), .Q(aq));
  // latches (GHIGH 1): L1 closed gate, CE=x, D!=q (expect q=0 hold)
  //                    L2 SR=x, open, CE=1, D=0=SRVAL, q=0 (expect 0)
  //                    L3 gate x, CE=0, D=1, q=0 (expect 0 hold)
  reg [2:0] lck, ld, lce, lsr;
  wire [2:0] lq;
  SLICE_LATX #(.INIT(1'b0), .SRVAL(1'b0)) l1 (.CK(lck[0]), .D(ld[0]), .CE(lce[0]), .SR(lsr[0]), .Q(lq[0]));
  SLICE_LATX #(.INIT(1'b0), .SRVAL(1'b0)) l2 (.CK(lck[1]), .D(ld[1]), .CE(lce[1]), .SR(lsr[1]), .Q(lq[1]));
  SLICE_LATX #(.INIT(1'b0), .SRVAL(1'b0)) l3 (.CK(lck[2]), .D(ld[2]), .CE(lce[2]), .SR(lsr[2]), .Q(lq[2]));
  initial begin
    fd  = 6'b100111;  // bit5..0
    fce = 6'bx1xx01;
    fsr = 6'b0x00xx;
    lck = 3'b0;  ld = 3'b0; lce = 3'b0; lsr = 3'b0;   // all closed, q=0
    #1000 lck = 3'b000; ld = 3'b101; lce = 3'b01x; lsr = 3'b0x0;
    #10   lck[1] = 1'b1;  lck[2] = 1'bx;              // L2 open, L3 gate x
    #4000 ck = 1;
    #3000;
    $display("FF  cases 0..5 (expect x x x x 0 1): %b %b %b %b %b %b", fq[0], fq[1], fq[2], fq[3], fq[4], fq[5]);
    $display("LAT L1..L3      (expect 0 0 0)     : %b %b %b", lq[0], lq[1], lq[2]);
    #1000 ad = 1; #10 ack = 1; #3000;
    $display("FF  aperture CE=x, D 0->1 10ps before CK (Kleene: x): %b", aq);
    $finish;
  end
endmodule
