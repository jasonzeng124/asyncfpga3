// tb_seq_x.v -- X handling of the research GLS's SLICE_LATX (LDCE) and SLICE_FFX
// (FDRE), against Lean Gen/Netlist.lean's Kleene tables (LDCE_INIT, FDRE_M/FFQ_SYNC
// through Core Lut.keval).  Each case prints  CASE <name> <q>.
`timescale 1ps/1ps
module tb_seq_x;
    reg l_ck, l_d, l_ce, l_sr;
    wire l_q;
    // LDCE: GHIGH=1 (open while CK=1), SRVAL=0 (CLR), INIT 0
    SLICE_LATX #(.INIT(1'b0), .SRVAL(1'b0), .GHIGH(1'b1), .TCKQ(100)) ul
        (.CK(l_ck), .D(l_d), .CE(l_ce), .SR(l_sr), .Q(l_q));
    reg f_ck, f_d, f_ce, f_sr;
    wire f_q;
    SLICE_FFX #(.INIT(1'b0), .SRVAL(1'b0), .TCKQ(100)) uf
        (.CK(f_ck), .D(f_d), .CE(f_ce), .SR(f_sr), .Q(f_q));
    initial begin
        // L1: latch closed (CK=0), CE goes x, D differs from q=0.  Lean: hold 0.
        l_sr = 0; l_ck = 0; l_ce = 0; l_d = 0; #1000;
        l_d = 1; #1000; l_ce = 1'bx; #1000;
        $display("CASE L1_closed_ce_x %b", l_q);
        // L2: CLR = x while open with D = 0 = q.  Lean: merge(0, 0) = 0.
        l_ce = 1; l_d = 0; l_ck = 1; #1000; l_sr = 1'bx; #1000;
        $display("CASE L2_clr_x_agree %b", l_q);
        // L3: CLR = x, latch closed, q = 0.  Lean: merge(0, q=0) = 0.
        l_sr = 0; #500; l_ck = 0; #500; l_d = 1; l_sr = 1'bx; #1000;
        $display("CASE L3_clr_x_closed %b", l_q);
        // F1: FDRE, R = x at the clock, CE = 1, D = 1, Q = 0.  Lean: X (merge(0, 1)).
        f_ck = 0; f_sr = 0; f_ce = 1; f_d = 0; #1000;
        f_ck = 1; #1000; f_ck = 0; #1000;              // Q = 0
        f_d = 1; f_sr = 1'bx; #1000; f_ck = 1; #1000; f_ck = 0; #1000;
        $display("CASE F1_r_x_d1 %b", f_q);
        // F2: FDRE, CE = x at the clock, R = 0, D = 0, Q = 1 (load 1 first).  Lean: X.
        f_sr = 0; f_ce = 1; f_d = 1; #1000; f_ck = 1; #1000; f_ck = 0; #1000;   // Q = 1
        f_d = 0; f_ce = 1'bx; #1000; f_ck = 1; #1000; f_ck = 0; #1000;
        $display("CASE F2_ce_x %b", f_q);
        $finish;
    end
endmodule
