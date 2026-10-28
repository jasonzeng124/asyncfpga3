`timescale 1ps / 1ps

// ---------------------------------------------------------------------------
// tb_arb_prot -- does hw/arb_prot.v's harness actually run?
//
// The rig's whole result is "two sticky bits stayed at zero", and a rig that
// never ran produces exactly that.  Before spending a build and a board on it,
// this bench checks the three things that make its zeros mean something:
//
//   1. the self-timed clients free-run -- r = delay(~A) really does cycle
//   2. both clients get served, repeatedly, under sustained contention
//   3. the serv detector (A1 ^ A2) fires, while viol (A1 . A2) and the
//      width-filtered grant overlap do not
//
// It instantiates the harness directly rather than the whole top, because
// BSCANE2 and the readback path are not what is in question here.
// ---------------------------------------------------------------------------
module tb_arb_prot;

    localparam integer H = `BD_HOP_PS;

    localparam integer CLEN1 = 3;
    localparam integer CLEN2 = 5;
    localparam integer SLEN  = 2;
    localparam integer WFILT = 2;

    reg rst = 1'b1;

    wire r1, r2, A1, A2, R0, A0, g1, g2;

    bd_arbiter uarb (.rst(rst), .r1(r1), .A1(A1), .r2(r2), .A2(A2),
                     .R0(R0), .A0(A0), .g1(g1), .g2(g2));

    bd_delay #(.N(SLEN)) usrv (.a(R0), .z(A0));

    wire c1_n, c2_n;
    LUT1 #(.INIT(2'h1)) uinv1 (.I0(A1), .O(c1_n));
    LUT1 #(.INIT(2'h1)) uinv2 (.I0(A2), .O(c2_n));
    bd_delay #(.N(CLEN1)) uc1 (.a(c1_n), .z(r1));
    bd_delay #(.N(CLEN2)) uc2 (.a(c2_n), .z(r2));

    // the three detectors, exactly as the rig builds them
    wire viol_raw, serv_raw, ovl_raw, ovl_d, ovl_flt;
    LUT2 #(.INIT(4'h8)) uviol_d (.I0(A1), .I1(A2), .O(viol_raw));
    LUT2 #(.INIT(4'h6)) userv_d (.I0(A1), .I1(A2), .O(serv_raw));
    LUT2 #(.INIT(4'h8)) uovl_d  (.I0(g1), .I1(g2), .O(ovl_raw));
    bd_delay #(.N(WFILT)) uovl_w (.a(ovl_raw), .z(ovl_d));
    LUT2 #(.INIT(4'h8)) uovl_a  (.I0(ovl_raw), .I1(ovl_d), .O(ovl_flt));

    integer errors = 0;
    task fail(input [511:0] why);
    begin
        errors = errors + 1;
        $display("  FAIL %0s at %0t", why, $time);
    end
    endtask

    // -- observation ---------------------------------------------------------
    reg watching = 1'b0;

    integer n_A1 = 0, n_A2 = 0;
    integer n_viol = 0, n_serv = 0, n_ovl_raw = 0, n_ovl_flt = 0;
    integer n_r1 = 0, n_r2 = 0;

    always @(posedge A1) if (watching) n_A1 = n_A1 + 1;
    always @(posedge A2) if (watching) n_A2 = n_A2 + 1;
    always @(posedge r1) if (watching) n_r1 = n_r1 + 1;
    always @(posedge r2) if (watching) n_r2 = n_r2 + 1;

    always @* if (watching && viol_raw === 1'b1) n_viol    = n_viol + 1;
    always @* if (watching && serv_raw === 1'b1) n_serv    = n_serv + 1;
    always @* if (watching && ovl_raw  === 1'b1) n_ovl_raw = n_ovl_raw + 1;
    always @* if (watching && ovl_flt  === 1'b1) n_ovl_flt = n_ovl_flt + 1;

    initial begin
        $display("tb_arb_prot  (BD_ROUTE_PS=%0d)", `BD_ROUTE_PS);

        #(200 * H);
        if (uarb.q !== 1'b1) fail("arbiter state node did not reset to 1");
        rst = 1'b0;

        #(400 * H);
        watching = 1'b1;
        #(40000 * H);
        watching = 1'b0;

        $display("  requests issued : r1 %0d, r2 %0d", n_r1, n_r2);
        $display("  acknowledges    : A1 %0d, A2 %0d", n_A1, n_A2);
        $display("  serv instants   : %0d", n_serv);
        $display("  viol instants   : %0d", n_viol);
        $display("  grant overlap   : raw %0d, width-filtered %0d",
                 n_ovl_raw, n_ovl_flt);

        // 1. the loops free-run
        if (n_r1 == 0) fail("client 1 never issued a request -- loop is dead");
        if (n_r2 == 0) fail("client 2 never issued a request -- loop is dead");

        // 2. both clients are actually served, so contention is real
        if (n_A1 < 10) fail("client 1 was starved");
        if (n_A2 < 10) fail("client 2 was starved");

        // 3. the detector that must fire, fires.  Without this the two zeros
        //    below are indistinguishable from a rig that never ran, which is
        //    the entire reason this bit exists in the design.
        if (n_serv == 0)
            fail("serv detector never fired -- the rig cannot self-report");

        // 4. and the two that must not, do not
        if (n_viol != 0)
            fail("both clients acknowledged at once -- the held node did not hold");
        if (n_ovl_flt != 0)
            fail("grant overlap survived the width filter");

        if (errors == 0) $display("tb_arb_prot PASS");
        else begin
            $display("tb_arb_prot FAIL (%0d errors)", errors);
            $fatal;
        end
        $finish;
    end
endmodule
