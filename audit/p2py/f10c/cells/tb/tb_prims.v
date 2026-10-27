// tb_prims.v -- C-elements, latches, delay line, data mux.
//
// The INIT constants are proved exhaustively in verify/inits.py.  What this
// bench checks is the thing that proof cannot see: that each instantiation
// wires the right net to the right pin, that the feedback closes, and that
// reset drives each cell to the polarity its cell comment claims.

`timescale 1ps / 1ps

module tb_prims;

    localparam integer T = 12 * `BD_HOP_PS;   // settle time, generous

    integer errors = 0;
    integer i;

    task chk(input [255:0] what, input got, input exp);
    begin
        if (got !== exp) begin
            errors = errors + 1;
            $display("  FAIL %0s: got %b expected %b at %0t", what, got, exp, $time);
        end
    end
    endtask

    task chkv(input [255:0] what, input [31:0] got, input [31:0] exp);
    begin
        if (got !== exp) begin
            errors = errors + 1;
            $display("  FAIL %0s: got %h expected %h at %0t", what, got, exp, $time);
        end
    end
    endtask

    reg rst = 1'b1;
    reg a = 1'b0, b = 1'b0, c = 1'b0, d = 1'b0;

    // ------------------------------------------------------------ C-elements
    wire q2, q2s, q2n, q2ns, q3, q4;
    bd_c2      u_c2   (.a(a), .b(b), .rst(rst), .q(q2));
    bd_c2_set  u_c2s  (.a(a), .b(b), .rst(rst), .q(q2s));
    bd_c2n     u_c2n  (.a(a), .b(b), .rst(rst), .q(q2n));
    bd_c2n_set u_c2ns (.a(a), .b(b), .rst(rst), .q(q2ns));
    bd_c3      u_c3   (.a(a), .b(b), .c(c), .rst(rst), .q(q3));
    bd_c4      u_c4   (.a(a), .b(b), .c(c), .d(d), .rst(rst), .q(q4));

    reg [4:0] tin = 5'b0;
    wire qt;
    bd_ctree #(.N(5)) u_ct (.a(tin), .rst(rst), .q(qt));

    // ---------------------------------------------------------------- latches
    reg  [3:0] ld = 4'h0;
    reg        len = 1'b0;
    wire [3:0] lq;
    bd_latch #(.W(4)) u_lat (.d(ld), .en(len), .q(lq));

    reg        rd = 1'b0, ren = 1'b0;
    wire       rq;
    bd_latch_rst #(.W(1), .RESET_VALUE(64'd0)) u_lr (
        .d(rd), .en(ren), .rst(rst), .q(rq));

    // ------------------------------------------------------------ delay line
    reg  dly_in = 1'b0;
    wire dly_out;
    bd_delay #(.N(4)) u_dly (.a(dly_in), .z(dly_out));

    // -------------------------------------------------------------- data mux
    reg  [3:0] ma = 4'h0, mb = 4'h0;
    reg        ms = 1'b0;
    wire [3:0] mz;
    bd_datamux #(.W(4)) u_dm (.a(ma), .b(mb), .s(ms), .z(mz));

    // reference C-element state
    reg e2, e2s, e2n, e2ns, e3, e4;

    // One four-phase cycle on the five join inputs, raised in a random order
    // and then lowered in another.  The rendezvous must not fire until the
    // last input is up, and must not release until the first goes down.
    integer j, k, pick;
    reg [4:0] pending;
    task ctree_cycle;
    begin
        pending = 5'b11111;
        for (j = 0; j < 5; j = j + 1) begin
            pick = $random % 5; if (pick < 0) pick = -pick;
            while (pending[pick] === 1'b0) pick = (pick + 1) % 5;
            pending[pick] = 1'b0;
            tin[pick] = 1'b1;
            #T;
            chk("ctree fired early", qt, (j == 4) ? 1'b1 : 1'b0);
        end
        pending = 5'b11111;
        for (j = 0; j < 5; j = j + 1) begin
            pick = $random % 5; if (pick < 0) pick = -pick;
            while (pending[pick] === 1'b0) pick = (pick + 1) % 5;
            pending[pick] = 1'b0;
            tin[pick] = 1'b0;
            #T;
            chk("ctree released early", qt, (j == 4) ? 1'b0 : 1'b1);
        end
    end
    endtask

    initial begin
        $display("tb_prims");

        // ---- reset drives every stateful cell to a defined value ----------
        #T;
        chk("c2 reset",       q2,   1'b0);
        chk("c2_set reset",   q2s,  1'b1);
        chk("c2n reset",      q2n,  1'b0);
        chk("c2n_set reset",  q2ns, 1'b1);
        chk("c3 reset",       q3,   1'b0);
        chk("c4 reset",       q4,   1'b0);
        chk("ctree reset",    qt,   1'b0);
        chk("latch_rst reset", rq,  1'b0);

        // reset must dominate the inputs, not merely win a race with them
        a = 1; b = 1; c = 1; d = 1; tin = 5'b11111; #T;
        chk("c2 reset dominates",  q2, 1'b0);
        chk("c4 reset dominates",  q4, 1'b0);
        chk("ctree reset dominates", qt, 1'b0);
        a = 0; b = 0; c = 0; d = 0; tin = 5'b0; #T;
        chk("c2_set reset dominates", q2s, 1'b1);

        rst = 0; #T;
        e2 = 0; e2s = 0; e2n = 0; e2ns = 1; e3 = 0; e4 = 0;
        // c2_set released with a=b=0 falls; c2n_set with a=0,b=0 holds at 1
        chk("c2_set falls after release", q2s, 1'b0); e2s = 0;
        chk("c2n_set holds after release", q2ns, 1'b1);

        // ---- rendezvous behaviour, randomised against a reference ---------
        for (i = 0; i < 64; i = i + 1) begin
            {d, c, b, a} = $random;
            #T;
            if ( a &&  b) e2 = 1; else if (!a && !b) e2 = 0;
            if ( a &&  b) e2s = 1; else if (!a && !b) e2s = 0;
            if ( a && !b) e2n = 1; else if (!a &&  b) e2n = 0;   // C(a,~b)
            if ( a && !b) e2ns = 1; else if (!a &&  b) e2ns = 0;
            if ( a &&  b &&  c) e3 = 1; else if (!a && !b && !c) e3 = 0;
            if ( a && b && c && d) e4 = 1;
            else if (!a && !b && !c && !d) e4 = 0;

            chk("c2",      q2,   e2);
            chk("c2_set",  q2s,  e2s);
            chk("c2n",     q2n,  e2n);
            chk("c2n_set", q2ns, e2ns);
            chk("c3",      q3,   e3);
            chk("c4",      q4,   e4);
        end

        // ---- the wide join, under the discipline it is specified for ------
        // bd_ctree is a tree, and a tree of C-elements is only equal to a flat
        // N-input C-element when every input rises before any falls.  Drive it
        // that way, in randomised orders, and check the output transitions
        // exactly on the last rise and the first fall.
        tin = 5'b0; #T;
        for (i = 0; i < 40; i = i + 1) begin
            ctree_cycle;
        end

        // ---- transparent-high latch ---------------------------------------
        ld = 4'hA; len = 1; #T; chkv("latch transparent", lq, 4'hA);
        ld = 4'h5;           #T; chkv("latch follows",    lq, 4'h5);
        len = 0;             #T; chkv("latch closed",     lq, 4'h5);
        ld = 4'hC;           #T; chkv("latch holds",      lq, 4'h5);
        len = 1;             #T; chkv("latch reopens",    lq, 4'hC);
        len = 0;             #T;

        // ---- resettable latch ---------------------------------------------
        rd = 1; ren = 1; #T; chk("latch_rst transparent", rq, 1'b1);
        ren = 0;         #T; chk("latch_rst holds",       rq, 1'b1);
        rst = 1;         #T; chk("latch_rst clears",      rq, 1'b0);
        rst = 0;         #T; chk("latch_rst stays clear", rq, 1'b0);

        // ---- delay line: four hops, no more and no less --------------------
        // Rise and fall are different arcs on this fabric (56 vs 124 ps), so
        // the chain is asymmetric and both directions are checked.  These are
        // CELL arcs only: on silicon each hop also carries ~354 ps of routing,
        // which is why no matched delay may ever be sized from this number.
        dly_in = 1;
        #(4 * `BD_T_RISE - 30);
        chk("delay rise not yet arrived", dly_out, 1'b0);
        #60;
        chk("delay rise arrived",         dly_out, 1'b1);
        dly_in = 0;
        #(4 * `BD_T_FALL - 30);
        chk("delay fall not yet arrived", dly_out, 1'b1);
        #60;
        chk("delay fall arrived",         dly_out, 1'b0);
        #T;

        // ---- data mux ------------------------------------------------------
        ma = 4'h3; mb = 4'hC;
        ms = 0; #T; chkv("datamux s=0 -> a", mz, 4'h3);
        ms = 1; #T; chkv("datamux s=1 -> b", mz, 4'hC);
        ma = 4'h9; #T; chkv("datamux ignores a when s=1", mz, 4'hC);
        ms = 0; #T; chkv("datamux back to a", mz, 4'h9);

        if (errors == 0) $display("tb_prims PASS");
        else             $display("tb_prims FAIL (%0d)", errors);
        $finish;
    end

    initial begin
        #10_000_000;
        $display("tb_prims FAIL (timeout)");
        $finish;
    end
endmodule
