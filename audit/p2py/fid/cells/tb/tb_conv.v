// tb_conv.v -- the two protocol converters, back to back.
//
//     bundled --> bd_bd2dr --> {t,f} --> bd_dr2bd --> bundled
//
// The round trip is the test: a bit that survives it survives both encodings.
// Three things are checked that a value comparison alone would not catch.
//
//   Dual-rail validity.  t and f may never be high together, and every
//   transaction must return both rails to zero before the next.
//
//   The decode direction costs a delay.  d and req come off the same two
//   wires, so without the delay the only thing separating them is one OR arc
//   -- routing luck, not a designed guardband.  A DELAY(0) instance is built
//   alongside the real one and both margins are measured, so what the delay
//   line actually buys is a number in the log rather than an assertion.
//
//   The spacer eats the data.  A bare d = t decode releases its payload one
//   whole phase before the bundled hold window closes; see the finding
//   written up in the header of rtl/bd_ctl.v.  Both the bare cell and the
//   held cell are instantiated on the same rails and monitored separately.
//   The bare one is EXPECTED to fail P2, and the bench asserts that it does
//   -- if it ever stops failing, either the model or the reasoning is wrong
//   and this bench should stop being trusted.

`timescale 1ps / 1ps

module tb_conv;

    localparam integer H = `BD_HOP_PS;
    localparam integer T = 12 * H;
    localparam integer NBIT = 24;

    integer errors = 0;
    integer i;

    task fail(input [511:0] why);
    begin
        errors = errors + 1;
        $display("  FAIL %0s at %0t", why, $time);
    end
    endtask

    function bit_of(input integer k);
        bit_of = k[0] ^ (k[1] & k[2]);
    endfunction

    // -- encoder, driven by a bundled source --------------------------------
    wire       req, ack;   wire [0:0] sdata;
    wire       t, f, ack_dr;

    bd_source #(.W(1)) src (.req(req), .ack(ack), .data(sdata));
    bd_bd2dr uenc (.req(req), .d(sdata[0]), .ack(ack),
                   .t(t), .f(f), .ack_dr(ack_dr));

    // -- the decode that is used: delayed request, held payload -------------
    wire dreq, dack, dd;
    bd_dr2bd #(.DELAY(4), .HOLD(1)) udec (.t(t), .f(f), .ack_dr(ack_dr),
                                          .req(dreq), .d(dd), .ack(dack));
    wire [0:0] dbus = dd;
    bd_sink #(.W(1)) snk (.req(dreq), .ack(dack), .data(dbus));

    bd_monitor #(.W(1), .CHAN("conv-in"))   mi (.req(req),  .ack(ack),  .data(sdata));
    bd_monitor #(.W(1), .CHAN("conv-held")) mh (.req(dreq), .ack(dack), .data(dbus));

    // -- the decode as specified: bare d = t --------------------------------
    // Same rails, same acknowledge, nothing driven from it.  Its monitor
    // records the finding.
    wire breq, bd;
    bd_dr2bd #(.DELAY(4), .HOLD(0)) ubare (.t(t), .f(f), .ack_dr(),
                                           .req(breq), .d(bd), .ack(dack));
    wire [0:0] bbus = bd;
    bd_monitor #(.W(1), .CHAN("conv-bare")) mb (.req(breq), .ack(dack), .data(bbus));

    // -- the same decode with no matched delay, for the margin comparison ---
    wire nreq, nd;
    bd_dr2bd #(.DELAY(0), .HOLD(1)) unod (.t(t), .f(f), .ack_dr(),
                                          .req(nreq), .d(nd), .ack(dack));

    reg watching = 1'b0;

    // No reset anywhere in this bench.  The held decode is a C-element, so it
    // is the only state here, and it powers up unknown ON PURPOSE: the first
    // valid code resolves it, and nothing reads d before then.  If that were
    // wrong the X would reach the monitor and this bench would say so.

    // -- dual-rail validity --------------------------------------------------
    always @* if (watching && t === 1'b1 && f === 1'b1)
        fail("both rails high at once");

    // Checked a few arcs after req-fall, not a few cycles: the encoder is one
    // LUT, and waiting longer only risks sampling the next transaction.
    always @(negedge req) if (watching) begin
        #(4 * `BD_T_FALL);
        if (t !== 1'b0 || f !== 1'b0) fail("rails did not return to zero");
    end

    // -- request-follows-data margin ----------------------------------------
    // Measured against the rails, not against d: d is a rename of t, so "when
    // did the payload become valid" is "when did a rail move".
    time t_rail = 0;
    integer lead_min = 1000000, nlead_min = 1000000;
    always @(t or f) if (watching) t_rail = $time;
    always @(posedge dreq) if (watching && t_rail != 0)
        if (($time - t_rail) < lead_min) lead_min = $time - t_rail;
    always @(posedge nreq) if (watching && t_rail != 0)
        if (($time - t_rail) < nlead_min) nlead_min = $time - t_rail;

    initial begin
        $display("tb_conv");
        #(4 * T);
        mi.arm; mh.arm; mb.arm; watching = 1'b1;

        for (i = 0; i < NBIT; i = i + 1) begin
            src.send(bit_of(i));
            #(2 * T);
        end

        if (snk.n != NBIT) begin
            errors = errors + 1;
            $display("  FAIL round trip delivered %0d of %0d bits", snk.n, NBIT);
        end
        for (i = 0; i < snk.n && i < NBIT; i = i + 1)
            if (snk.seen[i] !== bit_of(i)) begin
                errors = errors + 1;
                $display("  FAIL bit %0d: got %b expected %b",
                         i, snk.seen[i], bit_of(i));
            end

        $display("  decode margin: DELAY(4) %0d ps, DELAY(0) %0d ps -- the line buys %0d ps",
                 lead_min, nlead_min, lead_min - nlead_min);
        if (lead_min <= 0)  fail("decoded request did not follow its data");
        if (nlead_min <= 0) fail("undelayed decode did not follow its data either");
        if ((lead_min - nlead_min) < 3 * `BD_T_RISE)
            fail("the matched delay bought less margin than its own depth");

        // The finding, quantified.  Every transaction carrying a one has its
        // payload withdrawn by the spacer before the window closes; a zero has
        // nothing to withdraw, so half the transactions show it.
        $display("  bare decode (d = t, as specified): %0d hold-window violations in %0d transactions",
                 mb.errors, NBIT);
        if (mb.errors == 0)
            fail("bare decode showed no violation -- the finding does not reproduce");
        $display("  held decode (HOLD=1, same 1 LUT): %0d", mh.errors);

        errors = errors + mi.errors + mh.errors;
        if (errors == 0) $display("tb_conv PASS");
        else             $display("tb_conv FAIL (%0d)", errors);
        $finish;
    end

    initial begin
        #40_000_000;
        $display("tb_conv FAIL (timeout)");
        $finish;
    end
endmodule
