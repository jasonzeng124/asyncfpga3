// tb_arb.v -- the arbitration cell and the arbiter.
//
// WHAT THIS BENCH CANNOT DO.  It cannot test the property the cell is risky
// for.  Metastability is an analog phenomenon; a Verilog LUT model resolves
// every input to 0 or 1 in zero time and will never produce the intermediate
// level the cell's risk note is about.  A passing run here says the DIGITAL
// behaviour is right -- exclusion, handover, no manufactured acknowledges,
// defined reset -- and says nothing whatsoever about the failure rate.  That
// number has to be measured on hardware, and nothing in simulation discharges
// the obligation.
//
// What is testable, and is tested:
//
//   exclusion, continuously: g1 and g2 are never both high at any instant;
//
//   a lone request is granted, and a tie from idle goes to whichever side
//   holds the state node -- deterministically, because on a tie both the set
//   and the reset condition are false and q simply does not move;
//
//   under sustained contention, no manufactured acknowledges: the number of
//   transactions the shared server actually performed must equal the number
//   of clients that were acknowledged.  This is the check the arbiter as
//   specified fails, and the bench runs BOTH variants side by side so the
//   finding is a measured number rather than a claim.

`timescale 1ps / 1ps

// ---------------------------------------------------------------------------
// One arbiter, one shared server, two clients that always want it back.
// ---------------------------------------------------------------------------
module arb_harness #(parameter HOLD_ON_ACK = 0, parameter integer ROUNDS = 40)
    (input wire rst, input wire go);

    localparam integer H = `BD_HOP_PS;
    localparam integer T = 12 * H;

    reg  r1 = 1'b0, r2 = 1'b0;
    wire A1, A2, R0, g1, g2;
    reg  A0 = 1'b0;

    bd_arbiter #(.HOLD_ON_ACK(HOLD_ON_ACK)) dut (
        .rst(rst), .r1(r1), .A1(A1), .r2(r2), .A2(A2),
        .R0(R0), .A0(A0), .g1(g1), .g2(g2));

    integer both_seen = 0;
    reg     watching  = 1'b0;
    always @* if (watching && g1 === 1'b1 && g2 === 1'b1)
        both_seen = both_seen + 1;

    // The shared server.  A real four-phase consumer: it will not start a new
    // transaction until its own request has been low for a settled interval,
    // so a runt on R0 is not mistaken for a return to zero.
    integer served = 0;
    initial begin
        forever begin
            wait (R0 === 1'b1);
            #(2 * T);
            if (R0 === 1'b1) begin
                served = served + 1;
                A0 = 1'b1;
                wait (R0 === 1'b0);
                #(2 * T);
                A0 = 1'b0;
                #(2 * T);
            end
        end
    end

    integer done1 = 0, done2 = 0;
    integer k1, k2;

    initial begin
        wait (go);
        for (k1 = 0; k1 < ROUNDS; k1 = k1 + 1) begin
            r1 = 1'b1;
            wait (A1 === 1'b1);
            r1 = 1'b0;
            wait (A1 === 1'b0);
            done1 = done1 + 1;
            #(((k1 * 7) % 5) * H);      // uneven arrival, deliberately
        end
    end

    initial begin
        wait (go);
        for (k2 = 0; k2 < ROUNDS; k2 = k2 + 1) begin
            r2 = 1'b1;
            wait (A2 === 1'b1);
            r2 = 1'b0;
            wait (A2 === 1'b0);
            done2 = done2 + 1;
            #(((k2 * 3) % 5) * H);
        end
    end
endmodule

// ---------------------------------------------------------------------------
module tb_arb;

    localparam integer H = `BD_HOP_PS;
    localparam integer T = 12 * H;
    localparam integer ROUNDS = 40;

    integer errors = 0;

    task fail(input [511:0] why);
    begin
        errors = errors + 1;
        $display("  FAIL %0s at %0t", why, $time);
    end
    endtask

    reg rst = 1'b1;
    reg go  = 1'b0;

    arb_harness #(.HOLD_ON_ACK(0), .ROUNDS(ROUNDS)) spec (.rst(rst), .go(go));
    arb_harness #(.HOLD_ON_ACK(1), .ROUNDS(ROUNDS)) held (.rst(rst), .go(go));

    // -- the decision element on its own -------------------------------------
    reg  cr1 = 1'b0, cr2 = 1'b0;
    wire cg1, cg2;
    bd_arbcell ucell (.r1(cr1), .r2(cr2), .rst(rst), .g1(cg1), .g2(cg2));
    reg watching = 1'b0;
    // Counted, not failed on the spot.  Handover exclusion in the bare cell is
    // an ARC ORDERING, not a structural property: on the r2-to-r1 direction the
    // falling grant travels one fall arc (O6, 124 ps) and the rising grant
    // travels two rise arcs (q at 56 then O5 at 52), so with zero routing the
    // rise wins by 16 ps.  Routing puts a full hop in the q feedback and
    // restores the order with roughly twenty times the margin, which is why
    // this is asserted only in the routed regime.
    integer cell_overlap = 0;
    always @* if (watching && cg1 === 1'b1 && cg2 === 1'b1)
        cell_overlap = cell_overlap + 1;

    integer w;
    reg holder;

    initial begin
        $display("tb_arb");

        // Reset must leave the state node DEFINED -- an intermediate q is the
        // exact failure the risk note is about, so an x here is a real fault.
        #(4 * T);
        if (ucell.q !== 1'b1) fail("arbcell state node did not reset to 1");
        if (spec.dut.q !== 1'b1) fail("arbiter state node did not reset to 1");
        if (held.dut.q !== 1'b1) fail("held arbiter state node did not reset to 1");
        rst = 1'b0;
        #(4 * T);
        watching = 1'b1; spec.watching = 1'b1; held.watching = 1'b1;

        // -- uncontended: one client alone is granted ------------------------
        cr1 = 1'b1; #(4 * T);
        if (cg1 !== 1'b1 || cg2 !== 1'b0) fail("lone r1 was not granted");
        cr1 = 1'b0; #(4 * T);
        cr2 = 1'b1; #(4 * T);
        if (cg2 !== 1'b1 || cg1 !== 1'b0) fail("lone r2 was not granted");
        cr2 = 1'b0; #(4 * T);

        // -- a tie from idle goes to whoever holds q -------------------------
        // Both requests rising together makes set and reset both false, so q
        // does not move.  Which side that favours depends on who ran last --
        // r2 did, just above -- so the bench reads q rather than assuming it.
        holder = ucell.q;
        cr1 = 1'b1; cr2 = 1'b1;
        #(4 * T);
        if (ucell.q !== holder) fail("a tie moved the state node");
        if (holder === 1'b1) begin
            if (cg1 !== 1'b1 || cg2 !== 1'b0) fail("tie did not go to r1");
        end else begin
            if (cg2 !== 1'b1 || cg1 !== 1'b0) fail("tie did not go to r2");
        end
        // The holder standing down hands over, and only then.
        if (holder === 1'b1) begin
            cr1 = 1'b0; #(4 * T);
            if (cg2 !== 1'b1) fail("handover did not follow the winner standing down");
        end else begin
            cr2 = 1'b0; #(4 * T);
            if (cg1 !== 1'b1) fail("handover did not follow the winner standing down");
        end
        cr1 = 1'b0; cr2 = 1'b0; #(4 * T);

        // -- sustained contention, both variants -----------------------------
        go = 1'b1;
        for (w = 0; w < 60000 &&
                    (held.done1 < ROUNDS || held.done2 < ROUNDS ||
                     spec.done1 < ROUNDS || spec.done2 < ROUNDS); w = w + 1)
            #H;

        $display("  as specified (HOLD_ON_ACK=0): clients %0d+%0d acknowledged, server performed %0d",
                 spec.done1, spec.done2, spec.served);
        $display("  with the fix (HOLD_ON_ACK=1): clients %0d+%0d acknowledged, server performed %0d",
                 held.done1, held.done2, held.served);

        // The fixed variant is what must be correct.
        if (held.done1 != ROUNDS) fail("held: client 1 was starved");
        if (held.done2 != ROUNDS) fail("held: client 2 was starved");
        if (held.served != held.done1 + held.done2)
            fail("held: server transactions do not match client acknowledges");
        if (held.both_seen != 0) fail("held: exclusion was broken");

        // The specified variant is the finding.  If it ever stops failing,
        // either the model or the reasoning is wrong and the write-up in
        // rtl/bd_arb.v should stop being trusted.
        if (spec.served >= spec.done1 + spec.done2)
            fail("the reported arbiter defect did not reproduce");
        else
            $display("  finding reproduces: %0d acknowledges were manufactured",
                     spec.done1 + spec.done2 - spec.served);

        $display("  arbcell handover overlap at BD_ROUTE_PS=%0d: %0d instant(s)",
                 `BD_ROUTE_PS, cell_overlap);
        if (`BD_ROUTE_PS >= 56 && cell_overlap != 0)
            fail("grants overlapped during handover with routing included");
        if (`BD_ROUTE_PS == 0 && cell_overlap == 0)
            $display("  (no overlap even arc-only: safer than rtl/bd_arb.v claims, recheck it)");

        if (errors == 0) $display("tb_arb PASS");
        else             $display("tb_arb FAIL (%0d)", errors);
        $finish;
    end

    initial begin
        #200_000_000;
        $display("tb_arb FAIL (timeout)");
        $finish;
    end
endmodule
