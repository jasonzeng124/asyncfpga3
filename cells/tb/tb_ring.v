// tb_ring.v -- when does a CLOSED ring of pipeline stages circulate a token,
// and when does it just sit there?
//
// Every cycle in a dataflow graph becomes one of these rings, so the answer is
// the correctness precondition the compiler's slack pass has to enforce.  The
// weak form of that precondition -- "a cycle needs at least one storage stage"
// -- only rules out the pure combinational loop.  It is not sufficient, and
// this bench is what says so, in two independent ways.
//
// The ring is the simple Muller controller closed on itself:
//
//     c_i = C(c_i-1, ~c_i+1)          exactly what bd_link builds
//
// LENGTH.  N <= 2 is dead, and dead by construction rather than by luck.  Wrap
// two stages and each controller's two inputs become x and ~x -- permanently
// disagreeing, so a C-element holds, forever, from any state.  Three is the
// floor.  Said the other way: occupancy is half a token per stage, so one
// token already fills two stages and needs a third to move into.
//
// OCCUPANCY.  Strictly between 0 and N stages may come up holding.  Both ends
// are STABLE states, which is what makes them deadlock rather than a glitch:
// an empty closed ring has nothing to start it, and a full one has nowhere to
// move.  A ring is not free to "probably come up empty" -- see the reset
// section of docs/LIBRARY.md, which is the same fact from the reset side.
//
// Liveness is judged by counting transitions on c[0] over a fixed window,
// which is the whole measurement: a live ring circulates and toggles, a dead
// one is frozen and never does.

`timescale 1ps / 1ps

// A closed ring of N controllers, the first K of which come up holding.
module ring #(parameter integer N = 3, parameter integer K = 1)
    (input wire rst, output wire [N-1:0] c);
    genvar i;
    generate
        for (i = 0; i < N; i = i + 1) begin : st
            wire prev = c[(i + N - 1) % N];
            wire next = c[(i + 1) % N];
            if (i < K) bd_c2n_set u (.a(prev), .b(next), .rst(rst), .q(c[i]));
            else       bd_c2n     u (.a(prev), .b(next), .rst(rst), .q(c[i]));
        end
    endgenerate
endmodule

module tb_ring;

    // Both of these scale with the hop, because everything here does.  The
    // reset hold especially: release it while the power-up X is still draining
    // and a C-element latches C(x, .) = x into its own feedback loop, which
    // never clears -- the ring then reads as DEAD for a reason that has
    // nothing to do with its length.  At BD_ROUTE_PS=354 a fixed 200 ps hold
    // is far too short, and this bench found that out the hard way.
    localparam integer HOLD   = 40 * `BD_HOP_PS;   // reset asserted
    localparam integer WINDOW = 200 * `BD_HOP_PS;  // free running after reset
    localparam integer LIVE   = 2;       // more edges than this = circulating

    integer errors = 0;
    reg rst = 1'b1;

    // One instance per (N, K) case, each with its own edge counter on c[0].
    `define CASE(NN, KK) \
        wire [NN-1:0] c``NN``_``KK; \
        ring #(.N(NN), .K(KK)) r``NN``_``KK (.rst(rst), .c(c``NN``_``KK)); \
        integer e``NN``_``KK = 0; \
        always @(c``NN``_``KK[0]) if (!rst) e``NN``_``KK = e``NN``_``KK + 1;

    // length sweep, one stage holding
    `CASE(1,1) `CASE(2,1) `CASE(3,1) `CASE(4,1) `CASE(5,1) `CASE(6,1)
    // occupancy sweep at two lengths, including both degenerate ends
    `CASE(4,0) `CASE(4,2) `CASE(4,3) `CASE(4,4)
    `CASE(6,0) `CASE(6,3) `CASE(6,5) `CASE(6,6)

    // A case is judged against what the invariant PREDICTS, so this bench
    // fails if the library ever stops behaving the way the compiler assumes.
    task judge(input integer nn, input integer kk, input integer edges,
                input want_live);
    begin : b
        reg got_live;
        got_live = (edges > LIVE);
        $display("  N=%0d K=%0d  edges=%0d  %s", nn, kk, edges,
                 got_live ? "LIVE" : "DEAD");
        if (got_live !== want_live) begin
            errors = errors + 1;
            $display("  FAIL N=%0d K=%0d: expected %s", nn, kk,
                     want_live ? "LIVE" : "DEAD");
        end
    end
    endtask

    initial begin
        #HOLD rst = 1'b0;
        #WINDOW;

        $display("length sweep (one stage up holding) -- three is the floor:");
        judge(1, 1, e1_1, 1'b0);
        judge(2, 1, e2_1, 1'b0);
        judge(3, 1, e3_1, 1'b1);
        judge(4, 1, e4_1, 1'b1);
        judge(5, 1, e5_1, 1'b1);
        judge(6, 1, e6_1, 1'b1);

        $display("occupancy sweep -- neither empty nor full may circulate:");
        judge(4, 0, e4_0, 1'b0);
        judge(4, 2, e4_2, 1'b1);
        judge(4, 3, e4_3, 1'b1);
        judge(4, 4, e4_4, 1'b0);
        judge(6, 0, e6_0, 1'b0);
        judge(6, 3, e6_3, 1'b1);
        judge(6, 5, e6_5, 1'b1);
        judge(6, 6, e6_6, 1'b0);

        if (errors == 0) $display("tb_ring PASS");
        else             $display("tb_ring FAIL (%0d)", errors);
        $finish;
    end

    initial begin
        #50_000_000;
        $display("tb_ring FAIL (timeout)");
        $finish;
    end
endmodule
