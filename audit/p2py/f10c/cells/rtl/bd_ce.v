// ---------------------------------------------------------------------------
// bd_ce.v -- Muller C-elements.
//
// The rendezvous primitive: follow when the inputs agree, hold when they
// differ.  Symmetric C(a,b) is exactly majority(a, b, q), so one LUT6 holds
// the cell and its own feedback.
//
// Reset is not optional.  A LUT feedback loop has no defined power-up value
// and configuration does not clear it, so every C-element that holds control
// state carries rst on a real pin.  Polarity is per-cell:
//
//     bd_c2*      q = ~rst . C(...)   -- comes up empty   (link, fork, join,
//                                        merge acks, mux joins)
//     bd_c2_set   q =  rst + C(...)   -- comes up holding (the loop's select
//                                        token)
//
// An inverted input is a bubble on the pin that reads it, never a cell:
// bd_c2n is C(a, ~b) at exactly the same cost.
//
// Fan-in of four is the ceiling -- feedback and rst take two of the six
// inputs.  Beyond that use bd_ctree, and the tree depth becomes a term in the
// delay model.
//
// Every cell here contains a deliberate combinational loop.  It must stay a
// (* keep *) instance or synthesis dissolves it, and nextpnr needs
// --ignore-loops to accept the resulting SCC.  Feedback must remain an
// internal wire: promoting it to a module port costs 2 LUTs instead of 1.
// ---------------------------------------------------------------------------

`default_nettype none

// -- C(a,b), comes up at 0 --------------------------------------- 1 LUT6 ---
module bd_c2 (input wire a, input wire b, input wire rst, output wire q);
    (* keep *) LUT6 #(.INIT(64'h00E8_00E8_00E8_00E8)) u (
        .I0(a), .I1(b), .I2(q), .I3(rst), .I4(1'b0), .I5(1'b0), .O(q));
endmodule

// -- C(a,b), comes up at 1 --------------------------------------- 1 LUT6 ---
module bd_c2_set (input wire a, input wire b, input wire rst, output wire q);
    (* keep *) LUT6 #(.INIT(64'hFFE8_FFE8_FFE8_FFE8)) u (
        .I0(a), .I1(b), .I2(q), .I3(rst), .I4(1'b0), .I5(1'b0), .O(q));
endmodule

// -- C(a,~b), comes up at 0 -------------------------------------- 1 LUT6 ---
// This is the pipeline link's controller and, set-reset swapped, the
// arbitration cell's state node.  As an SR latch: set = a.~b, reset = ~a.b,
// hold on a tie.
module bd_c2n (input wire a, input wire b, input wire rst, output wire q);
    (* keep *) LUT6 #(.INIT(64'h00B2_00B2_00B2_00B2)) u (
        .I0(a), .I1(b), .I2(q), .I3(rst), .I4(1'b0), .I5(1'b0), .O(q));
endmodule

// -- C(a,~b), comes up at 1 -------------------------------------- 1 LUT6 ---
module bd_c2n_set (input wire a, input wire b, input wire rst, output wire q);
    (* keep *) LUT6 #(.INIT(64'hFFB2_FFB2_FFB2_FFB2)) u (
        .I0(a), .I1(b), .I2(q), .I3(rst), .I4(1'b0), .I5(1'b0), .O(q));
endmodule

// -- C(a,b,c), comes up at 0 ------------------------------------- 1 LUT6 ---
module bd_c3 (input wire a, input wire b, input wire c,
              input wire rst, output wire q);
    (* keep *) LUT6 #(.INIT(64'h0000_FE80_0000_FE80)) u (
        .I0(a), .I1(b), .I2(c), .I3(q), .I4(rst), .I5(1'b0), .O(q));
endmodule

// -- C(a,b,c,d), comes up at 0 ----------------------------------- 1 LUT6 ---
// Exactly six pins.  This is the widest C-element the fabric holds.
module bd_c4 (input wire a, input wire b, input wire c, input wire d,
              input wire rst, output wire q);
    (* keep *) LUT6 #(.INIT(64'h0000_0000_FFFE_8000)) u (
        .I0(a), .I1(b), .I2(c), .I3(d), .I4(q), .I5(rst), .O(q));
endmodule

// ---------------------------------------------------------------------------
// The two rows of the design review's mapping table that carry no reset pin.
// Legal only inside a cell that defines the node some other way; never in a
// control network, where "it will probably come up empty" is not an
// assumption available.
// ---------------------------------------------------------------------------
module bd_c2_norst (input wire a, input wire b, output wire q);
    (* keep *) LUT6 #(.INIT(64'hE8E8_E8E8_E8E8_E8E8)) u (
        .I0(a), .I1(b), .I2(q), .I3(1'b0), .I4(1'b0), .I5(1'b0), .O(q));
endmodule

module bd_c3_norst (input wire a, input wire b, input wire c, output wire q);
    (* keep *) LUT6 #(.INIT(64'hFE80_FE80_FE80_FE80)) u (
        .I0(a), .I1(b), .I2(c), .I3(q), .I4(1'b0), .I5(1'b0), .O(q));
endmodule

// ---------------------------------------------------------------------------
// bd_ctree -- rendezvous over N inputs.
//
// Up to four inputs this is one LUT.  Wider is a balanced tree, and its depth
// is a real term in the bundling budget.
//
// -- the tree is NOT a flat N-input C-element ------------------------------
//
// It is equal to one only under the four-phase discipline, and the difference
// is not academic.  Each sub-tree carries its own memory, so two sub-trees can
// hold stale ones taken from different moments.  With N = 5 split as
// C(C(a0,a1), C(a2,a3,a4)), the input vector 0 1 1 1 1 drives the tree to 1
// while a flat five-input C-element holds at 0 -- the left sub-tree tracks a0
// and a1, the right one is still holding a one from an earlier all-high
// moment, and the top sees two ones.
//
// Under the discipline this cell is actually used with, that state is
// unreachable: every input is a request that rises once and falls once per
// transaction, all of them rise before any falls, and nothing moves again
// until the acknowledge has completed the cycle.  Every sub-tree therefore
// returns to zero every cycle and can never be stale.  Verified by exhaustive
// search over interleavings in tb_prims.
//
// So: fine for a join or a fork, wrong for anything that samples N unrelated
// levels.
//
// Cost: ceil((N-1)/3) LUT6 for N > 1, rounded up by the tree's shape.
// ---------------------------------------------------------------------------
module bd_ctree #(parameter N = 2)
                 (input wire [N-1:0] a, input wire rst, output wire q);
    generate
        if (N == 1)      begin : g1 assign q = a[0]; end
        else if (N == 2) begin : g2 bd_c2 u (.a(a[0]), .b(a[1]), .rst(rst), .q(q)); end
        else if (N == 3) begin : g3 bd_c3 u (.a(a[0]), .b(a[1]), .c(a[2]), .rst(rst), .q(q)); end
        else if (N == 4) begin : g4 bd_c4 u (.a(a[0]), .b(a[1]), .c(a[2]), .d(a[3]), .rst(rst), .q(q)); end
        else begin : gt
            // Chunks of four, not halves.  A node holds four inputs -- six
            // pins less the feedback wire and rst -- so filling every node to
            // its ceiling is what minimises the count.  Halving wastes nodes:
            // five inputs split 2+3 costs three LUTs, split 4+1 costs two.
            localparam integer NCHUNK = (N + 3) / 4;
            wire [NCHUNK-1:0] part;
            genvar i;
            for (i = 0; i < NCHUNK; i = i + 1) begin : chunk
                localparam integer LO  = i * 4;
                localparam integer WID = (N - LO > 4) ? 4 : (N - LO);
                bd_ctree #(.N(WID)) u (.a(a[LO +: WID]), .rst(rst),
                                       .q(part[i]));
            end
            bd_ctree #(.N(NCHUNK)) utop (.a(part), .rst(rst), .q(q));
        end
    endgenerate
endmodule

`default_nettype wire
