// ---------------------------------------------------------------------------
// bd_merge.v -- merge with exclusive inputs.
//
// There is no select port.  Which input is live is inferred from the
// requests, and that inference is where the cell is delicate.
//
//     z_req  = delta(x_req + y_req)
//     x_ack  = C(x_req, z_ack)          y_ack = C(y_req, z_ack)
//     sel    = x_req + x_ack
//     z_data = sel ? x_data : y_data
//
// Two mistakes this cell exists to not make:
//
//   The acknowledge cannot be an AND.  With x_ack = x_req . z_ack the
//   acknowledge collapses the instant x drops its request, while z_ack is
//   still high; x believes it is finished and may raise a new request into a
//   channel that has not returned to zero.  C(x_req, z_ack) holds until both
//   have fallen, and handles the idle input for free -- C(0, z_ack) stays at
//   zero.
//
//   The select cannot be the request.  Selecting on x_req flips the mux the
//   moment x enters phase three, while the downstream latch is still
//   transparent.  The select must rise with the request and fall with the
//   acknowledge, which is x_req + x_ack.
//
// The obligation, rarely met: exclusivity is not enough.  The cell also
// requires that the second input cannot assert until the first transaction
// has fully completed, otherwise C(y_req, z_ack) fires into a still-high
// z_ack and acknowledges a token the merge never carried.  Pipelined code
// does not satisfy that, which is why the join at the bottom of an if is
// bd_mux and not this cell.
//
// Cost: 1 (request OR) + DELAY + 2 (acknowledges) + 1 (select) + W/2 (data).
// The two acknowledge C-elements touch five wires between them, but each also
// needs rst, so they land in separate LUT6s rather than sharing one.
// ---------------------------------------------------------------------------

`default_nettype none

module bd_merge #(parameter W = 8, parameter DELAY = 4)
    (input  wire             rst,

     input  wire             x_req,
     output wire             x_ack,
     input  wire [W-1:0]     x_data,

     input  wire             y_req,
     output wire             y_ack,
     input  wire [W-1:0]     y_data,

     output wire             z_req,
     input  wire             z_ack,
     output wire [W-1:0]     z_data);

    // Either request makes the output request, after a matched delay: it
    // rises through one OR while z_data crosses the select logic and the mux.
    wire either;
    LUT2 #(.INIT(4'hE)) uor (.I0(x_req), .I1(y_req), .O(either));
    bd_delay #(.N(DELAY)) udly (.a(either), .z(z_req));

    // One C-element per input; only the input that fired is acknowledged.
    bd_c2 uxa (.a(x_req), .b(z_ack), .rst(rst), .q(x_ack));
    bd_c2 uya (.a(y_req), .b(z_ack), .rst(rst), .q(y_ack));

    // High across exactly the x transaction.
    wire sel;
    LUT2 #(.INIT(4'hE)) usel (.I0(x_req), .I1(x_ack), .O(sel));

    bd_datamux #(.W(W)) udat (.a(y_data), .b(x_data), .s(sel), .z(z_data));
endmodule

`default_nettype wire
