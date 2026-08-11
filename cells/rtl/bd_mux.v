// ---------------------------------------------------------------------------
// bd_mux.v -- select-driven mux.
//
// The classical dual-rail-control form rebuilt on bundled data.  A control
// channel picks the input, so the sources need not be exclusive.
//
//     j0     = C(x_req, ctl_req . ~s)
//     j1     = C(y_req, ctl_req .  s)
//     z_req  = delta(j0 + j1)
//     x_ack  = C(j0, z_ack)             y_ack = C(j1, z_ack)
//     ctl_ack = z_ack
//     z_data = s ? y_data : x_data
//
// The control decode needs no gates of its own: folding ctl_req.~s into the
// C-element leaves a function of four wires, which is one LUT6 once rst joins
// it.  But the two joins together touch six distinct wires, so -- unlike the
// steer -- they cannot share a fractured LUT.
//
// Only the selected input is acknowledged: x_ack can only rise if j0 fired,
// and j0 can only fire if the control said x.  The other input keeps its
// token, untouched, which is exactly what a loop header needs.
//
// ctl_ack is z_ack directly.  The control token is consumed by whichever
// branch fired, and z_ack cannot rise until that branch's data has been
// taken, so it already carries the right timing.
//
// Why the select is safe here, where the merge's is not: the merge infers
// which input is live from a request wire, which falls a phase too early.
// The mux infers nothing.  s is ordinary channel data, held by the control
// channel's own contract from ctl_req-rise until ctl_ack-fall -- and since
// ctl_ack is z_ack, the select is valid across exactly the output window.
// That is the real argument for paying for a control channel: it converts a
// timing obligation into a data one.
//
// On dual-rail control: dual-rail is used classically because one wire cannot
// distinguish "control has not arrived" from "control arrived and says zero".
// Bundled control carries the same information split across ctl_req and s, so
// the decode recovers the rail pair exactly and the rest of the circuit is
// identical -- and here the decode is free, because it disappears into the
// join's LUT.
//
// Cost: 2 (joins) + 1 (request OR) + DELAY + 2 (acknowledges) + W/2 (data).
// ---------------------------------------------------------------------------

`default_nettype none

module bd_mux #(parameter W = 8, parameter DELAY = 4)
    (input  wire             rst,

     input  wire             x_req,
     output wire             x_ack,
     input  wire [W-1:0]     x_data,

     input  wire             y_req,
     output wire             y_ack,
     input  wire [W-1:0]     y_data,

     input  wire             ctl_req,
     output wire             ctl_ack,
     input  wire             s,

     output wire             z_req,
     input  wire             z_ack,
     output wire [W-1:0]     z_data);

    // The two joins.  The dashed decode in the schematic is not a cell.
    wire j0, j1;
    (* keep *) LUT6 #(.INIT(64'h0000_AE08_0000_AE08)) uj0 (
        .I0(x_req), .I1(ctl_req), .I2(s), .I3(j0), .I4(rst), .I5(1'b0),
        .O(j0));
    (* keep *) LUT6 #(.INIT(64'h0000_EA80_0000_EA80)) uj1 (
        .I0(y_req), .I1(ctl_req), .I2(s), .I3(j1), .I4(rst), .I5(1'b0),
        .O(j1));

    // Either join makes the output request, after a matched delay.
    wire either;
    LUT2 #(.INIT(4'hE)) uor (.I0(j0), .I1(j1), .O(either));
    bd_delay #(.N(DELAY)) udly (.a(either), .z(z_req));

    // Only the join that fired is acknowledged.
    bd_c2 uxa (.a(j0), .b(z_ack), .rst(rst), .q(x_ack));
    bd_c2 uya (.a(j1), .b(z_ack), .rst(rst), .q(y_ack));

    assign ctl_ack = z_ack;

    bd_datamux #(.W(W)) udat (.a(x_data), .b(y_data), .s(s), .z(z_data));
endmodule

`default_nettype wire
