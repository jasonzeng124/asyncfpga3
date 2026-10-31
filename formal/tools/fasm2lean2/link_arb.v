// fasm2lean2 fixture (probe C-11c): one bd_link stage (W=3: a fractured
// LUT6_2 latch pair, an odd LUT6 latch bit, the bd_c2n controller) and one
// bd_arbiter (two LUT6_2 sites, two bd_c2), sharing rst.  Cells verbatim
// from cells/rtl/; DELAY = DACK = 0 (the frozen defaults), so req_out and
// ack_in are both the controller node c.
`default_nettype none
module link_arb (input wire rst,
                 input wire req_in, output wire ack_in, input wire [2:0] data_in,
                 output wire req_out, input wire ack_out, output wire [2:0] data_out,
                 input wire r1, output wire A1, input wire r2, output wire A2,
                 output wire R0, input wire A0, output wire g1, output wire g2);
    bd_link #(.W(3)) lnk (.rst(rst), .req_in(req_in), .ack_in(ack_in), .data_in(data_in),
                          .req_out(req_out), .ack_out(ack_out), .data_out(data_out));
    bd_arbiter arb (.rst(rst), .r1(r1), .A1(A1), .r2(r2), .A2(A2), .R0(R0), .A0(A0),
                    .g1(g1), .g2(g2));
endmodule
`default_nettype wire
