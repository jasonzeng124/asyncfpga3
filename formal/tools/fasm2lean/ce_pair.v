// fasm2lean fixture: two library C-elements, one feeding the other, so the
// route has CLB-internal pips (LUT pin muxes) and INT interconnect pips
// between two LUTs.  q1 = C(a,b) (bd_c2), q2 = C(q1,~c) (bd_c2n).
`default_nettype none
module ce_pair (input wire a, input wire b, input wire c, input wire rst,
                output wire q1, output wire q2);
    bd_c2  u1 (.a(a),  .b(b), .rst(rst), .q(q1));
    bd_c2n u2 (.a(q1), .b(c), .rst(rst), .q(q2));
endmodule
`default_nettype wire
