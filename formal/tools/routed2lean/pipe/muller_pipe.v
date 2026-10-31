// routed2lean scale fixture: an N-stage Muller pipeline of library C-elements,
// c[i] = C(c[i-1], ~c[i+1]) (bd_c2n, inverted second input), c[-1] = req,
// c[N] = ack.  LUT-only, so 11b's fasm2lean reads it back from the bits.
`default_nettype none
module muller_pipe #(parameter N = 64) (input wire req, input wire ack, input wire rst,
                                        output wire q0, output wire qn);
    wire [N+1:0] c;
    assign c[0] = req;
    assign c[N+1] = ack;
    genvar i;
    generate for (i = 1; i <= N; i = i + 1) begin : st
        bd_c2n u (.a(c[i-1]), .b(c[i+1]), .rst(rst), .q(c[i]));
    end endgenerate
    assign q0 = c[1];
    assign qn = c[N];
endmodule
`default_nettype wire
