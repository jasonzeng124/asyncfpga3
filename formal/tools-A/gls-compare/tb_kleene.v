// tb_kleene.v -- X-propagation of the research GLS's SLICE_LUTX and SELMUX2_1.
// Drives every one of the 3^6 vectors over {0,1,x} on A1..A6 into one
// SLICE_LUTX (INIT set with -Ptb_kleene.INIT=...) and prints
//   V <a1..a6 as 0/1/x> <O6> <O5>
// and every 3^3 vector into SELMUX2_1:  M <d0> <d1> <s0> <out>
`timescale 1ps/1ps
module tb_kleene;
    parameter [63:0] INIT = 64'h0;
    reg [5:0] v;  // placeholder
    reg A1, A2, A3, A4, A5, A6, d0, d1, s0;
    wire o5, o6, mo;
    SLICE_LUTX #(.INIT(INIT)) u (.A1(A1), .A2(A2), .A3(A3), .A4(A4), .A5(A5), .A6(A6), .O5(o5), .O6(o6));
    SELMUX2_1 m (.D0(d0), .D1(d1), .S0(s0), .OUT(mo));
    function automatic tri3(input integer k);
        tri3 = (k == 0) ? 1'b0 : (k == 1) ? 1'b1 : 1'bx;
    endfunction
    integer i, j;
    initial begin
        for (i = 0; i < 729; i = i + 1) begin
            j = i;
            A1 = tri3(j % 3); j = j / 3; A2 = tri3(j % 3); j = j / 3;
            A3 = tri3(j % 3); j = j / 3; A4 = tri3(j % 3); j = j / 3;
            A5 = tri3(j % 3); j = j / 3; A6 = tri3(j % 3);
            #1000;
            $display("V %b%b%b%b%b%b %b %b", A1, A2, A3, A4, A5, A6, o6, o5);
        end
        for (i = 0; i < 27; i = i + 1) begin
            d0 = tri3(i % 3); d1 = tri3((i / 3) % 3); s0 = tri3(i / 9);
            #1000;
            $display("M %b %b %b %b", d0, d1, s0, mo);
        end
        $finish;
    end
endmodule
