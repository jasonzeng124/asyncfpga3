// Audit (shard C): ring with arbitrary reset mask, to vary TOKEN count.
`timescale 1ps / 1ps
module ringm #(parameter integer N = 4, parameter [31:0] M = 0)
    (input wire rst, output wire [N-1:0] c);
    genvar i;
    generate for (i = 0; i < N; i = i + 1) begin : st
        wire prev = c[(i + N - 1) % N];
        wire next = c[(i + 1) % N];
        if (M[i]) bd_c2n_set u (.a(prev), .b(next), .rst(rst), .q(c[i]));
        else      bd_c2n     u (.a(prev), .b(next), .rst(rst), .q(c[i]));
    end endgenerate
endmodule
module tb_ring_tokens;
    localparam integer HOLD = 40 * `BD_HOP_PS;
    localparam integer WINDOW = 200 * `BD_HOP_PS;
    reg rst = 1'b1;
    `define CASE(NAME, NN, MM) \
        wire [NN-1:0] c_``NAME; ringm #(.N(NN), .M(MM)) r_``NAME (.rst(rst), .c(c_``NAME)); \
        integer e_``NAME = 0; always @(c_``NAME) if (!rst) e_``NAME = e_``NAME + 1;
    `CASE(n4k2tb, 4, 32'b0011)   // tb_ring's (4,2): one token
    `CASE(n4tok2, 4, 32'b0101)   // two tokens, N=4 = 2k: predicted DEAD
    `CASE(n5tok2, 5, 32'b00101)  // two tokens, N=5 = 2k+1: predicted LIVE
    `CASE(n6tok3, 6, 32'b010101) // three tokens, N=6: predicted DEAD
    `CASE(n7tok3, 7, 32'b0010101)// three tokens, N=7: predicted LIVE
    `CASE(n6tok2, 6, 32'b000101) // two tokens, N=6: predicted LIVE
    initial begin
        #HOLD rst = 1'b0; #WINDOW;
        $display("n4k2tb edges(any node)=%0d", e_n4k2tb);
        $display("n4tok2 edges=%0d", e_n4tok2);
        $display("n5tok2 edges=%0d", e_n5tok2);
        $display("n6tok3 edges=%0d", e_n6tok3);
        $display("n7tok3 edges=%0d", e_n7tok3);
        $display("n6tok2 edges=%0d", e_n6tok2);
        $finish;
    end
endmodule
