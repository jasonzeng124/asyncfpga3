// Clocked twin of xorshift_round (bdc/fusion_bench.py, forks1-cap4):
// the same three xors in the same two cones, a 32-bit register where each
// design has a storage stage (after x, after v9), and a registered output.
// The source is an LFSR register so the routed netlist is self-contained.
// pin_in is the clock (the board has two PL pins; -noclkbuf routes it on the
// fabric, as the async designs' request wires are).
`default_nettype none

module sync_xorshift (input wire clk,
                      input wire [31:0] x_data,
                      output reg [31:0] out_data);
    reg [31:0] r_x, r_v9;
    wire [31:0] w_n3 = r_x << 32'hd;
    wire [31:0] w_n4 = r_x ^ w_n3;
    wire [31:0] w_n8 = w_n4 >> 32'h11;
    wire [31:0] v9 = w_n4 ^ w_n8;
    wire [31:0] w_n13 = r_v9 << 32'h5;
    always @(posedge clk) begin
        r_x <= x_data;
        r_v9 <= v9;
        out_data <= r_v9 ^ w_n13;
    end
endmodule

module sync_top (input wire pin_in, output wire pin_out);
    wire clk = pin_in;
    (* keep *) reg [31:0] src = 32'h5a3c5a3c;
    always @(posedge clk)
        src <= {src[30:0], src[31] ^ src[21] ^ src[1] ^ src[0]};
    wire [31:0] out_data;
    sync_xorshift uut (.clk(clk), .x_data(src), .out_data(out_data));
    (* keep *) reg q = 0;
    always @(posedge clk) q <= ^out_data;
    assign pin_out = q;
endmodule
`default_nettype wire
