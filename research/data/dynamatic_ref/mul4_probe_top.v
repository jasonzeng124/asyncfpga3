// Dynamatic's mul_4_stage (data/verilog/arith/muli.v, verbatim module) fed from a
// register chain shifted in from one pin; result XOR-reduced to one LED.
module dyn_top(input clk_p, output led_red, output led_green);
  wire clk;
  BUFG bg(.I(clk_p), .O(clk));
  reg [63:0] sr = 0;
  always @(posedge clk) sr <= {sr[62:0], ~sr[63] ^ sr[60]};
  wire [31:0] p;
  mul_4_stage #(.DATA_TYPE(32)) m(.clk(clk), .ce(1'b1), .a(sr[31:0]), .b(sr[63:32]), .p(p));
  reg o = 0;
  always @(posedge clk) o <= ^p;
  assign led_red = o;
  assign led_green = sr[0];
endmodule
