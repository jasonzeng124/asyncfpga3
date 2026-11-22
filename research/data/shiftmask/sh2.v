module shr_and(input [31:0] a, input [31:0] b, output [31:0] y); assign y = $signed(a) >>> (b & 32'd31); endmodule
module shru_and(input [31:0] a, input [31:0] b, output [31:0] y); assign y = a >> (b & 32'd31); endmodule
module shl_and(input [31:0] a, input [31:0] b, output [31:0] y); assign y = a << (b & 32'd31); endmodule
module shl_full(input [31:0] a, input [31:0] b, output [31:0] y); assign y = a << b; endmodule
module shr64_and(input [63:0] a, input [63:0] b, output [63:0] y); assign y = a >> (b & 64'd63); endmodule
module shr64_full(input [63:0] a, input [63:0] b, output [63:0] y); assign y = a >> b; endmodule
