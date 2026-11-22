module shr_full(input [31:0] a, input [31:0] b, output [31:0] y); assign y = $signed(a) >>> b; endmodule
module shr_low5(input [31:0] a, input [31:0] b, output [31:0] y); assign y = $signed(a) >>> b[4:0]; endmodule
module shru_full(input [31:0] a, input [31:0] b, output [31:0] y); assign y = a >> b; endmodule
module shru_low5(input [31:0] a, input [31:0] b, output [31:0] y); assign y = a >> b[4:0]; endmodule
