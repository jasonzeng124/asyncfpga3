// The narrowest possible reproducer: one 32x32 multiply, truncated to 32
// bits, exactly as ipow's `r = r * b` lowers.  No handshaking, no kernel,
// no PS -- if this mismatches after synthesis, nothing above it matters.
module mult32 (input [31:0] a, input [31:0] b, output [31:0] p);
  assign p = a * b;
endmodule
