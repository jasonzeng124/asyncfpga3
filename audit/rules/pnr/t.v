module top(input wire a, b, c, d, e, output wire y, z);
  wire n1, n2, n3, n4;
  (* keep *) LUT6 #(.INIT(64'h6996966996696996)) l1 (.I0(a),.I1(b),.I2(c),.I3(d),.I4(e),.I5(a^b),.O(n1));
  (* keep *) LUT6 #(.INIT(64'h8000000000000001)) l2 (.I0(n1),.I1(b),.I2(c),.I3(d),.I4(e),.I5(a),.O(n2));
  (* keep *) LUT6 #(.INIT(64'hFEFEFEFEFEFEFE01)) l3 (.I0(a),.I1(n1),.I2(n2),.I3(c),.I4(d),.I5(e),.O(n3));
  (* keep *) LUT6 #(.INIT(64'h1234567887654321)) l4 (.I0(n3),.I1(n2),.I2(n1),.I3(a),.I4(b),.I5(c),.O(n4));
  (* keep *) LUT6 #(.INIT(64'h0F0F0F0FF0F0F0F0)) l5 (.I0(n4),.I1(n3),.I2(n2),.I3(n1),.I4(e),.I5(d),.O(z));
  assign y = n4 ^ n1;
endmodule
