module t; reg [31:0] m[0:887]; reg [31:0] a,b; wire [31:0] s1=$signed(a)>>>b, s2=a<<b, s3=a-b, s4=a>>b; integer i;
initial begin $readmemh("mem.hex",m); for(i=0;i<444;i=i+1) begin a=m[2*i]; b=m[2*i+1]; #1 $display("%08x %08x %08x %08x %08x %08x",a,b,s1,s2,s3,s4); end end endmodule
