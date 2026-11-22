`timescale 1ps/1ps
module tb; reg rst=1; reg n_req=0, start_req=0, out0_ack=0, p_end_ack=0; reg [31:0] n_data=0;
wire n_ack,start_ack,out0_req,p_end_req; wire [31:0] out0_data;
bdc_collatz dut(.rst(rst),.n_req(n_req),.n_ack(n_ack),.n_data(n_data),.start_req(start_req),.start_ack(start_ack),.out0_req(out0_req),.out0_ack(out0_ack),.out0_data(out0_data),.p_end_req(p_end_req),.p_end_ack(p_end_ack));
integer i; reg [31:0] V[0:49];
initial begin
 V[0]=32'd1;
 V[1]=32'd2;
 V[2]=32'd3;
 V[3]=32'd4;
 V[4]=32'd5;
 V[5]=32'd6;
 V[6]=32'd7;
 V[7]=32'd8;
 V[8]=32'd9;
 V[9]=32'd16;
 V[10]=32'd27;
 V[11]=32'd97;
 V[12]=32'd871;
 V[13]=32'd6171;
 V[14]=32'd77031;
 V[15]=32'd14149;
 V[16]=32'd11960;
 V[17]=32'd97969;
 V[18]=32'd173;
 V[19]=32'd46846;
 V[20]=32'd39576;
 V[21]=32'd28790;
 V[22]=32'd11513;
 V[23]=32'd68079;
 V[24]=32'd12073;
 V[25]=32'd1086;
 V[26]=32'd84606;
 V[27]=32'd4324;
 V[28]=32'd9494;
 V[29]=32'd56179;
 V[30]=32'd81887;
 V[31]=32'd76972;
 V[32]=32'd91672;
 V[33]=32'd83484;
 V[34]=32'd30189;
 V[35]=32'd69988;
 V[36]=32'd93754;
 V[37]=32'd1992;
 V[38]=32'd58998;
 V[39]=32'd6126;
 V[40]=32'd91251;
 V[41]=32'd84349;
 V[42]=32'd84914;
 V[43]=32'd75309;
 V[44]=32'd5874;
 V[45]=32'd95207;
 V[46]=32'd53837;
 V[47]=32'd50121;
 V[48]=32'd6514;
 V[49]=32'd19782;
 #20000 rst=0; #20000;
 for (i=0;i<50;i=i+1) begin
  n_data=V[i]; #1000 n_req=1; start_req=1;
  fork begin wait(n_ack); n_req=0; wait(!n_ack); end begin wait(start_ack); start_req=0; wait(!start_ack); end
   begin wait(out0_req); #500 $display("RES %0d %0d", $signed(V[i]), $signed(out0_data)); out0_ack=1; wait(!out0_req); #500 out0_ack=0; end
   begin wait(p_end_req); #500 p_end_ack=1; wait(!p_end_req); #500 p_end_ack=0; end join
  #2000; end
 $display("DONE"); $finish; end
initial begin #2000000000; $display("TIMEOUT"); $finish; end
endmodule
