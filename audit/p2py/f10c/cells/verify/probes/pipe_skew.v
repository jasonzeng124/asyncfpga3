`timescale 1ps/1ps
module pipe_skew;
  reg rst=1, req_in=0, ack_out=0; reg [7:0] data_in=8'h00;
  wire ack_in, req_out; wire [7:0] data_out;
  bd_pipe #(.W(8), .N(4)) u (.rst(rst), .req_in(req_in), .ack_in(ack_in), .data_in(data_in),
                             .req_out(req_out), .ack_out(ack_out), .data_out(data_out));
  wire [3:0] c = {u.many.stage[3].u.c, u.many.stage[2].u.c, u.many.stage[1].u.c, u.many.stage[0].u.c};
  initial begin
    $monitor("%0t req_out=%b data_out=%h c=%b", $time, req_out, data_out, c);
    #2000 rst=0; #2000;
    data_in = 8'hA5; #4000;
    req_in = 1'b1;
    #4000;
    $finish;
  end
endmodule
