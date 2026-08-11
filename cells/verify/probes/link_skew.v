// Measure: does req_out lead data_out at a link's output boundary?
`timescale 1ps/1ps
module link_skew;
  reg rst=1, req_in=0, ack_out=0; reg [7:0] data_in=8'h00;
  wire ack_in, req_out; wire [7:0] data_out;
  bd_link #(.W(8)) u (.rst(rst), .req_in(req_in), .ack_in(ack_in), .data_in(data_in),
                      .req_out(req_out), .ack_out(ack_out), .data_out(data_out));
  time t_req, t_dat;
  initial begin t_req = 0; t_dat = 0; end

  // Two independent watchers so neither can mask the other's edge.
  initial begin
    @(posedge req_out) t_req = $time;
  end
  initial begin
    wait (data_out === 8'hA5) t_dat = $time;
  end

  initial begin
    #2000 rst = 0; #2000;
    data_in = 8'hA5; #4000;            // sender presents data well before req
    req_in  = 1'b1;                    // ... then the request
    #40000;
    $display("req_out rises at %0t ps, data_out settles at %0t ps -> req leads data by %0d ps",
             t_req, t_dat, t_dat - t_req);
    $display("final: req_out=%b data_out=%h ack_in=%b", req_out, data_out, ack_in);
    $finish;
  end
endmodule
