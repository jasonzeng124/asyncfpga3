// tb_capture.v -- the load-first lowering's hazard, at one arbitrated port (research/data/suite/dyn/README.md,
// "load first"): a load whose consumer is still reading when ANOTHER station on the same port clocks the RAM.
// Station A loads address 3 (word X); its consumer holds the result (z_ack low) for HOLD_NS before sampling z_data
// and acknowledging.  Inside that window station B stores word Y at address 5: its RAM edge rewrites DOADO (bd_mem is
// WRITE_FIRST), i.e. the load's p_rdata.  The consumer must still see X.
//   -DCAP: A is bdc_load_cap (the word captured at done, bdc/mem.py CAPTURE); without it, the plain bdc_load
//   (z_data = p_rdata): the negative control, which must FAIL.
// Compile with the generated stations/port (bdc/mem.py) and cells/sim + cells/rtl; prints TBCAP PASS / TBCAP FAIL.
`timescale 1ps/1ps
module tb_capture;
    reg rst = 1;
    reg aa_req = 0; wire aa_ack; reg [3:0] aa_data = 0;          // A's address
    wire az_req; reg az_ack = 0; wire [31:0] az_data;             // A's result
    reg ba_req = 0; wire ba_ack; reg [3:0] ba_data = 0;          // B's address
    reg bd_req = 0; wire bd_ack; reg [31:0] bd_data = 0;         // B's data
    wire bz_req; reg bz_ack = 0;                                  // B's completion
    wire [1:0] s_req, s_we, s_ack; wire [7:0] s_addr; wire [63:0] s_wdata; wire [31:0] p_rdata;
    bdc_memport_arb_4_32_2 uport (.rst(rst), .s_req(s_req), .s_addr(s_addr), .s_wdata(s_wdata), .s_we(s_we),
        .s_ack(s_ack), .p_rdata(p_rdata));
`ifdef CAP
    bdc_load_cap_4_32 ua (
`else
    bdc_load_4_32 ua (
`endif
        .rst(rst), .a_req(aa_req), .a_ack(aa_ack), .a_data(aa_data), .z_req(az_req), .z_ack(az_ack), .z_data(az_data),
        .p_req(s_req[0]), .p_ack(s_ack[0]), .p_addr(s_addr[3:0]), .p_wdata(s_wdata[31:0]), .p_we(s_we[0]),
        .p_rdata(p_rdata));
    bdc_store_4_32 ub (
        .rst(rst), .a_req(ba_req), .a_ack(ba_ack), .a_data(ba_data), .d_req(bd_req), .d_ack(bd_ack), .d_data(bd_data),
        .z_req(bz_req), .z_ack(bz_ack),
        .p_req(s_req[1]), .p_ack(s_ack[1]), .p_addr(s_addr[7:4]), .p_wdata(s_wdata[63:32]), .p_we(s_we[1]),
        .p_rdata(p_rdata));
    task store(input [3:0] a, input [31:0] d);
        begin
            ba_data = a; bd_data = d; #1000 ba_req = 1; bd_req = 1;
            wait (bz_req === 1'b1); #500 bz_ack = 1;
            wait (ba_ack === 1'b1 && bd_ack === 1'b1); ba_req = 0; bd_req = 0;
            wait (bz_req === 1'b0); #500 bz_ack = 0;
            wait (ba_ack === 1'b0 && bd_ack === 1'b0); #2000;
        end
    endtask
    integer hold_ns, fails;
    reg [31:0] got;
    initial begin
        if (!$value$plusargs("HOLD_NS=%d", hold_ns)) hold_ns = 30;
        fails = 0;
        #20000 rst = 0; #5000;
        store(4'd3, 32'h1111_1111);            // X at 3
        store(4'd5, 32'h0000_0000);
        // A loads 3; its consumer reads only after hold_ns; meanwhile B stores Y at 5.
        aa_data = 4'd3; #1000 aa_req = 1;
        wait (az_req === 1'b1);
        fork
            begin #(hold_ns * 1000) got = az_data; az_ack = 1; end
            begin #2000 store(4'd5, 32'hBAD0_0BAD); end
        join
        wait (aa_ack === 1'b1); aa_req = 0;
        wait (az_req === 1'b0); #500 az_ack = 0;
        wait (aa_ack === 1'b0); #2000;
        $display("TBCAP %s: the load of address 3 returned %08h (stored %08h; another station wrote %08h at 5 in between)",
                 got === 32'h1111_1111 ? "PASS" : "FAIL", got, 32'h1111_1111, 32'hBAD0_0BAD);
        $finish;
    end
    initial begin #2000000; $display("TBCAP FAIL (timeout)"); $finish; end
endmodule
