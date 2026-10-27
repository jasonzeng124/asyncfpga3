// tb_mux.v -- select-driven mux.
//
// The property that distinguishes this cell from the merge, and the reason it
// is what sits at the bottom of an if, is that THE UNSELECTED INPUT KEEPS ITS
// TOKEN.  So the bench holds a token standing on both inputs at all times and
// checks, every round, that only the branch the control named was consumed and
// the other one is still exactly where it was, value intact.
//
// That is also why the inputs are driven with offer/retract rather than send:
// a token that is offered and not taken is the normal, correct state of a
// mux input, and a testbench that can only do complete handshakes cannot
// express it.

`timescale 1ps / 1ps

module tb_mux;

    localparam integer W = 8;
    localparam integer H = `BD_HOP_PS;
    localparam integer T = 12 * H;

    integer errors = 0;
    integer i;

    task fail(input [511:0] why);
    begin
        errors = errors + 1;
        $display("  FAIL %0s at %0t", why, $time);
    end
    endtask

    reg rst = 1'b1;

    wire         x_req, x_ack;      wire [W-1:0] x_data;
    wire         y_req, y_ack;      wire [W-1:0] y_data;
    wire         c_req, c_ack;      wire [0:0]   c_data;
    wire         z_req, z_ack;      wire [W-1:0] z_data;

    bd_source #(.W(W)) xsrc (.req(x_req), .ack(x_ack), .data(x_data));
    bd_source #(.W(W)) ysrc (.req(y_req), .ack(y_ack), .data(y_data));
    bd_source #(.W(1)) csrc (.req(c_req), .ack(c_ack), .data(c_data));

    bd_mux #(.W(W), .DELAY(4)) dut (
        .rst(rst),
        .x_req(x_req), .x_ack(x_ack), .x_data(x_data),
        .y_req(y_req), .y_ack(y_ack), .y_data(y_data),
        .ctl_req(c_req), .ctl_ack(c_ack), .s(c_data[0]),
        .z_req(z_req), .z_ack(z_ack), .z_data(z_data));

    bd_sink #(.W(W)) zsnk (.req(z_req), .ack(z_ack), .data(z_data));

    bd_monitor #(.W(W), .CHAN("mux-z")) mz (.req(z_req), .ack(z_ack), .data(z_data));

    // Exclusivity of the joins: the two branches may never be acknowledged in
    // the same transaction.
    reg watching = 1'b0;
    always @* if (watching && x_ack === 1'b1 && y_ack === 1'b1)
        fail("both branches acknowledged at once");

    // -- one round ----------------------------------------------------------
    // The control send and the selected input's retraction have to run
    // concurrently: ctl_ack is z_ack, and z_ack cannot fall until the taken
    // branch has dropped its request, so a sequential bench would deadlock.
    reg [W-1:0] xheld, yheld;
    task round(input sv);
    begin
        xheld = x_data;
        yheld = y_data;
        fork
            csrc.send({sv});
            begin
                if (sv) begin wait (y_ack === 1'b1); ysrc.retract; end
                else    begin wait (x_ack === 1'b1); xsrc.retract; end
            end
        join
        #(2 * T);
    end
    endtask

    integer nz;
    reg [7:0] nx, ny;

    initial begin
        $display("tb_mux");
        #(4 * T);
        rst = 1'b0;
        #(4 * T);
        mz.arm; watching = 1'b1;

        nx = 8'h10;
        ny = 8'hA0;
        xsrc.offer(nx);
        ysrc.offer(ny);
        #(2 * T);

        nz = 0;
        for (i = 0; i < 16; i = i + 1) begin
            // A fixed pattern for the first four so both repeats and switches
            // are covered deterministically, then random.
            reg sv;
            sv = (i < 4) ? i[0] : ($random & 1);

            round(sv);
            nz = nz + 1;

            if (zsnk.n != nz) fail("mux dropped a token");
            else if (zsnk.seen[nz-1] !== (sv ? yheld : xheld)) begin
                errors = errors + 1;
                $display("  FAIL s=%b: got %h expected %h at %0t",
                         sv, zsnk.seen[nz-1], sv ? yheld : xheld, $time);
            end

            // The branch that was not named must still be standing there,
            // request up, value unchanged, never acknowledged.
            if (sv) begin
                if (x_req !== 1'b1 || x_data !== xheld)
                    fail("unselected x token was disturbed");
                ny = ny + 1;
                ysrc.offer(ny);
            end else begin
                if (y_req !== 1'b1 || y_data !== yheld)
                    fail("unselected y token was disturbed");
                nx = nx + 1;
                xsrc.offer(nx);
            end
            #(2 * T);
        end

        $display("  %0d rounds, %0d tokens out", 16, zsnk.n);

        errors = errors + mz.errors;
        if (errors == 0) $display("tb_mux PASS");
        else             $display("tb_mux FAIL (%0d)", errors);
        $finish;
    end

    initial begin
        #60_000_000;
        $display("tb_mux FAIL (timeout)");
        $finish;
    end
endmodule
