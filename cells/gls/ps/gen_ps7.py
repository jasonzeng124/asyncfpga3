#!/usr/bin/env python3
"""gen_ps7.py -- writes cells/gls/ps/ps7_master.v and ps7_bench.v from ps7_pins.py.

    python3 cells/gls/ps/gen_ps7.py      (re-run after editing ps7_pins.py or BODY)

ps7_master.v is a behavioural PS7_PS7 for the gcd_ps GLS: it drives FCLKCLK0
and is an AXI3 master on M_AXI_GP0 running gcd_ps.v's documented host sequence
over a vector file.  ps7_bench.v is the same master (the AXI tasks are shared
text) running hw/xsdb_bench_gen.tcl's batch sequence on hw/gen_bench.py's
register map instead (BENCH_BODY).  The port list is generated so it always
equals the pins gen.py connects (ps7_pins.py).
"""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ps7_pins

BUSES = {"MAXIGP0ARADDR": 32, "MAXIGP0ARID": 12, "MAXIGP0AWADDR": 32, "MAXIGP0AWID": 12,
         "MAXIGP0WDATA": 32, "MAXIGP0WSTRB": 4, "MAXIGP0BID": 12, "MAXIGP0RDATA": 32,
         "MAXIGP0RID": 12, "FCLKCLK": 4}

BODY = r'''
    // ---- knobs (plusargs) -------------------------------------------------
    //   +PSVEC=<file>   vectors (gen_vectors.py), default ps_vec.hex
    //   +NVEC=<n>       how many to run (default all 64 slots that loaded)
    //   +FCLK_PS=<ps>   FCLK0 period, default 10000 (100 MHz)
    //   +TVEC=<ns>      per-vector timeout for any one poll, default 60000
    //   +PIPE=1         overlap pairs of calls (a protocol violation, for FOR-RESEARCH s2)
    // Every AXI output changes TCO after the ACLK edge it is computed on, and
    // every input is sampled on the edge, as the PS7's registered interface.
    localparam integer TCO = 100;
    localparam [11:0] ID = 12'h3E7;            // never 0 (hw-docs/07: ID echo)
    reg fclk = 1'b0;
    integer fclk_ps, tvec_ns, nvec, maxvec, k, ok, err, hang, idmis, polls, pipe;
    reg [31:0] mem [0:191];
    reg [1023:0] vecfile;
    reg        aresetn = 1'b0;
    reg [31:0] araddr = 0, awaddr = 0, wdata = 0;
    reg [11:0] arid = 0, awid = 0;
    reg [3:0]  wstrb = 0;
    reg        arvalid = 0, awvalid = 0, bready = 0, rready = 0, wvalid = 0;
    reg [31:0] rd_data, st;
    reg        timed_out;
    time       t0, t_req, t_ack, t_out;
    initial begin
        fclk_ps = 10000; tvec_ns = 60000; nvec = 64; pipe = 0;
        if ($value$plusargs("PIPE=%d", pipe)) ;
        if ($value$plusargs("FCLK_PS=%d", fclk_ps)) ;
        if ($value$plusargs("TVEC=%d", tvec_ns)) ;
        if (!$value$plusargs("PSVEC=%s", vecfile)) vecfile = "ps_vec.hex";
        for (k = 0; k < 192; k = k + 1) mem[k] = 32'hxxxxxxxx;
        $readmemh(vecfile, mem);
        maxvec = 0;
        while (maxvec < 64 && mem[3 * maxvec + 2] !== 32'hxxxxxxxx) maxvec = maxvec + 1;
        if ($value$plusargs("NVEC=%d", nvec)) ;
        if (nvec > maxvec) nvec = maxvec;
        if (nvec == 0) begin $display("PS7: no vectors in %0s", vecfile); $finish; end
    end
    always #(fclk_ps / 2) fclk = ~fclk;

    task automatic edge_;  begin @(posedge MAXIGP0ACLK); #(TCO); end endtask

    task automatic axi_write(input [31:0] addr, input [31:0] data);
        integer n;
        begin
            edge_;
            awaddr = addr; awid = ID; wdata = data; wstrb = 4'hF;
            awvalid = 1'b1; wvalid = 1'b1; bready = 1'b1;
            n = 0;
            while (bvalid_i !== 1'b1 && n < 1000) begin @(posedge MAXIGP0ACLK); n = n + 1; end
            #(TCO);
            if (bid_i !== ID) idmis = idmis + 1;
            if (n >= 1000) begin $display("PS7: write 0x%0h got no BVALID", addr); timed_out = 1; end
            awvalid = 1'b0; wvalid = 1'b0;
            edge_;
            bready = 1'b0;
        end
    endtask

    task automatic axi_read(input [31:0] addr, output [31:0] data);
        integer n;
        begin
            edge_;
            araddr = addr; arid = ID;
            arvalid = 1'b1; rready = 1'b1;
            n = 0;
            while (rvalid_i !== 1'b1 && n < 1000) begin @(posedge MAXIGP0ACLK); n = n + 1; end
            data = rdata_i;          // sampled on the edge rvalid was seen on
            #(TCO);
            if (rid_i !== ID) idmis = idmis + 1;
            if (n >= 1000) begin $display("PS7: read 0x%0h got no RVALID", addr); timed_out = 1; end
            arvalid = 1'b0;
            edge_;
            rready = 1'b0;
        end
    endtask

    // poll STATUS until (STATUS & mask) == want, or tvec_ns pass
    task automatic poll(input [31:0] mask, input [31:0] want);
        begin
            t0 = $time;
            axi_read(32'h04, st);
            while (((st & mask) !== want) && ($time - t0 < tvec_ns * 1000) && !timed_out)
                axi_read(32'h04, st);
            if ((st & mask) !== want) timed_out = 1;
        end
    endtask

    initial begin
        ok = 0; err = 0; hang = 0; idmis = 0;
        #1;
        repeat (16) @(posedge MAXIGP0ACLK);
        #(TCO) aresetn = 1'b1;
        repeat (4) @(posedge MAXIGP0ACLK);
        axi_write(32'h00, 32'h4);               // hold the kernel in reset
        repeat (8) @(posedge MAXIGP0ACLK);
        axi_write(32'h00, 32'h0);               // release it
        repeat (8) @(posedge MAXIGP0ACLK);
        if (pipe) begin : pipelined
            // +PIPE=1: NOT gcd_ps.v's protocol.  Vectors in pairs (k, k+1): offer k, wait for
            // its i_ack, offer k+1 at once, then collect two results.  formal/FOR-RESEARCH.md
            // section 2 predicts pair k+1 overtakes a longer pair k; this mode exists to show
            // what a host that overlaps calls would get, which is why the harnesses must not.
            // stage names the wait that timed out: ack0/ack1 = the i_ack of pair k/k+1 (this
            // host offers k+1 and waits for its i_ack BEFORE reading k's result, so an ack1
            // hang can be this host's own deadlock, not the kernel's), out0/out1 = a result.
            reg [31:0] g0, g1;
            reg [8*4:1] stage;
            for (k = 0; k + 1 < nvec; k = k + 2) begin
                timed_out = 0; g0 = 32'hxxxxxxxx; g1 = 32'hxxxxxxxx;
                axi_write(32'h08, mem[3 * k]);     axi_write(32'h0C, mem[3 * k + 1]);
                stage = "ack0";
                axi_write(32'h00, 32'h1);          poll(32'h1, 32'h1);
                if (!timed_out) axi_write(32'h00, 32'h0);
                if (!timed_out) begin axi_write(32'h08, mem[3 * k + 3]); axi_write(32'h0C, mem[3 * k + 4]); end
                if (!timed_out) axi_write(32'h00, 32'h1);
                if (!timed_out) stage = "ack1";
                if (!timed_out) poll(32'h1, 32'h1);
                if (!timed_out) axi_write(32'h00, 32'h0);
                if (!timed_out) stage = "out0";
                if (!timed_out) poll(32'h2, 32'h2);
                if (!timed_out) axi_read(32'h10, g0);
                if (!timed_out) axi_write(32'h00, 32'h2);
                if (!timed_out) poll(32'h2, 32'h0);
                if (!timed_out) axi_write(32'h00, 32'h0);
                if (!timed_out) stage = "out1";
                if (!timed_out) poll(32'h2, 32'h2);
                if (!timed_out) axi_read(32'h10, g1);
                if (!timed_out) axi_write(32'h00, 32'h2);
                if (!timed_out) poll(32'h2, 32'h0);
                if (!timed_out) axi_write(32'h00, 32'h0);
                $display("PSPIPE vecs=%0d,%0d exp=%08h,%08h got=%08h,%08h %0s%0s", k, k + 1,
                         mem[3 * k + 2], mem[3 * k + 5], g0, g1, timed_out ? stage : "",
                         timed_out ? " HANG" :
                         (g0 === mem[3 * k + 2] && g1 === mem[3 * k + 5]) ? "IN_ORDER" :
                         (g0 === mem[3 * k + 5] && g1 === mem[3 * k + 2]) ? "REORDERED" : "WRONG");
                if (timed_out) begin
                    hang = hang + 1;
                    axi_write(32'h00, 32'h4); repeat (8) @(posedge MAXIGP0ACLK);
                    axi_write(32'h00, 32'h0); repeat (8) @(posedge MAXIGP0ACLK);
                end
            end
            $display("PSSUMMARY pipe n=%0d hang=%0d id_mismatch=%0d t_end=%0t", nvec, hang, idmis, $time);
            $finish;
        end
        for (k = 0; k < nvec; k = k + 1) begin
            timed_out = 0;
            axi_write(32'h08, mem[3 * k]);
            axi_write(32'h0C, mem[3 * k + 1]);
            t_req = $time;
            axi_write(32'h00, 32'h1);           // CTRL.i_req = 1
            poll(32'h1, 32'h1);                 // STATUS.i_ack (sticky)
            t_ack = $time;
            if (!timed_out) axi_write(32'h00, 32'h0);           // i_req = 0
            if (!timed_out) poll(32'h2, 32'h2);                 // STATUS.o_req
            t_out = $time;
            if (!timed_out) axi_read(32'h10, rd_data);          // O_DATA
            if (!timed_out) axi_write(32'h00, 32'h2);           // CTRL.o_ack = 1
            if (!timed_out) poll(32'h2, 32'h0);                 // o_req falls
            if (!timed_out) axi_write(32'h00, 32'h0);           // o_ack = 0
            if (timed_out) begin
                hang = hang + 1;
                $display("PSRES vec=%0d a=%08h b=%08h got=-------- exp=%08h HANG STATUS=%0h t_req=%0t",
                         k, mem[3 * k], mem[3 * k + 1], mem[3 * k + 2], st, t_req);
                axi_write(32'h00, 32'h4);       // reset the kernel and go on
                repeat (8) @(posedge MAXIGP0ACLK);
                axi_write(32'h00, 32'h0);
                repeat (8) @(posedge MAXIGP0ACLK);
            end else if (rd_data === mem[3 * k + 2]) begin
                ok = ok + 1;
                $display("PSRES vec=%0d a=%08h b=%08h got=%08h exp=%08h OK t_req=%0t t_ack=%0t t_out=%0t",
                         k, mem[3 * k], mem[3 * k + 1], rd_data, mem[3 * k + 2], t_req, t_ack, t_out);
            end else begin
                err = err + 1;
                $display("PSRES vec=%0d a=%08h b=%08h got=%08h exp=%08h ERR t_req=%0t t_out=%0t",
                         k, mem[3 * k], mem[3 * k + 1], rd_data, mem[3 * k + 2], t_req, t_out);
            end
        end
        $display("PSSUMMARY n=%0d ok=%0d err=%0d hang=%0d id_mismatch=%0d t_end=%0t",
                 nvec, ok, err, hang, idmis, $time);
        $finish;
    end
'''

BENCH_PROG = r'''
    // hw/xsdb_bench_gen.tcl's register map (byte offsets): 0x00 CTRL [2]=kernel rst, 0x08/0x0C OP0/OP1,
    // 0x10 ODATA, 0x14 NRUNS, 0x18 CYCLES, 0x1C PREPCYC, 0x20 BCTRL [0]=start(rise) [1]=bench_rst
    // [3:2]=mode, 0x24 BSTATUS [1]=done [31:16]=completed, 0x28/0x2C LATMIN/LATMAX, 0x38 SIG,
    // 0x3C MISM_ST, 0x50 RUNGAP, 0x54 FSMST, 0x58 ILL (gen_bench.py 7'h16: [3] the S_RTZ-pair sticky,
    // [7] the illegal-transition sticky, [10:8] from, [13:11] to, [31:16] run), 0x5C ILL cycles.
    initial begin
        idmis = 0; nhang = 0;
        #1;
        repeat (16) @(posedge MAXIGP0ACLK);
        #(TCO) aresetn = 1'b1;
        repeat (4) @(posedge MAXIGP0ACLK);
        axi_write(32'h08, 32'hA5A5A5A5); axi_read(32'h08, odata);
        if (odata !== 32'hA5A5A5A5) begin
            $display("BENCHSUMMARY OP0 readback FAILED (%08h): AXI plumbing not up", odata); $finish;
        end
        axi_write(32'h00, 32'h0);                       // release the kernel's reset
        repeat (8) @(posedge MAXIGP0ACLK);
        if (rungap >= 0) axi_write(32'h50, rungap);
        if (vfmt == 2) begin
            // v2: the bench describes itself (gen_bench.py LAYOUT 0xA0, MEMINFO[m] 0xC0 + 4m) and must agree with
            // the file's header; a kernel with <= 2 words and no memory has no LAYOUT register and reads 0 there.
            axi_read(32'hA0, lay);
            if (lay[15:0] == 16'hB5C2 ? (lay[23:16] != vwords || lay[31:24] != vmems) : (vwords > 2 || vmems > 0)) begin
                $display("BENCHSUMMARY LAYOUT MISMATCH: bench LAYOUT=%08h, %0s says words=%0d mems=%0d", lay, vecfile,
                         vwords, vmems);
                $finish;
            end
            vcall = vwords;
            for (m = 0; m < vmems; m = m + 1) begin
                axi_read(32'hC0 + 4 * m, minfo);
                mdepth[m] = minfo[31:16]; mwidth[m] = minfo[15:8]; vcall = vcall + mdepth[m];
            end
            nvf = vcall > 0 ? vtot / vcall : 0;
            if (vcall == 0 || nvf * vcall != vtot) begin
                $display("BENCHSUMMARY VECFILE %0s holds %0d words, not a whole number of %0d-word calls", vecfile, vtot,
                         vcall);
                $finish;
            end
            if (!$value$plusargs("NBATCH=%d", nbatch)) nbatch = nvf;
            if (nbatch > nvf) nbatch = nvf;
        end
        for (j = 0; j < nbatch; j = j + 1) begin
            if (j > 0) fclk_ps = fclk_ps + pstep;       // bench idle: only the AXI slave sees the change
            repeat (4) @(posedge MAXIGP0ACLK);
            axi_write(32'h20, 32'h2); axi_write(32'h20, 32'h0);   // bench_rst: stickies read 0 first
            axi_read(32'h58, ill);
            if (ill[3] || ill[7]) $display("BENCHPRE batch=%0d ILL=%08h not clear after bench_rst", j, ill);
            if (vfmt == 2) begin
                vbase = j * vcall;
                op0 = vwords > 0 ? vbig[vbase] : 32'h0; op1 = vwords > 1 ? vbig[vbase + 1] : 32'h0; opstep = 0;
                for (k2 = 2; k2 < vwords; k2 = k2 + 1) axi_write(32'h60 + 4 * (k2 - 2), vbig[vbase + k2]);
                // fill every memory through its host port, the kernel idle (between batches)
                axi_write(32'h8C, 32'h0);                // MEMSTAT: clear the count and the stickies
                vo = vbase + vwords;
                for (m = 0; m < vmems; m = m + 1) begin
                    axi_write(32'h80, m << 16);
                    for (i = 0; i < mdepth[m]; i = i + 1) axi_write(32'h84, vbig[vo + i]);
                    vo = vo + mdepth[m];
                end
                if (vmems > 0) begin
                    axi_read(32'h8C, mstat);
                    if (mstat[2:1] != 2'b0 || mstat[31:16] != vcall - vwords)
                        $display("BENCHMEM batch=%0d FILL FAILED MEMSTAT=%08h (%0d accesses expected)", j, mstat,
                                 vcall - vwords);
                end
                if (memchk && vmems > 0) begin
                    nbad = 0; vo = vbase + vwords;
                    for (m = 0; m < vmems; m = m + 1) begin
                        wmask = mwidth[m] >= 32 ? 32'hFFFFFFFF : (32'h1 << mwidth[m]) - 32'h1;
                        axi_write(32'h80, m << 16);
                        for (i = 0; i < mdepth[m]; i = i + 1) begin
                            axi_write(32'h88, 32'h1); axi_read(32'h90, rd);
                            if (rd !== (vbig[vo + i] & wmask)) nbad = nbad + 1;
                        end
                        vo = vo + mdepth[m];
                    end
                    $display("BENCHMEMCHK batch=%0d words=%0d bad=%0d", j, vcall - vwords, nbad);
                end
            end else
            if (nvf > 0) begin op0 = vmem[2 * j]; op1 = vmem[2 * j + 1]; opstep = 0; end
            axi_write(32'h08, op0 + j * opstep); axi_write(32'h0C, op1); axi_write(32'h14, nruns);
            axi_write(32'h20, 32'h0); axi_write(32'h20, 32'h1 | ((mode & 3) << 2));
            t0 = $time;
            axi_read(32'h24, bs);
            while (!bs[1] && ($time - t0 < tbatch_ns * 1000)) begin
                repeat (50) @(posedge MAXIGP0ACLK);
                axi_read(32'h24, bs);
            end
            axi_read(32'h18, cyc);  axi_read(32'h1C, prep); axi_read(32'h28, lmin); axi_read(32'h2C, lmax);
            axi_read(32'h38, sig);  axi_read(32'h3C, mism); axi_read(32'h10, odata);
            axi_read(32'h54, fsm);  axi_read(32'h58, ill);  axi_read(32'h5C, illc);
            $display("BENCHRES batch=%0d fclk_ps=%0d mode=%0d op0=%08h op1=%08h n=%0d completed=%0d cycles=%0d prepcyc=%0d latmin=%0d latmax=%0d sig=%08h odata=%08h mism_st=%0h ill=%08h ill_tr=%0d%0s%0d->%0d ill_rtz=%0d ill_cycles=%0d fsm=%08h t=%0t %0s",
                     j, fclk_ps, mode, op0 + j * opstep, op1, nruns, bs[31:16], cyc, prep, lmin, lmax, sig, odata,
                     mism, ill, ill[7], ":", ill[10:8], ill[13:11], ill[3], illc, fsm, $time, bs[1] ? "DONE" : "HANG");
            axi_write(32'h20, 32'h0);
            if (vfmt == 2 && memdump && vmems > 0 && bs[1]) begin
                // every memory after the batch, read through the host port (a written array's final contents)
                axi_write(32'h8C, 32'h0);
                for (m = 0; m < vmems; m = m + 1) begin
                    axi_write(32'h80, m << 16);
                    $write("BENCHMEM batch=%0d mem=%0d n=%0d data=", j, m, mdepth[m]);
                    for (i = 0; i < mdepth[m]; i = i + 1) begin
                        axi_write(32'h88, 32'h1); axi_read(32'h90, rd);
                        if (i > 0) $write(",");
                        $write("%08h", rd);
                    end
                    $write("\n");
                end
                axi_read(32'h8C, mstat);
                $display("BENCHMEMSTAT batch=%0d memstat=%08h", j, mstat);
            end
            if (!bs[1]) begin
                nhang = nhang + 1;
                axi_write(32'h20, 32'h2); axi_write(32'h20, 32'h0);
                axi_write(32'h00, 32'h4); repeat (8) @(posedge MAXIGP0ACLK);
                axi_write(32'h00, 32'h0); repeat (8) @(posedge MAXIGP0ACLK);
            end
        end
        $display("BENCHSUMMARY batches=%0d hang=%0d id_mismatch=%0d t_end=%0t", nbatch, nhang, idmis, $time);
        $finish;
    end
'''

BENCH_BODY = r'''
    // ---- knobs (plusargs) -------------------------------------------------
    //   +FCLK_PS=<ps>   FCLK0 period of batch 0, default 10000 (100 MHz)
    //   +PSTEP=<ps>     add this to the FCLK0 period before each later batch (a phase sweep of
    //                   the async kernel against aclk; default 0).  The period only changes while
    //                   the bench is idle between batches.
    //   +NBATCH=<n>     batches (default 1)
    //   +NRUNS=<n>      transactions per batch (default 8)
    //   +MODE=<m>       0 UNIFORM (OP0 = LFSR seed), 1 FIXED (default), 2 LEGACY
    //   +OP0=<hex> +OP1=<hex>   operands (default 30, 12 = 48, 18), +OPSTEP=<hex> added to OP0 per batch
    //   +RUNGAP=<n>     inter-run gap register (default: leave the reset value)
    //   +VECFILE=<file> hex "op0 op1" per line ($readmemh, 2 words per vector): batch j runs vector j
    //                   (overrides OP0/OP1/OPSTEP; NBATCH defaults to the number of vectors read)
    //                   A file whose FIRST line is "// benchvec words=W mems=M" is the v2 format instead
    //                   (research/data/suite/bench/README.md): per call, W operand words in signature order
    //                   (OP0, OP1 at 0x08/0x0C, OP2.. at 0x60..), then every element of each of the M memories in
    //                   signature order, its depth read from the bench's MEMINFO; the bench's LAYOUT must agree.
    //   +MEMCHECK=1     v2: after filling the memories, read every word back through the host port and compare
    //   +MEMDUMP=1      v2: after each batch, print every memory's contents (BENCHMEM lines)
    //   +TBATCH=<ns>    a batch that is not done after this is a HANG (default 200 + 20 us per run)
    // Same AXI3 master as gcd_ps's (gen_ps7.py), running hw/xsdb_bench_gen.tcl's run_batch.
    localparam integer TCO = 100;
    localparam [11:0] ID = 12'h3E7;
    localparam integer VBIG = 262144;
    reg fclk = 1'b0;
    integer fclk_ps, pstep, nbatch, nruns, mode, rungap, tbatch_ns, j, idmis, nhang;
    reg [31:0] op0, op1, opstep;
    reg        aresetn = 1'b0;
    reg [31:0] araddr = 0, awaddr = 0, wdata = 0;
    reg [11:0] arid = 0, awid = 0;
    reg [3:0]  wstrb = 0;
    reg        arvalid = 0, awvalid = 0, bready = 0, rready = 0, wvalid = 0;
    reg [31:0] bs, cyc, prep, lmin, lmax, sig, mism, odata, fsm, ill, illc;
    reg [31:0] vmem [0:511];
    reg [1023:0] vecfile;
    integer nvf;
    reg        timed_out;
    time       t0;
    // v2 vector files (gen_bench.py's wider ABI: more operand words, memories behind host ports)
    reg [31:0] vbig [0:VBIG - 1];
    reg [8*256-1:0] vline;
    integer vfmt, vwords, vmems, vfd, vtot, vcall, vbase, vo, m, i, k2, memchk, memdump, nbad;
    integer mdepth [0:7], mwidth [0:7];
    reg [31:0] lay, minfo, mstat, rd, wmask;
    initial begin
        fclk_ps = 10000; pstep = 0; nbatch = 1; nruns = 8; mode = 1; rungap = -1;
        op0 = 32'h30; op1 = 32'h12; opstep = 0;
        if ($value$plusargs("FCLK_PS=%d", fclk_ps)) ;
        if ($value$plusargs("PSTEP=%d", pstep)) ;
        if ($value$plusargs("NBATCH=%d", nbatch)) ;
        if ($value$plusargs("NRUNS=%d", nruns)) ;
        if ($value$plusargs("MODE=%d", mode)) ;
        if ($value$plusargs("OP0=%h", op0)) ;
        if ($value$plusargs("OP1=%h", op1)) ;
        if ($value$plusargs("OPSTEP=%h", opstep)) ;
        if ($value$plusargs("RUNGAP=%d", rungap)) ;
        tbatch_ns = 200000 + 20000 * nruns;
        if ($value$plusargs("TBATCH=%d", tbatch_ns)) ;
        nvf = 0;
        vfmt = 0; vwords = 2; vmems = 0; vtot = 0; vcall = 0; memchk = 0; memdump = 0;
        if ($value$plusargs("MEMCHECK=%d", memchk)) ;
        if ($value$plusargs("MEMDUMP=%d", memdump)) ;
        if ($value$plusargs("VECFILE=%s", vecfile)) begin
            // v2 says so on its first line; any other file is the two-word format, read exactly as before
            vfd = $fopen(vecfile, "r");
            if (vfd != 0) begin
                vline = 0;
                if ($fgets(vline, vfd) != 0)
                    if ($sscanf(vline, "// benchvec words=%d mems=%d", vwords, vmems) == 2) vfmt = 2;
                $fclose(vfd);
            end
            if (vfmt == 2) begin
                // the count of whole calls needs the memories' depths, read from the bench once AXI is up
                for (j = 0; j < VBIG; j = j + 1) vbig[j] = 32'hxxxxxxxx;
                $readmemh(vecfile, vbig);
                while (vtot < VBIG && vbig[vtot] !== 32'hxxxxxxxx) vtot = vtot + 1;
            end else begin
            vwords = 2; vmems = 0;
            for (j = 0; j < 512; j = j + 1) vmem[j] = 32'hxxxxxxxx;
            $readmemh(vecfile, vmem);
            while (nvf < 256 && vmem[2 * nvf + 1] !== 32'hxxxxxxxx) nvf = nvf + 1;
            if (!$value$plusargs("NBATCH=%d", nbatch)) nbatch = nvf;
            if (nbatch > nvf) nbatch = nvf;
            end
        end
    end
    always #(fclk_ps / 2) fclk = ~fclk;

''' + BODY[BODY.index("    task automatic edge_;"):BODY.index("    // poll STATUS")] + BENCH_PROG

def write(fname, body, what):
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)), fname)
    ports = ["    output %s" % p for p in ps7_pins.OUTPUTS] + ["    input  %s" % p for p in ps7_pins.INPUTS]
    lines = ["// GENERATED by cells/gls/ps/gen_ps7.py from ps7_pins.py -- do not edit.",
             what[0], what[1],
             "`timescale 1ps/1ps", "module PS7_PS7 (", ",\n".join(ports), ");"]
    def bus_in(name, w, reg):
        lines.append("    wire [%d:0] %s = {%s};" % (w - 1, reg, ", ".join("%s%d" % (name, i) for i in reversed(range(w)))))
    bus_in("MAXIGP0BID", 12, "bid_i"); bus_in("MAXIGP0RDATA", 32, "rdata_i"); bus_in("MAXIGP0RID", 12, "rid_i")
    lines.append("    wire bvalid_i = MAXIGP0BVALID, rvalid_i = MAXIGP0RVALID;")
    lines.append(body)
    outs = {"MAXIGP0ARADDR": "araddr", "MAXIGP0ARID": "arid", "MAXIGP0AWADDR": "awaddr", "MAXIGP0AWID": "awid",
            "MAXIGP0WDATA": "wdata", "MAXIGP0WSTRB": "wstrb"}
    for name, reg in outs.items():
        for i in range(BUSES[name]):
            lines.append("    assign %s%d = %s[%d];" % (name, i, reg, i))
    for p, r in [("FCLKCLK0", "fclk"), ("FCLKCLK1", "1'b0"), ("FCLKCLK2", "1'b0"), ("FCLKCLK3", "1'b0"),
                 ("MAXIGP0ARESETN", "aresetn"), ("MAXIGP0ARVALID", "arvalid"), ("MAXIGP0AWVALID", "awvalid"),
                 ("MAXIGP0BREADY", "bready"), ("MAXIGP0RREADY", "rready"), ("MAXIGP0WVALID", "wvalid")]:
        lines.append("    assign %s = %s;" % (p, r))
    lines.append("endmodule")
    open(out, "w").write("\n".join(lines) + "\n")
    print("wrote", out)


def main():
    write("ps7_master.v", BODY, ["// A behavioural PS7_PS7 for the gcd_ps GLS: FCLK0 plus an AXI3 master on",
                                 "// M_AXI_GP0 running hw/gcd_ps.v's documented host sequence (see gen_ps7.py)."])
    write("ps7_bench.v", BENCH_BODY, ["// A behavioural PS7_PS7 for the gcd_bench_gen GLS: FCLK0 plus an AXI3 master on",
                                      "// M_AXI_GP0 running hw/xsdb_bench_gen.tcl's batch sequence (see gen_ps7.py)."])

if __name__ == "__main__":
    main()
