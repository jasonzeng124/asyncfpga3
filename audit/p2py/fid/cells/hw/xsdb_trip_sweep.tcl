# xsdb driver for the GENERALISED per-kernel bench (cells/hw/gen_bench.py),
# NOT the old hand-written gcd_bench.v -- register map, batch protocol and
# histogram readback all differ. See gen_bench.py's emit() for the
# authoritative map; reproduced below, do not let it drift.
#
# Usage: xsdb cells/hw/xsdb_bench_gen.tcl <bitfile> <kernel-label> [n_uniform]
#   e.g. xsdb cells/hw/xsdb_bench_gen.tcl \
#          cells/build/hw/gcd_bench_gen/gcd_bench_gen.bit gcd 2000
#
# Sibling of xsdb_gcd_bench.tcl -- same connect/catch_cpu0_in_bootrom/fpga -f/
# SLCR/memmap/release-reset sequence, copied verbatim (see that file for the
# longer rationale on each step). What's NEW here:
#   - the wider register map (mismatch latch, signature, PREP_CYCLES,
#     64-word histogram at 0x100-0x1FC)
#   - a manual-path precheck using gcd(12,18)/(48,18)/(0,5) IF the kernel is
#     gcd (skipped for other kernels -- the manual path is generic across
#     kernels via OP0/OP1/ODATA, but the EXPECTED VALUES are gcd-specific;
#     no oracle is hardcoded here for the other five)
#   - a FIXED-mode repeatability + SIG determinism check
#   - a deliberate-corruption exercise proving MISMATCH_STICKY fires on
#     real silicon, not just in simulation (tb_gcd_bench_gen.v Section 4)
#   - a UNIFORM-mode batch with full 64-bucket histogram readback and
#     p50/p90/p99 reconstruction (log-octave + 2-bit mantissa decode,
#     matching gen_bench.py's bucket encoder exactly)
#
# Register map (byte offsets from M_AXI_GP0 base 0x40000000):
#   0x00 CTRL     RW [0]=i_req [1]=o_ack [2]=rst        (manual path)
#   0x04 STATUS   RO [0]=i_ack [1]=o_req                (manual path)
#   0x08 OP0      RW operand word 0 (also UNIFORM-mode LFSR seed)
#   0x0C OP1      RW operand word 1
#   0x10 ODATA    RO last result, captured on every completion
#   0x14 NRUNS    RW transactions per batch
#   0x18 CYCLES   RO batch cycles, EXCLUDING S_PREP settling
#   0x1C PREPCYC  RO S_PREP settling cycles for the same batch
#   0x20 BCTRL    RW [0]=start(rise) [1]=bench_rst [3:2]=mode(0=UNIFORM,1=FIXED,2=LEGACY)
#   0x24 BSTATUS  RO [0]=busy [1]=done [31:16]=completed runs
#   0x28 LATMIN   RO
#   0x2C LATMAX   RO
#   0x30 LASTOP0  RO
#   0x34 LASTOP1  RO
#   0x38 SIG      RO rotate-XOR signature over every result this batch
#   0x3C MISM_ST  RO [0]=mismatch sticky (FIXED mode repeatability check)
#   0x40 MISM_IDX RO
#   0x44 MISM_VAL RO
#   0x48 MISM_REF RO
#   0x4C META     RO {nargs[31:16], arg0_width[15:8], argN_width[7:0]}
#   0x100-0x1FC   RO hist[0..63], 4 bytes/word
#
# Clock: FCLK0 nominal 100 MHz (IO PLL 1000 MHz / 10). Same ~2% systematic
# uncertainty caveat as xsdb_gcd_bench.tcl -- not independently calibrated
# here.

set bitfile [lindex $argv 0]
set label   [lindex $argv 1]
if {$bitfile eq ""} { error "usage: xsdb xsdb_bench_gen.tcl <bitfile> <label> \[n_uniform\] \[clk_ctrl_hex\]" }
if {$label eq ""}   { set label "kernel" }
set N_UNIFORM [lindex $argv 2]
if {$N_UNIFORM eq ""} { set N_UNIFORM 2000 }

# Optional 4th arg: FPGA0_CLK_CTRL value (SLCR 0xF8000170), to drive FCLK0 --
# and therefore this bridge's AXI/measurement domain -- at something other
# than the 100 MHz default. Does NOT touch the DUT: the compiled kernel is
# bundled-data with no clock of its own: this only changes how fast the
# poller/histogram/AXI slave sample it. Default reproduces the original
# hardcoded value (DIVISOR0=10, DIVISOR1=1, SRCSEL=IO PLL -> 1000/10=100MHz).
# FCLK0_HZ_NOMINAL is derived from the SAME value so cyc2ns stays correct
# at any clock setting instead of silently assuming 100 MHz.
# xsdb exits nonzero on an uncaught `error` but prints NOTHING -- not on
# stdout, not on stderr.  Both of the last two failures here (the corruption
# race and the null kernel's oracle) presented as a log that simply stopped
# mid-sentence, and had to be re-derived from which puts was the last one to
# appear.  Echo the message on the way out so the log says what went wrong.
rename error _tcl_error
proc error {msg args} {
    puts "ERROR: $msg"
    flush stdout
    uplevel 1 [list _tcl_error $msg {*}$args]
}

set CLK_CTRL_VAL [lindex $argv 3]
if {$CLK_CTRL_VAL eq ""} { set CLK_CTRL_VAL 0x00100A00 }
set DIVISOR0 [expr {($CLK_CTRL_VAL >> 8)  & 0x3F}]
set DIVISOR1 [expr {($CLK_CTRL_VAL >> 20) & 0x3F}]
if {$DIVISOR0 == 0} { set DIVISOR0 1 }
if {$DIVISOR1 == 0} { set DIVISOR1 1 }
set FCLK0_HZ_NOMINAL [expr {1000000000.0 / double($DIVISOR0 * $DIVISOR1)}]
puts "FPGA0_CLK_CTRL=[format 0x%08x $CLK_CTRL_VAL] -> DIVISOR0=$DIVISOR0 DIVISOR1=$DIVISOR1 -> FCLK0 nominal [expr {$FCLK0_HZ_NOMINAL/1e6}] MHz"

set BASE     0x40000000
set CTRL     [expr {$BASE + 0x00}]
set STATUS   [expr {$BASE + 0x04}]
set OP0      [expr {$BASE + 0x08}]
set OP1      [expr {$BASE + 0x0C}]
set ODATA    [expr {$BASE + 0x10}]
set NRUNS    [expr {$BASE + 0x14}]
set CYCLES   [expr {$BASE + 0x18}]
set PREPCYC  [expr {$BASE + 0x1C}]
set BCTRL    [expr {$BASE + 0x20}]
set BSTATUS  [expr {$BASE + 0x24}]
set LATMIN   [expr {$BASE + 0x28}]
set LATMAX   [expr {$BASE + 0x2C}]
set LASTOP0  [expr {$BASE + 0x30}]
set LASTOP1  [expr {$BASE + 0x34}]
set SIG      [expr {$BASE + 0x38}]
set MISM_ST  [expr {$BASE + 0x3C}]
# Inter-run gap, in aclk cycles (gen_bench.py register 7'h14, reset 15).  The
# corruption exercise below needs it: a 200-run FIXED batch retires in about
# 226 us at the default gap, while a single JTAG mrd costs MILLISECONDS, so a
# host cannot land a write inside the batch at all.  Widening the gap is the
# only way to make "mid-batch" mean anything from the host's timescale.
set RUNGAP   [expr {$BASE + 0x50}]
set FSMST    [expr {$BASE + 0x54}]   ;# bit9 = o_req_latched (async-set catch of a narrow o_req)
set MISM_IDX [expr {$BASE + 0x40}]
set MISM_VAL [expr {$BASE + 0x44}]
set MISM_REF [expr {$BASE + 0x48}]
set META     [expr {$BASE + 0x4C}]
set HISTBASE [expr {$BASE + 0x100}]

set SLCR_UNLOCK     0xF8000008
set SLCR_LOCK       0xF8000004
set SLCR_UNLOCK_KEY 0xDF0D
set SLCR_LOCK_KEY   0x767B
set FPGA0_CLK_CTRL  0xF8000170
set LVL_SHFTR_EN    0xF8000900
set FPGA_RST_CTRL   0xF8000240

# Returns 1/0 instead of raising.  Used where a miss is a legitimate outcome
# being tested for, not a failure: the error shim above prints every raised
# message, so probing with `catch {poll_status ...}` would stamp a misleading
# "ERROR:" into a log where nothing went wrong.
proc poll_status_soft {mask want} {
    for {set i 0} {$i < 200} {incr i} {
        set s [mrd -value $::STATUS]
        if {([expr {$s & $mask}]) == $want} { return 1 }
    }
    return 0
}

proc poll_status {mask want tag} {
    for {set i 0} {$i < 200} {incr i} {
        set s [mrd -value $::STATUS]
        if {([expr {$s & $mask}]) == $want} { return $s }
    }
    error "TIMEOUT waiting for STATUS&[format 0x%x $mask]==[format 0x%x $want] ($tag); last STATUS=[format 0x%x $s]"
}

connect -url tcp:localhost:3121
puts "targets:"
puts [targets]

proc catch_cpu0_in_bootrom {} {
    for {set attempt 0} {$attempt < 5} {incr attempt} {
        if {[catch {targets -set -filter {name =~ "APU"}}]} {
            targets -set -filter {name =~ "DAP*"}
        }
        if {[catch {rst -system} e]} { puts "rst -system: $e"; after 1000; continue }
        set caught 0
        for {set i 0} {$i < 200} {incr i} {
            if {[catch {targets -set -filter {name =~ "ARM*#0"}}]} { after 10; continue }
            if {[catch {stop}]} { after 5; continue }
            after 10
            if {[string match "Stopped*" [state]]} { set caught 1; break }
        }
        if {!$caught} { puts "attempt $attempt: CPU0 not stopped, retrying"; continue }
        set pc [lindex [rrd pc] 1]
        if {[expr {"0x$pc" & 0xffffffff}] < 0x20000} {
            puts "CPU0 caught in BootROM: [state], pc: $pc (attempt $attempt, poll $i)"
            return
        }
        puts "attempt $attempt: caught too late (pc $pc, boot image already up), retrying"
    }
    error "could not catch CPU0 in BootROM after 5 resets"
}
catch_cpu0_in_bootrom

# memmap MUST be declared on APU and BEFORE fpga -f.
targets -set -filter {name =~ "APU"}
memmap -addr $BASE -size 0x1000 -flags 3
targets -set -filter {name =~ "ARM*#0"}

targets -set -filter {name =~ "xc7z010*"}
puts "programming $bitfile ..."
fpga -f $bitfile
puts "FPGA done."

targets -set -filter {name =~ "ARM*#0"}
mwr -force $SLCR_UNLOCK $SLCR_UNLOCK_KEY
mwr -force $FPGA0_CLK_CTRL $CLK_CTRL_VAL     ;# FCLK0 = IO PLL / (DIVISOR0*DIVISOR1)
mwr -force $LVL_SHFTR_EN 0xF
mwr -force $FPGA_RST_CTRL 0x0
mwr -force $SLCR_LOCK $SLCR_LOCK_KEY
puts "SLCR: FCLK0 set (100 MHz nominal), level shifters on, PL resets released."

proc run_batch {n mode op0 op1} {
    mwr -force $::OP0 $op0
    mwr -force $::OP1 $op1
    mwr -force $::NRUNS $n
    set bctrl_val [expr {0x1 | (($mode & 3) << 2)}]
    # start is edge-triggered; drive low first so the 0->1 edge does not depend
    # on every prior exit path having cleared it (an early error leaves it high).
    mwr -force $::BCTRL 0x0
    mwr -force $::BCTRL $bctrl_val

    set poll_iters [expr {200 + $n}]
    set bs 0
    set done 0
    for {set i 0} {$i < $poll_iters} {incr i} {
        set bs [mrd -value $::BSTATUS]
        if {$bs & 0x2} { set done 1; break }
        after 10
    }
    if {!$done} {
        set completed [expr {($bs >> 16) & 0xFFFF}]
        mwr -force $::BCTRL 0x0
        error "TIMEOUT waiting for BSTATUS.done (n=$n mode=$mode); last BSTATUS=[format 0x%08x $bs] completed=$completed/$n"
    }
    set completed [expr {($bs >> 16) & 0xFFFF}]
    if {$completed != ($n & 0xFFFF)} {
        puts "WARNING: completed=$completed != n&0xffff=[expr {$n & 0xFFFF}]"
    }

    set r [dict create n $n mode $mode completed $completed \
        cycles   [mrd -value $::CYCLES] \
        prepcyc  [mrd -value $::PREPCYC] \
        latmin   [mrd -value $::LATMIN] \
        latmax   [mrd -value $::LATMAX] \
        odata    [mrd -value $::ODATA] \
        lastop0  [mrd -value $::LASTOP0] \
        lastop1  [mrd -value $::LASTOP1] \
        sig      [mrd -value $::SIG] \
        mism_st  [mrd -value $::MISM_ST] \
        mism_idx [mrd -value $::MISM_IDX] \
        mism_val [mrd -value $::MISM_VAL] \
        mism_ref [mrd -value $::MISM_REF]]
    mwr -force $::BCTRL 0x0
    return $r
}

# Release the kernel from reset before running anything.  The bitstream comes up
# with CTRL.rst=1 and a batch started against a kernel in reset never completes:
# BSTATUS sits busy forever, which xsdb reports as no output at all.
mwr -force $CTRL 0x0
after 100
set v [mrd -value $CTRL]
if {$v != 0} { error "kernel did not leave reset: CTRL=[format 0x%x $v]" }

# ---------------------------------------------------------------------------
# TRIP-COUNT SWEEP for kernels that RETURN their own trip count.
#
# hw/xsdb_rounds_sweep.tcl varies an explicit rounds argument.  collatz and
# collatz64 take one argument and their running time is a wild function of it
# -- 1 takes 0 steps, 27 takes 111, and there is no arithmetic relation between
# them.  But collatz.c returns `steps`, so the kernel HANDS BACK the x-axis:
# odata is the number of loop iterations that run actually performed.  Fit
# cycles against it and the slope is ns per iteration with the call handshake
# divided out, the intercept is that handshake.
#
# The x-axis is therefore measured, not assumed -- and it is checked: the
# expected stopping time for each input is passed in and the board's answer
# must match it, or the fit is refused.  A sweep whose x-axis is wrong produces
# a beautifully linear plot of nothing.
# ---------------------------------------------------------------------------
# EVERY INPUT MUST FIT THE HARNESS'S DOMAIN MASK, WHICH IS NOT THE PORT WIDTH.
# This is not a formality.  The kernel's port is [31:0] and META duly reports
# 32 bits -- but hw/gen_bench.py masks collatz's argument to 16 bits before it
# ever reaches the kernel (see DOMAIN_MASKS there: every n <= 0xFFFF peaks at
# most 593,279,152, inside INT32_MAX, while the next mask up peaks at 1.7e10
# and does not fit).  It also maps 0 -> 1, because collatz(0) never terminates.
#
# So the first version of this sweep asked for 77031, the hardware answered for
# 77031 & 0xFFFF = 11495, and 86 steps really is that input's correct answer.
# A perfectly self-consistent wrong point, identical on both builds, that only
# the expected-value check caught.  Confirmed by probe: 77031 and 142567 both
# return collatz(11495)=86, and 100000 returns collatz(34464)=36.
#
# META is read below anyway -- it is the right check for a genuinely narrow
# port -- but it will NOT catch the harness mask.  Keep inputs <= 0xFFFF.
set v [mrd -value $META]
set NARGS   [expr {($v >> 16) & 0xFF}]
set ARG0_W  [expr {($v >>  8) & 0xFF}]
puts [format "META 0x%08x -> nargs=%d arg0 width=%d bits (max input %u)" \
      $v $NARGS $ARG0_W [expr {(1 << $ARG0_W) - 1}]]

# Inputs per kernel, chosen against each one's DOMAIN MASK in hw/gen_bench.py:
#   collatz   masks n to 0x0000FFFF, so nothing above 65535.
#   collatz64 masks only the HIGH word, so n may run to 2**32-1; its largest
#             sampled peak here is 966,616,035,460, well inside INT64_MAX.
# Expected stopping times are computed independently, not read off the board.
switch -glob -- [lindex $argv 1] {
    collatz64* {
        set INPUTS   {1 2 4 7 27 871 6171 52527 837799 8400511 63728127 670617279}
        set EXPECTED {0 1 2 16 111 178  261   339    524     685      949       986}
    }
    default {
        set INPUTS   {1 2 4 7 27 97 871 6171 52527}
        set EXPECTED {0 1 2 16 111 118 178 261 339}
    }
}
foreach n $INPUTS {
    if {$ARG0_W < 32 && $n > ((1 << $ARG0_W) - 1)} {
        error "input $n does not fit this kernel's $ARG0_W-bit argument port --\
               it would be truncated to [expr {$n & ((1 << $ARG0_W) - 1)}] and the\
               sweep would fit a straight line through the wrong x values"
    }
}
puts ""
puts [format "trip sweep (%.2f MHz):" [expr {$::FCLK0_HZ_NOMINAL/1e6}]]
set xs {}; set ys {}
foreach n $INPUTS want $EXPECTED {
    set d [run_batch 1 1 $n 0]
    set c [dict get $d latmax]
    # MISM_REF, not ODATA.  xsdb_bench_gen.tcl's own warning: ODATA is
    # o_data_capture, a register tracking the kernel's combinational output
    # EVERY cycle including after the batch finished, whereas MISM_REF is
    # latched at the instant the run completed -- "for an n=1 FIXED batch it is
    # exactly that run's result".  Both are read here and disagreement is
    # fatal, because if they ever diverge the x-axis is the thing at risk.
    set got  [dict get $d mism_ref]
    set seen [dict get $d odata]
    if {$got != $seen} {
        error "n=$n: mism_ref=$got but odata=$seen -- the captured result and the\
               live output disagree, so the trip count cannot be trusted"
    }
    if {$got != $want} {
        error "collatz($n) returned $got steps, expected $want -- the kernel is\
               wrong or this field is not the trip count; the x-axis cannot be\
               trusted"
    }
    lappend xs $got; lappend ys $c
    puts [format "  n=%-6d steps=%-4d %6d cyc %9.1f ns" $n $got $c \
          [expr {double($c)/$::FCLK0_HZ_NOMINAL*1e9}]]
}

set nn [llength $xs]
set sx 0.0; set sy 0.0; set sxx 0.0; set sxy 0.0
foreach x $xs y $ys {
    set sx [expr {$sx+$x}]; set sy [expr {$sy+$y}]
    set sxx [expr {$sxx+$x*$x}]; set sxy [expr {$sxy+$x*$y}]
}
set slope [expr {($nn*$sxy - $sx*$sy) / ($nn*$sxx - $sx*$sx)}]
set icept [expr {($sy - $slope*$sx) / $nn}]
set ss 0.0
foreach x $xs y $ys { set e [expr {$y - ($slope*$x + $icept)}]; set ss [expr {$ss + $e*$e}] }
set rms [expr {sqrt($ss/$nn)}]
puts ""
puts [format "TRIP label=%s ns_per_iter=%.2f ns_call_overhead=%.1f slope_cyc=%.4f icept_cyc=%.2f rms_cyc=%.2f points=%d" \
      [lindex $argv 1] [expr {$slope/$::FCLK0_HZ_NOMINAL*1e9}] \
      [expr {$icept/$::FCLK0_HZ_NOMINAL*1e9}] $slope $icept $rms $nn]
# A NEGATIVE intercept is not a measurement, it is the model failing.  Call
# overhead cannot be below zero, so if the fit reports one it means
# cycles = a*steps + b does not describe this kernel over this range -- for
# collatz64 unsized the fit is dominated by its high-step points (949 and 986
# steps) and misses the low ones, giving icept = -2.46 cyc against a MEASURED
# 7 cyc at zero steps.  The slope is still well determined there (rms 3.5 cyc
# against values up to 25326, 0.01%), but say so rather than printing a
# negative overhead as if it were a number about the hardware.
if {$icept < 0} {
    puts "  WARNING: fitted overhead is NEGATIVE -- the linear model does not"
    puts "  hold across this whole range, so treat the intercept as an artifact."
    puts [format "  The measured zero-step point is %d cyc; trust that instead." \
          [lindex $ys 0]]
}
puts "  ns_per_iter is the slope; ns_call_overhead is the intercept."
puts "  NOTE collatz's iterations are not uniform -- an even step is a shift, an"
puts "  odd step is 3n+1 -- so this slope is the MEAN over whatever mix each"
puts "  input happened to run.  That is the honest number for a data-dependent"
puts "  kernel, but it is a mean, not a single path's cost."
