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

# ---------------------------------------------------------------------------
# ROUNDS SWEEP -- separate the loop from the call.
#
# xorshift's latency is (per-iteration cost)*rounds + (call overhead), and the
# bench's FIXED mode holds the seed constant so rounds is the only thing that
# moves.  Sweep it: the SLOPE is the per-iteration cost with the handshake
# in/out divided out, which is the quantity Dynamatic's "1 cycle per iteration
# at period P" actually describes.  The INTERCEPT is that overhead -- what a
# single-point measurement silently charges to the loop.
#
# Same argument as the pure-link ring rig (hw/ro_link_ps.v): one ring gives you
# slope and intercept summed together, five rings give you each on its own.
#
# odata is printed per point and MUST differ between rounds, because xorshift
# mixes every bit every round.  Identical odata at two different rounds would
# mean the argument never reached the kernel and the slope is measuring
# nothing.
# ---------------------------------------------------------------------------
# Release the kernel from reset before running anything.  The bitstream comes
# up with CTRL.rst=1 (CTRL reads 0x4 after config) and a batch started against
# a kernel in reset never completes -- BSTATUS sits at 0x1, busy forever.  This
# is the same two lines hw/xsdb_bench_gen.tcl runs right after its liveness
# pre-check; omitting them is what made the first version of this sweep time
# out on its very first point.
mwr -force $CTRL 0x0
after 100
set v [mrd -value $CTRL]
puts [format "CTRL after reset release: 0x%08x (expect 0x0)" $v]
if {$v != 0} { error "kernel did not leave reset: CTRL=[format 0x%x $v]" }

set SEED 48
set ROUNDS {2 4 8 16 32 64 128 256}
puts ""
puts [format "rounds sweep (seed=%d, FIXED mode, %.2f MHz):" $SEED \
      [expr {$::FCLK0_HZ_NOMINAL/1e6}]]
set xs {}; set ys {}; set prev ""
set distinct 1
foreach r $ROUNDS {
    set d [run_batch 1 1 $SEED $r]
    set c [dict get $d latmax]
    set o [dict get $d odata]
    set gotr [dict get $d lastop1]
    if {$gotr != $r} { error "kernel saw rounds=$gotr, asked for $r" }
    if {$o eq $prev} { set distinct 0 }
    set prev $o
    lappend xs $r; lappend ys $c
    puts [format "  rounds %4d   %6d cyc   %9.1f ns   odata=%u" $r $c \
          [expr {double($c)/$::FCLK0_HZ_NOMINAL*1e9}] $o]
}
if {!$distinct} { error "two rounds values produced identical odata -- rounds is not reaching the kernel" }

set n [llength $xs]
set sx 0.0; set sy 0.0; set sxx 0.0; set sxy 0.0
foreach x $xs y $ys {
    set sx [expr {$sx+$x}]; set sy [expr {$sy+$y}]
    set sxx [expr {$sxx+$x*$x}]; set sxy [expr {$sxy+$x*$y}]
}
set slope [expr {($n*$sxy - $sx*$sy) / ($n*$sxx - $sx*$sx)}]
set icept [expr {($sy - $slope*$sx) / $n}]
# Residual, so a bad fit cannot pass as a measurement.
set ss 0.0
foreach x $xs y $ys { set e [expr {$y - ($slope*$x + $icept)}]; set ss [expr {$ss + $e*$e}] }
set rms [expr {sqrt($ss/$n)}]
puts ""
puts [format "SWEEP label=%s ns_per_iter=%.2f ns_call_overhead=%.1f slope_cyc=%.4f icept_cyc=%.2f rms_cyc=%.2f points=%d" \
      [lindex $argv 1] [expr {$slope/$::FCLK0_HZ_NOMINAL*1e9}] \
      [expr {$icept/$::FCLK0_HZ_NOMINAL*1e9}] $slope $icept $rms $n]
puts "  ns_per_iter is the slope: per-iteration cost, call overhead divided out."
puts "  ns_call_overhead is the intercept: what one-point numbers over-charge the loop."
