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

# --- liveness pre-check ---------------------------------------------------
set v [mrd -value $CTRL]
puts "CTRL  after config: [format 0x%08x $v] (expect 0x4: rst=1)"
mwr -force $OP0 0xA5A5A5A5
set v [mrd -value $OP0]
if {$v != 0xA5A5A5A5} { error "OP0 readback FAILED: [format 0x%x $v] != 0xa5a5a5a5 -- AXI plumbing not up" }
mwr -force $OP0 0x0
set v [mrd -value $META]
puts "META  : [format 0x%08x $v] (nargs<<16 | arg0_w<<8 | argN_w)"
puts "liveness pre-check PASS"

mwr -force $CTRL 0x0
after 100

# --- manual path smoke: proves the OP0/OP1/ODATA plumbing reaches the
#     real kernel, generically (no expected value asserted here except for
#     the gcd label, where the oracle is well known and cheap to check).
proc manual_once {op0 op1} {
    mwr -force $::OP0 $op0
    mwr -force $::OP1 $op1
    mwr -force $::CTRL 0x1
    poll_status 0x1 0x1 "i_ack rise (op0=$op0 op1=$op1)"
    mwr -force $::CTRL 0x0
    poll_status 0x2 0x2 "o_req rise (op0=$op0 op1=$op1)"
    set got [expr {[mrd -value $::ODATA] & 0xFFFFFFFF}]
    mwr -force $::CTRL 0x2
    poll_status 0x2 0x0 "o_req fall (op0=$op0 op1=$op1)"
    mwr -force $::CTRL 0x0
    return $got
}

if {$label eq "gcd"} {
    set got [manual_once 12 18]
    if {$got != 6} { error "manual pre-check FAILED: gcd(12,18) = $got, want 6" }
    puts "manual 4-phase pre-check PASS: gcd(12,18) = $got"
    set got [manual_once 48 18]
    if {$got != 6} { error "manual pre-check FAILED: gcd(48,18) = $got, want 6" }
    puts "manual 4-phase pre-check PASS: gcd(48,18) = $got"
    set got [manual_once 0 5]
    if {$got != 5} { error "manual pre-check FAILED: gcd(0,5) = $got, want 5" }
    puts "manual 4-phase pre-check PASS: gcd(0,5) = $got"
} else {
    # The generic branch used to call manual_once and inherit its assumption
    # that o_req is a HELD level.  It is not held by every kernel: the null
    # kernels drive out0_req from a bd_delay off their own joined_req and
    # never reference out0_ack, so their output request is a self-retracting
    # PULSE, nanoseconds wide.  A JTAG mrd costs milliseconds, so the level
    # poll cannot see it and timed out -- reported, wrongly, as "the ODATA
    # plumbing does not reach the kernel".
    #
    # Probe instead of assuming.  Try the level; if it never appears, ask the
    # bridge's async latch whether a pulse went by.  The latch is proven clear
    # first, so a 1 afterwards is this request's pulse and not some older one
    # (nothing clears that latch outside reset and S_ISSUE, and neither has
    # run since the bitstream was configured).
    mwr -force $::OP0 12
    mwr -force $::OP1 18
    set f0 [mrd -value $::FSMST]
    if {($f0 >> 9) & 1} {
        error "o_req_latched reads 1 BEFORE any request was issued (FSMST=[format 0x%08x $f0]) -- the latch cannot be used as evidence a pulse arrived"
    }
    mwr -force $::CTRL 0x1
    poll_status 0x1 0x1 "i_ack rise (op0=12 op1=18)"
    mwr -force $::CTRL 0x0
    set held [poll_status_soft 0x2 0x2]
    set f1 [mrd -value $::FSMST]
    set caught [expr {($f1 >> 9) & 1}]
    set got [expr {[mrd -value $::ODATA] & 0xFFFFFFFF}]
    if {$held} {
        mwr -force $::CTRL 0x2
        poll_status 0x2 0x0 "o_req fall (op0=12 op1=18)"
        mwr -force $::CTRL 0x0
        puts "manual 4-phase smoke ($label): op0=12 op1=18 -> ODATA=$got (no oracle asserted for this kernel)"
    } elseif {$caught} {
        puts "manual smoke ($label): op0=12 op1=18 -> ODATA=$got (free-running sample; no oracle asserted)"
        puts "  NOTE: this kernel's output request did NOT hold as a 4-phase level."
        puts "  It was seen only by the bridge's async o_req latch, i.e. it is a"
        puts "  self-retracting pulse.  bd_end.v's turnaround invariant says every"
        puts "  producer derives its request from the consumer's acknowledge; a"
        puts "  kernel that ignores out0_ack does not, and cannot be handshaked by"
        puts "  a host at JTAG speed.  The batch path below still measures it (the"
        puts "  FSM reads the same latch), but that is a REAL defect in the kernel,"
        puts "  not in this script."
        mwr -force $::CTRL 0x0
    } else {
        error "manual smoke FAILED ($label): i_ack rose but o_req was seen neither as a held level nor by the async latch (FSMST=[format 0x%08x $f1]) -- the output plumbing does not reach the bridge at all"
    }
}

# --- batch driver ----------------------------------------------------------
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

proc cyc2ns {c} { return [expr {double($c) / $::FCLK0_HZ_NOMINAL * 1e9}] }

# =========================================================================
# (a) FIXED-mode repeatability + SIG determinism, N=200
# =========================================================================
puts ""
puts "=== (a) FIXED-mode repeatability: op0=48 op1=18, N=200 ==="
set r [run_batch 200 1 48 18]
set latmin [dict get $r latmin]
set latmax [dict get $r latmax]
set sig    [dict get $r sig]
set mism   [dict get $r mism_st]
puts [format "  completed=%d latmin=%d latmax=%d cyc  prepcyc=%d  odata=%d sig=0x%08x mism_st=%d" \
      [dict get $r completed] $latmin $latmax [dict get $r prepcyc] [dict get $r odata] $sig $mism]
if {$latmin != $latmax} {
    puts "  NOTE: latmin != latmax on identical inputs -- real silicon jitter (not necessarily a bug; report the spread, do not assert equality the way sim did)"
}
if {$mism & 1} { error "FIXED batch: MISMATCH_STICKY set on identical operands -- real repeatability failure, mismatch_idx=[dict get $r mism_idx] mismatch_val=[dict get $r mism_val] mismatch_ref=[dict get $r mism_ref]" }
puts "FIXED-mode repeatability check PASS (no mismatch across [dict get $r completed] identical-input runs)"

# =========================================================================
# (b) deliberate corruption -- prove MISMATCH_STICKY fires on real silicon.
#     Same idea as tb_gcd_bench_gen.v Section 4: start a FIXED batch, let
#     run 0 retire, then rewrite OP1 mid-batch so every subsequent run
#     legitimately diverges from the run-0 reference.
# =========================================================================
puts ""
puts "=== (b) deliberate corruption: prove the mismatch path fires on hardware ==="
# Slow the batch down so the host can actually interleave with it.  At the
# default 15-cycle gap this whole batch is over in ~226 us -- long before the
# first BSTATUS read returns -- so OP1 was being rewritten AFTER the batch had
# finished and nothing ever diverged.  The test then blamed the mismatch path
# for a race in its own driver.  20000 cycles is 200 us per run, ~40 ms for the
# batch, which comfortably outlasts a JTAG round trip.
mwr -force $::RUNGAP 20000
set gap_rb [mrd -value $::RUNGAP]
if {$gap_rb != 20000} {
    error "corruption test: run_gap readback $gap_rb != 20000 -- this bitstream predates the run_gap register, so the batch cannot be slowed and this exercise would race"
}
mwr -force $::OP0 48
mwr -force $::OP1 18
mwr -force $::NRUNS 200
mwr -force $::BCTRL 0x0                         ;# clean 0->1 edge (see run_batch)
mwr -force $::BCTRL [expr {0x1 | (1 << 2)}]     ;# FIXED, start
set bs 0
for {set i 0} {$i < 400} {incr i} {
    set bs [mrd -value $::BSTATUS]
    if {(($bs >> 16) & 0xFFFF) >= 1} { break }
    after 5
}
if {(($bs >> 16) & 0xFFFF) < 1} { error "corruption test: run 0 never retired (BSTATUS=[format 0x%08x $bs])" }
mwr -force $::OP1 17          ;# the deliberate corruption -- FIXED mode resamples every run
set done 0
for {set i 0} {$i < 400} {incr i} {
    set bs [mrd -value $::BSTATUS]
    if {$bs & 0x2} { set done 1; break }
    after 10
}
if {!$done} { error "corruption test: batch never finished (BSTATUS=[format 0x%08x $bs])" }
set mism_st  [mrd -value $::MISM_ST]
set mism_idx [mrd -value $::MISM_IDX]
set mism_val [mrd -value $::MISM_VAL]
set mism_ref [mrd -value $::MISM_REF]
mwr -force $::BCTRL 0x0
mwr -force $::RUNGAP 15        ;# restore the default rate for section (c)
puts [format "  MISM_ST=%d MISM_IDX=%d MISM_VAL=%d MISM_REF=%d" $mism_st $mism_idx $mism_val $mism_ref]
if {!($mism_st & 1)} { error "corruption test FAILED: MISMATCH_STICKY never set after corrupting OP1 mid-batch -- the mismatch path does not work on real hardware" }
puts "deliberate-corruption exercise PASS: mismatch path fires on real silicon (idx=$mism_idx val=$mism_val ref=$mism_ref)"

# =========================================================================
# (c) UNIFORM-mode batch: latency/throughput statistics from the on-chip
#     log histogram.  Bucket decode matches gen_bench.py's encoder:
#     octave = bucket>>2, mantissa = bucket&3,
#     representative value = (octave==0) ? 1 : 2^octave * (1 + mantissa/4)
# =========================================================================
puts ""
puts "=== (c) UNIFORM-mode batch: op0 seed=0xACE12345, N=$N_UNIFORM ==="
set r [run_batch $N_UNIFORM 0 0xACE12345 0]
set completed [dict get $r completed]
set cycles    [dict get $r cycles]
set prepcyc   [dict get $r prepcyc]
set latmin    [dict get $r latmin]
set latmax    [dict get $r latmax]
set mism      [dict get $r mism_st]
puts [format "  completed=%d cycles=%d prepcyc=%d latmin=%d latmax=%d cyc  mism_st=%d" \
      $completed $cycles $prepcyc $latmin $latmax $mism]

set hist {}
set hist_total 0
for {set b 0} {$b < 64} {incr b} {
    set hv [mrd -value [expr {$::HISTBASE + $b*4}]]
    lappend hist $hv
    incr hist_total $hv
}
puts "  histogram sum = $hist_total (expect $completed)"
if {$hist_total != $completed} {
    # This used to be a WARNING, printed just above percentiles that were then
    # reported as if they were data.  It is not a warning.  Every percentile
    # below is reconstructed from these buckets, so a histogram that does not
    # conserve means p50/p90/p99 are fiction -- and the one time it fired for
    # real, the cause was the bridge running above its closing frequency and
    # dropping carries in the bucket counters (gen_bench.py's histogram
    # pipeline note).  min/max/mean/throughput come from separate plain
    # counters and remain trustworthy; the percentiles do not.
    error "histogram does not conserve: sum=$hist_total but completed=$completed runs. The percentiles below would be reconstructed from a distribution that is missing or inventing [expr {abs($hist_total - $completed)}] samples -- refusing to report them. Check the Fmax line in this build's pnr.log first."
}

# Mirrors gen_bench.py's encoder: bucket = leading_one*4 + 2 mantissa bits.
# Bucket 63 is now the SATURATION bucket -- the encoder was narrowed to 16 bits
# (see that file's histogram pipeline note), so anything at or above 2**16
# cycles lands there rather than being spread across the top octave.  Nothing
# in this suite comes within three orders of that, but decode it as a floor
# rather than a midpoint so a saturated run cannot be quoted as a precise one.
proc bucket_value {b} {
    if {$b == 63} { return 65536.0 }
    set o [expr {$b / 4}]
    set m [expr {$b % 4}]
    if {$o == 0} { return 1.0 }
    set base [expr {double(1 << $o)}]
    return [expr {$base * (1.0 + $m/4.0)}]
}

proc percentile {hist total p} {
    set target [expr {$total * $p}]
    set cum 0
    for {set b 0} {$b < 64} {incr b} {
        set cum [expr {$cum + [lindex $hist $b]}]
        if {$cum >= $target} { return [bucket_value $b] }
    }
    return [bucket_value 63]
}

set p50 [percentile $hist $hist_total 0.50]
set p90 [percentile $hist $hist_total 0.90]
set p99 [percentile $hist $hist_total 0.99]
set mean_cyc [expr {double($cycles) / $completed}]

puts ""
puts [format "  latency (cycles): min=%d p50~=%.0f p90~=%.0f p99~=%.0f max=%d mean=%.1f" \
      $latmin $p50 $p90 $p99 $latmax $mean_cyc]
puts [format "  latency (ns, @%.1fMHz nominal): min=%.1f p50~=%.1f p90~=%.1f p99~=%.1f max=%.1f mean=%.1f" \
      [expr {$FCLK0_HZ_NOMINAL/1e6}] [cyc2ns $latmin] [cyc2ns $p50] [cyc2ns $p90] [cyc2ns $p99] [cyc2ns $latmax] [cyc2ns $mean_cyc]]
set mean_ns [cyc2ns $mean_cyc]
puts [format "  throughput (this harness, 1 txn in flight -- NOT pipelined peak): %.1f tx/s" [expr {1.0e9/$mean_ns}]]
puts ""
puts "Histogram (bucket: count  approx-cycles):"
for {set b 0} {$b < 64} {incr b} {
    set hv [lindex $hist $b]
    if {$hv > 0} {
        set bv [bucket_value $b]
        puts [format "  bucket %2d: count=%-6d ~%.0f cyc" $b $hv $bv]
    }
}

puts ""
puts "=========================================================================="
puts "$label bench PASS"
puts "=========================================================================="
