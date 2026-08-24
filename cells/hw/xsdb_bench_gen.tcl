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
# Optional 5th argument: the SIG this kernel is known to produce for the
# FIXED (FIX_OP0,FIX_OP1) N=200 batch.  See the note at check (a) for why a bench with
# no oracle needs one.
set GOLD_SIG [lindex $argv 4]
# Optional 6th and 7th arguments: the operand pair the FIXED-mode batch and the
# corruption search use, defaulting to the historical hardcoded (48,18).
#
# They are a parameter because (48,18) is not a usable vector for every kernel.
# ipow(48,18) is 48**18 mod 2**32 = 0 EXACTLY, so its SIG folds to 0x00000000 --
# a value a dead kernel, a held-in-reset kernel and a kernel whose output bus
# reads zero all produce too.  Asserting it would be a check that cannot fail
# in the dangerous direction.  ipow is run at (3,7) -> 2187 instead.
set FIX_OP0 [lindex $argv 5]
set FIX_OP1 [lindex $argv 6]
if {$FIX_OP0 eq ""} { set FIX_OP0 48 }
if {$FIX_OP1 eq ""} { set FIX_OP1 18 }
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
# Wait until ANY bit under $mask is set, rather than for one exact value.
proc poll_status_any {mask tag} {
    for {set i 0} {$i < 200} {incr i} {
        set s [mrd -value $::STATUS]
        if {[expr {$s & $mask}] != 0} { return $s }
    }
    error "TIMEOUT waiting for STATUS&[format 0x%x $mask] != 0 ($tag); last STATUS=[format 0x%x $s]"
}

# The manual path has to drive two different kinds of kernel.
#
# DECOUPLED (every real kernel here -- they all carry bd_link/bd_pipe): i_ack
# rises first, the hardware's req_clr asynchronously drops i_req, and only then
# does o_req come up.  This is the sequence the proc used to assume outright.
#
# FULLY COUPLED (the null control: join -> bundling delay -> fork, no storage):
# i_ack CANNOT rise until the output has been taken, so waiting for i_ack before
# offering o_ack is a deadlock -- and it deadlocked exactly that way, STATUS
# stuck at 0x2 with o_req high and i_ack low, on all four null bitstreams.
# Coupled is legal 4-phase, so the host has to cope rather than the kernel.
#
# Two consequences, and the second is the subtle one: while i_ack has not
# arrived, i_req must STAY ASSERTED.  CTRL bit 0 writes straight through to
# req_core, so acknowledging with the usual CTRL=0x2 would drop i_req while the
# output transaction is still open -- joined_req falls, out0_req falls, and the
# result is retracted before it was taken.  The coupled branch writes CTRL=0x3,
# holding i_req across the acknowledge and letting req_clr retire it on i_ack.
# The decoupled branch must NOT do that: there req_core has already self-cleared,
# and re-writing bit 0 would launch a second, spurious request.
proc manual_once {op0 op1} {
    mwr -force $::OP0 $op0
    mwr -force $::OP1 $op1
    mwr -force $::CTRL 0x1
    set st [poll_status_any 0x3 "i_ack or o_req (op0=$op0 op1=$op1)"]
    if {$st & 0x1} {
        # decoupled: input retired, i_req already cleared in hardware
        mwr -force $::CTRL 0x0
        poll_status 0x2 0x2 "o_req rise (op0=$op0 op1=$op1)"
        set got [expr {[mrd -value $::ODATA] & 0xFFFFFFFF}]
        mwr -force $::CTRL 0x2
    } else {
        # coupled: hold i_req across the acknowledge
        poll_status 0x2 0x2 "o_req rise (op0=$op0 op1=$op1)"
        set got [expr {[mrd -value $::ODATA] & 0xFFFFFFFF}]
        mwr -force $::CTRL 0x3
    }
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
    # This branch used to probe-and-fall-back instead of calling manual_once.
    # The reason was real: the null kernels drove out0_req from a bd_delay off
    # their own joined_req and never referenced out0_ack, so their output
    # request was a self-retracting PULSE nanoseconds wide, and a JTAG mrd costs
    # milliseconds -- the level poll could not see it, so the branch asked the
    # bridge's async o_req latch whether a pulse had gone by and printed a NOTE
    # calling it a defect in the kernel.
    #
    # It was a defect, and it is fixed: the null control is now a proper 4-phase
    # relay (join -> bundling delay -> bd_fork, acknowledges rendezvoused in the
    # fork's C-element tree), so every kernel here holds o_req as a level and
    # manual_once drives all of them.  The pulse fallback is deliberately NOT
    # kept: it would silently accept exactly the protocol violation that was
    # just removed, which is how a regression gets back in.
    set got [manual_once 12 18]
    puts "manual 4-phase smoke ($label): op0=12 op1=18 -> ODATA=$got (no oracle asserted for this kernel)"
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
puts "=== (a) FIXED-mode repeatability: op0=$FIX_OP0 op1=$FIX_OP1, N=200 ==="
set r [run_batch 200 1 $FIX_OP0 $FIX_OP1]
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

# ---------------------------------------------------------------------------
# The repeatability check above cannot see a kernel that is DETERMINISTICALLY
# wrong.  No oracle is hardcoded for any kernel but gcd, so 200 identical runs
# that all return the same wrong answer pass every check in this script.
#
# That is not hypothetical.  A deliberately under-delayed xorshift build
# (ucmpi1 cut from 18 matched-delay links to 10) returned 4241718536 for EVERY
# input, in 4 cycles instead of 70 -- the loop-termination compare sampled
# before it settled, so the loop exited immediately.  Check (a) passed it.
# Check (b) only caught it as a side effect: it could not find any operand
# pair that changed the output, because nothing changed the output.
#
# So: if the caller knows what this kernel's SIG should be, assert it.  SIG is
# {sig[30:0],sig[31]} ^ o_data_capture folded over the batch (gen_bench.py),
# i.e. a pure function of the RESULT sequence with no timing in it -- so it is
# stable across routes, seeds and clock rates, and any change to it is a
# change to what the kernel computed.
if {$GOLD_SIG ne ""} {
    set want [expr {$GOLD_SIG}]
    if {$sig != $want} {
        error [format "SIG ORACLE FAILED: FIXED ($FIX_OP0,$FIX_OP1) N=200 folded to 0x%08x, expected 0x%08x. SIG has no timing in it, so this kernel computed something different -- not a slower route, a wrong answer." $sig $want]
    }
    puts [format "SIG oracle PASS (0x%08x matches the expected result fold)" $sig]
} else {
    puts "SIG oracle: not asserted (no expected value passed as argv 4) -- a deterministically wrong answer would NOT be caught by check (a)"
}

# =========================================================================
# (b) deliberate corruption -- prove MISMATCH_STICKY fires on real silicon.
#     Same idea as tb_gcd_bench_gen.v Section 4: start a FIXED batch, let
#     run 0 retire, then rewrite OP1 mid-batch so every subsequent run
#     legitimately diverges from the run-0 reference.
# =========================================================================
puts ""
puts "=== (b) deliberate corruption: prove the mismatch path fires on hardware ==="
# Corrupt something the kernel actually READS.  This used to hardcode
# "rewrite OP1 to 17" and then blame the mismatch path when nothing diverged.
# For half these kernels that corruption is invisible by construction:
# collatz, collatz64 and isprime report nargs=1 in META, so OP1 is not an
# input at all, and ipow reads both but at the old fixed (48,18) both 48**18 and
# 48**17 are 0 mod 2**32, so the "corrupted" run returned exactly the reference.
# A negative control that cannot be observed is not a negative control.  (ipow
# is now run at (3,7); the degeneracy was the vector, not the kernel.)
#
# So: measure first.  Run single-run FIXED batches until we find operands whose
# output actually differs from the reference, and only then run the exercise.
# Compare MISM_REF, not ODATA.  ODATA is o_data_capture, a register that tracks
# the kernel's combinational output EVERY cycle -- including after the batch has
# finished, when bench_busy drops and the operand mux switches back from the
# batch's bench_op0/bench_op1 to the host's raw OP0/OP1.  A pass-through kernel
# has no storage, so at that moment its output is simply the host's operands
# folded together, and the ODATA the host reads is a value NO RUN EVER PRODUCED.
#
# That is not hypothetical: collatz64's domain mask zeroes the high word (the
# 64-bit n is {OP1,OP0}, and the kernel must not be seeded above 2**32), so
# inside a batch collatz64_null cannot see OP1 at all.  ODATA still moved when
# OP1 changed -- 48^18 vs 48^17, measured after each batch -- so the search
# "verified" an operand pair the kernel is structurally blind to, and the
# exercise then failed for the only possible reason: nothing diverged.
#
# MISM_REF is captured DURING run 0, off the same o_data_pl but at the instant
# the run completes and while bench_busy is still high.  For an n=1 FIXED batch
# it is exactly that run's result.
set BASE_OP0 $FIX_OP0
set BASE_OP1 $FIX_OP1
set base_out [dict get [run_batch 1 1 $BASE_OP0 $BASE_OP1] mism_ref]
set cand_op0 ""
set cand_op1 ""
foreach cand [concat [list [list $BASE_OP0 [expr {$BASE_OP1 + 1}]] \
                          [list [expr {$BASE_OP0 + 1}] $BASE_OP1]] \
                    {{48 17} {48 19} {49 18} {47 18} {7 3} {12345 6789} {3 5} {1 1}}] {
    set c0 [lindex $cand 0]
    set c1 [lindex $cand 1]
    set o [dict get [run_batch 1 1 $c0 $c1] mism_ref]
    if {$o != $base_out} {
        set cand_op0 $c0
        set cand_op1 $c1
        puts "  corruption chosen: ($BASE_OP0,$BASE_OP1)->$base_out  vs  ($c0,$c1)->$o  (run-captured, not post-batch ODATA)"
        break
    }
}
if {$cand_op0 eq ""} {
    error "corruption test: no operand pair tried produces an output different from ($BASE_OP0,$BASE_OP1)->$base_out for this kernel, so no mid-batch corruption could ever be detected. Add a pair this kernel is actually sensitive to rather than asserting on one it is not."
}

# The exercise is a RACE between a JTAG write and an on-chip batch, and the
# version before this one reported LOSING that race as a hardware failure.
# xorshift retires a FIXED (48,18) run in ~99 cycles, so 200 runs can be over
# before the first BSTATUS read comes back and the "corrupting" write then
# lands on an idle harness.  Probed on the same bitstream with a longer batch:
# the write landed at run ~85 of 200 and MISMATCH_STICKY set immediately.  The
# mismatch path was never broken; the driver was.
#
# So the exercise now records `completed` at the instant the corrupting write
# lands and treats "the batch had already finished" as INCONCLUSIVE -- escalate
# to a longer batch -- rather than as evidence about the mismatch path.  Only a
# write that demonstrably landed mid-batch is allowed to fail the test.
proc corruption_try {gap nruns base0 base1 c0 c1} {
    mwr -force $::RUNGAP $gap
    set gap_rb [mrd -value $::RUNGAP]
    if {$gap_rb != $gap} {
        error "corruption test: run_gap readback $gap_rb != $gap -- this bitstream predates the run_gap register, so the batch cannot be slowed and this exercise would race"
    }
    mwr -force $::OP0 $base0
    mwr -force $::OP1 $base1
    mwr -force $::NRUNS $nruns
    mwr -force $::BCTRL 0x0                         ;# clean 0->1 edge (see run_batch)
    mwr -force $::BCTRL [expr {0x1 | (1 << 2)}]     ;# FIXED, start
    set bs 0
    for {set i 0} {$i < 400} {incr i} {
        set bs [mrd -value $::BSTATUS]
        if {($bs & 0x2) || ((($bs >> 16) & 0xFFFF) >= 1)} { break }
        after 5
    }
    if {!($bs & 0x2) && ((($bs >> 16) & 0xFFFF) < 1)} {
        mwr -force $::BCTRL 0x0
        error "corruption test: run 0 never retired (BSTATUS=[format 0x%08x $bs])"
    }
    # the deliberate corruption -- FIXED mode resamples both operands every run
    mwr -force $::OP0 $c0
    mwr -force $::OP1 $c1
    set at_write [mrd -value $::BSTATUS]
    set landed_mid [expr {($at_write & 0x2) ? 0 : 1}]
    set done 0
    set poll_max [expr {400 + $nruns}]
    for {set i 0} {$i < $poll_max} {incr i} {
        set bs [mrd -value $::BSTATUS]
        if {$bs & 0x2} { set done 1; break }
        after 10
    }
    if {!$done} {
        mwr -force $::BCTRL 0x0
        error "corruption test: batch never finished (BSTATUS=[format 0x%08x $bs])"
    }
    set r [dict create \
        landed_mid $landed_mid \
        at_completed [expr {($at_write >> 16) & 0xFFFF}] \
        mism_st  [mrd -value $::MISM_ST] \
        mism_idx [mrd -value $::MISM_IDX] \
        mism_val [mrd -value $::MISM_VAL] \
        mism_ref [mrd -value $::MISM_REF]]
    mwr -force $::BCTRL 0x0
    return $r
}

# 2000 runs at a 20000-cycle gap is ~0.8 s of batch at 50 MHz -- three orders
# of magnitude more than a JTAG round trip.  The ladder exists for the case
# where the host is much slower than that, not as a retry-until-green loop:
# a conclusive miss (write landed mid-batch, no mismatch) fails on the spot.
set res ""
foreach step {{20000 2000} {50000 4000} {100000 8000}} {
    set gap   [lindex $step 0]
    set nruns [lindex $step 1]
    set res [corruption_try $gap $nruns $BASE_OP0 $BASE_OP1 $cand_op0 $cand_op1]
    puts [format "  attempt gap=%d n=%d: write landed at run %d of %d (mid-batch=%d) -> MISM_ST=%d MISM_IDX=%d MISM_VAL=%d MISM_REF=%d" \
        $gap $nruns [dict get $res at_completed] $nruns [dict get $res landed_mid] \
        [dict get $res mism_st] [dict get $res mism_idx] [dict get $res mism_val] [dict get $res mism_ref]]
    if {[dict get $res mism_st] & 1} { break }
    if {[dict get $res landed_mid]} { break }
    puts "  INCONCLUSIVE: the batch finished before the corrupting write landed, so nothing diverged and this says nothing about the mismatch path. Retrying with a longer batch."
}
mwr -force $::RUNGAP 15        ;# restore the default rate for section (c)
set mism_st  [dict get $res mism_st]
set mism_idx [dict get $res mism_idx]
set mism_val [dict get $res mism_val]
set mism_ref [dict get $res mism_ref]
if {!($mism_st & 1)} {
    if {![dict get $res landed_mid]} {
        error "corruption test INCONCLUSIVE on every attempt: the batch finished before the corrupting write landed each time, so the mismatch path was never exercised. This is a host/JTAG speed problem, not a hardware result -- raise the gap ladder."
    }
    error "corruption test FAILED: the corrupting write landed at run [dict get $res at_completed] with the batch still running, and MISMATCH_STICKY never set. Switching the operands to ($cand_op0,$cand_op1) was verified above to produce a different output than ($BASE_OP0,$BASE_OP1). The corruption was observable, was applied mid-batch, and was not observed -- the mismatch path does not work on real hardware."
}
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
