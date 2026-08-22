# Step 2 validation: host-independent cross-check of gcd_bench_gen's
# UNIFORM-mode batch against host_gcd_replay.py, using the SAME LFSR seed.
#
# This is deliberately separate from xsdb_bench_gen.tcl's own section (c),
# which reports statistics but never asserts SIG/LASTOP0/LASTOP1 against an
# independently-computed oracle. That is exactly the gap the harness spec's
# step 2 calls out: "a histogram from a kernel that is computing the wrong
# answer is just a picture of noise." Here the host (host_gcd_replay.py)
# replays the identical 32-bit LFSR from the identical seed, computes gcd
# with the literal C algorithm (not math.gcd, though the two were checked to
# agree over 200k random nonnegative pairs), and this script is handed the
# expected SIG/LASTOP0/LASTOP1 as arguments so THE BOARD asserts against them
# and prints its own PASS/FAIL -- no human reads a register dump.
#
# Usage: xsdb xsdb_gcd_sig_check.tcl <bitfile> <seed_hex> <n> <exp_sig_hex> <exp_op0_hex> <exp_op1_hex>
set bitfile   [lindex $argv 0]
set seed_hex  [lindex $argv 1]
set n         [lindex $argv 2]
set exp_sig   [lindex $argv 3]
set exp_op0   [lindex $argv 4]
set exp_op1   [lindex $argv 5]
if {$bitfile eq "" || $exp_sig eq ""} {
    error "usage: xsdb xsdb_gcd_sig_check.tcl <bitfile> <seed_hex> <n> <exp_sig_hex> <exp_op0_hex> <exp_op1_hex>"
}

set BASE     0x40000000
set CTRL     [expr {$BASE + 0x00}]
set OP0      [expr {$BASE + 0x08}]
set OP1      [expr {$BASE + 0x0C}]
set NRUNS    [expr {$BASE + 0x14}]
set BCTRL    [expr {$BASE + 0x20}]
set BSTATUS  [expr {$BASE + 0x24}]
set LASTOP0  [expr {$BASE + 0x30}]
set LASTOP1  [expr {$BASE + 0x34}]
set SIG      [expr {$BASE + 0x38}]
set MISM_ST  [expr {$BASE + 0x3C}]

set SLCR_UNLOCK     0xF8000008
set SLCR_LOCK       0xF8000004
set SLCR_UNLOCK_KEY 0xDF0D
set SLCR_LOCK_KEY   0x767B
set FPGA0_CLK_CTRL  0xF8000170
set LVL_SHFTR_EN    0xF8000900
set FPGA_RST_CTRL   0xF8000240

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

targets -set -filter {name =~ "APU"}
memmap -addr $BASE -size 0x1000 -flags 3
targets -set -filter {name =~ "ARM*#0"}

targets -set -filter {name =~ "xc7z010*"}
puts "programming $bitfile ..."
fpga -f $bitfile
puts "FPGA done."

targets -set -filter {name =~ "ARM*#0"}
mwr -force $SLCR_UNLOCK $SLCR_UNLOCK_KEY
mwr -force $FPGA0_CLK_CTRL 0x00100A00
mwr -force $LVL_SHFTR_EN 0xF
mwr -force $FPGA_RST_CTRL 0x0
mwr -force $SLCR_LOCK $SLCR_LOCK_KEY
puts "SLCR: FCLK0 set (100 MHz nominal), level shifters on, PL resets released."

mwr -force $CTRL 0x0
after 100

mwr -force $OP0 $seed_hex
mwr -force $OP1 0
mwr -force $NRUNS $n
mwr -force $BCTRL 0x0   ;# BCTRL.start is edge-triggered (start_rise), so drive it
mwr -force $BCTRL 0x1   ;# low first -- a left-high bit would hang and read as a board fault

set bs 0
set done 0
for {set i 0} {$i < [expr {200 + $n}]} {incr i} {
    set bs [mrd -value $BSTATUS]
    if {$bs & 0x2} { set done 1; break }
    after 10
}
if {!$done} { error "TIMEOUT waiting for batch done, BSTATUS=[format 0x%08x $bs]" }
set completed [expr {($bs >> 16) & 0xFFFF}]

set got_sig  [mrd -value $SIG]
set got_op0  [mrd -value $LASTOP0]
set got_op1  [mrd -value $LASTOP1]
set mism     [mrd -value $MISM_ST]
mwr -force $BCTRL 0x0

puts ""
puts "=== gcd host cross-check: seed=$seed_hex n=$n ==="
puts [format "  completed=%d (want %d)" $completed $n]
puts [format "  SIG:     board=0x%08x  host=%s" $got_sig $exp_sig]
puts [format "  LASTOP0: board=0x%08x  host=%s" $got_op0 $exp_op0]
puts [format "  LASTOP1: board=0x%08x  host=%s" $got_op1 $exp_op1]

set ok 1
if {$completed != $n} { puts "  FAIL: completed != n"; set ok 0 }
if {[format 0x%08x $got_sig] ne $exp_sig}   { puts "  FAIL: SIG mismatch";     set ok 0 }
if {[format 0x%08x $got_op0] ne $exp_op0}   { puts "  FAIL: LASTOP0 mismatch"; set ok 0 }
if {[format 0x%08x $got_op1] ne $exp_op1}   { puts "  FAIL: LASTOP1 mismatch"; set ok 0 }

puts ""
if {$ok} {
    puts "GCD HOST CROSS-CHECK: PASS -- board's compiled kernel reproduces the host's independent gcd/LFSR replica exactly, $n/$n runs"
} else {
    puts "GCD HOST CROSS-CHECK: FAIL -- see mismatches above"
    error "gcd host cross-check FAILED"
}
