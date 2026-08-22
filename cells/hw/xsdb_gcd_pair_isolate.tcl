# One-pair isolation probe, kept as a permanent diagnostic tool.
#
# Given a single (op0, op1) pair and its expected gcd result, drives it two
# ways: once through the manual single-shot 4-phase register interface, and
# once through a FIXED-mode batch of n repeats (the SAME S_PREP/S_ISSUE/
# S_WAIT_ACK/S_WAIT_RES/S_ACK/S_RTZ/S_NEXT FSM path a UNIFORM batch uses,
# but with identical operands every run, so the mismatch-sticky repeatability
# latch is meaningful here). Self-reports PASS/FAIL on both paths, no human
# reads a register dump.
#
# Written to bisect this project's first documented SIG-accumulation race
# (2026-08-22): a UNIFORM-mode batch's on-chip SIG diverged from
# host_gcd_replay.py's independent replica starting at run index 3, even
# though that run's own operands (LASTOP0/LASTOP1) and its own result
# (ODATA) both matched the host exactly. Driving that exact pair through
# this script showed the kernel computes and holds the correct answer
# 50/50 times when its operands don't change between runs, which is what
# located the bug in the UNIFORM batch's back-to-back result sampling
# (gen_bench.py's old direct read of the combinational o_data_pl at the
# S_WAIT_RES completion edge) rather than in the compiled kernel. Re-run
# this any time a batched result looks wrong but the manual/single-pair
# path might be clean -- that split is exactly what it's for.
#
# Usage: xsdb xsdb_gcd_pair_isolate.tcl <bitfile> <op0_hex> <op1_hex> <expected_result_dec> <n>
set bitfile [lindex $argv 0]
set op0_hex [lindex $argv 1]
set op1_hex [lindex $argv 2]
set exp_res [lindex $argv 3]
set n       [lindex $argv 4]
if {$n eq ""} { set n 50 }

set BASE     0x40000000
set CTRL     [expr {$BASE + 0x00}]
set OP0      [expr {$BASE + 0x08}]
set OP1      [expr {$BASE + 0x0C}]
set ODATA    [expr {$BASE + 0x10}]
set NRUNS    [expr {$BASE + 0x14}]
set BCTRL    [expr {$BASE + 0x20}]
set BSTATUS  [expr {$BASE + 0x24}]
set LASTOP0  [expr {$BASE + 0x30}]
set LASTOP1  [expr {$BASE + 0x34}]
set SIG      [expr {$BASE + 0x38}]
set MISM_ST  [expr {$BASE + 0x3C}]
set MISM_IDX [expr {$BASE + 0x40}]
set MISM_VAL [expr {$BASE + 0x44}]
set MISM_REF [expr {$BASE + 0x48}]

set SLCR_UNLOCK     0xF8000008
set SLCR_LOCK       0xF8000004
set SLCR_UNLOCK_KEY 0xDF0D
set SLCR_LOCK_KEY   0x767B
set FPGA0_CLK_CTRL  0xF8000170
set LVL_SHFTR_EN    0xF8000900
set FPGA_RST_CTRL   0xF8000240

connect -url tcp:localhost:3121

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

mwr -force $CTRL 0x0
after 100

# --- (1) manual single-shot 4-phase transaction with the exact pair ------
proc manual_once {op0 op1} {
    mwr -force $::OP0 $op0
    mwr -force $::OP1 $op1
    mwr -force $::CTRL 0x1
    for {set i 0} {$i < 200} {incr i} { if {[mrd -value $::STATUS] & 0x1} break; after 5 }
    mwr -force $::CTRL 0x0
    for {set i 0} {$i < 200} {incr i} { if {[mrd -value $::STATUS] & 0x2} break; after 5 }
    set got [expr {[mrd -value $::ODATA] & 0xFFFFFFFF}]
    mwr -force $::CTRL 0x2
    for {set i 0} {$i < 200} {incr i} { if {!([mrd -value $::STATUS] & 0x2)} break; after 5 }
    mwr -force $::CTRL 0x0
    return $got
}
set STATUS [expr {$BASE + 0x04}]
set manual_got [manual_once $op0_hex $op1_hex]
puts [format "manual single-shot: op0=%s op1=%s -> ODATA=%d  (expected %d)" $op0_hex $op1_hex $manual_got $exp_res]
if {$manual_got != $exp_res} {
    puts "MANUAL PATH: WRONG ANSWER for this pair in isolation"
} else {
    puts "MANUAL PATH: correct"
}

# --- (2) FIXED-mode batch, same pair repeated n times, sampled through the
#         exact same S_PREP/S_ISSUE/S_WAIT_ACK/S_WAIT_RES FSM path that the
#         UNIFORM batch uses (unlike the manual path above), with the
#         hardware's own repeatability mismatch-sticky latch active. -------
puts "DEBUG: starting FIXED batch section"
if {[catch {mwr -force $OP0 $op0_hex} e]} { puts "ERR at OP0 write: $e"; error $e }
puts "DEBUG: OP0 written"
if {[catch {mwr -force $OP1 $op1_hex} e]} { puts "ERR at OP1 write: $e"; error $e }
puts "DEBUG: OP1 written"
if {[catch {mwr -force $NRUNS $n} e]} { puts "ERR at NRUNS write: $e"; error $e }
puts "DEBUG: NRUNS written"
if {[catch {mwr -force $BCTRL 0x0} e]} { puts "ERR at BCTRL clear: $e"; error $e }
puts "DEBUG: BCTRL cleared"
if {[catch {mwr -force $BCTRL [expr {0x1 | (1 << 2)}]} e]} { puts "ERR at BCTRL start: $e"; error $e }
puts "DEBUG: BCTRL start written, polling BSTATUS"
set bs 0
set done 0
for {set i 0} {$i < [expr {200 + $n}]} {incr i} {
    if {[catch {mrd -value $BSTATUS} bs]} { puts "ERR at BSTATUS poll iter $i: $bs"; error $bs }
    if {$bs & 0x2} { set done 1; break }
    after 10
}
puts "DEBUG: poll loop done, done=$done bs=[format 0x%08x $bs]"
if {!$done} { error "FIXED batch TIMEOUT, BSTATUS=[format 0x%08x $bs]" }
set completed [expr {($bs >> 16) & 0xFFFF}]
set got_odata [mrd -value $ODATA]
set got_sig   [mrd -value $SIG]
set mism      [mrd -value $MISM_ST]
set mism_idx  [mrd -value $MISM_IDX]
set mism_val  [mrd -value $MISM_VAL]
set mism_ref  [mrd -value $MISM_REF]
mwr -force $BCTRL 0x0

puts ""
puts "=== FIXED-mode batch: op0=$op0_hex op1=$op1_hex n=$n ==="
puts [format "  completed=%d (want %d)" $completed $n]
puts [format "  ODATA (last run)=%d  expected=%d" $got_odata $exp_res]
puts [format "  MISM_ST=%d MISM_IDX=%d MISM_VAL=%d MISM_REF=%d  (meaningful HERE: FIXED mode, same pair every run)" \
      $mism $mism_idx $mism_val $mism_ref]

set ok 1
if {$completed != $n} { set ok 0 }
if {$got_odata != $exp_res} { puts "  FAIL: last-run ODATA != expected"; set ok 0 }
if {$mism & 1} { puts "  FAIL: MISMATCH_STICKY fired -- kernel returned a DIFFERENT answer across identical-input repeats (idx=$mism_idx val=$mism_val ref=$mism_ref)"; set ok 0 }

puts ""
if {$ok} {
    puts "FIXED-MODE PROBE: PASS -- this exact pair reproduces the correct, repeatable answer $n/$n times through the FSM path"
} else {
    puts "FIXED-MODE PROBE: FAIL -- see above"
    error "fixed-mode probe failed"
}
