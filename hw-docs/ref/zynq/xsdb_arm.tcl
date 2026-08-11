# xsdb driver for the ARM bare-metal bus-speed drive of the knapsack
# AXI harness (zynq/arm/knapsack_drive.c) on the EBAZ4205.
# Usage: xsdb zynq/xsdb_arm.tcl [bitfile] [elffile]
# (Vivado Lab 2026.1 ships xsdb; hw_server at tcp:localhost:3121.)
#
# WHAT THIS VALIDATES: the exact shipped build/knapsack_ps/
# knapsack_ps_top.bit (the plain harness, NOT the bench wrapper) across
# the FULL 8-bit input space (cap 0..255) x REPEATS (default 40 ->
# 10240 transactions), driven by CPU0 itself at bus speed instead of
# ms-scale JTAG pokes. Expected results are compiled into the ELF from
# the golden interpreter (zynq/arm/knapsack_golden.h).
#
# Sequence (connect / cold-catch / memmap / fpga -f / SLCR copied
# VERBATIM from the proven zynq/xsct_knapsack.tcl):
#   - rst -system + tight stop-retry catches CPU0 in BootROM (PC <
#     0x20000) -- this matters doubly here: the ELF is linked at OCM
#     0x20000 (above the BootROM ROM shadow at 0x0..0x1FFFF) and
#     startup.S assumes the early-BootROM machine state (MMU/caches
#     off).
#   - fpga -f <bit>, SLCR bring-up (FCLK0=100 MHz, level shifters, PL
#     reset release).
#   - host-side liveness pre-check on the register map (same as
#     xsct_knapsack.tcl) BEFORE blaming any ARM-side failure on the ARM
#     program. CTRL.rst is left at its power-up 1; the ARM program does
#     its own reset release.
#   - dow <elf> + word-level readback verify (dow alone reports success
#     even if a region silently didn't stick), then con.
#   - poll the mailbox DONE flag. READ STRATEGY: non-intrusive DAP
#     reads through the APU target while CPU0 runs (hw_server routes
#     these via the DAP AHB-AP, no halt). If this xsdb/hw_server combo
#     refuses to read while running, fall back to stop/read/resume on
#     CPU0 -- safe for CORRECTNESS at any time, and safe for TIMING
#     once DONE=1 (the tick delta is captured by the program BEFORE it
#     sets DONE; a halt after that perturbs nothing). Mid-run halts
#     would inflate the A9 global timer delta (it does not pause in
#     debug), so the fallback only reads ~1 s intervals.
#   - print the report: pass/fail, first-8 failure triples, throughput
#     from the global-timer ticks, comparison vs the fabric-FSM
#     baseline (BENCH.md: 24.40 us/call), wall-clock cross-check.
#
# CLOCK MATH (see knapsack_drive.c header): the A9 global timer counts
# at CPU_3x2x = cpu_6x4x / 2 (ratio identical in 6:2:1 and 4:2:2 modes,
# UG585 ch.25). The program records raw SLCR words in the mailbox and
# this script derives, from readback (same policy as xsdb_bench.tcl):
#   cpu_6x4x = PS_CLK(33.33 MHz) x ARM_PLL_CTRL.FDIV[18:12]
#                                / ARM_CLK_CTRL.DIVISOR[13:8]
#   GT_HZ    = cpu_6x4x / 2
# Bench-read reset values on this board (2026-07-21, ARM run 1):
# ARM_PLL_CTRL=0x00028008 = FDIV=40 with only BYPASS_QUAL set (locked,
# PLL_STATUS=0x3f -- same non-bypassed story as the IO PLL, session
# item 18), ARM_CLK_CTRL=0x1f000200 = srcsel=ARM PLL, DIVISOR=2,
# CLK_621_TRUE=1 -> cpu_6x4x = 33.33x40/2 = 666.67 MHz, GT =
# 333.33 MHz. The wall-clock cross-check at the end catches a wrong
# derivation the same way item 18 caught the FCLK0 misread (a 2x-wrong
# GT rate would put the GT-derived sweep time ABOVE the wall time,
# which is impossible).
#
# Mailbox (fixed at OCM 0x0002F000; layout owned by knapsack_drive.c):
#   +0x00 MAGIC 0x4B505331  +0x04 DONE   +0x08 PASS    +0x0C FAIL
#   +0x10 TOTAL             +0x14 TICKS_LO +0x18 TICKS_HI
#   +0x1C ARM_PLL_CTRL      +0x20 ARM_CLK_CTRL  +0x24 CLK_621_TRUE
#   +0x28 PROGRESS          +0x2C ERR ((cap<<8)|step, 0 = none)
#   +0x30 first-8 failures x {cap, got, want}

set bitfile [lindex $argv 0]
if {$bitfile eq ""} { set bitfile "build/knapsack_ps/knapsack_ps_top.bit" }
set elffile [lindex $argv 1]
if {$elffile eq ""} { set elffile "zynq/arm/knapsack_drive.elf" }

set BASE   0x40000000
set CTRL   [expr {$BASE + 0x0}]
set STATUS [expr {$BASE + 0x4}]
set IDATA  [expr {$BASE + 0x8}]

set MB          0x0002F000
set MB_MAGIC    [expr {$MB + 0x00}]
set MB_DONE     [expr {$MB + 0x04}]
set MB_PASS     [expr {$MB + 0x08}]
set MB_FAIL     [expr {$MB + 0x0C}]
set MB_TOTAL    [expr {$MB + 0x10}]
set MB_TICKS_LO [expr {$MB + 0x14}]
set MB_TICKS_HI [expr {$MB + 0x18}]
set MB_ARM_PLL  [expr {$MB + 0x1C}]
set MB_ARM_CLK  [expr {$MB + 0x20}]
set MB_CLK621   [expr {$MB + 0x24}]
set MB_PROGRESS [expr {$MB + 0x28}]
set MB_ERR      [expr {$MB + 0x2C}]
set MB_FAILS    [expr {$MB + 0x30}]
set MAGIC_VAL   0x4B505331

set PS_CLK_HZ 33333333.0
set BASELINE_US_PER_CALL 24.40   ;# fabric-FSM measurement, zynq/BENCH.md

# SLCR registers (UG585)
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

# --- halt CPU0 cold (verbatim from xsct_knapsack.tcl) ------------------
proc catch_cpu0_in_bootrom {} {
    for {set attempt 0} {$attempt < 5} {incr attempt} {
        if {[catch {targets -set -filter {name =~ "APU"}}]} {
            targets -set -filter {name =~ "DAP*"}   ;# wedged-DAP recovery
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

# xsdb blocks PL AXI slave ranges by default; declare the register block.
targets -set -filter {name =~ "APU"}
memmap -addr $BASE -size 0x1000 -flags 3
targets -set -filter {name =~ "ARM*#0"}

# --- program PL -------------------------------------------------------
targets -set -filter {name =~ "xc7z010*"}
puts "programming $bitfile ..."
fpga -f $bitfile
puts "FPGA done."

# --- SLCR: FCLK0 + level shifters + PL reset release ------------------
targets -set -filter {name =~ "ARM*#0"}
mwr -force $SLCR_UNLOCK $SLCR_UNLOCK_KEY
mwr -force $FPGA0_CLK_CTRL 0x00100A00
mwr -force $LVL_SHFTR_EN 0xF
mwr -force $FPGA_RST_CTRL 0x0
mwr -force $SLCR_LOCK $SLCR_LOCK_KEY
puts "SLCR: FCLK0 set (IO PLL 1000/10 = 100 MHz), level shifters on, PL resets released."

# --- host-side liveness pre-check (CPU still halted) -------------------
# Proves bitstream + AXI plumbing before the ARM program is in the
# picture; leaves CTRL.rst=1 (the program releases it itself).
set v [mrd -value $CTRL]
puts "CTRL  after config: [format 0x%08x $v] (expect 0x4: rst=1)"
mwr -force $IDATA 0xA5
set v [mrd -value $IDATA]
if {$v != 0xA5} { error "I_DATA readback FAILED: [format 0x%x $v] != 0xa5 -- AXI plumbing not up" }
mwr -force $IDATA 0x0
set v [mrd -value $STATUS]
puts "STATUS in reset  : [format 0x%08x $v] (expect 0x0)"
puts "host liveness pre-check PASS"

# --- load + verify the ELF ---------------------------------------------
puts "downloading $elffile ..."
dow $elffile
# dow reports success even if a region silently didn't stick (e.g. a
# ROM-shadowed address); verify the vector word and the mailbox magic
# slot are really writable/read-back-able before running.
set v [mrd -value 0x00020000]
if {$v != 0xea000007} {
    error "ELF verify FAILED at 0x20000: [format 0x%08x $v] != 0xea000007 (b reset) -- OCM not writable at the link address?"
}
mwr -force $MB_MAGIC 0
set v [mrd -value $MB_MAGIC]
if {$v != 0} { error "mailbox scrub FAILED at [format 0x%x $::MB_MAGIC]" }
puts "ELF verified at 0x20000; mailbox scrubbed."

# --- run ----------------------------------------------------------------
set t0 [clock milliseconds]
con
puts "CPU0 running (entry 0x20000)."

# --- mailbox polling ----------------------------------------------------
# Preferred: non-intrusive DAP read via the APU target while CPU0 runs.
# Fallback: stop/read/resume on CPU0 (see header for why that is safe
# for the reported numbers once DONE=1).
set read_mode "dap"
proc mb_read {addr} {
    global read_mode
    if {$read_mode eq "dap"} {
        targets -set -filter {name =~ "APU"}
        if {![catch {mrd -value $addr} v]} { return $v }
        puts "NOTE: APU-target read while running failed ($v); falling back to stop/read/resume"
        set read_mode "halt"
    }
    targets -set -filter {name =~ "ARM*#0"}
    set was_running [string match "Running*" [state]]
    if {$was_running} { stop }
    set v [mrd -value $addr]
    if {$was_running} { con }
    return $v
}

set done 0
set t_done 0
for {set i 0} {$i < 120} {incr i} {
    after [expr {$i < 10 ? 200 : 1000}]
    set d [mb_read $MB_DONE]
    if {$d == 1} { set t_done [clock milliseconds]; set done 1; break }
    if {$i % 5 == 4} {
        puts "  waiting... DONE=0 PROGRESS=[mb_read $MB_PROGRESS] MAGIC=[format 0x%08x [mb_read $MB_MAGIC]]"
    }
}
if {!$done} {
    set prog [mb_read $MB_PROGRESS]
    set err  [mb_read $MB_ERR]
    error "TIMEOUT: mailbox DONE never set. PROGRESS=$prog ERR=[format 0x%x $err] (cap=[expr {$err >> 8}] step=[expr {$err & 0xff}])"
}
set wall_s [expr {($t_done - $t0) / 1000.0}]

# --- read the report (CPU halted now: results are final) ----------------
targets -set -filter {name =~ "ARM*#0"}
stop
set magic  [mrd -value $MB_MAGIC]
if {$magic != $MAGIC_VAL} { error "mailbox MAGIC bad: [format 0x%08x $magic]" }
set pass   [mrd -value $MB_PASS]
set fail   [mrd -value $MB_FAIL]
set total  [mrd -value $MB_TOTAL]
set tlo    [mrd -value $MB_TICKS_LO]
set thi    [mrd -value $MB_TICKS_HI]
set apll   [mrd -value $MB_ARM_PLL]
set aclk   [mrd -value $MB_ARM_CLK]
set c621   [mrd -value $MB_CLK621]
set errw   [mrd -value $MB_ERR]
set ticks  [expr {($thi << 32) | ($tlo & 0xffffffff)}]

# --- clock math (see header) --------------------------------------------
set fdiv    [expr {($apll >> 12) & 0x7f}]
set bypassf [expr {($apll >> 4) & 1}]
set divisor [expr {($aclk >> 8) & 0x3f}]
set srcsel  [expr {($aclk >> 4) & 0x3}]
if {$divisor == 0} { set divisor 1 }
set cpu6x [expr {($bypassf ? $PS_CLK_HZ : $PS_CLK_HZ * $fdiv) / $divisor}]
set gt_hz [expr {$cpu6x / 2.0}]
puts ""
puts [format "clock math: ARM_PLL_CTRL=0x%08x (FDIV=%d bypass_force=%d) ARM_CLK_CTRL=0x%08x (DIVISOR=%d srcsel=%d) CLK_621_TRUE=0x%x" \
      $apll $fdiv $bypassf $aclk $divisor $srcsel $c621]
if {$srcsel >= 2} { puts "WARNING: cpu clock source is not the ARM PLL (srcsel=$srcsel); GT rate derivation is wrong" }
puts [format "  cpu_6x4x = %.2f MHz -> global timer (CPU_3x2x) = %.2f MHz" \
      [expr {$cpu6x / 1e6}] [expr {$gt_hz / 1e6}]]

# --- report --------------------------------------------------------------
set sweep_s [expr {$ticks / $gt_hz}]
set us_per  [expr {$sweep_s * 1e6 / $total}]
set tps     [expr {$total / $sweep_s}]
puts ""
puts "=== ARM bare-metal exhaustive sweep report ==="
puts [format "  transactions : %d (256 caps x %d repeats)" $total [expr {$total / 256}]]
puts [format "  PASS         : %d" $pass]
puts [format "  FAIL         : %d" $fail]
if {$errw != 0} {
    puts [format "  first timeout: cap=%d at protocol step %d" [expr {$errw >> 8}] [expr {$errw & 0xff}]]
}
if {$fail > 0} {
    set n [expr {$fail < 8 ? $fail : 8}]
    for {set i 0} {$i < $n} {incr i} {
        set a [expr {$::MB_FAILS + 12 * $i}]
        set fc [mrd -value $a]
        set fg [mrd -value [expr {$a + 4}]]
        set fw [mrd -value [expr {$a + 8}]]
        puts [format "  fail\[%d\]: cap=%d got=%d (0x%x) want=%d" $i $fc $fg $fg $fw]
    }
}
puts [format "  GT ticks     : %s (%.6f s at %.2f MHz)" $ticks $sweep_s [expr {$gt_hz / 1e6}]]
puts [format "  throughput   : %.2f us/call = %.0f calls/s" $us_per $tps]
puts [format "  vs fabric-FSM baseline %.2f us/call (BENCH.md): %+.1f%% per-call overhead" \
      $BASELINE_US_PER_CALL [expr {100.0 * ($us_per - $BASELINE_US_PER_CALL) / $BASELINE_US_PER_CALL}]]
puts [format "  wall clock   : %.2f s con->done-observed (includes %s-poll latency; sanity only)" \
      $wall_s $read_mode]
if {$wall_s > 0} {
    puts [format "  GT-vs-wall   : sweep %.3f s by GT, %.2f s by wall -- ratio %.2f (expect <1: wall includes poll granularity)" \
          $sweep_s $wall_s [expr {$sweep_s / $wall_s}]]
}
puts [format "=== %s: %d/%d PASS ===" [expr {$fail == 0 ? "GREEN" : "RED"}] $pass $total]
if {$fail > 0} { exit 1 }
exit 0
