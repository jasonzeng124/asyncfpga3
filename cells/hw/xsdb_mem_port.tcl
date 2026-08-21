# xsdb driver for mem_port_ps (B2/B3): bd_mem itself, through its own
# manufactured strobe, driven only via req/addr/wdata/we/ack.  Ported
# near-verbatim from cells/hw/xsdb_gcd.tcl / xsdb_mem_bist.tcl -- same
# connect/catch_cpu0_in_bootrom/memmap-before-fpga sequence.
#
# Usage: xsdb cells/hw/xsdb_mem_port.tcl <bitfile> [label]
#
# One run does BOTH things at once (see hw/mem_port_ps.v's header):
#   CORRECTNESS -- walking-1/walking-0/addr=data through bd_mem's real
#                  four-phase handshake.
#   COST        -- SPD_N back-to-back read round trips at a fixed address,
#                  timed by a free-running aclk (100 MHz) cycle counter.
# `label` is printed in the result line only, so multiple builds (bufg1,
# bufg0, bufg0_derived, ...) can be told apart in a shared log without
# re-deriving anything from the bitfile name.
#
# Register map (M_AXI_GP0 base 0x40000000, see hw/mem_port_ps.v):
#   0x00 CTRL   RW [0]=rst
#   0x04 STATUS RO [0]=ack_s [1]=busy [2]=done [3]=pass
#   0x08 RESULT     mismatch count
#   0x0C FAIL_ADDR
#   0x10 FAIL_GOT
#   0x14 FAIL_EXPECT
#   0x18 FAIL_TAG   [1:0]=pattern [8:4]=k
#   0x1C PROGRESS
#   0x20 SPD_CYCLES aclk cycles elapsed over the SPD_N timed reads
#   0x24 SPD_N      constant, read back for self-check

set bitfile [lindex $argv 0]
if {$bitfile eq ""} { set bitfile "build/hw_mem/mem_port_ps/bufg1/mem_port_ps.bit" }
set label [lindex $argv 1]
if {$label eq ""} { set label $bitfile }

set BASE        0x40000000
set CTRL        [expr {$BASE + 0x00}]
set STATUS      [expr {$BASE + 0x04}]
set RESULT      [expr {$BASE + 0x08}]
set FAIL_ADDR   [expr {$BASE + 0x0C}]
set FAIL_GOT    [expr {$BASE + 0x10}]
set FAIL_EXPECT [expr {$BASE + 0x14}]
set FAIL_TAG    [expr {$BASE + 0x18}]
set PROGRESS    [expr {$BASE + 0x1C}]
set SPD_CYCLES  [expr {$BASE + 0x20}]
set SPD_NREG    [expr {$BASE + 0x24}]

set SLCR_UNLOCK     0xF8000008
set SLCR_LOCK       0xF8000004
set SLCR_UNLOCK_KEY 0xDF0D
set SLCR_LOCK_KEY   0x767B
set FPGA0_CLK_CTRL  0xF8000170
set LVL_SHFTR_EN    0xF8000900
set FPGA_RST_CTRL   0xF8000240

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
        puts "attempt $attempt: caught too late (pc $pc), retrying"
    }
    error "could not catch CPU0 in BootROM after 5 resets"
}

proc poll_status {mask want tag} {
    for {set i 0} {$i < 400} {incr i} {
        set s [mrd -value $::STATUS]
        if {([expr {$s & $mask}]) == $want} { return $s }
        after 50
    }
    error "TIMEOUT waiting for STATUS&[format 0x%x $mask]==[format 0x%x $want] ($tag); last STATUS=[format 0x%x $s]"
}

connect -url tcp:localhost:3121
puts "targets:"
puts [targets]

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
puts "SLCR: FCLK0 = 100 MHz, level shifters on, PL resets released."

set v [mrd -value $CTRL]
puts "CTRL after config: [format 0x%08x $v] (expect 0x1: rst=1)"
if {$v != 0x1} { error "CTRL readback FAILED: [format 0x%x $v] != 0x1 -- AXI plumbing not up" }
puts "liveness pre-check PASS"

mwr -force $CTRL 0x0
puts "CTRL.rst cleared -- correctness walk + SPD_N timed reads running ($label)"

if {[catch {poll_status 0x4 0x4 "STATUS.done"} s]} {
    puts "=== $label RESULT: TIMEOUT -- $s ==="
    set prog [mrd -value $PROGRESS]
    puts "last PROGRESS: [format 0x%08x $prog]"
    exit 1
}

set pass_bit  [expr {($s >> 3) & 0x1}]
set mismatches [mrd -value $RESULT]
set spd_cycles [mrd -value $SPD_CYCLES]
set spd_n      [mrd -value $SPD_NREG]

puts "STATUS: [format 0x%08x $s]  pass=$pass_bit  mismatches=$mismatches"
puts "SPD_CYCLES=$spd_cycles  SPD_N=$spd_n"

if {$spd_n > 0} {
    set ns_per_access [expr {double($spd_cycles) * 10.0 / double($spd_n)}]
    puts [format "per-access latency: %.1f ns (aclk=100MHz, %d cycles / %d reads)" \
          $ns_per_access $spd_cycles $spd_n]
}

if {$pass_bit == 1 && $mismatches == 0} {
    puts "=== $label RESULT: PASS -- bd_mem correct over 1024 addr x 16 bits x 3 patterns ==="
    set rc 0
} else {
    set fa   [mrd -value $FAIL_ADDR]
    set fg   [mrd -value $FAIL_GOT]
    set fe   [mrd -value $FAIL_EXPECT]
    set ft   [mrd -value $FAIL_TAG]
    set fpat [expr {$ft & 0x3}]
    set fk   [expr {($ft >> 4) & 0x1f}]
    puts "=== $label RESULT: FAIL -- $mismatches mismatch(es) ==="
    puts "first mismatch: pattern=$fpat (0=walk1 1=walk0 2=addr=data) bit=$fk addr=[format 0x%03x $fa] got=[format 0x%04x $fg] expect=[format 0x%04x $fe]"
    set rc 1
}
exit $rc
