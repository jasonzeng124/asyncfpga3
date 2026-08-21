# xsdb driver for mem_bist_ps (B1): does openXC7 encode a RAMB18E1 correctly
# at all?  Ordinary synchronous RAM, CLKARDCLK tied straight to aclk, no
# strobe generation, no bd_mem.  Ported near-verbatim from
# cells/hw/xsdb_gcd.tcl (connect/catch_cpu0_in_bootrom/memmap-before-fpga
# sequence, board-proven on this exact board) -- see that file's header for
# the full bench-history rationale behind each piece.
#
# Usage: xsdb cells/hw/xsdb_mem_bist.tcl [bitfile]
#
# Register map (M_AXI_GP0 base 0x40000000, see hw/mem_bist_ps.v):
#   0x00 CTRL        RW [0]=rst (powers up 1; clearing it starts one run)
#   0x04 STATUS      RO [0]=busy [1]=done [2]=pass
#   0x08 RESULT      RO total mismatch count
#   0x0C FAIL_ADDR   RO word address of first mismatch
#   0x10 FAIL_GOT    RO data read back at first mismatch
#   0x14 FAIL_EXPECT RO data that should have been there
#   0x18 FAIL_TAG    RO [1:0]=pattern [8:4]=bit index k
#   0x1C PROGRESS    RO [1:0]=pattern [8:4]=k [25:16]=addr
#
# The whole walking-1/walking-0/addr=data sweep (1024 addr x 16 bits x 3
# patterns) runs entirely in fabric at 100 MHz -- microseconds, not the
# hours a host-paced JTAG loop would take -- so ONE poll for STATUS.done
# is sufficient; there is nothing to stream per-vector.

set bitfile [lindex $argv 0]
if {$bitfile eq ""} { set bitfile "build/hw_mem/mem_bist_ps/default/mem_bist_ps.bit" }

set BASE       0x40000000
set CTRL       [expr {$BASE + 0x00}]
set STATUS     [expr {$BASE + 0x04}]
set RESULT     [expr {$BASE + 0x08}]
set FAIL_ADDR  [expr {$BASE + 0x0C}]
set FAIL_GOT   [expr {$BASE + 0x10}]
set FAIL_EXPECT [expr {$BASE + 0x14}]
set FAIL_TAG   [expr {$BASE + 0x18}]
set PROGRESS   [expr {$BASE + 0x1C}]

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

# memmap on APU, BEFORE fpga -f (hw-docs/02 section 5 / 07-gotchas).
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

# --- liveness pre-check --------------------------------------------------
set v [mrd -value $CTRL]
puts "CTRL after config: [format 0x%08x $v] (expect 0x1: rst=1)"
if {$v != 0x1} { error "CTRL readback FAILED: [format 0x%x $v] != 0x1 -- AXI plumbing not up" }
puts "liveness pre-check PASS"

# --- run the BIST ---------------------------------------------------------
mwr -force $CTRL 0x0
puts "CTRL.rst cleared -- BIST running (walking-1, walking-0, addr=data over 1024x16)"

if {[catch {poll_status 0x2 0x2 "STATUS.done"} s]} {
    puts "=== B1 RESULT: TIMEOUT -- $s ==="
    set prog [mrd -value $PROGRESS]
    puts "last PROGRESS: [format 0x%08x $prog] (pat=[expr {$prog & 0x3}] k=[expr {($prog>>4)&0x1f}] addr=[expr {($prog>>16)&0x3ff}])"
    exit 1
}

set pass_bit [expr {($s >> 2) & 0x1}]
set mismatches [mrd -value $RESULT]

puts "STATUS: [format 0x%08x $s]  pass=$pass_bit  mismatches=$mismatches"

if {$pass_bit == 1 && $mismatches == 0} {
    puts "=== B1 RESULT: PASS -- RAMB18E1 encodes correctly, all 1024 addr x 16 bits x 3 patterns match ==="
    exit 0
} else {
    set fa   [mrd -value $FAIL_ADDR]
    set fg   [mrd -value $FAIL_GOT]
    set fe   [mrd -value $FAIL_EXPECT]
    set ft   [mrd -value $FAIL_TAG]
    set fpat [expr {$ft & 0x3}]
    set fk   [expr {($ft >> 4) & 0x1f}]
    puts "=== B1 RESULT: FAIL -- $mismatches mismatch(es) ==="
    puts "first mismatch: pattern=$fpat (0=walk1 1=walk0 2=addr=data) bit=$fk addr=[format 0x%03x $fa] got=[format 0x%04x $fg] expect=[format 0x%04x $fe]"
    exit 1
}
