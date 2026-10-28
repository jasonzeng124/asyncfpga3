# xsdb driver for gcd_ps_top's AXI3 milestone on the EBAZ4205.
# Usage: xsdb cells/hw/xsdb_gcd.tcl [bitfile]
# (Vivado Lab 2026.1 ships xsdb; hw_server at tcp:localhost:3121.)
#
# Ported near-verbatim from hw-docs/ref/zynq/xsct_knapsack.tcl (the script
# that silicon-validated knapsack/gcd on this exact board) -- same PS7/SLCR
# bring-up sequence, same catch_cpu0_in_bootrom proc. Two differences from
# that harness's register map:
#   - two input registers (A_DATA, B_DATA) instead of one I_DATA -- gcd
#     is a binary op, so both operands must be latched before i_req rises.
#   - O_DATA is the full 32-bit result (like xsct_fib.tcl's Wout=32), NOT
#     truncated to 16 bits like knapsack's O_DATA.
# The host 4-phase sequence here also has only 3 polls (i_ack rise, o_req
# rise, o_req fall) per hw-docs/02-zynq-ebaz4205.md section 5's summary --
# unlike xsct_fib.tcl/xsct_knapsack.tcl, which additionally poll for
# i_ack to fall. STATUS.i_ack is sticky (holds at 1 once accepted; only
# CTRL.rst clears it), so there is nothing to wait for there.
#
# Sequence (see xsct_knapsack.tcl header for the full bench-history
# rationale behind each piece):
#   - connect, rst -system + catch CPU0 in BootROM (a fixed delay races
#     the NAND boot chain -- use the tight stop-retry loop, verify
#     PC < 0x20000)
#   - program PL via fpga -f
#   - SLCR: FCLK0 + level shifters + PL reset release (section 4, exact)
#   - memmap the AXI3 register block before any mrd/mwr (section 5)
#   - release the kernel from reset (CTRL.rst=0)
#   - full 4-phase poke sequence for the golden gcd(a,b) vectors, wrapped
#     in gcd_once so a hardware run can only report a real answer or a
#     named timeout -- never hang silently on a missing response, which
#     is this kernel's known failure mode (see MEMORY.md
#     nextpnr-lut-pinmap-bitstream-bug.md: the bug was a MISSING answer,
#     not a wrong one).
#
# Register map (M_AXI_GP0 base 0x40000000, see gcd_ps_top.v):
#   0x00 CTRL   [0]=i_req [1]=o_ack [2]=rst   (rst powers up at 1)
#   0x04 STATUS [0]=i_ack(sticky) [1]=o_req
#   0x08 A_DATA gcd's a : i32 (RW, readback echoes)
#   0x0C B_DATA gcd's b : i32 (RW, readback echoes)
#   0x10 O_DATA gcd's result : i32 (RO)

set bitfile [lindex $argv 0]
if {$bitfile eq ""} { set bitfile "build/hw/gcd_ps/gcd_ps.bit" }

set BASE   0x40000000
set CTRL   [expr {$BASE + 0x0}]
set STATUS [expr {$BASE + 0x4}]
set ADATA  [expr {$BASE + 0x8}]
set BDATA  [expr {$BASE + 0xC}]
set ODATA  [expr {$BASE + 0x10}]

# SLCR registers (UG585)
set SLCR_UNLOCK     0xF8000008
set SLCR_LOCK       0xF8000004
set SLCR_UNLOCK_KEY 0xDF0D
set SLCR_LOCK_KEY   0x767B
set FPGA0_CLK_CTRL  0xF8000170
set LVL_SHFTR_EN    0xF8000900
set FPGA_RST_CTRL   0xF8000240

# Golden vectors: (a, b, expected gcd(a,b)).
set vectors {
    {0      5        5}
    {7      0        7}
    {12     18       6}
    {48     18       6}
    {1      1        1}
    {17     5        1}
    {32     313524384 32}
    {21     462      21}
    {6      192      6}
    {4096   4096     4096}
    {99991  99991    99991}
    {12     788500   4}
    {1      2        1}
    {1      1000001  1}
    {12     60       12}
    {256    768      256}
}

proc poll_status {mask want tag} {
    # ~ms per iteration over JTAG; the core finishes in us -- generous.
    # Bounded so a MISSING answer (this kernel's known failure mode, see
    # MEMORY.md) shows up as a named timeout instead of an infinite hang.
    for {set i 0} {$i < 200} {incr i} {
        set s [mrd -value $::STATUS]
        if {([expr {$s & $mask}]) == $want} { return $s }
    }
    error "TIMEOUT waiting for STATUS&[format 0x%x $mask]==[format 0x%x $want] ($tag); last STATUS=[format 0x%x $s]"
}

connect -url tcp:localhost:3121
puts "targets:"
puts [targets]

# --- halt CPU0 cold ---------------------------------------------------
# Plain `stop` times out against whatever the stock NAND image leaves
# running. `rst -system` + an IMMEDIATE tight stop-retry loop catches the
# core in BootROM (PC ~0x608c) before the boot chain touches anything.
# Verified by PC: BootROM executes below 0x20000; anything higher means
# the catch was late and we reset again. NOTE: -system resets the PL
# too, so this MUST precede fpga -f. It is also the recovery path when a
# previous hung AXI access left the DAP in "APB AP transaction error":
# in that state only the DAP target is visible, and rst -system issued
# on it restores the APU target (bench-verified, xsct_knapsack.tcl).
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

# --- program PL -------------------------------------------------------
# Declare the AXI3 register block BEFORE programming, and on the APU rather
# than on a single A9.  Both matter, and getting either wrong gives the same
# message: "Blocked address 0x40000000 ... has not been added to the memory
# map" (hw-docs/02 section 8).  memmap attaches to the context it is issued
# against; the A9 cores inherit the APU's, so declaring it on APU covers both
# and survives the target switches below.  Declared after fpga -f it does not
# take -- which is exactly how this script failed the first time it ran.
targets -set -filter {name =~ "APU"}
memmap -addr $BASE -size 0x1000 -flags 3
targets -set -filter {name =~ "ARM*#0"}

targets -set -filter {name =~ "xc7z010*"}
puts "programming $bitfile ..."
fpga -f $bitfile
puts "FPGA done."

# --- SLCR: FCLK0 + level shifters + PL reset release ------------------
targets -set -filter {name =~ "ARM*#0"}
mwr -force $SLCR_UNLOCK $SLCR_UNLOCK_KEY     ;# SLCR unlock
mwr -force $FPGA0_CLK_CTRL 0x00100A00        ;# FCLK0 = IO PLL/10 = 100 MHz
mwr -force $LVL_SHFTR_EN 0xF                 ;# enable PL<->PS level shifters
mwr -force $FPGA_RST_CTRL 0x0                ;# release PL resets
mwr -force $SLCR_LOCK $SLCR_LOCK_KEY         ;# SLCR lock
puts "SLCR: FCLK0 set (IO PLL 1000/10 = 100 MHz), level shifters on, PL resets released."

# xsdb blocks PL AXI slave ranges by default ("Blocked address ... has
# not been added to the memory map"); declare the register block. Must
# come before any mrd/mwr against $BASE.
# (memmap is declared on APU before fpga -f -- see above.)

# --- liveness pre-check ------------------------------------------------
# CTRL powers up 0x4 (rst=1). A_DATA readback proves AXI write+read
# plumbing before any poll is trusted -- see hw-docs section 5.
set v [mrd -value $CTRL]
puts "CTRL  after config: [format 0x%08x $v] (expect 0x4: rst=1)"
mwr -force $ADATA 0xA5A5A5A5
set v [mrd -value $ADATA]
if {$v != 0xA5A5A5A5} { error "A_DATA readback FAILED: [format 0x%x $v] != 0xa5a5a5a5 -- AXI plumbing not up" }
mwr -force $ADATA 0x0
set v [mrd -value $STATUS]
puts "STATUS in reset  : [format 0x%08x $v] (expect 0x0)"
puts "liveness pre-check PASS"

# --- release kernel from reset -----------------------------------------
mwr -force $CTRL 0x0
after 100

# --- one gcd transaction -----------------------------------------------
# The 4-phase sequence returns CTRL to 0 (RTZ) at every step because the
# harness is a pulse adapter, not a level-sensitive core: holding i_req
# even ~1us past i_ack rise wedges the core permanently, and o_ack must
# drop again once o_req has fallen or the next transaction's o_req never
# rises. Each poll is bounded (poll_status, 200 iters) and names exactly
# which handshake edge it was waiting for, so a hang shows up as a
# labeled TIMEOUT (i_ack rise / o_req rise / o_req fall) instead of an
# infinite wait -- this kernel's known failure mode is a MISSING answer.
proc gcd_once {a b} {
    # data valid before req rise (bundled-data; separate writes)
    mwr -force $::ADATA $a
    mwr -force $::BDATA $b
    mwr -force $::CTRL 0x1                  ;# i_req=1
    poll_status 0x1 0x1 "i_ack rise (a=$a b=$b)"
    mwr -force $::CTRL 0x0                  ;# drop i_req (RTZ)
    poll_status 0x2 0x2 "o_req rise (a=$a b=$b)"
    set got [expr {[mrd -value $::ODATA] & 0xFFFFFFFF}]
    mwr -force $::CTRL 0x2                  ;# o_ack=1
    poll_status 0x2 0x0 "o_req fall (a=$a b=$b)"
    mwr -force $::CTRL 0x0                  ;# drop o_ack (RTZ complete)
    return $got
}

# --- golden vectors ------------------------------------------------------
set pass 0
set fail 0
set n 0
foreach v $vectors {
    incr n
    lassign $v a b want
    if {[catch {gcd_once $a $b} got]} {
        puts "vector $n: gcd($a,$b) = TIMEOUT ($got) (expected $want) MISMATCH"
        incr fail
        continue
    }
    if {$got == $want} {
        puts "vector $n: gcd($a,$b) = $got (expected $want) OK"
        incr pass
    } else {
        puts "vector $n: gcd($a,$b) = $got (expected $want) MISMATCH"
        incr fail
    }
}
puts "=== PASS $pass/[llength $vectors] ==="
if {$fail > 0} {
    puts "=== FAIL: $fail/[llength $vectors] vectors did not match ==="
    exit 1
}
exit 0
