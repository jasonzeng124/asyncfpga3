# xsdb driver for the knapsack_ps AXI milestone on the EBAZ4205.
# Usage: xsdb zynq/xsct_knapsack.tcl [bitfile]
# (Vivado Lab 2026.1 ships xsdb; hw_server at tcp:localhost:3121.)
#
# Sequence per zynq/BRINGUP.md milestone 3 + the bench findings
# (2026-07-21, BRINGUP_SESSION.md items 16-17):
#   - connect (recovering the DAP if a previous hung AXI access left it
#     in "APB AP transaction error" -- rst -system from the DAP clears it)
#   - rst -system, then catch CPU0 EARLY with a tight stop-retry loop:
#     a fixed post-reset delay is a race against the NAND boot chain (a
#     500 ms delay was observed to land at PC 0x0ff75a70 -- booted image
#     in DDR, MMU state unknown). The catch is verified to be in BootROM
#     (PC ~0x608c) and retried from another rst -system if late.
#     rst -system also returns SLCR to reset defaults and clears the PL,
#     so fpga -f comes after.
#   - program PL via fpga -f
#   - SLCR: set FCLK0, enable level shifters, release PL resets.
#     Bench-verified clock facts after rst -system (PLL_STATUS=0x3f):
#     all three PLLs are LOCKED at their reset FDIV; IO_PLL_CTRL=0x1e008
#     has only BYPASS_QUAL set (NOT BYPASS_FORCE -- misread in the first
#     bench pass, corrected by wall-clock calibration, see
#     BRINGUP_SESSION.md item 18), so the IO PLL output is live at
#     PS_CLK*FDIV(30) = 1000 MHz. FCLK0 = 1000/DIVISOR0 with no PLL
#     programming needed. divisor0=10 -> 100 MHz: the core is
#     clockless, FCLK0 only paces the AXI slave FSM between ms-spaced
#     JTAG pokes.
#   - liveness pre-check on the register map (write/readback I_DATA,
#     sanity-read CTRL/STATUS) before trusting any poll
#   - full 4-phase poke sequence for the 11 golden caps
#
# HISTORY: the first bench attempt hung every access to 0x40000000
# ("Timeout waiting for the Instruction Complete bit", DAP left in APB
# AP transaction error). Root cause was NOT the clock (see above) but
# the harness RTL: the register slave answered with constant BID/RID=0
# while M_AXI_GP0 is a full AXI3 port whose interconnect routes
# responses by ID. Fixed in zynq/knapsack_ps_top.v (bridge echoes
# AWID/ARID); this script requires the rebuilt bitstream.
#
# Register map (M_AXI_GP0 base 0x40000000, see zynq/knapsack_ps_top.v):
#   0x00 CTRL   [0]=i_req [1]=o_ack [2]=rst   (rst powers up at 1)
#   0x04 STATUS [0]=i_ack(sticky) [1]=o_req
#   0x08 I_DATA cap
#   0x0C O_DATA result
# STATUS.i_ack is the sticky "request accepted" flag: it stays 1 until
# CTRL.i_req is cleared (pulse adapter, see BRINGUP.md) -- do NOT wait
# for it to fall on its own.

set bitfile [lindex $argv 0]
if {$bitfile eq ""} { set bitfile "build/knapsack_ps/knapsack_ps_top.bit" }

set BASE   0x40000000
set CTRL   [expr {$BASE + 0x0}]
set STATUS [expr {$BASE + 0x4}]
set IDATA  [expr {$BASE + 0x8}]
set ODATA  [expr {$BASE + 0xC}]

# SLCR registers (UG585)
set SLCR_UNLOCK     0xF8000008
set SLCR_LOCK       0xF8000004
set SLCR_UNLOCK_KEY 0xDF0D
set SLCR_LOCK_KEY   0x767B
set FPGA0_CLK_CTRL  0xF8000170
set LVL_SHFTR_EN    0xF8000900
set FPGA_RST_CTRL   0xF8000240

set caps    {0 1 3 5 10 15 17 20 25 28 31}
set golden  {0 2 5 8 15 23 26 29 34 38 41}

proc poll_status {mask want tag} {
    # ~ms per iteration over JTAG; the core finishes in us -- generous.
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
# running (bench finding, 2026-07-21). `rst -system` + an IMMEDIATE
# tight stop-retry loop catches the core in BootROM (PC ~0x608c) before
# the boot chain touches anything: kills the armed-watchdog risk and
# the MMU phys/virt ambiguity at once (a fixed 500 ms delay lost that
# race once -- caught PC 0x0ff75a70, booted image). Verified by PC:
# BootROM executes below 0x20000; anything higher means the catch was
# late and we reset again. NOTE: -system resets the PL too, so this
# MUST precede fpga -f. It is also the recovery path when a previous
# hung AXI access left the DAP in "APB AP transaction error": in that
# state only the DAP target is visible, and rst -system issued on it
# restores the APU target (bench-verified).
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

# xsdb blocks PL AXI slave ranges by default ("Blocked address ...
# has not been added to the memory map"); declare the register block.
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
# FCLK0: srcsel=IO PLL (00), divisor1=1, divisor0=10. After rst -system
# the IO PLL is locked and LIVE (PLL_STATUS=0x3f; IO_PLL_CTRL=0x1e008 is
# BYPASS_QUAL only, not BYPASS_FORCE) at PS_CLK*30 = 1000 MHz, so
# FCLK0 = 100 MHz (wall-clock verified 97.9-99.2 MHz, session item 18).
# Exact rate is uncritical here: the core is clockless; FCLK0 only
# paces the AXI slave FSM between pokes.
# Bench-verified working at this setting; no PLL programming needed.
mwr -force $FPGA0_CLK_CTRL 0x00100A00
mwr -force $LVL_SHFTR_EN 0xF
mwr -force $FPGA_RST_CTRL 0x0
mwr -force $SLCR_LOCK $SLCR_LOCK_KEY
puts "SLCR: FCLK0 set (IO PLL 1000/10 = 100 MHz), level shifters on, PL resets released."

# --- liveness pre-check ----------------------------------------------
# CTRL powers up 0x4 (rst=1). Readback proves AXI write+read plumbing.
set v [mrd -value $CTRL]
puts "CTRL  after config: [format 0x%08x $v] (expect 0x4: rst=1)"
mwr -force $IDATA 0xA5
set v [mrd -value $IDATA]
if {$v != 0xA5} { error "I_DATA readback FAILED: [format 0x%x $v] != 0xa5 -- AXI plumbing not up" }
mwr -force $IDATA 0x0
set v [mrd -value $STATUS]
puts "STATUS in reset  : [format 0x%08x $v] (expect 0x0)"
puts "liveness pre-check PASS"

# --- release core reset ----------------------------------------------
mwr -force $CTRL 0x0
after 100

# --- golden vectors ---------------------------------------------------
set pass 0
set fail 0
foreach cap $caps want $golden {
    # data valid before req rise (bundled-data; separate writes)
    mwr -force $IDATA $cap
    mwr -force $CTRL 0x1                    ;# i_req=1
    poll_status 0x1 0x1 "i_ack rise (cap=$cap)"
    mwr -force $CTRL 0x0                    ;# drop i_req (RTZ)
    poll_status 0x1 0x0 "i_ack fall (cap=$cap)"
    poll_status 0x2 0x2 "o_req rise (cap=$cap)"
    set got [expr {[mrd -value $ODATA] & 0xFFFF}]
    mwr -force $CTRL 0x2                    ;# o_ack=1
    poll_status 0x2 0x0 "o_req fall (cap=$cap)"
    mwr -force $CTRL 0x0                    ;# drop o_ack (RTZ complete)
    if {$got == $want} {
        puts "PASS cap=$cap -> $got"
        incr pass
    } else {
        puts "FAIL cap=$cap -> $got (want $want)"
        incr fail
    }
}
puts "=== $pass/[llength $caps] golden vectors PASS, $fail FAIL ==="
if {$fail > 0} { exit 1 }
exit 0
