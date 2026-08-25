# xsdb driver for mem_arb_ps: the ARBITRATED bundled-data memory port, driven
# through a program-order token exactly the way tb_bdc_memseq.v's
# `BDC_SEQ_TOKEN mode drives it.  Ported near-verbatim from
# cells/hw/xsdb_mem_port.tcl -- same connect/catch_cpu0_in_bootrom/memmap-
# before-fpga sequence, same poll-then-read-results shape.  Only the register
# map and the verdict text differ, because the design under test differs (two
# `:seq` stations sharing one arbitrated port, not one bare bd_mem).
#
# Usage: xsdb cells/hw/xsdb_mem_arb.tcl <bitfile> [label]
#
# Three phases run inside the FPGA fabric before this script ever polls
# STATUS (see hw/mem_arb_ps.v's header for why each one exists):
#   PHASE 1 -- program order: N store/load pairs, one token apiece, load
#              reads the address its own store just wrote.
#   PHASE 2 -- the RAM actually holds it: a SECOND, independent pass that
#              re-stores and re-reads all N addresses, because bd_mem's
#              WRITE_MODE_A("WRITE_FIRST") lets a same-generation read pass
#              phase 1 without ever performing a real read.
#   PHASE 3 -- cost: SPD_N back-to-back store/load pairs at a fixed address,
#              timed by a free-running aclk (100 MHz) cycle counter.
#
# `label` is printed in the result line only, so multiple builds can be told
# apart in a shared log without re-deriving anything from the bitfile name.
#
# Register map (M_AXI_GP0 base 0x40000000, see hw/mem_arb_ps.v):
#   0x00 CTRL         RW [0]=rst
#   0x04 STATUS       RO [0]=busy [1]=done [2]=timeout_flag [3]=overall_pass
#                         [5:4]=phase (0=phase1 1=phase2 2=phase3/SPD)
#   0x08 P1_MISMATCH      phase 1 mismatch count
#   0x0C P2_MISMATCH      phase 2 mismatch count
#   0x10 TIMEOUT_CODE     0=none 1=WAIT_LZ 2=WAIT_TOK 3=RTZ -- which wait
#                         state the hang detector caught, if any
#   0x14 SPD_CYCLES       aclk cycles elapsed over the SPD_N timed phase
#   0x18 SPD_N            constant, read back for self-check
#   0x1C N_REG            constant N (addresses covered by phase 1/2), ditto
#   0x20 P1_FAIL_ADDR
#   0x24 P1_FAIL_GOT
#   0x28 P1_FAIL_EXPECT
#   0x2C P2_FAIL_ADDR
#   0x30 P2_FAIL_GOT
#   0x34 P2_FAIL_EXPECT
#   0x38 PROGRESS         {phase[1:0], st[2:0], idx[9:0]} -- idx reads 0 once
#                         phase 3 starts; see SPD_ITER (0x3C) for that phase
#   0x3C SPD_ITER         phase 3's own iteration counter (idx is too narrow
#                         to count SPD_N when SPD_N > 1024)

set bitfile [lindex $argv 0]
if {$bitfile eq ""} { set bitfile "build/hw_mem/mem_arb_ps/default/mem_arb_ps.bit" }
set label [lindex $argv 1]
if {$label eq ""} { set label $bitfile }

set BASE          0x40000000
set CTRL          [expr {$BASE + 0x00}]
set STATUS        [expr {$BASE + 0x04}]
set P1_MISMATCH   [expr {$BASE + 0x08}]
set P2_MISMATCH   [expr {$BASE + 0x0C}]
set TIMEOUT_CODE  [expr {$BASE + 0x10}]
set SPD_CYCLES    [expr {$BASE + 0x14}]
set SPD_NREG      [expr {$BASE + 0x18}]
set N_REG         [expr {$BASE + 0x1C}]
set P1_FAIL_ADDR  [expr {$BASE + 0x20}]
set P1_FAIL_GOT   [expr {$BASE + 0x24}]
set P1_FAIL_EXP   [expr {$BASE + 0x28}]
set P2_FAIL_ADDR  [expr {$BASE + 0x2C}]
set P2_FAIL_GOT   [expr {$BASE + 0x30}]
set P2_FAIL_EXP   [expr {$BASE + 0x34}]
set PROGRESS      [expr {$BASE + 0x38}]
set SPD_ITER      [expr {$BASE + 0x3C}]

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
puts "CTRL.rst cleared -- phase 1/2/3 running ($label)"

# STATUS bit 1 is `done`, which this design reaches either by finishing all
# three phases or by the hang detector firing -- either way the poll below
# returns and the register dump distinguishes which one happened.  A poller
# TIMEOUT here (as opposed to a STATUS.timeout_flag=1) means the fabric never
# even reached S_DONE, i.e. the on-chip hang detector's own bound
# (TIMEOUT_LIMIT, ~20 ms of aclk) was itself insufficient -- that would be
# its own finding, not just a slow run, and is reported distinctly below.
if {[catch {poll_status 0x2 0x2 "STATUS.done"} s]} {
    puts "=== $label RESULT: POLLER TIMEOUT -- $s ==="
    puts "    (STATUS never reached done=1; the on-chip hang detector's own"
    puts "    bound did not save this run -- see hw/mem_arb_ps.v's"
    puts "    TIMEOUT_LIMIT before assuming this is just a slow build)"
    set prog [mrd -value $PROGRESS]
    set siter [mrd -value $SPD_ITER]
    puts "last PROGRESS: [format 0x%08x $prog]  SPD_ITER: $siter"
    exit 1
}

set busy_bit    [expr {($s >> 0) & 0x1}]
set done_bit    [expr {($s >> 1) & 0x1}]
set timeout_bit [expr {($s >> 2) & 0x1}]
set pass_bit    [expr {($s >> 3) & 0x1}]
set phase_val   [expr {($s >> 4) & 0x3}]

set p1_mism [mrd -value $P1_MISMATCH]
set p2_mism [mrd -value $P2_MISMATCH]
set tmo_code [mrd -value $TIMEOUT_CODE]
set spd_cycles [mrd -value $SPD_CYCLES]
set spd_n      [mrd -value $SPD_NREG]
set n_val      [mrd -value $N_REG]

puts "STATUS: [format 0x%08x $s]  busy=$busy_bit done=$done_bit timeout=$timeout_bit pass=$pass_bit phase_at_stop=$phase_val"
puts "N=$n_val  P1_MISMATCH=$p1_mism  P2_MISMATCH=$p2_mism"
puts "SPD_CYCLES=$spd_cycles  SPD_N=$spd_n"

if {$spd_n > 0} {
    set ns_per_pair [expr {double($spd_cycles) * 10.0 / double($spd_n)}]
    puts [format "per-pair latency: %.1f ns (aclk=100MHz, %d cycles / %d store+load pairs)" \
          $ns_per_pair $spd_cycles $spd_n]
}

array set tmo_names {0 NONE 1 WAIT_LZ 2 WAIT_TOK 3 RTZ}
if {$timeout_bit} {
    set tmo_name [expr {[info exists tmo_names($tmo_code)] ? $tmo_names($tmo_code) : "UNKNOWN($tmo_code)"}]
    puts "HANG DETECTOR FIRED: wait state $tmo_name never resolved -- this is"
    puts "the deadlock AUDIT.md section 7 recorded for an unarbitrated or"
    puts "under-gated port claim; on the shipped design it should never fire."
}

if {$p1_mism > 0} {
    set fa [mrd -value $P1_FAIL_ADDR]
    set fg [mrd -value $P1_FAIL_GOT]
    set fe [mrd -value $P1_FAIL_EXP]
    puts "  phase1 (program order): $p1_mism mismatch(es); first at addr=[format 0x%03x $fa] got=[format 0x%08x $fg] expect=[format 0x%08x $fe]"
} else {
    puts "  phase1 (program order): CLEAN over $n_val addresses"
}

if {$p2_mism > 0} {
    set fa [mrd -value $P2_FAIL_ADDR]
    set fg [mrd -value $P2_FAIL_GOT]
    set fe [mrd -value $P2_FAIL_EXP]
    puts "  phase2 (RAM retention, re-store+re-read): $p2_mism mismatch(es); first at addr=[format 0x%03x $fa] got=[format 0x%08x $fg] expect=[format 0x%08x $fe]"
} else {
    puts "  phase2 (RAM retention, re-store+re-read): CLEAN over $n_val addresses"
}

# One parseable line, same spirit as xsdb_mem_port.tcl's MEMPORT line.
proc envdef {name} { if {[info exists ::env($name)]} { return $::env($name) } ; return "?" }
puts "MEMARB label=$label uco0=[envdef BD_SZ_UPORT_UMEM0_UCO] usetup0=[envdef BD_SZ_UPORT_UMEM0_USETUP] uco1=[envdef BD_SZ_UPORT_UMEM1_UCO] usetup1=[envdef BD_SZ_UPORT_UMEM1_USETUP] p1_mism=$p1_mism p2_mism=$p2_mism timeout=$timeout_bit"

if {$pass_bit == 1 && $timeout_bit == 0 && $p1_mism == 0 && $p2_mism == 0} {
    puts "=== $label RESULT: PASS -- program order held, RAM retained it, no timeout ==="
    exit 0
}
puts "=== $label RESULT: FAIL -- see the per-phase lines above ==="
exit 1
