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
# Usage: xsdb xsdb_gcd_sig_check.tcl <bitfile> <seed_hex> <n> <exp_sig_hex> <exp_op0_hex> <exp_op1_hex> [exp_lastresult_dec]
#
# exp_lastresult_dec (optional, 7th arg) is host_gcd_replay.py's LASTRESULT
# for this seed/n -- the actual gcd() answer for the FINAL run, independent
# of the SIG accumulation path. Compared against ODATA (o_data_capture),
# which the RTL captures on every completion. This splits "the kernel
# computed something wrong" from "the kernel was right and SIG/LASTOP
# readback mis-accumulated or mis-sampled" -- see MEMORY note on two-channel
# probes reading stale operands; ODATA is a one-channel read of the same
# register the manual path already trusts.
set bitfile   [lindex $argv 0]
set seed_hex  [lindex $argv 1]
set n         [lindex $argv 2]
set exp_sig   [lindex $argv 3]
set exp_op0   [lindex $argv 4]
set exp_op1   [lindex $argv 5]
set exp_lastresult [lindex $argv 6]
if {$bitfile eq ""} {
    error "usage: xsdb xsdb_gcd_trace.tcl <bitfile> <seed_hex> <n>"
}

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
set RUNGAP   [expr {$BASE + 0x50}]
# run_gap (gen_bench.py register 7'h14) = how many aclk cycles S_PREP occupies
# before each run, i.e. the INTER-RUN GAP.  Default 15 in the RTL, which
# reproduces the original fixed prep_ctr==4'd15 timing exactly.
#
# This is the controlled variable for the issue-rate question.  The compiled
# kernel passes 3014/3014 through hw/xsdb_gcd_sweep.tcl, which leaves ~80 ms
# between vectors; this bench issues 64 runs in ~410 us and parks forever in
# S_WAIT_RES at a random run.  Writing run_gap lets BOTH rates run on the SAME
# bitstream and the SAME route, so any difference is attributable to rate and
# not to a reroute ("one route is a sample").
set gap [lindex $argv 3]
if {$gap eq ""} { set gap 15 }
mwr -force $RUNGAP $gap
set gap_rb [mrd -value $RUNGAP]
if {$gap_rb != $gap} {
    error "run_gap readback $gap_rb != $gap -- this bitstream has no run_gap register (rebuild it), so the rate experiment would silently run at the default rate and prove nothing"
}
puts [format "run_gap = %d aclk cycles between runs (%.1f us at 100 MHz)" \
      $gap [expr {$gap / 100.0}]]
mwr -force $NRUNS $n
mwr -force $BCTRL 0x0   ;# BCTRL.start is edge-triggered (start_rise), so drive it
mwr -force $BCTRL 0x1   ;# low first -- a left-high bit would hang and read as a board fault

# ---------------------------------------------------------------------------
# Trace probe.  This does NOT assert anything and has no expected values -- it
# answers ONE question that the pass/fail check cannot: when a batch fails to
# reach bench_done, is the FSM HUNG or merely CRAWLING?
#
# Every counter read below already exists in gen_bench.py's register map; no
# RTL was added to get this.  The distinguishing evidence:
#
#   runs_done  frozen + cycles ADVANCING  -> the aclk domain is alive and the
#              FSM is ticking, but the kernel never returned: a genuine async
#              hang, and `st` is parked in S_WAIT_RES or S_RTZ.
#   runs_done  frozen + cycles FROZEN     -> the whole batch FSM stopped, i.e.
#              bench_busy dropped or the clock/AXI path died -- not a kernel
#              problem at all.
#   runs_done  ADVANCING slowly           -> not a hang: the batch is simply
#              slower than the poll loop's budget, and the "TIMEOUT" is the
#              loop giving up early rather than a defect.
#
# cycles counts every aclk while bench_busy && st != S_PREP; prep_cycles counts
# while st == S_PREP.  Their SUM advancing tells you the domain is live even if
# one of them alone is not.
set CYCLES   [expr {$BASE + 0x18}]
set PREPCYC  [expr {$BASE + 0x1C}]
set LATMIN   [expr {$BASE + 0x28}]
set LATMAX   [expr {$BASE + 0x2C}]

# HS = {o_req_s, i_ack_s} (gen_bench.py register 7'h01).  o_req_s is the
# SYNCHRONIZED view of the kernel's outgoing request, and it is what says which
# state a parked FSM is parked in:
#   o_req_s HIGH -> S_RTZ: the kernel raised its request and never returned it
#                   to zero, so the FSM's "if (!o_req_s)" never fires.
#   o_req_s LOW  -> S_WAIT_RES: the kernel never raised a request at all, so
#                   o_req_latched never got async-set.
set HS [expr {$BASE + 0x04}]

proc snap {} {
    global BSTATUS CYCLES PREPCYC HS
    set bs [mrd -value $BSTATUS]
    set hs [mrd -value $HS]
    # Progress is runs_done/busy/done ONLY.  cycles and prep_cycles are
    # deliberately NOT part of this tuple: cycles free-runs every aclk while
    # bench_busy is high, so including it made every sample differ from the
    # last and the "nothing is moving" test could never fire -- a hung batch
    # was reported as CRAWLING.  They are still printed; they just do not vote.
    list [expr {($bs >> 16) & 0xFFFF}] [expr {$bs & 1}] [expr {($bs >> 1) & 1}] \
         [expr {($hs >> 1) & 1}] [expr {$hs & 1}]
}
proc counters {} {
    global CYCLES PREPCYC
    list [mrd -value $CYCLES] [mrd -value $PREPCYC]
}

puts ""
puts "=== gcd batch trace: seed=$seed_hex n=$n ==="
puts "  sample     runs_done  busy done  o_req_s i_ack_s      cycles   prep_cycles"
set prev {}
set stable 0
for {set s 0} {$s < 12} {incr s} {
    set now [snap]
    lassign $now rd busy done oreq iack
    lassign [counters] cyc prep
    puts [format "  %6d %11d %5d %4d %8d %7d %11u %11u" \
          $s $rd $busy $done $oreq $iack $cyc $prep]
    if {$done} { break }
    if {$now eq $prev} { incr stable } else { set stable 0 }
    set prev $now
    if {$stable >= 3} {
        puts "  -- three consecutive identical samples: nothing is moving --"
        break
    }
    after 400
}

lassign [snap] rd busy done oreq iack
lassign [counters] cyc prep
set bs [mrd -value $BSTATUS]
puts ""
if {$done} {
    puts [format "VERDICT: batch COMPLETED %d/%d -- the poll budget was the only problem" $rd $n]
} elseif {$stable >= 3} {
    if {$cyc == 0 && $prep == 0} {
        puts "VERDICT: FSM DEAD -- runs_done, cycles and prep_cycles are all frozen at zero."
        puts "         bench_busy never really started; suspect the start pulse or aclk, NOT the kernel."
    } elseif {$busy} {
        puts [format "VERDICT: GENUINE HANG at run %d of %d." $rd $n]
        puts "         runs_done is frozen while bench_busy=1, so the batch FSM is parked"
        puts "         waiting on the async kernel, which did not complete this transaction."
        if {$prep != 0 && $cyc != 0} {
            puts "         cycles is still advancing and prep_cycles is not, so the aclk domain"
            puts "         is alive and the FSM is parked in a state OTHER than S_PREP."
        }
        if {$oreq} {
            puts "         o_req_s=1: the kernel RAISED its request and never returned it to"
            puts "         zero. The FSM is stuck in S_RTZ on \"if (!o_req_s)\". The kernel"
            puts "         either never saw its acknowledge or never finished its own RTZ."
        } else {
            puts "         o_req_s=0: the kernel never raised a request for this run at all."
            puts "         The FSM is stuck in S_WAIT_RES and o_req_latched never got set --"
            puts "         either the kernel deadlocked internally, or it already pulsed and"
            puts "         that pulse was consumed/cleared before S_WAIT_RES could observe it"
            puts "         (the o_req_latched-vs-S_ISSUE clear ordering is the suspect there)."
        }
    } else {
        puts [format "VERDICT: busy=0 done=0 at run %d -- the FSM left the batch without finishing it." $rd]
    }
} else {
    puts [format "VERDICT: CRAWLING, not hung -- runs_done reached %d of %d and was still moving" $rd $n]
    puts "         when the trace stopped. The earlier TIMEOUTs are a poll-budget artifact."
}
puts [format "  final: BSTATUS=0x%08x runs_done=%d busy=%d done=%d o_req_s=%d i_ack_s=%d cycles=%u prep_cycles=%u" \
      $bs $rd $busy $done $oreq $iack $cyc $prep]
puts [format "  lat_min=%u lat_max=%u (aclk cycles, only meaningful for runs that completed)" \
      [mrd -value $LATMIN] [mrd -value $LATMAX]]
mwr -force $BCTRL 0x0
