# xsdb driver for gcd_bench's fabric-side throughput/latency benchmark
# on the EBAZ4205.
# Usage: xsdb cells/hw/xsdb_gcd_bench.tcl [bitfile]
# (Vivado Lab 2026.1 ships xsdb; hw_server at tcp:localhost:3121.)
#
# Sibling of xsdb_gcd.tcl (same connect / catch_cpu0_in_bootrom / fpga -f /
# SLCR / memmap / release-reset sequence, copied verbatim) and modeled on
# hw-docs/ref/zynq/xsdb_bench.tcl (the bench driver that silicon-validated
# knapsack's fabric-FSM harness on this exact board). What differs from
# both:
#   - the register map is gcd_bench.v's, not gcd_ps.v's or knapsack's: two
#     operand registers (A_DATA/B_DATA) instead of one I_DATA, and the
#     bench block extends past them at 0x14-0x30 (see gcd_bench.v's
#     header for the authoritative map -- reproduced below, do not let it
#     drift from that file).
#   - gcd_bench has TWO batch modes (BCTRL[2]): FIXED reruns one operand
#     pair N times (the noise floor -- an async bundled-data kernel's own
#     jitter, not the algorithm's), LFSR draws N fresh pairs from a
#     32-bit LFSR seeded off A_DATA (the headline number -- how far
#     Stein's algorithm's latency actually swings with the operands).
#     gcd_bench.v's header argues why a fixed-operand bench would hide
#     the whole point of this backend; that argument is not repeated
#     here.
#   - this harness holds exactly ONE transaction in flight (single
#     operand register pair; the FSM does not issue run k+1 until run k
#     has returned to zero), so "throughput" below is 1/latency, not a
#     pipelined peak. Said once here and once in the printed report so
#     the number is never quoted without that caveat.
#
# Register map (M_AXI_GP0 base 0x40000000, gcd_bench.v). 0x00-0x10 are
# byte-compatible with gcd_ps.v's manual 4-phase path:
#   0x00 CTRL     RW [0]=i_req [1]=o_ack [2]=rst   (manual path; rst powers up 1)
#   0x04 STATUS   RO [0]=i_ack (sticky) [1]=o_req  (manual path)
#   0x08 A_DATA   RW gcd's a -- also the bench's a, and the LFSR seed
#   0x0C B_DATA   RW gcd's b -- also the bench's b in FIXED mode
#   0x10 O_DATA   RO last result, captured on every completion
#   0x14 N_RUNS   RW transactions per batch
#   0x18 CYCLES   RO total FCLK0 cycles for the batch, saturating
#   0x1C BCTRL    RW [0]=start (rise-triggered) [1]=bench_rst [2]=mode (0=FIXED,1=LFSR)
#   0x20 BSTATUS  RO [0]=busy [1]=done [31:16]=completed runs
#   0x24 LAT_MIN  RO smallest per-run latency, cycles (0xFFFFFFFF until one completes)
#   0x28 LAT_MAX  RO largest per-run latency, cycles
#   0x2C LAST_A   RO a of the most recent run
#   0x30 LAST_B   RO b of the most recent run
#
# Host batch protocol (gcd_bench.v header): write A_DATA/B_DATA and
# N_RUNS, set BCTRL, poll BSTATUS.done, read
# CYCLES/LAT_MIN/LAT_MAX/O_DATA/LAST_A/LAST_B, clear BCTRL. Do not touch
# CTRL[0]/[1] while busy -- the FSM owns the kernel handshake then.
# CTRL.rst must be 0 (released once, at bring-up, below).
#
# Clock: FCLK0 is nominal 100 MHz (IO PLL 1000 MHz / 10, SLCR recipe
# below) but hw-docs/02-zynq-ebaz4205.md section 4 records a measured
# wall-clock range of 97.9-99.2 MHz on this board. This script converts
# cycles to nanoseconds using the 100 MHz nominal figure and says so at
# every print -- treat printed ns/throughput numbers as carrying up to
# ~2% systematic uncertainty from that assumption, not as calibrated.

set bitfile [lindex $argv 0]
if {$bitfile eq ""} { set bitfile "build/hw/gcd_bench/gcd_bench.bit" }

set FCLK0_HZ_NOMINAL 100000000.0

set BASE    0x40000000
set CTRL    [expr {$BASE + 0x00}]
set STATUS  [expr {$BASE + 0x04}]
set ADATA   [expr {$BASE + 0x08}]
set BDATA   [expr {$BASE + 0x0C}]
set ODATA   [expr {$BASE + 0x10}]
set NRUNS   [expr {$BASE + 0x14}]
set CYCLES  [expr {$BASE + 0x18}]
set BCTRL   [expr {$BASE + 0x1C}]
set BSTATUS [expr {$BASE + 0x20}]
set LATMIN  [expr {$BASE + 0x24}]
set LATMAX  [expr {$BASE + 0x28}]
set LASTA   [expr {$BASE + 0x2C}]
set LASTB   [expr {$BASE + 0x30}]

# SLCR registers (UG585)
set SLCR_UNLOCK     0xF8000008
set SLCR_LOCK       0xF8000004
set SLCR_UNLOCK_KEY 0xDF0D
set SLCR_LOCK_KEY   0x767B
set FPGA0_CLK_CTRL  0xF8000170
set LVL_SHFTR_EN    0xF8000900
set FPGA_RST_CTRL   0xF8000240

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

# --- halt CPU0 cold (verbatim from xsdb_gcd.tcl) -----------------------
# rst -system + an IMMEDIATE tight stop-retry loop catches the core in
# BootROM (PC < 0x20000) before the NAND boot chain touches anything.
# NOTE: -system resets the PL too, so this MUST precede fpga -f. It is
# also the recovery path when a previous hung AXI access left the DAP in
# "APB AP transaction error" (only the DAP target visible).
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
# memmap must be declared on the APU (the A9s inherit it) and BEFORE
# fpga -f.  Either mistake gives "Blocked address 0x40000000 ... has not been
# added to the memory map".  See xsdb_gcd.tcl for the longer note.
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
puts "SLCR: FCLK0 set (IO PLL 1000/10 = 100 MHz nominal), level shifters on, PL resets released."

# xsdb blocks PL AXI slave ranges by default; declare the register block.
# Must come before any mrd/mwr against $BASE.
# (memmap is declared on APU before fpga -f -- see above.)

# --- liveness pre-check -------------------------------------------------
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
set v [mrd -value $BSTATUS]
puts "BSTATUS in reset : [format 0x%08x $v] (expect 0x0)"
puts "liveness pre-check PASS"

# --- release kernel from reset ------------------------------------------
mwr -force $CTRL 0x0
after 100

# --- functional pre-check: one manual 4-phase call ----------------------
# Exactly xsdb_gcd.tcl's gcd_once sequence (0x00-0x10 is byte-compatible
# with gcd_ps.v), against a known vector: proves the manual path and the
# kernel itself before any autonomous batch is trusted. Bounded by
# poll_status (200 iters/poll) so a MISSING answer -- this kernel's known
# failure mode, see MEMORY.md nextpnr-lut-pinmap-bitstream-bug.md -- shows
# up as a named timeout rather than a hang.
proc gcd_once {a b} {
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
set got [gcd_once 12 18]
if {$got != 6} { error "manual pre-check FAILED: gcd(12,18) = $got, want 6" }
puts "manual 4-phase pre-check PASS: gcd(12,18) = $got"

# =========================================================================
# Batch driver
# =========================================================================

# run_batch n mode -- drive one autonomous batch of n back-to-back
# transactions in fabric, mode 0=FIXED (rerun A_DATA/B_DATA) or 1=LFSR
# (operands drawn from a PRNG seeded off A_DATA). Caller sets A_DATA/
# B_DATA (via set_operands) before calling this; run_batch itself only
# touches N_RUNS/BCTRL and the read-back result registers.
#
# The done-poll is bounded (200 + n iterations, 10 ms/iteration -- scales
# with batch size so a 10000-run LFSR batch gets a proportionally longer
# leash than a 1000-run FIXED one, while still being a NAMED bound, never
# an infinite wait). A timeout reports BSTATUS's completed-run count
# (bits [31:16]) so you can tell a batch that never started (completed=0)
# from one that wedged partway through (0 < completed < n) from one that
# finished all n runs but never raised done (completed==n) -- three
# different failures that a bare "TIMEOUT" would collapse into one.
proc run_batch {n mode} {
    mwr -force $::NRUNS $n
    set bctrl_val [expr {0x1 | (($mode & 1) << 2)}]  ;# start=1, mode as given
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
        set busy      [expr {$bs & 0x1}]
        set diag [expr {$completed == 0 ? "never started (busy=$busy)" \
                        : ($completed < $n ? "wedged mid-batch" : "ran all $n but never raised done")}]
        mwr -force $::BCTRL 0x0
        error "TIMEOUT waiting for BSTATUS.done (n=$n mode=$mode, [expr {$poll_iters * 10}] ms budget); last BSTATUS=[format 0x%08x $bs] completed=$completed/$n -- $diag"
    }

    set completed [expr {($bs >> 16) & 0xFFFF}]
    if {$bs & 0x1} {
        puts "WARNING: BSTATUS.busy still set alongside done (n=$n mode=$mode); BSTATUS=[format 0x%08x $bs]"
    }
    if {$completed != ($n & 0xFFFF)} {
        puts "WARNING: completed=$completed != N_RUNS&0xffff=[expr {$n & 0xFFFF}] (n=$n mode=$mode)"
    }

    set cycles [mrd -value $::CYCLES]
    set latmin [mrd -value $::LATMIN]
    set latmax [mrd -value $::LATMAX]
    set odata  [mrd -value $::ODATA]
    set lasta  [mrd -value $::LASTA]
    set lastb  [mrd -value $::LASTB]
    mwr -force $::BCTRL 0x0

    return [dict create n $n mode $mode completed $completed cycles $cycles \
                latmin $latmin latmax $latmax odata $odata lasta $lasta lastb $lastb]
}

proc set_operands {a b} {
    mwr -force $::ADATA $a
    mwr -force $::BDATA $b
}

proc cyc2ns {c} { return [expr {double($c) / $::FCLK0_HZ_NOMINAL * 1e9}] }

# Print one batch's result as a report row and stash it for the final
# summary table. mean cycles/run = CYCLES/completed (CYCLES counts the
# whole batch, not per-run, so this is where "mean" actually comes from).
set ::results {}
proc report_batch {label a b r} {
    set n         [dict get $r n]
    set mode      [dict get $r mode]
    set completed [dict get $r completed]
    set cycles    [dict get $r cycles]
    set latmin    [dict get $r latmin]
    set latmax    [dict get $r latmax]
    set mean_cyc  [expr {double($cycles) / $completed}]
    set spread    [expr {$latmax - $latmin}]

    set min_ns  [cyc2ns $latmin]
    set max_ns  [cyc2ns $latmax]
    set mean_ns [cyc2ns $mean_cyc]
    set tps     [expr {1.0e9 / $mean_ns}]   ;# 1/mean-latency, NOT pipelined peak

    set modestr [expr {$mode ? "LFSR" : "FIXED"}]
    puts [format "%-22s mode=%-5s N=%-6d a=%-8s b=%-8s min=%6d max=%6d spread=%5d mean=%8.1f cyc  |  min=%8.1f max=%8.1f mean=%8.1f ns  |  %10.1f tx/s" \
          $label $modestr $n $a $b $latmin $latmax $spread $mean_cyc $min_ns $max_ns $mean_ns $tps]

    lappend ::results [dict create label $label mode $modestr n $n a $a b $b \
        min_cyc $latmin max_cyc $latmax spread_cyc $spread mean_cyc $mean_cyc \
        min_ns $min_ns max_ns $max_ns mean_ns $mean_ns tps $tps \
        odata [dict get $r odata] lasta [dict get $r lasta] lastb [dict get $r lastb]]
}

puts ""
puts "Clock assumption: FCLK0 = 100.000 MHz nominal (IO PLL 1000 MHz / 10)."
puts "  hw-docs/02-zynq-ebaz4205.md section 4 measured wall-clock 97.9-99.2 MHz on"
puts "  this board -- ns/throughput figures below carry up to ~2% systematic"
puts "  uncertainty from assuming the nominal 100 MHz instead of a calibrated rate."
puts "Throughput below is 1/mean-latency: this harness holds ONE transaction in"
puts "  flight (single operand register pair, run k+1 does not issue until run k"
puts "  returns to zero -- see gcd_bench.v's header), so it is NOT a pipelined"
puts "  peak rate."
puts ""

# =========================================================================
# (a) FIXED noise floor -- same (a,b) every run, N=1000. LAT_MIN and
#     LAT_MAX should come out nearly equal; the spread here is the
#     measurement's own jitter and calibrates how much of the LFSR
#     spread below is signal versus noise.
# =========================================================================
puts "=== (a) FIXED noise floor: a=12 b=18, N=1000 ==="
set_operands 12 18
set r [run_batch 1000 0]
report_batch "noise-floor(12,18)" 12 18 $r
set nf [lindex $::results end]
puts [format "  min=%d max=%d cycles, spread=%d cycles (%.1f ns), mean=%.1f cycles/run" \
      [dict get $nf min_cyc] [dict get $nf max_cyc] [dict get $nf spread_cyc] \
      [cyc2ns [dict get $nf spread_cyc]] [dict get $nf mean_cyc]]
puts ""

# =========================================================================
# (b) FIXED sweep -- several fixed pairs, N=1000 each. Each run is
#     individually deterministic (small min/max spread per pair, as in
#     (a)); the pair-to-pair variation is the operands changing gcd's
#     Stein's-algorithm iteration count, not measurement jitter.
# =========================================================================
puts "=== (b) FIXED sweep: several fixed pairs, N=1000 each ==="
set fixed_pairs {
    {12    18}
    {48    18}
    {1     1}
    {99991 99991}
    {12    788500}
}
foreach p $fixed_pairs {
    lassign $p a b
    set_operands $a $b
    set r [run_batch 1000 0]
    report_batch "fixed($a,$b)" $a $b $r
}
puts ""

# =========================================================================
# (c) LFSR headline -- N=10000, operands drawn from a 32-bit LFSR seeded
#     off A_DATA. LAT_MIN/LAT_MAX bracket the real data-dependent spread
#     across ten thousand different operand pairs; LAST_A/LAST_B are only
#     the final pair (the FSM does not log every pair, by design -- see
#     gcd_bench.v).
# =========================================================================
puts "=== (c) LFSR headline: N=10000, seeded from A_DATA ==="
set LFSR_SEED 0xACE1
set_operands $LFSR_SEED 0
set r [run_batch 10000 1]
report_batch "lfsr(seed=[format 0x%x $LFSR_SEED])" [format 0x%x $LFSR_SEED] "-" $r
set lf [lindex $::results end]
puts [format "  min=%d max=%d cycles, spread=%d cycles (%.1f ns) across %d runs; last pair a=%d b=%d -> %d" \
      [dict get $lf min_cyc] [dict get $lf max_cyc] [dict get $lf spread_cyc] \
      [cyc2ns [dict get $lf spread_cyc]] [dict get $r completed] \
      [dict get $lf lasta] [dict get $lf lastb] [dict get $lf odata]]
puts ""

# =========================================================================
# Summary
# =========================================================================
puts "=== summary: [llength $::results] runs ==="
puts [format "%-22s %-6s %-7s %-8s %-8s %-8s %-8s %-8s %-10s %-10s" \
      label mode N min_cyc max_cyc mean_cyc min_ns max_ns mean_ns tx/s]
foreach r $::results {
    puts [format "%-22s %-6s %-7d %-8d %-8d %-8.1f %-8.1f %-8.1f %-10.1f %-10.1f" \
          [dict get $r label] [dict get $r mode] [dict get $r n] \
          [dict get $r min_cyc] [dict get $r max_cyc] [dict get $r mean_cyc] \
          [dict get $r min_ns] [dict get $r max_ns] [dict get $r mean_ns] [dict get $r tps]]
}
puts "=== done: [llength $::results]/[llength $::results] batches completed without a timeout ==="
exit 0
