# xsdb driver for the knapsack hardware benchmark harness
# (zynq/knapsack_bench_top.v) on the EBAZ4205.
# Usage: xsdb zynq/xsdb_bench.tcl [bitfile]
# (Vivado Lab 2026.1 ships xsdb; hw_server at tcp:localhost:3121.)
#
# Modeled on zynq/xsct_knapsack.tcl (2026-07-21 revision): the connect /
# cold-halt / memmap / fpga -f / SLCR recipe below is copied VERBATIM
# from that script's bench-verified sequence (BRINGUP_SESSION.md items
# 16-17). Only the register-map driving differs: instead of host-paced
# 4-phase pokes per call, the fabric-side repeat FSM runs N back-to-back
# transactions and counts FCLK0 cycles, so throughput/latency are
# measured entirely in hardware (JTAG pokes are ms-scale; one knapsack
# call is us-scale -- host-side timing would be 99.9% JTAG overhead).
#
# Register map (M_AXI_GP0 base 0x40000000, zynq/knapsack_bench_top.v;
# 0x00-0x0C byte-compatible with knapsack_ps_top.v):
#   0x00 CTRL     [0]=i_req [1]=o_ack [2]=rst   (rst powers up at 1)
#   0x04 STATUS   [0]=i_ack(sticky) [1]=o_req
#   0x08 I_DATA   cap (also the cap the bench FSM presents)
#   0x0C O_DATA   LAST_RESULT (captured on each o_req rise)
#   0x10 N_RUNS   number of back-to-back transactions
#   0x14 CYCLES   total FCLK0 cycles first i_req -> run N's RTZ (saturating)
#   0x18 BCTRL    [0]=bench_start (rise-triggered level) [1]=bench_rst
#   0x1C BSTATUS  [0]=busy [1]=done [15:8]=runs_lo
#   0x20 LAT_MIN  min per-run latency (cycles)
#   0x24 LAT_MAX  max per-run latency (cycles)
#
# Output: per-cap report on stdout + machine-readable TSV at
# build/knapsack_bench/results.tsv, plus an FCLK0 wall-clock calibration
# (long batch timed with the host clock; see zynq/BENCH.md).

set bitfile [lindex $argv 0]
if {$bitfile eq ""} { set bitfile "build/knapsack_bench/knapsack_bench_top.bit" }
set tsvfile "build/knapsack_bench/results.tsv"

# ---- FCLK0 rate ------------------------------------------------------
# MEASURED FACT (this board, 2026-07-21): with the verbatim
# xsct_knapsack.tcl SLCR recipe (srcsel=IO PLL, DIV0=10), FCLK0 is
# 100 MHz, NOT 33.33/10 MHz. xsct_knapsack.tcl's comment says the IO
# PLL is "locked-but-BYPASSED" after rst -system; SLCR readback shows
# IO_PLL_CTRL=0x0001e008 = FDIV=30 with only PLL_BYPASS_QUAL (bit 3)
# set -- PLL_BYPASS_FORCE (bit 4) is CLEAR, and BootROM has already
# locked the PLLs (PLL_STATUS=0x3f), so the output mux passes
# 33.33 MHz x 30 = 1000 MHz and FCLK0 = 1000/DIV0. A 7-second
# wall-clock calibration batch measured 99.2 MHz (the ~1% deficit is
# done-poll latency); the script re-derives the nominal rate from SLCR
# readback below and the calibration at the end cross-checks it.
# Protocol safety is FCLK0-independent (async-clear pulse adapter, see
# knapsack_bench_top.v); the rate only sets quantization (10 ns/cycle
# at 100 MHz) and the cycles->seconds conversion.
set FCLK0_DIV0 10
set PS_CLK_HZ  33333333.0
set CAL_SECONDS 5.0

set BASE    0x40000000
set CTRL    [expr {$BASE + 0x00}]
set STATUS  [expr {$BASE + 0x04}]
set IDATA   [expr {$BASE + 0x08}]
set ODATA   [expr {$BASE + 0x0C}]
set NRUNS   [expr {$BASE + 0x10}]
set CYCLES  [expr {$BASE + 0x14}]
set BCTRL   [expr {$BASE + 0x18}]
set BSTATUS [expr {$BASE + 0x1C}]
set LATMIN  [expr {$BASE + 0x20}]
set LATMAX  [expr {$BASE + 0x24}]

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
set NRUNS_PER_CAP 1000

proc poll_status {mask want tag} {
    # ~ms per iteration over JTAG; the core finishes in us -- generous.
    for {set i 0} {$i < 200} {incr i} {
        set s [mrd -value $::STATUS]
        if {([expr {$s & $mask}]) == $want} { return $s }
    }
    error "TIMEOUT waiting for STATUS&[format 0x%x $mask]==[format 0x%x $want] ($tag); last STATUS=[format 0x%x $s]"
}

# Poll BSTATUS.done; budget scales with the expected batch length.
proc poll_done {iters tag} {
    for {set i 0} {$i < $iters} {incr i} {
        set s [mrd -value $::BSTATUS]
        if {$s & 0x2} { return $s }
        after 10
    }
    error "TIMEOUT waiting for BSTATUS.done ($tag); last BSTATUS=[format 0x%x $s] (runs_lo=[expr {($s >> 8) & 0xff}])"
}

connect -url tcp:localhost:3121
puts "targets:"
puts [targets]

# --- halt CPU0 cold (verbatim from xsct_knapsack.tcl) ------------------
# rst -system + an IMMEDIATE tight stop-retry loop catches the core in
# BootROM (PC < 0x20000) before the NAND boot chain touches anything:
# kills the armed-watchdog risk and the MMU phys/virt ambiguity at once.
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
# Verbatim recipe from xsct_knapsack.tcl, with DIV0 parameterized (the
# bench-verified value is 10 -> 0x00100A00). srcsel=IO PLL (00),
# divisor1=1, divisor0=FCLK0_DIV0.
targets -set -filter {name =~ "ARM*#0"}
mwr -force $SLCR_UNLOCK $SLCR_UNLOCK_KEY
mwr -force $FPGA0_CLK_CTRL [expr {0x00100000 | ($FCLK0_DIV0 << 8)}]
mwr -force $LVL_SHFTR_EN 0xF
mwr -force $FPGA_RST_CTRL 0x0
mwr -force $SLCR_LOCK $SLCR_LOCK_KEY

# Derive nominal FCLK0 from the ACTUAL clock-tree state (see header).
set IO_PLL_CTRL 0xF8000108
set io_pll [mrd -value $IO_PLL_CTRL]
set fdiv   [expr {($io_pll >> 12) & 0x7f}]
set forced [expr {($io_pll >> 4) & 1}]
set pll_hz [expr {$forced ? $PS_CLK_HZ : $PS_CLK_HZ * $fdiv}]
set FCLK0_HZ [expr {$pll_hz / $FCLK0_DIV0}]
puts [format "SLCR: IO_PLL_CTRL=0x%08x (FDIV=%d bypass_force=%d) -> FCLK0 nominal %.3f MHz; level shifters on, PL resets released." \
      $io_pll $fdiv $forced [expr {$FCLK0_HZ / 1e6}]]

# --- liveness pre-check ----------------------------------------------
set v [mrd -value $CTRL]
puts "CTRL  after config: [format 0x%08x $v] (expect 0x4: rst=1)"
mwr -force $IDATA 0xA5
set v [mrd -value $IDATA]
if {$v != 0xA5} { error "I_DATA readback FAILED: [format 0x%x $v] != 0xa5 -- AXI plumbing not up" }
mwr -force $IDATA 0x0
set v [mrd -value $STATUS]
puts "STATUS in reset  : [format 0x%08x $v] (expect 0x0)"
set v [mrd -value $BSTATUS]
puts "BSTATUS in reset : [format 0x%08x $v] (expect 0x0)"
puts "liveness pre-check PASS"

# --- release core reset ----------------------------------------------
mwr -force $CTRL 0x0
after 100

# --- functional pre-check: one MANUAL 4-phase call (byte-compat path) --
# Exactly xsct_knapsack.tcl's poke sequence; proves the 0x00-0x0C map
# and the core before trusting any autonomous batch.
mwr -force $IDATA 3
mwr -force $CTRL 0x1
poll_status 0x1 0x1 "i_ack rise (manual cap=3)"
mwr -force $CTRL 0x0
poll_status 0x1 0x0 "i_ack fall (manual cap=3)"
poll_status 0x2 0x2 "o_req rise (manual cap=3)"
set got [expr {[mrd -value $ODATA] & 0xFFFF}]
mwr -force $CTRL 0x2
poll_status 0x2 0x0 "o_req fall (manual cap=3)"
mwr -force $CTRL 0x0
if {$got != 5} { error "manual pre-check FAILED: knapsack(3) = $got, want 5" }
puts "manual 4-phase pre-check PASS: knapsack(3) = 5"

# --- one autonomous batch ----------------------------------------------
# Returns {result cycles latmin latmax runs_lo}. Caller checks golden.
proc bench_batch {cap n poll_iters tag} {
    mwr -force $::IDATA $cap
    mwr -force $::NRUNS $n
    mwr -force $::BCTRL 0x1                     ;# bench_start rise
    set bs [poll_done $poll_iters $tag]
    mwr -force $::BCTRL 0x0                     ;# re-arm for next batch
    if {$bs & 0x1} { error "busy still set after done ($tag)" }
    set result  [expr {[mrd -value $::ODATA] & 0xFFFF}]
    set cycles  [mrd -value $::CYCLES]
    set latmin  [mrd -value $::LATMIN]
    set latmax  [mrd -value $::LATMAX]
    set runs_lo [expr {($bs >> 8) & 0xff}]
    if {$runs_lo != ($n & 0xff)} {
        error "runs_lo=$runs_lo != N&0xff=[expr {$n & 0xff}] ($tag)"
    }
    return [list $result $cycles $latmin $latmax $runs_lo]
}

# --- golden sweep: 11 caps x N_RUNS_PER_CAP ----------------------------
set tsv [open $tsvfile w]
puts $tsv [join {cap result golden pass n_runs cycles cycles_per_run lat_min lat_max us_per_call calls_per_sec fclk0_hz_nominal} "\t"]

set pass 0
set fail 0
puts ""
puts [format "%-4s %-6s %-6s %-10s %-12s %-8s %-8s %-10s %-12s" \
      cap result golden cycles cycles/run lat_min lat_max us/call calls/sec]
foreach cap $caps want $golden {
    set r [bench_batch $cap $NRUNS_PER_CAP 3000 "cap=$cap N=$NRUNS_PER_CAP"]
    lassign $r result cycles latmin latmax runs_lo
    set cpr   [expr {double($cycles) / $NRUNS_PER_CAP}]
    set uspc  [expr {$cpr / $FCLK0_HZ * 1e6}]
    set cps   [expr {$FCLK0_HZ / $cpr}]
    set ok    [expr {$result == $want}]
    if {$ok} { incr pass } else { incr fail }
    puts [format "%-4d %-6d %-6d %-10d %-12.1f %-8d %-8d %-10.2f %-12.0f %s" \
          $cap $result $want $cycles $cpr $latmin $latmax $uspc $cps \
          [expr {$ok ? "PASS" : "FAIL"}]]
    puts $tsv [join [list $cap $result $want [expr {$ok ? 1 : 0}] \
          $NRUNS_PER_CAP $cycles [format %.2f $cpr] $latmin $latmax \
          [format %.3f $uspc] [format %.1f $cps] [format %.0f $FCLK0_HZ]] "\t"]
}
close $tsv
puts "TSV written: $tsvfile"
puts "=== $pass/[llength $caps] golden caps PASS, $fail FAIL ==="

# --- FCLK0 wall-clock calibration --------------------------------------
# Size a batch to ~CAL_SECONDS from the measured cycles/run (cap=15),
# time the busy period with the host clock, and compare CYCLES/wall_s
# against the nominal rate. Poll granularity (~10 ms) over several
# seconds keeps this within a few %.
set r [bench_batch 15 $NRUNS_PER_CAP 3000 "calib presample"]
set cpr [expr {double([lindex $r 1]) / $NRUNS_PER_CAP}]
set ncal [expr {int($FCLK0_HZ * $CAL_SECONDS / $cpr)}]
if {$ncal < 1} { set ncal 1 }
puts [format "calibration: N=%d (~%.1f s nominal) ..." $ncal $CAL_SECONDS]
set t0 [clock milliseconds]
set r [bench_batch 15 $ncal [expr {int($CAL_SECONDS * 1000) + 60000}] "calibration N=$ncal"]
set t1 [clock milliseconds]
set wall_s [expr {($t1 - $t0) / 1000.0}]
set cyc [lindex $r 1]
set hz_meas [expr {$cyc / $wall_s}]
puts [format "calibration: %d cycles in %.3f s wall -> FCLK0 ~ %.3f MHz (nominal %.3f MHz, %+.1f%%)" \
      $cyc $wall_s [expr {$hz_meas / 1e6}] [expr {$FCLK0_HZ / 1e6}] \
      [expr {100.0 * ($hz_meas - $FCLK0_HZ) / $FCLK0_HZ}]]
puts "NOTE: wall time includes start-write + done-poll JTAG latency (tens of ms);"
puts "      trust the % only when the batch runs multiple seconds."

if {$fail > 0} { exit 1 }
exit 0
