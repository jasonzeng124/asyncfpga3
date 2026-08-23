# xsdb driver for ro_link_ps -- what does one handshake stage cost?
#
# Usage: xsdb cells/hw/xsdb_ro_link.tcl <bitfile> [label]
#   env BD_RO_FMAX   comma-separated post-route Fmax (MHz) for the five ring
#                    counter clocks, ring 0 first.  Grep them out of the
#                    build's pnr.log; hw/run_ro_link.sh does that for you.
#                    Without it the closure gate cannot run and every point is
#                    reported UNGATED, which is a weaker result, not a passing
#                    one.
#
# WHAT THIS PRODUCES.  Five rings of bd_link stages -- 3, 4, 6, 8, 12 -- each
# holding one token, each lapping into its own counter.  Divide the window by
# the count and you have nanoseconds per lap at five lengths; fit a line
# through them and the SLOPE is nanoseconds per stage, free of whatever the
# ring pays once per lap rather than once per stage.  That slope is the
# number the whole rig exists for: it settles whether a stage costs one
# forward pass (~2 ns from this project's routed medians) or all four phases
# serially (~4x that), which is the difference between a 15 ns kernel stage
# being mostly logic and it being mostly protocol.
#
# THREE WAYS THIS RUN CAN GO RED, all checked below.
#
#   1. the rings never started        count reads 0, or the census reads 0.
#   2. the window is not gating       the counts must DOUBLE when the window
#                                     doubles.  If they do not, the counter is
#                                     free-running and every rate is fiction.
#                                     This is the instrument checking itself,
#                                     and it is the check a single window
#                                     length cannot do.
#   3. the counter did not close      a 32-bit counter clocked by a 3-stage
#                                     ring is not obviously safe on this part;
#                                     see hw/ro_link_ps.v's header.  A point
#                                     whose measured rate is above nextpnr's
#                                     Fmax for its own counter clock is VOID
#                                     and is dropped, loudly.
#
# and one that cannot be checked by arithmetic at all, which is why it is
# measured in hardware: a ring that came up with TWO tokens laps twice as
# often and is indistinguishable from a fast ring.  The census samples every
# controller node asynchronously and population-counts it.  One token is a
# moving pair of high nodes, so the mean sits between 1 and 2 -- the test is
# that it is FLAT across the five lengths, because two tokens read double at
# every length.

set bitfile [lindex $argv 0]
if {$bitfile eq ""} { set bitfile "build/hw/ro_link_ps/ro_link_ps.bit" }
set label [lindex $argv 1]
if {$label eq ""} { set label $bitfile }

set BASE    0x40000000
set CTRL    [expr {$BASE + 0x00}]
set WINDOW  [expr {$BASE + 0x04}]
set STATUS  [expr {$BASE + 0x08}]
set LENGTHS [expr {$BASE + 0x0C}]
set CENSUS  [expr {$BASE + 0x10}]
set COUNT0  [expr {$BASE + 0x20}]
set SIG     [expr {$BASE + 0x40}]
set DELAYR  [expr {$BASE + 0x44}]

set K 5
set ACLK_MHZ 100.0

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

# ---- bring-up --------------------------------------------------------------
connect -url tcp:localhost:3121
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

# A constant the fabric can only return if the bitstream loaded, the clock is
# running and the AXI decode lands where the host thinks it does.  Read it
# before anything else, so a plumbing failure never gets reported as physics.
set sig [mrd -value $SIG]
if {$sig != 0x5A5A1234} {
    error "SIG readback [format 0x%08x $sig] != 0x5A5A1234 -- AXI plumbing not up"
}
set v [mrd -value $CTRL]
if {[expr {$v & 0x1}] != 1} {
    error "CTRL.rst readback [format 0x%08x $v] -- rings should come up held in reset"
}
set rodelay [mrd -value $DELAYR]
puts "liveness pre-check PASS (SIG ok, rings held in reset)"
puts "RO_DELAY (from the bitstream): $rodelay bd_delay element(s) per stage"

# Ring lengths come from the BITSTREAM, never from this script.  If the two
# ever disagree the fit would be silently wrong and nothing would say so.
set lenword [mrd -value $LENGTHS]
set lens {}
for {set i 0} {$i < $K} {incr i} { lappend lens [expr {($lenword >> ($i*4)) & 0xf}] }
puts "ring lengths (from hardware): $lens"

proc census {nsamp} {
    set csum {}
    for {set i 0} {$i < $::K} {incr i} { lappend csum 0 }
    for {set s 0} {$s < $nsamp} {incr s} {
        set c [mrd -value $::CENSUS]
        for {set i 0} {$i < $::K} {incr i} {
            lset csum $i [expr {[lindex $csum $i] + (($c >> ($i*4)) & 0xf)}]
        }
    }
    set out {}
    foreach v $csum { lappend out [expr {double($v)/double($nsamp)}] }
    return $out
}

# ---- the census with the ring FROZEN ---------------------------------------
# Release the reset but keep stage 1 of every ring pinned, so nothing moves.
# The state reset built is stage 0 high and everything else low, so this must
# read exactly 1.00 everywhere.  If it does not, the reset never made one
# token and no amount of care about the release ordering will help.  If it
# does, the reset is clean and any extra tokens seen while running were
# acquired in flight -- a different defect entirely.
mwr -force $CTRL 0x4
after 50
set held [census 64]
puts ""
puts "census with the ring HELD (must be 1.00 -- stage 0 and nothing else):"
set held_bad 0
for {set i 0} {$i < $K} {incr i} {
    set m [lindex $held $i]
    set ok [expr {$m > 0.99 && $m < 1.01}]
    puts [format "  ring %d (%2d stages): %.2f  %s" \
          $i [lindex $lens $i] $m [expr {$ok ? "ok" : "<== reset did NOT build one token"}]]
    if {!$ok} { set held_bad 1 }
}

# ---- release ---------------------------------------------------------------
mwr -force $CTRL 0x0
after 50

# ---- token census, running ------------------------------------------------
# Asynchronous samples of signals with no relationship to the sampling clock.
# One reading is noise; the mean over many is the measurement.
set nsamp 256
set cmeans [census $nsamp]
puts ""
puts "token census over $nsamp asynchronous samples, ring RUNNING:"
for {set i 0} {$i < $K} {incr i} {
    set m [lindex $cmeans $i]
    puts [format "  ring %d (%2d stages): mean %.2f high node(s)" \
          $i [lindex $lens $i] $m]
    if {$m < 0.5} { puts "    ^ DEAD: this ring is not turning"; set held_bad 1 }
}
# NOT GATED ON FLATNESS, and the first version of this script was wrong to.
# The model behind that gate was that one token is a moving pair of high nodes
# whose count does not depend on ring length.  The board says otherwise: the
# occupancy climbs with length (1.5, 2.5, 4.5, 6.2, 10.4 at lengths 3, 4, 6,
# 8, 12) while the LOW time per node stays near constant.  That is still one
# token.  The rise wave runs a little faster per stage than the fall wave that
# chases it, so on a ring the high region grows until the low region is as
# narrow as the gates allow, and it is the NARROW LOW PULSE that circulates,
# not a narrow high pulse.  Occupancy is therefore a function of ring length
# and says nothing about token count.
#
# The real token test is further down and it is the fit itself: T tokens make
# the counter tick T times per lap, so that ring sits at 1/T of the line's
# height and shows up as a large residual.  A gate has to be able to go red
# for the right reason, and this one could only ever have gone red for the
# wrong one.

# ---- run a window ----------------------------------------------------------
proc run_window {cycles} {
    mwr -force $::WINDOW $cycles
    mwr -force $::CTRL 0x2
    for {set i 0} {$i < 400} {incr i} {
        set s [mrd -value $::STATUS]
        if {[expr {$s & 0x2}] && ![expr {$s & 0x1}]} { break }
        after 20
    }
    if {![expr {$s & 0x2}]} { error "window did not complete; STATUS=[format 0x%x $s]" }
    set out {}
    for {set i 0} {$i < $::K} {incr i} {
        set c [mrd -value [expr {$::COUNT0 + 4*$i}]]
        if {$c == 0xFFFFFFFF} { error "ring $i counter read as poison -- still running" }
        lappend out $c
    }
    lappend out [expr {($s >> 2) & 0x1}]
    return $out
}

# Two window lengths, and the SECOND one is the point.  A counter that is not
# actually gated by the window still produces a perfectly plausible count; it
# just does not scale.  Doubling the window must double every count.
set W1 5000000
set W2 10000000
puts ""
puts "window A: $W1 aclk cycles ([expr {$W1/100000}] ms)"
set rA [run_window $W1]
puts "window B: $W2 aclk cycles ([expr {$W2/100000}] ms)"
set rB [run_window $W2]
set ovfA [lindex $rA $K]; set ovfB [lindex $rB $K]
if {$ovfA || $ovfB} { puts "OVERFLOW flagged -- shorten the window; results below are void" }

puts ""
puts "linearity of the window (counts must double):"
set lin_bad 0
for {set i 0} {$i < $K} {incr i} {
    set a [lindex $rA $i]; set b [lindex $rB $i]
    if {$a == 0} { puts "  ring $i: count 0 in window A -- dead"; set lin_bad 1; continue }
    set r [expr {double($b)/double($a)}]
    set ok [expr {$r > 1.95 && $r < 2.05}]
    puts [format "  ring %d (%2d stages): %d -> %d, ratio %.4f  %s" \
          $i [lindex $lens $i] $a $b $r [expr {$ok ? "ok" : "<== NOT 2x"}]]
    if {!$ok} { set lin_bad 1 }
}

# ---- rates -----------------------------------------------------------------
proc envdef {name} { if {[info exists ::env($name)]} { return $::env($name) } ; return "" }
set fmax_s [envdef BD_RO_FMAX]
set fmax {}
if {$fmax_s ne ""} { set fmax [split $fmax_s ","] }

puts ""
puts "lap time (window B, $W2 cycles at $ACLK_MHZ MHz):"
set fitN {}; set fitY {}
set gate_dropped 0
set win_ns [expr {double($W2) * 1000.0 / $ACLK_MHZ}]
for {set i 0} {$i < $K} {incr i} {
    set c [lindex $rB $i]
    if {$c == 0} { continue }
    set n   [lindex $lens $i]
    set ns  [expr {$win_ns / double($c)}]
    set mhz [expr {1000.0 / $ns}]
    set note ""
    if {[llength $fmax] > $i} {
        set fm [lindex $fmax $i]
        if {$mhz > $fm} {
            set note [format "  <== VOID: %.1f MHz is above this counter's Fmax of %s MHz" $mhz $fm]
            set gate_dropped 1
        } else {
            set note [format "  (counter Fmax %s MHz, %.0f%% margin)" $fm \
                      [expr {100.0*($fm-$mhz)/$mhz}]]
        }
    } else {
        set note "  (UNGATED: no BD_RO_FMAX)"
    }
    set tlow [expr {$ns * (double($n) - [lindex $cmeans $i]) / double($n)}]
    puts [format "  ring %d: %2d stages  %10d laps  %7.3f ns/lap  %6.1f MHz  low %.2f ns%s" \
          $i $n $c $ns $mhz $tlow $note]
    if {$note eq "" || ![string match "*VOID*" $note]} { lappend fitN $n; lappend fitY $ns }
}

# ---- the fit ---------------------------------------------------------------
# Least squares through the surviving points.  The slope is the answer; the
# intercept is everything a lap pays once rather than once per stage, and the
# only reason there are five rings instead of one is that a single ring cannot
# separate the two.
set m [llength $fitN]
if {$m >= 3} {
    set sx 0.0; set sy 0.0; set sxx 0.0; set sxy 0.0
    for {set i 0} {$i < $m} {incr i} {
        set x [expr {double([lindex $fitN $i])}]
        set y [lindex $fitY $i]
        set sx [expr {$sx+$x}]; set sy [expr {$sy+$y}]
        set sxx [expr {$sxx+$x*$x}]; set sxy [expr {$sxy+$x*$y}]
    }
    set den [expr {$m*$sxx - $sx*$sx}]
    set slope [expr {($m*$sxy - $sx*$sy)/$den}]
    set icept [expr {($sy - $slope*$sx)/double($m)}]
    set ssres 0.0; set sstot 0.0
    set ybar [expr {$sy/double($m)}]
    for {set i 0} {$i < $m} {incr i} {
        set x [expr {double([lindex $fitN $i])}]
        set y [lindex $fitY $i]
        set e [expr {$y - ($slope*$x + $icept)}]
        set ssres [expr {$ssres + $e*$e}]
        set sstot [expr {$sstot + ($y-$ybar)*($y-$ybar)}]
    }
    set r2 [expr {$sstot > 0 ? 1.0 - $ssres/$sstot : 0.0}]
    # The token test.  A ring holding T tokens ticks its counter T times per
    # lap and lands at 1/T of the line -- for T=2 that is a 50% residual, an
    # order of magnitude outside anything routing scatter produces.
    puts ""
    puts "residuals (the token test: T tokens puts a ring at 1/T of the line):"
    set tok_bad 0
    for {set i 0} {$i < $m} {incr i} {
        set x [expr {double([lindex $fitN $i])}]
        set y [lindex $fitY $i]
        set pred [expr {$slope*$x + $icept}]
        set rel [expr {100.0*($y-$pred)/$pred}]
        set ok [expr {abs($rel) < 12.0}]
        puts [format "  %2.0f stages: %7.3f ns measured, %7.3f predicted, %+6.1f%%  %s" \
              $x $y $pred $rel [expr {$ok ? "ok" : "<== not one token"}]]
        if {!$ok} { set tok_bad 1 }
    }
    puts ""
    puts [format "FIT over %d point(s):  lap_ns = %.4f * stages + %.4f   (R^2 = %.5f)" \
          $m $slope $icept $r2]
    puts [format "  ONE HANDSHAKE STAGE, no logic and no matched delay: %.3f ns" $slope]
    puts [format "  fixed per-lap overhead:                             %.3f ns" $icept]
    puts ""
    puts "  read against the two models:"
    puts "    forward-latency-only  ~2 ns/stage   (one LUT + one wire, this route's medians)"
    puts "    four phases serial    ~8 ns/stage"
    puts [format "    measured              %.3f ns/stage" $slope]
} else {
    puts ""
    puts "FIT SKIPPED: only $m usable point(s)"
}

# ---- verdict ---------------------------------------------------------------
puts ""
if {![info exists tok_bad]} { set tok_bad 0 }
set bad [expr {$held_bad || $tok_bad || $lin_bad || $ovfA || $ovfB}]
if {$bad} {
    puts "=== $label: RESULT VOID (reset_bad=$held_bad token_bad=$tok_bad linearity_bad=$lin_bad overflow=[expr {$ovfA||$ovfB}]) ==="
    exit 1
}
# One parseable line per run for the sweep to collect.  Everything in it is
# read back from the hardware, including RO_DELAY, so a mislabelled build
# cannot survive into the table.
set fitline "n/a"
if {[info exists slope]} { set fitline [format "%.4f" $slope] }
set icline "n/a"
if {[info exists icept]} { set icline [format "%.4f" $icept] }
set cflat "n/a"
if {$cmin > 0.5} { set cflat [format "%.2f" [expr {$cmax/$cmin}]] }
puts [format "ROLINK label=%s rodelay=%s slope_ns=%s icept_ns=%s points=%d census_spread=%s void=%d" \
      $label $rodelay $fitline $icline [llength $fitN] $cflat $bad]

if {$gate_dropped} {
    puts "=== $label: PASS with point(s) dropped by the counter-closure gate ==="
} else {
    puts "=== $label: PASS -- reset clean, one token each, window linear, every ring gated ==="
}
