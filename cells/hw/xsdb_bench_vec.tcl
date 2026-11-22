# xsdb driver: run a suite VECTOR FILE through the generalised bench (cells/hw/gen_bench.py) on the board, exactly as
# the GLS host does it (cells/gls/ps/gen_ps7.py BENCH_PROG, i.e. cells/gls/ps/ps7_bench.v with +MODE=1 +VECFILE=...),
# and print the SAME lines (BENCHRES / BENCHPRE / BENCHMEM / BENCHMEMCHK / BENCHMEMSTAT / BENCHSUMMARY), so the
# judge that reads a GLS run.log reads the board's log unchanged: research/tools/suite/board_vec_judge.py (the rules of
# research/tools/eventgraph/bench_gate.sh: every call's last result = the C's, every run of the call agreed, every
# run completed; with a memory oracle, every array = the C's after the call).
#
# Usage: xsdb cells/hw/xsdb_bench_vec.tcl <bitfile> <vecfile> [nruns] [clk_ctrl_hex] [memdump] [memcheck]
#   nruns     transactions per call (default 2, as bench_gate.sh's GATE_NRUNS; a kernel that writes its arrays sees
#             its own writes on the next run, so its oracle must be run with the same count)
#   clk_ctrl  FPGA0_CLK_CTRL (default 0x00100C00 = 83.33 MHz, the GLS's +FCLK_PS=12000)
#   memdump   1: after each call, print every memory's contents (BENCHMEM lines; needed for a memory oracle)
#   memcheck  1: after filling the memories, read every word back and count mismatches (BENCHMEMCHK)
# Vector files: research/data/suite/vec/*.hex (v2: first line "// benchvec words=W mems=M"; per call W operand
# words, then every element of each memory in signature order, the depths from the bench's MEMINFO) or the two-word
# format ("op0 op1" per call: research/data/eventgraph/gate/*.hex, kernels/K/vec.hex). Parsed as $readmemh does:
# hex words, "//" comments; an "@" address line is refused.
# Board steps (connect, catch CPU0 in the BootROM, memmap, program, SLCR clock / level shifters / PL resets) are
# hw/xsdb_bench_gen.tcl's, copied. The register sequence per call is BENCH_PROG's, line for line; the only timing
# difference is the host's own speed (JTAG accesses take ~ms, the GLS host's take ns): the bench holds every operand
# and memory word until the next write, and a call starts only on BCTRL's start edge, so the kernel sees the same
# stimulus. cells/hw/test_bench_vec.sh runs this script under tclsh against a mock bench (no board needed).

rename error _tcl_error
proc error {msg args} {
    puts "ERROR: $msg"
    flush stdout
    uplevel 1 [list _tcl_error $msg {*}$args]
}

set bitfile [lindex $argv 0]
set vecfile [lindex $argv 1]
if {$bitfile eq "" || $vecfile eq ""} {
    error "usage: xsdb xsdb_bench_vec.tcl <bitfile> <vecfile> \[nruns\] \[clk_ctrl_hex\] \[memdump\] \[memcheck\]"
}
set NRUNS_SET [lindex $argv 2];    if {$NRUNS_SET eq ""} { set NRUNS_SET 2 }
set CLK_CTRL_VAL [lindex $argv 3]; if {$CLK_CTRL_VAL eq ""} { set CLK_CTRL_VAL 0x00100C00 }
set MEMDUMP [lindex $argv 4];      if {$MEMDUMP eq ""} { set MEMDUMP 0 }
set MEMCHK [lindex $argv 5];       if {$MEMCHK eq ""} { set MEMCHK 0 }
set MODE 1   ;# FIXED, as bench_gate.sh
set DIVISOR0 [expr {($CLK_CTRL_VAL >> 8) & 0x3F}]
set DIVISOR1 [expr {($CLK_CTRL_VAL >> 20) & 0x3F}]
if {$DIVISOR0 == 0} { set DIVISOR0 1 }
if {$DIVISOR1 == 0} { set DIVISOR1 1 }
set FCLK_PS [expr {int(round(1000.0 * $DIVISOR0 * $DIVISOR1))}]   ;# IO PLL 1000 MHz / divisors, in ps
puts "xsdb_bench_vec: bit $bitfile vec $vecfile nruns $NRUNS_SET FPGA0_CLK_CTRL=[format 0x%08x $CLK_CTRL_VAL] (fclk_ps $FCLK_PS)"

# ---- the vector file, as $readmemh reads it --------------------------------------------------------------------
set fd [open $vecfile r]; set vtext [read $fd]; close $fd
set lines [split $vtext "\n"]
set VFMT 1; set VWORDS 2; set VMEMS 0
if {[regexp {^// benchvec words=(\d+) mems=(\d+)} [lindex $lines 0] -> w m]} { set VFMT 2; set VWORDS $w; set VMEMS $m }
set VW {}
foreach ln $lines {
    set i [string first "//" $ln]
    if {$i >= 0} { set ln [string range $ln 0 [expr {$i - 1}]] }
    foreach tok [regexp -all -inline {\S+} $ln] {
        if {[string index $tok 0] eq "@"} { error "$vecfile: an @address line ($tok) is not supported" }
        if {![regexp {^[0-9a-fA-F_]+$} $tok]} { error "$vecfile: not a hex word: $tok" }
        lappend VW [expr {"0x[string map {_ {}} $tok]" & 0xFFFFFFFF}]
    }
}
set VTOT [llength $VW]
if {$VFMT == 1} {
    if {$VTOT % 2} { error "$vecfile: an odd number of words ($VTOT) in a two-word vector file" }
    set NVF [expr {$VTOT / 2}]
}
puts "vector file: format v$VFMT, $VTOT word(s)[expr {$VFMT == 2 ? ", words=$VWORDS mems=$VMEMS" : ", [expr {$VTOT / 2}] call(s)"}]"

# ---- the board (hw/xsdb_bench_gen.tcl's steps) -------------------------------------------------------------------
set BASE 0x40000000
proc reg {off} { return [expr {$::BASE + $off}] }
proc w {off val} { mwr -force [reg $off] [expr {$val & 0xFFFFFFFF}] }
proc r {off} { return [expr {[mrd -value [reg $off]] & 0xFFFFFFFF}] }

set SLCR_UNLOCK 0xF8000008; set SLCR_LOCK 0xF8000004; set FPGA0_CLK_CTRL 0xF8000170
set LVL_SHFTR_EN 0xF8000900; set FPGA_RST_CTRL 0xF8000240

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
mwr -force $SLCR_UNLOCK 0xDF0D
mwr -force $FPGA0_CLK_CTRL $CLK_CTRL_VAL
mwr -force $LVL_SHFTR_EN 0xF
mwr -force $FPGA_RST_CTRL 0x0
mwr -force $SLCR_LOCK 0x767B

# ---- BENCH_PROG, line for line -----------------------------------------------------------------------------------
w 0x08 0xA5A5A5A5
set v [r 0x08]
if {$v != 0xA5A5A5A5} { puts [format "BENCHSUMMARY OP0 readback FAILED (%08x): AXI plumbing not up" $v]; exit 2 }
w 0x00 0x0                                    ;# release the kernel's reset
after 1
set MDEPTH {}; set MWIDTH {}
if {$VFMT == 2} {
    set lay [r 0xA0]
    if {($lay & 0xFFFF) == 0xB5C2} {
        set bad [expr {(($lay >> 16) & 0xFF) != $VWORDS || (($lay >> 24) & 0xFF) != $VMEMS}]
    } else {
        set bad [expr {$VWORDS > 2 || $VMEMS > 0}]
    }
    if {$bad} {
        puts [format "BENCHSUMMARY LAYOUT MISMATCH: bench LAYOUT=%08x, %s says words=%d mems=%d" $lay $vecfile $VWORDS $VMEMS]
        exit 2
    }
    set VCALL $VWORDS
    for {set m 0} {$m < $VMEMS} {incr m} {
        set mi [r [expr {0xC0 + 4 * $m}]]
        lappend MDEPTH [expr {($mi >> 16) & 0xFFFF}]; lappend MWIDTH [expr {($mi >> 8) & 0xFF}]
        incr VCALL [expr {($mi >> 16) & 0xFFFF}]
    }
    set NVF [expr {$VCALL > 0 ? $VTOT / $VCALL : 0}]
    if {$VCALL == 0 || $NVF * $VCALL != $VTOT} {
        puts "BENCHSUMMARY VECFILE $vecfile holds $VTOT words, not a whole number of $VCALL-word calls"
        exit 2
    }
}
set NBATCH $NVF
set NHANG 0
for {set j 0} {$j < $NBATCH} {incr j} {
    w 0x20 0x2; w 0x20 0x0                    ;# bench_rst: stickies read 0 first
    set ill [r 0x58]
    if {($ill & 0x8) || ($ill & 0x80)} { puts [format "BENCHPRE batch=%d ILL=%08x not clear after bench_rst" $j $ill] }
    if {$VFMT == 2} {
        set vbase [expr {$j * $VCALL}]
        set op0 [expr {$VWORDS > 0 ? [lindex $VW $vbase] : 0}]
        set op1 [expr {$VWORDS > 1 ? [lindex $VW [expr {$vbase + 1}]] : 0}]
        for {set k2 2} {$k2 < $VWORDS} {incr k2} { w [expr {0x60 + 4 * ($k2 - 2)}] [lindex $VW [expr {$vbase + $k2}]] }
        w 0x8C 0x0                            ;# MEMSTAT: clear the count and the stickies
        set vo [expr {$vbase + $VWORDS}]
        for {set m 0} {$m < $VMEMS} {incr m} {
            w 0x80 [expr {$m << 16}]
            for {set i 0} {$i < [lindex $MDEPTH $m]} {incr i} { w 0x84 [lindex $VW [expr {$vo + $i}]] }
            incr vo [lindex $MDEPTH $m]
        }
        if {$VMEMS > 0} {
            set mstat [r 0x8C]
            if {($mstat & 0x6) != 0 || (($mstat >> 16) & 0xFFFF) != $VCALL - $VWORDS} {
                puts [format "BENCHMEM batch=%d FILL FAILED MEMSTAT=%08x (%d accesses expected)" $j $mstat [expr {$VCALL - $VWORDS}]]
            }
        }
        if {$MEMCHK && $VMEMS > 0} {
            set nbad 0; set vo [expr {$vbase + $VWORDS}]
            for {set m 0} {$m < $VMEMS} {incr m} {
                set mw [lindex $MWIDTH $m]
                set wmask [expr {$mw >= 32 ? 0xFFFFFFFF : (1 << $mw) - 1}]
                w 0x80 [expr {$m << 16}]
                for {set i 0} {$i < [lindex $MDEPTH $m]} {incr i} {
                    w 0x88 0x1; set rd [r 0x90]
                    if {$rd != ([lindex $VW [expr {$vo + $i}]] & $wmask)} { incr nbad }
                }
                incr vo [lindex $MDEPTH $m]
            }
            puts "BENCHMEMCHK batch=$j words=[expr {$VCALL - $VWORDS}] bad=$nbad"
        }
    } else {
        set op0 [lindex $VW [expr {2 * $j}]]; set op1 [lindex $VW [expr {2 * $j + 1}]]
    }
    w 0x08 $op0; w 0x0C $op1; w 0x14 $NRUNS_SET
    w 0x20 0x0; w 0x20 [expr {0x1 | (($MODE & 3) << 2)}]
    # BENCH_PROG polls BSTATUS for TBATCH (1.2 ms in bench_gate.sh); a JTAG read takes ~ms, so poll ~2 s of reads
    set bs [r 0x24]
    for {set i 0} {$i < 200 && !($bs & 0x2)} {incr i} { after 10; set bs [r 0x24] }
    set cyc [r 0x18]; set prep [r 0x1C]; set lmin [r 0x28]; set lmax [r 0x2C]
    set sig [r 0x38]; set mism [r 0x3C]; set odata [r 0x10]
    set fsm [r 0x54]; set ill [r 0x58]; set illc [r 0x5C]
    puts [format "BENCHRES batch=%d fclk_ps=%d mode=%d op0=%08x op1=%08x n=%d completed=%d cycles=%d prepcyc=%d latmin=%d latmax=%d sig=%08x odata=%08x mism_st=%x ill=%08x ill_tr=%d%s%d->%d ill_rtz=%d ill_cycles=%d fsm=%08x t=0 %s" \
        $j $FCLK_PS $MODE $op0 $op1 $NRUNS_SET [expr {($bs >> 16) & 0xFFFF}] $cyc $prep $lmin $lmax $sig $odata $mism $ill \
        [expr {($ill >> 7) & 1}] ":" [expr {($ill >> 8) & 7}] [expr {($ill >> 11) & 7}] [expr {($ill >> 3) & 1}] $illc $fsm \
        [expr {($bs & 0x2) ? "DONE" : "HANG"}]]
    w 0x20 0x0
    if {$VFMT == 2 && $MEMDUMP && $VMEMS > 0 && ($bs & 0x2)} {
        w 0x8C 0x0
        for {set m 0} {$m < $VMEMS} {incr m} {
            w 0x80 [expr {$m << 16}]
            set vals {}
            for {set i 0} {$i < [lindex $MDEPTH $m]} {incr i} { w 0x88 0x1; lappend vals [format %08x [r 0x90]] }
            puts "BENCHMEM batch=$j mem=$m n=[lindex $MDEPTH $m] data=[join $vals ,]"
        }
        puts [format "BENCHMEMSTAT batch=%d memstat=%08x" $j [r 0x8C]]
    }
    if {!($bs & 0x2)} {
        incr NHANG
        w 0x20 0x2; w 0x20 0x0
        w 0x00 0x4; after 1
        w 0x00 0x0; after 1
    }
}
puts "BENCHSUMMARY batches=$NBATCH hang=$NHANG id_mismatch=0 t_end=0"
