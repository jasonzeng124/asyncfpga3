# mock_xsdb_vec.tcl -- runs hw/xsdb_bench_vec.tcl under plain tclsh against a MOCK bench (no board, no xsdb), for
# cells/hw/test_bench_vec.sh.  It stands in for xsdb's commands (connect, targets, rst, stop, state, rrd, memmap, fpga,
# mwr, mrd) and for gen_bench.py's register map: operands, BCTRL's start edge, BSTATUS, LAYOUT / MEMINFO, the
# memory host port (0x80 select, 0x84 write, 0x88 read-advance, 0x90 read data, 0x8C MEMSTAT count).  A call's
# ODATA is the j-th word of MOCK_EXP (the "kernel" is the oracle itself; MOCK_CORRUPT=j flips bit 0 of call j's,
# MOCK_HANG=j leaves call j not done).  Every register write goes to MOCK_LOG ("W addr data"; "START j" at each start)
# so the test can check the stimulus against the vector file.
#   tclsh mock_xsdb_vec.tcl <xsdb_bench_vec.tcl> <its args...>
#   env: MOCK_EXP (required), MOCK_LOG, MOCK_LAYOUT (hex, default 0: no LAYOUT register), MOCK_MEMINFO ("depth:width,...")
set script [lindex $argv 0]
set argv [lrange $argv 1 end]
set argc [llength $argv]
set ::EXPW {}
set fd [open $::env(MOCK_EXP) r]; foreach t [regexp -all -inline {\S+} [read $fd]] { lappend ::EXPW $t }; close $fd
set ::LOG [open [expr {[info exists ::env(MOCK_LOG)] ? $::env(MOCK_LOG) : "/dev/null"}] w]
set ::CORRUPT [expr {[info exists ::env(MOCK_CORRUPT)] ? $::env(MOCK_CORRUPT) : -1}]
set ::HANG [expr {[info exists ::env(MOCK_HANG)] ? $::env(MOCK_HANG) : -1}]
set ::LAYOUT [expr {[info exists ::env(MOCK_LAYOUT)] ? $::env(MOCK_LAYOUT) : 0}]
set ::MINFO {}
if {[info exists ::env(MOCK_MEMINFO)] && $::env(MOCK_MEMINFO) ne ""} {
    foreach dw [split $::env(MOCK_MEMINFO) ,] { lassign [split $dw :] d wd; lappend ::MINFO [list $d $wd] }
}
# MOCK_MEMEXP=FILE (oracle_mem.sh's ORACLE_MEMOUT: "call=J mem=M ... data=w,w,..."): after call J, until the next
# bench_rst, a read through the host port returns the C's array (a "perfect kernel" for array-writing kernels)
array set ::MX {}
if {[info exists ::env(MOCK_MEMEXP)] && $::env(MOCK_MEMEXP) ne "" && [file exists $::env(MOCK_MEMEXP)]} {
    set fd [open $::env(MOCK_MEMEXP) r]
    foreach ln [split [read $fd] "\n"] {
        if {[regexp {call=(\d+)} $ln -> cj] && [regexp {mem=(\d+)} $ln -> cm] && [regexp {data=(\S+)} $ln -> cd]} {
            set ::MX($cj,$cm) [split $cd ,]
        }
    }
    close $fd
}
set ::POST -1
array set ::R {}
set ::NSTART 0; set ::MSEL 0; set ::WIDX 0; set ::RIDX 0; set ::MCOUNT 0; set ::RDVAL 0
array set ::MEM {}
proc connect {args} {}
proc targets {args} { return "1 APU\n2 ARM Cortex-A9 MPCore #0 (Stopped)\n3 xc7z010" }
proc rst {args} {}
proc stop {args} {}
proc state {} { return "Stopped (Mock)" }
proc rrd {args} { return "pc 00000100" }
proc memmap {args} {}
proc fpga {args} {}
proc mwr {args} {
    set a [lindex $args end-1]; set v [expr {[lindex $args end] & 0xFFFFFFFF}]
    if {$a < 0x40000000 || $a >= 0x40001000} { return }   ;# SLCR writes
    set off [expr {$a - 0x40000000}]
    puts $::LOG [format "W %02x %08x" $off $v]
    # 0x20 BCTRL (start edge runs a call), 0x80 select a memory, 0x84 write its next word, 0x88 read-advance,
    # 0x8C MEMSTAT clear
    switch -- $off {
        32 {
            set prev [expr {[info exists ::R(32)] ? $::R(32) : 0}]
            set ::R(32) $v
            if {($v & 2)} { set ::R(36) 0; set ::POST -1 }
            if {!($prev & 1) && ($v & 1)} {
                set j $::NSTART; incr ::NSTART
                puts $::LOG "START $j"; set ::POST $j
                set n [expr {[info exists ::R(20)] ? $::R(20) : 0}]
                set o [expr {"0x[lindex $::EXPW $j]" & 0xFFFFFFFF}]
                if {$j == $::CORRUPT} { set o [expr {$o ^ 1}] }
                set ::R(16) $o; set ::R(56) $o; set ::R(60) 2
                set ::R(24) [expr {100 + $j}]; set ::R(28) 3; set ::R(40) 40; set ::R(44) 44
                set ::R(84) 0; set ::R(88) 0; set ::R(92) 0
                set ::R(36) [expr {$j == $::HANG ? (1 << 16) : (($n & 0xFFFF) << 16) | 2}]
            }
        }
        128 { set ::MSEL [expr {$v >> 16}]; set ::WIDX 0; set ::RIDX 0 }
        132 { set ::MEM($::MSEL,$::WIDX) $v; incr ::WIDX; incr ::MCOUNT }
        136 {
            if {$::POST >= 0 && [info exists ::MX($::POST,$::MSEL)]} {
                set ::RDVAL [expr {"0x[lindex $::MX($::POST,$::MSEL) $::RIDX]" & 0xFFFFFFFF}]
            } else {
                set ::RDVAL [expr {[info exists ::MEM($::MSEL,$::RIDX)] ? $::MEM($::MSEL,$::RIDX) : 0}]
            }
            incr ::RIDX; incr ::MCOUNT
        }
        140 { set ::MCOUNT 0 }
        default { set ::R($off) $v }
    }
}
proc mrd {args} {
    set a [lindex $args end]; set off [expr {$a - 0x40000000}]
    switch -- $off {
        160 { return $::LAYOUT }
        140 { return [expr {($::MCOUNT & 0xFFFF) << 16}] }
        144 { return $::RDVAL }
        default {
            if {$off >= 192 && $off < 224} {
                set m [expr {($off - 192) / 4}]
                if {$m < [llength $::MINFO]} {
                    lassign [lindex $::MINFO $m] d wd
                    return [expr {($d << 16) | ($wd << 8) | 7}]
                }
                return 0
            }
            return [expr {[info exists ::R($off)] ? $::R($off) : 0}]
        }
    }
}
source $script
close $::LOG
