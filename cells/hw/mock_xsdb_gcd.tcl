# mock_xsdb_gcd.tcl -- run xsdb_gcd.tcl in plain tclsh against a fake board, to check that
# the board script's own verdict (=== PASS n/n ===, exit code) is right and CAN fail.
#
#   tclsh cells/hw/mock_xsdb_gcd.tcl [FAULT] -- <args for xsdb_gcd.tcl>
#     FAULT = none | wrong:<k> | hang:<k> | deadaxi
#       wrong:<k>  the k-th transaction (1-based) returns gcd+1
#       hang:<k>   the k-th transaction never raises o_req
#       deadaxi    A_DATA reads back 0 (the liveness pre-check must refuse)
#
# The fake board is gcd_ps.v's register map (CTRL/STATUS/A_DATA/B_DATA/O_DATA at 0x40000000)
# with the kernel replaced by an independent gcd (Euclid here, not the Stein transcription the
# vector file was generated with), answering at once.  It checks the SCRIPT, not the design:
# a board run is the only test of the design.
set fault [lindex $argv 0]
set sep [lsearch -exact $argv --]
set argv [lrange $argv [expr {$sep + 1}] end]
set argc [llength $argv]

set R(ctrl) 4; set R(st) 0; set R(a) 0; set R(b) 0; set R(o) 0; set ntx 0
proc gcd_ref {a b} { while {$b != 0} { set t [expr {$a % $b}]; set a $b; set b $t }; return $a }
proc connect {args} {}
proc targets {args} { return "1 APU\n2 ARM*#0\n3 xc7z010" }
proc rst {args} {}
proc stop {args} {}
proc state {} { return "Stopped" }
proc rrd {args} { return "pc 0000608c" }
proc memmap {args} {}
proc fpga {args} {}
proc after {args} {}
proc mwr {args} {
    global R ntx fault
    set addr [lindex $args end-1]; set v [expr {[lindex $args end] & 0xFFFFFFFF}]
    switch -- [format 0x%08x $addr] {
        0x40000000 {
            set old $R(ctrl); set R(ctrl) $v
            if {$v & 4} { set R(st) 0; return }
            if {($v & 1) && !($old & 1)} {
                incr ntx
                set g [gcd_ref $R(a) $R(b)]
                if {$fault eq "wrong:$ntx"} { incr g }
                set R(o) $g; set R(st) 1                     ;# i_ack sticky
                set R(hang) [expr {$fault eq "hang:$ntx"}]
            }
            if {!($v & 1) && ($R(st) & 1) && !$R(hang)} { set R(st) [expr {$R(st) | 2}] }  ;# o_req
            if {($v & 2)} { set R(st) [expr {$R(st) & ~2}] }                               ;# o_ack drops o_req
        }
        0x40000008 { set R(a) $v }
        0x4000000c { set R(b) $v }
    }
}
proc mrd {args} {
    global R fault
    set addr [lindex $args end]
    switch -- [format 0x%08x $addr] {
        0x40000000 { return $R(ctrl) }
        0x40000004 { return $R(st) }
        0x40000008 { if {$fault eq "deadaxi"} { return 0 }; return $R(a) }
        0x4000000c { return $R(b) }
        0x40000010 { return $R(o) }
    }
    return 0
}
set R(hang) 0
source [file join [file dirname [info script]] xsdb_gcd.tcl]
