
connect -url tcp:localhost:3121
targets -set -filter {name =~ "xc7z010*"}

jtag targets -set -filter {name =~ "xc7z010*"}

# See ro_measure.py / hw/README.md: a background hw_server chain poll can
# shift a stray control word into this design between scans.  Nothing here
# can be erased by one (no clear bit exists), but an address glitch mid-scan
# is still a nuisance, so lock for the duration regardless.
jtag lock 600000

set seq [jtag sequence]
set ctrl 0

proc u1 {addr} {
    global seq ctrl
    $seq clear
    $seq irshift -state IDLE -integer 6 0x02
    $seq drshift -capture -state IDLE -integer 48 [expr {$addr | $ctrl}]
    return [$seq run -hex]
}

proc rd {addr} {
    u1 $addr
    return [u1 $addr]
}

foreach a {8 9} {
    puts "CONST $a [rd $a]"
}
for {set k 0} {$k < 24} {incr k} {
    puts "SAMPLE 0 [rd 12]"
}

puts "THRESH [rd 3]"
puts "CTRL [rd 4]"

for {set rep 0} {$rep < 0} {incr rep} {
    set ctrl 0x20                           ;# hold_run moved to bit 5 when
                                             ;# hold_addr widened to 5 bits
    u1 0                                    ;# run=1
    set t0 [clock microseconds]
    after 8000
    set ctrl 0x00
    u1 0                                    ;# run=0
    set t1 [clock microseconds]
    puts "WINDOW $rep [expr {$t1 - $t0}]"
    puts "R1COUNT $rep [rd 0]"
    puts "R2COUNT $rep [rd 1]"
}

puts "ANOM [rd 2]"
puts "FLT [rd 19]"
puts "POP0 [rd 5]"
puts "POP1 [rd 20]"
puts "POP2 [rd 21]"
puts "POP3 [rd 22]"
puts "POP4 [rd 23]"
puts "POP5 [rd 24]"
puts "POPF0 [rd 26]"
puts "POPF1 [rd 27]"
puts "POPF2 [rd 28]"
puts "POPF3 [rd 29]"
puts "POPF4 [rd 30]"
puts "POPF5 [rd 31]"
puts "HITCNT0 [rd 6]"
puts "HITCNT1 [rd 7]"
puts "HITCNT2 [rd 11]"
puts "HITCNT3 [rd 13]"
puts "HITCNT4 [rd 14]"
puts "HITCNT5 [rd 15]"
puts "RATEA [rd 10]"
puts "RATEB [rd 25]"
puts "WINCTRL [rd 16]"
puts "DIAG16 [rd 17]"
puts "DIAG8 [rd 18]"

jtag unlock
puts "DONE"
exit
