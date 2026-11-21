
connect -url tcp:localhost:3121
targets -set -filter {name =~ "xc7z010*"}

jtag targets -set -filter {name =~ "xc7z010*"}

jtag lock 600000

set seq [jtag sequence]
set ctrl 0x000

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

foreach a {2 3} {
    puts "CONST $a [rd $a]"
}
puts "CFG [rd 4]"

# Zero the sticky array before anything is measured.  Without this the words
# read back are a cumulative record since configuration -- including the
# free-running sweeps that always happen between the FPGA coming up and this
# script's pin write landing -- rather than a verdict on this run.  Held for a
# few scan updates so the clear reaches all thirty-two latches, then released
# so they can accumulate again.
# The readback happens WHILE hold[11] is still asserted, and that ordering is
# the whole point.  Releasing first and then reading proves nothing: the rig
# keeps running, and a fast vector re-sets its own sticky in the microseconds
# between release and scan.  Measured -- pinned to vector 0, which completes a
# gcd every 3.5 housekeeping cycles, the array read back 0x0001 immediately
# after a clear that had in fact worked.
set ctrl 0x800
u1 0
u1 0
u1 0
puts "CLRERR [rd 8]"
puts "CLROK [rd 9]"
puts "CLRABSN [rd 10]"
puts "CLRABSS [rd 11]"
puts "CLRCMPB [rd 14]"
puts "CLRCMPS [rd 15]"
puts "CLRCMPB0 [rd 20]"
set ctrl 0x000
u1 0

puts "STATUS [rd 5]"
for {set k 0} {$k < 24} {incr k} {
    puts "SAMPLE 0 [rd 6]"
}

for {set rep 0} {$rep < 2} {incr rep} {
    set ctrl 0x020
    u1 0
    set t0 [clock microseconds]
    after 3000
    set ctrl 0x000
    u1 0
    set t1 [clock microseconds]
    puts "WINDOW $rep [expr {$t1 - $t0}]"
    puts "HKCOUNT $rep [rd 0]"
    puts "LAPCOUNT $rep [rd 1]"
}

puts "ERR [rd 8]"
puts "OK [rd 9]"
puts "ABSN [rd 10]"
puts "ABSS [rd 11]"
puts "ABSV [rd 12]"
puts "ABSI [rd 13]"
puts "CMPB [rd 14]"
puts "CMPS [rd 15]"
puts "CMPV [rd 16]"
puts "CMPI [rd 17]"
puts "ERRV [rd 18]"
puts "ERRI [rd 19]"
puts "CMPB0 [rd 20]"

jtag unlock
puts "DONE"
exit
