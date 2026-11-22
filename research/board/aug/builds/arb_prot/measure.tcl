
connect -url tcp:localhost:3121
targets -set -filter {name =~ "xc7z010*"}

jtag targets -set -filter {name =~ "xc7z010*"}

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

foreach a {2 3} {
    puts "CONST $a [rd $a]"
}
puts "CFG [rd 4]"
puts "STATUS [rd 5]"
for {set k 0} {$k < 24} {incr k} {
    puts "SAMPLE 0 [rd 6]"
}

for {set rep 0} {$rep < 3} {incr rep} {
    set ctrl 0x20
    u1 0
    set t0 [clock microseconds]
    after 8000
    set ctrl 0x00
    u1 0
    set t1 [clock microseconds]
    puts "WINDOW $rep [expr {$t1 - $t0}]"
    puts "HKCOUNT $rep [rd 0]"
    puts "SVCCOUNT $rep [rd 1]"
}

puts "VIOL0 [rd 8]"
puts "VIOL1 [rd 9]"
puts "VIOL2 [rd 10]"
puts "OVL0 [rd 12]"
puts "OVL1 [rd 13]"
puts "OVL2 [rd 14]"
puts "SERV0 [rd 16]"
puts "SERV1 [rd 17]"
puts "SERV2 [rd 18]"

jtag unlock
puts "DONE"
exit
