
connect -url tcp:localhost:3121
targets -set -filter {name =~ "xc7z010*"}
fpga -f /home/jayjay/dev2/proj/asyncfpga3/cells/build/hw/ro_top/ro_top.bit
jtag targets -set -filter {name =~ "xc7z010*"}

# LOCK THE PORT, AND THIS IS NOT A PRECAUTION.
#
# hw_server rescans the chain on its own schedule.  A rescan that shifts DR
# while USER1 is still the selected instruction lands in THIS design's shift
# register and is then committed by the same Update-DR -- so an unrelated
# background poll writes a random control word.  Bit 5 of a random word is the
# clear bit, so about half of those polls wipe every counter, and the symptom
# is not noise: it is a clean, plausible, entirely wrong zero.  Measured, not
# theorised -- unlocked, all five counters read exactly 0 across a one-second
# window in which the rings were provably turning.
jtag lock 600000

set seq [jtag sequence]
set ctrl 0

# The control bits are STICKY on the host side.  A read is two scans and every
# scan commits a control word, so a read helper that sends a bare address
# silently drops run and clear -- which makes it impossible to read anything
# while the counters are running, including the poison value that proves they
# are.  Holding the bits here means a scan changes only what it means to.
proc u1 {addr} {
    global seq ctrl
    $seq clear
    $seq irshift -state IDLE -integer 6 0x02
    $seq drshift -capture -state IDLE -integer 48 [expr {$addr | $ctrl}]
    return [$seq run -hex]
}

# Both shifts end in IDLE, not in PAUSE: Pause-DR does not pass through
# Update-DR, so a scan that parks in PAUSE captures correctly and then never
# commits anything at all.
proc rd {addr} {
    u1 $addr
    return [u1 $addr]
}

foreach a {8 9 10 12} {
    puts "CONST $a [rd $a]"
}

# Is anything turning?  An asynchronous sample of each ring node, repeated:
# the value means nothing, the variance means everything.
for {set k 0} {$k < 24} {incr k} {
    puts "SAMPLE 0 [rd 12]"
}

for {set rep 0} {$rep < 30} {incr rep} {
    set ctrl 0x20
    u1 0                                    ;# clear=1
    set ctrl 0x00
    u1 0                                    ;# clear=0
    set ctrl 0x10
    u1 0                                    ;# run=1
    set t0 [clock microseconds]
    puts "POISON $rep [rd 0]"
    after 8000
    set ctrl 0x00
    u1 0                                    ;# run=0
    set t1 [clock microseconds]
    puts "WINDOW $rep [expr {$t1 - $t0}]"
    for {set a 0} {$a < 5} {incr a} {
        puts "COUNT $rep $a [rd $a]"
    }
}
jtag unlock
puts "DONE"
exit
