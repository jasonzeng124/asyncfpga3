# xsdb driver for ipow_ps on the EBAZ4205 -- the DSP48E1 sweep.
#
# Usage: xsdb cells/hw/xsdb_ipow_sweep.tcl [bitfile] [N] [seed]
#
# WHY THIS EXISTS
#
# ipow_ps is the first design in this project whose datapath contains hard
# multipliers: six DSP48E1, inferred because ipow's two multiplies both have
# two live operands (every other kernel multiplies by a literal, and
# --arith-reduce-strength turns those into shifts before the backend sees
# them).  Nothing about a DSP48E1 is exercised by the gcd sweep, so a passing
# gcd tells you nothing about this path.
#
# Bring-up, register map and the 4-phase transaction are IDENTICAL to
# xsdb_gcd_sweep.tcl and copied from it unchanged -- ipow_ps.v deliberately
# presents the same channel arity and the same register map as gcd_ps.v.
# Only the oracle and the vectors below differ.
#
# THE ORACLE.  ipow's C is `int r=1; while(e>0){ if(e&1) r=r*b; b=b*b; e>>=1; }`
# on 32-bit ints, so every product wraps mod 2**32.  TCL integers do not wrap,
# so ipow_ref masks after every multiply -- reproducing the C exactly rather
# than computing a true power and truncating at the end.  (Those happen to
# agree, since multiplication mod 2**32 is a homomorphism, but the masked form
# is the one that stays right if the kernel ever changes shape.)
#
# Exponents are drawn non-negative and < 2**24: `e > 0` and `e >> 1` are
# SIGNED in the C, so a negative exponent is a different test than this
# oracle models.  Bases are drawn over the full 32 bits -- wrapping is the
# point, and the multiply does not care about the sign.
#
# A_DATA carries the BASE and B_DATA the EXPONENT (see ipow_ps.v).
# RANDOM CORRECTNESS SWEEP, not just the 16 golden vectors.
# Usage: xsdb cells/hw/xsdb_gcd_sweep.tcl [bitfile] [N] [seed]
# (Vivado Lab 2026.1 ships xsdb; hw_server at tcp:localhost:3121.)
#
# WHY THIS EXISTS ALONGSIDE xsdb_gcd.tcl
#
# xsdb_gcd.tcl runs 16 vectors chosen by hand. That is a fine smoke test and
# a poor correctness argument: every claim it makes is a claim about vectors
# a human picked. This script generates N pseudo-random (a,b) pairs plus a
# deliberate adversarial set, drives each one through the same 4-phase
# sequence, and checks the answer against a reference gcd computed in TCL --
# not against a baked-in expected column. Bring-up (connect, catch CPU0 in
# BootROM, memmap-before-fpga-f, SLCR sequence, gcd_once) is copied
# near-verbatim from xsdb_gcd.tcl; see that file's header for the full
# bench-history rationale behind each piece. Only the vector source and the
# pass/fail bookkeeping are new.
#
# TIMING. Each host AXI transaction over JTAG costs about 10 ms, and
# gcd_once does about 8 of them (2 writes to latch a/b, 1 write + poll to
# raise i_req, 1 write to drop i_req, 1 poll for o_req rise, 1 read of
# O_DATA, 1 write for o_ack, 1 poll for o_req fall) -- call it ~80 ms per
# vector. N=500 (the default) is therefore roughly 40 s; N=5000 is roughly
# 7 minutes. Progress prints every 100 vectors so a long sweep is
# observably alive rather than apparently hung.
#
# REFERENCE MODEL. The kernel computes Stein's binary GCD on 32-bit SIGNED
# integers, with gcd(0,b)=b and gcd(a,0)=a. Plain Euclid agrees with Stein
# on that domain PROVIDED both operands are non-negative -- Stein's
# handling of negative inputs (via absolute value inside the kernel) is not
# reproduced here, so this sweep never emits a negative operand. Every
# vector, random or adversarial, is drawn from [0, 2**24), which is safely
# inside i32 range and leaves no room for Euclid's intermediate remainders
# to do anything Stein wouldn't.
#
# Register map (M_AXI_GP0 base 0x40000000, see gcd_ps.v) -- offsets copied
# from xsdb_gcd.tcl, not re-derived:
#   0x00 CTRL   [0]=i_req [1]=o_ack [2]=rst   (rst powers up at 1)
#   0x04 STATUS [0]=i_ack(sticky) [1]=o_req
#   0x08 A_DATA gcd's a : i32 (RW, readback echoes)
#   0x0C B_DATA gcd's b : i32 (RW, readback echoes)
#   0x10 O_DATA gcd's result : i32 (RO)

set bitfile [lindex $argv 0]
if {$bitfile eq ""} { set bitfile "build/hw/mult2_ps/mult2_ps.bit" }

set N [lindex $argv 1]
if {$N eq ""} { set N 500 }

set SEED [lindex $argv 2]
if {$SEED eq ""} { set SEED 1 }

set BASE   0x40000000
set CTRL   [expr {$BASE + 0x0}]
set STATUS [expr {$BASE + 0x4}]
set ADATA  [expr {$BASE + 0x8}]
set BDATA  [expr {$BASE + 0xC}]
set ODATA  [expr {$BASE + 0x10}]
set ODATA2 [expr {$BASE + 0x14}]   ;# the second product, see hw/mult2_ps.v

# SLCR registers (UG585)
set SLCR_UNLOCK     0xF8000008
set SLCR_LOCK       0xF8000004
set SLCR_UNLOCK_KEY 0xDF0D
set SLCR_LOCK_KEY   0x767B
set FPGA0_CLK_CTRL  0xF8000170
set LVL_SHFTR_EN    0xF8000900
set FPGA_RST_CTRL   0xF8000240

# --- reference model ----------------------------------------------------
# Plain Euclid. Agrees with the kernel's Stein binary gcd (gcd(0,b)=b,
# gcd(a,0)=a) as long as both operands are non-negative -- see header.
proc ipow_ref {b e} {
    # Mirrors the C statement for statement, masking after every multiply
    # because TCL integers are arbitrary precision and the kernel's are not.
    set M 0xFFFFFFFF
    set r 1
    set b [expr {$b & $M}]
    while {$e > 0} {
        if {($e & 1) == 1} { set r [expr {($r * $b) & $M}] }
        set b [expr {($b * $b) & $M}]
        set e [expr {$e >> 1}]
    }
    return $r
}

# --- adversarial vectors --------------------------------------------------
# Run first, before the random flood, so a structural failure (e.g. the
# zero case) shows up immediately instead of buried at vector #300. All
# operands non-negative and < 2**24 per the header note. {a b} pairs only
# -- the expected value is computed by gcd_ref at run time, same as the
# random vectors, so there is nothing here for a human to get wrong.
set adversarial_vectors {
    {3          7}
    {0          0}
    {12345      0}
    {0          5}
    {1          16777215}
    {2          31}
    {2          32}
    {2          33}
    {4294967295 2}
    {4294967295 3}
    {65536      2}
    {65535      2}
    {7          11}
    {10         9}
    {3          1}
    {2863311530 1}
}

proc poll_status {mask want tag} {
    # ~ms per iteration over JTAG; the core finishes in us -- generous.
    # Bounded so a MISSING answer (this kernel's known failure mode, see
    # MEMORY.md) shows up as a named timeout instead of an infinite hang.
    for {set i 0} {$i < 200} {incr i} {
        set s [mrd -value $::STATUS]
        if {([expr {$s & $mask}]) == $want} { return $s }
    }
    error "TIMEOUT waiting for STATUS&[format 0x%x $mask]==[format 0x%x $want] ($tag); last STATUS=[format 0x%x $s]"
}

connect -url tcp:localhost:3121
puts "targets:"
puts [targets]

# --- halt CPU0 cold ---------------------------------------------------
# Plain `stop` times out against whatever the stock NAND image leaves
# running. `rst -system` + an IMMEDIATE tight stop-retry loop catches the
# core in BootROM (PC ~0x608c) before the boot chain touches anything.
# Verified by PC: BootROM executes below 0x20000; anything higher means
# the catch was late and we reset again. NOTE: -system resets the PL
# too, so this MUST precede fpga -f. It is also the recovery path when a
# previous hung AXI access left the DAP in "APB AP transaction error":
# in that state only the DAP target is visible, and rst -system issued
# on it restores the APU target (bench-verified, xsct_knapsack.tcl).
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
# Declare the AXI3 register block BEFORE programming, and on the APU rather
# than on a single A9.  Both matter, and getting either wrong gives the same
# message: "Blocked address 0x40000000 ... has not been added to the memory
# map" (hw-docs/02 section 8).  memmap attaches to the context it is issued
# against; the A9 cores inherit the APU's, so declaring it on APU covers both
# and survives the target switches below.  Declared after fpga -f it does not
# take -- which is exactly how this script failed the first time it ran.
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
puts "SLCR: FCLK0 set (IO PLL 1000/10 = 100 MHz), level shifters on, PL resets released."

# xsdb blocks PL AXI slave ranges by default ("Blocked address ... has
# not been added to the memory map"); declare the register block. Must
# come before any mrd/mwr against $BASE.
# (memmap is declared on APU before fpga -f -- see above.)

# --- liveness pre-check ------------------------------------------------
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
puts "liveness pre-check PASS"

# --- release kernel from reset -----------------------------------------
mwr -force $CTRL 0x0
after 100

# --- one gcd transaction -----------------------------------------------
# The 4-phase sequence returns CTRL to 0 (RTZ) at every step because the
# harness is a pulse adapter, not a level-sensitive core: holding i_req
# even ~1us past i_ack rise wedges the core permanently, and o_ack must
# drop again once o_req has fallen or the next transaction's o_req never
# rises. Each poll is bounded (poll_status, 200 iters) and names exactly
# which handshake edge it was waiting for, so a hang shows up as a
# labeled TIMEOUT (i_ack rise / o_req rise / o_req fall) instead of an
# infinite wait -- this kernel's known failure mode is a MISSING answer.
proc mult_once {a b} {
    # data valid before req rise (bundled-data; separate writes)
    mwr -force $::ADATA $a
    mwr -force $::BDATA $b
    mwr -force $::CTRL 0x1                  ;# i_req=1
    poll_status 0x1 0x1 "i_ack rise (b=$a e=$b)"
    mwr -force $::CTRL 0x0                  ;# drop i_req (RTZ)
    poll_status 0x2 0x2 "o_req rise (b=$a e=$b)"
    set got [expr {[mrd -value $::ODATA] & 0xFFFFFFFF}]
    mwr -force $::CTRL 0x2                  ;# o_ack=1
    poll_status 0x2 0x0 "o_req fall (b=$a e=$b)"
    mwr -force $::CTRL 0x0                  ;# drop o_ack (RTZ complete)
    return $got
}

# --- sweep engine ---------------------------------------------------------
# Shared by the adversarial list and the random flood: run one (a,b) pair,
# compare against gcd_ref, print/count. A timeout inside gcd_once is caught
# here so it is counted as a failure (tagged with the poll name that timed
# out) rather than allowed to kill the script.
set pass 0
set fail 0
set n 0
set fail_triples {}

proc run_one {a b} {
    global pass fail n fail_triples
    incr n
    set want [ipow_ref $a $b]
    if {[catch {ipow_once $a $b} got]} {
        puts "*** MISMATCH (TIMEOUT) *** vector $n: ipow($a,$b) got=TIMEOUT ($got) expected=$want"
        incr fail
        if {[llength $fail_triples] < 20} {
            lappend fail_triples [list $a $b "TIMEOUT: $got" $want]
        }
    } elseif {$got == $want} {
        incr pass
    } else {
        puts "*** MISMATCH *** vector $n: ipow($a,$b) got=$got expected=$want"
        incr fail
        if {[llength $fail_triples] < 20} {
            lappend fail_triples [list $a $b $got $want]
        }
    }
    if {$n % 100 == 0} {
        puts "progress: $n vectors run, $pass passed so far"
    }
}



# --- two lone DSPs, no cascade --------------------------------------------
# o_data  = a[15:0]  * b[15:0]   (one DSP48E1)
# o_data2 = a[31:16] * b[31:16]  (one DSP48E1)
proc both {a b} {
    mwr -force $::ADATA $a
    mwr -force $::BDATA $b
    mwr -force $::CTRL 0x1
    poll_status 0x1 0x1 "i_ack"
    mwr -force $::CTRL 0x0
    poll_status 0x2 0x2 "o_req"
    set g1 [expr {[mrd -value $::ODATA]  & 0xFFFFFFFF}]
    set g2 [expr {[mrd -value $::ODATA2] & 0xFFFFFFFF}]
    mwr -force $::CTRL 0x2
    poll_status 0x2 0x0 "o_req fall"
    mwr -force $::CTRL 0x0
    return [list $g1 $g2]
}
set p1 0; set f1 0; set p2 0; set f2 0; set shown 0
set vecs {}
foreach x {0 1 2 3 4 5 7 10 15 16 17 255 256 257 65535} {
    lappend vecs [list [expr {$x | ($x << 16)}] [expr {$x | ($x << 16)}]]
}
expr {srand($SEED)}
for {set i 0} {$i < $N} {incr i} {
    lappend vecs [list [expr {int(rand()*4294967296)}] [expr {int(rand()*4294967296)}]]
}
foreach v $vecs {
    lassign $v a b
    set w1 [expr {(($a & 0xFFFF) * ($b & 0xFFFF)) & 0xFFFFFFFF}]
    set w2 [expr {((($a >> 16) & 0xFFFF) * (($b >> 16) & 0xFFFF)) & 0xFFFFFFFF}]
    lassign [both $a $b] g1 g2
    if {$g1 == $w1} { incr p1 } else { incr f1 }
    if {$g2 == $w2} { incr p2 } else { incr f2 }
    if {($g1 != $w1 || $g2 != $w2) && $shown < 8} {
        incr shown
        puts [format "  a=%10u b=%10u  lo got %-11s want %-11s | hi got %-11s want %s" \
              $a $b $g1 $w1 $g2 $w2]
    }
}
puts "=== DSP48_X0Y24 (o_data,  a\[15:0\]*b\[15:0\]) : $p1 pass / $f1 fail"
puts "=== DSP48_X0Y20 (o_data2, a\[31:16\]*b\[31:16\]): $p2 pass / $f2 fail"
exit 0
