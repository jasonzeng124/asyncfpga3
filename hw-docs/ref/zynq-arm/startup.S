/* startup.S -- bare-metal Cortex-A9 entry for the OCM-resident knapsack
 * driver (see knapsack_drive.c / ocm.ld).
 *
 * Environment contract: loaded via xsdb `dow` into low OCM with CPU0
 * halted in early BootROM (the proven rst -system catch from
 * zynq/xsct_knapsack.tcl, PC < 0x20000 -- before BootROM configures
 * MMU/caches). We still force MMU/D-cache/I-cache/branch-predictor OFF
 * explicitly: the catch point is a debugger race, not an architectural
 * guarantee, and everything here relies on uncached strongly-ordered
 * accesses (AXI register map at 0x40000000, mailbox in OCM read by the
 * debugger, global timer).
 *
 * Interrupts stay masked (CPSID if); no vector infrastructure is needed,
 * but VBAR is pointed at our own table so a stray abort spins visibly
 * in `hang` instead of executing whatever is at address 0.
 */
    .syntax unified
    .arm

    .section .vectors, "ax"
    .global _start
_start:
    b   reset
    b   hang        /* undefined instruction */
    b   hang        /* svc */
    b   hang        /* prefetch abort */
    b   hang        /* data abort */
    b   hang        /* (reserved) */
    b   hang        /* irq */
    b   hang        /* fiq */

hang:
    b   hang

    .text
reset:
    cpsid   aif                     /* mask async abort + IRQ + FIQ */

    /* VBAR -> our vector table; SCTLR.V (high vectors) cleared below
     * via the explicit bit clears (reset value of V is 0 anyway). */
    ldr r0, =_start
    mcr p15, 0, r0, c12, c0, 0

    /* SCTLR: MMU off, D-cache off, I-cache off, branch predictor off. */
    mrc p15, 0, r0, c1, c0, 0
    bic r0, r0, #0x0001             /* M: MMU */
    bic r0, r0, #0x0004             /* C: D-cache */
    bic r0, r0, #0x1000             /* I: I-cache */
    bic r0, r0, #0x0800             /* Z: branch predictor */
    mcr p15, 0, r0, c1, c0, 0
    isb

    /* Invalidate stale state (nothing dirty to flush: if the catch was
     * early enough D was never on; if it wasn't, the tcl re-resets). */
    mov r0, #0
    mcr p15, 0, r0, c8, c7, 0       /* invalidate unified TLB */
    mcr p15, 0, r0, c7, c5, 0       /* invalidate I-cache */
    mcr p15, 0, r0, c7, c5, 6       /* invalidate branch predictor */
    dsb
    isb

    ldr sp, =__stack_top

    /* zero .bss */
    ldr r0, =__bss_start
    ldr r1, =__bss_end
    mov r2, #0
1:  cmp r0, r1
    bhs 2f
    str r2, [r0], #4
    b   1b
2:
    bl  main
3:  wfe                             /* main returned: park */
    b   3b
