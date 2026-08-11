/* ocm.ld -- link the bare-metal knapsack driver into low OCM.
 *
 * Memory contract (see zynq/BRINGUP.md "ARM bare-metal drive route" and
 * knapsack_drive.c): after the proven rst -system BootROM catch, OCM is
 * mapped 0x00000000..0x0002FFFF low (192 KB) + 64 KB at 0xFFFF0000.
 * We deliberately link at 0x00020000, NOT 0x0: the Zynq-7000 BootROM's
 * 128 KB ROM can shadow 0x00000000..0x0001FFFF while BootROM is still
 * the active image (exactly our catch point), so the lowest 128 KB is
 * not guaranteed writable through the halted CPU. 0x20000..0x2FFFF is
 * plain OCM RAM in every BootROM state. Layout:
 *
 *   0x00020000 .. 0x0002EFFF   text/rodata/data/bss + stack (60 KB)
 *   0x0002F000 .. 0x0002FFFF   MAILBOX (fixed, last 4 KB of low OCM;
 *                              layout in knapsack_drive.c -- the host
 *                              tcl reads it by absolute address)
 *
 * Stack top = 0x0002F000, growing down (first push lands at 0x2EFFC,
 * inside the RAM region, never in the mailbox).
 */

ENTRY(_start)

MEMORY
{
    RAM (rwx) : ORIGIN = 0x00020000, LENGTH = 0x0000F000  /* 60 KB */
}

SECTIONS
{
    .text : {
        KEEP(*(.vectors))
        *(.text*)
        *(.rodata*)
        . = ALIGN(4);
    } > RAM

    .data : {
        *(.data*)
        . = ALIGN(4);
    } > RAM

    .bss (NOLOAD) : {
        . = ALIGN(4);
        __bss_start = .;
        *(.bss*)
        *(COMMON)
        . = ALIGN(4);
        __bss_end = .;
    } > RAM

    __stack_top = ORIGIN(RAM) + LENGTH(RAM);   /* 0x0002F000 */

    /DISCARD/ : { *(.ARM.exidx*) *(.comment) *(.note*) }
}

/* Guarantee >= 4 KB of stack headroom below __stack_top. */
ASSERT(__bss_end <= __stack_top - 0x1000, "image too big: < 4 KB stack headroom in OCM")
