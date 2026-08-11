# Bare-metal Cortex-A9 knapsack driver (OCM-resident, JTAG-loaded).
# See knapsack_drive.c / ocm.ld / zynq/BRINGUP.md "ARM bare-metal drive
# route".  Toolchain: arm-none-eabi-gcc 10.3 (Ubuntu package, newlib
# present but unused -- freestanding, no libc, no semihosting).
#
#   make            -> knapsack_drive.elf + knapsack_drive.dis
#   make REPEATS=10 -> smaller sweep (default 40 -> 10240 transactions)

CROSS   ?= arm-none-eabi-
CC      := $(CROSS)gcc
OBJDUMP := $(CROSS)objdump
SIZE    := $(CROSS)size

REPEATS ?= 40

CFLAGS  := -mcpu=cortex-a9 -marm -O2 -Wall -Wextra \
           -ffreestanding -fno-builtin -fomit-frame-pointer \
           -DREPEATS=$(REPEATS)
LDFLAGS := -nostdlib -nostartfiles -Wl,-T,ocm.ld -Wl,--build-id=none \
           -Wl,-Map,knapsack_drive.map

all: knapsack_drive.elf knapsack_drive.dis

knapsack_drive.elf: startup.S knapsack_drive.c ocm.ld knapsack_golden.h
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ startup.S knapsack_drive.c
	$(SIZE) $@

knapsack_drive.dis: knapsack_drive.elf
	$(OBJDUMP) -d -j .text -j .vectors $< > $@

knapsack_golden.h: gen_golden.py
	cd ../.. && python3 zynq/arm/gen_golden.py

clean:
	rm -f knapsack_drive.elf knapsack_drive.dis knapsack_drive.map

.PHONY: all clean
