//===- memsum.c - a loop that reads memory -------------------------*- C -*-===//
//
// WHY THIS KERNEL (research, 2026-11-17; PROGRAM "General first" item 3): the loop reads an array, so the flow must
// lower a load (bdc/mem.py) inside a ring. CLAUDE.md's warning applies: iverilog cannot see yosys memory inference, so
// this kernel's gate needs the bits-decoded netlist, never the RTL.
//
//===----------------------------------------------------------------------===//
#include "memsum.h"
#include "dynamatic/Integration.h"

int memsum(in_int_t a[N], in_int_t n) {
  int s = 0;
  for (int i = 0; i < n && i < N; i++)
    s = s + a[i] * (i + 1);
  return s;
}

int main(void) {
  in_int_t a[N];
  for (int i = 0; i < N; i++) a[i] = 3 * i - 7;
  in_int_t n = 20;
  CALL_KERNEL(memsum, a, n);
  return 0;
}
