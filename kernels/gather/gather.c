//===- gather.c - a load whose address is read from memory ----------*- C -*-===//
//
// WHY THIS KERNEL (suitew, 2026-11-17; PROGRAM "A benchmark suite for the compiler", memory shapes: "an index read
// from memory", a[b[i]]): memsum with its address read from a second array.  The load of a cannot issue before the
// load of b has returned, so one iteration is two dependent memory round trips on two mem_controllers.
// Input range in gather.h.
//
//===----------------------------------------------------------------------===//
#include "gather.h"
#include "dynamatic/Integration.h"

int gather(in_int_t a[N], in_int_t b[N], in_int_t n) {
  int s = 0;
  for (int i = 0; i < n && i < N; i++)
    s = s + a[b[i]] * (i + 1);
  return s;
}

int main(void) {
  in_int_t a[N];
  in_int_t b[N];
  for (int i = 0; i < N; i++) {
    a[i] = 3 * i - 7;
    b[i] = (7 * i + 3) % N;
  }
  in_int_t n = 20;
  CALL_KERNEL(gather, a, b, n);
  return 0;
}
