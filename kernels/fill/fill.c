//===- fill.c - a loop that writes memory ---------------------------*- C -*-===//
//
// WHY THIS KERNEL (stores, 2026-11-18; PROGRAM "A benchmark suite for the compiler": "memory: ... write"): the
// smallest loop with a STORE, so the flow must lower a store accessor and its completion obligation (the controller's
// memEnd only after every store of the call has landed; research/data/suite/stores.md).  One array, one store, no
// load: the store is the controller's only accessor (bdc's plain port, plus the bench's host slot).  The address is
// loop-carried and not the induction variable (3, 10, 17, ... step 7 mod N), the value a data-dependent sequence, and
// n > N writes some elements twice (the later write must win); elements it does not reach keep their contents.  The
// result is returned so the bench (which completes a call on out0) can run it.
//
//===----------------------------------------------------------------------===//
#include "fill.h"
#include "dynamatic/Integration.h"

int fill(inout_int_t a[N], in_int_t n, in_int_t x) {
  int s = 0;
  int j = 3;
  for (int i = 0; i < n; i++) {
    x = (x ^ (x << 5)) + i;
    a[j] = x;
    s = s + (x >> 3);
    j = (j + 7) & (N - 1);
  }
  return s;
}

int main(void) {
  inout_int_t a[N];
  for (int i = 0; i < N; i++) a[i] = 5 * i - 11;
  in_int_t n = 20;
  in_int_t x = 12345;
  CALL_KERNEL(fill, a, n, x);
  return 0;
}
