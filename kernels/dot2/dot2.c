//===- dot2.c - a loop that reads two arrays ------------------------*- C -*-===//
//
// WHY THIS KERNEL (suitew, 2026-11-17; PROGRAM "A benchmark suite for the compiler", memory shapes: "two arrays"):
// memsum with its weight read from a second array.  Each array has its own mem_controller and its own load in the
// same ring, so the two loads of one iteration are in flight together and their data must meet at the multiply.
// Input range in dot2.h.
//
//===----------------------------------------------------------------------===//
#include "dot2.h"
#include "dynamatic/Integration.h"

int dot2(in_int_t a[N], in_int_t b[N], in_int_t n) {
  int s = 0;
  for (int i = 0; i < n && i < N; i++)
    s = s + a[i] * b[i];
  return s;
}

int main(void) {
  in_int_t a[N];
  in_int_t b[N];
  for (int i = 0; i < N; i++) {
    a[i] = 3 * i - 7;
    b[i] = 50 - 5 * i;
  }
  in_int_t n = 20;
  CALL_KERNEL(dot2, a, b, n);
  return 0;
}
