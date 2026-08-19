//===- collatz.h - Collatz stopping time --------------------------*- C -*-===//
//
// Declares the collatz kernel: how many halve/triple steps a number takes to
// reach 1.
//
//===----------------------------------------------------------------------===//

#ifndef COLLATZ_COLLATZ_H
#define COLLATZ_COLLATZ_H

typedef int in_int_t;

/// Number of Collatz steps needed to bring n down to 1.
int collatz(in_int_t n);

#endif // COLLATZ_COLLATZ_H
