#ifndef TWOLOOPS_TWOLOOPS_H
#define TWOLOOPS_TWOLOOPS_H
typedef int in_int_t;
/// Loop 1 mixes a for n rounds; loop 2 runs (its result & 255) rounds of a second mix on it.
int twoloops(in_int_t a, in_int_t n);
#endif
