#ifndef COUNTLOOP_COUNTLOOP_H
#define COUNTLOOP_COUNTLOOP_H
typedef int in_int_t;
/// s = (s + i) ^ a for i = 0 .. n-1, from s = 0 (unsigned arithmetic).
int countloop(in_int_t a, in_int_t n);
#endif
