#ifndef MEMSUM_MEMSUM_H
#define MEMSUM_MEMSUM_H
#define N 32
typedef int in_int_t;
/// Weighted sum over the first n entries of a, a[i] * (i + 1), with n clamped to N.
int memsum(in_int_t a[N], in_int_t n);
#endif
