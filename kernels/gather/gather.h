#ifndef GATHER_GATHER_H
#define GATHER_GATHER_H
#define N 32
typedef int in_int_t;
/// Weighted sum over the first n entries of b of a[b[i]] * (i + 1), n clamped to N (n <= 0: no iteration, 0).
/// Input range (the C is defined): n any int; every b[i] in [0, N - 1] (an index outside it reads outside a: UB);
/// every a[j] in [-2^21, 2^21] (2^21 * (1 + 2 + ... + 32) = 1107296256 <= INT_MAX).
int gather(in_int_t a[N], in_int_t b[N], in_int_t n);
#endif
