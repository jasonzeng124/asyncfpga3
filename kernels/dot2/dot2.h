#ifndef DOT2_DOT2_H
#define DOT2_DOT2_H
#define N 32
typedef int in_int_t;
/// Dot product of the first n entries of a and b, n clamped to N (n <= 0: no iteration, 0).
/// Input range (the C is defined): n any int; every a[i], b[i] in [-8191, 8191]
/// (32 * 8191 * 8191 = 2146959392 <= INT_MAX, so no partial sum overflows).
int dot2(in_int_t a[N], in_int_t b[N], in_int_t n);
#endif
