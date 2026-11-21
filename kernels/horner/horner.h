#ifndef HORNER_HORNER_H
#define HORNER_HORNER_H
typedef int in_int_t;
/// Horner evaluation at x of the degree n-1 polynomial with coefficients (i ^ 0x5a), mod 2^32.
int horner(in_int_t x, in_int_t n);
#endif
