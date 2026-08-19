#ifndef XORSHIFT_XORSHIFT_H
#define XORSHIFT_XORSHIFT_H

typedef int in_int_t;

/// Advance Marsaglia's xorshift32 generator `rounds` times from `seed`.
int xorshift(in_int_t seed, in_int_t rounds);

#endif // XORSHIFT_XORSHIFT_H
