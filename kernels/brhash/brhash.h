#ifndef BRHASH_BRHASH_H
#define BRHASH_BRHASH_H
typedef int in_int_t;
/// n rounds of a hash whose step is one of two multi-operation arms, chosen by the state's low bit.
int brhash(in_int_t x, in_int_t n);
#endif
