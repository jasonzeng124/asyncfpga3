#ifndef NEST3_NEST3_H
#define NEST3_NEST3_H
typedef int in_int_t;
/// Three-deep loop nest: i < a, j < b, k < ((i ^ j) & 3), mixing (i, j, k) into one accumulator.
int nest3(in_int_t a, in_int_t b);
#endif
