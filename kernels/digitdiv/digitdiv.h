#ifndef DIGITDIV_DIGITDIV_H
#define DIGITDIV_DIGITDIV_H
typedef int in_int_t;
/// Sum of the base-b digits of x (as unsigned), each digit as v - (v / b) * b: a division and no modulo.
int digitdiv(in_int_t x, in_int_t base);
#endif
