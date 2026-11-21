#ifndef DIVMODU_DIVMODU_H
#define DIVMODU_DIVMODU_H
typedef int in_int_t;
/// (a / b) + 2 * (a % b) on the operands read as unsigned; b != 0.
int divmodu(in_int_t a, in_int_t b);
#endif
