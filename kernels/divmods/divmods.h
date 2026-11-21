#ifndef DIVMODS_DIVMODS_H
#define DIVMODS_DIVMODS_H
typedef int in_int_t;
/// (a / b) ^ (a % b) with C's signed division; b != 0, not INT_MIN / -1.
int divmods(in_int_t a, in_int_t b);
#endif
