#ifndef VARSHIFT_VARSHIFT_H
#define VARSHIFT_VARSHIFT_H
typedef int in_int_t;
/// n rounds of a mix whose shift amounts (left, logical right, arithmetic right) come from the state.
int varshift(in_int_t x, in_int_t n);
#endif
