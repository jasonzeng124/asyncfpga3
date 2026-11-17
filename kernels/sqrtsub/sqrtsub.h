#ifndef SQRTSUB_SQRTSUB_H
#define SQRTSUB_SQRTSUB_H
typedef int in_int_t;
/// floor(sqrt(n)) for n >= 0 (0 for n < 0), by subtracting the odd numbers 1, 3, 5, ... from n.
int sqrtsub(in_int_t n);
#endif
