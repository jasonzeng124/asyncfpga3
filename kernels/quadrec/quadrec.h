#ifndef QUADREC_QUADREC_H
#define QUADREC_QUADREC_H
typedef int in_int_t;
/// n steps of a four-term recurrence (a, b, c, d) <- (b, c, d, a + (b ^ c) + (d >> 3)) seeded by x.
int quadrec(in_int_t x, in_int_t n);
#endif
