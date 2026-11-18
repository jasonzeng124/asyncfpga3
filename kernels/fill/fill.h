#ifndef FILL_FILL_H
#define FILL_FILL_H
#define N 32
typedef int in_int_t;
typedef int inout_int_t;
/// Writes n values of a shift-xor-add sequence seeded by x into a[], at the
/// indices 3, 10, 17, ... (step 7 mod N, so n > N overwrites), and returns the
/// sum of the values shifted right by 3.  Defined for every n and x (int
/// arithmetic wraps: the oracle compiles with -fwrapv); n <= 0 writes nothing.
int fill(inout_int_t a[N], in_int_t n, in_int_t x);
#endif
