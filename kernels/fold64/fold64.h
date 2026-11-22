#ifndef FOLD64_FOLD64_H
#define FOLD64_FOLD64_H
typedef long long in_int_t;
/// Low byte of v rounds of a 64-bit add / shift / compare mix of v; returns the two halves xor-folded.
int fold64(in_int_t v);
#endif
