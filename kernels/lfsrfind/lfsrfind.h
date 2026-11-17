#ifndef LFSRFIND_LFSRFIND_H
#define LFSRFIND_LFSRFIND_H
typedef int in_int_t;
/// Steps of a 16-bit Galois LFSR from seed until it equals key (low 16 bits of each); 256 if not found.
int lfsrfind(in_int_t seed, in_int_t key);
#endif
