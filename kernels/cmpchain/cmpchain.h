#ifndef CMPCHAIN_CMPCHAIN_H
#define CMPCHAIN_CMPCHAIN_H
typedef int in_int_t;
/// Classifies (x, y) by an if / else-if chain of seven signed and unsigned compares; class << 28 ^ (x - y).
int cmpchain(in_int_t x, in_int_t y);
#endif
