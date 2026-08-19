// 64-bit collatz. Same kernel as collatz, widened, to answer one question:
// is the backend width-generic, or is 32 baked in? A 32-bit collatz overflows
// at n=113383 (the first n whose trajectory leaves int32), which is a real
// ceiling on the inputs worth testing, so this is worth knowing.
#include "collatz64.h"
#include "dynamatic/Integration.h"

int collatz64(in_int_t n) {
  int steps = 0;

  while (n != 1) {
    if ((n & 1) == 0)
      n = n >> 1;
    else
      n = 3 * n + 1;
    steps = steps + 1;
  }

  return steps;
}

int main(void) {
  in_int_t n = 27;
  CALL_KERNEL(collatz64, n);
  return 0;
}
