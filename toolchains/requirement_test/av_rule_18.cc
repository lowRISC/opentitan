#include <stddef.h>
#include <cstdint>

struct S {
  char c;
  double d;
};

uint8_t FailsAvRule18() { return offsetof(S, d); }