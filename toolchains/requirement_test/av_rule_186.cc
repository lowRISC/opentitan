#include <cstdint>

uint32_t FailAvRule186() {
  uint32_t a = 0;
  if (false) {
    a++;  // Unreachable code
  }
  return a;
}