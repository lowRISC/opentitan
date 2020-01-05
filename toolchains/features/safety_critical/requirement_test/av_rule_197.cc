#include <cstdint>

uint32_t FailAvRule197(uint32_t a) {
  uint32_t result = 0;
  // float used as loop counter
  for (float i = 0.0; i < a; i += 1.0) {
    result++;
  }
  return result;
}