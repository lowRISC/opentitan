#include <cstdint>

uint32_t FailAvRule162() {
  uint8_t a = 5;
  int8_t b = 6;
  if (a > b) {     // Mixing of signed and unsigned comparison operations
    return a - b;  // Mixing of signed and unsigned arithmetic operations
  }
  return a;
}