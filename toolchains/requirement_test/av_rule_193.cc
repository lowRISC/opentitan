#include <cstdint>

uint32_t FailAvRule193(uint8_t a) {
  uint32_t result = 0;
  switch (a) {
    case 0:
      result = 1;
      // No break statement, fallthrough
    default:
      result = 2;
      break;
  }
  return result;
}