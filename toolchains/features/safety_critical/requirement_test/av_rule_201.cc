#include <cstdint>

void FailAvRule201() {
  for (uint32_t i = 0; i < 2; i++) {
    i += 2;  // Iterator modified in loop
  }
}