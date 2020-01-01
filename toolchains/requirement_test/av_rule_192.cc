#include <cstdint>
uint32_t FailAvRule192(uint32_t a) {
  if (a) {
  } else if (a > 1) {
    return a;
  }  // No else
  return 0;
}