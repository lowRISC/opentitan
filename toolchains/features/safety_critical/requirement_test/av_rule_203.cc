#include <cstdint>

void FailAvRule203() {
  uint8_t a = 255;
  a++;
  a = 0;
  a--;
}