#include <cstdint>

void FailAvRule188_189() {
  uint8_t a = 1;
evil_label:
  goto evil_label;
}