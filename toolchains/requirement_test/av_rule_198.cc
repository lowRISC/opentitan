#include <cstdint>

void NoOp() { return; }

uint32_t FailAvRule198() {
  for (NoOp();;) {
  }
  return 1;
}