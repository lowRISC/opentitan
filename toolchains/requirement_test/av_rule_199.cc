#include <cstdint>

void NoOp() { return; }

uint32_t FailAvRule199() {
  for (uint32_t i = 0; i < 0; NoOp()) {
  }
  return 1;
}