#include <cstdint>

uint32_t FailAvRule135() {
  uint32_t var = 0;
  {
    // Var shadowing here
    uint32_t var = 1;
    return var;
  }
}