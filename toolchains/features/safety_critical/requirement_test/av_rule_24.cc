#include <stdlib.h>
#include <cstdint>

void FailAvRule24() {
  auto env = getenv("A");
  abort();
  exit(1);
}