#include <stdlib.h>
#include <cstdint>

float FailAvRule23() {
  const char number_string[] = "10";
  auto a = atof(number_string);
  auto b = atoi(number_string);
  auto c = atol(number_string);
  return a + b + c;
}