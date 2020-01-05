
#include <cstdint>

/**
 * @brief Should not pass runtime compiler checks for AV Rule 3 on cyclomatic
 * complexity
 *
 * Reference: http://www.stroustrup.com/JSF-AV-rules.pdf
 *
 * @param a
 * @param b
 * @param c
 */
void FailAvRule3(uint8_t a, uint8_t b, uint8_t c) {
  if (a > 0)  // 1
  {
    if (b)  // 2
    {
    }
    for (int32_t i(0); i < a; ++i)  // 3
    {
    }
    if (c)  // 4
    {
    }
  } else if (0 == a)  // 5
  {
    if (b)  // 6
    {
    }
    if (c)  // 7
    {
    }
  } else if (b > 0) {
    if (a)  // 8
    {
    }
    if (c)  // 9
    {
    }
  } else if (b == 0) {
    if (a)  // 10
    {
    }
    if (c)  // 11
    {
    }
  } else {
    if (c)  // 12
    {
    }
    for (int32_t i(-a - 1); i >= 0; --i)  // 13
    {
    }
    if (b)  // 14
    {
    }
  }

  if (b > 0) {   // 15
    if (a == 0)  // 16
    {
    }
    if (c == 0)  // 17
    {
    }
    if (a < 0)  // 18
    {
    }
    if (c > 0)  // 19
    {
    }
  }
  // Non-Compliant: STCYC = #decisions + 1 = 20
}