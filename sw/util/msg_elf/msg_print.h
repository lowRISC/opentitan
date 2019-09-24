// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _MSG_PRINT_H_
#define _MSG_PRINT_H_

#include <stdarg.h>

#define _xstr(a) _str(a)
#define _str(a) #a
#define CONCAT1(a, b) a##b
#define CONCAT2(a, b) CONCAT1(a, b)
#define VA_ARGS(...) , ##__VA_ARGS__

// SW msg addr
#ifndef SW_MSG_ADDR
#define SW_MSG_ADDR 0x1000fff4
#endif

// VA_ARGS metaprogramming to allow for upto 24 arguments
#define VA_ARGS(...) , ##__VA_ARGS__
#define ___VA_NARGS(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12,    \
                    x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, n, \
                    ...)                                                      \
  n
#define __VA_NARGS(...) ___VA_NARGS(__VA_ARGS__)
#define _VA_NARGS(...)                                                        \
  __VA_NARGS(__VA_ARGS__, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, \
             10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0)
#define VA_NARGS(...) _VA_NARGS(0 VA_ARGS(__VA_ARGS__))

#define _WR_VA_ARG0()

#define _WR_VA_ARG1(d1) REG32(SW_MSG_ADDR) = d1;

#define _WR_VA_ARG2(d1, d2) \
  _WR_VA_ARG1(d1)           \
  _WR_VA_ARG1(d2)

#define _WR_VA_ARG3(d1, d2, d3) \
  _WR_VA_ARG1(d1)               \
  _WR_VA_ARG2(d2, d3)

#define _WR_VA_ARG4(d1, d2, d3, d4) \
  _WR_VA_ARG2(d1, d2)               \
  _WR_VA_ARG2(d3, d4)

#define _WR_VA_ARG5(d1, d2, d3, d4, d5) \
  _WR_VA_ARG2(d1, d2)                   \
  _WR_VA_ARG3(d3, d4, d5)

#define _WR_VA_ARG6(d1, d2, d3, d4, d5, d6) \
  _WR_VA_ARG3(d1, d2, d3)                   \
  _WR_VA_ARG3(d4, d5, d6)

#define _WR_VA_ARG7(d1, d2, d3, d4, d5, d6, d7) \
  _WR_VA_ARG3(d1, d2, d3)                       \
  _WR_VA_ARG4(d4, d5, d6, d7)

#define _WR_VA_ARG8(d1, d2, d3, d4, d5, d6, d7, d8) \
  _WR_VA_ARG4(d1, d2, d3, d4)                       \
  _WR_VA_ARG4(d5, d6, d7, d8)

#define _WR_VA_ARG9(d1, d2, d3, d4, d5, d6, d7, d8, d9) \
  _WR_VA_ARG4(d1, d2, d3, d4)                           \
  _WR_VA_ARG5(d5, d6, d7, d8, d9)

#define _WR_VA_ARG10(d1, d2, d3, d4, d5, d6, d7, d8, d9, d10) \
  _WR_VA_ARG5(d1, d2, d3, d4, d5)                             \
  _WR_VA_ARG5(d6, d7, d8, d9, d10)

#define _WR_VA_ARG11(d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11) \
  _WR_VA_ARG5(d1, d2, d3, d4, d5)                                  \
  _WR_VA_ARG6(d6, d7, d8, d9, d10, d11)

#define _WR_VA_ARG12(d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12) \
  _WR_VA_ARG6(d1, d2, d3, d4, d5, d6)                                   \
  _WR_VA_ARG6(d7, d8, d9, d10, d11, d12)

#define _WR_VA_ARG13(d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13) \
  _WR_VA_ARG6(d1, d2, d3, d4, d5, d6)                                        \
  _WR_VA_ARG7(d7, d8, d9, d10, d11, d12, d13)

#define _WR_VA_ARG14(d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, \
                     d14)                                                    \
  _WR_VA_ARG7(d1, d2, d3, d4, d5, d6, d7)                                    \
  _WR_VA_ARG7(d8, d9, d10, d11, d12, d13, d14)

#define _WR_VA_ARG15(d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, \
                     d14, d15)                                               \
  _WR_VA_ARG7(d1, d2, d3, d4, d5, d6, d7)                                    \
  _WR_VA_ARG8(d8, d9, d10, d11, d12, d13, d14, d15)

#define _WR_VA_ARG16(d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, \
                     d14, d15, d16)                                          \
  _WR_VA_ARG8(d1, d2, d3, d4, d5, d6, d7, d8)                                \
  _WR_VA_ARG8(d9, d10, d11, d12, d13, d14, d15, d16)

#define _WR_VA_ARG17(d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, \
                     d14, d15, d16, d17)                                     \
  _WR_VA_ARG8(d1, d2, d3, d4, d5, d6, d7, d8)                                \
  _WR_VA_ARG9(d9, d10, d11, d12, d13, d14, d15, d16, d17)

#define _WR_VA_ARG18(d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, \
                     d14, d15, d16, d17, d18)                                \
  _WR_VA_ARG9(d1, d2, d3, d4, d5, d6, d7, d8, d9)                            \
  _WR_VA_ARG9(d10, d11, d12, d13, d14, d15, d16, d17, d18)

#define _WR_VA_ARG19(d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, \
                     d14, d15, d16, d17, d18, d19)                           \
  _WR_VA_ARG9(d1, d2, d3, d4, d5, d6, d7, d8, d9)                            \
  _WR_VA_ARG10(d10, d11, d12, d13, d14, d15, d16, d17, d18, d19)

#define _WR_VA_ARG20(d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, \
                     d14, d15, d16, d17, d18, d19, d20)                      \
  _WR_VA_ARG10(d1, d2, d3, d4, d5, d6, d7, d8, d9, d10)                      \
  _WR_VA_ARG10(d11, d12, d13, d14, d15, d16, d17, d18, d19, d20)

#define _WR_VA_ARG21(d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, \
                     d14, d15, d16, d17, d18, d19, d20, d21)                 \
  _WR_VA_ARG10(d1, d2, d3, d4, d5, d6, d7, d8, d9, d10)                      \
  _WR_VA_ARG11(d11, d12, d13, d14, d15, d16, d17, d18, d19, d20)

#define _WR_VA_ARG22(d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, \
                     d14, d15, d16, d17, d18, d19, d20, d21, d22)            \
  _WR_VA_ARG11(d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11)                 \
  _WR_VA_ARG11(d12, d13, d14, d15, d16, d17, d18, d19, d20, d21, d22)

#define _WR_VA_ARG23(d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, \
                     d14, d15, d16, d17, d18, d19, d20, d21, d22, d23)       \
  _WR_VA_ARG11(d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11)                 \
  _WR_VA_ARG12(d12, d13, d14, d15, d16, d17, d18, d19, d20, d21, d22, d23)

#define _WR_VA_ARG24(d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, \
                     d14, d15, d16, d17, d18, d19, d20, d21, d22, d23, d24)  \
  _WR_VA_ARG12(d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12)            \
  _WR_VA_ARG12(d13, d14, d15, d16, d17, d18, d19, d20, d21, d22, d23, d24)

#define _WR_VA_ARG_(N, ...) N(__VA_ARGS__)

#define _WR_VA_ARG_N(...) \
  _WR_VA_ARG_(CONCAT2(_WR_VA_ARG, VA_NARGS(__VA_ARGS__)), __VA_ARGS__)

// The following set of macros are used by the standard msg print macro
// flavors in ../msg.h

/** print the final msg consisting of header and the msg string
 *
 * calls msg_print() function to process formatted string and insert args
 * uses UART to pring msg string character by character
 * Do not invoke this macro directly; use  the standard
 */
#define MSG_PRINT(msg_header, fmt, ...)                             \
  do {                                                              \
    static const char msg[] __attribute__((section(".msg_data"))) = \
        "\\" msg_header "\\" _xstr(VA_NARGS(__VA_ARGS__)) "\\" fmt; \
    REG32(SW_MSG_ADDR) = (uint32_t)msg;                             \
    _WR_VA_ARG_N(__VA_ARGS__)                                       \
  } while (0)

/** set msg_header string with type, verbosity, file and line
 *
 * This macro sets the msg_header to
 * \type\verbosity\file\line
 */
#define MSG_HEADER(msg_type, verbosity) \
  msg_type "\\" verbosity "\\" __FILE__ "\\" _xstr(__LINE__)

/** msg type amd verbosity strings
 */
#define MSG_TYPE_INFO "i"
#define MSG_TYPE_WARNING "w"
#define MSG_TYPE_ERROR "e"
#define MSG_TYPE_FATAL "f"
#define MSG_VERB_NONE "l"
#define MSG_VERB_LOW "l"
#define MSG_VERB_MEDIUM "m"
#define MSG_VERB_HIGH "h"
#define MSG_VERB_FULL "f"
#define MSG_VERB_DEBUG "d"

#endif  // _MSG_PRINT_H_
