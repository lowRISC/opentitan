// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/dbg_print.h"

#include <assert.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/csr.h"
#include "sw/device/silicon_creator/lib/drivers/uart.h"
#include "sw/device/silicon_creator/lib/epmp_defs.h"

void print_integer(unsigned value, bool is_signed) {
  char buf[12];
  char *b = buf + sizeof(buf);
  if (is_signed && (int)value < 0) {
    uart_putchar('-');
    value = (unsigned)(-(int)value);
  }
  *--b = '\0';
  do {
    *--b = '0' + value % 10;
    value /= 10;
  } while (value);
  while (*b) {
    uart_putchar(*b++);
  }
}

void dbg_printf(const char *format, ...) {
  va_list args;
  va_start(args, format);

  for (; *format != '\0'; ++format) {
    if (*format != '%') {
      uart_putchar(*format);
      continue;
    }

    ++format;  // Skip over the '%'.
    switch (*format) {
      case '%':
        uart_putchar(*format);
        break;
      case 'c': {
        int ch = va_arg(args, int);
        uart_putchar((char)ch);
        break;
      }
      case 's': {
        // Print a null-terminated string.
        const char *str = va_arg(args, const char *);
        while (*str != '\0') {
          uart_putchar(*str++);
        }
        break;
      }
      case 'd':
        // `print_integer` will handle the sign bit of the value.
        print_integer(va_arg(args, unsigned), true);
        break;
      case 'u':
        print_integer(va_arg(args, unsigned), false);
        break;
      case 'p':
        OT_FALLTHROUGH_INTENDED;
      case 'x': {
        // Print an `unsigned int` in hexadecimal.
        static const char kHexTable[16] = "0123456789abcdef";
        unsigned int v = va_arg(args, unsigned int);
        for (int i = 0; i < sizeof(v) * 2; ++i) {
          int shift = sizeof(v) * 8 - 4;
          uart_putchar(kHexTable[v >> shift]);
          v <<= 4;
        }
        break;
      }
      default:
        // For an invalid format specifier, back up one char and allow the
        // output via the normal mechanism.
        uart_putchar('%');
        --format;
    }
  }
  va_end(args);
}

void dbg_print_epmp(void) {
  uint32_t pmpaddr[16];
  uint32_t pmpcfg[4];
  uint32_t mseccfg;
  uint8_t *cfg = (uint8_t *)pmpcfg;

  // Get address registers.
  CSR_READ(CSR_REG_PMPADDR0, &pmpaddr[0]);
  CSR_READ(CSR_REG_PMPADDR1, &pmpaddr[1]);
  CSR_READ(CSR_REG_PMPADDR2, &pmpaddr[2]);
  CSR_READ(CSR_REG_PMPADDR3, &pmpaddr[3]);
  CSR_READ(CSR_REG_PMPADDR4, &pmpaddr[4]);
  CSR_READ(CSR_REG_PMPADDR5, &pmpaddr[5]);
  CSR_READ(CSR_REG_PMPADDR6, &pmpaddr[6]);
  CSR_READ(CSR_REG_PMPADDR7, &pmpaddr[7]);
  CSR_READ(CSR_REG_PMPADDR8, &pmpaddr[8]);
  CSR_READ(CSR_REG_PMPADDR9, &pmpaddr[9]);
  CSR_READ(CSR_REG_PMPADDR10, &pmpaddr[10]);
  CSR_READ(CSR_REG_PMPADDR11, &pmpaddr[11]);
  CSR_READ(CSR_REG_PMPADDR12, &pmpaddr[12]);
  CSR_READ(CSR_REG_PMPADDR13, &pmpaddr[13]);
  CSR_READ(CSR_REG_PMPADDR14, &pmpaddr[14]);
  CSR_READ(CSR_REG_PMPADDR15, &pmpaddr[15]);

  // Get configuration registers.
  CSR_READ(CSR_REG_PMPCFG0, &pmpcfg[0]);
  CSR_READ(CSR_REG_PMPCFG1, &pmpcfg[1]);
  CSR_READ(CSR_REG_PMPCFG2, &pmpcfg[2]);
  CSR_READ(CSR_REG_PMPCFG3, &pmpcfg[3]);

  // Get mseccfg.
  CSR_READ(CSR_REG_MSECCFG, &mseccfg);

  for (int i = 0; i < 16; ++i) {
    uint32_t mode = cfg[i] & EPMP_CFG_A_MASK;
    uint32_t addr = pmpaddr[i];
    uint32_t size = 0;
    if (mode == EPMP_CFG_A_NAPOT) {
      size = 1 << bitfield_count_trailing_zeroes32(~addr);
      addr = addr & ~(size - 1);
      size <<= 3;
    } else if (mode == EPMP_CFG_A_TOR) {
      size = (addr - pmpaddr[i - 1]) << 2;
    } else if (mode == EPMP_CFG_A_NA4) {
      size = 4;
    }
    addr <<= 2;
    dbg_printf("%d: %x %s %c%c%c%c sz=%x\r\n", i, addr,
               (mode == EPMP_CFG_A_TOR)     ? "  TOR"
               : (mode == EPMP_CFG_A_NA4)   ? "  NA4"
               : (mode == EPMP_CFG_A_NAPOT) ? "NAPOT"
                                            : "-----",
               cfg[i] & EPMP_CFG_L ? 'L' : '-', cfg[i] & EPMP_CFG_X ? 'X' : '-',
               cfg[i] & EPMP_CFG_W ? 'W' : '-', cfg[i] & EPMP_CFG_R ? 'R' : '-',
               size);
  }
  dbg_printf("mseccfg = %x\r\n", mseccfg);
}
