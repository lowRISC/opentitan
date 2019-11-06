// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _COMMON_H_
#define _COMMON_H_

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#ifdef SIMULATION
#define CLK_FIXED_FREQ_HZ (500 * 1000)
static const unsigned long UART_BAUD_RATE = 9600;
#else
#define CLK_FIXED_FREQ_HZ (50ULL * 1000 * 1000)
static const unsigned long UART_BAUD_RATE = 230400;
#endif

// Flash memory base defines, _SZ are presented in bytes
#define FLASH_MEM_BASE_ADDR 0x20000000
#define FLASH_WORDS_PER_PAGE 256
#define FLASH_WORD_SZ 4
#define FLASH_PAGE_SZ FLASH_WORDS_PER_PAGE *FLASH_WORD_SZ
#define FLASH_PAGES_PER_BANK 256
#define FLASH_BANK_SZ FLASH_PAGES_PER_BANK *FLASH_PAGE_SZ

#define REG8(add) *((volatile uint8_t *)(add))
#define REG16(add) *((volatile uint16_t *)(add))
#define REG32(add) *((volatile uint32_t *)(add))
#define SETBIT(val, bit) (val | 1 << bit)
#define CLRBIT(val, bit) (val & ~(1 << bit))

#define ARRAYSIZE(x) (sizeof(x) / sizeof(x[0]))

/* Hamming weight */
#define BITLENGTH_1(X) ((X) - (((X) >> 1) & 0x55555555))
#define BITLENGTH_2(X) (((X)&0x33333333) + (((X) >> 2) & 0x33333333))
#define BITLENGTH_3(X) (((X) + ((X) >> 4)) & 0x0f0f0f0f)
#define BITLENGTH_4(X) ((X) + ((X) >> 8))
#define BITLENGTH_5(X) ((X) + ((X) >> 16))
#define BITLENGTH(X) \
  ((BITLENGTH_5(BITLENGTH_4(BITLENGTH_3(BITLENGTH_2(BITLENGTH_1(X)))))) & 0x7f)

void *memcpy(void *restrict dest, const void *restrict src, size_t n);
void *memset(void *dest, int val, size_t n);

size_t strlen(const char *s);

#endif
