// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_COMMON_H_
#define OPENTITAN_SW_DEVICE_LIB_COMMON_H_

#ifdef SIMULATION
static const unsigned long UART_BAUD_RATE = 9600;
#else
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

#endif  // OPENTITAN_SW_DEVICE_LIB_COMMON_H_
