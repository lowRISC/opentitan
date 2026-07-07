// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// Register definitions
#define OTP_CTRL_BASE_ADDR TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR
#define OTP_CTRL_STATUS_REG_OFFSET 0x10
#define OTP_CTRL_STATUS_DAI_IDLE_BIT 18

#define OTP_CTRL_DIRECT_ACCESS_CMD_REG_OFFSET 0x4c
#define OTP_CTRL_DIRECT_ACCESS_CMD_WR_BIT 1
#define OTP_CTRL_DIRECT_ACCESS_CMD_DIGEST_BIT 2

#define OTP_CTRL_DIRECT_ACCESS_ADDRESS_REG_OFFSET 0x50
#define OTP_CTRL_DIRECT_ACCESS_WDATA_0_REG_OFFSET 0x54

#define OTP_CTRL_SECRET1_DIGEST_0_REG_OFFSET 0xd0
#define OTP_CTRL_SECRET1_DIGEST_1_REG_OFFSET 0xd4

#define OTP_CTRL_PARAM_SECRET1_OFFSET 1784
#define OTP_CTRL_PARAM_FLASH_DATA_KEY_SEED_OFFSET 1816

#define UART_STATUS_REG_OFFSET 0x14
#define UART_STATUS_TXFULL_BIT 0
#define UART_WDATA_REG_OFFSET 0x1c

static void uart_putchar(char c) {
  while (*((volatile uint32_t *)(TOP_EARLGREY_UART0_BASE_ADDR +
                                 UART_STATUS_REG_OFFSET)) &
         (1 << UART_STATUS_TXFULL_BIT)) {
  }
  *((volatile uint32_t *)(TOP_EARLGREY_UART0_BASE_ADDR +
                          UART_WDATA_REG_OFFSET)) = (uint32_t)c;
}

static void uart_write_imm(const char *str) {
  while (*str) {
    uart_putchar(*str++);
  }
}

static inline void wait_for_interrupt(void) { __asm__ volatile("wfi"); }

// Helper function to read/write registers directly
static inline uint32_t reg_read(uint32_t offset) {
  return *((volatile uint32_t *)(OTP_CTRL_BASE_ADDR + offset));
}

static inline void reg_write(uint32_t offset, uint32_t val) {
  *((volatile uint32_t *)(OTP_CTRL_BASE_ADDR + offset)) = val;
}

static void wait_for_dai_idle(void) {
  while (!(reg_read(OTP_CTRL_STATUS_REG_OFFSET) &
           (1 << OTP_CTRL_STATUS_DAI_IDLE_BIT)))
    ;
}

static void dai_write32(uint32_t addr, uint32_t val) {
  wait_for_dai_idle();
  reg_write(OTP_CTRL_DIRECT_ACCESS_ADDRESS_REG_OFFSET, addr);
  reg_write(OTP_CTRL_DIRECT_ACCESS_WDATA_0_REG_OFFSET, val);
  reg_write(OTP_CTRL_DIRECT_ACCESS_CMD_REG_OFFSET,
            (1 << OTP_CTRL_DIRECT_ACCESS_CMD_WR_BIT));
  wait_for_dai_idle();
}

static void lock_secret1_partition(void) {
  wait_for_dai_idle();
  reg_write(OTP_CTRL_DIRECT_ACCESS_ADDRESS_REG_OFFSET,
            OTP_CTRL_PARAM_SECRET1_OFFSET);
  reg_write(OTP_CTRL_DIRECT_ACCESS_CMD_REG_OFFSET,
            (1 << OTP_CTRL_DIRECT_ACCESS_CMD_DIGEST_BIT));
  wait_for_dai_idle();
}

int main(void) {
  // Check if SECRET1 partition is already locked (digest is non-zero)
  uint32_t digest0 = reg_read(OTP_CTRL_SECRET1_DIGEST_0_REG_OFFSET);
  uint32_t digest1 = reg_read(OTP_CTRL_SECRET1_DIGEST_1_REG_OFFSET);

  if (digest0 == 0 && digest1 == 0) {
    // Write 128-bit scrambling key to SECRET1 partition (4 x 32-bit words
    // starting at address 1816)
    uint32_t mock_key[4] = {0x01234567, 0x89ABCDEF, 0xFEDCBA98, 0x76543210};
    for (uint32_t i = 0; i < 4; i++) {
      dai_write32(
          (uint32_t)OTP_CTRL_PARAM_FLASH_DATA_KEY_SEED_OFFSET + (i * 4u),
          mock_key[i]);
    }

    // Lock SECRET1 partition (calculates digest and disables write access)
    lock_secret1_partition();
  }

  // Print bootstrap trigger signature to UART using Mask ROM's uart_write_imm
  // function
  uart_write_imm("Bootstrap requested.\n");

  // Sleep and wait for external reset
  wait_for_interrupt();

  return 0;
}
