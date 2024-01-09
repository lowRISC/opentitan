// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom/bootstrap.h"

#include <string.h>

#include "sw/device/silicon_creator/lib/drivers/otp.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/lib/drivers/spi_device.h"
#include "sw/lib/sw/device/base/abs_mmio.h"
#include "sw/lib/sw/device/base/bitfield.h"
#include "sw/lib/sw/device/base/hardened.h"
#include "sw/lib/sw/device/silicon_creator/base/chip.h"
#include "sw/lib/sw/device/silicon_creator/error.h"

#include "gpio_regs.h"
#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"
#include "otp_ctrl_regs.h"

enum {
  /*
   * Maximum ctn sram address, exclusive.
   */
  kMaxAddress = TOP_DARJEELING_RAM_CTN_SIZE_BYTES,
};

/**
 * Bootstrap states.
 *
 * OpenTitan bootstrap consists of three states between which the chip
 * transitions sequentially.
 *
 * Encoding generated with
 * $ ./util/design/sparse-fsm-encode.py -d 5 -m 3 -n 32 \
 *     -s 375382971 --language=c
 *
 * Minimum Hamming distance: 17
 * Maximum Hamming distance: 19
 * Minimum Hamming weight: 16
 * Maximum Hamming weight: 19
 */
typedef enum bootstrap_state {
  /**
   * Initial bootstrap state where the chip waits for a SECTOR_ERASE or
   * CHIP_ERASE command.
   */
  kBootstrapStateErase = 0xd4576543,
  /**
   * Second bootstrap state where the chip verifies that all data banks have
   * been erased.
   */
  kBootstrapStateEraseVerify = 0xf3c71bac,
  /**
   * Final bootstrap state. This is the main program loop where the chip handles
   * erase, program, and reset commands.
   */
  kBootstrapStateProgram = 0xbdd8ca60,
} bootstrap_state_t;

/**
 * Handles access permissions and erases both data banks of the ctn sram.
 *
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
static rom_error_t bootstrap_chip_erase(void) {
  memset((void *)TOP_DARJEELING_RAM_CTN_BASE_ADDR,
         0x0, TOP_DARJEELING_RAM_CTN_SIZE_BYTES);

  return kErrorOk;
}

/**
 * Handles access permissions and erases a 4 KiB region in the data partition of
 * the ctn sram.
 *
 * @param addr Address that falls within the 4 KiB region being deleted.
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
static rom_error_t bootstrap_sector_erase(uint32_t addr) {
  enum {
    /**
     * Mask for truncating `addr` to the lower 4 KiB aligned address.
     */
    kPageAddrMask = ~UINT32_C(4096) + 1,
  };

  if (addr >= kMaxAddress) {
    return kErrorBootstrapEraseAddress;
  }
  addr &= kPageAddrMask;

  memset((void *)(TOP_DARJEELING_RAM_CTN_BASE_ADDR + addr), 0x0, 4096);

  return kErrorOk;
}

/**
 * Handles access permissions and programs up to 256 bytes of memory
 * starting at `addr`.
 *
 * @param addr Address to write to data into memory.
 * @param byte_count Number of bytes to write into memory.
 * @param data Data to write into memory.
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
static rom_error_t bootstrap_page_program(uint32_t addr, size_t byte_count,
                                          uint8_t *data) {
  if (addr + byte_count >= kMaxAddress) {
    return kErrorBootstrapProgramAddress;
  }
  memcpy((void *)addr, data, byte_count);
  return kErrorOk;
}

/**
 * Bootstrap state 1: Wait for an erase command and erase the data
 * partition.
 *
 * @param state Bootstrap state.
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
static rom_error_t bootstrap_handle_erase(bootstrap_state_t *state) {
  HARDENED_CHECK_EQ(*state, kBootstrapStateErase);

  spi_device_cmd_t cmd;
  RETURN_IF_ERROR(spi_device_cmd_get(&cmd));
  // Erase requires WREN, ignore if WEL is not set.
  if (!bitfield_bit32_read(spi_device_flash_status_get(), kSpiDeviceWelBit)) {
    return kErrorOk;
  }

  rom_error_t error = kErrorUnknown;
  switch (cmd.opcode) {
    case kSpiDeviceOpcodeChipErase:
    case kSpiDeviceOpcodeSectorErase:
      error = bootstrap_chip_erase();
      HARDENED_RETURN_IF_ERROR(error);
      *state = kBootstrapStateEraseVerify;
      // Note: We clear WIP and WEN bits in `bootstrap_handle_erase_verify()`
      // after checking that both data banks have been erased.
      break;
    default:
      // Ignore any other command, e.g. PAGE_PROGRAM, RESET, and clear WIP and
      // WEN bits right away.
      spi_device_flash_status_clear();
      error = kErrorOk;
  }

  return error;
}

/**
 * Bootstrap state 2: Verify that all data banks have been erased.
 *
 * This function also clears the WIP and WEN bits of the flash status register.
 *
 * @param state Bootstrap state.
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
static rom_error_t bootstrap_handle_erase_verify(bootstrap_state_t *state) {
  HARDENED_CHECK_EQ(*state, kBootstrapStateEraseVerify);

  memset((void *)TOP_DARJEELING_RAM_CTN_BASE_ADDR,
         0x0, TOP_DARJEELING_RAM_CTN_SIZE_BYTES);

  rom_error_t err_0 = kErrorOk;
  for (uint32_t i = 0; i < TOP_DARJEELING_RAM_CTN_SIZE_BYTES / 4; i++) {
    uint32_t zero = 0x0;
    if (!memcmp((void *)(TOP_DARJEELING_RAM_CTN_BASE_ADDR + 4 * i),
                (void *)zero, 4)) {
        err_0 = kErrorFlashCtrlDataEraseVerify;
        break;
    }
  }
  HARDENED_RETURN_IF_ERROR(err_0);

  *state = kBootstrapStateProgram;
  spi_device_flash_status_clear();
  return err_0;
}

/**
 * Bootstrap state 3: (Erase/)Program loop.
 *
 * @param state Bootstrap state.
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
static rom_error_t bootstrap_handle_program(bootstrap_state_t *state) {
  static_assert(alignof(spi_device_cmd_t) >= sizeof(uint32_t) &&
                    offsetof(spi_device_cmd_t, payload) >= sizeof(uint32_t),
                "Payload must be word aligned.");
  HARDENED_CHECK_EQ(*state, kBootstrapStateProgram);

  spi_device_cmd_t cmd;
  RETURN_IF_ERROR(spi_device_cmd_get(&cmd));
  // Erase and program require WREN, ignore if WEL is not set.
  if (cmd.opcode != kSpiDeviceOpcodeReset &&
      !bitfield_bit32_read(spi_device_flash_status_get(), kSpiDeviceWelBit)) {
    return kErrorOk;
  }

  rom_error_t error = kErrorUnknown;
  switch (cmd.opcode) {
    case kSpiDeviceOpcodeChipErase:
      error = bootstrap_chip_erase();
      break;
    case kSpiDeviceOpcodeSectorErase:
      error = bootstrap_sector_erase(cmd.address);
      break;
    case kSpiDeviceOpcodePageProgram:
      error = bootstrap_page_program(cmd.address, cmd.payload_byte_count,
                                     cmd.payload);
      break;
    case kSpiDeviceOpcodeReset:
      rstmgr_reset();
#ifdef OT_PLATFORM_RV32
      HARDENED_TRAP();
#else
      // If this is an off-target test, return `kErrorUnknown` to be able to
      // test without requiring EXPECT_DEATH.
      error = kErrorUnknown;
#endif
      break;
    default:
      // We don't expect any other commands but we can potentially end up
      // here with a 0x0 opcode due to glitches on SPI or strap lines (see
      // #11871).
      error = kErrorOk;
  }
  HARDENED_RETURN_IF_ERROR(error);

  spi_device_flash_status_clear();
  return error;
}

hardened_bool_t bootstrap_requested(void) {
  uint32_t bootstrap_dis =
      otp_read32(OTP_CTRL_PARAM_OWNER_SW_CFG_ROM_BOOTSTRAP_DIS_OFFSET);
  if (launder32(bootstrap_dis) == kHardenedBoolTrue) {
    return kHardenedBoolFalse;
  }
  HARDENED_CHECK_NE(bootstrap_dis, kHardenedBoolTrue);

  // A single read is sufficient since we expect strong pull-ups on the strap
  // pins.
  uint32_t res = launder32(kHardenedBoolTrue) ^ SW_STRAP_BOOTSTRAP;
  res ^=
      abs_mmio_read32(TOP_DARJEELING_GPIO_BASE_ADDR + GPIO_DATA_IN_REG_OFFSET) &
      SW_STRAP_MASK;
  if (launder32(res) != kHardenedBoolTrue) {
    return kHardenedBoolFalse;
  }
  HARDENED_CHECK_EQ(res, kHardenedBoolTrue);
  return res;
}

rom_error_t bootstrap(void) {
  hardened_bool_t requested = bootstrap_requested();
  if (launder32(requested) != kHardenedBoolTrue) {
    return kErrorBootstrapNotRequested;
  }
  HARDENED_CHECK_EQ(requested, kHardenedBoolTrue);

  spi_device_init();

  // Bootstrap event loop.
  bootstrap_state_t state = kBootstrapStateErase;
  rom_error_t error = kErrorUnknown;
  while (true) {
    switch (launder32(state)) {
      case kBootstrapStateErase:
        HARDENED_CHECK_EQ(state, kBootstrapStateErase);
        error = bootstrap_handle_erase(&state);
        break;
      case kBootstrapStateEraseVerify:
        HARDENED_CHECK_EQ(state, kBootstrapStateEraseVerify);
        error = bootstrap_handle_erase_verify(&state);
        break;
      case kBootstrapStateProgram:
        HARDENED_CHECK_EQ(state, kBootstrapStateProgram);
        error = bootstrap_handle_program(&state);
        break;
      default:
        error = kErrorBootstrapInvalidState;
    }
    HARDENED_RETURN_IF_ERROR(error);
  }
  HARDENED_TRAP();
}
