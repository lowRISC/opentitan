// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/bootstrap.h"

#include <assert.h>
#include <stdalign.h>
#include <stdint.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/lib/drivers/spi_device.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/nvm_ctrl.h"
#include "sw/device/silicon_creator/lib/stack_utilization.h"

enum {
  /*
   * Maximum flash address, exclusive.
   */
  kMaxAddress = NVM_DATA_SIZE_BYTES,
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
 * Handles access permissions and erases a 4 KiB region in the data partition of
 * the embedded flash.
 *
 * Since OpenTitan's flash page size is 2 KiB, this function erases two
 * consecutive pages.
 *
 * @param addr Address that falls within the 4 KiB region being deleted.
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
static rom_error_t bootstrap_sector_erase(uint32_t addr) {
  if (addr >= kMaxAddress) {
    return kErrorBootstrapEraseAddress;
  }
  return nvm_ctrl_sector_erase(addr);
}

/**
 * Handles access permissions and programs up to 256 bytes of flash memory
 * starting at `addr`.
 *
 * If `byte_count` is not a multiple of flash word size, it's rounded up to next
 * flash word and missing bytes in `data` are set to `0xff`.
 *
 * @param addr Address to write to, must be flash word aligned.
 * @param byte_count Number of bytes to write. Rounded up to next flash word if
 * not a multiple of flash word size. Missing bytes in `data` are set to `0xff`.
 * @param data Data to write, must be word aligned. If `byte_count` is not a
 * multiple of flash word size, `data` must have enough space until the next
 * flash word.
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
static rom_error_t bootstrap_page_program(uint32_t addr, size_t byte_count,
                                          uint8_t *data) {
  if (addr & (NVM_BYTES_PER_WORD - 1) || addr >= kMaxAddress) {
    return kErrorBootstrapProgramAddress;
  }
  return nvm_ctrl_page_program(addr, byte_count, data);
}

/**
 * Bootstrap state 1: Wait for an erase command and erase the data
 * partition.
 *
 * This function erases both data banks of the flash regardless of the type of
 * the erase command (CHIP_ERASE or SECTOR_ERASE).
 *
 * @param state Bootstrap state.
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
static rom_error_t bootstrap_handle_erase(bootstrap_state_t *state) {
  HARDENED_CHECK_EQ(*state, kBootstrapStateErase);

  spi_device_cmd_t cmd;
  RETURN_IF_ERROR(spi_device_cmd_get(&cmd, /*blocking=*/true));
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

  const rom_error_t err = bootstrap_erase_verify();
  HARDENED_RETURN_IF_ERROR(err);

  spi_device_flash_status_clear();

  *state = kBootstrapStateProgram;
  return err;
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
  static_assert(sizeof((spi_device_cmd_t){0}.payload) % NVM_BYTES_PER_WORD == 0,
                "Payload size must be a multiple of flash word size.");

  HARDENED_CHECK_EQ(*state, kBootstrapStateProgram);

  spi_device_cmd_t cmd;
  RETURN_IF_ERROR(spi_device_cmd_get(&cmd, /*blocking=*/true));
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
      // In a normal build, this function inlines to nothing.
      stack_utilization_print();
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

rom_error_t enter_bootstrap(void) {
  spi_device_init_bootstrap();

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
