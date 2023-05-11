// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom/bootstrap.h"

#include <stdalign.h>

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/silicon_creator/lib/base/chip.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/lib/drivers/spi_device.h"
#include "sw/device/silicon_creator/lib/error.h"

#include "flash_ctrl_regs.h"
#include "gpio_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"

enum {
  /*
   * Maximum flash address, exclusive.
   */
  kMaxAddress =
      FLASH_CTRL_PARAM_BYTES_PER_BANK * FLASH_CTRL_PARAM_REG_NUM_BANKS,
};

static_assert(FLASH_CTRL_PARAM_REG_NUM_BANKS == 2, "Flash must have 2 banks");

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
 * Handles access permissions and erases both data banks of the embedded flash.
 *
 * @return Result of the operation.
 */
static rom_error_t bootstrap_chip_erase(void) {
  flash_ctrl_bank_erase_perms_set(kHardenedBoolTrue);
  rom_error_t err_0 = flash_ctrl_data_erase(0, kFlashCtrlEraseTypeBank);
  rom_error_t err_1 = flash_ctrl_data_erase(FLASH_CTRL_PARAM_BYTES_PER_BANK,
                                            kFlashCtrlEraseTypeBank);
  flash_ctrl_bank_erase_perms_set(kHardenedBoolFalse);

  HARDENED_RETURN_IF_ERROR(err_0);
  return err_1;
}

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
static rom_error_t bootstrap_sector_erase(uint32_t addr) {
  static_assert(FLASH_CTRL_PARAM_BYTES_PER_PAGE == 2048,
                "Page size must be 2 KiB");
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

  flash_ctrl_data_default_perms_set((flash_ctrl_perms_t){
      .read = kMultiBitBool4False,
      .write = kMultiBitBool4False,
      .erase = kMultiBitBool4True,
  });
  rom_error_t err_0 = flash_ctrl_data_erase(addr, kFlashCtrlEraseTypePage);
  rom_error_t err_1 = flash_ctrl_data_erase(
      addr + FLASH_CTRL_PARAM_BYTES_PER_PAGE, kFlashCtrlEraseTypePage);
  flash_ctrl_data_default_perms_set((flash_ctrl_perms_t){
      .read = kMultiBitBool4False,
      .write = kMultiBitBool4False,
      .erase = kMultiBitBool4False,
  });

  HARDENED_RETURN_IF_ERROR(err_0);
  return err_1;
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
static rom_error_t bootstrap_page_program(uint32_t addr, size_t byte_count,
                                          uint8_t *data) {
  static_assert(__builtin_popcount(FLASH_CTRL_PARAM_BYTES_PER_WORD) == 1,
                "Bytes per flash word must be a power of two.");
  enum {
    /**
     * Mask for checking that `addr` is flash word aligned.
     */
    kFlashWordMask = FLASH_CTRL_PARAM_BYTES_PER_WORD - 1,
    /**
     * SPI flash programming page size in bytes.
     */
    kFlashProgPageSize = 256,
    /**
     * Mask for checking whether `addr` is flash programming page aligned.
     *
     * Flash programming page size is 256 bytes, writes that start at an `addr`
     * with a non-zero LSB wrap to the start of the 256 byte region.
     */
    kFlashProgPageMask = kFlashProgPageSize - 1,
  };

  if (addr & kFlashWordMask || addr >= kMaxAddress) {
    return kErrorBootstrapProgramAddress;
  }

  // Round up to next flash word and fill missing bytes with `0xff`.
  size_t flash_word_misalignment = byte_count & kFlashWordMask;
  if (flash_word_misalignment > 0) {
    size_t padding_byte_count =
        FLASH_CTRL_PARAM_BYTES_PER_WORD - flash_word_misalignment;
    for (size_t i = 0; i < padding_byte_count; ++i) {
      data[byte_count++] = 0xff;
    }
  }
  size_t rem_word_count = byte_count / sizeof(uint32_t);

  flash_ctrl_data_default_perms_set((flash_ctrl_perms_t){
      .read = kMultiBitBool4False,
      .write = kMultiBitBool4True,
      .erase = kMultiBitBool4False,
  });
  // Perform two writes if the start address is not page-aligned (256 bytes).
  // Note: Address is flash-word-aligned (8 bytes) due to the check above.
  rom_error_t err_0 = kErrorOk;
  size_t prog_page_misalignment = addr & kFlashProgPageMask;
  if (prog_page_misalignment > 0) {
    size_t word_count =
        (kFlashProgPageSize - prog_page_misalignment) / sizeof(uint32_t);
    if (word_count > rem_word_count) {
      word_count = rem_word_count;
    }
    err_0 = flash_ctrl_data_write(addr, word_count, data);
    rem_word_count -= word_count;
    data += word_count * sizeof(uint32_t);
    // Wrap to the beginning of the current page since PAGE_PROGRAM modifies
    // a single page only.
    addr &= ~kFlashProgPageMask;
  }
  rom_error_t err_1 = kErrorOk;
  if (rem_word_count > 0) {
    err_1 = flash_ctrl_data_write(addr, rem_word_count, data);
  }
  flash_ctrl_data_default_perms_set((flash_ctrl_perms_t){
      .read = kMultiBitBool4False,
      .write = kMultiBitBool4False,
      .erase = kMultiBitBool4False,
  });

  HARDENED_RETURN_IF_ERROR(err_0);
  return err_1;
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
static rom_error_t bootstrap_handle_erase_verify(bootstrap_state_t *state) {
  HARDENED_CHECK_EQ(*state, kBootstrapStateEraseVerify);

  rom_error_t err_0 = flash_ctrl_data_erase_verify(0, kFlashCtrlEraseTypeBank);
  rom_error_t err_1 = flash_ctrl_data_erase_verify(
      FLASH_CTRL_PARAM_BYTES_PER_BANK, kFlashCtrlEraseTypeBank);
  HARDENED_RETURN_IF_ERROR(err_0);
  HARDENED_RETURN_IF_ERROR(err_1);

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
static rom_error_t bootstrap_handle_program(bootstrap_state_t *state) {
  static_assert(alignof(spi_device_cmd_t) >= sizeof(uint32_t) &&
                    offsetof(spi_device_cmd_t, payload) >= sizeof(uint32_t),
                "Payload must be word aligned.");
  static_assert(
      sizeof((spi_device_cmd_t){0}.payload) % FLASH_CTRL_PARAM_BYTES_PER_WORD ==
          0,
      "Payload size must be a multiple of flash word size.");

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
      abs_mmio_read32(TOP_EARLGREY_GPIO_BASE_ADDR + GPIO_DATA_IN_REG_OFFSET) &
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
