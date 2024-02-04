// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/otbn.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/crc32.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/random_order.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/impl/status.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otbn_regs.h"  // Generated.

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('d', 'b', 'n')

enum {
  /**
   * Base address for OTBN.
   */
  kBase = TOP_EARLGREY_OTBN_BASE_ADDR,
  /**
   * DMEM size in bytes.
   */
  kOtbnDMemSizeBytes = OTBN_DMEM_SIZE_BYTES,
  /**
   * IMEM size in bytes.
   */
  kOtbnIMemSizeBytes = OTBN_IMEM_SIZE_BYTES,
  /**
   * ERR_BITS register value in the case of no errors.
   *
   * Although some parts of the ERR_BITS register are marked reserved, the OTBN
   * documentation explicitly guarantees that ERR_BITS is zero for a successful
   * execution:
   *   https://opentitan.org/book/hw/ip/otbn/doc/theory_of_operation.html#software-execution-design-details
   */
  kOtbnErrBitsNoError = 0,
};

/**
 * OTBN commands
 */
typedef enum otbn_cmd {
  kOtbnCmdExecute = 0xd8,
  kOtbnCmdSecWipeDmem = 0xc3,
  kOtbnCmdSecWipeImem = 0x1e,
} otbn_cmd_t;

/**
 * OTBN status
 */
typedef enum otbn_status {
  kOtbnStatusIdle = 0x00,
  kOtbnStatusBusyExecute = 0x01,
  kOtbnStatusBusySecWipeDmem = 0x02,
  kOtbnStatusBusySecWipeImem = 0x03,
  kOtbnStatusBusySecWipeInt = 0x04,
  kOtbnStatusLocked = 0xFF,
} otbn_status_t;

/**
 * Ensures that a memory access fits within the given memory size.
 *
 * @param offset_bytes Memory offset at which to start.
 * @param num_words Number of 32b words to access.
 * @param mem_size Size of memory.
 * @return Result of the operation.
 */
static status_t check_offset_len(uint32_t offset_bytes, size_t num_words,
                                 size_t mem_size) {
  if (num_words > UINT32_MAX / sizeof(uint32_t)) {
    return OTCRYPTO_BAD_ARGS;
  }
  uint32_t num_bytes = num_words * sizeof(uint32_t);

  if (offset_bytes > UINT32_MAX - num_bytes) {
    return OTCRYPTO_BAD_ARGS;
  }
  uint32_t adjusted_offset_bytes = offset_bytes + num_bytes;

  if (adjusted_offset_bytes > mem_size) {
    return OTCRYPTO_BAD_ARGS;
  }

  return OTCRYPTO_OK;
}

/**
 * Ensures OTBN is idle.
 *
 * If OTBN is busy or locked, this function will return
 * `OTCRYPTO_ASYNC_INCOMPLETE`; otherwise it will return `OTCRYPTO_OK`.
 *
 * @return Result of the operation.
 */
static status_t otbn_assert_idle(void) {
  uint32_t status = launder32(~(uint32_t)kOtbnStatusIdle);
  status_t res = (status_t){
      .value = (int32_t)launder32((uint32_t)OTCRYPTO_OK.value ^ status)};
  status = abs_mmio_read32(kBase + OTBN_STATUS_REG_OFFSET);
  res.value ^= ~status;
  if (launder32(OT_UNSIGNED(res.value)) == kHardenedBoolTrue) {
    HARDENED_CHECK_EQ(res.value, kHardenedBoolTrue);
    HARDENED_CHECK_EQ(abs_mmio_read32(kBase + OTBN_STATUS_REG_OFFSET),
                      kOtbnStatusIdle);
    return res;
  }
  return OTCRYPTO_ASYNC_INCOMPLETE;
}

/**
 * Update a checksum value with a given IMEM or DMEM write.
 *
 * Calculates the checksum stream according to:
 * https://opentitan.org/book/hw/ip/otbn/doc/theory_of_operation.html#memory-load-integrity
 *
 * This means each write is a 48b value, where the most significant two bytes
 * indicate the location and the least significant four bytes are the 32-bit
 * value that was written. Byte-writes or unaligned writes are not included in
 * the checksum.
 *
 * The location bytes are formatted as follows (described from MSB->LSB):
 * - The first bit (MSB) is 1 for IMEM, 0 for DMEM
 * - The next 5b are zero
 * - The next 10b are the word-index of the address in memory
 *
 * The 48b value is read by OTBN in little-endian order, so we accumulate it to
 * the checksum with least significant bytes first.
 *
 * @param checksum Checksum value (updated in-place).
 * @param is_imem Indicates whether the write is to IMEM.
 * @param addr Address of the write.
 * @param value Value to be written.
 */
static void update_checksum_for_write(uint32_t *checksum, bool is_imem,
                                      uint32_t addr, uint32_t value) {
  // Calculate prefix: is_imem || addr[11:2] || 00000
  uint16_t prefix = is_imem ? 0x8000 : 0;
  prefix |= (addr & 0x7ff) >> 2;
  unsigned char *prefix_bytes = (unsigned char *)&prefix;

  // The value and prefix are reversed here because of the little-endian
  // ordering.
  crc32_add32(checksum, value);
  crc32_add8(checksum, prefix_bytes[0]);
  crc32_add8(checksum, prefix_bytes[1]);
}

/**
 * Helper function for writing to OTBN's DMEM or IMEM.
 *
 * Checks OTBN's CRC32 checksum register to ensure that the data was properly
 * loaded.
 *
 * @param is_imem Boolean indicating whether the write is to IMEM.
 * @param dest_addr Destination address.
 * @param src Source buffer.
 * @param num_words Number of words to copy.
 */
OT_WARN_UNUSED_RESULT
static status_t otbn_write(bool is_imem, uint32_t dest_addr,
                           const uint32_t *src, size_t num_words) {
  // Read the initial checksum value from OTBN.
  uint32_t checksum = launder32(otbn_load_checksum_get());
  HARDENED_CHECK_EQ(checksum, otbn_load_checksum_get());

  // Invert the checksum to match the internal representation.
  checksum ^= UINT32_MAX;

  // Set up the iteration.
  random_order_t iter;
  random_order_init(&iter, num_words);

  // Create a copy of the iterator to use for the checksum.
  random_order_t iter_copy;
  memcpy(&iter_copy, &iter, sizeof(iter));

  // Calculate the expected checksum.
  size_t i = 0;
  for (; launder32(i) < random_order_len(&iter_copy); i++) {
    size_t idx = random_order_advance(&iter_copy);
    if (idx < num_words) {
      uint32_t addr = dest_addr + idx * sizeof(uint32_t);
      uint32_t value = src[idx];
      update_checksum_for_write(&checksum, is_imem, addr, value);
    }
  }
  HARDENED_CHECK_EQ(i, random_order_len(&iter_copy));
  checksum = crc32_finish(&checksum);

  // Perform the write.
  i = 0;
  for (; launder32(i) < random_order_len(&iter); i++) {
    size_t idx = random_order_advance(&iter);
    if (launder32(idx) < num_words) {
      HARDENED_CHECK_LT(idx, num_words);
      uint32_t addr = dest_addr + idx * sizeof(uint32_t);
      uint32_t value = src[idx];
      abs_mmio_write32(addr, value);
    }
  }
  HARDENED_CHECK_EQ(i, random_order_len(&iter));

  // Ensure the checksum updated the same way here and on OTBN.
  if (launder32(checksum) != otbn_load_checksum_get()) {
    return OTCRYPTO_FATAL_ERR;
  }
  HARDENED_CHECK_EQ(checksum, otbn_load_checksum_get());

  return OTCRYPTO_OK;
}

OT_WARN_UNUSED_RESULT
static status_t otbn_imem_write(size_t num_words, const uint32_t *src,
                                otbn_addr_t dest) {
  HARDENED_TRY(check_offset_len(dest, num_words, kOtbnIMemSizeBytes));
  return otbn_write(/*is_imem=*/true, kBase + OTBN_IMEM_REG_OFFSET + dest, src,
                    num_words);
}

status_t otbn_dmem_write(size_t num_words, const uint32_t *src,
                         otbn_addr_t dest) {
  HARDENED_TRY(check_offset_len(dest, num_words, kOtbnDMemSizeBytes));
  return otbn_write(/*is_imem=*/false, kBase + OTBN_DMEM_REG_OFFSET + dest, src,
                    num_words);
}

status_t otbn_dmem_set(size_t num_words, const uint32_t src, otbn_addr_t dest) {
  HARDENED_TRY(check_offset_len(dest, num_words, kOtbnDMemSizeBytes));

  // No need to randomize here, since all the values are the same.
  size_t i = 0;
  for (; launder32(i) < num_words; ++i) {
    abs_mmio_write32(kBase + OTBN_DMEM_REG_OFFSET + dest + i * sizeof(uint32_t),
                     src);
    HARDENED_CHECK_LT(i, num_words);
  }
  HARDENED_CHECK_EQ(i, num_words);
  return OTCRYPTO_OK;
}

status_t otbn_dmem_read(size_t num_words, otbn_addr_t src, uint32_t *dest) {
  HARDENED_TRY(check_offset_len(src, num_words, kOtbnDMemSizeBytes));

  size_t i = 0;
  for (; launder32(i) < num_words; ++i) {
    dest[i] = abs_mmio_read32(kBase + OTBN_DMEM_REG_OFFSET + src +
                              i * sizeof(uint32_t));
  }
  HARDENED_CHECK_EQ(i, num_words);

  return OTCRYPTO_OK;
}

status_t otbn_execute(void) {
  // Ensure that the entropy complex is in a good state (for the RND
  // instruction and data wiping).
  HARDENED_TRY(entropy_complex_check());

  // Ensure OTBN is idle before attempting to run a command.
  HARDENED_TRY(otbn_assert_idle());

  abs_mmio_write32(kBase + OTBN_CMD_REG_OFFSET, kOtbnCmdExecute);
  return OTCRYPTO_OK;
}

status_t otbn_busy_wait_for_done(void) {
  uint32_t status = launder32(UINT32_MAX);
  status_t res = (status_t){
      .value = (int32_t)launder32((uint32_t)kHardenedBoolTrue ^ status)};
  do {
    status = abs_mmio_read32(kBase + OTBN_STATUS_REG_OFFSET);
  } while (launder32(status) != kOtbnStatusIdle &&
           launder32(status) != kOtbnStatusLocked);
  res.value ^= ~status;

  uint32_t err_bits = otbn_err_bits_get();

  if (launder32(OT_UNSIGNED(res.value)) == kHardenedBoolTrue &&
      launder32(err_bits) == kOtbnErrBitsNoError) {
    HARDENED_CHECK_EQ(res.value, kHardenedBoolTrue);
    err_bits = otbn_err_bits_get();
    HARDENED_CHECK_EQ(err_bits, kOtbnErrBitsNoError);
    HARDENED_CHECK_EQ(abs_mmio_read32(kBase + OTBN_STATUS_REG_OFFSET),
                      kOtbnStatusIdle);
    return res;
  }

  // If OTBN is idle (not locked), then return a recoverable error.
  if (launder32(status) == kOtbnStatusIdle) {
    HARDENED_CHECK_EQ(status, kOtbnStatusIdle);
    return OTCRYPTO_RECOV_ERR;
  }

  // OTBN is locked; return a fatal error.
  HARDENED_CHECK_EQ(status, kOtbnStatusLocked);
  return OTCRYPTO_FATAL_ERR;
}

uint32_t otbn_err_bits_get(void) {
  return abs_mmio_read32(kBase + OTBN_ERR_BITS_REG_OFFSET);
}

uint32_t otbn_load_checksum_get(void) {
  return abs_mmio_read32(kBase + OTBN_LOAD_CHECKSUM_REG_OFFSET);
}

void otbn_load_checksum_reset(void) {
  abs_mmio_write32(kBase + OTBN_LOAD_CHECKSUM_REG_OFFSET, 0);
}

uint32_t otbn_instruction_count_get(void) {
  return abs_mmio_read32(kBase + OTBN_INSN_CNT_REG_OFFSET);
}

status_t otbn_imem_sec_wipe(void) {
  HARDENED_TRY(entropy_complex_check());
  HARDENED_TRY(otbn_assert_idle());
  abs_mmio_write32(kBase + OTBN_CMD_REG_OFFSET, kOtbnCmdSecWipeImem);
  HARDENED_TRY(otbn_busy_wait_for_done());
  return OTCRYPTO_OK;
}

status_t otbn_dmem_sec_wipe(void) {
  HARDENED_TRY(entropy_complex_check());
  HARDENED_TRY(otbn_assert_idle());
  abs_mmio_write32(kBase + OTBN_CMD_REG_OFFSET, kOtbnCmdSecWipeDmem);
  HARDENED_TRY(otbn_busy_wait_for_done());
  return OTCRYPTO_OK;
}

status_t otbn_set_ctrl_software_errs_fatal(bool enable) {
  // Ensure OTBN is idle (otherwise CTRL writes will be ignored).
  HARDENED_TRY(otbn_assert_idle());

  // Only one bit in the CTRL register so no need to read current value.
  uint32_t new_ctrl;

  if (enable) {
    new_ctrl = 1;
  } else {
    new_ctrl = 0;
  }

  abs_mmio_write32(kBase + OTBN_CTRL_REG_OFFSET, new_ctrl);

  return OTCRYPTO_OK;
}

/**
 * Checks if the OTBN application's IMEM and DMEM address parameters are valid.
 *
 * This function checks the following properties:
 * - IMEM and DMEM ranges must not be "backwards" in memory, with the end
 * address coming before the start address.
 * - The IMEM range must be non-empty.
 *
 * @param app the OTBN application to check
 * @return `OTCRYPTO_OK` if checks pass, otherwise `OTCRYPTO_BAD_ARGS`.
 */
static status_t check_app_address_ranges(const otbn_app_t *app) {
  // IMEM must not be backwards or empty.
  if (app->imem_end <= app->imem_start) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_LT(app->imem_start, app->imem_end);

  // DMEM data section must not be backwards.
  if (app->dmem_data_end < app->dmem_data_start) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_LE(app->dmem_data_start, app->dmem_data_end);

  return OTCRYPTO_OK;
}

status_t otbn_load_app(const otbn_app_t app) {
  HARDENED_TRY(check_app_address_ranges(&app));

  // Ensure OTBN is idle.
  HARDENED_TRY(otbn_assert_idle());

  const size_t imem_num_words = (size_t)(app.imem_end - app.imem_start);
  const size_t data_num_words =
      (size_t)(app.dmem_data_end - app.dmem_data_start);

  // Wipe the memories and reset the checksum register.
  HARDENED_TRY(otbn_imem_sec_wipe());
  HARDENED_TRY(otbn_dmem_sec_wipe());
  otbn_load_checksum_reset();

  // IMEM always starts at zero.
  otbn_addr_t imem_start_addr = 0;
  HARDENED_TRY(
      otbn_imem_write(imem_num_words, app.imem_start, imem_start_addr));

  if (data_num_words > 0) {
    HARDENED_TRY(otbn_dmem_write(data_num_words, app.dmem_data_start,
                                 app.dmem_data_start_addr));
  }

  return OTCRYPTO_OK;
}
