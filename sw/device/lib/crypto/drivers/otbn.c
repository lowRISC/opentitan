// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/otbn.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/status.h"
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
   *   https://docs.opentitan.org/hw/ip/otbn/doc/#design-details-software-execution
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
  if (launder32(res.value) == kHardenedBoolTrue) {
    HARDENED_CHECK_EQ(res.value, kHardenedBoolTrue);
    HARDENED_CHECK_EQ(abs_mmio_read32(kBase + OTBN_STATUS_REG_OFFSET),
                      kOtbnStatusIdle);
    return res;
  }
  return OTCRYPTO_ASYNC_INCOMPLETE;
}

/**
 * Helper function for writing to OTBN's DMEM or IMEM.
 *
 * @param dest_addr Destination address.
 * @param src Source buffer.
 * @param num_words Number of words to copy.
 */
static void otbn_write(uint32_t dest_addr, const uint32_t *src,
                       size_t num_words) {
  // TODO: replace 0 with a random index like the silicon_creator driver
  // (requires an interface to Ibex's RND valid bit and data register).
  size_t i = ((uint64_t)0 * (uint64_t)num_words) >> 32;
  enum { kStep = 1 };
  size_t iter_cnt = 0;
  for (; launder32(iter_cnt) < num_words; ++iter_cnt) {
    abs_mmio_write32(dest_addr + i * sizeof(uint32_t), src[i]);
    i += kStep;
    if (launder32(i) >= num_words) {
      i -= num_words;
    }
    HARDENED_CHECK_LT(i, num_words);
  }
  HARDENED_CHECK_EQ(iter_cnt, num_words);
}

static status_t otbn_imem_write(size_t num_words, const uint32_t *src,
                                otbn_addr_t dest) {
  HARDENED_TRY(check_offset_len(dest, num_words, kOtbnIMemSizeBytes));
  otbn_write(kBase + OTBN_IMEM_REG_OFFSET + dest, src, num_words);
  return OTCRYPTO_OK;
}

status_t otbn_dmem_write(size_t num_words, const uint32_t *src,
                         otbn_addr_t dest) {
  HARDENED_TRY(check_offset_len(dest, num_words, kOtbnDMemSizeBytes));
  otbn_write(kBase + OTBN_DMEM_REG_OFFSET + dest, src, num_words);
  return OTCRYPTO_OK;
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

  if (launder32(res.value) == kHardenedBoolTrue &&
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

uint32_t otbn_instruction_count_get(void) {
  return abs_mmio_read32(kBase + OTBN_INSN_CNT_REG_OFFSET);
}

status_t otbn_imem_sec_wipe(void) {
  HARDENED_TRY(otbn_assert_idle());
  abs_mmio_write32(kBase + OTBN_CMD_REG_OFFSET, kOtbnCmdSecWipeImem);
  HARDENED_TRY(otbn_busy_wait_for_done());
  return OTCRYPTO_OK;
}

status_t otbn_dmem_sec_wipe(void) {
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

  HARDENED_TRY(otbn_imem_sec_wipe());
  HARDENED_TRY(otbn_dmem_sec_wipe());

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
