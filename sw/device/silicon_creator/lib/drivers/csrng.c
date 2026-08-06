// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/csrng.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/silicon_creator/lib/error.h"

#include "csrng_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

enum {
  kBaseCsrng = TOP_EARLGREY_CSRNG_BASE_ADDR,
  kCsrngPollTimeout = 1000000,
};

typedef enum csrng_app_cmd_id {
  kCsrngCmdInstantiate = 1,
  kCsrngCmdGenerate = 3,
} csrng_app_cmd_id_t;

/**
 * Polls until the CSRNG command interface is ready for a new command.
 */
static inline rom_error_t csrng_wait_ready(void) {
  uint32_t timeout = kCsrngPollTimeout;
  while (timeout--) {
    uint32_t sts = abs_mmio_read32(kBaseCsrng + CSRNG_SW_CMD_STS_REG_OFFSET);
    if (bitfield_bit32_read(sts, CSRNG_SW_CMD_STS_CMD_RDY_BIT)) {
      return kErrorOk;
    }
  }
  return kErrorUnknown;
}

/**
 * Sends a CSRNG application command (Instantiate or Generate).
 */
static rom_error_t csrng_send_cmd(csrng_app_cmd_id_t cmd_id, uint32_t glen) {
  HARDENED_RETURN_IF_ERROR(csrng_wait_ready());

  if (cmd_id != kCsrngCmdGenerate) {
    abs_mmio_write32(kBaseCsrng + CSRNG_INTR_STATE_REG_OFFSET,
                     1u << CSRNG_INTR_STATE_CS_CMD_REQ_DONE_BIT);
  }

  // Header: bits [3:0] = cmd_id, bits [7:4] = 0 (len), bits [11:8] = 0x9
  // (TRNG), bits [30:12] = glen
  uint32_t header = (cmd_id & 0xf) | (kMultiBitBool4False << 8) | (glen << 12);
  abs_mmio_write32(kBaseCsrng + CSRNG_CMD_REQ_REG_OFFSET, header);

  if (cmd_id == kCsrngCmdGenerate) {
    uint32_t timeout = kCsrngPollTimeout;
    while (timeout--) {
      uint32_t vld = abs_mmio_read32(kBaseCsrng + CSRNG_GENBITS_VLD_REG_OFFSET);
      if (bitfield_bit32_read(vld, CSRNG_GENBITS_VLD_GENBITS_VLD_BIT)) {
        return kErrorOk;
      }
    }
    return kErrorUnknown;
  } else {
    uint32_t timeout = kCsrngPollTimeout;
    while (timeout--) {
      uint32_t intr = abs_mmio_read32(kBaseCsrng + CSRNG_INTR_STATE_REG_OFFSET);
      if (bitfield_bit32_read(intr, CSRNG_INTR_STATE_CS_CMD_REQ_DONE_BIT)) {
        uint32_t sts =
            abs_mmio_read32(kBaseCsrng + CSRNG_SW_CMD_STS_REG_OFFSET);
        if (!bitfield_field32_read(sts, CSRNG_SW_CMD_STS_CMD_STS_FIELD)) {
          return kErrorOk;
        }
        return kErrorUnknown;
      }
    }
    return kErrorUnknown;
  }
}

rom_error_t csrng_enable(void) {
  uint32_t ctrl = 0;
  ctrl =
      bitfield_field32_write(ctrl, CSRNG_CTRL_ENABLE_FIELD, kMultiBitBool4True);
  ctrl = bitfield_field32_write(ctrl, CSRNG_CTRL_SW_APP_ENABLE_FIELD,
                                kMultiBitBool4True);
  ctrl = bitfield_field32_write(ctrl, CSRNG_CTRL_READ_INT_STATE_FIELD,
                                kMultiBitBool4True);
  ctrl = bitfield_field32_write(ctrl, CSRNG_CTRL_FIPS_FORCE_ENABLE_FIELD,
                                kMultiBitBool4False);
  abs_mmio_write32(kBaseCsrng + CSRNG_CTRL_REG_OFFSET, ctrl);
  return kErrorOk;
}

rom_error_t csrng_instantiate(void) {
  HARDENED_RETURN_IF_ERROR(csrng_enable());
  return csrng_send_cmd(kCsrngCmdInstantiate, 0);
}

rom_error_t csrng_read_words(uint32_t *dest, size_t num_words) {
  if (num_words == 0) {
    return kErrorOk;
  }

  size_t blocks_128bit = (num_words + 3) / 4;
  HARDENED_RETURN_IF_ERROR(
      csrng_send_cmd(kCsrngCmdGenerate, (uint32_t)blocks_128bit));

  size_t words_read = 0;
  for (size_t block = 0; block < blocks_128bit; ++block) {
    if (block > 0) {
      uint32_t timeout = kCsrngPollTimeout;
      while (timeout--) {
        uint32_t vld =
            abs_mmio_read32(kBaseCsrng + CSRNG_GENBITS_VLD_REG_OFFSET);
        if (bitfield_bit32_read(vld, CSRNG_GENBITS_VLD_GENBITS_VLD_BIT)) {
          break;
        }
      }
      if (timeout == 0) {
        return kErrorUnknown;
      }
    }

    for (size_t w = 0; w < 4; ++w) {
      uint32_t word = abs_mmio_read32(kBaseCsrng + CSRNG_GENBITS_REG_OFFSET);
      if (words_read < num_words) {
        dest[words_read++] = word;
      }
    }
  }

  return kErrorOk;
}
