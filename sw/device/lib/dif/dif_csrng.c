// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_csrng.h"

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/mmio.h"

#include "csrng_regs.h"  // Generated

dif_csrng_result_t dif_csrng_init(dif_csrng_params_t params,
                                  dif_csrng_t *csrng) {
  if (csrng == NULL) {
    return kDifCsrngBadArg;
  }
  *csrng = (dif_csrng_t){.params = params};
  return kDifCsrngOk;
}

dif_csrng_result_t dif_csrng_configure(const dif_csrng_t *csrng,
                                       dif_csrng_config_t config) {
  if (csrng == NULL) {
    return kDifCsrngBadArg;
  }

  uint32_t reg = bitfield_bit32_write(0, CSRNG_CTRL_ENABLE_BIT, 1);
  reg = bitfield_bit32_write(reg, CSRNG_CTRL_AES_CIPHER_DISABLE_BIT,
                             config.debug_config.bypass_aes_cipher);

  // TODO: Determine if the dif library should support a diagnostics mode
  // of operation.
  reg = bitfield_field32_write(reg, CSRNG_CTRL_FIFO_DEPTH_STS_SEL_FIELD, 0);

  mmio_region_write32(csrng->params.base_addr, CSRNG_CTRL_REG_OFFSET, reg);
  return kDifCsrngOk;
}

dif_csrng_result_t dif_csrng_get_cmd_interface_status(
    const dif_csrng_t *csrng, dif_csrng_cmd_status_t *status) {
  if (csrng == NULL || status == NULL) {
    return kDifCsrngBadArg;
  }

  uint32_t reg =
      mmio_region_read32(csrng->params.base_addr, CSRNG_SW_CMD_STS_REG_OFFSET);
  bool cmd_ready = bitfield_bit32_read(reg, CSRNG_SW_CMD_STS_CMD_RDY_BIT);
  bool cmd_error = bitfield_bit32_read(reg, CSRNG_SW_CMD_STS_CMD_STS_BIT);

  // The function prioritizes error detection to avoid masking errors
  // when `cmd_ready` is set to true.
  if (cmd_error) {
    *status = kDifCsrngCmdStatusError;
    return kDifCsrngOk;
  }

  if (cmd_ready) {
    *status = kDifCsrngCmdStatusReady;
    return kDifCsrngOk;
  }

  *status = kDifCsrngCmdStatusBusy;
  return kDifCsrngOk;
}

dif_csrng_result_t dif_csrng_get_output_status(
    const dif_csrng_t *csrng, dif_csrng_output_status_t *status) {
  if (csrng == NULL || status == NULL) {
    return kDifCsrngBadArg;
  }
  uint32_t reg =
      mmio_region_read32(csrng->params.base_addr, CSRNG_GENBITS_VLD_REG_OFFSET);
  status->valid_data =
      bitfield_bit32_read(reg, CSRNG_GENBITS_VLD_GENBITS_VLD_BIT);
  status->fips_mode =
      bitfield_bit32_read(reg, CSRNG_GENBITS_VLD_GENBITS_FIPS_BIT);
  return kDifCsrngOk;
}
