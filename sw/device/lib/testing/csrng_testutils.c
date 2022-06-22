// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/csrng_testutils.h"

#include "sw/device/lib/dif/dif_csrng.h"
#include "sw/device/lib/testing/test_framework/check.h"

void csrng_testutils_cmd_ready_wait(const dif_csrng_t *csrng) {
  dif_csrng_cmd_status_t cmd_status;
  do {
    CHECK_DIF_OK(dif_csrng_get_cmd_interface_status(csrng, &cmd_status));
    CHECK(cmd_status.kind != kDifCsrngCmdStatusError);
  } while (cmd_status.kind != kDifCsrngCmdStatusReady);
}

void csrng_testutils_cmd_generate_run(const dif_csrng_t *csrng,
                                      uint32_t *output, size_t output_len) {
  csrng_testutils_cmd_ready_wait(csrng);
  CHECK_DIF_OK(dif_csrng_generate_start(csrng, output_len));

  dif_csrng_output_status_t output_status;
  do {
    CHECK_DIF_OK(dif_csrng_get_output_status(csrng, &output_status));
  } while (!output_status.valid_data);

  CHECK_DIF_OK(dif_csrng_generate_read(csrng, output, output_len));
}
