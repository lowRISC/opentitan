// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/kmac.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_alerts.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "kmac_regs.h"  // Generated.

#define MODULE_ID MAKE_MODULE_ID('t', 's', 't')

OTTF_DEFINE_TEST_CONFIG();

static status_t run_kmac_test(void) {
  LOG_INFO("Running positive KMAC (SHA3-256) test.");

  HARDENED_TRY(kmac_hwip_default_configure());

  const uint8_t kMsg[] = "abc";
  uint32_t digest[8];

  const uint32_t kExpectedDigest[8] = {0xa75d983a, 0xb225e24f, 0x2d175c04,
                                       0xbd90d36b, 0x6e085f85, 0x5b529d3e,
                                       0x45e2bf46, 0x32154311};

  otcrypto_const_byte_buf_t msg_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, kMsg, sizeof(kMsg) - 1);

  TRY(kmac_sha3_256(&msg_buf, digest));

  CHECK_ARRAYS_EQ(digest, kExpectedDigest, ARRAYSIZE(kExpectedDigest));

  return OTCRYPTO_OK;
}

static status_t run_negative_test(void) {
  LOG_INFO("Running negative tests.");

  // Test invalid key length check
  CHECK(kmac_key_length_check(99).value == OTCRYPTO_BAD_ARGS.value);

  // Null pointer check
  otcrypto_const_byte_buf_t null_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, NULL, 0);
  CHECK(kmac_sha3_256(&null_buf, NULL).value == OTCRYPTO_BAD_ARGS.value);

  // Test string prefix length limits (func_name + cust_str > 36 bytes)
  uint8_t func_name[20] = {0};
  uint8_t cust_str[20] = {0};
  uint32_t dummy_digest[8];
  CHECK(kmac_cshake_128(&null_buf, func_name, 20, cust_str, 20, dummy_digest, 8)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Send an invalid command to the CMD register to trigger the error interrupt
  uint32_t cmd_addr = TOP_EARLGREY_KMAC_BASE_ADDR + KMAC_CMD_REG_OFFSET;
  abs_mmio_write32(cmd_addr, 0xFFFFFFFF);
  CHECK(kmac_hwip_default_configure().value == OTCRYPTO_RECOV_ERR.value);
  abs_mmio_write32(TOP_EARLGREY_KMAC_BASE_ADDR + KMAC_INTR_STATE_REG_OFFSET,
                   1 << KMAC_INTR_STATE_KMAC_ERR_BIT);
  abs_mmio_write32(TOP_EARLGREY_KMAC_BASE_ADDR + KMAC_ERR_CODE_REG_OFFSET,
                   0xFFFFFFFF);

  // Test shadow reg update mismatch
  CHECK_STATUS_OK(
      ottf_alerts_expect_alert_start(kTopEarlgreyAlertIdKmacRecovOperationErr));
  uint32_t cfg_addr =
      TOP_EARLGREY_KMAC_BASE_ADDR + KMAC_CFG_SHADOWED_REG_OFFSET;
  abs_mmio_write32(cfg_addr, 0xAAAAAAAA);  // First write
  abs_mmio_write32(cfg_addr, 0xBBBBBBBB);  // Mismatched second write
  CHECK(kmac_hwip_default_configure().value == OTCRYPTO_RECOV_ERR.value);
  CHECK_STATUS_OK(ottf_alerts_expect_alert_finish(
      kTopEarlgreyAlertIdKmacRecovOperationErr));

  return OTCRYPTO_OK;
}

bool test_main(void) {
  status_t result = OK_STATUS();

  CHECK_STATUS_OK(entropy_complex_init());

  EXECUTE_TEST(result, run_kmac_test);
  EXECUTE_TEST(result, run_negative_test);

  return status_ok(result);
}
