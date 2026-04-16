// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/hmac.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hmac_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#define MODULE_ID MAKE_MODULE_ID('t', 's', 't')

OTTF_DEFINE_TEST_CONFIG();

static status_t run_hmac_test(void) {
  LOG_INFO("Running HMAC-SHA256 test vector.");

  const uint8_t kMsg[] = "abc";
  uint32_t digest[8];

  const uint32_t kExpectedDigest[8] = {0xbf1678ba, 0xeacf018f, 0xde404141,
                                       0x2322ae5d, 0xa36103b0, 0x9c7a1796,
                                       0x61ff10b4, 0xad1500f2};

  otcrypto_const_byte_buf_t msg_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, kMsg, sizeof(kMsg) - 1);

  TRY(hmac_hash_sha256(&msg_buf, digest));

  CHECK_ARRAYS_EQ(digest, kExpectedDigest, ARRAYSIZE(kExpectedDigest));

  return OTCRYPTO_OK;
}

static status_t run_negative_test(void) {
  LOG_INFO("Running negative tests.");

  // Negative test hmac_key_integrity_checksum_check()
  hmac_key_t bad_key = {
      .key_len = 8,
      .key_block = {0x01, 0x23, 0x45, 0x67, 0x89, 0xAB, 0xCD, 0xEF}};
  bad_key.checksum = hmac_key_integrity_checksum(&bad_key) ^ 0xFFFFFFFF;
  CHECK(hmac_key_integrity_checksum_check(&bad_key) == kHardenedBoolFalse);

  // Test HMAC while it is not idle
  uint32_t cfg =
      abs_mmio_read32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_CFG_REG_OFFSET);
  cfg = bitfield_bit32_write(cfg, HMAC_CFG_SHA_EN_BIT, 1);
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_CFG_REG_OFFSET, cfg);
  uint32_t cmd = bitfield_bit32_write(0, HMAC_CMD_HASH_START_BIT, 1);
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_CMD_REG_OFFSET, cmd);
  uint32_t dummy_digest[8];
  otcrypto_word32_buf_t digest_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_word32_buf_t, dummy_digest, ARRAYSIZE(dummy_digest));
  otcrypto_const_byte_buf_t null_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, NULL, 0);
  CHECK(hmac_hash_sha256(&null_buf, dummy_digest).value ==
        OTCRYPTO_RECOV_ERR.value);
  cmd = bitfield_bit32_write(0, HMAC_CMD_HASH_PROCESS_BIT, 1);
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_CMD_REG_OFFSET, cmd);
  uint32_t status;
  do {
    status =
        abs_mmio_read32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_STATUS_REG_OFFSET);
  } while (bitfield_bit32_read(status, HMAC_STATUS_HMAC_IDLE_BIT) == 0);
  uint32_t intr_state =
      abs_mmio_read32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_INTR_STATE_REG_OFFSET);
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_INTR_STATE_REG_OFFSET,
                   intr_state);

  // Negative test hmac_idle_wait
  hmac_ctx_t ctx;
  hmac_hash_sha256_init(&ctx);
  uint8_t dummy_msg[] = "A";
  otcrypto_const_byte_buf_t dummy_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, dummy_msg, 1);
  TRY(hmac_update(&ctx, &dummy_buf));
  // Corrupt the context to specify an absurdly large message length
  ctx.lower = 0xFFFFFFFF;
  ctx.upper = 0xFFFFFFFF;
  CHECK(hmac_final(&ctx, &digest_buf).value == OTCRYPTO_FATAL_ERR.value);
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_CFG_REG_OFFSET, 0);

  return OTCRYPTO_OK;
}

bool test_main(void) {
  status_t result = OK_STATUS();

  CHECK_STATUS_OK(entropy_complex_init(kHardenedBoolFalse));

  EXECUTE_TEST(result, run_hmac_test);
  EXECUTE_TEST(result, run_negative_test);

  return status_ok(result);
}
