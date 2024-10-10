// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_clkmgr.h"
#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/kmac_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "kmac_regs.h"  // Generated.

static dif_kmac_t kmac;

OTTF_DEFINE_TEST_CONFIG();

/**
 * KMAC test description.
 */
typedef struct kmac_test {
  dif_kmac_mode_kmac_t mode;
  dif_kmac_key_t key;

  const char *message;
  size_t message_len;

  const char *customization_string;
  size_t customization_string_len;

  const uint32_t digest[16];
  size_t digest_len;
  bool digest_len_is_fixed;
} kmac_test_t;

/**
 * A single KMAC example.
 */
static const kmac_test_t kKmacTestVector = {
    .mode = kDifKmacModeKmacLen256,
    .key =
        (dif_kmac_key_t){
            .share0 = {0x43424140, 0x47464544, 0x4b4a4948, 0x4f4e4f4c,
                       0x53525150, 0x57565554, 0x5b5a5958, 0x5f5e5d5c},
            .share1 = {0},
            .length = kDifKmacKeyLen256,
        },
    .message =
        "\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0a\x0b\x0c\x0d\x0e\x0f"
        "\x10\x11\x12\x13\x14\x15\x16\x17\x18\x19\x1a\x1b\x1c\x1d\x1e\x1f"
        "\x20\x21\x22\x23\x24\x25\x26\x27\x28\x29\x2a\x2b\x2c\x2d\x2e\x2f"
        "\x30\x31\x32\x33\x34\x35\x36\x37\x38\x39\x3a\x3b\x3c\x3d\x3e\x3f"
        "\x40\x41\x42\x43\x44\x45\x46\x47\x48\x49\x4a\x4b\x4c\x4d\x4e\x4f"
        "\x50\x51\x52\x53\x54\x55\x56\x57\x58\x59\x5a\x5b\x5c\x5d\x5e\x5f"
        "\x60\x61\x62\x63\x64\x65\x66\x67\x68\x69\x6a\x6b\x6c\x6d\x6e\x6f"
        "\x70\x71\x72\x73\x74\x75\x76\x77\x78\x79\x7a\x7b\x7c\x7d\x7e\x7f"
        "\x80\x81\x82\x83\x84\x85\x86\x87\x88\x89\x8a\x8b\x8c\x8d\x8e\x8f"
        "\x90\x91\x92\x93\x94\x95\x96\x97\x98\x99\x9a\x9b\x9c\x9d\x9e\x9f"
        "\xa0\xa1\xa2\xa3\xa4\xa5\xa6\xa7\xa8\xa9\xaa\xab\xac\xad\xae\xaf"
        "\xb0\xb1\xb2\xb3\xb4\xb5\xb6\xb7\xb8\xb9\xba\xbb\xbc\xbd\xbe\xbf"
        "\xc0\xc1\xc2\xc3\xc4\xc5\xc6\xc7",
    .message_len = 200,
    .customization_string = "My Tagged Application",
    .customization_string_len = 21,
    .digest = {0x1c73bed5, 0x73d74e95, 0x59bb4628, 0xe3a8e3db, 0x7ae7830f,
               0x5944ff4b, 0xb4c2f1f2, 0xceb8ebec, 0xc601ba67, 0x57b88a2e,
               0x9b492d8d, 0x6727bbd1, 0x90117868, 0x6a300a02, 0x1d28de97,
               0x5d3030cc},
    .digest_len = 16,
    .digest_len_is_fixed = false,
};

/**
 * ErrWaitTimerExpired.
 *
 * This test checks whether the ErrWaitTimerExpired error code is
 * returned by the hardware when KMAC timed out while waiting for EDN entropy.
 * By configuring a small wait timer (=1), the timeout immediately will be
 * triggered and we should see the expected error code.
 *
 * @return OK or error.
 */
status_t test_err_wait_timer_expired(void) {
  LOG_INFO("Testing ErrWaitTimerExpired error.");

  // Init the KMAC block.
  TRY(dif_kmac_init(mmio_region_from_addr(TOP_EARLGREY_KMAC_BASE_ADDR), &kmac));

  dif_kmac_config_t config = (dif_kmac_config_t){
      .entropy_mode = kDifKmacEntropyModeEdn,
      .entropy_wait_timer = 0x001,  // Small wait time out to trigger the error.
      .entropy_prescaler = 0x000,
      .entropy_fast_process = kDifToggleDisabled,
      .entropy_seed = {0xaa25b4bf, 0x48ce8fff, 0x5a78282a, 0x48465647,
                       0x70410fef},
      .message_big_endian = kDifToggleDisabled,
      .output_big_endian = kDifToggleDisabled,
      .sideload = kDifToggleDisabled,
      .msg_mask = kDifToggleEnabled,
  };

  TRY(dif_kmac_configure(&kmac, config));

  dif_kmac_operation_state_t kmac_operation_state;
  TRY(dif_kmac_mode_kmac_start(&kmac, &kmac_operation_state,
                               kKmacTestVector.mode, 0, &kKmacTestVector.key,
                               NULL));

  TRY(dif_kmac_absorb(&kmac, &kmac_operation_state, kKmacTestVector.message,
                      kKmacTestVector.message_len, NULL));

  // This is where timeout might happen, so we handle dif return manually.
  uint32_t digest[kKmacTestVector.digest_len];
  dif_result_t res = dif_kmac_squeeze(&kmac, &kmac_operation_state, digest,
                                      kKmacTestVector.digest_len,
                                      /*processed=*/NULL, /*capacity=*/NULL);

  // It is OK to get kDifError at this point because of possible timeout.
  TRY_CHECK(res == kDifOk || res == kDifError);

  // Check if there is a new error.
  bool irq_err_pending;
  TRY(dif_kmac_irq_is_pending(&kmac, kDifKmacIrqKmacErr, &irq_err_pending));
  if (irq_err_pending) {
    dif_kmac_error_t err_status;
    uint32_t err_info;
    TRY(dif_kmac_get_error(&kmac, &err_status, &err_info));
    CHECK(err_status == kDifErrorEntropyWaitTimerExpired,
          "Error other than EDN timeout occurred.");
    LOG_INFO("EDN timed out.");
  } else {
    LOG_INFO("EDN seed received before timeout.");
  }

  // At this point, irq_err_pending says if timeout is observed
  CHECK(irq_err_pending == true,
        "EDN timeout expectation doesn't match observation.");

  // Flush out the result and check correctness
  TRY(dif_kmac_end(&kmac, &kmac_operation_state));

  // If err interrupt is generated, we need clean-up
  if (irq_err_pending) {
    // Clean INTR_STATE
    TRY(dif_kmac_irq_acknowledge_all(&kmac));

    // Reset FSM by setting `err_processed` bit
    TRY(dif_kmac_reset(&kmac, &kmac_operation_state));

    // At this point, we expect that there are no remaining interrupts.
    dif_kmac_irq_state_snapshot_t intr_snapshot;
    TRY(dif_kmac_irq_get_state(&kmac, &intr_snapshot));
    CHECK(intr_snapshot == 0, "INTR_STATE is non-zero after timeout clean-up.");

    bool is_kmac_locked;
    TRY(dif_kmac_config_is_locked(&kmac, &is_kmac_locked));
    CHECK(!is_kmac_locked, "KMAC still locked after timeout clean-up.");
  }

  return OK_STATUS();
}

/**
 * ErrIncorrectEntropyMode.
 *
 * This test checks whether the ErrIncorrectEntropyMode error code is
 * returned by the hardware when using a wrong entropy mode configuration.
 *
 * @return OK or error.
 */
status_t test_err_incorrect_entropy_mode(void) {
  LOG_INFO("Testing ErrIncorrectEntropyMode error.");

  // Re-init KMAC for the test.
  TRY(dif_kmac_init(mmio_region_from_addr(TOP_EARLGREY_KMAC_BASE_ADDR), &kmac));

  // Write configuration register.
  uint32_t cfg_reg = 0;
  // Provide invalid entropy mode (other than kDifKmacEntropyModeSoftware or
  // kDifKmacEntropyModeEdn)
  cfg_reg = bitfield_field32_write(cfg_reg,
                                   KMAC_CFG_SHADOWED_ENTROPY_MODE_FIELD, 0xf);
  // Set remaining config to a valid one.
  cfg_reg = bitfield_bit32_write(cfg_reg, KMAC_CFG_SHADOWED_MSG_ENDIANNESS_BIT,
                                 kDifToggleDisabled);
  cfg_reg = bitfield_bit32_write(
      cfg_reg, KMAC_CFG_SHADOWED_STATE_ENDIANNESS_BIT, kDifToggleDisabled);
  cfg_reg = bitfield_bit32_write(
      cfg_reg, KMAC_CFG_SHADOWED_ENTROPY_FAST_PROCESS_BIT, kDifToggleDisabled);
  cfg_reg = bitfield_bit32_write(cfg_reg, KMAC_CFG_SHADOWED_SIDELOAD_BIT,
                                 kDifToggleDisabled);
  cfg_reg =
      bitfield_bit32_write(cfg_reg, KMAC_CFG_SHADOWED_ENTROPY_READY_BIT, true);
  cfg_reg = bitfield_bit32_write(cfg_reg, KMAC_CFG_SHADOWED_MSG_MASK_BIT,
                                 kDifToggleEnabled);
  mmio_region_write32_shadowed(kmac.base_addr, KMAC_CFG_SHADOWED_REG_OFFSET,
                               cfg_reg);

  // Read out error information.
  dif_kmac_error_t err;
  uint32_t info;
  TRY(dif_kmac_get_error(&kmac, &err, &info));
  CHECK(err == kDifErrorEntropyModeIncorrect,
        "Error other than kDifErrorEntropyModeIncorrect occurred.");

  // Reset the KMAC FSM.
  dif_kmac_operation_state_t kmac_operation_state;
  TRY(dif_kmac_reset(&kmac, &kmac_operation_state));

  return OK_STATUS();
}

/**
 * ErrorSoftwareCommandSequence.
 *
 * This test checks whether the kDifErrorSoftwareCommandSequence error code is
 * returned by the hardware when sending software commands in a wrong order to
 * the KMAC block. Note that this test is not exhaustive, i.e., the test does
 * not trying to reach the ErrorSoftwareCommandSequence error state from each
 * other state.
 *
 * @return OK or error.
 */
status_t test_err_sw_cmd_sequence(void) {
  LOG_INFO("Testing kDifErrorSoftwareCommandSequence error.");
  uint32_t cmds[3] = {KMAC_CMD_CMD_VALUE_PROCESS, KMAC_CMD_CMD_VALUE_RUN,
                      KMAC_CMD_CMD_VALUE_DONE};

  for (int it = 0; it < ARRAYSIZE(cmds); it++) {
    // Re-init KMAC for the test.
    TRY(dif_kmac_init(mmio_region_from_addr(TOP_EARLGREY_KMAC_BASE_ADDR),
                      &kmac));
    // Configure KMAC hardware (using software key and software entropy).
    CHECK_STATUS_OK(kmac_testutils_config(&kmac, false));

    // Send CmdDone after initializing KMAC.
    uint32_t cmd_reg = bitfield_field32_write(0, KMAC_CMD_CMD_FIELD, cmds[it]);
    mmio_region_write32(kmac.base_addr, KMAC_CMD_REG_OFFSET, cmd_reg);

    // Read out error information.
    dif_kmac_error_t err;
    uint32_t info;
    TRY(dif_kmac_get_error(&kmac, &err, &info));
    CHECK(err == kDifErrorSoftwareCommandSequence,
          "Error other than kDifErrorSoftwareCommandSequence occurred.");

    // Reset the KMAC FSM.
    dif_kmac_operation_state_t kmac_operation_state;
    TRY(dif_kmac_reset(&kmac, &kmac_operation_state));
  }

  return OK_STATUS();
}

status_t test_err_key_not_valid(void) {
  LOG_INFO("Testing ErrKeyNotValid error.");
  // Re-init KMAC for the test.
  TRY(dif_kmac_init(mmio_region_from_addr(TOP_EARLGREY_KMAC_BASE_ADDR), &kmac));
  // Configure KMAC to use the sideloaded key.
  CHECK_STATUS_OK(kmac_testutils_config(&kmac, true));

  // Start the KMAC operation without setting a valid sideloaded key. The
  // provided SW key is ignored as we configured KMAC to use the sideloaded key.
  dif_kmac_operation_state_t kmac_operation_state;
  TRY(dif_kmac_mode_kmac_start(&kmac, &kmac_operation_state,
                               kKmacTestVector.mode, 0, &kKmacTestVector.key,
                               NULL));

  // Read out error information.
  dif_kmac_error_t err;
  uint32_t info;
  TRY(dif_kmac_get_error(&kmac, &err, &info));
  CHECK(err == kDifErrorKeyNotValid,
        "Error other than kDifErrorKeyNotValid occurred.");

  // Reset the KMAC FSM.
  TRY(dif_kmac_reset(&kmac, &kmac_operation_state));

  return OK_STATUS();
}

/**
 * ErrUnexpectedModeStrength.
 *
 * This test checks whether the ErrUnexpectedModeStrength error code is
 * returned by the hardware when using a wrong strength. For mode SHA3 use
 * 128-bit strength and for SHAKE 224-bit.
 *
 * @return OK or error.
 */
status_t test_err_unexpected_mode_strength(void) {
  LOG_INFO("Testing ErrUnexpectedModeStrength error.");

  uint32_t misconfigured_strength[2] = {KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L128,
                                        KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L224};
  uint32_t mode[2] = {KMAC_CFG_SHADOWED_MODE_VALUE_SHA3,
                      KMAC_CFG_SHADOWED_MODE_VALUE_SHAKE};

  for (int it = 0; it < ARRAYSIZE(mode); it++) {
    // Re-init KMAC for the test.
    TRY(dif_kmac_init(mmio_region_from_addr(TOP_EARLGREY_KMAC_BASE_ADDR),
                      &kmac));
    CHECK_STATUS_OK(kmac_testutils_config(&kmac, false));

    uint32_t cfg_reg =
        mmio_region_read32(kmac.base_addr, KMAC_CFG_SHADOWED_REG_OFFSET);
    // Misconfigure the strength.
    cfg_reg = bitfield_field32_write(cfg_reg, KMAC_CFG_SHADOWED_KSTRENGTH_FIELD,
                                     misconfigured_strength[it]);
    cfg_reg =
        bitfield_field32_write(cfg_reg, KMAC_CFG_SHADOWED_MODE_FIELD, mode[it]);
    mmio_region_write32(kmac.base_addr, KMAC_CFG_SHADOWED_REG_OFFSET, cfg_reg);
    mmio_region_write32(kmac.base_addr, KMAC_CFG_SHADOWED_REG_OFFSET, cfg_reg);

    // Issue start command.
    uint32_t cmd_reg =
        bitfield_field32_write(0, KMAC_CMD_CMD_FIELD, KMAC_CMD_CMD_VALUE_START);
    mmio_region_write32(kmac.base_addr, KMAC_CMD_REG_OFFSET, cmd_reg);

    // Read out error information.
    dif_kmac_error_t err;
    uint32_t info;
    TRY(dif_kmac_get_error(&kmac, &err, &info));
    CHECK(err == kDifErrorUnexpectedModeStrength,
          "Error other than kDifErrorUnexpectedModeStrength occurred.");

    // Reset the KMAC FSM.
    dif_kmac_operation_state_t kmac_operation_state;
    TRY(dif_kmac_reset(&kmac, &kmac_operation_state));
  }

  return OK_STATUS();
}

/**
 * ErrSwPushedMsgFifo.
 *
 * This test checks whether the ErrSwPushedMsgFifo error code is
 * returned by the hardware when writing to the message FIFO without first
 * sending a START command. This is different to the test description in the
 * test plan as writing to the message FIFO during a keymanager app request is
 * not easy to implement. However, this test still checks whether the correct
 * error code is generated.
 *
 * @return OK or error.
 */
status_t test_err_sw_pushed_msg_fifo(void) {
  LOG_INFO("Testing ErrSwPushedMsgFifo error.");
  // Re-init KMAC for the test.
  TRY(dif_kmac_init(mmio_region_from_addr(TOP_EARLGREY_KMAC_BASE_ADDR), &kmac));
  // Configure KMAC to use the sideloaded key.
  CHECK_STATUS_OK(kmac_testutils_config(&kmac, true));

  // Write to message FIFO without sending START command.
  mmio_region_write8(kmac.base_addr, KMAC_MSG_FIFO_REG_OFFSET, 0xff);

  // Read out error information.
  dif_kmac_error_t err;
  uint32_t info;
  TRY(dif_kmac_get_error(&kmac, &err, &info));
  CHECK(err == kDifErrorSoftwarePushedMessageFifo,
        "Error other than kDifErrorSoftwarePushedMessageFifo occurred.");

  // Reset the KMAC FSM.
  dif_kmac_operation_state_t kmac_operation_state;
  TRY(dif_kmac_reset(&kmac, &kmac_operation_state));

  return OK_STATUS();
}

/**
 * ErrorIncorrectFunctionName.
 *
 * This test checks whether the kDifErrorIncorrectFunctionName error code is
 * returned by the hardware when using a wrong (i.e., other than "KMAC")
 * function name when in KMAC mode.
 *
 * @return OK or error.
 */
status_t test_err_incorrect_fnc_name(void) {
  LOG_INFO("Testing kDifErrorIncorrectFunctionName error.");
  // Re-init KMAC for the test.
  TRY(dif_kmac_init(mmio_region_from_addr(TOP_EARLGREY_KMAC_BASE_ADDR), &kmac));
  CHECK_STATUS_OK(kmac_testutils_config(&kmac, false));

  // Configure cSHAKE mode with the given strength and enable KMAC mode.
  uint32_t cfg_reg =
      mmio_region_read32(kmac.base_addr, KMAC_CFG_SHADOWED_REG_OFFSET);
  cfg_reg = bitfield_bit32_write(cfg_reg, KMAC_CFG_SHADOWED_KMAC_EN_BIT, true);
  cfg_reg = bitfield_field32_write(cfg_reg, KMAC_CFG_SHADOWED_KSTRENGTH_FIELD,
                                   KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L256);
  cfg_reg = bitfield_field32_write(cfg_reg, KMAC_CFG_SHADOWED_MODE_FIELD,
                                   KMAC_CFG_SHADOWED_MODE_VALUE_CSHAKE);
  mmio_region_write32(kmac.base_addr, KMAC_CFG_SHADOWED_REG_OFFSET, cfg_reg);
  mmio_region_write32(kmac.base_addr, KMAC_CFG_SHADOWED_REG_OFFSET, cfg_reg);

  // Expected function name is "KMAC", set it to something different in order to
  // trigger the expected error.
  uint32_t prefix_regs[11];
  memset(&prefix_regs, 0xff, ARRAYSIZE(prefix_regs) * sizeof(uint32_t));

  // Write PREFIX register values.
  const mmio_region_t base = kmac.base_addr;
  mmio_region_write32(base, KMAC_PREFIX_0_REG_OFFSET, prefix_regs[0]);
  mmio_region_write32(base, KMAC_PREFIX_1_REG_OFFSET, prefix_regs[1]);
  mmio_region_write32(base, KMAC_PREFIX_2_REG_OFFSET, prefix_regs[2]);
  mmio_region_write32(base, KMAC_PREFIX_3_REG_OFFSET, prefix_regs[3]);
  mmio_region_write32(base, KMAC_PREFIX_4_REG_OFFSET, prefix_regs[4]);
  mmio_region_write32(base, KMAC_PREFIX_5_REG_OFFSET, prefix_regs[5]);
  mmio_region_write32(base, KMAC_PREFIX_6_REG_OFFSET, prefix_regs[6]);
  mmio_region_write32(base, KMAC_PREFIX_7_REG_OFFSET, prefix_regs[7]);
  mmio_region_write32(base, KMAC_PREFIX_8_REG_OFFSET, prefix_regs[8]);
  mmio_region_write32(base, KMAC_PREFIX_9_REG_OFFSET, prefix_regs[9]);
  mmio_region_write32(base, KMAC_PREFIX_10_REG_OFFSET, prefix_regs[10]);

  // Issue start command.
  uint32_t cmd_reg =
      bitfield_field32_write(0, KMAC_CMD_CMD_FIELD, KMAC_CMD_CMD_VALUE_START);
  mmio_region_write32(kmac.base_addr, KMAC_CMD_REG_OFFSET, cmd_reg);

  // Read out error information.
  dif_kmac_error_t err;
  uint32_t info;
  TRY(dif_kmac_get_error(&kmac, &err, &info));
  CHECK(err == kDifErrorIncorrectFunctionName,
        "Error other than kDifErrorIncorrectFunctionName occurred.");

  // Reset the KMAC FSM.
  dif_kmac_operation_state_t kmac_operation_state;
  TRY(dif_kmac_reset(&kmac, &kmac_operation_state));

  return OK_STATUS();
}

bool test_main(void) {
  test_err_wait_timer_expired();
  test_err_incorrect_entropy_mode();
  test_err_sw_cmd_sequence();
  test_err_key_not_valid();
  test_err_unexpected_mode_strength();
  test_err_sw_pushed_msg_fifo();
  test_err_incorrect_fnc_name();

  return true;
}
