// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_csrng.h"
#include "sw/device/lib/dif/dif_entropy_src.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/dif/dif_lc_ctrl.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/csrng_testutils.h"
#include "sw/device/lib/testing/entropy_src_testutils.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/rand_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

enum {
  /**
   * The size of the buffer used in firmware to process the entropy bits in
   * firmware override mode.
   */
  kEntropyFifoBufferSize = 12,
  /**
   * Maximum number of attempts of entropy_src operations that may stall due
   * to FIFO operations.
   */
  kTestParamEntropySrcMaxAttempts = 256,
  /**
   * The size of the exit token in bytes or words.
   */
  kExitTokenSizeInBytes = 16,
  kExitTokenSizeInWords = kExitTokenSizeInBytes / sizeof(uint32_t),
};

// Store CSRNG output in flash to compare results across life cycle stages.
OT_SET_BSS_SECTION(".non_volatile_scratch",
                   uint32_t nv_csrng_output[kEntropyFifoBufferSize];)

static dif_lc_ctrl_t lc_ctrl;
static dif_otp_ctrl_t otp_ctrl;
static dif_csrng_t csrng;
static dif_entropy_src_t entropy_src;
static dif_flash_ctrl_state_t flash_ctrl_state;
static dif_kmac_t kmac;
static dif_rstmgr_t rstmgr;

// LC exit token value for LC state transition.
static const dif_lc_ctrl_token_t kLcExitToken = {
    .data =
        {
            0x00,
            0x01,
            0x02,
            0x03,
            0x04,
            0x05,
            0x06,
            0x07,
            0x08,
            0x09,
            0x0a,
            0x0b,
            0x0c,
            0x0d,
            0x0e,
            0x0f,
        },
};
static_assert(kExitTokenSizeInBytes == ARRAYSIZE(kLcExitToken.data),
              "Invalid exit token size.");

/**
 * Initializes KMAC with software provided entropy to avoid sending requests to
 * EDN0.
 */
static void kmac_init(void) {
  CHECK_DIF_OK(
      dif_kmac_init(mmio_region_from_addr(TOP_EARLGREY_KMAC_BASE_ADDR), &kmac));

  // Configure KMAC hardware using software entropy.
  dif_kmac_config_t config = (dif_kmac_config_t){
      .entropy_mode = kDifKmacEntropyModeSoftware,
      .entropy_seed = {0xb153e3fe, 0x09596819, 0x3e85a6e8, 0xb6dcdaba,
                       0x50dc409c, 0x11e1ebd1},
      .entropy_fast_process = kDifToggleEnabled,
  };
  CHECK_DIF_OK(dif_kmac_configure(&kmac, config));
}

/**
 * Initializes the peripherals used in this test.
 */
static void peripherals_init(void) {
  CHECK_DIF_OK(dif_csrng_init(
      mmio_region_from_addr(TOP_EARLGREY_CSRNG_BASE_ADDR), &csrng));
  CHECK_DIF_OK(dif_lc_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_LC_CTRL_REGS_BASE_ADDR), &lc_ctrl));
  CHECK_DIF_OK(dif_entropy_src_init(
      mmio_region_from_addr(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR), &entropy_src));
  CHECK_DIF_OK(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp_ctrl));
  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));

  CHECK_DIF_OK(dif_flash_ctrl_init_state(
      &flash_ctrl_state,
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));

  kmac_init();
}

/**
 * Calculates the cShake128 of the test exit token and returns its
 * representation in two 64bit halves.
 *
 * @param[out] otp_token_l Lower half of the text exit token.
 * @param[out] otp_token_h Higher half of the text exit token.
 */
static void exit_token_cshake_hash(uint64_t *otp_token_l,
                                   uint64_t *otp_token_h) {
  dif_kmac_customization_string_t s;
  CHECK_DIF_OK(
      dif_kmac_customization_string_init(/*data=*/"LC_CTRL", /*len=*/7, &s));

  dif_kmac_operation_state_t op_state;
  CHECK_DIF_OK(dif_kmac_mode_cshake_start(
      &kmac, &op_state, kDifKmacModeCshakeLen128, /*n=*/NULL, &s));
  CHECK_DIF_OK(dif_kmac_absorb(&kmac, &op_state, kLcExitToken.data,
                               ARRAYSIZE(kLcExitToken.data),
                               /*processed=*/NULL));

  uint32_t token_hash[kExitTokenSizeInWords];
  CHECK_DIF_OK(dif_kmac_squeeze(&kmac, &op_state, token_hash,
                                kExitTokenSizeInWords, /*processed=*/NULL,
                                /*capacity=*/NULL));
  CHECK_DIF_OK(dif_kmac_end(&kmac, &op_state));

  *otp_token_l = 0;
  *otp_token_h = 0;
  uint8_t *p_token = (uint8_t *)token_hash;
  for (size_t i = 0; i < kExitTokenSizeInBytes; i++) {
    if (i < kExitTokenSizeInBytes / 2) {
      *otp_token_l |= (uint64_t)p_token[i] << (i * 8);
    } else {
      *otp_token_h |= (uint64_t)p_token[i]
                      << ((i - kExitTokenSizeInBytes / 2) * 8);
    }
  }
}

/**
 * Configures the test exit token and locks down the secret0 partition.
 */
static void lock_otp_secret0_partition(void) {
  uint64_t otp_token_l;
  uint64_t opt_token_h;
  exit_token_cshake_hash(&otp_token_l, &opt_token_h);

  CHECK_DIF_OK(dif_otp_ctrl_dai_program64(&otp_ctrl,
                                          kDifOtpCtrlPartitionSecret0,
                                          /*address=*/0x10,
                                          /*value=*/otp_token_l));
  CHECK_STATUS_OK(otp_ctrl_testutils_wait_for_dai(&otp_ctrl));
  CHECK_DIF_OK(dif_otp_ctrl_dai_program64(&otp_ctrl,
                                          kDifOtpCtrlPartitionSecret0,
                                          /*address=*/0x18,
                                          /*value=*/opt_token_h));
  CHECK_STATUS_OK(otp_ctrl_testutils_wait_for_dai(&otp_ctrl));

  CHECK_DIF_OK(dif_otp_ctrl_dai_digest(&otp_ctrl, kDifOtpCtrlPartitionSecret0,
                                       /*digest=*/0));
  CHECK_STATUS_OK(otp_ctrl_testutils_wait_for_dai(&otp_ctrl));
}

/**
 * Retuns a random pick one DEV, PROD or PROD_END lc state.
 */
static dif_lc_ctrl_state_t lc_next_state(void) {
  uint32_t index = rand_testutils_gen32_range(/*min=*/0, /*max=*/2);
  dif_lc_ctrl_state_t next_state;
  switch (index) {
    case 0:
      next_state = kDifLcCtrlStateDev;
      break;
    case 1:
      next_state = kDifLcCtrlStateProd;
      break;
    case 2:
      next_state = kDifLcCtrlStateProdEnd;
      break;
    default:
      CHECK(false, "Unexpected case index: %d", index);
      return kDifLcCtrlStateInvalid;
  }
  return next_state;
}

/**
 * Stops the entropy_src conditioner.
 *
 * @param entropy_src A entropy source handle.
 */
static void entropy_conditioner_stop(const dif_entropy_src_t *entropy_src) {
  uint32_t fail_count = 0;
  dif_result_t op_result;
  do {
    op_result = dif_entropy_src_conditioner_stop(entropy_src);
    if (op_result == kDifIpFifoFull) {
      CHECK(fail_count++ < kTestParamEntropySrcMaxAttempts);
    } else {
      CHECK_DIF_OK(op_result);
    }
  } while (op_result == kDifIpFifoFull);
}

/**
 * Writes data to the entropy source firmware override buffer.
 *
 * @param entropy_src A entropy source handle.
 */
static void fw_override_conditioner_write(
    const dif_entropy_src_t *entropy_src) {
  CHECK_DIF_OK(dif_entropy_src_conditioner_start(entropy_src));

  const uint32_t kInputMsg[kEntropyFifoBufferSize] = {
      0xa52a0da9, 0xcae141b2, 0x6d5bab9d, 0x2c3e5cc0, 0x225afc93, 0x5d31a610,
      0x91b7f960, 0x0d566bb3, 0xef35e170, 0x94ba7d8e, 0x534eb741, 0x6b60b0da,
  };

  uint32_t fail_count = 0;
  uint32_t total = 0;
  do {
    uint32_t count;
    dif_result_t op_result = dif_entropy_src_fw_ov_data_write(
        entropy_src, kInputMsg + total, ARRAYSIZE(kInputMsg) - total, &count);
    total += count;
    if (op_result == kDifIpFifoFull) {
      CHECK(fail_count++ < kTestParamEntropySrcMaxAttempts);
    } else {
      fail_count = 0;
      CHECK_DIF_OK(op_result);
    }
  } while (total < ARRAYSIZE(kInputMsg));
  entropy_conditioner_stop(entropy_src);
}

/**
 * Issues CSRNG instantiate and generate command.
 *
 * @param[out] output Output buffer.
 * @param output_len Requested number of entropy words. It must be at least the
 * size of the `output` buffer.
 */
static void csrng_static_generate_run(uint32_t *output, size_t output_len) {
  CHECK_STATUS_OK(entropy_testutils_stop_all());
  // TODO: May need to flush the output buffers before enabling enabling
  // firmware override connected to csrng.
  CHECK_STATUS_OK(entropy_src_testutils_fw_override_enable(
      &entropy_src, kEntropyFifoBufferSize,
      /*firmware_override_enable=*/false,
      /*bypass_conditioner=*/false));
  CHECK_DIF_OK(dif_csrng_configure(&csrng));
  fw_override_conditioner_write(&entropy_src);

  const dif_csrng_seed_material_t kEmptySeedMaterial = {0};
  CHECK_DIF_OK(dif_csrng_instantiate(&csrng, kDifCsrngEntropySrcToggleEnable,
                                     &kEmptySeedMaterial));

  CHECK_STATUS_OK(
      csrng_testutils_cmd_generate_run(&csrng, NULL, output, output_len));
  uint32_t prev_word = 0;
  for (size_t i = 0; i < output_len; ++i) {
    CHECK(prev_word != output[i],
          "Unexpected duplicate value at index: %d value: 0x%x", i, prev_word);
    prev_word = output[i];
  }
}

bool test_main(void) {
  peripherals_init();
  CHECK_STATUS_OK(
      flash_ctrl_testutils_default_region_access(&flash_ctrl_state,
                                                 /*rd_en=*/true,
                                                 /*prog_en=*/true,
                                                 /*erase_en=*/true,
                                                 /*scramble_en=*/false,
                                                 /*ecc_en=*/false,
                                                 /*he_en=*/false));

  dif_rstmgr_reset_info_bitfield_t rst_info = rstmgr_testutils_reason_get();
  rstmgr_testutils_reason_clear();

  dif_lc_ctrl_state_t lc_state;
  CHECK_DIF_OK(dif_lc_ctrl_get_state(&lc_ctrl, &lc_state));
  LOG_INFO("lc state: %d", lc_state);

  if (rst_info == kDifRstmgrResetInfoPor &&
      lc_state == kDifLcCtrlStateTestUnlocked0) {
    enum {
      kPartitionId = 0,
    };
    uint32_t address =
        (uint32_t)(nv_csrng_output)-TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR;
    uint32_t expected[kEntropyFifoBufferSize];
    csrng_static_generate_run(expected, ARRAYSIZE(expected));
    CHECK_STATUS_OK(flash_ctrl_testutils_write(&flash_ctrl_state, address,
                                               /*partition_id=*/0, expected,
                                               kDifFlashCtrlPartitionTypeData,
                                               ARRAYSIZE(expected)));
    CHECK_ARRAYS_EQ(nv_csrng_output, expected, ARRAYSIZE(expected));

    lock_otp_secret0_partition();
    CHECK_DIF_OK(dif_rstmgr_software_device_reset(&rstmgr));

    // The CPU may be able to continue execution before the reset takes effect.
    wait_for_interrupt();
    CHECK(false, "Unexpected wakeup.");
  } else if (rst_info == kDifRstmgrResetInfoSw &&
             lc_state == kDifLcCtrlStateTestUnlocked0) {
    uint32_t got[kEntropyFifoBufferSize];
    csrng_static_generate_run(got, ARRAYSIZE(got));
    static_assert(ARRAYSIZE(got) == ARRAYSIZE(nv_csrng_output),
                  "Array size mismatch.");
    CHECK_ARRAYS_EQ(got, nv_csrng_output, ARRAYSIZE(got));

    CHECK_DIF_OK(dif_lc_ctrl_mutex_try_acquire(&lc_ctrl));
    CHECK_DIF_OK(dif_lc_ctrl_configure(&lc_ctrl, lc_next_state(),
                                       /*use_ext_clock=*/false, &kLcExitToken),
                 "LC transition configuration failed!");

    CHECK_DIF_OK(dif_lc_ctrl_transition(&lc_ctrl), "LC transition failed!");

    // SV testbench waits for this message.
    LOG_INFO("LC transition in progress.");
    wait_for_interrupt();
    CHECK(false, "Unexpected wakeup.");
  } else {
    CHECK(lc_state == kDifLcCtrlStateDev || lc_state == kDifLcCtrlStateProd ||
              lc_state == kDifLcCtrlStateProdEnd,
          "Unexpected LC state: %d", lc_state);
    uint32_t got[kEntropyFifoBufferSize];
    csrng_static_generate_run(got, ARRAYSIZE(got));
    static_assert(ARRAYSIZE(got) == ARRAYSIZE(nv_csrng_output),
                  "Array size mismatch.");

    if (lc_state == kDifLcCtrlStateDev) {
      CHECK_ARRAYS_EQ(got, nv_csrng_output, ARRAYSIZE(got));
    } else {
      CHECK_ARRAYS_NE(got, nv_csrng_output, ARRAYSIZE(got));
    }
    return true;
  }
  CHECK(false, "Invalid reset: %d, or LC state: %d", rst_info, lc_state);
  return false;
}
