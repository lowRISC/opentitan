// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <string.h>

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_aes.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_entropy_src.h"
#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aes_testutils.h"
#include "sw/device/lib/testing/edn_testutils.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/kmac_testutils.h"
#include "sw/device/lib/testing/rand_testutils.h"
#include "sw/device/lib/testing/rv_core_ibex_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/tests/otbn_randomness_impl.h"

#include "entropy_src_regs.h"                         // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.

OTTF_DEFINE_TEST_CONFIG();

enum {
  kEntropySrcHealthTestWindowSize = 0x200,
  /**
   * Observe FIFO threshold: half of the FIFO size.
   */
  kEntropySrcFifoThreshold = 16,
  /**
   * The number of contiguous samples we want to capture.
   */
  kContiguousSamplesCount = 1024,
  /**
   * Number of bits per sample.
   */
  kBitsPerSample = 4,
  /**
   * Size of buffer in words to hold all the samples, assuming
   * 4-bit samples at the most.
   */
  kFifoBufferSizeWords =
      kContiguousSamplesCount * kBitsPerSample / sizeof(uint32_t),
  /**
   * Maximum number of words to move from the output buffer in one ISR.
   *
   * This number has to be small otherwise the conditioner runs for too long
   * and blocks the ISR.
   */
  kMaxOutputWords = 16,
  /**
   * Number of micro seconds we wait between having extracted words from the
   * observe FIFO and inserting words back into the entropy source.
   */
  kOutputDelayUs = 128,
  /**
   * The size of the buffer used in firmware to process the entropy bits in
   * firmware override mode.
   */
  kEntropyFifoBufferSize = 12,
};

static dif_aes_t aes;
static dif_csrng_t csrng;
static dif_edn_t edn0;
static dif_edn_t edn1;
static dif_entropy_src_t entropy_src;
static dif_kmac_t kmac;
static dif_otbn_t otbn;
static dif_rv_core_ibex_t rv_core_ibex;
static dif_rv_plic_t rv_plic;

// Buffers to collect samples into.
//
// We use a double-buffering approach, where one buffer is for the "input"
// samples that we read from the observe FIFO, and the other is for "output"
// samples that we need to write to the conditioner.
//
// When the input buffer is filled and the output buffer is empty, we swap them
// and the bytes we collected are written out to the conditioner. The input
// buffer is now empty, and we can start writing new samples to it.
static uint32_t sample_buf_0[kFifoBufferSizeWords];
static uint32_t sample_buf_1[kFifoBufferSizeWords];

// These pointers track which buffer is the input or the output and are cursors
// into where we have written to / read from them so far.
static uint32_t *input_buf = sample_buf_0;
static uint32_t *output_buf = sample_buf_1 + kFifoBufferSizeWords;

// These counters track how many words are remaining to be written to the input
// buffer or read out of the output buffer.
static size_t words_to_input = kFifoBufferSizeWords;
static size_t words_to_output = 0;

static dif_edn_auto_params_t edn_params0;
static dif_edn_auto_params_t edn_params1;

static bool fw_ov_insert_wait_enabled = false;

/**
 * Determine whether the observe FIFO has overflowed.
 *
 * TODO(#21279) Normally, one would rely on the FW_OV_RD_FIFO_OVERFLOW
 * register but due to an RTL bug, the overflow bit is pulsed
 * instead of latched so we cannot rely on it. Instead, rely
 * on OBSERVE_FIFO_DEPTH and assume that if the FIFO is full
 * then it has overflowed.
 */
bool entropy_src_fifo_has_overflowed(void) {
  uint32_t fifo_depth;
  CHECK_DIF_OK(dif_entropy_src_get_fifo_depth(&entropy_src, &fifo_depth));
  return fifo_depth == ENTROPY_SRC_PARAM_OBSERVE_FIFO_DEPTH;
}

void ottf_external_isr(uint32_t *exc_info) {
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(dif_rv_plic_irq_claim(&rv_plic, kTopEarlgreyPlicTargetIbex0,
                                     &plic_irq_id));

  top_earlgrey_plic_peripheral_t peripheral =
      top_earlgrey_plic_interrupt_for_peripheral[plic_irq_id];
  CHECK(peripheral == kTopEarlgreyPlicPeripheralEntropySrc);

  // If the observe buffer overflows while we're still collecting samples
  // then we need to drain it and start again or our samples won't be
  // contiguous.
  if (words_to_input > 0 && entropy_src_fifo_has_overflowed()) {
    CHECK_STATUS_OK(entropy_testutils_drain_observe_fifo(&entropy_src));
    // Reset the input buffer.
    input_buf -= (kFifoBufferSizeWords - words_to_input);
    words_to_input = kFifoBufferSizeWords;
  }

  if (words_to_input > 0) {
    // Move at most `kEntropySrcFifoThreshold` into the input buffer.
    // We don't want to slow down this ISR by copying too many words or waiting
    // for more entropy to arrive.
    size_t len = words_to_input;
    if (len > kEntropySrcFifoThreshold) {
      len = kEntropySrcFifoThreshold;
    }

    CHECK_DIF_OK(dif_entropy_src_observe_fifo_nonblocking_read(
        &entropy_src, input_buf, &len));

    input_buf += len;
    words_to_input -= len;
  }

  // If we've filled the input buffer and drained the output buffer, swap
  // them.
  if (words_to_input == 0 && words_to_output == 0) {
    // Swap the buffers.
    uint32_t *output_tmp = output_buf;
    output_buf = input_buf - kFifoBufferSizeWords;
    input_buf = output_tmp - kFifoBufferSizeWords;

    words_to_input = kFifoBufferSizeWords;
    words_to_output = kFifoBufferSizeWords;
  }

  if (fw_ov_insert_wait_enabled) {
    busy_spin_micros(kOutputDelayUs);
  }

  if (words_to_output > 0) {
    // Move out at most `kMaxOutputWords` into the override FIFO.
    size_t len = words_to_output;
    if (len > kMaxOutputWords) {
      len = kMaxOutputWords;
    }

    // Start the SHA3 process so that it is ready to accept entropy data.
    CHECK_DIF_OK(dif_entropy_src_fw_override_sha3_start_insert(
        &entropy_src, kDifToggleEnabled));

    size_t words_written = 0;
    CHECK_DIF_OK(dif_entropy_src_fw_ov_data_write(&entropy_src, output_buf, len,
                                                  &words_written));

    output_buf += words_written;
    words_to_output -= words_written;

    // Stop the SHA3 process causing it to finish up and push the results
    // through the rest of the entropy source.
    CHECK_DIF_OK(dif_entropy_src_fw_override_sha3_start_insert(
        &entropy_src, kDifToggleDisabled));
  }

  CHECK_DIF_OK(dif_entropy_src_irq_acknowledge(
      &entropy_src, kDifEntropySrcIrqEsObserveFifoReady));

  CHECK_DIF_OK(dif_rv_plic_irq_complete(&rv_plic, kTopEarlgreyPlicTargetIbex0,
                                        plic_irq_id));
}

static status_t configure_interrupts(void) {
  TRY(dif_rv_plic_irq_set_priority(
      &rv_plic, kTopEarlgreyPlicIrqIdEntropySrcEsObserveFifoReady, 0x1));

  TRY(dif_rv_plic_target_set_threshold(&rv_plic, kTopEarlgreyPlicTargetIbex0,
                                       0x0));

  TRY(dif_rv_plic_irq_set_enabled(
      &rv_plic, kTopEarlgreyPlicIrqIdEntropySrcEsObserveFifoReady,
      kTopEarlgreyPlicTargetIbex0, kDifToggleEnabled));

  TRY(dif_entropy_src_irq_set_enabled(
      &entropy_src, kDifEntropySrcIrqEsObserveFifoReady, kDifToggleEnabled));

  return OK_STATUS();
}

// Configure the entropy complex.
static status_t entropy_config(
    dif_entropy_src_single_bit_mode_t single_bit_mode,
    bool bypass_conditioner) {
  // Don't let the extract and insert interrupt handler run until we've enabled
  // the entropy source.
  irq_external_ctrl(false);

  LOG_INFO("Disabling entropy complex");
  // Disable the entropy complex.
  TRY(entropy_testutils_stop_all());
  // Disable all health tests.
  TRY(entropy_testutils_disable_health_tests(&entropy_src));

  // Enable FW override.
  TRY(dif_entropy_src_fw_override_configure(
      &entropy_src,
      (dif_entropy_src_fw_override_config_t){
          .entropy_insert_enable = true,
          .buffer_threshold = kEntropySrcFifoThreshold,
      },
      kDifToggleEnabled));

  // Enable entropy_src.
  LOG_INFO("Enabling entropy source");
  TRY(dif_entropy_src_configure(
      &entropy_src,
      (dif_entropy_src_config_t){
          .fips_enable = true,
          .fips_flag = true,
          .rng_fips = true,
          .route_to_firmware = false,
          .bypass_conditioner = bypass_conditioner,
          .single_bit_mode = single_bit_mode,
          .health_test_threshold_scope = false,
          .health_test_window_size = kEntropySrcHealthTestWindowSize,
          .alert_threshold = UINT16_MAX},
      kDifToggleEnabled));

  // Enable the interrupt handler to provide CSRNG with entropy.
  irq_external_ctrl(true);

  // Enable CSRNG
  LOG_INFO("Enabling CSRNG");
  TRY(dif_csrng_configure(&csrng));

  // Enable EDNs in auto request mode
  LOG_INFO("Enabling EDNs");
  TRY(dif_edn_set_auto_mode(&edn0, edn_params0));
  TRY(dif_edn_set_auto_mode(&edn1, edn_params1));

  LOG_INFO("Entropy complex configured");

  return OK_STATUS();
}

// Configure the entropy complex.
static status_t reenable_entropy_src(
    dif_entropy_src_single_bit_mode_t single_bit_mode,
    bool bypass_conditioner) {
  uint32_t data;
  bool entropy_req_intr = false;
  size_t words_written = 0;
  uint32_t kInputMsg[kEntropyFifoBufferSize];
  uint32_t cnt = 0;

  // Don't let the extract and insert interrupt handler run until we've
  // re-enabled the entropy source.
  irq_external_ctrl(false);

  // Make ENTROPY_SRC produce new seeds until CSRNG has no outstanding
  // entropy requests.
  do {
    // If the FW_OV_WR_DATA register is not ready yet,
    // we wait for a bit and try again.
    data = mmio_region_read32(entropy_src.base_addr,
                              ENTROPY_SRC_FW_OV_WR_FIFO_FULL_REG_OFFSET);
    if (data) {
      busy_spin_micros(10);
      continue;
    }
    // Make SHA3 absorb new data and produce a new seed right away.
    // We use a counter for the input message to avoid triggering
    // ES_BUS_CMP_ALERT.
    CHECK_DIF_OK(dif_entropy_src_fw_override_sha3_start_insert(
        &entropy_src, kDifToggleEnabled));
    for (int i = 0; i < kEntropyFifoBufferSize; i++) {
      kInputMsg[i] = cnt++;
    }
    CHECK_DIF_OK(dif_entropy_src_fw_ov_data_write(
        &entropy_src, (const uint32_t *)kInputMsg, kEntropyFifoBufferSize,
        &words_written));
    CHECK_DIF_OK(dif_entropy_src_fw_override_sha3_start_insert(
        &entropy_src, kDifToggleDisabled));
    // Clear CS_ENTROPY_REQ and check if it is reasserted.
    // If not, we can disable ENTROPY_SRC and check if the entropy
    // complex still produces entropy after reenabling ENTROPY_SRC.
    CHECK_DIF_OK(dif_csrng_irq_acknowledge_state(
        &csrng, 1 << CSRNG_INTR_STATE_CS_ENTROPY_REQ_BIT));
    CHECK_DIF_OK(dif_csrng_irq_is_pending(
        &csrng, CSRNG_INTR_STATE_CS_ENTROPY_REQ_BIT, &entropy_req_intr));
  } while (entropy_req_intr);

  // Disable the entropy source.
  LOG_INFO("Disabling entropy_src");
  TRY(dif_entropy_src_set_enabled(&entropy_src, kDifToggleDisabled));

  // Wait for CSRNG to request a seed while ENTROPY_SRC is diabled.
  do {
    if (rv_core_ibex_testutils_is_rnd_data_valid(&rv_core_ibex)) {
      TRY(dif_rv_core_ibex_read_rnd_data(&rv_core_ibex, &data));
    }
    CHECK_DIF_OK(dif_csrng_irq_is_pending(
        &csrng, CSRNG_INTR_STATE_CS_ENTROPY_REQ_BIT, &entropy_req_intr));
  } while (!entropy_req_intr);

  // Reenable ENTROPY_SRC now that CSRNG has an outstanding entropy request.
  TRY(dif_entropy_src_set_enabled(&entropy_src, kDifToggleEnabled));
  LOG_INFO("ENTROPY_SRC re-enabled");

  // Enable the interrupt handler to provide CSRNG with entropy.
  irq_external_ctrl(true);

  return OK_STATUS();
}

/**
 * Configure the entropy source in extract and insert mode and run some entropy
 * consumers.
 */
status_t firmware_override_extract_insert(
    dif_entropy_src_single_bit_mode_t single_bit_mode, bool bypass_conditioner,
    bool reenable_es) {
  LOG_INFO("==================");
  LOG_INFO("Configuring single_bit_mode=%u, bypass_conditioner=%d",
           single_bit_mode, bypass_conditioner);

  entropy_config(single_bit_mode, bypass_conditioner);

  // Generate some random numbers.
  LOG_INFO("Generating random numbers...");
  uint32_t data;
  for (size_t i = 0; i < 16; i++) {
    TRY(rv_core_ibex_testutils_get_rnd_data(&rv_core_ibex,
                                            /*timeout_usec=*/100 * 1000,
                                            &data));
  }

  if (reenable_es) {
    // Now that we know that a seed was produced we reenable the entropy_src
    // and see whether the entropy complex still works as expected.
    reenable_entropy_src(single_bit_mode, bypass_conditioner);
  }

  // Run an AES encryption and decryption process.
  dif_aes_transaction_t transaction = {
      .operation = kDifAesOperationEncrypt,
      .mode = kDifAesModeEcb,
      .key_len = kDifAesKey256,
      .key_provider = kDifAesKeySoftwareProvided,
      .mask_reseeding = kDifAesReseedPerBlock,
      .manual_operation = kDifAesManualOperationAuto,
      .reseed_on_key_change = true,
      .ctrl_aux_lock = false,
  };

  LOG_INFO("Running AES...");
  TRY(aes_testutils_setup_encryption(transaction, &aes));
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusOutputValid, true,
                                /*timeout_usec=*/1 * 1000 * 1000);
  TRY(aes_testutils_decrypt_ciphertext(transaction, &aes));

  // Run KMAC
  dif_kmac_config_t config = {
      .entropy_mode = kDifKmacEntropyModeEdn,
      .entropy_fast_process = false,
      .entropy_seed = {0},
      .entropy_hash_threshold = 1,
      .entropy_wait_timer = 0,
      .entropy_prescaler = 0,
      .message_big_endian = false,
      .output_big_endian = false,
      .sideload = false,
      .msg_mask = true,
  };
  TRY(dif_kmac_configure(&kmac, config));

  dif_kmac_key_t software_key = {
      .share0 = {0x43424140, 0x47464544, 0x4B4A4948, 0x4F4E4D4C, 0x53525150,
                 0x57565554, 0x5B5A5958, 0x5F5E5D5C},
      .share1 = {0},
      .length = kDifKmacKeyLen256,
  };
  uint32_t output[8];
  LOG_INFO("Running KMAC...");
  TRY(kmac_testutils_kmac(&kmac, kDifKmacModeKmacLen128, &software_key,
                          /*custom_string=*/NULL, /*custom_string_len=*/0,
                          /*message=*/"hello", /*message_len=*/6,
                          ARRAYSIZE(output), output, /*capacity=*/NULL));

  LOG_INFO("Running OTBN...");
  otbn_randomness_test_start(&otbn, /*iters=*/10);
  TRY_CHECK(otbn_randomness_test_end(&otbn, /*skip_otbn_done_check=*/false));

  return OK_STATUS();
}

bool test_main(void) {
  mmio_region_t base_addr;

  base_addr = mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR);
  CHECK_DIF_OK(dif_aes_init(base_addr, &aes));
  base_addr = mmio_region_from_addr(TOP_EARLGREY_CSRNG_BASE_ADDR);
  CHECK_DIF_OK(dif_csrng_init(base_addr, &csrng));
  base_addr = mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR);
  CHECK_DIF_OK(dif_edn_init(base_addr, &edn0));
  base_addr = mmio_region_from_addr(TOP_EARLGREY_EDN1_BASE_ADDR);
  CHECK_DIF_OK(dif_edn_init(base_addr, &edn1));
  base_addr = mmio_region_from_addr(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR);
  CHECK_DIF_OK(dif_entropy_src_init(base_addr, &entropy_src));
  base_addr = mmio_region_from_addr(TOP_EARLGREY_KMAC_BASE_ADDR);
  CHECK_DIF_OK(dif_kmac_init(base_addr, &kmac));
  base_addr = mmio_region_from_addr(TOP_EARLGREY_OTBN_BASE_ADDR);
  CHECK_DIF_OK(dif_otbn_init(base_addr, &otbn));
  base_addr = mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_core_ibex_init(base_addr, &rv_core_ibex));
  base_addr = mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_plic_init(base_addr, &rv_plic));

  LOG_INFO("Configuring interrupts...");
  configure_interrupts();
  irq_global_ctrl(true);
  irq_external_ctrl(false);

  LOG_INFO("Computing EDN parameters");
  edn_params0 = edn_testutils_auto_params_build(
      /*disable_rand=*/true, /*res_itval=*/1, /*glen_val=*/1);
  edn_params1 = edn_testutils_auto_params_build(
      /*disable_rand=*/true, /*res_itval=*/1, /*glen_val=*/1);

  // Test all modes.
  static dif_entropy_src_single_bit_mode_t kModes[] = {
      kDifEntropySrcSingleBitModeDisabled, kDifEntropySrcSingleBitMode0,
      kDifEntropySrcSingleBitMode1,        kDifEntropySrcSingleBitMode2,
      kDifEntropySrcSingleBitMode3,
  };

  status_t test_result = OK_STATUS();

  for (size_t i = 0; i < ARRAYSIZE(kModes); i++) {
    EXECUTE_TEST(test_result, firmware_override_extract_insert, kModes[i],
                 false, false);
    EXECUTE_TEST(test_result, firmware_override_extract_insert, kModes[i], true,
                 false);
  }
  // Rerun the test with single bit mode disabled, this time we reenable the
  // entropy_src without reenabling the rest of the entropy complex.
  EXECUTE_TEST(test_result, firmware_override_extract_insert,
               kDifEntropySrcSingleBitModeDisabled, false, true);
  EXECUTE_TEST(test_result, firmware_override_extract_insert,
               kDifEntropySrcSingleBitModeDisabled, true, true);
  // Rerun the test with single bit mode disabled,
  // this time with an output delay.
  fw_ov_insert_wait_enabled = true;
  EXECUTE_TEST(test_result, firmware_override_extract_insert,
               kDifEntropySrcSingleBitModeDisabled, false, false);
  EXECUTE_TEST(test_result, firmware_override_extract_insert,
               kDifEntropySrcSingleBitModeDisabled, true, false);

  return status_ok(test_result);
}
