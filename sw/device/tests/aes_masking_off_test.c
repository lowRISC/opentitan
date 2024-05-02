// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "hw/ip/aes/model/aes_modes.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/ip/aes/dif/dif_aes.h"
#include "sw/ip/aes/test/utils/aes_testutils.h"
#include "sw/ip/csrng/dif/dif_csrng.h"
#include "sw/ip/csrng/dif/shared/dif_csrng_shared.h"
#include "sw/ip/csrng/test/utils/csrng_testutils.h"
#include "sw/ip/edn/dif/dif_edn.h"
#include "sw/lib/sw/device/base/memory.h"
#include "sw/lib/sw/device/base/mmio.h"
#include "sw/lib/sw/device/base/multibits.h"
#include "sw/lib/sw/device/runtime/log.h"

#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"

enum {
  kTestTimeout = (1000 * 1000),
};

// The mask share, used to mask kKey. Note that the masking should not be done
// manually. Software is expected to get the key in two shares right from the
// beginning.
static const uint8_t kKeyShare1[] = {
    0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
    0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
    0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
};

OTTF_DEFINE_TEST_CONFIG();

status_t execute_test(void) {
  // Perform the known-answer testing on the CSRNG SW application interface.
  CHECK_STATUS_OK(aes_testutils_csrng_kat());

  // Test AES with masking switched off.
  //
  // For this to work:
  // - CSRNG needs to generate the required seed to have the AES masking PRNG
  //   output an all-zero vector and forward that to AES over EDN.
  // - AES needs to be configured with the CTRL_AUX_SHADOWED.FORCE_MASKS bit
  //   set.
  // - Share 1 of the initial key must be an all-zero vector.
  //
  // Since the masking is transparent to software, software cannot actually
  // verify that the masking is off. Instead, DV needs to probe into the design.
  LOG_INFO("Testing AES with masking switched off");

  // Initialize EDN and CSRNG to generate the required seed.
  CHECK_STATUS_OK(aes_testutils_masking_prng_zero_output_seed());

  // Initialise AES.
  dif_aes_t aes;
  CHECK_DIF_OK(
      dif_aes_init(mmio_region_from_addr(TOP_DARJEELING_AES_BASE_ADDR), &aes));
  CHECK_DIF_OK(dif_aes_reset(&aes));

  // Mask the key. Note that this should not be done manually. Software is
  // expected to get the key in two shares right from the beginning.
  uint8_t key_share0[sizeof(kAesModesKey128)];
  for (int i = 0; i < sizeof(kAesModesKey128); ++i) {
    key_share0[i] = kAesModesKey128[i] ^ kKeyShare1[i];
  }

  // "Convert" key share byte arrays to `dif_aes_key_share_t`.
  dif_aes_key_share_t key;
  memcpy(key.share0, key_share0, sizeof(key.share0));
  memcpy(key.share1, kKeyShare1, sizeof(key.share1));

  // Setup ECB encryption transaction with the CTRL_AUX_SHADOWED.FORCE_MASKS bit
  // set.
  dif_aes_transaction_t transaction = {
      .operation = kDifAesOperationEncrypt,
      .mode = kDifAesModeEcb,
      .key_len = kDifAesKey128,
      .key_provider = kDifAesKeySoftwareProvided,
      .mask_reseeding = kDifAesReseedPer8kBlock,
      .manual_operation = kDifAesManualOperationAuto,
      .reseed_on_key_change = false,
      .force_masks = true,
      .ctrl_aux_lock = false,
  };
  CHECK_DIF_OK(dif_aes_start(&aes, &transaction, &key, NULL));

  // Trigger a reseed of the internal PRNGs. This will load the seed generated
  // by CSRNG to be loaded into the AES masking PRNG. After this point, the AES
  // masking PRNG outputs an all-zero vector.
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusIdle, true, kTestTimeout);
  CHECK_DIF_OK(dif_aes_trigger(&aes, kDifAesTriggerPrngReseed));
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusIdle, true, kTestTimeout);

  // Trigger the clearing of the output data registers. After this point, also
  // the PRNG buffer stage will output an all-zero vector.
  CHECK_DIF_OK(dif_aes_trigger(&aes, kDifAesTriggerDataOutClear));
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusIdle, true, kTestTimeout);

  // "Convert" plain data byte arrays to `dif_aes_data_t` array.
  enum {
    kAesNumBlocks = 4,
  };
  dif_aes_data_t plain_text[kAesNumBlocks];
  dif_aes_data_t cipher_text[kAesNumBlocks];
  memcpy(plain_text[0].data, kAesModesPlainText, sizeof(kAesModesPlainText));

  // Encrypt kAesNumBlocks blocks.
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusInputReady, true,
                                kTestTimeout);
  CHECK_DIF_OK(dif_aes_process_data(&aes, plain_text, cipher_text,
                                    (size_t)kAesNumBlocks));

  // Check the produced cipher text.
  CHECK_ARRAYS_EQ((uint8_t *)cipher_text[0].data, kAesModesCipherTextEcb128,
                  sizeof(kAesModesCipherTextEcb128));
  return OK_STATUS();
}

bool test_main(void) {
  // Test seed generation using CSRNG SW application interface.
  //
  // We try to generate the seed leading to an all-zero output of the AES
  // masking PRNG using the CSRNG SW application interface. Unlike the HW
  // application interfaces of CSRNG that connect to the EDNs, this interface
  // allows for probing the internal state of the CSRNG instance after
  // individual commands. This gives us higher visibility. If for some reason
  // this phase isn't succesful, we don't even need to try it on the HW
  // interfaces.
  LOG_INFO("Testing CSRNG SW application interface");

  // Disable EDN connected to AES as well as CSRNG.
  const dif_edn_t edn = {
      .base_addr = mmio_region_from_addr(TOP_DARJEELING_EDN0_BASE_ADDR)};
  const dif_csrng_t csrng = {
      .base_addr = mmio_region_from_addr(TOP_DARJEELING_CSRNG_BASE_ADDR)};
  CHECK_DIF_OK(dif_edn_stop(&edn));
  CHECK_DIF_OK(dif_csrng_stop(&csrng));

  // Re-eanble CSRNG.
  CHECK_DIF_OK(dif_csrng_configure(&csrng));

  return status_ok(execute_test());
}
