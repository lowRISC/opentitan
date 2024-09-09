// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "hw/ip/aes/model/aes_modes.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_aes.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aes_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#define TIMEOUT (1000 * 1000)

// The mask share, used to mask kKey. Note that the masking should not be done
// manually. Software is expected to get the key in two shares right from the
// beginning.

static const unsigned char plain_text_0[16] = {
    0x32, 0x43, 0xf6, 0xa8, 0x88, 0x5a, 0x30, 0x8d,
    0x31, 0x31, 0x98, 0xa2, 0xe0, 0x37, 0x07, 0x34};

static const uint8_t kKeyShare1[] = {0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae,
                                           0xd2, 0xa6, 0xab, 0xf7, 0x15, 0x88,
                                           0x09, 0xcf, 0x4f, 0x3c};

static const uint8_t key_32_0[] = {
    0x0f, 0x1f, 0x2f, 0x3f, 0x4f, 0x5f, 0x6f, 0x7f, 0x8f, 0x9f, 0xaf,
    0xbf, 0xcf, 0xdf, 0xef, 0xff, 0x0a, 0x1a, 0x2a, 0x3a, 0x4a, 0x5a,
    0x6a, 0x7a, 0x8a, 0x9a, 0xaa, 0xba, 0xca, 0xda, 0xea, 0xfa,
};

//static constexpr size_t kBlockCount = 3;
//  static constexpr size_t kBlockSize = 4;
//  static constexpr dif_aes_data_t kDataIn[kBlockCount] = {
//      {.data = {0xA55AA55A, 0xA55AA55A, 0xA55AA55A, 0xA55AA55A}},
//      {.data = {0x5AA5A55A, 0x5AA5A55A, 0x5AA5A55A, 0x5AA5A55A}},
//      {.data = {0xA55AA55A, 0xA55AA55A, 0xA55AA55A, 0xA55AA55A}},
//  };


OTTF_DEFINE_TEST_CONFIG();

status_t execute_test(dif_aes_t *aes) {


  // Mask the key. Note that this should not be done manually. Software is
  // expected to get the key in two shares right from the beginning.
  uint8_t key_share0[sizeof(kAesModesKey128)];
  for (int i = 0; i < sizeof(kAesModesKey128); ++i) {
    key_share0[i] = kAesModesKey128[i] ^ kKeyShare1[i];
  }

  // "Convert" key share byte arrays to `dif_aes_key_share_t`.
  dif_aes_key_share_t key;
  memcpy(key.share0, key_share0, sizeof(key.share0));
 

  // "Convert" iv byte arrays to `dif_aes_iv_t`.
  dif_aes_iv_t iv;
  memcpy(iv.iv, kAesModesIvCbc, sizeof(iv.iv));


  
  // Setup CBC encryption transaction.
  dif_aes_transaction_t transaction = {
      .operation = kDifAesOperationEncrypt,
      .mode = kDifAesModeCbc,
      .key_len = kDifAesKey128,
      .key_provider = kDifAesKeySoftwareProvided,
      .mask_reseeding = kDifAesReseedPerBlock,
      .manual_operation = kDifAesManualOperationAuto,
      .reseed_on_key_change = false,
      .ctrl_aux_lock = false,
  };

  CHECK_STATUS_OK(aes_testutils_setup_encryption(transaction, aes));



  //  EXPECT_READ32(AES_STATUS_REG_OFFSET, {{AES_STATUS_INPUT_READY_BIT, true},
  //                                       {AES_STATUS_OUTPUT_VALID_BIT, true}});

  // ExpectWriteMultreg(AES_DATA_IN_0_REG_OFFSET, kDataIn[0].data, kBlockSize);
  //EXPECT_READ32(AES_STATUS_REG_OFFSET, {{AES_STATUS_INPUT_READY_BIT, true}});

  //ExpectWriteMultreg(AES_DATA_IN_0_REG_OFFSET, kDataIn[1].data, kBlockSize);
  //EXPECT_READ32(AES_STATUS_REG_OFFSET, {{AES_STATUS_OUTPUT_VALID_BIT, true}});
  //ExpectReadMultreg(AES_DATA_OUT_0_REG_OFFSET, kDataOut[0].data, kBlockSize);

  //ExpectWriteMultreg(AES_DATA_IN_0_REG_OFFSET, kDataIn[2].data, kBlockSize);
  //EXPECT_READ32(AES_STATUS_REG_OFFSET, {{AES_STATUS_OUTPUT_VALID_BIT, true}});
  //ExpectReadMultreg(AES_DATA_OUT_0_REG_OFFSET, kDataOut[1].data, kBlockSize);

  //EXPECT_READ32(AES_STATUS_REG_OFFSET, {{AES_STATUS_OUTPUT_VALID_BIT, true}});
  //ExpectReadMultreg(AES_DATA_OUT_0_REG_OFFSET, kDataOut[2].data, kBlockSize);

  dif_aes_data_t out_data;

  EXPECT_DIF_OK(dif_aes_process_data(&aes_, plain_text_0, out_data, 1));
  

    
 
 
  AES_TESTUTILS_WAIT_FOR_STATUS(aes, kDifAesStatusOutputValid, true, TIMEOUT);

  // Check the ciphertext against the expected value.
  dif_aes_data_t out_data;
  CHECK_DIF_OK(dif_aes_read_output(aes, &out_data));
  CHECK_ARRAYS_EQ((uint8_t *)out_data.data, kAesModesCipherTextCbc128,
                  sizeof(out_data.data));

  // Write the KEY_IV_DATA_IN_CLEAR and DATA_OUT_CLEAR trigger bits to 1 and
  // wait for it to complete by polling the status idle bit.
  ////  CHECK_DIF_OK(dif_aes_trigger(aes, kDifAesTriggerDataOutClear));
  //// CHECK_DIF_OK(dif_aes_trigger(aes, kDifAesTriggerKeyIvDataInClear));
  AES_TESTUTILS_WAIT_FOR_STATUS(aes, kDifAesStatusIdle, true, TIMEOUT);

  // Read back the data out CSRs - they should all read garbage values.
  CHECK(dif_aes_read_output(aes, &out_data) == kDifError);
  CHECK(!aes_testutils_get_status(aes, kDifAesStatusOutputValid));

  // Assertion check verifies that the internal states (data_in, key share and
  // IV are also garbage, i.e. different from the originally written values.
  CHECK_DIF_OK(dif_aes_read_iv(aes, &iv));
  CHECK_ARRAYS_NE((uint8_t *)iv.iv, kAesModesIvCbc, sizeof(kAesModesIvCbc));

  CHECK_DIF_OK(dif_aes_end(aes));

  return OK_STATUS();
}

bool test_main(void) {
  dif_aes_t aes;

  // Initialise AES.
  CHECK_DIF_OK(
      dif_aes_init(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR), &aes));
  CHECK_DIF_OK(dif_aes_reset(&aes));

  return status_ok(execute_test(&aes));
}
